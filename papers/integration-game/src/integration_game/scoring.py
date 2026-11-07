"""
scoring.py
Tier-1/2/3 evaluation, cost functional J, fitness S, and ranking of winning plays.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Sequence

from .primitives import Message, TransferMode
from .interfaces import Interface
from .board import Board
from .ulsc import TBAEvaluationResult, UniversalLSC

# Spec-aligned breach severity Ω
OMEGA_BREACH = 10000.0


@dataclass
class ScoreBreakdown:
    board_name: str
    snapshot_label: str
    tier1_struct_penalty: float
    tier2_kin_penalty: float
    tier3_tba_penalty: float
    static_cost: float
    dynamic_cost: float
    total_cost_J: float
    fitness_score_S: float
    tier1_satisfied: bool
    tier2_satisfied: bool
    tier3_satisfied: bool
    tba_result: TBAEvaluationResult
    notes: List[str] = field(default_factory=list)
    residual_cost: float = 0.0  # static+dyn among winners

    @property
    def is_winning_play(self) -> bool:
        return self.tier1_satisfied and self.tier2_satisfied and self.tier3_satisfied


class BoardEvaluator:
    def __init__(
        self,
        w_unconnected: float = 20.0,
        w_color: float = 10.0,
        w_rep: float = 8.0,
        w_prov: float = 10.0,
        w_kin: float = 15.0,
        w_cut_progress: float = 25.0,
        w_breach: float = 12.0,
        w_clock_overrun: float = 3.0,
        w_val_err: float = 5.0,
        use_omega: bool = True,
    ):
        self.w_unconnected = w_unconnected
        self.w_color = w_color
        self.w_rep = w_rep
        self.w_prov = w_prov
        self.w_kin = w_kin
        self.w_cut_progress = w_cut_progress
        self.w_breach = w_breach
        self.w_clock_overrun = w_clock_overrun
        self.w_val_err = w_val_err
        self.use_omega = use_omega

    def evaluate(
        self,
        board: Board,
        ulsc: UniversalLSC,
        scenario_inputs: Dict[int, Dict[str, Message]],
        snapshot_label: str = "Snapshot",
    ) -> ScoreBreakdown:
        notes: List[str] = []
        tier1_penalty = 0.0
        tier2_penalty = 0.0

        all_offers: List[Interface] = []
        for comp in board.components.values():
            all_offers.extend(comp.offers.values())

        for comp in board.components.values():
            for need_if in comp.needs.values():
                if need_if.connected_route_id is None:
                    candidate_offers = [
                        off_if for off_if in all_offers if off_if.component_id != comp.comp_id
                    ]
                    min_c_dist = min(
                        (self._shape_color_distance(off_if, need_if) for off_if in candidate_offers),
                        default=3.0,
                    )
                    has_rep_match = any(
                        bool(off_if.shape.allowed_reps & need_if.shape.allowed_reps)
                        for off_if in candidate_offers
                    )
                    rep_gap = 0.0 if has_rep_match else (0.5 * self.w_rep)
                    weight = 1.0 if comp.is_boundary else 0.5
                    tier1_penalty += weight * (
                        self.w_unconnected + self.w_color * (min_c_dist / 3.0) + rep_gap
                    )
                    notes.append(
                        f"Unconnected Need '{need_if.full_id}' "
                        f"(min color gap={min_c_dist:.2f}, rep_match={has_rep_match})"
                    )
                else:
                    route = board.routes[need_if.connected_route_id]
                    src_if = board.get_interface(route.source_if)

                    c_dist = self._shape_color_distance(src_if, need_if)
                    if c_dist > 0.0:
                        tier1_penalty += self.w_color * c_dist
                        notes.append(
                            f"Color mismatch on route '{route.route_id}' (distance={c_dist:.2f})"
                        )

                    if not (src_if.shape.allowed_reps & need_if.shape.allowed_reps):
                        tier1_penalty += self.w_rep
                        notes.append(f"Representation mismatch on route '{route.route_id}'")

                    # Provenance contract gap (static floor / assurance)
                    if need_if.shape.min_trust_score > src_if.shape.min_trust_score and (
                        need_if.shape.min_trust_score > 0.0
                    ):
                        # Only penalize when need requires elevated trust and offer doesn't advertise it
                        if src_if.shape.min_trust_score < need_if.shape.min_trust_score:
                            tier1_penalty += self.w_prov * (
                                need_if.shape.min_trust_score - src_if.shape.min_trust_score
                            )
                            notes.append(
                                f"Provenance trust gap on '{route.route_id}' "
                                f"(need>={need_if.shape.min_trust_score}, "
                                f"offer_floor={src_if.shape.min_trust_score})"
                            )
                    if (
                        need_if.shape.required_assurance is not None
                        and src_if.shape.required_assurance != need_if.shape.required_assurance
                        and need_if.shape.required_assurance == "TMR_VOTED"
                    ):
                        # Offer shape may not advertise assurance; runtime ProvTMR sets message assurance.
                        # Static Tier1: if need requires TMR_VOTED and source offer shape doesn't declare it,
                        # check whether source component is ProvTMRVoteBlock (satisfied) else penalize.
                        src_comp = board.components[src_if.component_id]
                        from .components import ProvTMRVoteBlock

                        if not isinstance(src_comp, ProvTMRVoteBlock):
                            if src_if.shape.required_assurance != need_if.shape.required_assurance:
                                tier1_penalty += self.w_prov
                                notes.append(
                                    f"Provenance assurance gap on '{route.route_id}' "
                                    f"(need={need_if.shape.required_assurance})"
                                )

                    # Silent no-transfer: wired but incompatible for runtime
                    if not board._is_route_compatible(src_if, need_if):
                        notes.append(
                            f"Wired but non-transferring route '{route.route_id}' "
                            f"(runtime gate closed)"
                        )

                    # Tier 2 kinematics: port mode mismatch
                    if src_if.mode != need_if.mode:
                        tier2_penalty += self.w_kin
                        notes.append(
                            f"Kinematic mismatch on route '{route.route_id}': "
                            f"{src_if.mode.value} Offer → {need_if.mode.value} Need"
                        )
                    else:
                        # Velocity consistency: PUSH offer should have v>0, PULL v==0
                        if src_if.is_offer and src_if.offer is not None:
                            if src_if.mode == TransferMode.PUSH and src_if.offer.velocity <= 0.0:
                                tier2_penalty += 0.5 * self.w_kin
                                notes.append(f"PUSH offer '{src_if.full_id}' has non-positive velocity")
                            if src_if.mode == TransferMode.PULL and src_if.offer.velocity != 0.0:
                                tier2_penalty += 0.5 * self.w_kin
                                notes.append(f"PULL offer '{src_if.full_id}' has nonzero velocity")

        tier1_ok = tier1_penalty == 0.0
        tier2_ok = tier2_penalty == 0.0

        outputs_by_consumer = board.simulate(scenario_inputs, ulsc.horizon)
        target_outputs = outputs_by_consumer.get(ulsc.target_need_id, {})
        tba_res = ulsc.evaluate_trace(scenario_inputs, target_outputs)

        tier3_penalty = (
            self.w_cut_progress * (1.0 - tba_res.cut_progress_ratio)
            + self.w_breach * min(3, tba_res.hot_breaches)
            + self.w_clock_overrun * min(5.0, tba_res.total_clock_overrun)
            + self.w_val_err * min(5.0, tba_res.total_value_error)
        )
        if self.use_omega and tba_res.hot_breaches > 0:
            tier3_penalty += OMEGA_BREACH
        # Also fold negative RM reward magnitude lightly for diagnostics (already in Omega)
        tier3_ok = tba_res.satisfied

        static_cost = sum(c.static_cost for c in board.interior_blocks) + sum(
            r.carrier_cost for r in board.routes.values()
        )
        dynamic_cost = 0.0
        for comp in board.components.values():
            dynamic_cost += 2.0 * len(comp.disruption_events)
            dynamic_cost += sum(loss for _, loss, _ in comp.info_loss_events)
            dynamic_cost += sum(lat for _, lat, _ in getattr(comp, "latency_events", []))

        residual = static_cost + dynamic_cost
        total_J = round(
            tier1_penalty + tier2_penalty + tier3_penalty + static_cost + dynamic_cost,
            2,
        )
        # Fitness uses capped view so Omega doesn't make S meaningless for tables;
        # still total_J carries full Omega for ranking losers below winners.
        display_J = total_J
        fitness_S = round(max(0.0, 100.0 - min(display_J, 10000.0)), 2)
        if tba_res.hot_breaches > 0 and self.use_omega:
            # Report S based on pre-Omega structural progress for readable tables
            soft_J = (
                tier1_penalty
                + tier2_penalty
                + (
                    self.w_cut_progress * (1.0 - tba_res.cut_progress_ratio)
                    + self.w_breach * min(3, tba_res.hot_breaches)
                    + self.w_clock_overrun * min(5.0, tba_res.total_clock_overrun)
                    + self.w_val_err * min(5.0, tba_res.total_value_error)
                )
                + static_cost
                + dynamic_cost
            )
            fitness_S = round(max(0.0, 100.0 - soft_J), 2)

        return ScoreBreakdown(
            board_name=board.name,
            snapshot_label=snapshot_label,
            tier1_struct_penalty=round(tier1_penalty, 2),
            tier2_kin_penalty=round(tier2_penalty, 2),
            tier3_tba_penalty=round(tier3_penalty, 2),
            static_cost=round(static_cost, 2),
            dynamic_cost=round(dynamic_cost, 2),
            total_cost_J=total_J,
            fitness_score_S=fitness_S,
            tier1_satisfied=tier1_ok,
            tier2_satisfied=tier2_ok,
            tier3_satisfied=tier3_ok,
            tba_result=tba_res,
            notes=notes + tba_res.diagnostics,
            residual_cost=round(residual, 2),
        )

    @staticmethod
    def _shape_color_distance(src_if: Interface, tgt_if: Interface) -> float:
        sk, tk = src_if.shape.kind, tgt_if.shape.kind
        if sk != tk:
            return src_if.shape.primary_color.distance_to(tgt_if.shape.primary_color) + 1.0
        if src_if.shape.kind.value == "RECORD":
            if set(src_if.shape.slots.keys()) != set(tgt_if.shape.slots.keys()):
                return src_if.shape.primary_color.distance_to(tgt_if.shape.primary_color) + 1.0
            return sum(
                src_if.shape.slots[s].distance_to(tgt_if.shape.slots[s]) for s in src_if.shape.slots
            )
        return src_if.shape.primary_color.distance_to(tgt_if.shape.primary_color)


def rank_winning_plays(results: Sequence[ScoreBreakdown]) -> List[ScoreBreakdown]:
    """Rank winning plays by residual cost (static+dyn); losers excluded."""
    winners = [r for r in results if r.is_winning_play]
    return sorted(winners, key=lambda r: (r.residual_cost, r.total_cost_J))


def print_progression_table(results: List[ScoreBreakdown]) -> None:
    header = (
        f"{'Snapshot / Move':<42} | {'T1':>6} | {'T2':>6} | "
        f"{'T3':>7} | {'C_st':>5} | {'J':>8} | {'S':>6} | {'Status':<8}"
    )
    print("=" * len(header))
    print(header)
    print("-" * len(header))
    for r in results:
        status = "WIN" if r.is_winning_play else "UNSAT"
        print(
            f"{r.snapshot_label:<42} | {r.tier1_struct_penalty:>6.1f} | {r.tier2_kin_penalty:>6.1f} | "
            f"{r.tier3_tba_penalty:>7.1f} | {r.static_cost:>5.2f} | {r.total_cost_J:>8.1f} | "
            f"{r.fitness_score_S:>6.1f} | {status:<8}"
        )
    print("=" * len(header))
