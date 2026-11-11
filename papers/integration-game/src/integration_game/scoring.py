"""
scoring.py
Tier-1/2/3 evaluation, cost functional J, fitness S, and ranking of winning plays.
Designed to satisfy the 7 technology-independent cost assertions (A1–A7):
  A1. Feasibility Dominance (Win > Lose)
  A2. Credit Only Connected Moves
  A3. Prefer Useful Moves
  A4. Close Ports Continuously
  A5. Rank Breaches by Severity
  A6. Prefer Better QoS
  A7. Prefer Simpler Boards
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Sequence, Set, Tuple

from .config import ColorDistanceConfig, DEFAULT_CONFIG, GameConfig, ScoringConfig
from .primitives import Message, TransferMode, representation_sets_compatible
from .interfaces import Interface
from .board import Board
from .components import ProvTMRVoteBlock
from .ulsc import LSCMonitor, TBAEvaluationResult

# Spec-aligned default breach severity Ω
OMEGA_BREACH = DEFAULT_CONFIG.scoring.omega_breach


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
    residual_cost: float = 0.0  # static + dynamic cost among winners

    @property
    def is_winning_play(self) -> bool:
        return self.tier1_satisfied and self.tier2_satisfied and self.tier3_satisfied


class BoardEvaluator:
    def __init__(
        self,
        w_unconnected: Optional[float] = None,
        w_color: Optional[float] = None,
        w_rep: Optional[float] = None,
        w_prov: Optional[float] = None,
        w_kin: Optional[float] = None,
        w_velocity: Optional[float] = None,
        w_cut_progress: Optional[float] = None,
        w_breach: Optional[float] = None,
        w_clock_overrun: Optional[float] = None,
        w_val_err: Optional[float] = None,
        w_lat: Optional[float] = None,
        w_loss: Optional[float] = None,
        w_drop: Optional[float] = None,
        gamma: Optional[float] = None,
        use_omega: Optional[bool] = None,
        config: Optional[ScoringConfig] = None,
        game_config: Optional[GameConfig] = None,
    ):
        base_game_cfg = game_config or DEFAULT_CONFIG
        base = config or base_game_cfg.scoring
        self.color_cfg: ColorDistanceConfig = base_game_cfg.color_distance
        self.carrier_cfg = base_game_cfg.carrier_costs

        overrides = {}
        if w_unconnected is not None:
            overrides["w_unconnected"] = w_unconnected
        if w_color is not None:
            overrides["w_color"] = w_color
        if w_rep is not None:
            overrides["w_rep"] = w_rep
        if w_prov is not None:
            overrides["w_prov"] = w_prov
        if w_kin is not None:
            overrides["w_kin"] = w_kin
        if w_velocity is not None:
            overrides["w_velocity"] = w_velocity
        if w_cut_progress is not None:
            overrides["w_cut_progress"] = w_cut_progress
        if w_breach is not None:
            overrides["w_breach"] = w_breach
        if w_clock_overrun is not None:
            overrides["w_clock_overrun"] = w_clock_overrun
        if w_val_err is not None:
            overrides["w_val_err"] = w_val_err
        if w_lat is not None:
            overrides["w_lat"] = w_lat
        if w_loss is not None:
            overrides["w_loss"] = w_loss
        if w_drop is not None:
            overrides["w_drop"] = w_drop
        if gamma is not None:
            overrides["gamma"] = gamma
        if use_omega is not None:
            overrides["use_omega"] = use_omega

        self.cfg: ScoringConfig = base.with_overrides(**overrides) if overrides else base

        # Expose direct attributes for backward compatibility
        self.w_unconnected = self.cfg.w_unconnected
        self.w_color = self.cfg.w_color
        self.w_rep = self.cfg.w_rep
        self.w_prov = self.cfg.w_prov
        self.w_kin = self.cfg.w_kin
        self.w_velocity = self.cfg.w_velocity
        self.w_cut_progress = self.cfg.w_cut_progress
        self.w_breach = self.cfg.w_breach
        self.w_clock_overrun = self.cfg.w_clock_overrun
        self.w_val_err = self.cfg.w_val_err
        self.w_lat = self.cfg.w_lat
        self.w_loss = self.cfg.w_loss
        self.w_drop = self.cfg.w_drop
        self.gamma = self.cfg.gamma
        self.use_omega = self.cfg.use_omega

    def _structural_tier_penalties(
        self, board: Board
    ) -> Tuple[float, float, List[str]]:
        """Tier-1/2 chain evaluation without simulation (lookahead / MCTS hook)."""
        notes: List[str] = []
        live_offers = board.live_offers()

        root_needs: List[Interface] = []
        for comp in board.components.values():
            if comp.is_boundary:
                root_needs.extend(comp.needs.values())
        if not root_needs:
            for comp in board.components.values():
                root_needs.extend(comp.needs.values())

        visited_routes: Set[str] = set()
        visited_needs: Set[str] = set()
        tier1_penalty = 0.0
        tier2_penalty = 0.0

        for r_need in root_needs:
            t1, t2 = self._eval_need_chain(
                board=board,
                need_if=r_need,
                weight=1.0,
                live_offers=live_offers,
                visited_routes=visited_routes,
                visited_needs=visited_needs,
                ancestors=set(),
                notes=notes,
            )
            tier1_penalty += t1
            tier2_penalty += t2

        for rid, route in board.routes.items():
            if rid in visited_routes:
                continue
            src_if = board.get_interface(route.source_if)
            tgt_if = board.get_interface(route.target_if)
            t1, t2, r_notes = self._pair_mismatch(board, src_if, tgt_if, route_id=rid)
            tier1_penalty += t1
            tier2_penalty += t2
            notes.extend(r_notes)

        return tier1_penalty, tier2_penalty, notes

    def evaluate_structural(
        self,
        board: Board,
        snapshot_label: str = "Structural",
    ) -> ScoreBreakdown:
        """
        Cheap Tier-1/2 + static cost score without board.simulate / TBA.
        Intended for greedy/MCTS one-step lookahead; not a win certificate.
        """
        from .ulsc import TBAEvaluationResult

        tier1_penalty, tier2_penalty, notes = self._structural_tier_penalties(board)
        tier1_ok = round(tier1_penalty, 6) == 0.0
        tier2_ok = round(tier2_penalty, 6) == 0.0
        static_cost = sum(c.static_cost for c in board.interior_blocks) + sum(
            r.carrier.cost_with_config(self.carrier_cfg) for r in board.routes.values()
        )
        tba_res = TBAEvaluationResult(
            satisfied=False,
            hot_breaches=0,
            missed_deadlines=0,
            silence_violations=0,
            total_clock_overrun=0.0,
            total_value_error=0.0,
            cut_progress_ratio=0.0,
            diagnostics=["structural_only"],
        )
        residual = static_cost
        soft_J = tier1_penalty + tier2_penalty + residual
        fitness_S = round(self._soft_j_to_fitness(soft_J), 2)
        total_J = round(tier1_penalty + tier2_penalty + residual, 4)
        return ScoreBreakdown(
            board_name=board.name,
            snapshot_label=snapshot_label,
            tier1_struct_penalty=round(tier1_penalty, 2),
            tier2_kin_penalty=round(tier2_penalty, 2),
            tier3_tba_penalty=0.0,
            static_cost=round(static_cost, 2),
            dynamic_cost=0.0,
            total_cost_J=round(total_J, 2),
            fitness_score_S=fitness_S,
            tier1_satisfied=tier1_ok,
            tier2_satisfied=tier2_ok,
            tier3_satisfied=False,
            tba_result=tba_res,
            notes=notes + ["structural_only"],
            residual_cost=round(residual, 2),
        )

    def evaluate(
        self,
        board: Board,
        ulsc: LSCMonitor,
        scenario_inputs: Dict[int, Dict[str, Message]],
        snapshot_label: str = "Snapshot",
    ) -> ScoreBreakdown:
        notes: List[str] = []
        tier1_penalty, tier2_penalty, struct_notes = self._structural_tier_penalties(board)
        notes.extend(struct_notes)

        tier1_ok = round(tier1_penalty, 6) == 0.0
        tier2_ok = round(tier2_penalty, 6) == 0.0

        # Simulate board and evaluate uLSC / CompositeLSC monitor
        outputs_by_consumer = board.simulate(scenario_inputs, ulsc.horizon)
        if hasattr(ulsc, "evaluate_board_outputs"):
            tba_res = ulsc.evaluate_board_outputs(scenario_inputs, outputs_by_consumer)
        else:
            target_outputs = outputs_by_consumer.get(ulsc.target_need_id, {})
            tba_res = ulsc.evaluate_trace(scenario_inputs, target_outputs)

        # Uncapped Tier-3 behavioral deficiency (strictly monotonic in all error components, Axiom A5)
        raw_tier3 = (
            self.cfg.w_cut_progress * (1.0 - tba_res.cut_progress_ratio)
            + self.cfg.w_breach * float(tba_res.hot_breaches)
            + self.cfg.w_clock_overrun * float(tba_res.total_clock_overrun)
            + self.cfg.w_val_err * float(tba_res.total_value_error)
        )
        tier3_ok = tba_res.satisfied
        if not tier3_ok and raw_tier3 == 0.0:
            raw_tier3 += self.cfg.w_cut_progress

        tier3_penalty = raw_tier3
        if self.cfg.use_omega and (tba_res.hot_breaches > 0 or not tier3_ok):
            tier3_penalty += self.cfg.omega_breach

        # Static construction cost (Axiom A7)
        static_cost = sum(c.static_cost for c in board.interior_blocks) + sum(
            r.carrier.cost_with_config(self.carrier_cfg) for r in board.routes.values()
        )

        # Dynamic operational cost with optional discount factor gamma (Paper Eq. 8, Axiom A6)
        dynamic_cost = 0.0
        for comp in board.components.values():
            for tick, _code, _reason in comp.disruption_events:
                dynamic_cost += (self.cfg.gamma ** tick) * self.cfg.w_drop
            for tick, loss, _reason in comp.info_loss_events:
                dynamic_cost += (self.cfg.gamma ** tick) * self.cfg.w_loss * float(loss)
            for tick, lat, _reason in getattr(comp, "latency_events", []):
                dynamic_cost += (self.cfg.gamma ** tick) * self.cfg.w_lat * float(lat)

        residual = static_cost + dynamic_cost
        is_win = tier1_ok and tier2_ok and tier3_ok

        # Ensure lexicographic dominance of winning plays over losing plays in total_cost_J (Axiom A1)
        omega_term = 0.0
        if self.cfg.use_omega and not is_win and tier3_penalty < self.cfg.omega_breach:
            omega_term = self.cfg.omega_breach

        total_J = round(
            tier1_penalty + tier2_penalty + tier3_penalty + omega_term + static_cost + dynamic_cost,
            4,
        )

        # Compute human-readable fitness S in (0, 100] as a C^1-smooth, strictly decreasing
        # function of soft_J (never saturating at 0.0 or capping error gradients).
        if is_win:
            soft_J = residual
        else:
            M = self.cfg.soft_error_scale
            soft_tier3 = (
                self.cfg.w_cut_progress * (1.0 - tba_res.cut_progress_ratio)
                + self._smooth_cap(self.cfg.w_breach * float(tba_res.hot_breaches), M)
                + self._smooth_cap(self.cfg.w_clock_overrun * float(tba_res.total_clock_overrun), M)
                + self._smooth_cap(self.cfg.w_val_err * float(tba_res.total_value_error), M)
            )
            if not tier3_ok and soft_tier3 == 0.0:
                soft_tier3 += self.cfg.w_cut_progress
            # Guarantee a strict margin above winning residual costs even if only Tier1/2 fails
            min_failure_floor = 0.0 if not tier3_ok else self.cfg.w_cut_progress * 0.5
            soft_J = tier1_penalty + tier2_penalty + soft_tier3 + min_failure_floor + residual

        fitness_S = round(self._soft_j_to_fitness(soft_J), 2)

        return ScoreBreakdown(
            board_name=board.name,
            snapshot_label=snapshot_label,
            tier1_struct_penalty=round(tier1_penalty, 2),
            tier2_kin_penalty=round(tier2_penalty, 2),
            tier3_tba_penalty=round(tier3_penalty, 2),
            static_cost=round(static_cost, 2),
            dynamic_cost=round(dynamic_cost, 2),
            total_cost_J=round(total_J, 2),
            fitness_score_S=fitness_S,
            tier1_satisfied=tier1_ok,
            tier2_satisfied=tier2_ok,
            tier3_satisfied=tier3_ok,
            tba_result=tba_res,
            notes=notes + tba_res.diagnostics,
            residual_cost=round(residual, 2),
        )

    def _eval_need_chain(
        self,
        board: Board,
        need_if: Interface,
        weight: float,
        live_offers: Sequence[Interface],
        visited_routes: Set[str],
        visited_needs: Set[str],
        ancestors: Set[str],
        notes: List[str],
    ) -> Tuple[float, float]:
        if need_if.full_id in visited_needs:
            return 0.0, 0.0
        visited_needs.add(need_if.full_id)

        if need_if.connected_route_id is None or need_if.connected_route_id not in board.routes:
            # Open frontier Need: evaluate against grounded live_offers (Axioms A2, A3, A4)
            t1_gap, t2_gap, f_note = self._frontier_gap_for_need(
                board=board,
                need_if=need_if,
                live_offers=live_offers,
                ancestors=ancestors | {need_if.component_id},
            )
            notes.append(f_note)
            return weight * (self.cfg.w_unconnected + t1_gap), weight * t2_gap

        # Connected Need
        rid = need_if.connected_route_id
        visited_routes.add(rid)
        route = board.routes[rid]
        src_if = board.get_interface(route.source_if)
        t1_pair, t2_pair, pair_notes = self._pair_mismatch(board, src_if, need_if, route_id=rid)
        notes.extend(pair_notes)

        t1_total = weight * t1_pair
        t2_total = weight * t2_pair

        src_comp = board.components[src_if.component_id]
        if not src_comp.is_boundary and len(src_comp.needs) > 0 and src_comp.comp_id not in ancestors:
            sub_needs = list(src_comp.needs.values())
            sub_weight = weight / float(len(sub_needs))
            next_ancestors = ancestors | {need_if.component_id, src_comp.comp_id}
            for sub_n in sub_needs:
                sub_t1, sub_t2 = self._eval_need_chain(
                    board=board,
                    need_if=sub_n,
                    weight=sub_weight,
                    live_offers=live_offers,
                    visited_routes=visited_routes,
                    visited_needs=visited_needs,
                    ancestors=next_ancestors,
                    notes=notes,
                )
                t1_total += sub_t1
                t2_total += sub_t2

        return t1_total, t2_total

    def _frontier_gap_for_need(
        self,
        board: Board,
        need_if: Interface,
        live_offers: Sequence[Interface],
        ancestors: Set[str],
    ) -> Tuple[float, float, str]:
        candidates = [
            off_if
            for off_if in live_offers
            if off_if.component_id not in ancestors
        ]
        if not candidates:
            t1_fallback = self.cfg.w_color * self.cfg.default_no_offer_color_dist + 0.5 * self.cfg.w_rep
            return (
                t1_fallback,
                0.0,
                f"Unconnected Need '{need_if.full_id}' (no live offers available)",
            )

        best_t1 = float("inf")
        best_t2 = float("inf")
        best_off: Optional[Interface] = None

        for off_if in candidates:
            t1_pair, t2_pair, _ = self._pair_mismatch(board, off_if, need_if, route_id=None)
            # Include any unresolved upstream deficiency on partially-wired multi-input blocks
            up_t1, up_t2 = self._upstream_unwired_deficiency(board, off_if.component_id, ancestors)
            tot_t1 = t1_pair + up_t1
            tot_t2 = t2_pair + up_t2
            if (tot_t1 + tot_t2) < (best_t1 + best_t2):
                best_t1 = tot_t1
                best_t2 = tot_t2
                best_off = off_if

        assert best_off is not None
        c_dist = self._shape_color_distance(best_off, need_if, self.color_cfg)
        has_rep = representation_sets_compatible(
            best_off.shape.allowed_reps, need_if.shape.allowed_reps
        )
        note = (
            f"Unconnected Need '{need_if.full_id}' "
            f"(closest live offer='{best_off.full_id}', color_dist={c_dist:.2f}, rep_match={has_rep})"
        )
        return best_t1, best_t2, note

    def _upstream_unwired_deficiency(
        self,
        board: Board,
        comp_id: str,
        ancestors: Set[str],
    ) -> Tuple[float, float]:
        """
        If a live interior component has multiple Needs and some are still unwired,
        account for their fractional unwired penalty so partial multi-input wiring is graded smoothly.
        """
        if comp_id in ancestors or comp_id not in board.components:
            return 0.0, 0.0
        comp = board.components[comp_id]
        if comp.is_boundary or not comp.needs:
            return 0.0, 0.0
        k = len(comp.needs)
        t1 = 0.0
        t2 = 0.0
        for n_if in comp.needs.values():
            if n_if.connected_route_id is None or n_if.connected_route_id not in board.routes:
                t1 += (1.0 / k) * self.cfg.w_unconnected
            else:
                r = board.routes[n_if.connected_route_id]
                src_cid = r.source_if.split(".", 1)[0]
                sub_t1, sub_t2 = self._upstream_unwired_deficiency(
                    board, src_cid, ancestors | {comp_id}
                )
                t1 += (1.0 / k) * sub_t1
                t2 += (1.0 / k) * sub_t2
        return t1, t2

    def _pair_mismatch(
        self,
        board: Board,
        src_if: Interface,
        need_if: Interface,
        route_id: Optional[str] = None,
    ) -> Tuple[float, float, List[str]]:
        """
        Exact pairwise Tier-1 and Tier-2 mismatch between `src_if` (Offer) and `need_if` (Need).
        Used identically for connected routes and candidate frontier pairs (Axiom A4).
        """
        t1 = 0.0
        t2 = 0.0
        pair_notes: List[str] = []
        label = f"route '{route_id}'" if route_id else f"pair '{src_if.full_id}->{need_if.full_id}'"

        # 1. Color / shape distance
        c_dist = self._shape_color_distance(src_if, need_if, self.color_cfg)
        if c_dist > 0.0:
            t1 += self.cfg.w_color * c_dist
            if route_id:
                pair_notes.append(f"Color mismatch on {label} (distance={c_dist:.2f})")

        # 2. Representation compatibility (ABI aliases: C_ABI↔NATIVE_STRUCT, DDS_BINDING↔CDR_DDS)
        if not representation_sets_compatible(
            src_if.shape.allowed_reps, need_if.shape.allowed_reps
        ):
            t1 += self.cfg.w_rep
            if route_id:
                pair_notes.append(f"Representation mismatch on {label}")

        # 3. Provenance contract gap (trust score + assurance level)
        if need_if.shape.min_trust_score > 0.0 and (
            src_if.shape.min_trust_score < need_if.shape.min_trust_score
        ):
            trust_gap = need_if.shape.min_trust_score - src_if.shape.min_trust_score
            t1 += 0.5 * self.cfg.w_prov * trust_gap
            if route_id:
                pair_notes.append(
                    f"Provenance trust gap on {label} "
                    f"(need>={need_if.shape.min_trust_score}, offer_floor={src_if.shape.min_trust_score})"
                )

        if (
            need_if.shape.required_assurance is not None
            and src_if.shape.required_assurance != need_if.shape.required_assurance
        ):
            src_comp = board.components[src_if.component_id]
            is_tmr_ok = (
                need_if.shape.required_assurance == "TMR_VOTED"
                and isinstance(src_comp, ProvTMRVoteBlock)
            )
            if not is_tmr_ok:
                t1 += 0.5 * self.cfg.w_prov
                if route_id:
                    pair_notes.append(
                        f"Provenance assurance gap on {label} "
                        f"(need={need_if.shape.required_assurance})"
                    )

        if route_id and not board._is_route_compatible(src_if, need_if):
            pair_notes.append(f"Wired but non-transferring {label} (runtime gate closed)")

        # 4. Tier-2 Kinematics (Push/Pull transfer mode + velocity consistency)
        if src_if.mode != need_if.mode:
            t2 += self.cfg.w_kin
            if route_id:
                pair_notes.append(
                    f"Kinematic mismatch on {label}: "
                    f"{src_if.mode.value} Offer → {need_if.mode.value} Need"
                )
        else:
            if src_if.is_offer and src_if.offer is not None:
                if src_if.mode == TransferMode.PUSH and src_if.offer.velocity <= 0.0:
                    t2 += self.cfg.w_velocity
                    if route_id:
                        pair_notes.append(f"PUSH offer '{src_if.full_id}' has non-positive velocity")
                if src_if.mode == TransferMode.PULL and src_if.offer.velocity != 0.0:
                    t2 += self.cfg.w_velocity
                    if route_id:
                        pair_notes.append(f"PULL offer '{src_if.full_id}' has nonzero velocity")

        return t1, t2, pair_notes

    @staticmethod
    def _smooth_cap(val: float, scale: float) -> float:
        """Strictly increasing, bounded rational compression (scale * val) / (scale + val)."""
        if val <= 0.0:
            return 0.0
        return (scale * val) / (scale + val)

    def _soft_j_to_fitness(self, soft_j: float) -> float:
        """
        C^1-smooth, strictly decreasing bijection from soft_j in [0, inf) to (0, fitness_ceiling].
        Linear (ceiling - soft_j) on [0, knee], with smooth rational tail above knee.
        """
        ceiling = self.cfg.fitness_ceiling
        knee = 0.7 * ceiling  # 70.0 when ceiling=100.0
        tail = ceiling - knee  # 30.0
        if soft_j <= 0.0:
            return ceiling
        if soft_j <= knee:
            return ceiling - soft_j
        return tail / (1.0 + (soft_j - knee) / tail)

    @staticmethod
    def _shape_color_distance(
        src_if: Interface,
        tgt_if: Interface,
        color_cfg: Optional[ColorDistanceConfig] = None,
    ) -> float:
        c_cfg = color_cfg or DEFAULT_CONFIG.color_distance
        sk, tk = src_if.shape.kind, tgt_if.shape.kind
        if sk != tk:
            return (
                src_if.shape.primary_color.distance_to(tgt_if.shape.primary_color, c_cfg)
                + c_cfg.kind_mismatch_penalty
            )
        if src_if.shape.kind.value == "RECORD":
            src_keys = set(src_if.shape.slots.keys())
            tgt_keys = set(tgt_if.shape.slots.keys())
            if src_keys != tgt_keys:
                # Average slot color distance across target slots using best matching source slot
                slot_dists = []
                for tk_name, t_col in tgt_if.shape.slots.items():
                    if tk_name in src_if.shape.slots:
                        slot_dists.append(src_if.shape.slots[tk_name].distance_to(t_col, c_cfg))
                    else:
                        min_d = min(
                            s_col.distance_to(t_col, c_cfg) for s_col in src_if.shape.slots.values()
                        )
                        slot_dists.append(min_d + 0.5 * c_cfg.slot_mismatch_penalty)
                avg_d = sum(slot_dists) / float(max(1, len(slot_dists)))
                arity_diff = abs(len(src_keys) - len(tgt_keys))
                return avg_d + (0.5 + 0.25 * arity_diff) * c_cfg.slot_mismatch_penalty
            # Normalized average slot distance so N-slot records are on the same [0, 3] scale
            total_d = sum(
                src_if.shape.slots[s].distance_to(tgt_if.shape.slots[s], c_cfg)
                for s in tgt_if.shape.slots
            )
            return total_d / float(max(1, len(tgt_if.shape.slots)))
        if src_if.shape.kind.value == "CHOICE":
            src_keys = set(src_if.shape.choice_alternatives.keys())
            tgt_keys = set(tgt_if.shape.choice_alternatives.keys())
            if src_keys != tgt_keys:
                return (
                    src_if.shape.primary_color.distance_to(tgt_if.shape.primary_color, c_cfg)
                    + c_cfg.slot_mismatch_penalty
                )
            total_d = sum(
                src_if.shape.choice_alternatives[k].distance_to(
                    tgt_if.shape.choice_alternatives[k], c_cfg
                )
                for k in tgt_keys
            )
            return total_d / float(max(1, len(tgt_keys)))
        return src_if.shape.primary_color.distance_to(tgt_if.shape.primary_color, c_cfg)


def rank_winning_plays(results: Sequence[ScoreBreakdown]) -> List[ScoreBreakdown]:
    """Rank winning plays by residual cost (static+dyn); losers excluded."""
    winners = [r for r in results if r.is_winning_play]
    return sorted(winners, key=lambda r: (r.residual_cost, r.total_cost_J))


def print_progression_table(results: List[ScoreBreakdown]) -> None:
    header = (
        f"{'Snapshot / Move':<44} | {'T1':>6} | {'T2':>6} | "
        f"{'T3':>8} | {'C_st':>5} | {'C_dy':>5} | {'J':>8} | {'S':>6} | {'Status':<6}"
    )
    print("=" * len(header))
    print(header)
    print("-" * len(header))
    for r in results:
        status = "WIN" if r.is_winning_play else "UNSAT"
        print(
            f"{r.snapshot_label:<44} | {r.tier1_struct_penalty:>6.1f} | {r.tier2_kin_penalty:>6.1f} | "
            f"{r.tier3_tba_penalty:>8.1f} | {r.static_cost:>5.2f} | {r.dynamic_cost:>5.2f} | "
            f"{r.total_cost_J:>8.1f} | {r.fitness_score_S:>6.2f} | {status:<6}"
        )
    print("=" * len(header))
