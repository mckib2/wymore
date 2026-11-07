"""
Masked offline synthesis MDP for the Integration Game.
Observation + legal discrete actions + stepwise RM reward + terminal -J.
"""
from __future__ import annotations

import json
from dataclasses import dataclass, field
from typing import Any, Callable, Dict, List, Optional, Sequence, Tuple

from integration_game.board import Board
from integration_game.components import (
    CacheStoreBlock,
    ConsumerBoundary,
    ProducerBoundary,
    RecolorBlock,
    RepresentationBridgeBlock,
    WymorianComponent,
)
from integration_game.game import AddOperator, AddRoute, FinalizeBoard, IllegalMoveError, Play
from integration_game.primitives import (
    Color,
    Dynamics,
    Field,
    Message,
    MessageShape,
    Provenance,
    Representation,
    TransferMode,
)
from integration_game.scoring import BoardEvaluator, ScoreBreakdown
from integration_game.ulsc import RMState, UniversalLSC


@dataclass
class SynthTask:
    """Frozen synthesis problem: boundaries + catalog factories + scenario + uLSC."""
    name: str
    make_initial_board: Callable[[], Board]
    catalog: List[Tuple[str, Callable[[], WymorianComponent]]]
    scenario: Dict[int, Dict[str, Message]]
    ulsc: UniversalLSC
    max_moves: int = 12


def make_ping_pong_task() -> SynthTask:
    c_ping = Color(C="Net.Ping", L="SeqNum", P="uint16")
    c_pong_u16 = Color(C="Net.Pong", L="SeqNum", P="uint16")
    c_pong = Color(C="Net.Pong", L="SeqNum", P="uint32")

    def initial() -> Board:
        b = Board("RL_PingPong")
        b.add_component(
            ProducerBoundary(
                "PingGen",
                "out",
                c_ping,
                mode=TransferMode.PUSH,
                rep=Representation.BYTE_BLOB_JSON,
            )
        )
        b.add_component(
            ConsumerBoundary(
                "PongSink",
                "in",
                MessageShape.single(c_pong, reps=(Representation.NATIVE_STRUCT,)),
                mode=TransferMode.PULL,
                pull_schedule=lambda t: True,
            )
        )
        return b

    catalog = [
        (
            "json_bridge",
            lambda: RepresentationBridgeBlock(
                "JSON2Nat",
                c_ping,
                Representation.BYTE_BLOB_JSON,
                Representation.NATIVE_STRUCT,
                decode_fn=lambda s: int(json.loads(s)["seq"]),
            ),
        ),
        (
            "recolor_c",
            lambda: RecolorBlock("Recolor_C", c_ping, c_pong_u16, value_fn=int),
        ),
        (
            "recolor_p",
            lambda: RecolorBlock("Recolor_P", c_pong_u16, c_pong, value_fn=int),
        ),
        (
            "cache_consume",
            lambda: CacheStoreBlock("Queue", c_pong, retain_on_read=False),
        ),
        # Note: retain-on-read LVC is a Tier-3 silence trap; omitted from the
        # synthesis catalog so legal winning policies remain reachable.
    ]

    scenario = {
        1: {
            "PingGen.out": Message.single(
                Field(
                    json.dumps({"seq": 101}),
                    c_ping,
                    Dynamics("PingGen.out", 1.0),
                    representation=Representation.BYTE_BLOB_JSON,
                    provenance=Provenance(("PingGen",), timestamp_tick=1),
                )
            )
        },
        5: {
            "PingGen.out": Message.single(
                Field(
                    json.dumps({"seq": 202}),
                    c_ping,
                    Dynamics("PingGen.out", 1.0),
                    representation=Representation.BYTE_BLOB_JSON,
                    provenance=Provenance(("PingGen",), timestamp_tick=5),
                )
            )
        },
    }
    ulsc = UniversalLSC(
        name="uLSC_PingPong_RL",
        target_need_id="PongSink.in",
        horizon=8,
        pre_trigger_fn=lambda t, env: env.get("PingGen.out"),
        value_distance_fn=lambda trig, out: abs(
            float(json.loads(trig.first_field().value)["seq"]) - float(out.first_field().value)
        ),
        tolerance=0.0,
        min_delay=0,
        max_delay=1,
        enforce_silence=True,
    )
    return SynthTask("ex02_ping_pong", initial, catalog, scenario, ulsc, max_moves=14)


@dataclass
class StepResult:
    obs: Dict[str, float]
    reward: float
    done: bool
    info: Dict[str, Any]


class IntegrationGameEnv:
    """
    Discrete synthesis environment.
    Action ids index into legal_moves() for the current state (masked).
    """

    def __init__(self, task: SynthTask, step_penalty: float = 0.05):
        self.task = task
        self.step_penalty = step_penalty
        self.evaluator = BoardEvaluator()
        self.play: Optional[Play] = None
        self.moves_taken = 0
        self._last_rm_reward = 0.0
        self._catalog_used: set = set()

    def reset(self) -> Dict[str, float]:
        self.play = Play(board=self.task.make_initial_board())
        self.moves_taken = 0
        self._last_rm_reward = 0.0
        self._catalog_used = set()
        return self.observe()

    def observe(self) -> Dict[str, float]:
        assert self.play is not None
        unmet = self.play.unmet_needs()
        score = self._quick_score()
        rm_state = 0.0
        if score.tba_result.rm_state_trace:
            last = score.tba_result.rm_state_trace[-1]
            rm_state = float(list(RMState).index(last))
        return {
            "n_unmet": float(len(unmet)),
            "tier1": float(score.tier1_struct_penalty),
            "tier2": float(score.tier2_kin_penalty),
            "tier3": float(score.tier3_tba_penalty),
            "static": float(score.static_cost),
            "S": float(score.fitness_score_S),
            "rm_state": rm_state,
            "moves": float(self.moves_taken),
            "n_components": float(len(self.play.board.components)),
            "n_routes": float(len(self.play.board.routes)),
            "cut": float(score.tba_result.cut_progress_ratio),
            "breaches": float(score.tba_result.hot_breaches),
        }

    def _quick_score(self) -> ScoreBreakdown:
        assert self.play is not None
        return self.evaluator.evaluate(
            self.play.board, self.task.ulsc, self.task.scenario, "env"
        )

    def legal_moves(self) -> List[Tuple[str, Any]]:
        """Return list of (kind, payload) legal actions."""
        assert self.play is not None
        moves: List[Tuple[str, Any]] = []
        board = self.play.board

        # Add catalog operators not yet placed (by template name / unique comp id)
        for name, factory in self.task.catalog:
            if name in self._catalog_used:
                continue
            # Peek id
            probe = factory()
            if probe.comp_id not in board.components:
                moves.append(("add", name))

        # Compatible routes (strict)
        offers = []
        needs = []
        for comp in board.components.values():
            for iface in comp.offers.values():
                offers.append(iface.full_id)
            for iface in comp.needs.values():
                if iface.connected_route_id is None:
                    needs.append(iface.full_id)
        for o in offers:
            for n in needs:
                reasons = board.check_route_compatibility(o, n, require_exact_transfer=True)
                if not reasons:
                    # Avoid duplicate route
                    rid = f"{o}-->{n}"
                    if rid not in board.routes:
                        moves.append(("connect", (o, n)))

        moves.append(("finalize", None))
        return moves

    def step(self, action_index: int) -> StepResult:
        assert self.play is not None
        legal = self.legal_moves()
        if not legal:
            return StepResult(self.observe(), -1.0, True, {"error": "no_legal_moves"})
        action_index = max(0, min(action_index, len(legal) - 1))
        kind, payload = legal[action_index]

        reward = -self.step_penalty
        info: Dict[str, Any] = {"action": kind, "payload": payload}
        done = False

        try:
            if kind == "add":
                name = payload
                factory = dict(self.task.catalog)[name]
                comp = factory()
                self.play.apply(AddOperator(comp))
                self._catalog_used.add(name)
                reward -= float(comp.static_cost) * 0.1
            elif kind == "connect":
                src, tgt = payload
                self.play.apply(AddRoute(src, tgt, strict=True))
            elif kind == "finalize":
                self.play.apply(FinalizeBoard())
                done = True
        except IllegalMoveError as exc:
            reward -= 1.0
            info["illegal"] = str(exc)
            self.moves_taken += 1
            return StepResult(self.observe(), reward, self.moves_taken >= self.task.max_moves, info)

        self.moves_taken += 1
        score = self._quick_score()

        # Dense RM pulse delta
        rm_total = score.tba_result.total_rm_reward
        reward += 0.01 * (rm_total - self._last_rm_reward)
        self._last_rm_reward = rm_total

        # Potential shaping on structural tiers
        reward += 0.001 * (100.0 - score.tier1_struct_penalty - score.tier2_kin_penalty)

        if score.is_winning_play:
            reward += 50.0 - score.residual_cost
            done = True
            info["win"] = True
        elif score.tba_result.rm_state_trace and score.tba_result.rm_state_trace[-1] == RMState.BREACH:
            # Absorbing breach after finalize-like evaluation on partial boards is common;
            # only terminate early if finalized or many breaches
            if self.play.finalized or score.tba_result.hot_breaches >= 5:
                reward -= 20.0
                done = True
                info["breach"] = True

        if self.moves_taken >= self.task.max_moves:
            done = True
            if not score.is_winning_play:
                reward -= 10.0 + 0.001 * score.total_cost_J

        if done and kind == "finalize" and not score.is_winning_play:
            reward -= 0.001 * score.total_cost_J

        info["score"] = score
        info["n_legal"] = len(legal)
        return StepResult(self.observe(), reward, done, info)
