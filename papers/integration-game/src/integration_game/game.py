"""
game.py
First-class Play / Move API for offline board synthesis (MDP action space).
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Union

from .board import Board, CompatibilityError
from .components import WymorianComponent
from .primitives import Carrier, Message
from .scoring import BoardEvaluator, ScoreBreakdown
from .ulsc import UniversalLSC


class IllegalMoveError(ValueError):
    pass


@dataclass(frozen=True)
class AddOperator:
    component: WymorianComponent


@dataclass(frozen=True)
class AddRoute:
    source_if: str
    target_if: str
    carrier: Carrier = Carrier.IN_PROCESS
    strict: bool = True


@dataclass(frozen=True)
class SetParameters:
    comp_id: str
    params: Dict[str, Any]


@dataclass(frozen=True)
class RemoveOperator:
    comp_id: str


@dataclass(frozen=True)
class RemoveRoute:
    route_id: str


@dataclass(frozen=True)
class FinalizeBoard:
    pass


Move = Union[AddOperator, AddRoute, SetParameters, RemoveOperator, RemoveRoute, FinalizeBoard]


@dataclass
class Play:
    """
    Mutable play state: board + move history + finalize flag.
    Supports cloneable snapshots for progressive agent trajectories.
    """
    board: Board
    history: List[Move] = field(default_factory=list)
    finalized: bool = False

    @classmethod
    def new(cls, name: str) -> "Play":
        return cls(board=Board(name))

    def clone(self, new_name: Optional[str] = None) -> "Play":
        b = self.board.clone(new_name or self.board.name)
        return Play(board=b, history=list(self.history), finalized=self.finalized)

    def apply(self, move: Move) -> "Play":
        if self.finalized:
            raise IllegalMoveError("Play is already finalized; no further moves allowed.")
        if isinstance(move, AddOperator):
            try:
                self.board.add_component(move.component)
            except ValueError as exc:
                raise IllegalMoveError(str(exc)) from exc
        elif isinstance(move, AddRoute):
            try:
                self.board.connect(
                    move.source_if,
                    move.target_if,
                    carrier=move.carrier,
                    strict=move.strict,
                    allow_incompatible=not move.strict,
                )
            except (ValueError, CompatibilityError) as exc:
                raise IllegalMoveError(str(exc)) from exc
        elif isinstance(move, SetParameters):
            if move.comp_id not in self.board.components:
                raise IllegalMoveError(f"Unknown component '{move.comp_id}'")
            comp = self.board.components[move.comp_id]
            for k, v in move.params.items():
                if k == "active_index" and hasattr(comp, "set_active"):
                    comp.set_active(int(v))
                elif hasattr(comp, k):
                    setattr(comp, k, v)
                elif isinstance(comp.state, dict):
                    comp.state[k] = v
                else:
                    raise IllegalMoveError(f"Cannot set parameter '{k}' on '{move.comp_id}'")
        elif isinstance(move, RemoveOperator):
            try:
                self.board.remove_component(move.comp_id)
            except ValueError as exc:
                raise IllegalMoveError(str(exc)) from exc
        elif isinstance(move, RemoveRoute):
            if move.route_id not in self.board.routes:
                raise IllegalMoveError(f"Unknown route '{move.route_id}'")
            self.board._disconnect_route(move.route_id)
        elif isinstance(move, FinalizeBoard):
            self.finalized = True
        else:
            raise IllegalMoveError(f"Unknown move type: {type(move)}")
        self.history.append(move)
        return self

    def unmet_needs(self) -> List[str]:
        return self.board.unmet_needs()

    def evaluate(
        self,
        ulsc: UniversalLSC,
        scenario_inputs: Dict[int, Dict[str, Message]],
        snapshot_label: str = "Play",
        evaluator: Optional[BoardEvaluator] = None,
    ) -> ScoreBreakdown:
        ev = evaluator or BoardEvaluator()
        return ev.evaluate(self.board, ulsc, scenario_inputs, snapshot_label)
