"""
interfaces.py
Local-visibility Interfaces with Need-XOR-Offer exclusivity and directed Routes.
Carrier is a Route transport attribute (cost), not a color axis.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Optional

from .primitives import Carrier, Color, Message, MessageShape, ResultCode, TransferMode


@dataclass(frozen=True)
class NeedSpec:
    """What an input Interface requires (color, dynamics, representation, provenance)."""
    shape: MessageShape
    mode: TransferMode

    @property
    def primary_color(self) -> Color:
        return self.shape.primary_color


@dataclass(frozen=True)
class OfferSpec:
    """What an output Interface produces."""
    shape: MessageShape
    mode: TransferMode
    velocity: float = 1.0

    def __post_init__(self) -> None:
        if self.mode == TransferMode.PULL and self.velocity != 0.0:
            object.__setattr__(self, "velocity", 0.0)
        elif self.mode == TransferMode.PUSH and self.velocity <= 0.0:
            object.__setattr__(self, "velocity", 1.0)

    @property
    def primary_color(self) -> Color:
        return self.shape.primary_color


@dataclass
class Interface:
    """
    Strict Need-XOR-Offer exclusivity:
      Need => route toward IF; Offer => route away from IF.
    """
    name: str
    component_id: str
    need: Optional[NeedSpec] = None
    offer: Optional[OfferSpec] = None
    connected_route_ids: Optional[list] = None  # Offer may fan-out to many Needs
    connected_route_id: Optional[str] = None  # Primary / Need side single connection
    inbox: Optional[Message] = None
    outbox: Optional[Message] = None
    last_result: ResultCode = ResultCode.SUCCESS

    def __post_init__(self) -> None:
        if (self.need is None) == (self.offer is None):
            raise ValueError(
                f"Interface '{self.full_id}' violates Need-XOR-Offer exclusivity: "
                "must specify exactly one of `need` or `offer`."
            )
        if self.connected_route_ids is None:
            self.connected_route_ids = []

    @property
    def full_id(self) -> str:
        return f"{self.component_id}.{self.name}"

    @property
    def is_need(self) -> bool:
        return self.need is not None

    @property
    def is_offer(self) -> bool:
        return self.offer is not None

    @property
    def mode(self) -> TransferMode:
        return self.need.mode if self.is_need else self.offer.mode  # type: ignore[union-attr]

    @property
    def shape(self) -> MessageShape:
        return self.need.shape if self.is_need else self.offer.shape  # type: ignore[union-attr]


@dataclass(frozen=True)
class Route:
    """
    Directed Offer -> Need edge. Transports messages without changing Color / ρ / values.
    `carrier` contributes only to static transport cost.
    """
    route_id: str
    source_if: str
    target_if: str
    carrier: Carrier = Carrier.IN_PROCESS

    @property
    def carrier_cost(self) -> float:
        return self.carrier.cost
