"""
board.py
Integration Game Board and resultant coupled system RSY(Board).
Routes enforce Color, Representation, Provenance predicates, and Push/Pull compatibility.
Offers may fan-out to multiple Needs (non-destructive PUSH copy).
"""
from __future__ import annotations

import copy
from typing import Dict, List, Optional, Tuple

from .primitives import Carrier, Message, MessageShape, TransferMode
from .interfaces import Interface, Route
from .components import (
    CacheStoreBlock,
    ConsumerBoundary,
    ProducerBoundary,
    PumpBlock,
    WymorianComponent,
)


class CompatibilityError(ValueError):
    """Raised when a proposed route cannot legally transfer."""


class Board:
    def __init__(self, name: str):
        self.name = name
        self.components: Dict[str, WymorianComponent] = {}
        self.routes: Dict[str, Route] = {}
        self._execution_order: List[str] = []

    def clone(self, new_name: Optional[str] = None) -> "Board":
        """Deep-ish clone of structure (fresh component instances via deepcopy)."""
        cloned = copy.deepcopy(self)
        if new_name:
            cloned.name = new_name
        return cloned

    def add_component(self, comp: WymorianComponent) -> WymorianComponent:
        if comp.comp_id in self.components:
            raise ValueError(f"Component '{comp.comp_id}' already exists on board.")
        self.components[comp.comp_id] = comp
        self._execution_order.append(comp.comp_id)
        return comp

    def remove_component(self, comp_id: str) -> None:
        if comp_id not in self.components:
            raise ValueError(f"Unknown component '{comp_id}'")
        # Remove incident routes
        to_remove = [
            rid
            for rid, r in self.routes.items()
            if r.source_if.startswith(comp_id + ".") or r.target_if.startswith(comp_id + ".")
        ]
        for rid in to_remove:
            self._disconnect_route(rid)
        del self.components[comp_id]
        self._execution_order = [c for c in self._execution_order if c != comp_id]

    def get_interface(self, full_if_id: str) -> Interface:
        comp_id, if_name = full_if_id.split(".", 1)
        return self.components[comp_id].interfaces[if_name]

    def check_route_compatibility(
        self,
        source_if_id: str,
        target_if_id: str,
        require_exact_transfer: bool = True,
    ) -> List[str]:
        """Return list of incompatibility reasons (empty => OK for transfer)."""
        reasons: List[str] = []
        src_if = self.get_interface(source_if_id)
        tgt_if = self.get_interface(target_if_id)
        if not src_if.is_offer:
            reasons.append(f"source '{source_if_id}' is not an Offer")
        if not tgt_if.is_need:
            reasons.append(f"target '{target_if_id}' is not a Need")
        if reasons:
            return reasons
        if src_if.mode != tgt_if.mode:
            reasons.append(f"mode mismatch {src_if.mode.value}->{tgt_if.mode.value}")
        if not src_if.shape.compatible_with(tgt_if.shape):
            reasons.append("shape/color/representation incompatibility")
        # Provenance predicates are on Need shape; Offer shape may declare min_trust as capability floor
        # Static check: offer's declared min_trust should be >= need's required min_trust when known
        if tgt_if.shape.min_trust_score > 0.0:
            # At connect-time we only know shape contracts; runtime still checks message provenance
            if src_if.shape.min_trust_score < tgt_if.shape.min_trust_score:
                # Soft warning for static capability: allow connect but note potential Tier1 risk
                # For strict boards we treat as mismatch when require_exact and offer advertises lower floor
                if require_exact_transfer and src_if.shape.min_trust_score > 0.0:
                    reasons.append(
                        f"provenance trust floor {src_if.shape.min_trust_score} "
                        f"< need {tgt_if.shape.min_trust_score}"
                    )
        if tgt_if.shape.required_assurance and src_if.shape.required_assurance:
            if src_if.shape.required_assurance != tgt_if.shape.required_assurance:
                reasons.append("assurance level mismatch")
        return reasons

    def connect(
        self,
        source_if_id: str,
        target_if_id: str,
        carrier: Carrier = Carrier.IN_PROCESS,
        carrier_cost: Optional[float] = None,
        allow_incompatible: bool = True,
        strict: bool = False,
    ) -> Route:
        """
        Add Offer→Need route.
        Progressive demos may wire mismatches (`allow_incompatible=True`, default).
        Set `strict=True` (or `allow_incompatible=False`) to reject incompatible routes.
        """
        if strict:
            allow_incompatible = False
        # carrier_cost retained for backward compat; prefer Carrier enum
        if carrier_cost is not None:
            if carrier_cost >= 3.0:
                carrier = Carrier.IPC_SERIALIZED
            elif carrier_cost >= 0.5:
                carrier = Carrier.GENERIC_TREE
            else:
                carrier = Carrier.IN_PROCESS

        src_if = self.get_interface(source_if_id)
        tgt_if = self.get_interface(target_if_id)
        if not src_if.is_offer:
            raise ValueError(f"Route source '{source_if_id}' must be an Offer interface.")
        if not tgt_if.is_need:
            raise ValueError(f"Route target '{target_if_id}' must be a Need interface.")

        reasons = self.check_route_compatibility(source_if_id, target_if_id)
        # Mode/color mismatches are the teaching cases — allow_incompatible for demos
        if reasons and not allow_incompatible:
            # Always allow connect for progressive pedagogy if only mode/color differ;
            # still raise on Offer/Need direction errors (already handled).
            # Strict mode: raise CompatibilityError
            raise CompatibilityError(
                f"Cannot connect {source_if_id} → {target_if_id}: " + "; ".join(reasons)
            )

        if tgt_if.connected_route_id is not None:
            # Replace previous route into this Need
            self._disconnect_route(tgt_if.connected_route_id)

        route_id = f"{source_if_id}-->{target_if_id}"
        route = Route(
            route_id=route_id,
            source_if=source_if_id,
            target_if=target_if_id,
            carrier=carrier,
        )
        self.routes[route_id] = route
        if route_id not in (src_if.connected_route_ids or []):
            src_if.connected_route_ids = list(src_if.connected_route_ids or []) + [route_id]
        tgt_if.connected_route_id = route_id
        return route

    def _disconnect_route(self, route_id: str) -> None:
        if route_id not in self.routes:
            return
        route = self.routes.pop(route_id)
        src_if = self.get_interface(route.source_if)
        tgt_if = self.get_interface(route.target_if)
        src_if.connected_route_ids = [r for r in (src_if.connected_route_ids or []) if r != route_id]
        if tgt_if.connected_route_id == route_id:
            tgt_if.connected_route_id = None

    @property
    def producers(self) -> List[ProducerBoundary]:
        return [c for c in self.components.values() if isinstance(c, ProducerBoundary)]

    @property
    def consumers(self) -> List[ConsumerBoundary]:
        return [c for c in self.components.values() if isinstance(c, ConsumerBoundary)]

    @property
    def interior_blocks(self) -> List[WymorianComponent]:
        # Honor deterministic execution order
        return [
            self.components[cid]
            for cid in self._execution_order
            if cid in self.components and not self.components[cid].is_boundary
        ]

    def simulate(
        self,
        scenario_inputs: Dict[int, Dict[str, Message]],
        horizon: int,
    ) -> Dict[str, Dict[int, Message]]:
        for comp in self.components.values():
            comp.reset()

        for tick in range(horizon):
            env_at_tick = scenario_inputs.get(tick, {})
            for prod in self.producers:
                prod.step(tick, env_at_tick)
            # Also step SourceBlocks that are interior but produce spontaneously
            self._propagate_routes(tick)
            for block in self.interior_blocks:
                block.step(tick)
                self._propagate_routes(tick)
            for cons in self.consumers:
                cons.step(tick)

        return {
            cons.full_need_id: dict(cons.state.get("received_history", {}))
            for cons in self.consumers
        }

    def _propagate_routes(self, tick: int) -> None:
        for route in list(self.routes.values()):
            src_if = self.get_interface(route.source_if)
            tgt_if = self.get_interface(route.target_if)
            src_comp = self.components[src_if.component_id]
            tgt_comp = self.components[tgt_if.component_id]

            if not self._is_route_compatible(src_if, tgt_if):
                continue

            if src_if.mode == TransferMode.PUSH and tgt_if.mode == TransferMode.PUSH:
                if src_if.outbox is not None:
                    msg = src_if.outbox
                    if not msg.satisfies_provenance(tgt_if.shape):
                        continue
                    # Fan-out: copy to target; clear outbox only after all fan-out targets served
                    tgt_if.inbox = msg
                    fan_routes = src_if.connected_route_ids or [route.route_id]
                    # Mark this route served this tick via transient tag on message id
                    served = getattr(src_if, "_served_routes_tick", None)
                    if served is None or served[0] != tick:
                        src_if._served_routes_tick = (tick, set())  # type: ignore[attr-defined]
                    src_if._served_routes_tick[1].add(route.route_id)  # type: ignore[attr-defined]
                    if src_if._served_routes_tick[1] >= set(fan_routes):  # type: ignore[attr-defined]
                        src_if.outbox = None

            elif src_if.mode == TransferMode.PULL and tgt_if.mode == TransferMode.PULL:
                wants_pull = True
                if hasattr(tgt_comp, "wants_to_pull"):
                    wants_pull = tgt_comp.wants_to_pull(tick)
                if wants_pull:
                    if isinstance(src_comp, CacheStoreBlock):
                        pulled_msg = src_comp.on_pulled()
                    else:
                        pulled_msg = src_if.outbox
                    if pulled_msg is not None and pulled_msg.satisfies_provenance(tgt_if.shape):
                        tgt_if.inbox = pulled_msg

    @staticmethod
    def _is_route_compatible(src_if: Interface, tgt_if: Interface) -> bool:
        if src_if.mode != tgt_if.mode:
            return False
        if not src_if.shape.compatible_with(tgt_if.shape):
            return False
        return True

    def unmet_needs(self) -> List[str]:
        ids = []
        for comp in self.components.values():
            for need in comp.needs.values():
                if need.connected_route_id is None:
                    ids.append(need.full_id)
                else:
                    route = self.routes.get(need.connected_route_id)
                    if route is None:
                        ids.append(need.full_id)
                    else:
                        src = self.get_interface(route.source_if)
                        if not self._is_route_compatible(src, need):
                            ids.append(need.full_id)
        return ids
