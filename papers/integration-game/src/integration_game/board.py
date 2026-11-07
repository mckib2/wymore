"""
board.py
Integration Game Board and resultant coupled system RSY(Board).
Routes enforce Color, Representation, Provenance predicates, and Push/Pull compatibility.
Includes topological execution ordering and live-frontier reachability analysis.
"""
from __future__ import annotations

import copy
from typing import Dict, List, Optional, Set, Tuple

from .config import CarrierCostConfig, DEFAULT_CONFIG
from .primitives import Carrier, Message, TransferMode
from .interfaces import Interface, Route
from .components import (
    CacheStoreBlock,
    ConsumerBoundary,
    ProducerBoundary,
    PumpBlock,
    SourceBlock,
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
        """Deep clone of board structure and component configurations."""
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
        if tgt_if.shape.min_trust_score > 0.0:
            if src_if.shape.min_trust_score < tgt_if.shape.min_trust_score:
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
        carrier_config: Optional[CarrierCostConfig] = None,
    ) -> Route:
        """
        Add Offer→Need route.
        Progressive demos may wire mismatches (`allow_incompatible=True`, default).
        Set `strict=True` (or `allow_incompatible=False`) to reject incompatible routes.
        """
        if strict:
            allow_incompatible = False
        c_cfg = carrier_config or DEFAULT_CONFIG.carrier_costs
        if carrier_cost is not None:
            if carrier_cost >= c_cfg.ipc_threshold:
                carrier = Carrier.IPC_SERIALIZED
            elif carrier_cost >= c_cfg.generic_tree_threshold:
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
        if reasons and not allow_incompatible:
            raise CompatibilityError(
                f"Cannot connect {source_if_id} → {target_if_id}: " + "; ".join(reasons)
            )

        if tgt_if.connected_route_id is not None:
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
        """Return interior blocks in topological causal order (with insertion order tie-break)."""
        interior_ids = [
            cid
            for cid in self._execution_order
            if cid in self.components
            and not isinstance(self.components[cid], (ProducerBoundary, ConsumerBoundary))
        ]
        if len(interior_ids) <= 1:
            return [self.components[cid] for cid in interior_ids]

        id_set = set(interior_ids)
        order_index = {cid: idx for idx, cid in enumerate(interior_ids)}
        adj: Dict[str, List[str]] = {cid: [] for cid in interior_ids}
        in_deg: Dict[str, int] = {cid: 0 for cid in interior_ids}

        for r in self.routes.values():
            u = r.source_if.split(".", 1)[0]
            v = r.target_if.split(".", 1)[0]
            if u in id_set and v in id_set and u != v:
                if v not in adj[u]:
                    adj[u].append(v)
                    in_deg[v] += 1

        ready = [cid for cid in interior_ids if in_deg[cid] == 0]
        ready.sort(key=lambda c: order_index[c])
        sorted_ids: List[str] = []

        while len(sorted_ids) < len(interior_ids):
            if not ready:
                remaining = [cid for cid in interior_ids if cid not in sorted_ids]
                ready.append(remaining[0])
            curr = ready.pop(0)
            if curr in sorted_ids:
                continue
            sorted_ids.append(curr)
            for nxt in adj[curr]:
                if nxt not in sorted_ids:
                    in_deg[nxt] -= 1
                    if in_deg[nxt] <= 0 and nxt not in ready:
                        ready.append(nxt)
                        ready.sort(key=lambda c: order_index[c])

        return [self.components[cid] for cid in sorted_ids]

    def live_offers(self) -> List[Interface]:
        """
        Compute the set of Offer interfaces grounded in a genuine data source
        (ProducerBoundary, SourceBlock, or boundary component with Offers) via
        connected upstream routes. Prevents disconnected interior blocks from
        spoofing Tier-1 semantic proximity (Axiom A2).
        """
        live_comp_ids: Set[str] = set()
        for cid, comp in self.components.items():
            if isinstance(comp, (ProducerBoundary, SourceBlock)) or (comp.is_boundary and len(comp.offers) > 0):
                live_comp_ids.add(cid)

        changed = True
        while changed:
            changed = False
            for cid, comp in self.components.items():
                if cid in live_comp_ids or len(comp.offers) == 0:
                    continue
                # An interior component's offers become live if at least one of its Needs
                # is connected to an Offer on an already-live component.
                has_live_input = False
                for need_if in comp.needs.values():
                    if need_if.connected_route_id and need_if.connected_route_id in self.routes:
                        r = self.routes[need_if.connected_route_id]
                        src_cid = r.source_if.split(".", 1)[0]
                        if src_cid in live_comp_ids:
                            has_live_input = True
                            break
                if has_live_input:
                    live_comp_ids.add(cid)
                    changed = True

        result: List[Interface] = []
        for cid in self._execution_order:
            if cid in live_comp_ids and cid in self.components:
                result.extend(self.components[cid].offers.values())
        return result

    def simulate(
        self,
        scenario_inputs: Dict[int, Dict[str, Message]],
        horizon: int,
    ) -> Dict[str, Dict[int, Message]]:
        for comp in self.components.values():
            comp.reset()

        for tick in range(horizon):
            env_at_tick = scenario_inputs.get(tick, {})
            pulled_routes_this_tick: Set[str] = set()

            # 1. Step boundary producers and propagate their PUSH emissions
            for prod in self.producers:
                prod.step(tick, env_at_tick)
                self._propagate_push_from(prod.comp_id, tick)

            # 2. Step interior blocks in topological order
            for block in self.interior_blocks:
                self._propagate_pull_into(block.comp_id, tick, pulled_routes_this_tick)
                block.step(tick, env_at_tick)
                self._propagate_push_from(block.comp_id, tick)

            # 3. Step boundary consumers (pulling first if in PULL mode)
            for cons in self.consumers:
                self._propagate_pull_into(cons.comp_id, tick, pulled_routes_this_tick)
                cons.step(tick, env_at_tick)

        return {
            cons.full_need_id: dict(cons.state.get("received_history", {}))
            for cons in self.consumers
        }

    def _propagate_push_from(self, src_comp_id: str, tick: int) -> None:
        """Propagate PUSH offers originating from `src_comp_id` along all compatible fan-out routes."""
        src_comp = self.components[src_comp_id]
        for src_if in src_comp.offers.values():
            if src_if.mode != TransferMode.PUSH or src_if.outbox is None:
                continue
            msg = src_if.outbox
            fan_routes = [rid for rid in (src_if.connected_route_ids or []) if rid in self.routes]
            for rid in fan_routes:
                route = self.routes[rid]
                tgt_if = self.get_interface(route.target_if)
                if not self._is_route_compatible(src_if, tgt_if):
                    continue
                if not msg.satisfies_provenance(tgt_if.shape):
                    continue
                tgt_if.inbox = msg
            # Clear outbox once fan-out propagation completes for this source interface
            if fan_routes:
                src_if.outbox = None

    def _propagate_pull_into(
        self,
        tgt_comp_id: str,
        tick: int,
        pulled_routes_this_tick: Set[str],
    ) -> None:
        """Propagate PULL requests into `tgt_comp_id` at most once per route per tick."""
        tgt_comp = self.components[tgt_comp_id]
        for tgt_if in tgt_comp.needs.values():
            if tgt_if.mode != TransferMode.PULL or tgt_if.connected_route_id is None:
                continue
            rid = tgt_if.connected_route_id
            if rid in pulled_routes_this_tick or rid not in self.routes:
                continue
            route = self.routes[rid]
            src_if = self.get_interface(route.source_if)
            src_comp = self.components[src_if.component_id]

            if not self._is_route_compatible(src_if, tgt_if):
                continue

            wants_pull = True
            if hasattr(tgt_comp, "wants_to_pull"):
                wants_pull = tgt_comp.wants_to_pull(tick)
            if wants_pull:
                pulled_routes_this_tick.add(rid)
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
