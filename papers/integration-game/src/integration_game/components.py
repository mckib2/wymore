"""
components.py
Semantically-enabled Wymorian DSYSTEM components and the full technology catalog T.
All default static costs and intrinsic parameters are sourced from CatalogCostConfig.
"""
from __future__ import annotations

from typing import Any, Callable, Dict, List, Optional, Sequence, Tuple, Union

from .config import CatalogCostConfig, DEFAULT_CONFIG
from .primitives import (
    AggregationKind,
    Color,
    Dynamics,
    Field,
    Message,
    MessageShape,
    Provenance,
    Representation,
    ResultCode,
    TransferMode,
)
from .interfaces import Interface, NeedSpec, OfferSpec


class WymorianComponent:
    """Z = (S_Z, IF_need, IF_offer, transition, readout, static_cost)."""

    def __init__(self, comp_id: str, static_cost: float = 0.0, is_boundary: bool = False):
        self.comp_id = comp_id
        self.static_cost = static_cost
        self.is_boundary = is_boundary
        self.interfaces: Dict[str, Interface] = {}
        self.state: Dict[str, Any] = {}
        self.disruption_events: List[Tuple[int, ResultCode, str]] = []
        self.info_loss_events: List[Tuple[int, float, str]] = []
        self.latency_events: List[Tuple[int, float, str]] = []

    def add_need(self, name: str, shape: MessageShape, mode: TransferMode) -> Interface:
        iface = Interface(name=name, component_id=self.comp_id, need=NeedSpec(shape=shape, mode=mode))
        self.interfaces[name] = iface
        return iface

    def add_offer(
        self,
        name: str,
        shape: MessageShape,
        mode: TransferMode,
        velocity: float = 1.0,
    ) -> Interface:
        iface = Interface(
            name=name,
            component_id=self.comp_id,
            offer=OfferSpec(shape=shape, mode=mode, velocity=velocity),
        )
        self.interfaces[name] = iface
        return iface

    @property
    def needs(self) -> Dict[str, Interface]:
        return {k: v for k, v in self.interfaces.items() if v.is_need}

    @property
    def offers(self) -> Dict[str, Interface]:
        return {k: v for k, v in self.interfaces.items() if v.is_offer}

    def reset(self) -> None:
        for iface in self.interfaces.values():
            iface.inbox = None
            iface.outbox = None
            iface.last_result = ResultCode.SUCCESS
        self.disruption_events.clear()
        self.info_loss_events.clear()
        self.latency_events.clear()

    def step(self, tick: int, env_inputs: Optional[Dict[str, Message]] = None) -> None:
        raise NotImplementedError

    def wants_to_pull(self, tick: int) -> bool:
        return False


# ---------------------------------------------------------------------------
# Boundaries
# ---------------------------------------------------------------------------

class ProducerBoundary(WymorianComponent):
    def __init__(
        self,
        comp_id: str,
        offer_name: str,
        color: Color,
        mode: TransferMode = TransferMode.PUSH,
        rep: Representation = Representation.NATIVE_STRUCT,
        reps: Optional[Tuple[Representation, ...]] = None,
        slot: str = "val",
        shape: Optional[MessageShape] = None,
        trust_score: float = 1.0,
        assurance_level: str = "UNVERIFIED",
        velocity: Optional[float] = None,
    ):
        super().__init__(comp_id=comp_id, static_cost=0.0, is_boundary=True)
        self.offer_name = offer_name
        self.color = color
        self.rep = rep
        self.slot = slot
        self.trust_score = trust_score
        self.assurance_level = assurance_level
        allowed = reps if reps is not None else (rep,)
        offer_shape = shape or MessageShape.single(color=color, slot=slot, reps=allowed)
        nom_vel = velocity if velocity is not None else (1.0 if mode == TransferMode.PUSH else 0.0)
        self.add_offer(
            name=offer_name,
            shape=offer_shape,
            mode=mode,
            velocity=nom_vel,
        )

    def reset(self) -> None:
        super().reset()
        self.state = {"stored_pull_msg": None}

    def step(self, tick: int, env_inputs: Optional[Dict[str, Message]] = None) -> None:
        iface = self.interfaces[self.offer_name]
        iface.outbox = None
        if env_inputs and self.full_offer_id in env_inputs:
            raw_msg = env_inputs[self.full_offer_id]
            if iface.mode == TransferMode.PUSH:
                iface.outbox = raw_msg
            else:
                self.state["stored_pull_msg"] = raw_msg
                iface.outbox = raw_msg
        elif iface.mode == TransferMode.PULL and self.state.get("stored_pull_msg") is not None:
            iface.outbox = self.state["stored_pull_msg"]

    @property
    def full_offer_id(self) -> str:
        return f"{self.comp_id}.{self.offer_name}"


class ConsumerBoundary(WymorianComponent):
    def __init__(
        self,
        comp_id: str,
        need_name: str,
        shape: MessageShape,
        mode: TransferMode = TransferMode.PUSH,
        pull_schedule: Optional[Callable[[int], bool]] = None,
    ):
        super().__init__(comp_id=comp_id, static_cost=0.0, is_boundary=True)
        self.need_name = need_name
        self.pull_schedule = pull_schedule or (lambda t: True)
        self.add_need(name=need_name, shape=shape, mode=mode)

    def reset(self) -> None:
        super().reset()
        self.state = {"received_history": {}}

    def wants_to_pull(self, tick: int) -> bool:
        iface = self.interfaces[self.need_name]
        return iface.mode == TransferMode.PULL and self.pull_schedule(tick)

    def step(self, tick: int, env_inputs: Optional[Dict[str, Message]] = None) -> None:
        iface = self.interfaces[self.need_name]
        if iface.inbox is not None:
            self.state["received_history"][tick] = iface.inbox
            iface.inbox = None

    @property
    def full_need_id(self) -> str:
        return f"{self.comp_id}.{self.need_name}"


class SourceBlock(WymorianComponent):
    """Generates declared-color fields without upstream (constants, clocks)."""

    def __init__(
        self,
        comp_id: str,
        color: Color,
        value_fn: Callable[[int], Any],
        mode: TransferMode = TransferMode.PUSH,
        period: int = 1,
        rep: Representation = Representation.NATIVE_STRUCT,
        static_cost: Optional[float] = None,
        slot: str = "val",
        cost_config: Optional[CatalogCostConfig] = None,
    ):
        cfg = cost_config or DEFAULT_CONFIG.catalog_costs
        super().__init__(
            comp_id=comp_id,
            static_cost=static_cost if static_cost is not None else cfg.source,
        )
        self.color = color
        self.value_fn = value_fn
        self.period = max(1, period)
        self.rep = rep
        self.slot = slot
        self.add_offer(
            "out",
            MessageShape.single(color, slot=slot, reps=(rep,)),
            mode=mode,
            velocity=(1.0 / self.period) if mode == TransferMode.PUSH else 0.0,
        )

    def step(self, tick: int, env_inputs: Optional[Dict[str, Message]] = None) -> None:
        out_if = self.interfaces["out"]
        out_if.outbox = None
        if tick % self.period == 0:
            f = Field(
                value=self.value_fn(tick),
                color=self.color,
                dynamics=Dynamics(
                    position=out_if.full_id,
                    velocity=(1.0 / self.period) if out_if.mode == TransferMode.PUSH else 0.0,
                ),
                representation=self.rep,
                provenance=Provenance(sources=(self.comp_id,), timestamp_tick=tick),
            )
            out_if.outbox = Message.single(f, slot=self.slot)


class SinkBlock(WymorianComponent):
    """Terminates unused offers (observability / disposal)."""

    def __init__(
        self,
        comp_id: str,
        shape: MessageShape,
        mode: TransferMode = TransferMode.PUSH,
        static_cost: Optional[float] = None,
        cost_config: Optional[CatalogCostConfig] = None,
    ):
        cfg = cost_config or DEFAULT_CONFIG.catalog_costs
        super().__init__(
            comp_id=comp_id,
            static_cost=static_cost if static_cost is not None else cfg.sink,
        )
        self.add_need("in", shape, mode=mode)

    def reset(self) -> None:
        super().reset()
        self.state = {"consumed": []}

    def step(self, tick: int, env_inputs: Optional[Dict[str, Message]] = None) -> None:
        in_if = self.interfaces["in"]
        if in_if.inbox is not None:
            self.state["consumed"].append((tick, in_if.inbox))
            in_if.inbox = None


# ---------------------------------------------------------------------------
# Recolor / Representation
# ---------------------------------------------------------------------------

class RecolorBlock(WymorianComponent):
    def __init__(
        self,
        comp_id: str,
        in_color: Color,
        out_color: Color,
        value_fn: Callable[[Any], Any] = lambda x: x,
        mode: TransferMode = TransferMode.PUSH,
        rep: Representation = Representation.NATIVE_STRUCT,
        info_loss: float = 0.0,
        static_cost: Optional[float] = None,
        slot: str = "val",
        out_slot: Optional[str] = None,
        latency: float = 0.0,
        cost_config: Optional[CatalogCostConfig] = None,
    ):
        cfg = cost_config or DEFAULT_CONFIG.catalog_costs
        if static_cost is None:
            cost = 0.0
            if in_color.C != out_color.C:
                cost += cfg.recolor_c
            if in_color.L != out_color.L:
                cost += cfg.recolor_l
            if in_color.P != out_color.P:
                cost += cfg.recolor_p
            static_cost = max(cfg.recolor_min, round(cost, 2))
        super().__init__(comp_id=comp_id, static_cost=static_cost)
        self.in_color = in_color
        self.out_color = out_color
        self.value_fn = value_fn
        self.info_loss = info_loss
        self.slot = slot
        self.out_slot = out_slot or slot
        self.latency = latency
        self.add_need("in", MessageShape.single(in_color, slot=self.slot, reps=(rep,)), mode=mode)
        self.add_offer(
            "out",
            MessageShape.single(out_color, slot=self.out_slot, reps=(rep,)),
            mode=mode,
            velocity=1.0 if mode == TransferMode.PUSH else 0.0,
        )

    def wants_to_pull(self, tick: int) -> bool:
        return self.interfaces["in"].mode == TransferMode.PULL

    def step(self, tick: int, env_inputs: Optional[Dict[str, Message]] = None) -> None:
        in_if = self.interfaces["in"]
        out_if = self.interfaces["out"]
        out_if.outbox = None
        if in_if.inbox is not None:
            msg_in = in_if.inbox
            f_in = msg_in.first_field(self.slot)
            in_if.inbox = None
            try:
                new_val = self.value_fn(f_in.value)
                if self.info_loss > 0.0:
                    self.info_loss_events.append((tick, self.info_loss, f"{self.comp_id} precision loss"))
                if self.latency > 0.0:
                    self.latency_events.append((tick, self.latency, self.comp_id))
                f_out = Field(
                    value=new_val,
                    color=self.out_color,
                    dynamics=Dynamics(
                        position=out_if.full_id,
                        velocity=1.0 if out_if.mode == TransferMode.PUSH else 0.0,
                    ),
                    representation=f_in.representation,
                    provenance=f_in.provenance.append_op(self.comp_id, tick),
                )
                out_if.outbox = Message.single(f_out, slot=self.out_slot, key=msg_in.correlation_key)
            except Exception as exc:
                self.disruption_events.append((tick, ResultCode.ERROR, str(exc)))


class RepresentationBridgeBlock(WymorianComponent):
    """Transcode_Rep: change ρ without altering (C,L,P). Supports single-slot or full RECORD shapes."""

    def __init__(
        self,
        comp_id: str,
        color: Optional[Color],
        in_rep: Representation,
        out_rep: Representation,
        mode: TransferMode = TransferMode.PUSH,
        decode_fn: Callable[[Any], Any] = lambda x: x,
        static_cost: Optional[float] = None,
        slot: str = "val",
        slots: Optional[Dict[str, Color]] = None,
        in_reps: Optional[Tuple[Representation, ...]] = None,
        out_reps: Optional[Tuple[Representation, ...]] = None,
        cost_config: Optional[CatalogCostConfig] = None,
    ):
        cfg = cost_config or DEFAULT_CONFIG.catalog_costs
        super().__init__(
            comp_id=comp_id,
            static_cost=static_cost if static_cost is not None else cfg.rep_bridge,
        )
        self.color = color
        self.in_rep = in_rep
        self.out_rep = out_rep
        self.decode_fn = decode_fn
        self.slot = slot
        self.slots = slots
        allowed_in = frozenset(in_reps) if in_reps is not None else frozenset({in_rep})
        allowed_out = frozenset(out_reps) if out_reps is not None else frozenset({out_rep})
        if slots is not None:
            in_shape = MessageShape(kind=AggregationKind.RECORD, slots=dict(slots), allowed_reps=allowed_in)
            out_shape = MessageShape(kind=AggregationKind.RECORD, slots=dict(slots), allowed_reps=allowed_out)
        else:
            if color is None:
                raise ValueError("RepresentationBridgeBlock requires either `color` or `slots`.")
            in_shape = MessageShape(kind=AggregationKind.RECORD, slots={slot: color}, allowed_reps=allowed_in)
            out_shape = MessageShape(kind=AggregationKind.RECORD, slots={slot: color}, allowed_reps=allowed_out)
        self.add_need("in", in_shape, mode=mode)
        self.add_offer(
            "out",
            out_shape,
            mode=mode,
            velocity=1.0 if mode == TransferMode.PUSH else 0.0,
        )

    def wants_to_pull(self, tick: int) -> bool:
        return self.interfaces["in"].mode == TransferMode.PULL

    def step(self, tick: int, env_inputs: Optional[Dict[str, Message]] = None) -> None:
        in_if = self.interfaces["in"]
        out_if = self.interfaces["out"]
        out_if.outbox = None
        if in_if.inbox is not None:
            msg_in = in_if.inbox
            in_if.inbox = None
            try:
                if self.slots is not None and msg_in.kind == AggregationKind.RECORD:
                    out_fields: Dict[str, Field] = {}
                    for k, f_in in msg_in.fields.items():
                        val = self.decode_fn(f_in.value)
                        out_fields[k] = Field(
                            value=val,
                            color=f_in.color,
                            dynamics=Dynamics(
                                position=out_if.full_id,
                                velocity=1.0 if out_if.mode == TransferMode.PUSH else 0.0,
                            ),
                            representation=self.out_rep,
                            provenance=f_in.provenance.append_op(self.comp_id, tick),
                        )
                    out_if.outbox = Message.record(out_fields, key=msg_in.correlation_key)
                else:
                    f_in = msg_in.first_field(self.slot)
                    val = self.decode_fn(f_in.value)
                    f_out = Field(
                        value=val,
                        color=f_in.color,
                        dynamics=Dynamics(
                            position=out_if.full_id,
                            velocity=1.0 if out_if.mode == TransferMode.PUSH else 0.0,
                        ),
                        representation=self.out_rep,
                        provenance=f_in.provenance.append_op(self.comp_id, tick),
                    )
                    out_if.outbox = Message.single(f_out, slot=self.slot, key=msg_in.correlation_key)
            except Exception as exc:
                self.disruption_events.append((tick, ResultCode.ERROR, str(exc)))


# ---------------------------------------------------------------------------
# Stores / Flow / Time
# ---------------------------------------------------------------------------

class CacheStoreBlock(WymorianComponent):
    """Push→Pull decelerator (a < 0). retain_on_read selects LVC vs consume-on-read latch."""

    def __init__(
        self,
        comp_id: str,
        color: Color,
        retain_on_read: bool = True,
        max_age: Optional[int] = None,
        capacity: int = 1,
        rep: Representation = Representation.NATIVE_STRUCT,
        static_cost: Optional[float] = None,
        slot: str = "val",
        shape: Optional[MessageShape] = None,
        cost_config: Optional[CatalogCostConfig] = None,
    ):
        cfg = cost_config or DEFAULT_CONFIG.catalog_costs
        base = static_cost if static_cost is not None else cfg.cache_base
        mem_cost = round(base + cfg.cache_per_extra_slot * max(0, capacity - 1), 4)
        super().__init__(comp_id=comp_id, static_cost=mem_cost)
        self.color = color
        self.retain_on_read = retain_on_read
        self.max_age = max_age
        self.capacity = max(1, capacity)
        self.slot = slot
        shape_in = shape or MessageShape.single(color, slot=slot, reps=(rep,))
        self.add_need("in", shape_in, mode=TransferMode.PUSH)
        self.add_offer("out", shape_in, mode=TransferMode.PULL, velocity=0.0)

    def reset(self) -> None:
        super().reset()
        self.state = {"queue": [], "stored_ticks": []}

    def step(self, tick: int, env_inputs: Optional[Dict[str, Message]] = None) -> None:
        in_if = self.interfaces["in"]
        out_if = self.interfaces["out"]
        if in_if.inbox is not None:
            msg = in_if.inbox
            in_if.inbox = None
            if msg.kind == AggregationKind.RECORD:
                new_fields = {
                    k: Field(
                        value=f.value,
                        color=f.color,
                        dynamics=f.dynamics.decelerate_to_rest(self.comp_id),
                        representation=f.representation,
                        provenance=f.provenance.append_op(self.comp_id, tick),
                    )
                    for k, f in msg.fields.items()
                }
                cached = Message.record(new_fields, key=msg.correlation_key)
            else:
                f0 = msg.first_field(self.slot)
                cached = Message.single(
                    Field(
                        value=f0.value,
                        color=f0.color,
                        dynamics=f0.dynamics.decelerate_to_rest(self.comp_id),
                        representation=f0.representation,
                        provenance=f0.provenance.append_op(self.comp_id, tick),
                    ),
                    slot=self.slot,
                    key=msg.correlation_key,
                )
            q: List[Message] = self.state["queue"]
            ticks: List[int] = self.state["stored_ticks"]
            if len(q) >= self.capacity:
                q.pop(0)
                ticks.pop(0)
                if not self.retain_on_read:
                    self.disruption_events.append((tick, ResultCode.NO_SPACE, "cache replace-oldest"))
            q.append(cached)
            ticks.append(tick)

        # Stale gate
        if self.max_age is not None and self.state["queue"]:
            while self.state["queue"] and (tick - self.state["stored_ticks"][0]) > self.max_age:
                self.state["queue"].pop(0)
                self.state["stored_ticks"].pop(0)
                self.disruption_events.append((tick, ResultCode.TIMEOUT, "stale drop"))

        out_if.outbox = self.state["queue"][0] if self.state["queue"] else None

    def on_pulled(self) -> Optional[Message]:
        out_if = self.interfaces["out"]
        msg = out_if.outbox
        if msg is not None and not self.retain_on_read:
            self.state["queue"].pop(0)
            self.state["stored_ticks"].pop(0)
            out_if.outbox = self.state["queue"][0] if self.state["queue"] else None
        return msg


class PumpBlock(WymorianComponent):
    """Pull→Push accelerator (a > 0)."""

    def __init__(
        self,
        comp_id: str,
        color: Color,
        period: int = 1,
        rep: Representation = Representation.NATIVE_STRUCT,
        static_cost: Optional[float] = None,
        slot: str = "val",
        shape: Optional[MessageShape] = None,
        cost_config: Optional[CatalogCostConfig] = None,
    ):
        cfg = cost_config or DEFAULT_CONFIG.catalog_costs
        super().__init__(
            comp_id=comp_id,
            static_cost=static_cost if static_cost is not None else cfg.pump,
        )
        self.color = color
        self.period = max(1, period)
        self.slot = slot
        shape_io = shape or MessageShape.single(color, slot=slot, reps=(rep,))
        self.add_need("in", shape_io, mode=TransferMode.PULL)
        self.add_offer("out", shape_io, mode=TransferMode.PUSH, velocity=1.0 / self.period)

    def wants_to_pull(self, tick: int) -> bool:
        return (tick % self.period) == 0

    def step(self, tick: int, env_inputs: Optional[Dict[str, Message]] = None) -> None:
        in_if = self.interfaces["in"]
        out_if = self.interfaces["out"]
        out_if.outbox = None
        if in_if.inbox is not None:
            msg = in_if.inbox
            in_if.inbox = None
            v_out = 1.0 / self.period
            if msg.kind == AggregationKind.RECORD:
                fields = {
                    k: Field(
                        value=f.value,
                        color=f.color,
                        dynamics=f.dynamics.accelerate_to_push(out_if.full_id, v_out),
                        representation=f.representation,
                        provenance=f.provenance.append_op(self.comp_id, tick),
                    )
                    for k, f in msg.fields.items()
                }
                out_if.outbox = Message.record(fields, key=msg.correlation_key)
            else:
                f_in = msg.first_field(self.slot)
                f_out = Field(
                    value=f_in.value,
                    color=f_in.color,
                    dynamics=f_in.dynamics.accelerate_to_push(out_if.full_id, v_out),
                    representation=f_in.representation,
                    provenance=f_in.provenance.append_op(self.comp_id, tick),
                )
                out_if.outbox = Message.single(f_out, slot=self.slot)


class RateAdapterBlock(WymorianComponent):
    """Downsample / pace emissions (keeps latest, emits every period)."""

    def __init__(
        self,
        comp_id: str,
        color: Color,
        emit_period: int = 2,
        rep: Representation = Representation.NATIVE_STRUCT,
        static_cost: Optional[float] = None,
        slot: str = "val",
        cost_config: Optional[CatalogCostConfig] = None,
    ):
        cfg = cost_config or DEFAULT_CONFIG.catalog_costs
        super().__init__(
            comp_id=comp_id,
            static_cost=static_cost if static_cost is not None else cfg.rate_adapter,
        )
        self.emit_period = max(1, emit_period)
        self.loss_per_period = cfg.rate_adapter_loss_per_period
        self.slot = slot
        shape = MessageShape.single(color, slot=slot, reps=(rep,))
        self.add_need("in", shape, mode=TransferMode.PUSH)
        self.add_offer("out", shape, mode=TransferMode.PUSH, velocity=1.0 / self.emit_period)

    def reset(self) -> None:
        super().reset()
        self.state = {"latest": None}

    def step(self, tick: int, env_inputs: Optional[Dict[str, Message]] = None) -> None:
        in_if = self.interfaces["in"]
        out_if = self.interfaces["out"]
        out_if.outbox = None
        if in_if.inbox is not None:
            self.state["latest"] = in_if.inbox
            in_if.inbox = None
        if self.state["latest"] is not None and (tick % self.emit_period) == 0:
            out_if.outbox = self.state["latest"]
            self.info_loss_events.append(
                (tick, self.loss_per_period * (self.emit_period - 1), "rate downsample")
            )


class StaleGateBlock(WymorianComponent):
    """Suppress values older than max_age relative to message provenance timestamp."""

    def __init__(
        self,
        comp_id: str,
        color: Color,
        max_age: int = 2,
        mode: TransferMode = TransferMode.PUSH,
        rep: Representation = Representation.NATIVE_STRUCT,
        static_cost: Optional[float] = None,
        slot: str = "val",
        shape: Optional[MessageShape] = None,
        cost_config: Optional[CatalogCostConfig] = None,
    ):
        cfg = cost_config or DEFAULT_CONFIG.catalog_costs
        super().__init__(
            comp_id=comp_id,
            static_cost=static_cost if static_cost is not None else cfg.stale_gate,
        )
        self.max_age = max_age
        self.slot = slot
        shape_io = shape or MessageShape.single(color, slot=slot, reps=(rep,))
        self.add_need("in", shape_io, mode=mode)
        self.add_offer("out", shape_io, mode=mode, velocity=1.0 if mode == TransferMode.PUSH else 0.0)

    def step(self, tick: int, env_inputs: Optional[Dict[str, Message]] = None) -> None:
        in_if = self.interfaces["in"]
        out_if = self.interfaces["out"]
        out_if.outbox = None
        if in_if.inbox is not None:
            msg = in_if.inbox
            in_if.inbox = None
            age = tick - msg.first_field(self.slot).provenance.timestamp_tick
            if age <= self.max_age:
                out_if.outbox = msg
            else:
                self.disruption_events.append((tick, ResultCode.TIMEOUT, f"stale age={age}"))


# ---------------------------------------------------------------------------
# Aggregation
# ---------------------------------------------------------------------------

class AssembleBlock(WymorianComponent):
    """Aggregate single-field inputs into a multi-slot RECORD."""

    def __init__(
        self,
        comp_id: str,
        slot_colors: Dict[str, Color],
        mode: TransferMode = TransferMode.PUSH,
        rep: Representation = Representation.NATIVE_STRUCT,
        wait_for_all: bool = True,
        static_cost: Optional[float] = None,
        cost_config: Optional[CatalogCostConfig] = None,
    ):
        cfg = cost_config or DEFAULT_CONFIG.catalog_costs
        super().__init__(
            comp_id=comp_id,
            static_cost=static_cost if static_cost is not None else cfg.assemble,
        )
        self.slot_colors = slot_colors
        self.wait_for_all = wait_for_all
        for slot_name, color in slot_colors.items():
            self.add_need(
                f"in_{slot_name}",
                MessageShape.single(color, slot="val", reps=(rep,)),
                mode=mode,
            )
        self.add_offer(
            "out",
            MessageShape(kind=AggregationKind.RECORD, slots=slot_colors, allowed_reps=frozenset({rep})),
            mode=mode,
            velocity=1.0 if mode == TransferMode.PUSH else 0.0,
        )

    def reset(self) -> None:
        super().reset()
        self.state = {"staged": {}}

    def step(self, tick: int, env_inputs: Optional[Dict[str, Message]] = None) -> None:
        out_if = self.interfaces["out"]
        out_if.outbox = None
        for slot_name in self.slot_colors:
            in_if = self.interfaces[f"in_{slot_name}"]
            if in_if.inbox is not None:
                f = in_if.inbox.first_field("val")
                self.state["staged"][slot_name] = Field(
                    value=f.value,
                    color=self.slot_colors[slot_name],
                    dynamics=f.dynamics,
                    representation=f.representation,
                    provenance=f.provenance.append_op(self.comp_id, tick),
                )
                in_if.inbox = None

        if len(self.state["staged"]) == len(self.slot_colors) or (
            not self.wait_for_all and len(self.state["staged"]) > 0
        ):
            assembled = dict(self.state["staged"])
            if self.wait_for_all:
                self.state["staged"].clear()
            out_if.outbox = Message.record(assembled)


class DisassembleBlock(WymorianComponent):
    """Split a RECORD into per-slot Offer outputs."""

    def __init__(
        self,
        comp_id: str,
        slot_colors: Dict[str, Color],
        mode: TransferMode = TransferMode.PUSH,
        rep: Representation = Representation.NATIVE_STRUCT,
        static_cost: Optional[float] = None,
        normalize_output_slot: bool = False,
        cost_config: Optional[CatalogCostConfig] = None,
    ):
        cfg = cost_config or DEFAULT_CONFIG.catalog_costs
        super().__init__(
            comp_id=comp_id,
            static_cost=static_cost if static_cost is not None else cfg.disassemble,
        )
        self.slot_colors = slot_colors
        self.normalize_output_slot = normalize_output_slot
        self.add_need(
            "in",
            MessageShape(kind=AggregationKind.RECORD, slots=slot_colors, allowed_reps=frozenset({rep})),
            mode=mode,
        )
        for slot_name, color in slot_colors.items():
            out_slot = "val" if normalize_output_slot else slot_name
            self.add_offer(
                f"out_{slot_name}",
                MessageShape.single(color, slot=out_slot, reps=(rep,)),
                mode=mode,
                velocity=1.0 if mode == TransferMode.PUSH else 0.0,
            )

    def step(self, tick: int, env_inputs: Optional[Dict[str, Message]] = None) -> None:
        in_if = self.interfaces["in"]
        for slot_name in self.slot_colors:
            self.interfaces[f"out_{slot_name}"].outbox = None
        if in_if.inbox is not None:
            msg = in_if.inbox
            in_if.inbox = None
            for slot_name in self.slot_colors:
                if slot_name in msg.fields:
                    out_slot = "val" if self.normalize_output_slot else slot_name
                    self.interfaces[f"out_{slot_name}"].outbox = Message.single(
                        msg.fields[slot_name], slot=out_slot, key=msg.correlation_key
                    )


class ProjectBlock(WymorianComponent):
    """Select a subset of RECORD slots."""

    def __init__(
        self,
        comp_id: str,
        in_slots: Dict[str, Color],
        keep_slots: List[str],
        mode: TransferMode = TransferMode.PUSH,
        rep: Representation = Representation.NATIVE_STRUCT,
        static_cost: Optional[float] = None,
        cost_config: Optional[CatalogCostConfig] = None,
    ):
        cfg = cost_config or DEFAULT_CONFIG.catalog_costs
        super().__init__(
            comp_id=comp_id,
            static_cost=static_cost if static_cost is not None else cfg.project,
        )
        out_slots = {s: in_slots[s] for s in keep_slots}
        self.keep_slots = keep_slots
        self.add_need(
            "in",
            MessageShape(kind=AggregationKind.RECORD, slots=in_slots, allowed_reps=frozenset({rep})),
            mode=mode,
        )
        self.add_offer(
            "out",
            MessageShape(kind=AggregationKind.RECORD, slots=out_slots, allowed_reps=frozenset({rep})),
            mode=mode,
            velocity=1.0 if mode == TransferMode.PUSH else 0.0,
        )

    def step(self, tick: int, env_inputs: Optional[Dict[str, Message]] = None) -> None:
        in_if = self.interfaces["in"]
        out_if = self.interfaces["out"]
        out_if.outbox = None
        if in_if.inbox is not None:
            msg = in_if.inbox
            in_if.inbox = None
            out_if.outbox = Message.record(
                {s: msg.fields[s] for s in self.keep_slots if s in msg.fields},
                key=msg.correlation_key,
            )


class InjectBlock(WymorianComponent):
    """Inject a constant field into a RECORD."""

    def __init__(
        self,
        comp_id: str,
        in_slots: Dict[str, Color],
        inject_slot: str,
        inject_color: Color,
        inject_value: Any,
        mode: TransferMode = TransferMode.PUSH,
        rep: Representation = Representation.NATIVE_STRUCT,
        static_cost: Optional[float] = None,
        cost_config: Optional[CatalogCostConfig] = None,
    ):
        cfg = cost_config or DEFAULT_CONFIG.catalog_costs
        super().__init__(
            comp_id=comp_id,
            static_cost=static_cost if static_cost is not None else cfg.inject,
        )
        self.inject_slot = inject_slot
        self.inject_color = inject_color
        self.inject_value = inject_value
        self.rep = rep
        out_slots = dict(in_slots)
        out_slots[inject_slot] = inject_color
        self.add_need(
            "in",
            MessageShape(kind=AggregationKind.RECORD, slots=in_slots, allowed_reps=frozenset({rep})),
            mode=mode,
        )
        self.add_offer(
            "out",
            MessageShape(kind=AggregationKind.RECORD, slots=out_slots, allowed_reps=frozenset({rep})),
            mode=mode,
            velocity=1.0 if mode == TransferMode.PUSH else 0.0,
        )

    def step(self, tick: int, env_inputs: Optional[Dict[str, Message]] = None) -> None:
        in_if = self.interfaces["in"]
        out_if = self.interfaces["out"]
        out_if.outbox = None
        if in_if.inbox is not None:
            msg = in_if.inbox
            in_if.inbox = None
            fields = dict(msg.fields)
            fields[self.inject_slot] = Field(
                value=self.inject_value,
                color=self.inject_color,
                dynamics=Dynamics(position=out_if.full_id, velocity=1.0),
                representation=self.rep,
                provenance=Provenance(sources=(self.comp_id,), timestamp_tick=tick),
            )
            out_if.outbox = Message.record(fields, key=msg.correlation_key)


# ---------------------------------------------------------------------------
# Topology
# ---------------------------------------------------------------------------

class FanOutBlock(WymorianComponent):
    """1→N broadcast; colors preserved. Non-destructive fan-out of a PUSH message."""

    def __init__(
        self,
        comp_id: str,
        color: Color,
        n_outputs: int = 2,
        mode: TransferMode = TransferMode.PUSH,
        rep: Representation = Representation.NATIVE_STRUCT,
        static_cost: Optional[float] = None,
        slot: str = "val",
        shape: Optional[MessageShape] = None,
        cost_config: Optional[CatalogCostConfig] = None,
    ):
        cfg = cost_config or DEFAULT_CONFIG.catalog_costs
        super().__init__(
            comp_id=comp_id,
            static_cost=static_cost if static_cost is not None else cfg.fan_out,
        )
        self.n_outputs = n_outputs
        self.slot = slot
        shape_io = shape or MessageShape.single(color, slot=slot, reps=(rep,))
        self.add_need("in", shape_io, mode=mode)
        for i in range(n_outputs):
            self.add_offer(
                f"out_{i}",
                shape_io,
                mode=mode,
                velocity=1.0 if mode == TransferMode.PUSH else 0.0,
            )

    def step(self, tick: int, env_inputs: Optional[Dict[str, Message]] = None) -> None:
        in_if = self.interfaces["in"]
        for i in range(self.n_outputs):
            self.interfaces[f"out_{i}"].outbox = None
        if in_if.inbox is not None:
            msg = in_if.inbox
            in_if.inbox = None
            for i in range(self.n_outputs):
                self.interfaces[f"out_{i}"].outbox = msg


class FanInBlock(WymorianComponent):
    """N→1 merge with first-available policy."""

    def __init__(
        self,
        comp_id: str,
        color: Color,
        n_inputs: int = 2,
        mode: TransferMode = TransferMode.PUSH,
        rep: Representation = Representation.NATIVE_STRUCT,
        static_cost: Optional[float] = None,
        slot: str = "val",
        cost_config: Optional[CatalogCostConfig] = None,
    ):
        cfg = cost_config or DEFAULT_CONFIG.catalog_costs
        super().__init__(
            comp_id=comp_id,
            static_cost=static_cost if static_cost is not None else cfg.fan_in,
        )
        self.n_inputs = n_inputs
        self.slot = slot
        shape = MessageShape.single(color, slot=slot, reps=(rep,))
        for i in range(n_inputs):
            self.add_need(f"in_{i}", shape, mode=mode)
        self.add_offer("out", shape, mode=mode, velocity=1.0 if mode == TransferMode.PUSH else 0.0)

    def step(self, tick: int, env_inputs: Optional[Dict[str, Message]] = None) -> None:
        out_if = self.interfaces["out"]
        out_if.outbox = None
        for i in range(self.n_inputs):
            in_if = self.interfaces[f"in_{i}"]
            if in_if.inbox is not None:
                out_if.outbox = in_if.inbox
                in_if.inbox = None
                break


class JoinBlock(WymorianComponent):
    """Keyed / temporal join of two RECORD inputs into an aggregated RECORD."""

    def __init__(
        self,
        comp_id: str,
        left_slots: Dict[str, Color],
        right_slots: Dict[str, Color],
        key_slot_left: str,
        key_slot_right: str,
        window: int = 1,
        mode: TransferMode = TransferMode.PUSH,
        rep: Representation = Representation.NATIVE_STRUCT,
        static_cost: Optional[float] = None,
        use_provenance_timestamp: bool = False,
        cost_config: Optional[CatalogCostConfig] = None,
    ):
        cfg = cost_config or DEFAULT_CONFIG.catalog_costs
        super().__init__(
            comp_id=comp_id,
            static_cost=static_cost if static_cost is not None else cfg.join,
        )
        self.key_slot_left = key_slot_left
        self.key_slot_right = key_slot_right
        self.window = window
        self.use_provenance_timestamp = use_provenance_timestamp
        out_slots = {**left_slots, **right_slots}
        for k in left_slots:
            if k in right_slots and k != key_slot_left:
                out_slots[f"left_{k}"] = left_slots[k]
                out_slots[f"right_{k}"] = right_slots[k]
                out_slots.pop(k, None)
        self.out_slots = out_slots
        self.left_slots = left_slots
        self.right_slots = right_slots
        self.add_need(
            "in_left",
            MessageShape(kind=AggregationKind.RECORD, slots=left_slots, allowed_reps=frozenset({rep})),
            mode=mode,
        )
        self.add_need(
            "in_right",
            MessageShape(kind=AggregationKind.RECORD, slots=right_slots, allowed_reps=frozenset({rep})),
            mode=mode,
        )
        self.add_offer(
            "out",
            MessageShape(kind=AggregationKind.RECORD, slots=out_slots, allowed_reps=frozenset({rep})),
            mode=mode,
            velocity=1.0 if mode == TransferMode.PUSH else 0.0,
        )

    def reset(self) -> None:
        super().reset()
        self.state = {"left_buf": [], "right_buf": []}

    def step(self, tick: int, env_inputs: Optional[Dict[str, Message]] = None) -> None:
        out_if = self.interfaces["out"]
        out_if.outbox = None
        left = self.interfaces["in_left"]
        right = self.interfaces["in_right"]
        if left.inbox is not None:
            t_l = (
                left.inbox.fields[self.key_slot_left].provenance.timestamp_tick
                if self.use_provenance_timestamp
                else tick
            )
            self.state["left_buf"].append((t_l, left.inbox))
            left.inbox = None
        if right.inbox is not None:
            t_r = (
                right.inbox.fields[self.key_slot_right].provenance.timestamp_tick
                if self.use_provenance_timestamp
                else tick
            )
            self.state["right_buf"].append((t_r, right.inbox))
            right.inbox = None

        # Drop aged
        self.state["left_buf"] = [(t, m) for t, m in self.state["left_buf"] if tick - t <= self.window]
        self.state["right_buf"] = [(t, m) for t, m in self.state["right_buf"] if tick - t <= self.window]

        matched = None
        for i, (tl, ml) in enumerate(list(self.state["left_buf"])):
            kl = ml.fields[self.key_slot_left].value
            for j, (tr, mr) in enumerate(list(self.state["right_buf"])):
                kr = mr.fields[self.key_slot_right].value
                if kl == kr and abs(tl - tr) <= self.window:
                    fields = {}
                    for s, f in ml.fields.items():
                        fields[s if s not in mr.fields or s == self.key_slot_left else f"left_{s}"] = f
                    for s, f in mr.fields.items():
                        if s == self.key_slot_right and self.key_slot_left in fields:
                            continue
                        fields[s if s not in ml.fields else f"right_{s}"] = f
                    matched = Message.record(fields, key=kl)
                    self.state["left_buf"].pop(i)
                    self.state["right_buf"].pop(j)
                    break
            if matched is not None:
                break
        out_if.outbox = matched


# ---------------------------------------------------------------------------
# Derive / Filter / Provenance
# ---------------------------------------------------------------------------

class DeriveBlock(WymorianComponent):
    def __init__(
        self,
        comp_id: str,
        in_shape: MessageShape,
        out_shape: MessageShape,
        compute_fn: Callable[[Message, Dict[str, Any], int], Tuple[Optional[Message], Dict[str, Any]]],
        init_state_fn: Callable[[], Dict[str, Any]] = lambda: {},
        mode: TransferMode = TransferMode.PUSH,
        static_cost: Optional[float] = None,
        latency: float = 0.0,
        cost_config: Optional[CatalogCostConfig] = None,
    ):
        cfg = cost_config or DEFAULT_CONFIG.catalog_costs
        super().__init__(
            comp_id=comp_id,
            static_cost=static_cost if static_cost is not None else cfg.derive,
        )
        self.compute_fn = compute_fn
        self.init_state_fn = init_state_fn
        self.latency = latency
        self.add_need("in", in_shape, mode=mode)
        self.add_offer(
            "out",
            out_shape,
            mode=mode,
            velocity=1.0 if mode == TransferMode.PUSH else 0.0,
        )

    def reset(self) -> None:
        super().reset()
        self.state = self.init_state_fn()

    def step(self, tick: int, env_inputs: Optional[Dict[str, Message]] = None) -> None:
        in_if = self.interfaces["in"]
        out_if = self.interfaces["out"]
        out_if.outbox = None
        if in_if.inbox is not None:
            msg_in = in_if.inbox
            in_if.inbox = None
            msg_out, new_state = self.compute_fn(msg_in, self.state, tick)
            self.state = new_state
            if self.latency > 0.0:
                self.latency_events.append((tick, self.latency, self.comp_id))
            out_if.outbox = msg_out


class FilterBlock(WymorianComponent):
    def __init__(
        self,
        comp_id: str,
        color: Color,
        predicate: Callable[[Field], bool],
        mode: TransferMode = TransferMode.PUSH,
        rep: Representation = Representation.NATIVE_STRUCT,
        static_cost: Optional[float] = None,
        slot: str = "val",
        cost_config: Optional[CatalogCostConfig] = None,
    ):
        cfg = cost_config or DEFAULT_CONFIG.catalog_costs
        super().__init__(
            comp_id=comp_id,
            static_cost=static_cost if static_cost is not None else cfg.filter,
        )
        self.predicate = predicate
        self.slot = slot
        shape = MessageShape.single(color, slot=slot, reps=(rep,))
        self.add_need("in", shape, mode=mode)
        self.add_offer("out", shape, mode=mode, velocity=1.0 if mode == TransferMode.PUSH else 0.0)

    def step(self, tick: int, env_inputs: Optional[Dict[str, Message]] = None) -> None:
        in_if = self.interfaces["in"]
        out_if = self.interfaces["out"]
        out_if.outbox = None
        if in_if.inbox is not None:
            msg = in_if.inbox
            in_if.inbox = None
            if self.predicate(msg.first_field(self.slot)):
                out_if.outbox = msg
            else:
                self.disruption_events.append((tick, ResultCode.NO_DATA, "filtered"))


class ProvVerifyBlock(WymorianComponent):
    """Pass-through that raises assurance if trust_score meets threshold."""

    def __init__(
        self,
        comp_id: str,
        color: Color,
        min_trust: float = 0.8,
        assurance_out: str = "VERIFIED",
        mode: TransferMode = TransferMode.PUSH,
        rep: Representation = Representation.NATIVE_STRUCT,
        static_cost: Optional[float] = None,
        slot: str = "val",
        cost_config: Optional[CatalogCostConfig] = None,
    ):
        cfg = cost_config or DEFAULT_CONFIG.catalog_costs
        super().__init__(
            comp_id=comp_id,
            static_cost=static_cost if static_cost is not None else cfg.prov_verify,
        )
        self.min_trust = min_trust
        self.assurance_out = assurance_out
        self.slot = slot
        shape_in = MessageShape.single(color, slot=slot, reps=(rep,))
        shape_out = MessageShape.single(
            color, slot=slot, reps=(rep,), min_trust=min_trust, required_assurance=assurance_out
        )
        self.add_need("in", shape_in, mode=mode)
        self.add_offer("out", shape_out, mode=mode, velocity=1.0 if mode == TransferMode.PUSH else 0.0)

    def step(self, tick: int, env_inputs: Optional[Dict[str, Message]] = None) -> None:
        in_if = self.interfaces["in"]
        out_if = self.interfaces["out"]
        out_if.outbox = None
        if in_if.inbox is not None:
            msg = in_if.inbox
            in_if.inbox = None
            f = msg.first_field(self.slot)
            if f.provenance.trust_score >= self.min_trust:
                f2 = f.with_provenance(
                    f.provenance.append_op(self.comp_id, tick, assurance_level=self.assurance_out)
                )
                out_if.outbox = Message.single(f2, slot=self.slot)
            else:
                self.disruption_events.append((tick, ResultCode.ERROR, "provenance verify failed"))


class ProvTMRVoteBlock(WymorianComponent):
    """Triple modular redundancy vote across three same-color inputs (supports tolerance or exact vote)."""

    def __init__(
        self,
        comp_id: str,
        color: Color,
        mode: TransferMode = TransferMode.PUSH,
        rep: Representation = Representation.NATIVE_STRUCT,
        static_cost: Optional[float] = None,
        slot: str = "val",
        out_min_trust_shape: bool = True,
        vote_tolerance: float = 1e-6,
        cost_config: Optional[CatalogCostConfig] = None,
    ):
        cfg = cost_config or DEFAULT_CONFIG.catalog_costs
        super().__init__(
            comp_id=comp_id,
            static_cost=static_cost if static_cost is not None else cfg.prov_tmr,
        )
        self.slot = slot
        self.vote_tolerance = vote_tolerance
        self.cost_config = cfg
        shape_in = MessageShape.single(color, slot=slot, reps=(rep,))
        shape_out = (
            MessageShape.single(
                color,
                slot=slot,
                reps=(rep,),
                min_trust=cfg.tmr_default_min_trust,
                required_assurance="TMR_VOTED",
            )
            if out_min_trust_shape
            else shape_in
        )
        for i in range(3):
            self.add_need(f"in_{i}", shape_in, mode=mode)
        self.add_offer("out", shape_out, mode=mode, velocity=1.0 if mode == TransferMode.PUSH else 0.0)

    def reset(self) -> None:
        super().reset()
        self.state = {"buf": [None, None, None]}

    def step(self, tick: int, env_inputs: Optional[Dict[str, Message]] = None) -> None:
        out_if = self.interfaces["out"]
        out_if.outbox = None
        for i in range(3):
            in_if = self.interfaces[f"in_{i}"]
            if in_if.inbox is not None:
                self.state["buf"][i] = in_if.inbox.first_field(self.slot)
                in_if.inbox = None
        buf: List[Optional[Field]] = self.state["buf"]
        if all(b is not None for b in buf):
            vals = [b.value for b in buf]  # type: ignore[union-attr]
            winner_idx: Optional[int] = None
            for idx_a, va in enumerate(vals):
                agreements = 0
                for vb in vals:
                    if isinstance(va, (int, float)) and isinstance(vb, (int, float)):
                        if abs(float(va) - float(vb)) <= self.vote_tolerance:
                            agreements += 1
                    elif va == vb:
                        agreements += 1
                if agreements >= 2:
                    winner_idx = idx_a
                    break
            if winner_idx is not None:
                base = buf[winner_idx]
                assert base is not None
                others = [b.provenance for i, b in enumerate(buf) if b is not None and i != winner_idx]
                prov = base.provenance.merge_vote(others, self.comp_id, tick, cfg=self.cost_config)
                out_if.outbox = Message.single(
                    Field(
                        value=base.value,
                        color=base.color,
                        dynamics=Dynamics(position=out_if.full_id, velocity=1.0),
                        representation=base.representation,
                        provenance=prov,
                    ),
                    slot=self.slot,
                )
                self.state["buf"] = [None, None, None]
            else:
                self.state["buf"] = [None, None, None]
                self.disruption_events.append((tick, ResultCode.ERROR, "TMR disagree"))


class MuxSwitchBlock(WymorianComponent):
    """
    Online adaptive multi-source selector.
    Supports either a static `active_index` or a dynamic `policy_fn(tick, inboxes, state) -> int`
    for online runtime failover.
    """

    def __init__(
        self,
        comp_id: str,
        color: Color,
        n_inputs: int = 2,
        mode: TransferMode = TransferMode.PUSH,
        rep: Representation = Representation.NATIVE_STRUCT,
        static_cost: Optional[float] = None,
        slot: str = "val",
        active_index: int = 0,
        policy_fn: Optional[Callable[[int, Dict[int, Optional[Message]], Dict[str, Any]], int]] = None,
        cost_config: Optional[CatalogCostConfig] = None,
    ):
        cfg = cost_config or DEFAULT_CONFIG.catalog_costs
        super().__init__(
            comp_id=comp_id,
            static_cost=static_cost if static_cost is not None else cfg.mux_switch,
        )
        self.n_inputs = n_inputs
        self.slot = slot
        self.initial_active_index = active_index
        self.policy_fn = policy_fn
        self.state = {"active_index": active_index}
        shape = MessageShape.single(color, slot=slot, reps=(rep,))
        for i in range(n_inputs):
            self.add_need(f"in_{i}", shape, mode=mode)
        self.add_offer("out", shape, mode=mode, velocity=1.0 if mode == TransferMode.PUSH else 0.0)

    def reset(self) -> None:
        super().reset()
        self.state = {"active_index": self.initial_active_index}

    def set_active(self, index: int) -> None:
        self.initial_active_index = max(0, min(self.n_inputs - 1, index))
        self.state["active_index"] = self.initial_active_index

    def step(self, tick: int, env_inputs: Optional[Dict[str, Message]] = None) -> None:
        out_if = self.interfaces["out"]
        out_if.outbox = None
        inboxes = {i: self.interfaces[f"in_{i}"].inbox for i in range(self.n_inputs)}
        if self.policy_fn is not None:
            idx = self.policy_fn(tick, inboxes, self.state)
            self.state["active_index"] = max(0, min(self.n_inputs - 1, idx))
        idx = self.state.get("active_index", 0)
        for i in range(self.n_inputs):
            in_if = self.interfaces[f"in_{i}"]
            if in_if.inbox is not None:
                if i == idx:
                    out_if.outbox = in_if.inbox
                in_if.inbox = None
