"""
primitives.py
Authoritative Field ontology: Unified Stateful Color axes —
TBox (C,L,P), Dynamics k=(x,v,a), runtime ABI Representation ρ, Provenance π —
plus Message aggregations (Record / Sequence / Choice).
Carrier is a Route Carrier attribute (transport), not a color axis.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import Any, Dict, FrozenSet, List, Optional, Tuple

from .config import (
    CarrierCostConfig,
    CatalogCostConfig,
    ColorDistanceConfig,
    DEFAULT_CONFIG,
)


class TransferMode(str, Enum):
    PUSH = "PUSH"  # Velocity v > 0
    PULL = "PULL"  # Velocity v == 0


class Representation(str, Enum):
    """
    Runtime language / ABI in-memory realization of a Field value (ρ).

    Distinct from Platform P (UDDL PDM abstract machine type/precision) and from
    Route Carrier (bus/transport). Prefer the ABI-named members; legacy names are
    retained as aliases so existing scenarios keep compiling.
    """

    # Preferred ABI / language-binding names
    C_ABI = "C_ABI"
    PY_OBJECT = "PY_OBJECT"
    NATIVE_STRUCT = "NATIVE_STRUCT"  # in-process C-layout / POD ABI
    DDS_BINDING = "DDS_BINDING"  # DDS language binding (e.g. CDR-backed object)
    JVM_OBJECT = "JVM_OBJECT"

    # Legacy aliases (reinterpreted as ABI / binding; not wire transport)
    GENERIC_TREE = "GENERIC_TREE"
    BYTE_BLOB_JSON = "BYTE_BLOB_JSON"  # Python-runtime encoded object
    BYTE_BLOB_PROTO = "BYTE_BLOB_PROTO"
    CDR_DDS = "CDR_DDS"  # alias semantics of DDS_BINDING
    XML_UTF8 = "XML_UTF8"
    ASN1_BER = "ASN1_BER"
    MIL_STD_1553 = "MIL_STD_1553"  # deprecated as ρ; prefer Carrier.MIL_STD_1553


# Equivalent in-memory ABI / language-binding families (ρ aliases).
_REP_EQUIV_CLASSES: Tuple[FrozenSet[Representation], ...] = (
    frozenset({Representation.C_ABI, Representation.NATIVE_STRUCT}),
    frozenset({Representation.DDS_BINDING, Representation.CDR_DDS}),
)


def _expand_rep_aliases(reps: FrozenSet[Representation]) -> FrozenSet[Representation]:
    out = set(reps)
    for cls in _REP_EQUIV_CLASSES:
        if out & cls:
            out |= set(cls)
    return frozenset(out)


def representation_sets_compatible(
    a: FrozenSet[Representation], b: FrozenSet[Representation]
) -> bool:
    """True iff the two allowed-ρ sets share a member under ABI aliasing."""
    return bool(_expand_rep_aliases(a) & _expand_rep_aliases(b))


def representation_accepted(
    rep: Representation, allowed: FrozenSet[Representation]
) -> bool:
    """True iff `rep` is admitted by `allowed` under ABI aliasing."""
    return representation_sets_compatible(frozenset({rep}), allowed)


class AggregationKind(str, Enum):
    RECORD = "RECORD"
    SEQUENCE = "SEQUENCE"
    CHOICE = "CHOICE"


class Carrier(str, Enum):
    """Route Carrier: transport medium; never alters Stateful Color κ."""

    IN_PROCESS = "IN_PROCESS"
    SHARED_MEMORY = "SHARED_MEMORY"
    GENERIC_TREE = "GENERIC_TREE"
    IPC_SERIALIZED = "IPC_SERIALIZED"
    MIL_STD_1553 = "MIL_STD_1553"
    DDS_TOPIC = "DDS_TOPIC"

    def cost_with_config(self, cfg: Optional[CarrierCostConfig] = None) -> float:
        c = cfg or DEFAULT_CONFIG.carrier_costs
        return {
            Carrier.IN_PROCESS: c.in_process,
            Carrier.SHARED_MEMORY: c.shared_memory,
            Carrier.GENERIC_TREE: c.generic_tree,
            Carrier.IPC_SERIALIZED: c.ipc_serialized,
            Carrier.MIL_STD_1553: c.mil_std_1553,
            Carrier.DDS_TOPIC: c.dds_topic,
        }[self]

    @property
    def cost(self) -> float:
        return self.cost_with_config()


class ResultCode(str, Enum):
    SUCCESS = "Success"
    NO_DATA = "No_Data"
    NO_SPACE = "No_Space"
    TIMEOUT = "Timeout"
    NOT_ACTIVE = "Not_Active"
    ERROR = "Error"


@dataclass(frozen=True)
class Color:
    """TBox semantic signature: Conceptual / Logical / Platform."""
    C: str
    L: str
    P: str

    def distance_to(
        self,
        target: "Color",
        cfg: Optional[ColorDistanceConfig] = None,
    ) -> float:
        c_cfg = cfg or DEFAULT_CONFIG.color_distance
        dist = 0.0
        if self.C != target.C:
            self_parts = self.C.split(".")
            tgt_parts = target.C.split(".")
            common = 0
            for sp, tp in zip(self_parts, tgt_parts):
                if sp == tp:
                    common += 1
                else:
                    break
            if common == 0:
                dist += c_cfg.c_diff_root_penalty
            elif common == 1:
                dist += c_cfg.c_same_root_penalty
            else:
                # Deeper shared hierarchy in UDDL entity path (e.g. Engine.Cylinder.Piston)
                dist += round(max(0.2, c_cfg.c_same_root_penalty * (0.7 ** (common - 1))), 4)
        if self.L != target.L:
            dist += c_cfg.l_mismatch_penalty
        if self.P != target.P:
            dist += c_cfg.p_mismatch_penalty
        return dist

    def __str__(self) -> str:
        return f"({self.C} | {self.L} | {self.P})"


@dataclass(frozen=True)
class Dynamics:
    """
    Data kinematics state k = (x, v, a):
      - position (x): locus of the datum on the board (component, interface, or route).
      - velocity (v): >0 for kinetic PUSH flows; ==0 for stationary PULL potential data.
      - acceleration (a = dv/dt): posits the rate of velocity change, interpreted as
        impulsive mode transitions at stores (a < 0 decelerating push to rest) and
        pumps (a > 0 accelerating rest to push), or continuous rate ramps during bursts.
    """
    position: str = "unplaced"
    velocity: float = 0.0
    acceleration: float = 0.0

    @property
    def mode(self) -> TransferMode:
        return TransferMode.PUSH if self.velocity > 0.0 else TransferMode.PULL

    def decelerate_to_rest(self, new_position: str) -> "Dynamics":
        return Dynamics(position=new_position, velocity=0.0, acceleration=-abs(self.velocity))

    def accelerate_to_push(self, new_position: str, velocity: float = 1.0) -> "Dynamics":
        v = max(velocity, 1e-9)
        return Dynamics(position=new_position, velocity=v, acceleration=+v)


@dataclass(frozen=True)
class Provenance:
    """Lineage and trust metadata; gates Tier-1 satisfaction when Needs declare predicates."""
    sources: Tuple[str, ...] = ()
    ops_applied: Tuple[str, ...] = ()
    timestamp_tick: int = 0
    trust_score: float = 1.0
    assurance_level: str = "UNVERIFIED"

    def append_op(
        self,
        op_id: str,
        tick: int,
        trust_multiplier: float = 1.0,
        assurance_level: Optional[str] = None,
        update_timestamp: bool = False,
    ) -> "Provenance":
        return Provenance(
            sources=self.sources,
            ops_applied=self.ops_applied + (op_id,),
            timestamp_tick=tick if update_timestamp else self.timestamp_tick,
            trust_score=round(self.trust_score * trust_multiplier, 4),
            assurance_level=assurance_level if assurance_level is not None else self.assurance_level,
        )

    def merge_vote(
        self,
        others: List["Provenance"],
        op_id: str,
        tick: int,
        cfg: Optional[CatalogCostConfig] = None,
    ) -> "Provenance":
        c_cfg = cfg or DEFAULT_CONFIG.catalog_costs
        all_sources: List[str] = list(self.sources)
        for o in others:
            all_sources.extend(o.sources)
        min_trust = min([self.trust_score] + [o.trust_score for o in others])
        voted_trust = min(
            1.0,
            max(c_cfg.tmr_trust_floor, min_trust + c_cfg.tmr_trust_boost),
        )
        return Provenance(
            sources=tuple(dict.fromkeys(all_sources)),
            ops_applied=self.ops_applied + (op_id,),
            timestamp_tick=tick,
            trust_score=round(voted_trust, 4),
            assurance_level="TMR_VOTED",
        )


@dataclass(frozen=True)
class Field:
    """Atomic mediated datum. Values change only via Recolor/Derive contracts."""
    value: Any
    color: Color
    dynamics: Dynamics = field(default_factory=Dynamics)
    representation: Representation = Representation.NATIVE_STRUCT
    provenance: Provenance = field(default_factory=Provenance)

    def with_kinematics(self, position: str, velocity: float, acceleration: float = 0.0) -> "Field":
        return Field(
            value=self.value,
            color=self.color,
            dynamics=Dynamics(position=position, velocity=velocity, acceleration=acceleration),
            representation=self.representation,
            provenance=self.provenance,
        )

    def with_provenance(self, provenance: Provenance) -> "Field":
        return Field(
            value=self.value,
            color=self.color,
            dynamics=self.dynamics,
            representation=self.representation,
            provenance=provenance,
        )


@dataclass(frozen=True)
class MessageShape:
    """
    Static contract of a Message.
    For RECORD: slots maps name -> Color.
    For SEQUENCE: sequence_item_color is the homogeneous element color (slots may be empty).
    For CHOICE: choice_alternatives maps tag -> Color.
    """
    kind: AggregationKind = AggregationKind.RECORD
    slots: Dict[str, Color] = field(default_factory=dict)
    sequence_item_color: Optional[Color] = None
    choice_alternatives: Dict[str, Color] = field(default_factory=dict)
    allowed_reps: FrozenSet[Representation] = frozenset({Representation.NATIVE_STRUCT})
    min_trust_score: float = 0.0
    required_source: Optional[str] = None
    required_assurance: Optional[str] = None

    def __post_init__(self) -> None:
        if self.kind == AggregationKind.RECORD and not self.slots:
            raise ValueError("RECORD MessageShape requires non-empty slots.")
        if self.kind == AggregationKind.SEQUENCE and self.sequence_item_color is None:
            raise ValueError("SEQUENCE MessageShape requires sequence_item_color.")
        if self.kind == AggregationKind.CHOICE and not self.choice_alternatives:
            raise ValueError("CHOICE MessageShape requires choice_alternatives.")

    @classmethod
    def single(
        cls,
        color: Color,
        slot: str = "val",
        reps: Tuple[Representation, ...] = (Representation.NATIVE_STRUCT,),
        min_trust: float = 0.0,
        required_source: Optional[str] = None,
        required_assurance: Optional[str] = None,
    ) -> "MessageShape":
        return cls(
            kind=AggregationKind.RECORD,
            slots={slot: color},
            allowed_reps=frozenset(reps),
            min_trust_score=min_trust,
            required_source=required_source,
            required_assurance=required_assurance,
        )

    @classmethod
    def sequence(
        cls,
        item_color: Color,
        reps: Tuple[Representation, ...] = (Representation.NATIVE_STRUCT,),
        min_trust: float = 0.0,
    ) -> "MessageShape":
        return cls(
            kind=AggregationKind.SEQUENCE,
            sequence_item_color=item_color,
            allowed_reps=frozenset(reps),
            min_trust_score=min_trust,
        )

    @classmethod
    def choice(
        cls,
        alternatives: Dict[str, Color],
        reps: Tuple[Representation, ...] = (Representation.NATIVE_STRUCT,),
        min_trust: float = 0.0,
    ) -> "MessageShape":
        return cls(
            kind=AggregationKind.CHOICE,
            choice_alternatives=dict(alternatives),
            allowed_reps=frozenset(reps),
            min_trust_score=min_trust,
        )

    @property
    def primary_color(self) -> Color:
        if self.kind == AggregationKind.RECORD:
            return next(iter(self.slots.values()))
        if self.kind == AggregationKind.SEQUENCE:
            assert self.sequence_item_color is not None
            return self.sequence_item_color
        return next(iter(self.choice_alternatives.values()))

    def compatible_with(self, other: "MessageShape") -> bool:
        if self.kind != other.kind:
            return False
        if not representation_sets_compatible(self.allowed_reps, other.allowed_reps):
            return False
        if self.kind == AggregationKind.RECORD:
            if set(self.slots.keys()) != set(other.slots.keys()):
                return False
            return all(self.slots[s] == other.slots[s] for s in self.slots)
        if self.kind == AggregationKind.SEQUENCE:
            return self.sequence_item_color == other.sequence_item_color
        return self.choice_alternatives == other.choice_alternatives


@dataclass(frozen=True)
class Message:
    """
    Runtime aggregation.
      RECORD: fields dict
      SEQUENCE: sequence list of Fields
      CHOICE: choice_tag + choice_field
    """
    kind: AggregationKind = AggregationKind.RECORD
    fields: Dict[str, Field] = field(default_factory=dict)
    sequence: Tuple[Field, ...] = ()
    choice_tag: Optional[str] = None
    choice_field: Optional[Field] = None
    correlation_key: Optional[Any] = None

    @classmethod
    def single(cls, f: Field, slot: str = "val", key: Optional[Any] = None) -> "Message":
        return cls(kind=AggregationKind.RECORD, fields={slot: f}, correlation_key=key)

    @classmethod
    def record(cls, fields: Dict[str, Field], key: Optional[Any] = None) -> "Message":
        return cls(kind=AggregationKind.RECORD, fields=dict(fields), correlation_key=key)

    @classmethod
    def as_sequence(cls, items: List[Field], key: Optional[Any] = None) -> "Message":
        return cls(kind=AggregationKind.SEQUENCE, sequence=tuple(items), correlation_key=key)

    @classmethod
    def as_choice(cls, tag: str, f: Field, key: Optional[Any] = None) -> "Message":
        return cls(kind=AggregationKind.CHOICE, choice_tag=tag, choice_field=f, correlation_key=key)

    def first_field(self, slot: str = "val") -> Field:
        if self.kind == AggregationKind.RECORD:
            if slot in self.fields:
                return self.fields[slot]
            return next(iter(self.fields.values()))
        if self.kind == AggregationKind.SEQUENCE:
            if not self.sequence:
                raise ValueError("Empty SEQUENCE message")
            return self.sequence[0]
        if self.choice_field is None:
            raise ValueError("Empty CHOICE message")
        return self.choice_field

    def all_fields(self) -> List[Field]:
        if self.kind == AggregationKind.RECORD:
            return list(self.fields.values())
        if self.kind == AggregationKind.SEQUENCE:
            return list(self.sequence)
        return [self.choice_field] if self.choice_field is not None else []

    def matches_shape(self, shape: MessageShape) -> bool:
        if self.kind != shape.kind:
            return False
        if self.kind == AggregationKind.RECORD:
            if set(self.fields.keys()) != set(shape.slots.keys()):
                return False
            return all(
                self.fields[s].color == shape.slots[s]
                and representation_accepted(self.fields[s].representation, shape.allowed_reps)
                for s in shape.slots
            )
        if self.kind == AggregationKind.SEQUENCE:
            return all(
                f.color == shape.sequence_item_color
                and representation_accepted(f.representation, shape.allowed_reps)
                for f in self.sequence
            )
        if self.choice_tag is None or self.choice_field is None:
            return False
        expected = shape.choice_alternatives.get(self.choice_tag)
        return (
            expected is not None
            and self.choice_field.color == expected
            and representation_accepted(self.choice_field.representation, shape.allowed_reps)
        )

    def satisfies_provenance(self, shape: MessageShape) -> bool:
        for f in self.all_fields():
            if f.provenance.trust_score < shape.min_trust_score:
                return False
            if shape.required_source is not None and shape.required_source not in f.provenance.sources:
                return False
            if (
                shape.required_assurance is not None
                and f.provenance.assurance_level != shape.required_assurance
            ):
                return False
        return True
