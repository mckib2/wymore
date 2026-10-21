"""JSON schema load/validation for ISR documentation packages."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any


SCHEMA_VERSION = 1


class SchemaError(ValueError):
    """Raised when a design JSON document is invalid."""


def _req_str(obj: dict[str, Any], key: str, ctx: str) -> str:
    val = obj.get(key)
    if not isinstance(val, str):
        raise SchemaError(f"{ctx}: missing or non-string field '{key}'")
    return val


def _opt_str(obj: dict[str, Any], key: str, default: str = "") -> str:
    val = obj.get(key, default)
    if val is None:
        return default
    if not isinstance(val, str):
        raise SchemaError(f"field '{key}' must be a string")
    return val


def _req_list(obj: dict[str, Any], key: str, ctx: str) -> list[Any]:
    val = obj.get(key)
    if not isinstance(val, list):
        raise SchemaError(f"{ctx}: missing or non-list field '{key}'")
    return val


@dataclass
class PortDoc:
    name: str
    value_type: str = ""


@dataclass
class ComponentDoc:
    name: str
    state_type: str = ""
    in_ports: list[PortDoc] = field(default_factory=list)
    out_ports: list[PortDoc] = field(default_factory=list)
    role: str = ""


@dataclass
class WireDoc:
    name: str
    from_component: str
    from_port: str
    to_component: str
    to_port: str


@dataclass
class BoundaryPortDoc:
    component: str
    port: str
    direction: str  # "in" | "out"


@dataclass
class TechnologyDoc:
    name: str
    members: list[str]
    unused_shelf: list[str] = field(default_factory=list)


@dataclass
class CouplingDoc:
    name: str
    components: list[ComponentDoc]
    wires: list[WireDoc]
    boundary_ports: list[BoundaryPortDoc] = field(default_factory=list)


@dataclass
class LscDoc:
    chart_name: str = ""
    pre_condition: str = ""
    main_condition: str = ""
    in_message: str = ""
    out_message: str = ""


@dataclass
class IorDoc:
    name: str
    input_type: str = ""
    output_type: str = ""
    horizon: str = "infinite"
    description: str = ""
    lsc: LscDoc | None = None


@dataclass
class ImplementsDoc:
    functional_system: str
    implementing_system: str
    mode_witness: str = ""
    hom_witness: str = ""
    notes: str = ""


@dataclass
class IsrPackageDoc:
    schema_version: int
    id: str
    title: str
    summary: str
    technology: TechnologyDoc
    coupling: CouplingDoc
    ior: IorDoc
    functional_system: str
    buildable_system: str
    implements: ImplementsDoc
    formal_refs: list[str] = field(default_factory=list)


def _parse_port(raw: Any, ctx: str) -> PortDoc:
    if not isinstance(raw, dict):
        raise SchemaError(f"{ctx}: port must be an object")
    return PortDoc(
        name=_req_str(raw, "name", ctx),
        value_type=_opt_str(raw, "valueType"),
    )


def _parse_component(raw: Any, ctx: str) -> ComponentDoc:
    if not isinstance(raw, dict):
        raise SchemaError(f"{ctx}: component must be an object")
    name = _req_str(raw, "name", ctx)
    return ComponentDoc(
        name=name,
        state_type=_opt_str(raw, "stateType"),
        in_ports=[_parse_port(p, f"{ctx}.{name}.inPorts") for p in raw.get("inPorts", [])],
        out_ports=[_parse_port(p, f"{ctx}.{name}.outPorts") for p in raw.get("outPorts", [])],
        role=_opt_str(raw, "role"),
    )


def _parse_wire(raw: Any, ctx: str) -> WireDoc:
    if not isinstance(raw, dict):
        raise SchemaError(f"{ctx}: wire must be an object")
    return WireDoc(
        name=_opt_str(raw, "name"),
        from_component=_req_str(raw, "fromComponent", ctx),
        from_port=_req_str(raw, "fromPort", ctx),
        to_component=_req_str(raw, "toComponent", ctx),
        to_port=_req_str(raw, "toPort", ctx),
    )


def _parse_boundary(raw: Any, ctx: str) -> BoundaryPortDoc:
    if not isinstance(raw, dict):
        raise SchemaError(f"{ctx}: boundary port must be an object")
    direction = _req_str(raw, "direction", ctx)
    if direction not in ("in", "out"):
        raise SchemaError(f"{ctx}: direction must be 'in' or 'out'")
    return BoundaryPortDoc(
        component=_req_str(raw, "component", ctx),
        port=_req_str(raw, "port", ctx),
        direction=direction,
    )


def load_isr_package(data: dict[str, Any]) -> IsrPackageDoc:
    """Validate and parse a design.json object."""
    if not isinstance(data, dict):
        raise SchemaError("root must be a JSON object")

    version = data.get("schemaVersion")
    if version != SCHEMA_VERSION:
        raise SchemaError(
            f"unsupported schemaVersion {version!r}; expected {SCHEMA_VERSION}"
        )

    tech_raw = data.get("technology")
    if not isinstance(tech_raw, dict):
        raise SchemaError("technology must be an object")
    members = _req_list(tech_raw, "members", "technology")
    if not all(isinstance(m, str) for m in members):
        raise SchemaError("technology.members must be strings")
    unused = tech_raw.get("unusedShelf", [])
    if not isinstance(unused, list) or not all(isinstance(m, str) for m in unused):
        raise SchemaError("technology.unusedShelf must be a list of strings")
    technology = TechnologyDoc(
        name=_req_str(tech_raw, "name", "technology"),
        members=list(members),
        unused_shelf=list(unused),
    )

    coup_raw = data.get("coupling")
    if not isinstance(coup_raw, dict):
        raise SchemaError("coupling must be an object")
    components = [
        _parse_component(c, "coupling.components")
        for c in _req_list(coup_raw, "components", "coupling")
    ]
    wires = [
        _parse_wire(w, "coupling.wires")
        for w in _req_list(coup_raw, "wires", "coupling")
    ]
    boundaries = [
        _parse_boundary(b, "coupling.boundaryPorts")
        for b in coup_raw.get("boundaryPorts", [])
    ]
    coupling = CouplingDoc(
        name=_req_str(coup_raw, "name", "coupling"),
        components=components,
        wires=wires,
        boundary_ports=boundaries,
    )

    ior_raw = data.get("ior")
    if not isinstance(ior_raw, dict):
        raise SchemaError("ior must be an object")
    lsc_obj = None
    lsc_raw = ior_raw.get("lsc")
    if isinstance(lsc_raw, dict):
        lsc_obj = LscDoc(
            chart_name=_opt_str(lsc_raw, "chartName"),
            pre_condition=_opt_str(lsc_raw, "preCondition"),
            main_condition=_opt_str(lsc_raw, "mainCondition"),
            in_message=_opt_str(lsc_raw, "inMessage"),
            out_message=_opt_str(lsc_raw, "outMessage"),
        )

    ior = IorDoc(
        name=_req_str(ior_raw, "name", "ior"),
        input_type=_opt_str(ior_raw, "inputType"),
        output_type=_opt_str(ior_raw, "outputType"),
        horizon=_opt_str(ior_raw, "horizon", "infinite"),
        description=_opt_str(ior_raw, "description"),
        lsc=lsc_obj,
    )

    impl_raw = data.get("implements")
    if not isinstance(impl_raw, dict):
        raise SchemaError("implements must be an object")
    implements = ImplementsDoc(
        functional_system=_req_str(impl_raw, "functionalSystem", "implements"),
        implementing_system=_req_str(impl_raw, "implementingSystem", "implements"),
        mode_witness=_opt_str(impl_raw, "modeWitness"),
        hom_witness=_opt_str(impl_raw, "homWitness"),
        notes=_opt_str(impl_raw, "notes"),
    )

    refs = data.get("formalRefs", [])
    if not isinstance(refs, list) or not all(isinstance(r, str) for r in refs):
        raise SchemaError("formalRefs must be a list of strings")

    return IsrPackageDoc(
        schema_version=SCHEMA_VERSION,
        id=_req_str(data, "id", "root"),
        title=_opt_str(data, "title"),
        summary=_opt_str(data, "summary"),
        technology=technology,
        coupling=coupling,
        ior=ior,
        functional_system=_opt_str(data, "functionalSystem"),
        buildable_system=_opt_str(data, "buildableSystem"),
        implements=implements,
        formal_refs=list(refs),
    )
