"""
Example 5: Hierarchical Airframe / Engine / Piston Model.
Demonstrates structural disaggregation, projection, multi-axis (C, L, P) recoloring
across a three-level UDDL part-whole hierarchy (Airframe -> Engine -> Cylinder/Piston),
kinematic pull-to-push pumping of a stationary airframe mount sensor, and synthesis:
  - Producer 1 (ECU): pushes a 4-slot RECORD in CDR_DDS:
      * piston1_temp: (Engine.Cylinder1.Piston.CrownTemp, Fahrenheit, float32)
      * piston2_temp: (Engine.Cylinder2.Piston.CrownTemp, Fahrenheit, float32)
      * crank_rpm:    (Engine.Crankshaft.AngularVelocity, RPM, uint16)
      * manifold_p:   (Engine.Intake.ManifoldPressure, PSI, float32) [extraneous slot]
  - Producer 2 (AirframeMount): stationary PULL offer in NATIVE_STRUCT:
      * mount_temp:   (Airframe.Nacelle.MountTemp, Celsius, float64)
  - Consumer (PropulsionHealthMonitor): expects a 3-slot RECORD in NATIVE_STRUCT:
      * max_piston_temp:  (Airframe.Propulsion.PeakPistonTemp, Kelvin, float64)
      * thermal_gradient: (Airframe.Propulsion.PistonMountDeltaT, Kelvin, float64)
      * shaft_omega:      (Airframe.Propulsion.ShaftSpeed, RadPerSec, float64)
"""
from __future__ import annotations

import math
from typing import Dict, List

from integration_game import (
    AssembleBlock,
    Board,
    BoardEvaluator,
    Color,
    ConsumerBoundary,
    DeriveBlock,
    DisassembleBlock,
    Dynamics,
    Field,
    Message,
    MessageShape,
    ProducerBoundary,
    ProjectBlock,
    Provenance,
    PumpBlock,
    RecolorBlock,
    Representation,
    RepresentationBridgeBlock,
    ScoreBreakdown,
    TransferMode,
    UniversalLSC,
)


def example_05_piston() -> List[ScoreBreakdown]:
    # Producer 1 (ECU) colors
    c_p1_f = Color("Engine.Cylinder1.Piston.CrownTemp", "Fahrenheit", "float32")
    c_p2_f = Color("Engine.Cylinder2.Piston.CrownTemp", "Fahrenheit", "float32")
    c_rpm_u16 = Color("Engine.Crankshaft.AngularVelocity", "RPM", "uint16")
    c_psi = Color("Engine.Intake.ManifoldPressure", "PSI", "float32")

    # Producer 2 (Airframe nacelle mount) color
    c_mount_c = Color("Airframe.Nacelle.MountTemp", "Celsius", "float64")
    c_mount_k = Color("Airframe.Nacelle.MountTemp", "Kelvin", "float64")

    # Intermediate & Target Consumer colors
    c_rpm_f64 = Color("Engine.Crankshaft.AngularVelocity", "RPM", "float64")
    c_omega_eng = Color("Engine.Crankshaft.AngularVelocity", "RadPerSec", "float64")
    c_omega_air = Color("Airframe.Propulsion.ShaftSpeed", "RadPerSec", "float64")

    c_peak_k = Color("Airframe.Propulsion.PeakPistonTemp", "Kelvin", "float64")
    c_grad_k = Color("Airframe.Propulsion.PistonMountDeltaT", "Kelvin", "float64")

    ecu_slots = {
        "piston1_temp": c_p1_f,
        "piston2_temp": c_p2_f,
        "crank_rpm": c_rpm_u16,
        "manifold_p": c_psi,
    }
    projected_slots = {
        "piston1_temp": c_p1_f,
        "piston2_temp": c_p2_f,
        "crank_rpm": c_rpm_u16,
    }
    phm_slots = {
        "max_piston_temp": c_peak_k,
        "thermal_gradient": c_grad_k,
        "shaft_omega": c_omega_air,
    }

    horizon = 5
    # Test samples: Piston1=572 F (573.15 K), Piston2=608 F (593.15 K), RPM=3000 (314.159 rad/s), Mount=100 C (373.15 K)
    scenario: Dict[int, Dict[str, Message]] = {}
    for t in (0, 2, 4):
        p1_f = 572.0 + 18.0 * (t // 2)
        p2_f = 608.0 + 18.0 * (t // 2)
        rpm = 3000 + 300 * (t // 2)
        scenario[t] = {
            "ECU.out": Message.record(
                {
                    "piston1_temp": Field(
                        p1_f,
                        c_p1_f,
                        Dynamics("ECU.out", 1.0),
                        representation=Representation.CDR_DDS,
                        provenance=Provenance(("ECU",), timestamp_tick=t),
                    ),
                    "piston2_temp": Field(
                        p2_f,
                        c_p2_f,
                        Dynamics("ECU.out", 1.0),
                        representation=Representation.CDR_DDS,
                        provenance=Provenance(("ECU",), timestamp_tick=t),
                    ),
                    "crank_rpm": Field(
                        rpm,
                        c_rpm_u16,
                        Dynamics("ECU.out", 1.0),
                        representation=Representation.CDR_DDS,
                        provenance=Provenance(("ECU",), timestamp_tick=t),
                    ),
                    "manifold_p": Field(
                        14.7,
                        c_psi,
                        Dynamics("ECU.out", 1.0),
                        representation=Representation.CDR_DDS,
                        provenance=Provenance(("ECU",), timestamp_tick=t),
                    ),
                }
            ),
            "AirframeMount.out": Message.single(
                Field(
                    100.0,
                    c_mount_c,
                    Dynamics("AirframeMount.out", 0.0),
                    representation=Representation.NATIVE_STRUCT,
                    provenance=Provenance(("AirframeMount",), timestamp_tick=t),
                )
            ),
        }

    def f_to_k(f_val: float) -> float:
        return (float(f_val) - 32.0) * (5.0 / 9.0) + 273.15

    def phm_error(trig: Message, out: Message) -> float:
        p1_k = f_to_k(trig.fields["piston1_temp"].value)
        p2_k = f_to_k(trig.fields["piston2_temp"].value)
        expected_peak = max(p1_k, p2_k)
        expected_grad = expected_peak - (100.0 + 273.15)
        expected_omega = float(trig.fields["crank_rpm"].value) * (2.0 * math.pi / 60.0)

        err_peak = abs(expected_peak - float(out.fields["max_piston_temp"].value))
        err_grad = abs(expected_grad - float(out.fields["thermal_gradient"].value))
        err_omega = abs(expected_omega - float(out.fields["shaft_omega"].value))
        return err_peak + err_grad + err_omega

    ulsc = UniversalLSC(
        name="uLSC_PistonHierarchy",
        target_need_id="PHM.in",
        horizon=horizon,
        pre_trigger_fn=lambda t, env: env.get("ECU.out"),
        value_distance_fn=phm_error,
        tolerance=0.05,
        max_delay=1,
        enforce_silence=True,
    )

    def bounds(b: Board) -> None:
        b.add_component(
            ProducerBoundary(
                "ECU",
                "out",
                c_p1_f,
                shape=MessageShape(slots=ecu_slots, allowed_reps=frozenset({Representation.CDR_DDS})),
            )
        )
        b.add_component(
            ProducerBoundary(
                "AirframeMount",
                "out",
                c_mount_c,
                mode=TransferMode.PULL,
                rep=Representation.NATIVE_STRUCT,
            )
        )
        b.add_component(
            ConsumerBoundary("PHM", "in", MessageShape(slots=phm_slots))
        )

    ev = BoardEvaluator()
    snaps: List[ScoreBreakdown] = []

    # S0: Unconnected
    b0 = Board("Ex5_S0")
    bounds(b0)
    snaps.append(ev.evaluate(b0, ulsc, scenario, "S0: Unconnected hierarchy"))

    # S1: Transcode CDR_DDS -> NATIVE_STRUCT, Project (drop manifold_p), and Disassemble
    b1 = Board("Ex5_S1")
    bounds(b1)
    b1.add_component(
        RepresentationBridgeBlock(
            "CDR2Nat",
            color=None,
            in_rep=Representation.CDR_DDS,
            out_rep=Representation.NATIVE_STRUCT,
            slots=ecu_slots,
        )
    )
    b1.add_component(
        ProjectBlock("DropManifold", ecu_slots, ["piston1_temp", "piston2_temp", "crank_rpm"])
    )
    b1.add_component(
        DisassembleBlock("SplitECU", projected_slots, normalize_output_slot=True)
    )
    b1.connect("ECU.out", "CDR2Nat.in")
    b1.connect("CDR2Nat.out", "DropManifold.in")
    b1.connect("DropManifold.out", "SplitECU.in")
    snaps.append(ev.evaluate(b1, ulsc, scenario, "S1: +CDR_DDS decode, Project & Disassemble"))

    # S2: Recolor crankshaft RPM (uint16 -> float64 -> RadPerSec -> ShaftSpeed) + Pump & Recolor AirframeMount
    b2 = b1.clone("Ex5_S2")
    b2.add_component(RecolorBlock("RPM_P", c_rpm_u16, c_rpm_f64, value_fn=float))
    b2.add_component(
        RecolorBlock("RPM_L", c_rpm_f64, c_omega_eng, value_fn=lambda r: round(float(r) * 2.0 * math.pi / 60.0, 4))
    )
    b2.add_component(RecolorBlock("RPM_C", c_omega_eng, c_omega_air))
    b2.connect("SplitECU.out_crank_rpm", "RPM_P.in")
    b2.connect("RPM_P.out", "RPM_L.in")
    b2.connect("RPM_L.out", "RPM_C.in")

    b2.add_component(PumpBlock("MountPump", c_mount_c, period=2))
    b2.add_component(
        RecolorBlock("Mount_L", c_mount_c, c_mount_k, value_fn=lambda c: round(float(c) + 273.15, 4))
    )
    b2.connect("AirframeMount.out", "MountPump.in")
    b2.connect("MountPump.out", "Mount_L.in")
    snaps.append(ev.evaluate(b2, ulsc, scenario, "S2: +Shaft C/L/P recolor & Mount Pump"))

    # S3: Lying L-cast trap (passes Tier 1 & Tier 2, but forgets Fahrenheit->Kelvin conversion -> Tier 3 fail)
    therm_in_slots = {"p1": c_p1_f, "p2": c_p2_f, "mount": c_mount_k}
    therm_out_slots = {"max_piston_temp": c_peak_k, "thermal_gradient": c_grad_k}

    def bad_thermal_derive(msg: Message, state: Dict, tick: int):
        # Lying conversion: uses raw Fahrenheit numbers as if they were Kelvin!
        p1 = float(msg.fields["p1"].value)
        p2 = float(msg.fields["p2"].value)
        m_k = float(msg.fields["mount"].value)
        peak = max(p1, p2)
        grad = peak - m_k
        prov = msg.fields["p1"].provenance.append_op("BadThermal", tick)
        return (
            Message.record(
                {
                    "max_piston_temp": Field(peak, c_peak_k, Dynamics("o", 1.0), provenance=prov),
                    "thermal_gradient": Field(grad, c_grad_k, Dynamics("o", 1.0), provenance=prov),
                }
            ),
            state,
        )

    b3 = b2.clone("Ex5_S3")
    b3.add_component(AssembleBlock("AsmTherm", therm_in_slots))
    b3.add_component(
        DeriveBlock(
            "ThermDerive",
            MessageShape(slots=therm_in_slots),
            MessageShape(slots=therm_out_slots),
            bad_thermal_derive,
            static_cost=1.5,
        )
    )
    b3.add_component(DisassembleBlock("SplitTherm", therm_out_slots, normalize_output_slot=True))
    b3.add_component(AssembleBlock("AsmPHM", phm_slots))
    b3.connect("SplitECU.out_piston1_temp", "AsmTherm.in_p1")
    b3.connect("SplitECU.out_piston2_temp", "AsmTherm.in_p2")
    b3.connect("Mount_L.out", "AsmTherm.in_mount")
    b3.connect("AsmTherm.out", "ThermDerive.in")
    b3.connect("ThermDerive.out", "SplitTherm.in")
    b3.connect("SplitTherm.out_max_piston_temp", "AsmPHM.in_max_piston_temp")
    b3.connect("SplitTherm.out_thermal_gradient", "AsmPHM.in_thermal_gradient")
    b3.connect("RPM_C.out", "AsmPHM.in_shaft_omega")
    b3.connect("AsmPHM.out", "PHM.in")
    snaps.append(ev.evaluate(b3, ulsc, scenario, "S3: Lying Fahrenheit cast (Tier3 fail)"))

    # S4: Proper Fahrenheit->Kelvin conversion inside thermal synthesis (WIN)
    def good_thermal_derive(msg: Message, state: Dict, tick: int):
        p1_k = f_to_k(float(msg.fields["p1"].value))
        p2_k = f_to_k(float(msg.fields["p2"].value))
        m_k = float(msg.fields["mount"].value)
        peak = round(max(p1_k, p2_k), 4)
        grad = round(peak - m_k, 4)
        prov = msg.fields["p1"].provenance.append_op("GoodThermal", tick)
        return (
            Message.record(
                {
                    "max_piston_temp": Field(peak, c_peak_k, Dynamics("o", 1.0), provenance=prov),
                    "thermal_gradient": Field(grad, c_grad_k, Dynamics("o", 1.0), provenance=prov),
                }
            ),
            state,
        )

    b4 = b2.clone("Ex5_S4")
    b4.add_component(AssembleBlock("AsmTherm", therm_in_slots))
    b4.add_component(
        DeriveBlock(
            "ThermDerive",
            MessageShape(slots=therm_in_slots),
            MessageShape(slots=therm_out_slots),
            good_thermal_derive,
            static_cost=1.5,
        )
    )
    b4.add_component(DisassembleBlock("SplitTherm", therm_out_slots, normalize_output_slot=True))
    b4.add_component(AssembleBlock("AsmPHM", phm_slots))
    b4.connect("SplitECU.out_piston1_temp", "AsmTherm.in_p1")
    b4.connect("SplitECU.out_piston2_temp", "AsmTherm.in_p2")
    b4.connect("Mount_L.out", "AsmTherm.in_mount")
    b4.connect("AsmTherm.out", "ThermDerive.in")
    b4.connect("ThermDerive.out", "SplitTherm.in")
    b4.connect("SplitTherm.out_max_piston_temp", "AsmPHM.in_max_piston_temp")
    b4.connect("SplitTherm.out_thermal_gradient", "AsmPHM.in_thermal_gradient")
    b4.connect("RPM_C.out", "AsmPHM.in_shaft_omega")
    b4.connect("AsmPHM.out", "PHM.in")
    snaps.append(ev.evaluate(b4, ulsc, scenario, "S4: Full hierarchical C/L/P + Derive (WIN)"))

    return snaps


example_05_piston_hierarchy = example_05_piston
example_05_piston_rotary = example_05_piston

