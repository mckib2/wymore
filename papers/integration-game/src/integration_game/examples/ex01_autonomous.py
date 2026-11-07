"""
Example 1: Autonomous Closed-Loop Cryogenic Thermal Regulation (I_ext = ∅, O_ext = ∅).
Demonstrates how a completely autonomous system (zero external environment inputs)
is mediated across two internal paths:
  1. Forward sensing: Plant (Payload.FocalPlane.Temp, Kelvin, float32, PUSH)
     -> Regulator (Chamber.Temp, Celsius, float32, PULL)
  2. Feedback actuation: Regulator (Chiller.Command.Power, Milliwatts, float32, PULL)
     -> Plant (Cryocooler.Drive.Power, Watts, float32, PUSH)
Evaluated via an internal diagnostic monitor Need observing the closed-loop plant state.
"""
from __future__ import annotations

from typing import Any, Dict, List, Optional

from integration_game import (
    Board,
    BoardEvaluator,
    CacheStoreBlock,
    Color,
    ConsumerBoundary,
    Dynamics,
    Field,
    Message,
    MessageShape,
    Provenance,
    PumpBlock,
    RecolorBlock,
    ScoreBreakdown,
    TransferMode,
    UniversalLSC,
    WymorianComponent,
)


class CryoPlantComponent(WymorianComponent):
    """
    Internal Cryogenic Focal Plane Plant & Sensor:
      - State T_core(0) = 85.0 K, drifts +1.0 K/tick without cooling.
      - Need `cool_in`: Cryocooler.Drive.Power (Watts, float32, PUSH), reduces T by 0.25 * P_watts.
      - Offer `temp_out`: Payload.FocalPlane.Temp (Kelvin, float32, PUSH).
      - Offer `diag_out`: Sys.Cryo.InBand ( Kelvin, float32, PUSH) for non-intrusive state readout.
    """

    def __init__(self, c_temp: Color, c_power: Color):
        super().__init__(comp_id="CryoPlant", static_cost=0.0, is_boundary=True)
        self.c_temp = c_temp
        self.c_power = c_power
        self.add_need("cool_in", MessageShape.single(c_power), mode=TransferMode.PUSH)
        self.add_offer("temp_out", MessageShape.single(c_temp), mode=TransferMode.PUSH, velocity=1.0)
        self.add_offer("diag_out", MessageShape.single(c_temp), mode=TransferMode.PUSH, velocity=1.0)

    def reset(self) -> None:
        super().reset()
        self.state = {"T_core": 85.0}

    def step(self, tick: int, env_inputs: Optional[Dict[str, Message]] = None) -> None:
        cool_if = self.interfaces["cool_in"]
        temp_if = self.interfaces["temp_out"]
        diag_if = self.interfaces["diag_out"]
        temp_if.outbox = None
        diag_if.outbox = None

        p_watts = 0.0
        if cool_if.inbox is not None:
            p_watts = float(cool_if.inbox.first_field().value)
            cool_if.inbox = None

        # Thermal physics: +1.0 K parasitic heat load, -0.25 K per Watt of cooling
        t_curr = float(self.state.get("T_core", 85.0))
        if tick > 0:
            t_curr = t_curr + 1.0 - 0.25 * p_watts
        self.state["T_core"] = round(t_curr, 4)

        f = Field(
            value=self.state["T_core"],
            color=self.c_temp,
            dynamics=Dynamics(position=temp_if.full_id, velocity=1.0),
            provenance=Provenance(sources=("CryoPlant",), timestamp_tick=tick),
        )
        msg = Message.single(f)
        temp_if.outbox = msg
        diag_if.outbox = msg


class LegacyRegulatorComponent(WymorianComponent):
    """
    COTS Proportional Chiller Regulator:
      - Need `temp_in`: Chamber.Temp (Celsius, float32, PULL).
      - Offer `cmd_out`: Chiller.Command.Power (Milliwatts, float32, PULL).
    """

    def __init__(self, c_temp_c: Color, c_cmd_mw: Color):
        super().__init__(comp_id="Regulator", static_cost=0.0, is_boundary=True)
        self.c_temp_c = c_temp_c
        self.c_cmd_mw = c_cmd_mw
        self.add_need("temp_in", MessageShape.single(c_temp_c), mode=TransferMode.PULL)
        self.add_offer("cmd_out", MessageShape.single(c_cmd_mw), mode=TransferMode.PULL, velocity=0.0)

    def reset(self) -> None:
        super().reset()
        self.state = {"cmd_mw": 0.0}

    def wants_to_pull(self, tick: int) -> bool:
        return True

    def step(self, tick: int, env_inputs: Optional[Dict[str, Message]] = None) -> None:
        in_if = self.interfaces["temp_in"]
        out_if = self.interfaces["cmd_out"]
        if in_if.inbox is not None:
            t_c = float(in_if.inbox.first_field().value)
            in_if.inbox = None
            # Target setpoint: 75.5 K = -197.65 C; proportional gain = 2000 mW/K (2 W/K)
            # Loop gain K = 0.25 * 2.0 = 0.5 < 1.0 -> stable convergence to 77.5 K equilibrium!
            err = t_c - (-197.65)
            cmd_mw = max(0.0, 2000.0 * err)
            self.state["cmd_mw"] = round(cmd_mw, 2)

        f_out = Field(
            value=self.state["cmd_mw"],
            color=self.c_cmd_mw,
            dynamics=Dynamics(position=out_if.full_id, velocity=0.0),
            provenance=Provenance(sources=("Regulator",), timestamp_tick=tick),
        )
        out_if.outbox = Message.single(f_out)


def example_01_autonomous() -> List[ScoreBreakdown]:
    c_plant_k = Color("Payload.FocalPlane.Temp", "Kelvin", "float32")
    c_reg_c = Color("Chamber.Temp", "Celsius", "float32")
    c_reg_mw = Color("Chiller.Command.Power", "Milliwatts", "float32")
    c_plant_w = Color("Cryocooler.Drive.Power", "Watts", "float32")

    horizon = 12
    scenario: Dict[int, Dict[str, Message]] = {}  # Zero external inputs (autonomous)

    def steady_state_err(trig: Message, out: Message) -> float:
        t_k = float(out.first_field().value)
        # Target equilibrium band: [76.5 K, 78.5 K] (center 77.5 K, tolerance 1.0 K)
        return abs(t_k - 77.5)

    ulsc = UniversalLSC(
        name="uLSC_AutonomousCryoLoop",
        target_need_id="DiagMonitor.in",
        horizon=horizon,
        # Check steady-state thermal band on ticks t >= 6
        pre_trigger_fn=lambda t, env: Message.single(Field(77.5, c_plant_k)) if t >= 6 else None,
        value_distance_fn=steady_state_err,
        tolerance=1.0,
        min_delay=0,
        max_delay=0,
        enforce_silence=False,
    )

    def base_board(name: str) -> Board:
        b = Board(name)
        b.add_component(CryoPlantComponent(c_plant_k, c_plant_w))
        b.add_component(LegacyRegulatorComponent(c_reg_c, c_reg_mw))
        b.add_component(ConsumerBoundary("DiagMonitor", "in", MessageShape.single(c_plant_k)))
        b.connect("CryoPlant.diag_out", "DiagMonitor.in")
        return b

    ev = BoardEvaluator()
    snaps: List[ScoreBreakdown] = []

    # S0: Open loop (Plant and Regulator completely unwired; T_core drifts to 96 K -> breach)
    b0 = base_board("Ex1_S0")
    snaps.append(ev.evaluate(b0, ulsc, scenario, "S0: Open-loop plant (thermal runaway)"))

    # S1: Forward path recolored (Kelvin -> Celsius) and cached (PUSH -> PULL) into Regulator
    b1 = base_board("Ex1_S1")
    b1.add_component(RecolorBlock("Fwd_C", c_plant_k, Color("Chamber.Temp", "Kelvin", "float32")))
    b1.add_component(
        RecolorBlock(
            "Fwd_L",
            Color("Chamber.Temp", "Kelvin", "float32"),
            c_reg_c,
            value_fn=lambda k: round(float(k) - 273.15, 4),
        )
    )
    b1.add_component(CacheStoreBlock("SenseCache", c_reg_c, retain_on_read=True))
    b1.connect("CryoPlant.temp_out", "Fwd_C.in")
    b1.connect("Fwd_C.out", "Fwd_L.in")
    b1.connect("Fwd_L.out", "SenseCache.in")
    b1.connect("SenseCache.out", "Regulator.temp_in")
    snaps.append(ev.evaluate(b1, ulsc, scenario, "S1: Sensing path mediated (feedback open)"))

    # S2: Feedback path wired with Pump (PULL->PUSH) and Recolor_C, but missing mW->W unit scaling (over-cools!)
    b2 = b1.clone("Ex1_S2")
    b2.add_component(PumpBlock("ActPump", c_reg_mw, period=1))
    b2.add_component(RecolorBlock("Fb_Bad", c_reg_mw, c_plant_w, value_fn=float))
    b2.connect("Regulator.cmd_out", "ActPump.in")
    b2.connect("ActPump.out", "Fb_Bad.in")
    b2.connect("Fb_Bad.out", "CryoPlant.cool_in")
    snaps.append(ev.evaluate(b2, ulsc, scenario, "S2: +Pump & bad mW->W cast (Tier3 breach)"))

    # S3: Proper feedback Recolor_C + Recolor_L (mW * 1e-3 -> W) + Pump -> closed-loop stabilizes at 77.8 K (WIN)
    b3 = b1.clone("Ex1_S3")
    b3.add_component(PumpBlock("ActPump", c_reg_mw, period=1))
    b3.add_component(RecolorBlock("Fb_C", c_reg_mw, Color("Cryocooler.Drive.Power", "Milliwatts", "float32")))
    b3.add_component(
        RecolorBlock(
            "Fb_L",
            Color("Cryocooler.Drive.Power", "Milliwatts", "float32"),
            c_plant_w,
            value_fn=lambda mw: round(float(mw) * 1e-3, 4),
        )
    )
    b3.connect("Regulator.cmd_out", "ActPump.in")
    b3.connect("ActPump.out", "Fb_C.in")
    b3.connect("Fb_C.out", "Fb_L.in")
    b3.connect("Fb_L.out", "CryoPlant.cool_in")
    snaps.append(ev.evaluate(b3, ulsc, scenario, "S3: Closed-loop C/L + Cache/Pump (WIN)"))

    return snaps
