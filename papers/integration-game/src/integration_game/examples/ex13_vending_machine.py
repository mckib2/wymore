"""
Example 13: Reactive Vending Machine (Stateful Behavioral Protocol Mediation).
Demonstrates:
  - CoinSlot (PUSH): emits (Payment.Coin, Cents, uint16) -> 25 cents at t=0, 75 cents at t=1
  - Keypad (PULL): holds (Selection.Code, ItemID, string) -> "A1"
  - Dispenser (PUSH): expects RECORD {paid: (Payment.Credit, USD, float64), item: (Selection.Code, ItemID, string)}
  - Behavioral contract (UniversalLSC with enforce_silence=True):
      * Must remain strictly silent at t=0 when credit is only $0.25 (< $1.00 price)
      * Must dispense {paid: 1.00, item: "A1"} at t=1 when accumulated credit reaches $1.00!
  - Stateless Assembly trap emits prematurely at t=0 (silence breach) and fails to accumulate at t=1;
    stateful FSM DeriveBlock accumulates credit and dispenses only when balance >= $1.00 (WIN).
"""
from __future__ import annotations

from typing import Dict, List

from integration_game import (
    AssembleBlock,
    Board,
    BoardEvaluator,
    Color,
    ConsumerBoundary,
    DeriveBlock,
    Dynamics,
    Field,
    Message,
    MessageShape,
    ProducerBoundary,
    Provenance,
    PumpBlock,
    RecolorBlock,
    ScoreBreakdown,
    TransferMode,
    UniversalLSC,
)


def example_13_vending_machine() -> List[ScoreBreakdown]:
    c_cents = Color("Payment.Coin", "Cents", "uint16")
    c_usd = Color("Payment.Credit", "USD", "float64")
    c_item = Color("Selection.Code", "ItemID", "string")

    dispense_slots = {"paid": c_usd, "item": c_item}
    horizon = 3

    scenario = {
        0: {
            "CoinSlot.out": Message.single(
                Field(25, c_cents, Dynamics("CoinSlot.out", 1.0), provenance=Provenance(("CoinSlot",), timestamp_tick=0))
            ),
            "Keypad.out": Message.single(
                Field("A1", c_item, Dynamics("Keypad.out", 0.0), provenance=Provenance(("Keypad",), timestamp_tick=0))
            ),
        },
        1: {
            "CoinSlot.out": Message.single(
                Field(75, c_cents, Dynamics("CoinSlot.out", 1.0), provenance=Provenance(("CoinSlot",), timestamp_tick=1))
            ),
        },
    }

    def dispense_error(trig: Message, out: Message) -> float:
        paid_err = abs(1.00 - float(out.fields["paid"].value))
        item_err = 0.0 if str(out.fields["item"].value) == "A1" else 10.0
        return paid_err + item_err

    # Only trigger when the 75-cent coin arrives at t=1 (completing $1.00);
    # enforce_silence=True penalizes any premature emission at t=0!
    ulsc = UniversalLSC(
        name="uLSC_VendingFSM",
        target_need_id="Dispenser.in",
        horizon=horizon,
        pre_trigger_fn=lambda t, env: env.get("CoinSlot.out") if t == 1 else None,
        value_distance_fn=dispense_error,
        tolerance=0.01,
        min_delay=0,
        max_delay=0,
        enforce_silence=True,
    )

    def bounds(b: Board) -> None:
        b.add_component(ProducerBoundary("CoinSlot", "out", c_cents, mode=TransferMode.PUSH))
        b.add_component(ProducerBoundary("Keypad", "out", c_item, mode=TransferMode.PULL))
        b.add_component(ConsumerBoundary("Dispenser", "in", MessageShape(slots=dispense_slots), mode=TransferMode.PUSH))

    ev = BoardEvaluator()
    snaps: List[ScoreBreakdown] = []

    # S0: Unconnected
    b0 = Board("Ex13_S0")
    bounds(b0)
    snaps.append(ev.evaluate(b0, ulsc, scenario, "S0: Unconnected vending interfaces"))

    # S1: Recolor Coin (Cents -> USD) + Pump Keypad (PULL -> PUSH)
    b1 = Board("Ex13_S1")
    bounds(b1)
    b1.add_component(
        RecolorBlock("CentsToUSD", c_cents, c_usd, value_fn=lambda c: round(float(c) / 100.0, 2))
    )
    b1.add_component(PumpBlock("KeyPump", c_item, period=1))
    b1.connect("CoinSlot.out", "CentsToUSD.in")
    b1.connect("Keypad.out", "KeyPump.in")
    snaps.append(ev.evaluate(b1, ulsc, scenario, "S1: +Cents->USD Recolor & Keypad Pump"))

    # S2: Stateless AssembleBlock wired directly to Dispenser (emits $0.25 at t=0 -> silence breach, and $0.75 at t=1 -> value breach!)
    b2 = b1.clone("Ex13_S2")
    b2.add_component(AssembleBlock("PairInputs", dispense_slots))
    b2.connect("CentsToUSD.out", "PairInputs.in_paid")
    b2.connect("KeyPump.out", "PairInputs.in_item")
    b2.connect("PairInputs.out", "Dispenser.in")
    snaps.append(ev.evaluate(b2, ulsc, scenario, "S2: Stateless Assemble (premature emit)"))

    # S3: Stateful Vending FSM DeriveBlock accumulates credit across ticks and dispenses at >= $1.00 (WIN)
    def vending_fsm(msg: Message, state: Dict, tick: int):
        coin_usd = float(msg.fields["paid"].value)
        item_str = str(msg.fields["item"].value)
        bal = round(float(state.get("balance", 0.0)) + coin_usd, 2)
        if bal >= 1.00:
            state["balance"] = 0.0
            prov = msg.fields["paid"].provenance.append_op("VendingFSM", tick)
            out_msg = Message.record(
                {
                    "paid": Field(bal, c_usd, Dynamics("VendingFSM.out", 1.0), provenance=prov),
                    "item": Field(item_str, c_item, Dynamics("VendingFSM.out", 1.0), provenance=prov),
                }
            )
            return out_msg, state
        state["balance"] = bal
        return None, state  # Remain silent until threshold is met!

    b3 = b1.clone("Ex13_S3")
    b3.add_component(AssembleBlock("PairInputs", dispense_slots))
    b3.add_component(
        DeriveBlock(
            "VendingFSM",
            MessageShape(slots=dispense_slots),
            MessageShape(slots=dispense_slots),
            vending_fsm,
            init_state_fn=lambda: {"balance": 0.0},
        )
    )
    b3.connect("CentsToUSD.out", "PairInputs.in_paid")
    b3.connect("KeyPump.out", "PairInputs.in_item")
    b3.connect("PairInputs.out", "VendingFSM.in")
    b3.connect("VendingFSM.out", "Dispenser.in")
    snaps.append(ev.evaluate(b3, ulsc, scenario, "S3: Stateful Vending FSM Controller (WIN)"))

    return snaps
