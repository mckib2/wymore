"""Core unit tests: ontology contracts, TBA/RM, moves, aggregations, kinematics."""
from __future__ import annotations

import pytest

from integration_game import (
    AddOperator,
    AddRoute,
    AggregationKind,
    Board,
    CacheStoreBlock,
    Color,
    ConsumerBoundary,
    Dynamics,
    Field,
    IllegalMoveError,
    Message,
    MessageShape,
    Play,
    ProducerBoundary,
    Provenance,
    PumpBlock,
    RecolorBlock,
    Representation,
    RMState,
    TransferMode,
    UniversalLSC,
)


def test_need_xor_offer():
    from integration_game.interfaces import Interface, NeedSpec, OfferSpec

    shape = MessageShape.single(Color("A", "u", "f"))
    with pytest.raises(ValueError):
        Interface("x", "c", need=NeedSpec(shape, TransferMode.PUSH), offer=OfferSpec(shape, TransferMode.PUSH))


def test_message_sequence_and_choice():
    c = Color("X", "u", "f")
    seq = Message.as_sequence([Field(1, c), Field(2, c)])
    assert seq.kind == AggregationKind.SEQUENCE
    assert MessageShape.sequence(c).kind == AggregationKind.SEQUENCE
    ch = Message.as_choice("a", Field(1, c))
    assert ch.kind == AggregationKind.CHOICE
    shape = MessageShape.choice({"a": c, "b": c})
    assert ch.matches_shape(shape)


def test_cache_decelerates_and_pump_accelerates():
    c = Color("D", "u", "f")
    board = Board("kin")
    board.add_component(ProducerBoundary("P", "out", c))
    board.add_component(CacheStoreBlock("Cache", c, retain_on_read=False))
    board.add_component(PumpBlock("Pump", c, period=1))
    board.add_component(ConsumerBoundary("C", "in", MessageShape.single(c)))
    board.connect("P.out", "Cache.in")
    board.connect("Cache.out", "Pump.in")
    board.connect("Pump.out", "C.in")
    scenario = {
        0: {
            "P.out": Message.single(
                Field(1, c, Dynamics("P", 1.0), provenance=Provenance(timestamp_tick=0))
            )
        }
    }
    out = board.simulate(scenario, 2)
    assert 0 in out["C.in"]
    delivered = out["C.in"][0].first_field()
    assert delivered.dynamics.velocity > 0.0
    assert delivered.dynamics.acceleration > 0.0


def test_ulsc_cut_progress_only_on_proper_fulfillment():
    ulsc = UniversalLSC(
        name="t",
        target_need_id="N",
        horizon=3,
        pre_trigger_fn=lambda t, env: Message.single(Field(t, Color("A", "u", "f"))) if t == 0 else None,
        value_distance_fn=lambda trig, out: 10.0,  # always bad
        tolerance=0.0,
        max_delay=1,
        enforce_silence=True,
    )
    outs = {0: Message.single(Field(0, Color("A", "u", "f")))}
    res = ulsc.evaluate_trace({}, outs)
    assert res.cut_progress_ratio == 0.0
    assert res.hot_breaches >= 1
    assert RMState.BREACH in res.rm_state_trace


def test_ulsc_silence_and_win():
    c = Color("A", "u", "f")
    ulsc = UniversalLSC(
        name="t",
        target_need_id="N",
        horizon=3,
        pre_trigger_fn=lambda t, env: Message.single(Field(1, c)) if t == 1 else None,
        value_distance_fn=lambda trig, out: abs(float(trig.first_field().value) - float(out.first_field().value)),
        tolerance=0.0,
        max_delay=0,
        enforce_silence=True,
    )
    ok = ulsc.evaluate_trace({}, {1: Message.single(Field(1, c))})
    assert ok.satisfied
    assert ok.cut_progress_ratio == 1.0
    bad = ulsc.evaluate_trace({}, {1: Message.single(Field(1, c)), 2: Message.single(Field(1, c))})
    assert not bad.satisfied
    assert bad.silence_violations >= 1


def test_play_illegal_strict_route():
    play = Play.new("p")
    c1, c2 = Color("A", "u", "f"), Color("B", "u", "f")
    play.board.add_component(ProducerBoundary("P", "out", c1))
    play.board.add_component(ConsumerBoundary("C", "in", MessageShape.single(c2)))
    with pytest.raises(IllegalMoveError):
        play.apply(AddRoute("P.out", "C.in", strict=True))


def test_play_add_operator_and_clone():
    play = Play.new("p")
    c = Color("A", "u", "f")
    play.apply(AddOperator(RecolorBlock("R", c, c)))
    assert "R" in play.board.components
    cloned = play.clone("p2")
    assert "R" in cloned.board.components
    assert cloned.board is not play.board


def test_provenance_gates_transfer():
    c = Color("A", "u", "f")
    board = Board("prov")
    board.add_component(ProducerBoundary("P", "out", c))
    need = MessageShape.single(c, min_trust=0.99, required_assurance="TMR_VOTED")
    board.add_component(ConsumerBoundary("C", "in", need))
    board.connect("P.out", "C.in")
    scenario = {
        0: {
            "P.out": Message.single(
                Field(
                    1,
                    c,
                    Dynamics("P", 1.0),
                    provenance=Provenance(trust_score=0.5, assurance_level="UNVERIFIED", timestamp_tick=0),
                )
            )
        }
    }
    out = board.simulate(scenario, 1)
    assert out["C.in"] == {}


def test_representation_mismatch_blocks_transfer():
    c = Color("A", "u", "f")
    board = Board("rep")
    board.add_component(
        ProducerBoundary("P", "out", c, rep=Representation.BYTE_BLOB_JSON)
    )
    board.add_component(
        ConsumerBoundary("C", "in", MessageShape.single(c, reps=(Representation.NATIVE_STRUCT,)))
    )
    board.connect("P.out", "C.in")
    scenario = {
        0: {
            "P.out": Message.single(
                Field(
                    "{}",
                    c,
                    Dynamics("P", 1.0),
                    representation=Representation.BYTE_BLOB_JSON,
                    provenance=Provenance(timestamp_tick=0),
                )
            )
        }
    }
    assert board.simulate(scenario, 1)["C.in"] == {}


def test_topological_execution_order_independence():
    """Adding interior blocks in reverse vs forward causal order yields identical simulation output."""
    c1 = Color("Nav.Pos", "cm", "int32")
    c2 = Color("Nav.Pos", "cm", "float64")
    c3 = Color("Nav.Pos", "m", "float64")
    scenario = {
        0: {
            "P.out": Message.single(
                Field(250, c1, Dynamics("P", 1.0), provenance=Provenance(timestamp_tick=0))
            )
        }
    }

    # Board 1: Forward insertion order (R1 then R2)
    b_fwd = Board("fwd")
    b_fwd.add_component(ProducerBoundary("P", "out", c1))
    b_fwd.add_component(ConsumerBoundary("C", "in", MessageShape.single(c3)))
    b_fwd.add_component(RecolorBlock("R1", c1, c2, value_fn=float))
    b_fwd.add_component(RecolorBlock("R2", c2, c3, value_fn=lambda x: x / 100.0))
    b_fwd.connect("P.out", "R1.in")
    b_fwd.connect("R1.out", "R2.in")
    b_fwd.connect("R2.out", "C.in")

    # Board 2: Reverse insertion order (R2 added BEFORE R1!)
    b_rev = Board("rev")
    b_rev.add_component(ProducerBoundary("P", "out", c1))
    b_rev.add_component(ConsumerBoundary("C", "in", MessageShape.single(c3)))
    b_rev.add_component(RecolorBlock("R2", c2, c3, value_fn=lambda x: x / 100.0))
    b_rev.add_component(RecolorBlock("R1", c1, c2, value_fn=float))
    b_rev.connect("P.out", "R1.in")
    b_rev.connect("R1.out", "R2.in")
    b_rev.connect("R2.out", "C.in")

    out_fwd = b_fwd.simulate(scenario, 1)
    out_rev = b_rev.simulate(scenario, 1)
    assert 0 in out_fwd["C.in"] and 0 in out_rev["C.in"]
    assert out_fwd["C.in"][0].first_field().value == pytest.approx(2.5)
    assert out_rev["C.in"][0].first_field().value == pytest.approx(2.5)


def test_single_pull_per_tick_with_multiple_interior_blocks():
    """A PULL route from a consume-on-read CacheStoreBlock pops at most 1 item per tick."""
    c = Color("Q.Item", "idx", "int32")
    b = Board("single_pull")
    b.add_component(ProducerBoundary("P", "out", c))
    b.add_component(CacheStoreBlock("FIFO", c, retain_on_read=False, capacity=4))
    # Add several unrelated interior blocks to ensure _propagate_pull_into does not over-pop
    for i in range(4):
        b.add_component(RecolorBlock(f"Dummy_{i}", c, c))
    b.add_component(ConsumerBoundary("C", "in", MessageShape.single(c), mode=TransferMode.PULL))
    b.connect("P.out", "FIFO.in")
    b.connect("FIFO.out", "C.in")

    scenario = {
        0: {"P.out": Message.single(Field(10, c, Dynamics("P", 1.0), provenance=Provenance(timestamp_tick=0)))},
        1: {"P.out": Message.single(Field(20, c, Dynamics("P", 1.0), provenance=Provenance(timestamp_tick=1)))},
    }
    out = b.simulate(scenario, 2)
    assert out["C.in"][0].first_field().value == 10
    assert out["C.in"][1].first_field().value == 20


def test_uddl_hierarchical_color_distance():
    """Multi-level dot-path hierarchy in C gives graded semantic distances."""
    c_p1 = Color("Engine.Cylinder1.Piston.CrownTemp", "K", "f64")
    c_p2 = Color("Engine.Cylinder1.Piston.SkirtTemp", "K", "f64")
    c_cyl2 = Color("Engine.Cylinder2.Piston.CrownTemp", "K", "f64")
    c_air = Color("Airframe.Nacelle.MountTemp", "K", "f64")

    # Deeper shared prefix (Engine.Cylinder1.Piston.*) is closer than (Engine.*) which is closer than (Airframe.*)
    assert 0.0 < c_p1.distance_to(c_p2) < c_p1.distance_to(c_cyl2) < c_p1.distance_to(c_air)

