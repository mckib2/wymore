"""Registry and compatibility exports for the 14 Progressive Integration Game Examples.

Each example resides in its own dedicated module (`ex01_autonomous` .. `ex14_cost_sensitivity`)
and returns a `List[ScoreBreakdown]` evaluated by `BoardEvaluator`.
"""

from __future__ import annotations

from typing import Callable, List, Tuple

from integration_game.examples.ex01_autonomous import example_01_autonomous
from integration_game.examples.ex02_ping_pong import example_02_ping_pong
from integration_game.examples.ex03_kalman import example_03_kalman
from integration_game.examples.ex04_multi_representation import (
    example_04_multi_rep,
    example_04_multi_representation,
    example_04_rest_db,
)
from integration_game.examples.ex05_piston_hierarchy import (
    example_05_piston,
    example_05_piston_hierarchy,
    example_05_piston_rotary,
)
from integration_game.examples.ex06_calculator import example_06_calculator
from integration_game.examples.ex07_hard_latency import example_07_latency
from integration_game.examples.ex08_multi_flow import example_08_fanout
from integration_game.examples.ex09_mismatched_ticks import example_09_ticks
from integration_game.examples.ex10_provenance_tmr import example_10_provenance
from integration_game.examples.ex11_temporal_join import example_11_temporal_join
from integration_game.examples.ex12_failover import example_12_failover
from integration_game.examples.ex13_vending_machine import example_13_vending_machine
from integration_game.examples.ex14_cost_sensitivity import example_14_cost_sensitivity
from integration_game.scoring import ScoreBreakdown


ALL_EXAMPLES: List[Tuple[str, Callable[[], List[ScoreBreakdown]]]] = [
    ("Ex01: Autonomous Closed-Loop Cryogenic Regulation", example_01_autonomous),
    ("Ex02: Ping/Pong Request/Response Causality", example_02_ping_pong),
    ("Ex03: Multi-Rate Kalman Kinematic Estimator", example_03_kalman),
    ("Ex04: Multi-Representation Tactical Data Link Gateway", example_04_multi_rep),
    ("Ex05: UDDL Hierarchical Airframe/Engine/Piston Model", example_05_piston),
    ("Ex06: Non-Commutative Kinetic Energy ALU", example_06_calculator),
    ("Ex07: Hard Real-Time Latency Threat Avoidance", example_07_latency),
    ("Ex08: Dual-Producer / Dual-Consumer FanOut & Assembly", example_08_fanout),
    ("Ex09: Mismatched Clocks (10Hz->50Hz) with Freshness Gate", example_09_ticks),
    ("Ex10: Provenance TMR Voting & Glitch Masking", example_10_provenance),
    ("Ex11: Asynchronous Keyed Temporal-Window Join", example_11_temporal_join),
    ("Ex12: Dynamic Runtime Failover Multiplexer", example_12_failover),
    ("Ex13: Stateful Reactive Vending Machine FSM", example_13_vending_machine),
    ("Ex14: Cost Sensitivity & Pareto Architecture Ranking", example_14_cost_sensitivity),
]

__all__ = [
    "example_01_autonomous",
    "example_02_ping_pong",
    "example_03_kalman",
    "example_04_multi_rep",
    "example_04_multi_representation",
    "example_04_rest_db",
    "example_05_piston",
    "example_05_piston_hierarchy",
    "example_05_piston_rotary",
    "example_06_calculator",
    "example_07_latency",
    "example_08_fanout",
    "example_09_ticks",
    "example_10_provenance",
    "example_11_temporal_join",
    "example_12_failover",
    "example_13_vending_machine",
    "example_14_cost_sensitivity",
    "ALL_EXAMPLES",
]
