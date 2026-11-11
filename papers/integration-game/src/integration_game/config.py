"""
config.py
Centralized, tunable configuration dataclasses for the Integration Game.
Eliminates hard-coded magic numbers across primitives, components, board,
uLSC Reward Machine, and the multi-tier cost/fitness evaluator.
"""
from __future__ import annotations

from dataclasses import dataclass, field, replace
from typing import Any


@dataclass(frozen=True)
class ColorDistanceConfig:
    """Weights for TBox Color (C, L, P) and MessageShape semantic distance."""
    c_same_root_penalty: float = 0.6
    c_diff_root_penalty: float = 1.0
    l_mismatch_penalty: float = 1.0
    p_mismatch_penalty: float = 1.0
    kind_mismatch_penalty: float = 1.0
    slot_mismatch_penalty: float = 1.0

    def with_overrides(self, **kwargs: Any) -> "ColorDistanceConfig":
        return replace(self, **kwargs)


@dataclass(frozen=True)
class CarrierCostConfig:
    """Static Route Carrier transport costs (never Color axes)."""
    in_process: float = 0.0
    shared_memory: float = 0.2
    generic_tree: float = 0.5
    ipc_serialized: float = 3.0
    mil_std_1553: float = 4.0
    dds_topic: float = 2.5
    generic_tree_threshold: float = 0.5
    ipc_threshold: float = 3.0

    def with_overrides(self, **kwargs: Any) -> "CarrierCostConfig":
        return replace(self, **kwargs)


@dataclass(frozen=True)
class CatalogCostConfig:
    """Default static costs and intrinsic parameters for technology catalog T."""
    source: float = 0.2
    sink: float = 0.1
    recolor_c: float = 0.5
    recolor_l: float = 1.0
    recolor_p: float = 0.1
    recolor_min: float = 0.1
    rep_bridge: float = 0.4
    cache_base: float = 0.5
    cache_per_extra_slot: float = 0.05
    pump: float = 0.6
    rate_adapter: float = 0.5
    rate_adapter_loss_per_period: float = 0.1
    stale_gate: float = 0.3
    assemble: float = 0.3
    disassemble: float = 0.2
    project: float = 0.2
    inject: float = 0.2
    fan_out: float = 0.2
    fan_in: float = 0.2
    join: float = 0.8
    derive: float = 2.0
    filter: float = 0.4
    prov_verify: float = 0.5
    prov_tmr: float = 1.5
    tmr_default_min_trust: float = 0.9
    tmr_trust_boost: float = 0.25
    tmr_trust_floor: float = 0.95
    mux_switch: float = 0.4

    def with_overrides(self, **kwargs: Any) -> "CatalogCostConfig":
        return replace(self, **kwargs)


@dataclass(frozen=True)
class RewardMachineConfig:
    """Reward Machine pulses and default uLSC timing tolerances."""
    r_prog: float = 1.0
    r_goal: float = 5.0
    r_breach: float = -10000.0
    default_tolerance: float = 1e-3
    default_min_delay: int = 0
    default_max_delay: int = 2

    def with_overrides(self, **kwargs: Any) -> "RewardMachineConfig":
        return replace(self, **kwargs)


@dataclass(frozen=True)
class ScoringConfig:
    """
    Weights and scaling parameters for the four-component cost functional J
    and human-readable fitness score S.
    Calibrated so every valid mediation operator from CatalogCostConfig
    yields a strictly positive net potential reduction (Axiom A3).
    """
    # Tier 1: Structural, semantic, representation, and provenance gaps
    w_unconnected: float = 8.0
    w_color: float = 8.0
    w_rep: float = 5.0
    w_prov: float = 6.0

    # Tier 2: Kinematic push/pull and velocity/rate compatibility
    w_kin: float = 10.0
    w_velocity: float = 5.0

    # Tier 3: uLSC / Timed Buchi Automaton behavioral penalties
    w_cut_progress: float = 25.0
    w_breach: float = 8.0
    w_clock_overrun: float = 4.0
    w_val_err: float = 5.0
    omega_breach: float = 10000.0
    use_omega: bool = True

    # Dynamic operational QoS weights (Paper Eq. 8)
    w_lat: float = 1.0
    w_loss: float = 1.0
    w_drop: float = 2.0
    gamma: float = 1.0

    # Fitness normalization
    fitness_ceiling: float = 100.0
    soft_error_scale: float = 15.0
    default_no_offer_color_dist: float = 3.0

    def with_overrides(self, **kwargs: Any) -> "ScoringConfig":
        return replace(self, **kwargs)


@dataclass(frozen=True)
class GameConfig:
    """Master configuration container for the Integration Game."""
    color_distance: ColorDistanceConfig = field(default_factory=ColorDistanceConfig)
    carrier_costs: CarrierCostConfig = field(default_factory=CarrierCostConfig)
    catalog_costs: CatalogCostConfig = field(default_factory=CatalogCostConfig)
    reward_machine: RewardMachineConfig = field(default_factory=RewardMachineConfig)
    scoring: ScoringConfig = field(default_factory=ScoringConfig)

    def with_overrides(self, **kwargs: Any) -> "GameConfig":
        return replace(self, **kwargs)


DEFAULT_CONFIG = GameConfig()
