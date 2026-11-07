"""
ulsc.py
IOR encoded as Universal Live Sequence Charts, compiled into an explicit
Timed Büchi Automaton / Reward Machine monitor.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import Callable, Dict, List, Optional

from .primitives import Message


class RMState(str, Enum):
    IDLE_WAIT_PRE = "IDLE_WAIT_PRE"
    PRE_MATCHING = "PRE_MATCHING"
    MAIN_ACTIVE = "MAIN_ACTIVE"
    SILENCE_CHECK = "SILENCE_CHECK"
    COMPLETED = "COMPLETED"
    BREACH = "BREACH"


@dataclass
class RewardPulse:
    tick: int
    amount: float
    reason: str
    state: RMState


@dataclass
class ObligationWindow:
    trigger_tick: int
    trigger_msg: Message
    min_tick: int
    max_tick: int
    fulfilled: bool = False
    fulfilled_properly: bool = False  # on-time AND within tolerance
    breached: bool = False


@dataclass
class TBAEvaluationResult:
    satisfied: bool
    hot_breaches: int
    missed_deadlines: int
    silence_violations: int
    total_clock_overrun: float
    total_value_error: float
    cut_progress_ratio: float
    rm_state_trace: List[RMState] = field(default_factory=list)
    reward_pulses: List[RewardPulse] = field(default_factory=list)
    total_rm_reward: float = 0.0
    diagnostics: List[str] = field(default_factory=list)


class RewardMachine:
    """
    Explicit Reward Machine compiled from a Universal LSC.
    States: IDLE_WAIT_PRE → PRE_MATCHING → MAIN_ACTIVE → COMPLETED | BREACH
    (SILENCE_CHECK is transient on ticks with output while obligations idle.)
    """

    R_PROG = 1.0
    R_GOAL = 5.0
    R_BREACH = -10000.0  # Ω catastrophic

    def __init__(self) -> None:
        self.state = RMState.IDLE_WAIT_PRE
        self.trace: List[RMState] = [RMState.IDLE_WAIT_PRE]
        self.pulses: List[RewardPulse] = []

    def _goto(self, new_state: RMState) -> None:
        self.state = new_state
        self.trace.append(new_state)

    def on_pre_trigger(self, tick: int) -> None:
        if self.state in (RMState.IDLE_WAIT_PRE, RMState.COMPLETED, RMState.SILENCE_CHECK):
            self._goto(RMState.PRE_MATCHING)
            self._goto(RMState.MAIN_ACTIVE)
            self.pulses.append(RewardPulse(tick, self.R_PROG, "pre_chart_matched", self.state))
        elif self.state == RMState.MAIN_ACTIVE:
            self.pulses.append(RewardPulse(tick, self.R_PROG, "additional_obligation", self.state))

    def on_proper_fulfillment(self, tick: int, remaining_open: int) -> None:
        self.pulses.append(RewardPulse(tick, self.R_PROG, "main_chart_progress", self.state))
        if remaining_open == 0:
            self.pulses.append(RewardPulse(tick, self.R_GOAL, "main_chart_complete", RMState.COMPLETED))
            self._goto(RMState.COMPLETED)

    def on_breach(self, tick: int, reason: str) -> None:
        self.pulses.append(RewardPulse(tick, self.R_BREACH, reason, RMState.BREACH))
        self._goto(RMState.BREACH)

    def on_silence_ok(self, tick: int) -> None:
        if self.state == RMState.COMPLETED:
            return
        if self.state == RMState.MAIN_ACTIVE:
            return
        self._goto(RMState.SILENCE_CHECK)
        self._goto(RMState.IDLE_WAIT_PRE if self.state != RMState.BREACH else RMState.BREACH)

    @property
    def total_reward(self) -> float:
        return sum(p.amount for p in self.pulses)


class UniversalLSC:
    """
    Assertional IOR encoding compiled to TBA / Reward Machine:
      - Cold Pre-Chart: pre_trigger_fn
      - Hot Main-Chart: value envelope + [min_delay, max_delay] deadline
      - Silence Obligation: unsolicited outputs are hot breaches when enforce_silence
    Cut-progress advances ONLY on proper fulfillment (on-time AND in-tolerance).
    """

    def __init__(
        self,
        name: str,
        target_need_id: str,
        horizon: int,
        pre_trigger_fn: Callable[[int, Dict[str, Message]], Optional[Message]],
        value_distance_fn: Callable[[Message, Message], float],
        tolerance: float = 1e-3,
        min_delay: int = 0,
        max_delay: int = 2,
        enforce_silence: bool = True,
    ):
        self.name = name
        self.target_need_id = target_need_id
        self.horizon = horizon
        self.pre_trigger_fn = pre_trigger_fn
        self.value_distance_fn = value_distance_fn
        self.tolerance = tolerance
        self.min_delay = min_delay
        self.max_delay = max_delay
        self.enforce_silence = enforce_silence

    def evaluate_trace(
        self,
        scenario_inputs: Dict[int, Dict[str, Message]],
        consumer_outputs: Dict[int, Message],
    ) -> TBAEvaluationResult:
        windows: List[ObligationWindow] = []
        hot_breaches = 0
        missed_deadlines = 0
        silence_violations = 0
        total_clock_overrun = 0.0
        total_value_error = 0.0
        diagnostics: List[str] = []
        rm = RewardMachine()

        for tick in range(self.horizon):
            env_at_tick = scenario_inputs.get(tick, {})
            trig_msg = self.pre_trigger_fn(tick, env_at_tick)
            if trig_msg is not None:
                windows.append(
                    ObligationWindow(
                        trigger_tick=tick,
                        trigger_msg=trig_msg,
                        min_tick=tick + self.min_delay,
                        max_tick=tick + self.max_delay,
                    )
                )
                rm.on_pre_trigger(tick)

            # Expire windows that have passed max_tick without proper fulfillment
            for win in windows:
                if not win.fulfilled and not win.breached and tick > win.max_tick:
                    # Still allow late delivery this tick if output arrives; mark provisional miss
                    # Actual miss is finalized if no output matches below.
                    pass

            out_msg = consumer_outputs.get(tick)
            if out_msg is not None:
                open_windows = [
                    w for w in windows
                    if not w.fulfilled and not w.breached and tick >= w.min_tick
                ]
                if not open_windows:
                    if self.enforce_silence:
                        silence_violations += 1
                        hot_breaches += 1
                        diagnostics.append(
                            f"Tick {tick}: Hot Silence Breach (unsolicited output)."
                        )
                        rm.on_breach(tick, "silence_breach")
                else:
                    win = open_windows[0]
                    val_err = self.value_distance_fn(win.trigger_msg, out_msg)
                    excess_err = max(0.0, val_err - self.tolerance)
                    total_value_error += excess_err

                    late = tick > win.max_tick
                    value_bad = excess_err > 0.0

                    if late:
                        overrun = float(tick - win.max_tick)
                        total_clock_overrun += overrun
                        missed_deadlines += 1
                        hot_breaches += 1
                        diagnostics.append(
                            f"Tick {tick}: Deadline overrun by {overrun:.0f} "
                            f"(trigger at {win.trigger_tick})."
                        )
                        rm.on_breach(tick, "deadline_overrun")

                    if value_bad:
                        hot_breaches += 1
                        diagnostics.append(
                            f"Tick {tick}: Value envelope breach "
                            f"(error={val_err:.4f} > tol={self.tolerance})."
                        )
                        rm.on_breach(tick, "value_breach")

                    win.fulfilled = True
                    win.fulfilled_properly = (not late) and (not value_bad)
                    if win.fulfilled_properly:
                        rem = sum(
                            1
                            for w in windows
                            if w is not win
                            and not w.fulfilled_properly
                            and not w.breached
                            and not w.fulfilled
                        )
                        rm.on_proper_fulfillment(tick, rem)
                    else:
                        win.breached = True
            else:
                rm.on_silence_ok(tick)

        # Unfulfilled at horizon
        for win in windows:
            if not win.fulfilled and not win.breached:
                missed_deadlines += 1
                hot_breaches += 1
                overrun = float(max(1, self.horizon - win.max_tick))
                total_clock_overrun += overrun
                win.breached = True
                diagnostics.append(
                    f"End of Horizon: Unfulfilled obligation from trigger at tick {win.trigger_tick}."
                )
                rm.on_breach(self.horizon - 1, "unfulfilled_at_horizon")

        total_triggers = len(windows)
        proper = sum(1 for w in windows if w.fulfilled_properly)
        if total_triggers == 0:
            cut_progress = 1.0 if hot_breaches == 0 else 0.0
        else:
            cut_progress = proper / float(total_triggers)

        satisfied = (hot_breaches == 0) and (total_triggers > 0 or not self.enforce_silence)
        if satisfied and rm.state != RMState.BREACH:
            if rm.state != RMState.COMPLETED:
                rm._goto(RMState.COMPLETED)

        return TBAEvaluationResult(
            satisfied=satisfied,
            hot_breaches=hot_breaches,
            missed_deadlines=missed_deadlines,
            silence_violations=silence_violations,
            total_clock_overrun=round(total_clock_overrun, 4),
            total_value_error=round(total_value_error, 4),
            cut_progress_ratio=round(cut_progress, 4),
            rm_state_trace=list(rm.trace),
            reward_pulses=list(rm.pulses),
            total_rm_reward=round(rm.total_reward, 4),
            diagnostics=diagnostics,
        )
