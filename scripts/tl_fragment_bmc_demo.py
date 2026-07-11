#!/venvs/wymore/bin/python
"""Bounded unrolling demo for dynamics-encoding clauses (illustrative only).

Checks finite-horizon consistency queries for:
  * ones-counter transition laws (Wymore 2.128-style)
  * real accumulator δ(s,u)=s+u (case study B)

This is not a proof of the paper bi-implication; it illustrates bounded
property checking mentioned in the methodology/discussion.

Usage:
  /venvs/wymore/bin/python scripts/tl_fragment_bmc_demo.py
"""

from __future__ import annotations

from z3 import Int, Real, Bool, Solver, Implies, Or, Not, sat, unsat


def check_ones_counter(T: int = 5) -> bool:
    count = [Int(f"c_{t}") for t in range(T + 1)]
    bit = [Bool(f"b_{t}") for t in range(T)]

    s = Solver()
    s.add(count[0] == 0)
    for t in range(T):
        s.add(Implies(bit[t], count[t + 1] == count[t] + 1))
        s.add(Implies(Not(bit[t]), count[t + 1] == count[t]))
        s.add(count[t] >= 0)

    s.push()
    s.add(Or(*[count[t + 1] > count[t] + 1 for t in range(T)]))
    result = s.check()
    s.pop()
    print(f"ones-counter BMC T={T}: overshoot -> {result} (expect unsat)")
    return result == unsat


def check_real_accumulator(T: int = 4) -> bool:
    state = [Real(f"s_{t}") for t in range(T + 1)]
    inp = [Real(f"u_{t}") for t in range(T)]

    s = Solver()
    s.add(state[0] == 0)
    for t in range(T):
        s.add(state[t + 1] == state[t] + inp[t])

    # Violation: next state differs from s+u
    s.push()
    s.add(Or(*[state[t + 1] != state[t] + inp[t] for t in range(T)]))
    # Under the transition axioms above this is immediately unsat; instead ask
    # whether |s_T| can exceed sum of absolute inputs when all u>=0 (should be unsat
    # if we also constrain u>=0 and claim s_T > sum u).
    s.pop()

    s2 = Solver()
    s2.add(state[0] == 0)
    for t in range(T):
        s2.add(inp[t] >= 0)
        s2.add(state[t + 1] == state[t] + inp[t])
    total = sum(inp)
    s2.add(state[T] > total)
    result = s2.check()
    print(f"real-accumulator BMC T={T}: s_T > sum(u) with u>=0 -> {result} (expect unsat)")
    return result == unsat


def main() -> int:
    ok_ones = check_ones_counter()
    ok_real = check_real_accumulator()
    if ok_ones and ok_real:
        print("OK: bounded dynamics-encoding constraints behave as expected.")
        return 0
    print("Unexpected sat; inspect encoding.")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
