# The Integration Game — Python Reference Implementation

Proof-of-concept simulator for the Wymorian **Integration Game**: place mediation
components, wire Offer→Need routes, and evaluate plays against a uLSC
compiled into a Timed Büchi / Reward Machine monitor.

Authoritative ontology: [`src/integration_game/ONTOLOGY.md`](src/integration_game/ONTOLOGY.md).

## Setup

```bash
cd papers/integration-game
pip install -e ".[dev]"
# Optional Gymnasium adapter for SB3 / CleanRL / custom Torch loops:
pip install -e ".[rl]"
```

Or without install:

```bash
PYTHONPATH=src /venvs/wymore/bin/python -m integration_game.examples.run_progressive_examples
/venvs/wymore/bin/pytest
```

## What it demonstrates

- **Tier 1** — color / representation / provenance structural compatibility  
- **Tier 2** — push/pull kinematics (Cache decelerates, Pump accelerates)  
- **Tier 3** — uLSC → Reward Machine (deadlines, value envelopes, silence)  
- Progressive move sequences for **Examples 1–15** where fitness rises toward a three-tier win, including intentional Tier-1+2-pass / Tier-3-fail traps
- Offline synthesis MDP (`integration_game.rl`) with random/greedy/beam/REINFORCE baselines
- Gymnasium wrapper with stable `Discrete(A_max)` + `action_mask` for MaskablePPO

## Gymnasium / external RL frameworks

```python
from integration_game.rl import make_offline_gym_env

env = make_offline_gym_env("ex02", max_actions=64)
obs, info = env.reset(seed=0)
# obs["obs"] float32[12], obs["action_mask"] bool[A_max]
action = int(obs["action_mask"].nonzero()[0][0])  # any legal slot
obs, reward, terminated, truncated, info = env.step(action)
```

Core env helpers: `clone()` / `get_state()` / `set_state()`, `structural_score()` (Tier-1/2 without TBA sim), picklable `SynthTask` via rebuild registry.

## Game API (offline synthesis)

```python
from integration_game import Play, AddOperator, AddRoute, RecolorBlock, Color, TransferMode

play = Play.new("demo")
play.apply(AddOperator(RecolorBlock("R", Color("A","u","f"), Color("B","u","f"))))
# play.apply(AddRoute("Src.out", "R.in", strict=True))
```

## Layout

```
src/integration_game/
  ONTOLOGY.md          # shared conceptual contract
  primitives.py        # Field, Color, Dynamics, Message aggregations
  interfaces.py        # Need XOR Offer, Routes + Carrier
  components.py        # Technology catalog T
  board.py             # RSY(Board) simulation
  ulsc.py              # uLSC → TBA / Reward Machine
  scoring.py           # J / S / ranking
  game.py              # Play / Move MDP API
  rl/                  # Offline/online MDP + Gymnasium adapter
  examples/catalog.py  # Examples 1–15
tests/
```
