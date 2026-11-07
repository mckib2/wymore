# The Integration Game — Python Reference Implementation

Proof-of-concept simulator for the Wymorian **Integration Game**: place mediation
components, wire Offer→Need routes, and evaluate plays against a Universal LSC
compiled into a Timed Büchi / Reward Machine monitor.

Authoritative ontology: [`src/integration_game/ONTOLOGY.md`](src/integration_game/ONTOLOGY.md).

## Setup

```bash
cd papers/integration-game
pip install -e ".[dev]"
```

Or without install:

```bash
PYTHONPATH=src python -m integration_game.examples.run_progressive_examples
pytest
```

## What it demonstrates

- **Tier 1** — color / representation / provenance structural compatibility  
- **Tier 2** — push/pull kinematics (Cache decelerates, Pump accelerates)  
- **Tier 3** — uLSC → Reward Machine (deadlines, value envelopes, silence)  
- Progressive move sequences for **Examples 1–12** where fitness rises toward a three-tier win, including intentional Tier-1+2-pass / Tier-3-fail traps

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
  examples/catalog.py  # Examples 1–12
tests/
```
