# Wymore System Scripts

Python utilities for parsing Wymore system definitions from Lean 4 and generating paper figures.

## Scripts

| Script | Purpose |
|---|---|
| `parser.py` | Parse Appendix3 `wymore_system` finite set literals into a `WymoreSystem` AST |
| `scxml_transformer.py` | Transform a `WymoreSystem` into SCXML |
| `batch_transform.py` | Batch-convert Lean files in a directory to SCXML |
| `traceability.py` | Verify textbook ↔ Lean traceability tags |
| `techdoc/` | ISR package JSON → TikZ figure PDFs + LaTeX report PDF |
| `swarm_diagram_theme.py` | Shared colors/fonts for swarm case-study figures (matches `papers/ltl_paper/main.tex`) |
| `render_swarm_systems.py` | Generate unified swarm verification-architecture TikZ for the paper case study |
| `tl_fragment_bmc_demo.py` | Optional bounded Z3 demo for ones-counter / real-accumulator clauses (illustrative; Lean is primary). Run: `/venvs/wymore/bin/python scripts/tl_fragment_bmc_demo.py` |
| `check_no_sorry.sh` | Mbse proof-quality gate: sorry/admit/axiom scan, forbidden `set_option` bans, lint-clean build |

## Technology / coupling / PoI documenter (`techdoc`)

Mark an `ImplementableSystemDesign` root with `@[techdoc "id"]` (see `Mbse/TechdocAttr.lean`).
`lake exe mbse-doc-export` derives `IsrPackageDoc` JSON by walking elaborated Lean `Expr`
values (`Mbse/TechdocDerive.lean`) — technology members, CSCR wires, boundary ports, IOR.
Python (`scripts/techdoc`) renders standalone TikZ figure PDFs and a report PDF.

### Requirements

- Lean package build (`lake build mbse-doc-export`; exe needs `supportInterpreter = true`)
- Python 3.x (stdlib only)
- `pdflatex` with TikZ / `standalone` / `xcolor` / `booktabs` / `longtable`

### Registered ids

```bash
make techdoc-list
# or: lake exe mbse-doc-export list
```

Currently: `toy` (`@[techdoc "toy"]` on `ToyCascade.toy_in_isr`),
`rle` (`@[techdoc "rle"]` on `AssertionalCotyledonBridge.rle_in_isr`).

### Build one report

```bash
make techdoc-toy          # any registered id: make techdoc-<id>
make techdoc-rle
```

Outputs under `build/techdoc/<id>/`:

- `design.json` — derived Lean export
- `figures/{technology,coupling,poi,lsc}.pdf` — compiled TikZ figures
- `report.pdf` — narrative document including those figures

### Manual / golden JSON (no Lean rebuild)

Golden snapshots live under `examples/techdoc/<id>/design.json`. Render only:

```bash
PYTHONPATH=scripts python3 -m techdoc \
  --in examples/techdoc/toy/design.json \
  --out-dir build/techdoc/toy
```

### Adding a new design

1. Formal Lean ISR package (`Technology`, `SystemCouplingRecipe`, `ImplementableSystemDesign`)
2. `@[techdoc "id"]` on the ISR root (optional docstring → title/summary)
3. `make techdoc-<id>` — no Makefile edit, no parallel `IsrPackageDoc`

## Mbse quality gate

From repo root:

```bash
make check-no-sorry   # or ./scripts/check_no_sorry.sh
make check            # build + quality gate
```

The script scans all `Mbse/**/*.lean` files (not a fixed list), forbids blanket
`set_option linter.* false` for unused section vars, unused simp args, and
unnecessary seq focus (prefer structural fixes), and fails on any
`warning: Mbse/` line from `lake build Mbse`. Add path substrings to
`WARNING_ALLOWLIST` in `scripts/check_no_sorry.sh` only when a warning is
intentionally accepted.

## Swarm case-study figure

Generates a TikZ fragment under `papers/ltl_paper/build/` (included via `\input` in `main.tex`):

- `swarm_verification.tex` — dual verification paths ($\Phi$ assertional and $Z_{\text{spec}}+h$ constructive) on $Z_{\text{impl}}$

Generated files live in the LaTeX `build/` directory alongside the compiled PDF and are rebuilt before each paper build.

### Requirements

- Python 3.x (stdlib only)
- LaTeX with TikZ (`positioning` library — already loaded in `main.tex`)

No Graphviz or external image tools required.

### From repo root

```bash
python3 scripts/render_swarm_systems.py \
  --case-study Mbse/SwarmCaseStudy.lean \
  --examples Mbse/SwarmExamples.lean \
  --out-dir papers/ltl_paper/build \
  --agents 3
```

Use `--agents N` for the schematic agent count shown in the diagram (parametric fleet size remains $N$ in prose).

### From the paper directory (Makefile)

```bash
cd papers/ltl_paper
make figures          # rebuild TikZ when Lean or scripts change
make                  # figures + build/main.pdf
make figures SWARM_AGENTS=5   # override schematic agent count
```

Figures rebuild when any of these change: `Mbse/SwarmCaseStudy.lean`, `Mbse/SwarmExamples.lean`, `scripts/render_swarm_systems.py`, `scripts/swarm_diagram_theme.py`.

Customize colors and TikZ styles in `swarm_diagram_theme.py`.

## Appendix3 SCXML transform

### Batch transform

```bash
python3 scripts/batch_transform.py -i Appendix3 -o output_scxml
```

### Single file

```bash
python3 scripts/scxml_transformer.py Appendix3/Zx1.lean
python3 scripts/scxml_transformer.py Appendix3/Zx1.lean -o Zx1.scxml
```

## Traceability

```bash
python3 scripts/traceability.py
```

Generates `traceability_report.md` at the repo root.
