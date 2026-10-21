.PHONY: build check check-no-sorry solver solver-artifacts techdoc-list techdoc-all

PYTHON ?= /venvs/wymore/bin/python
export PYTHONPATH := scripts$(if $(PYTHONPATH),:$(PYTHONPATH),)

TECHDOC_OUT := build/techdoc

build:
	lake build Mbse

check: build check-no-sorry

check-no-sorry:
	./scripts/check_no_sorry.sh

report:
	lake exe mbse

# Decide conformance for every instance with the SAT solver and cross-check each
# verdict against its machine-checked counterpart.  Non-zero exit on disagreement.
solver:
	$(PYTHON) scripts/phi_dyn_solver.py

# Regenerate everything the paper and the repository consume from the solver:
# the results table, the DIMACS instances, and the Lean file that re-checks a
# solver-found conformance map with `decide`.
solver-artifacts:
	$(PYTHON) scripts/phi_dyn_solver.py \
	  --tex papers/ltl_paper/generated/solver-results.tex \
	  --dimacs-dir build/cnf \
	  --emit-lean Mbse/SolverWitness.lean
	lake build Mbse.SolverWitness

# ISR / technology documentation (JSON export + TikZ figure PDFs + report PDF).
# Registered ids come from Mbse/DocExportRegistry.lean — no per-design Makefile lines.
# Usage: make techdoc-toy   /   make techdoc-rle   /   make techdoc-<id>
techdoc-list:
	lake exe mbse-doc-export list

techdoc-%:
	@mkdir -p $(TECHDOC_OUT)/$*
	lake exe mbse-doc-export export $* --out $(TECHDOC_OUT)/$*/design.json
	$(PYTHON) -m techdoc --in $(TECHDOC_OUT)/$*/design.json --out-dir $(TECHDOC_OUT)/$*

techdoc-all:
	@for id in $$(lake exe mbse-doc-export list); do \
	  $(MAKE) techdoc-$$id; \
	done
