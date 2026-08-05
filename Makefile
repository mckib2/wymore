.PHONY: build check check-no-sorry solver solver-artifacts

PYTHON ?= /venvs/wymore/bin/python

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
