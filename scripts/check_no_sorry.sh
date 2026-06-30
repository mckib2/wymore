#!/usr/bin/env bash
# Fail if temporal-logic modules contain sorry, admit, or custom axiom declarations.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
FILES=(
  "$ROOT/Mbse/TemporalLogic.lean"
  "$ROOT/Mbse/FOLTL.lean"
  "$ROOT/Mbse/SystemToFormula.lean"
  "$ROOT/Mbse/SystemToLTL.lean"
)
if rg -n 'sorry|admit|^[[:space:]]*axiom[[:space:]]' "${FILES[@]}"; then
  echo "ERROR: forbidden proof placeholders found in temporal-logic modules" >&2
  exit 1
fi
echo "OK: no sorry/admit/axiom in temporal-logic modules"
