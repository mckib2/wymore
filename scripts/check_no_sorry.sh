#!/usr/bin/env bash
# Mbse proof-quality gate for CI and local `make check-no-sorry`.
#
# Checks:
#   1. No sorry / admit / axiom in any Mbse/*.lean module
#   2. No blanket linter suppressions (e.g. unusedSectionVars false)
#      Prefer structural fixes (F.sz_finite in clause defs), narrow variable
#      scope, or per-theorem `omit` instead of set_option.
#   3. lint-clean `lake build Mbse` — fail on any `warning: Mbse/` line
#
# Allowlisted exceptions live in ALLOWED_SET_OPTION_* and WARNING_ALLOWLIST below.
# To add a new exception, document why here and in scripts/README.md.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
MBSE="$ROOT/Mbse"
BUILD_LOG="$(mktemp)"
trap 'rm -f "$BUILD_LOG"' EXIT

fail() {
  echo "ERROR: $1" >&2
  exit 1
}

mapfile -t LEAN_FILES < <(find "$MBSE" -name '*.lean' -type f | sort)
if ((${#LEAN_FILES[@]} == 0)); then
  fail "no Mbse/*.lean files found under $MBSE"
fi

# --- 1. sorry / admit / axiom ---
# Lean proof placeholders only (skip `--` / `/-` comment lines to avoid prose false positives).
filter_code_hits() {
  while IFS= read -r line; do
    [[ -z "$line" ]] && continue
    content="${line#*:*:}"
    trimmed="${content#"${content%%[![:space:]]*}"}"
    [[ "$trimmed" == --* ]] && continue
    [[ "$trimmed" == /-/* ]] && continue
    echo "$line"
  done
}

SORRY_PLACEHOLDER_PATTERN='by[[:space:]]+(sorry|admit)\b|^[[:space:]]*(sorry|admit)[[:space:]]*$|:=[[:space:]]+(sorry|admit)\b'
AXIOM_PATTERN='^[[:space:]]*axiom[[:space:]]'

if mapfile -t hits < <(
  { rg -n "$SORRY_PLACEHOLDER_PATTERN" "${LEAN_FILES[@]}" || true
    rg -n "$AXIOM_PATTERN" "${LEAN_FILES[@]}" || true
  } | filter_code_hits
); then
  if ((${#hits[@]} > 0)); then
    printf '%s\n' "${hits[@]}" >&2
    fail "forbidden proof placeholders found in Mbse modules"
  fi
fi
echo "OK: no sorry/admit/axiom in Mbse modules"

# --- 2. forbidden set_option suppressions ---
FORBIDDEN_SET_OPTION_PATTERNS=(
  'set_option[[:space:]]+linter\.unusedSectionVars[[:space:]]+false'
  'set_option[[:space:]]+linter\.unusedSimpArgs[[:space:]]+false'
  'set_option[[:space:]]+linter\.unnecessarySeqFocus[[:space:]]+false'
)

for pattern in "${FORBIDDEN_SET_OPTION_PATTERNS[@]}"; do
  if rg -n "$pattern" "${LEAN_FILES[@]}"; then
    fail "forbidden set_option linter suppression found (use omit / narrow variable scope instead)"
  fi
done

# Allowlisted set_option uses (path substring : reason)
ALLOWED_SET_OPTION_PATHS=(
  'Mbse/WymoreTactics.lean'  # set_option hygiene false — custom tactic/macro hygiene
)

if mapfile -t set_option_hits < <(rg -n 'set_option[[:space:]]' "${LEAN_FILES[@]}" || true); then
  for hit in "${set_option_hits[@]}"; do
    [[ -z "$hit" ]] && continue
    file="${hit%%:*}"
    rel="${file#"$ROOT"/}"
    allowed=false
    for path in "${ALLOWED_SET_OPTION_PATHS[@]}"; do
      if [[ "$rel" == "$path" ]]; then
        allowed=true
        break
      fi
    done
    if ! $allowed; then
      echo "$hit" >&2
      fail "unexpected set_option in $rel (allowlist in scripts/check_no_sorry.sh if intentional)"
    fi
  done
fi
echo "OK: no forbidden set_option suppressions"

# --- 3. lint-clean build ---
echo "Building Mbse (lint gate)..."
if ! (cd "$ROOT" && lake build Mbse >"$BUILD_LOG" 2>&1); then
  cat "$BUILD_LOG" >&2
  fail "lake build Mbse failed"
fi

# Fail on any Lean warning emitted from Mbse modules (extend WARNING_ALLOWLIST to opt out).
WARNING_ALLOWLIST=(
)

filter_warnings() {
  local line
  while IFS= read -r line; do
    [[ -z "$line" ]] && continue
    for allow in "${WARNING_ALLOWLIST[@]}"; do
      if [[ "$line" == *"$allow"* ]]; then
        continue 2
      fi
    done
    echo "$line"
  done
}

if mapfile -t hits < <(rg 'warning: Mbse/' "$BUILD_LOG" | filter_warnings || true); then
  if ((${#hits[@]} > 0)); then
    printf '%s\n' "${hits[@]}" >&2
    fail "Mbse build emitted linter warnings (allowlist in scripts/check_no_sorry.sh if intentional)"
  fi
fi

echo "OK: Mbse build is lint-clean"
echo "All Mbse quality checks passed."
