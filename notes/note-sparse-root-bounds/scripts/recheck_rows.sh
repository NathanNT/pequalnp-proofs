#!/usr/bin/env bash
# Recompile the eighteen Lean files discussed in the note and the three Lean files that accompany it,
# and check the axioms each final theorem rests on.
#
# Run from the root of a clone of open-goat/pequalnp-proofs that contains this note, after the project's own setup
# has fetched the prebuilt Mathlib (tools/pnp.sh setup, or `lake exe cache get` in lean/):
#
#   bash notes/note-sparse-root-bounds/scripts/recheck_rows.sh
#
# For each repository file the line `import PEqualNP.Defs` is deleted where present (the statements use Mathlib
# only), `#print axioms <final theorem>` is appended, and `lake env lean` is run on the copy.
# RealExponentMoments.lean imports the module PEqualNP.Outside.L_gct_234, which is built first.
# The script exits with status 0 only if every file compiles and every axiom list is exactly
#   [propext, Classical.choice, Quot.sound].
# A Lean file runs code while it compiles; run this only on files you trust or in an isolated environment.
set -uo pipefail
ROOT="$(git rev-parse --show-toplevel)"
NOTE="$ROOT/notes/note-sparse-root-bounds"
TMP="$(mktemp -d)"
EXPECTED="[propext, Classical.choice, Quot.sound]"
fail=0
cd "$ROOT/lean"

check() {  # check <label> <file>
  local label="$1" file="$2" out status axioms
  if out="$(lake env lean "$file" 2>&1)"; then status=ok; else status=FAILED; fail=1; fi
  axioms="$(printf '%s' "$out" | tr '\n' ' ' | grep -o "depends on axioms: \[[^]]*\]" | sed 's/depends on axioms: //' | tr -s ' ' | sort -u)"
  if [ "$axioms" != "$EXPECTED" ]; then status="$status, UNEXPECTED AXIOMS"; fail=1; fi
  echo "$label: $status; axioms: ${axioms:-none printed}"
}

for n in 234 241 243 245 247 249 251 253 255 257 259 261 263 265 267 269 271 273; do
  dst="$TMP/Check_$n.lean"
  grep -v '^import PEqualNP.Defs' "PEqualNP/Outside/L_gct_$n.lean" > "$dst"
  printf '\n#print axioms PEqualNP.Outside.L_gct_%s\n' "$n" >> "$dst"
  check "L-gct-$n" "$dst"
done
for f in FourCubes15 FiveCubes19; do
  check "$f" "$NOTE/lean/$f.lean"
done
if lake build PEqualNP.Outside.L_gct_234 >/dev/null 2>&1; then
  check "RealExponentMoments" "$NOTE/lean/RealExponentMoments.lean"
else
  echo "RealExponentMoments: FAILED (could not build PEqualNP.Outside.L_gct_234)"; fail=1
fi
rm -rf "$TMP"
if [ "$fail" -ne 0 ]; then echo "RESULT: at least one check failed"; exit 1; fi
echo "RESULT: all twenty-one files compile and depend only on $EXPECTED"
