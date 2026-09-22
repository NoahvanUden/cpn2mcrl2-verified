#!/usr/bin/env bash
#
# Machine-checks, for one Lake package, the two claims the READMEs make about it: that nothing
# in it is left unproved, and that what is proved rests on Lean's standard axioms alone.
#
#   check-lean-proved.sh <package directory> [<assertion file, relative to it>]
#
# Both matter because `sorry` is a *warning* in Lean 4. `lake build` exits 0 with one in the
# tree (verified: 38 jobs, "Build completed successfully", one warning), so until this ran, the
# sentence in Proof/README.md was checked by nobody.
#
# Phase 1 greps the build log for `declaration uses`. Lake replays the diagnostics of an
# up-to-date module from its trace rather than staying silent, so this is not defeated by the
# warm .lake that `clean: false` keeps on the runner between runs -- verified by rebuilding
# four times over an unchanged tree and getting the warning every time. It covers declarations
# the second phase never names, including ones reached only through a tactic or a macro.
#
# Phase 2 is `#print axioms` on the top-level theorems (see Proof/scripts/Axioms.lean). It
# covers what phase 1 cannot: a declaration may depend on a subset of Lean's three standard
# axioms and nothing else. An unproved one drags in `sorryAx`, `native_decide` drags in
# `Lean.ofReduceBool`, and an `axiom` of this repository's own is simply not on the list.
set -euo pipefail

ALLOWED="Classical.choice Quot.sound propext"

pkg=${1:?usage: check-lean-proved.sh <package directory> [assertion file]}
file=${2:-scripts/Axioms.lean}

status=0

echo "== $pkg: build log =="
log=$(cd "$pkg" && lake build)
echo "$log"
if echo "$log" | grep -n 'declaration uses'; then
  echo "check-lean-proved: FAIL $pkg has an unproved declaration" >&2
  status=1
fi

expected=$(grep -c '^#print axioms' "$pkg/$file")
if [ "$expected" -eq 0 ]; then
  echo "check-lean-proved: FAIL $pkg/$file asserts nothing" >&2
  exit 1
fi

echo "== $pkg: axioms of $expected declarations =="
# Elaboration errors -- a renamed or deleted theorem, a broken import -- exit non-zero here,
# so coverage cannot quietly shrink to nothing.
output=$(cd "$pkg" && lake env lean "$file")
echo "$output"

seen=0
while IFS= read -r line; do
  [ -n "$line" ] || continue
  case $line in
    "'"*"' does not depend on any axioms")
      seen=$((seen + 1))
      ;;
    "'"*"' depends on axioms: ["*"]")
      seen=$((seen + 1))
      decl=${line#\'}; decl=${decl%%\'*}
      axioms=${line#*: [}; axioms=${axioms%]}
      IFS=',' read -ra parts <<< "$axioms"
      for axiom in "${parts[@]}"; do
        axiom=$(echo "$axiom" | tr -d '[:space:]')
        case " $ALLOWED " in
          *" $axiom "*) ;;
          *)
            echo "check-lean-proved: FAIL $decl depends on '$axiom', not one of: $ALLOWED" >&2
            status=1
            ;;
        esac
      done
      ;;
    *)
      echo "check-lean-proved: FAIL unexpected output: $line" >&2
      status=1
      ;;
  esac
done <<< "$output"

if [ "$seen" -ne "$expected" ]; then
  echo "check-lean-proved: FAIL reported on $seen declarations, expected $expected" >&2
  status=1
fi

if [ "$status" -eq 0 ]; then
  echo "check-lean-proved: OK -- $pkg builds clean, $seen declarations on standard axioms only"
fi
exit $status
