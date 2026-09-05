#!/usr/bin/env bash
#
# The validation harness of Implementation/docs/Target.md 4, run on every fixture.
#
# Three checks per fixture, which are tiers T0 and T4 of Implementation/docs/Plan.md 2 --
# the ones that are tested rather than proved:
#
#   1. mcrl22lps accepts the emitted text.                                        (T0)
#   2. The linearized process has |T| + 1 summands and |P| parameters.
#      Target.md 2: "If not, what was emitted was not an LPE."
#   3. lps2lts gives an LTS strongly bisimilar to the recorded golden one.        (T4)
#
# The golden LTSs are checked with ltscompare -ebisim rather than compared as text, because
# state numbering is not part of what is being asserted.
#
# Usage:  scripts/check.sh            from Implementation/Lean
#         MCRL2_BIN=/path scripts/check.sh
set -u

here="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$here" || exit 1

MCRL2_BIN="${MCRL2_BIN:-}"
if [ -z "$MCRL2_BIN" ]; then
  for cand in "/c/Program Files/mCRL2/bin" "/usr/local/bin" "/opt/mcrl2/bin"; do
    if [ -x "$cand/mcrl22lps" ] || [ -x "$cand/mcrl22lps.exe" ]; then MCRL2_BIN="$cand"; break; fi
  done
fi
if [ -z "$MCRL2_BIN" ]; then
  if command -v mcrl22lps >/dev/null 2>&1; then MCRL2_BIN="$(dirname "$(command -v mcrl22lps)")"; fi
fi
if [ -z "$MCRL2_BIN" ]; then
  echo "mcrl22lps not found. Set MCRL2_BIN to the mCRL2 bin directory." >&2
  exit 2
fi

BIN=".lake/build/bin/cpn2mcrl2"
[ -x "$BIN" ] || BIN=".lake/build/bin/cpn2mcrl2.exe"
if [ ! -x "$BIN" ]; then
  echo "translator not built; run 'lake build' first" >&2
  exit 2
fi

mkdir -p out
fail=0

report() { printf '  %-14s %s\n' "$1" "$2"; }

while read -r name summands params; do
  case "$name" in ''|\#*) continue;; esac
  echo "== $name =="

  if ! "$BIN" "fixtures/$name.cpn.json" "out/$name.mcrl2"; then
    report "translate" "FAILED"; fail=1; continue
  fi
  report "translate" "ok"

  if ! "$MCRL2_BIN/mcrl22lps" -q "out/$name.mcrl2" "out/$name.lps" 2>"out/$name.err"; then
    report "mcrl22lps" "REJECTED the emitted text (T0)"; sed 's/^/    /' "out/$name.err"
    fail=1; continue
  fi
  report "mcrl22lps" "accepted (T0)"

  info="$("$MCRL2_BIN/lpsinfo" "out/$name.lps" 2>/dev/null)"
  got_s="$(printf '%s\n' "$info" | sed -n 's/.*Number of summands *: *\([0-9]*\).*/\1/p')"
  got_p="$(printf '%s\n' "$info" | sed -n 's/.*Number of process parameters *: *\([0-9]*\).*/\1/p')"
  if [ "$got_s" = "$summands" ] && [ "$got_p" = "$params" ]; then
    report "shape" "$got_s summands, $got_p parameters"
  else
    report "shape" "expected $summands summands and $params parameters, got $got_s and $got_p"
    fail=1
  fi

  if ! "$MCRL2_BIN/lps2lts" -q "out/$name.lps" "out/$name.aut" 2>"out/$name.err"; then
    report "lps2lts" "FAILED"; sed 's/^/    /' "out/$name.err"; fail=1; continue
  fi
  if [ -f "fixtures/$name.aut" ]; then
    if "$MCRL2_BIN/ltscompare" -ebisim "fixtures/$name.aut" "out/$name.aut" >/dev/null 2>&1; then
      report "lts" "bisimilar to the golden LTS"
    else
      report "lts" "DIFFERS from fixtures/$name.aut"
      diff "fixtures/$name.aut" "out/$name.aut" | sed 's/^/    /'
      fail=1
    fi
  else
    report "lts" "no golden LTS recorded; out/$name.aut written"
  fi
done < fixtures/expected.tsv

for bad in fixtures/rejected/*.cpn.json; do
  [ -e "$bad" ] || continue
  echo "== $(basename "$bad" .cpn.json) (must be rejected) =="
  if msg="$("$BIN" "$bad" 2>&1 >/dev/null)"; then
    report "validate" "ACCEPTED a net that is not a CPN"; fail=1
  else
    report "validate" "rejected"
    printf '%s\n' "$msg" | sed 's/^/    /'
  fi
done

echo
if [ "$fail" -eq 0 ]; then echo "all fixtures green"; else echo "FAILURES"; fi
exit "$fail"
