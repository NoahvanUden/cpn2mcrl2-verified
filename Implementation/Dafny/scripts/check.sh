#!/usr/bin/env bash
#
# The validation harness of Implementation/docs/Target.md 4, run on every fixture.
#
# Four checks per fixture, in both encodings. Three are tiers T0 and T4 of
# Implementation/docs/Plan.md 2 -- the ones that are tested rather than proved:
#
#   1. mcrl22lps accepts the emitted text.                                        (T0)
#   2. The linearized process has |T| + 1 summands and |P| parameters.
#      Target.md 2: "If not, what was emitted was not an LPE."
#   3. lps2lts gives an LTS strongly bisimilar to the recorded golden one.        (T4)
#   4. The two encodings are strongly bisimilar to each other.                    (T5, tested)
#
# The fourth is the differential test Languages.md 5 wants out of building the translator
# more than once: if a byte of Implementation/Lean is on the machine, every emitted
# specification is also diffed against the one the Lean translator emits from the same
# fixture. The two are expected to be identical, not merely bisimilar -- both print the
# same terms through the same encoding, and both order places, transitions and variables
# by sorted key.
#
# The golden LTSs are checked with ltscompare -ebisim rather than compared as text, because
# state numbering is not part of what is being asserted.
#
# Rejection is read off the output file rather than an exit code: Dafny 4.11 does not allow
# `Main` a non-ghost out parameter, so src/Main.dfy has no exit status to set and simply
# writes nothing when it refuses a net.
#
# Usage:  scripts/check.sh            from Implementation/Dafny
#         MCRL2_BIN=/path scripts/check.sh
#         LEAN_BIN=/path/to/cpn2mcrl2 scripts/check.sh
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

BIN="./cpn2mcrl2"
[ -x "$BIN" ] || BIN="./cpn2mcrl2.exe"
if [ ! -x "$BIN" ]; then
  echo "translator not built; run 'dafny build --target:cs --output cpn2mcrl2 src/*.dfy' first" >&2
  exit 2
fi

# The Lean translator, for the differential test. Optional.
LEAN_BIN="${LEAN_BIN:-}"
if [ -z "$LEAN_BIN" ]; then
  for cand in "../Lean/.lake/build/bin/cpn2mcrl2" "../Lean/.lake/build/bin/cpn2mcrl2.exe"; do
    if [ -x "$cand" ]; then LEAN_BIN="$cand"; break; fi
  done
fi

mkdir -p out

# ltscompare EXITS ZERO whether or not the two LTSs are equal: the verdict is the last
# line of its stdout, "true" or "false". Written as `if ltscompare ...`, as this script
# was until Tests/ found it, the check passes unconditionally and reports every pair as
# bisimilar. See Tests/docs/Findings.md 1.
bisim() {
  [ "$("$MCRL2_BIN/ltscompare" -ebisim "$1" "$2" 2>/dev/null | tail -1)" = "true" ]
}

fail=0

report() { printf '  %-16s %s\n' "$1" "$2"; }

# translate <fixture> <target> [--list]; returns non-zero when the net was refused.
translate() {
  rm -f "$2"
  "$BIN" ${3:-} "$1" "$2" >"$2.msg" 2>&1
  [ -f "$2" ]
}

while read -r name summands params; do
  case "$name" in ''|\#*) continue;; esac
  echo "== $name =="

  for mode in bag list; do
    if [ "$mode" = bag ]; then flag=""; tag=""; else flag="--list"; tag=".list"; fi

    if ! translate "fixtures/$name.cpn.json" "out/$name$tag.mcrl2" "$flag"; then
      report "translate $mode" "REFUSED a valid fixture"
      sed 's/^/    /' "out/$name$tag.mcrl2.msg"; fail=1; continue
    fi
    report "translate $mode" "ok"

    if ! "$MCRL2_BIN/mcrl22lps" -q "out/$name$tag.mcrl2" "out/$name$tag.lps" \
        2>"out/$name$tag.err"; then
      report "mcrl22lps $mode" "REJECTED the emitted text (T0)"
      sed 's/^/    /' "out/$name$tag.err"; fail=1; continue
    fi
    report "mcrl22lps $mode" "accepted (T0)"

    info="$("$MCRL2_BIN/lpsinfo" "out/$name$tag.lps" 2>/dev/null)"
    got_s="$(printf '%s\n' "$info" | sed -n 's/.*Number of summands *: *\([0-9]*\).*/\1/p')"
    got_p="$(printf '%s\n' "$info" | sed -n 's/.*Number of process parameters *: *\([0-9]*\).*/\1/p')"
    if [ "$got_s" = "$summands" ] && [ "$got_p" = "$params" ]; then
      report "shape $mode" "$got_s summands, $got_p parameters"
    else
      report "shape $mode" \
        "expected $summands summands and $params parameters, got $got_s and $got_p"
      fail=1
    fi

    if ! "$MCRL2_BIN/lps2lts" -q "out/$name$tag.lps" "out/$name$tag.aut" \
        2>"out/$name$tag.err"; then
      report "lps2lts $mode" "FAILED"; sed 's/^/    /' "out/$name$tag.err"; fail=1; continue
    fi

    if [ -n "$LEAN_BIN" ]; then
      "$LEAN_BIN" $flag "fixtures/$name.cpn.json" "out/$name$tag.lean.mcrl2" 2>/dev/null
      if [ -f "out/$name$tag.lean.mcrl2" ] && \
         diff -q <(tr -d '\r' < "out/$name$tag.lean.mcrl2") \
                 <(tr -d '\r' < "out/$name$tag.mcrl2") >/dev/null; then
        report "vs Lean $mode" "identical text"
      else
        report "vs Lean $mode" "DIFFERS from the Lean translator's output"
        diff <(tr -d '\r' < "out/$name$tag.lean.mcrl2") \
             <(tr -d '\r' < "out/$name$tag.mcrl2") | sed 's/^/    /'
        fail=1
      fi
    fi
  done

  if [ -f "fixtures/$name.aut" ]; then
    if bisim "fixtures/$name.aut" "out/$name.aut"; then
      report "lts" "bisimilar to the golden LTS"
    else
      report "lts" "DIFFERS from fixtures/$name.aut"
      diff "fixtures/$name.aut" "out/$name.aut" | sed 's/^/    /'
      fail=1
    fi
  else
    report "lts" "no golden LTS recorded; out/$name.aut written"
  fi

  # The refinement of Plan.md 5, proved in src/ListEncoding.dfy, run against the toolset.
  states_of() { head -1 "$1" | tr -d ' \r' | sed 's/.*,\([0-9]*\))$/\1/'; }
  bagstates="$(states_of "out/$name.aut")"
  liststates="$(states_of "out/$name.list.aut")"
  if bisim "out/$name.aut" "out/$name.list.aut"; then
    if [ "$bagstates" = "$liststates" ]; then
      report "refinement" "bisimilar to the bag encoding ($bagstates states each)"
    else
      report "refinement" \
        "bisimilar to the bag encoding, $bagstates bag states against $liststates list states"
    fi
  else
    report "refinement" "NOT bisimilar to the bag encoding"
    fail=1
  fi
# The corpus list is filtered through `tr -d '\r'`: on a Windows checkout the file
# arrives with CRLF, the last field of every row then ends in a carriage return, and
# the shape comparison can never match -- it prints "expected 4 and 3, got 4 and 3"
# and fails. See Tests/docs/Findings.md 2.
done < <(tr -d '\r' < fixtures/expected.tsv)

for bad in fixtures/rejected/*.cpn.json; do
  [ -e "$bad" ] || continue
  base="$(basename "$bad" .cpn.json)"
  echo "== $base (must be rejected) =="
  if translate "$bad" "out/rejected.$base.mcrl2"; then
    report "validate" "ACCEPTED a net that is not a CPN"; fail=1
  else
    report "validate" "rejected"
    sed 's/^/    /' "out/rejected.$base.mcrl2.msg"
  fi
done

echo
if [ -z "$LEAN_BIN" ]; then
  echo "note: the Lean translator was not found, so the differential test was skipped."
  echo "      build Implementation/Lean, or set LEAN_BIN, to run it."
fi
if [ "$fail" -eq 0 ]; then echo "all fixtures green"; else echo "FAILURES"; fi
exit "$fail"
