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
# more than once. Every emitted specification is also diffed against the ones the Lean and
# the Dafny translators emit from the same fixture, whichever of them is on the machine.
# All three are expected to be identical, not merely bisimilar.
#
# Running it on Windows
# ---------------------
# The OCaml translator is built inside WSL and the mCRL2 toolset is a Windows install, so
# neither can see the other's binaries directly. Run this script from Git Bash: it calls the
# Windows mcrl2 tools natively and reaches the translator through `wsl`. On Linux or macOS
# nothing special happens and the translator is called directly.
#
# Usage:  scripts/check.sh            from Implementation/OCaml
#         MCRL2_BIN=/path scripts/check.sh
#         LEAN_BIN=/path DAFNY_BIN=/path scripts/check.sh
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

# How to run the translator. A native ELF or Mach-O binary is called directly; on Windows the
# build lives inside WSL, so it is reached through `wsl`.
BIN="./_build/default/bin/main.exe"
if [ ! -f "$BIN" ]; then
  echo "translator not built; run 'dune build' first" >&2
  exit 2
fi
if ./"$BIN" --help >/dev/null 2>&1 || [ -x "$BIN" ] && "$BIN" >/dev/null 2>&1; then
  RUN=("$BIN")
elif command -v wsl >/dev/null 2>&1; then
  RUN=(wsl -d Ubuntu -- "$BIN")
else
  RUN=("$BIN")
fi

# The other two translators, for the differential test. Both optional.
LEAN_BIN="${LEAN_BIN:-}"
if [ -z "$LEAN_BIN" ]; then
  for cand in "../Lean/.lake/build/bin/cpn2mcrl2" "../Lean/.lake/build/bin/cpn2mcrl2.exe"; do
    if [ -x "$cand" ]; then LEAN_BIN="$cand"; break; fi
  done
fi
DAFNY_BIN="${DAFNY_BIN:-}"
if [ -z "$DAFNY_BIN" ]; then
  for cand in "../Dafny/cpn2mcrl2" "../Dafny/cpn2mcrl2.exe"; do
    if [ -x "$cand" ]; then DAFNY_BIN="$cand"; break; fi
  done
fi

mkdir -p out
fail=0

report() { printf '  %-16s %s\n' "$1" "$2"; }

# translate <fixture> <target> [--list]; returns non-zero when the net was refused.
#
# stdin is closed on every external command below. `wsl` reads its own stdin, and without
# this it swallows the rest of fixtures/expected.tsv and the loop runs once.
translate() {
  rm -f "$2"
  "${RUN[@]}" ${3:-} "$1" "$2" >"$2.msg" 2>&1 </dev/null
  [ -f "$2" ]
}

# diff_against <label> <other translator> <fixture> <target> <flag>
diff_against() {
  local label="$1" other="$2" fixture="$3" target="$4" flag="$5"
  [ -n "$other" ] || return 0
  local ref="$target.$label"
  rm -f "$ref"
  "$other" $flag "$fixture" "$ref" 2>/dev/null </dev/null
  if [ -f "$ref" ] && diff -q <(tr -d '\r' < "$ref") <(tr -d '\r' < "$target") >/dev/null; then
    report "vs $label" "identical text"
  else
    report "vs $label" "DIFFERS from the $label translator's output"
    diff <(tr -d '\r' < "$ref") <(tr -d '\r' < "$target") | sed 's/^/    /'
    fail=1
  fi
}

# ltscompare EXITS ZERO whether or not the two LTSs are equal: the verdict is the last
# line of its stdout, "true" or "false". Written as `if ltscompare ...`, as this script
# was until Tests/ found it, the check passes unconditionally: it reported every pair as
# bisimilar, including a pair that is not. See Tests/docs/Findings.md 1.
bisim() {
  [ "$("$MCRL2_BIN/ltscompare" -ebisim "$1" "$2" 2>/dev/null </dev/null | tail -1)" = "true" ]
}

# Carriage returns are stripped from both sides of the shape comparison below. On Windows
# git checks expected.tsv out with CRLF, and the Windows build of lpsinfo writes CRLF; the
# two counts used to agree only because both carried a stray CR, so stripping one side
# alone made a number compare unequal to itself.
while read -r name summands params; do
  case "$name" in ''|\#*) continue;; esac
  summands="${summands%$'\r'}"
  params="${params%$'\r'}"
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

    info="$("$MCRL2_BIN/lpsinfo" "out/$name$tag.lps" 2>/dev/null | tr -d $'\r')"
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

    diff_against "lean"  "$LEAN_BIN"  "fixtures/$name.cpn.json" "out/$name$tag.mcrl2" "$flag"
    diff_against "dafny" "$DAFNY_BIN" "fixtures/$name.cpn.json" "out/$name$tag.mcrl2" "$flag"
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

  # The refinement of Plan.md 5, run against the toolset.
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
done < <(tr -d '' < fixtures/expected.tsv)

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
[ -n "$LEAN_BIN" ]  || echo "note: the Lean translator was not found, so that half of the differential test was skipped."
[ -n "$DAFNY_BIN" ] || echo "note: the Dafny translator was not found, so that half of the differential test was skipped."
if [ "$fail" -eq 0 ]; then echo "all fixtures green"; else echo "FAILURES"; fi
exit "$fail"
