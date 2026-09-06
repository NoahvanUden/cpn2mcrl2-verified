#!/usr/bin/env bash
#
# The harness of Tests/docs/Plan.md 6. Four legs, over the corpus of Corpus.md:
#
#   A  the three translators emit byte-identical text                      (existing)
#   B  the emitted LTS agrees with an oracle written outside this project  (new)
#   B2 and on the bag encoding, marking for marking, which is sharper      (new)
#   C  the bag and list encodings are bisimilar                            (existing)
#   D  every net in corpus/rejected/ is refused, by name                   (new)
#
# Plus the two checks that need no oracle: the linearized process has |T| + 1 summands
# and |P| parameters, and the hand-computed state and edge counts of expected.tsv --
# a person's arithmetic as a third opinion, which is why tier 1 is hand-computable.
#
# Usage:  bash Tests/scripts/check.sh [net ...]
#         MCRL2_BIN=/path PYTHON=/path bash Tests/scripts/check.sh
set -u

here="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
root="$(cd "$here/.." && pwd)"
out="$here/out"
mkdir -p "$out"

# ------------------------------------------------------------------ toolchains

MCRL2_BIN="${MCRL2_BIN:-}"
if [ -z "$MCRL2_BIN" ]; then
  for cand in "/c/Program Files/mCRL2/bin" "/usr/local/bin" "/opt/mcrl2/bin"; do
    if [ -x "$cand/mcrl22lps" ] || [ -x "$cand/mcrl22lps.exe" ]; then MCRL2_BIN="$cand"; break; fi
  done
fi
if [ -z "$MCRL2_BIN" ] && command -v mcrl22lps >/dev/null 2>&1; then
  MCRL2_BIN="$(dirname "$(command -v mcrl22lps)")"
fi
if [ -z "$MCRL2_BIN" ]; then
  echo "mcrl22lps not found. Set MCRL2_BIN to the mCRL2 bin directory." >&2
  exit 2
fi

# The oracle runs in the virtual environment of Tests/.venv, so that nothing outside
# this directory depends on it.
VENV="$here/.venv/Scripts/python.exe"
[ -x "$VENV" ] || VENV="$here/.venv/bin/python"
ORACLE_PY="${PYTHON:-$VENV}"
[ -x "$ORACLE_PY" ] || ORACLE_PY="$(command -v python || true)"
PY="$(command -v python || true)"

LEAN="$root/Implementation/Lean/.lake/build/bin/cpn2mcrl2.exe"
[ -x "$LEAN" ] || LEAN="$root/Implementation/Lean/.lake/build/bin/cpn2mcrl2"
DAFNY="$root/Implementation/Dafny/cpn2mcrl2.exe"
OCAML="$root/Implementation/OCaml/_build/default/bin/main.exe"

# The OCaml translator is a Linux binary here, so it is run through WSL when it is not
# directly executable, and reported as absent when neither works. Plan.md 8 rates a
# missing toolchain as a reported gap, not a red build.
ocaml_mode="none"
if [ -x "$OCAML" ] && "$OCAML" --help >/dev/null 2>&1; then
  ocaml_mode="native"
elif command -v wsl.exe >/dev/null 2>&1 &&
     wsl.exe -e bash -c "test -x '$(echo "$OCAML" | sed 's|^/c/|/mnt/c/|')'" 2>/dev/null; then
  ocaml_mode="wsl"
fi

# Success is "the output file was written", not "the exit code was zero". The three
# translators do not agree on how a refusal is signalled: Lean and OCaml exit non-zero
# and write nothing, and Dafny exits zero and writes nothing. Its own harness checks
# for the file too. Anything that treats exit status as the criterion reports Dafny as
# having accepted every net in corpus/rejected/.
translate() {  # translator flags in out   (out is the last argument)
  local t="$1"; shift
  local out_file="${@: -1}"
  rm -f "$out_file"
  case "$t" in
    lean)  "$LEAN"  "$@" >/dev/null 2>&1 ;;
    dafny) "$DAFNY" "$@" >/dev/null 2>&1 ;;
    ocaml)
      case "$ocaml_mode" in
        native) "$OCAML" "$@" >/dev/null 2>&1 ;;
        wsl)
          local args=""
          for a in "$@"; do args="$args '$(echo "$a" | sed 's|^/c/|/mnt/c/|')'"; done
          wsl.exe -e bash -c "'$(echo "$OCAML" | sed 's|^/c/|/mnt/c/|')'$args"             >/dev/null 2>&1 ;;
        *) return 99 ;;
      esac ;;
  esac
  [ -f "$out_file" ]
}

# The message a translator prints when it refuses, for the leg D report.
refusal() {  # translator net
  case "$1" in
    lean)  "$LEAN"  "$2" 2>&1 >/dev/null ;;
    dafny) "$DAFNY" "$2" 2>&1 >/dev/null ;;
    ocaml)
      case "$ocaml_mode" in
        native) "$OCAML" "$2" 2>&1 >/dev/null ;;
        wsl) wsl.exe -e bash -c                "'$(echo "$OCAML" | sed 's|^/c/|/mnt/c/|')' '$(echo "$2" | sed 's|^/c/|/mnt/c/|')'"                2>&1 >/dev/null ;;
        *) return 99 ;;
      esac ;;
  esac
}

# --------------------------------------------------------------------- reporting

fail=0
unsupported=0
uncompared=0
report() { printf '  %-18s %s\n' "$1" "$2"; }
states_of() { head -1 "$1" | tr -d ' \r' | sed 's/.*,\([0-9]*\))$/\1/'; }
edges_of()  { head -1 "$1" | tr -d ' \r' | sed 's/^des(\([0-9]*\),\([0-9]*\),.*/\2/'; }

# ltscompare EXITS ZERO whether or not the two LTSs are equal: the verdict is the last
# line of its stdout, "true" or "false". A harness written as `if ltscompare ...` is
# vacuous and reports every pair as bisimilar. Found while checking that this harness
# can be made to go red; see Tests/docs/Findings.md 1.
bisim() {
  [ "$("$MCRL2_BIN/ltscompare" -ebisim "$1" "$2" 2>/dev/null | tail -1)" = "true" ]
}

# ------------------------------------------------------------------- the corpus

only="$*"

# Read the corpus on file descriptor 3: the translators and the mCRL2 tools inherit
# stdin, and one of them swallowing the rest of the list is a bug that looks like a
# passing run over a corpus of one.
while read -r tier name summands params want_states want_edges <&3; do
  case "$tier" in ''|\#*) continue;; esac
  if [ -n "$only" ]; then
    case " $only " in *" $name "*) ;; *) continue;; esac
  fi

  # Tier 3 is the translators' own fixtures, read where they live rather than copied,
  # so that there is one copy of each net. Corpus.md 4.
  case "$tier" in
    tier3) net="$root/Implementation/Lean/fixtures/$name.cpn.json" ;;
    *)     net="$here/corpus/$tier/$name.cpn.json" ;;
  esac
  if [ ! -f "$net" ]; then
    echo "== $name =="; report "corpus" "MISSING $net"; fail=1; continue
  fi
  echo "== $name ($tier) =="

  # -- leg A, and the two shape checks, per encoding -------------------------
  ok=1
  for flag in "" "--list"; do
    sfx=""; [ -n "$flag" ] && sfx=".list"

    emitted=""
    for t in lean dafny ocaml; do
      target="$out/$name$sfx.$t.mcrl2"
      translate "$t" $flag "$net" "$target"; rc=$?
      if [ "$rc" = 99 ]; then continue; fi
      if [ "$rc" != 0 ]; then report "translate$sfx" "$t emitted nothing"; fail=1; ok=0; continue; fi
      emitted="$emitted $t"
    done
    [ "$ok" = 1 ] || continue

    ref=""
    same=1
    for t in $emitted; do
      if [ -z "$ref" ]; then ref="$out/$name$sfx.$t.mcrl2"
      elif ! cmp -s "$ref" "$out/$name$sfx.$t.mcrl2"; then same=0; fi
    done
    n_t=$(echo $emitted | wc -w)
    if [ "$same" = 1 ]; then
      report "leg A$sfx" "byte-identical across $n_t translators ($(echo $emitted | tr ' ' ','))"
    else
      report "leg A$sfx" "TRANSLATORS DISAGREE"; fail=1; ok=0; continue
    fi

    cp "$ref" "$out/$name$sfx.mcrl2"
    if ! "$MCRL2_BIN/mcrl22lps" -q "$out/$name$sfx.mcrl2" "$out/$name$sfx.lps" \
         2>"$out/$name$sfx.err"; then
      report "mcrl22lps$sfx" "REJECTED the emitted text (T0)"
      sed 's/^/    /' "$out/$name$sfx.err"; fail=1; ok=0; continue
    fi

    # The shape check needs a linearization that has not been simplified. By default
    # mcrl22lps applies constant elimination, which removes a parameter whose place
    # never changes, and rewrites a False-guarded summand away entirely -- so on a
    # degenerate net the default run reports a shape the translator did not emit.
    # See Tests/docs/Corpus.md 2.2. The plain .lps above is still what the LTS legs
    # use, because those simplifications preserve behaviour and make exploration
    # cheaper.
    "$MCRL2_BIN/mcrl22lps" -q --no-constelm --no-rewrite "$out/$name$sfx.mcrl2"       "$out/$name$sfx.shape.lps" 2>/dev/null
    info="$("$MCRL2_BIN/lpsinfo" "$out/$name$sfx.shape.lps" 2>/dev/null)"
    got_s="$(printf '%s\n' "$info" | sed -n 's/.*Number of summands *: *\([0-9]*\).*/\1/p')"
    got_p="$(printf '%s\n' "$info" | sed -n 's/.*Number of process parameters *: *\([0-9]*\).*/\1/p')"
    if [ "$got_s" = "$summands" ] && [ "$got_p" = "$params" ]; then
      report "shape$sfx" "$got_s summands, $got_p parameters"
    else
      report "shape$sfx" "expected $summands summands and $params parameters, got $got_s and $got_p"
      fail=1
    fi

    if ! "$MCRL2_BIN/lps2lts" -q "$out/$name$sfx.lps" "$out/$name$sfx.aut" \
         2>"$out/$name$sfx.err"; then
      report "lps2lts$sfx" "FAILED"; sed 's/^/    /' "$out/$name$sfx.err"; fail=1; ok=0; continue
    fi
    # Leg B2 reads the markings out of the state space, so it needs the unsimplified
    # process: constant elimination would drop exactly the parameters it compares.
    "$MCRL2_BIN/lps2lts" -q -ofsm "$out/$name$sfx.shape.lps" "$out/$name$sfx.fsm" 2>/dev/null
  done
  [ "$ok" = 1 ] || continue

  # -- leg C ------------------------------------------------------------------
  bag_states="$(states_of "$out/$name.aut")"
  list_states="$(states_of "$out/$name.list.aut")"
  if bisim "$out/$name.aut" "$out/$name.list.aut"; then
    if [ "$bag_states" = "$list_states" ]; then
      report "leg C" "the two encodings are bisimilar ($bag_states states each)"
    else
      report "leg C" "bisimilar; $bag_states bag states against $list_states list states"
    fi
  else
    report "leg C" "THE TWO ENCODINGS ARE NOT BISIMILAR"; fail=1
  fi

  # -- the oracle -------------------------------------------------------------
  "$ORACLE_PY" "$here/oracle/run.py" "$net" "$out/$name" >/dev/null 2>"$out/$name.oracle.err"
  orc=$?
  case "$orc" in
    2) report "oracle" "cannot express this net -- recorded, not a failure"
       sed 's/^/    /' "$out/$name.oracle.err"; unsupported=$((unsupported+1)); continue ;;
    3) report "oracle" "state cap exceeded -- no verdict for this net"
       uncompared=$((uncompared+1)); continue ;;
    0) : ;;
    *) report "oracle" "THE ADAPTER FAILED"
       sed 's/^/    /' "$out/$name.oracle.err"; fail=1; continue ;;
  esac
  o_states="$(states_of "$out/$name.oracle.aut")"
  o_edges="$(edges_of "$out/$name.oracle.aut")"
  report "oracle" "$o_states states, $o_edges edges ($(tail -1 "$out/$name.oracle.err" | sed 's/.*(\(.*\))/\1/'))"

  # -- the hand-computed counts, which are neither machine's opinion ----------
  if [ "$want_states" != "-" ]; then
    if [ "$o_states" = "$want_states" ] && [ "$o_edges" = "$want_edges" ]; then
      report "by hand" "$want_states states and $want_edges edges, as written down"
    else
      report "by hand" "EXPECTED $want_states states and $want_edges edges"
      fail=1
    fi
  fi

  # -- leg B ------------------------------------------------------------------
  for flag in "" ".list"; do
    if bisim "$out/$name.oracle.aut" "$out/$name$flag.aut"; then
      report "leg B$flag" "bisimilar to the oracle"
    else
      report "leg B$flag" "NOT BISIMILAR TO THE ORACLE"
      fail=1
    fi
  done

  # -- leg B2, bag encoding only ----------------------------------------------
  if [ -f "$out/$name.fsm" ]; then
    if msg="$("$PY" "$here/scripts/markings.py" "$out/$name.fsm" \
                "$out/$name.oracle.markings" "$out/$name.oracle.aut" 2>&1)"; then
      report "leg B2" "$(echo "$msg" | tail -1)"
    else
      report "leg B2" "MARKINGS DIFFER FROM THE ORACLE"
      printf '%s\n' "$msg" | sed 's/^/    /'
      fail=1
    fi
  fi
# The corpus list is filtered through `tr -d '\r'`: on a Windows checkout the file
# arrives with CRLF, the last field of every row then ends in a carriage return, and
# the shape comparison can never match -- it prints "expected 4 and 3, got 4 and 3"
# and fails. See Tests/docs/Findings.md 2.
done 3< <(tr -d '\r' < "$here/corpus/expected.tsv")

# ------------------------------------------------------------------- leg D

if [ -z "$only" ]; then
  for bad in "$here"/corpus/rejected/*.cpn.json; do
    [ -e "$bad" ] || continue
    b="$(basename "$bad" .cpn.json)"
    echo "== $b (must be rejected) =="
    allrejected=1
    refusers=""
    for t in lean dafny ocaml; do
      translate "$t" "$bad" "$out/rejected.$b.$t.mcrl2"; rc=$?
      [ "$rc" = 99 ] && continue
      if [ "$rc" = 0 ]; then
        report "leg D" "$t ACCEPTED a net that is not a CPN"; allrejected=0; fail=1
      else
        refusers="$refusers $t"
      fi
    done
    if [ "$allrejected" = 1 ]; then
      report "leg D" "refused by $(echo $refusers | tr ' ' ',')"
      refusal lean "$bad" | head -1 | sed 's/^/    /'
    fi
  done
fi

# ------------------------------------------------------------------- summary

echo
[ "$ocaml_mode" = "none" ] && echo "note: the OCaml translator was not runnable; leg A compared two translators"
[ "$unsupported" -gt 0 ] && echo "note: $unsupported net(s) the oracle cannot express -- see Oracle.md 2.4"
[ "$uncompared" -gt 0 ] && echo "note: $uncompared net(s) over the state cap, with no verdict"
if [ "$fail" -eq 0 ]; then echo "all green"; else echo "FAILURES"; fi
exit "$fail"
