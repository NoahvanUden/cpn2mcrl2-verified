#!/usr/bin/env bash
#
# The round-trip criterion of Tests/docs/Plan.md 3.1 item 4, which is what makes the
# M7 importer trustworthy enough to build a corpus on:
#
#   PNML --pnml2cpn.py--> native JSON --translator--> mCRL2, byte-identical to the
#   text the committed fixture produces.
#
# Two of the three fixtures meet that exactly. `jobs` cannot, and the reason is the
# finding recorded in ../README.md 3.3: standard PNML has no projection on a product
# sort, so the same behaviour has to be written with a tuple pattern, which is a
# different net. It is therefore checked up to bisimilarity instead.
#
# Usage:  scripts are run from anywhere; paths are resolved from this file.
set -u

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
root="$(cd "$here/../../.." && pwd)"
out="$here/out"
mkdir -p "$out"

MCRL2_BIN="${MCRL2_BIN:-}"
if [ -z "$MCRL2_BIN" ]; then
  for cand in "/c/Program Files/mCRL2/bin" "/usr/local/bin" "/opt/mcrl2/bin"; do
    if [ -x "$cand/mcrl22lps" ] || [ -x "$cand/mcrl22lps.exe" ]; then MCRL2_BIN="$cand"; break; fi
  done
fi
if [ -z "$MCRL2_BIN" ] && command -v mcrl22lps >/dev/null 2>&1; then
  MCRL2_BIN="$(dirname "$(command -v mcrl22lps)")"
fi

PY="${PYTHON:-python}"
LEAN="$root/Implementation/Lean/.lake/build/bin/cpn2mcrl2.exe"
[ -x "$LEAN" ] || LEAN="$root/Implementation/Lean/.lake/build/bin/cpn2mcrl2"
DAFNY="$root/Implementation/Dafny/cpn2mcrl2.exe"
OCAML="$root/Implementation/OCaml/_build/default/bin/main.exe"

fail=0
report() { printf '  %-22s %s\n' "$1" "$2"; }

# The OCaml translator may be a Linux binary built under WSL, in which case it is run
# through wsl.exe. Anything else is skipped rather than failed: Tests/docs/Plan.md 8
# rates a missing toolchain as a reported gap, not a red build.
ocaml_mode="none"
if [ -x "$OCAML" ] && "$OCAML" --help >/dev/null 2>&1; then
  ocaml_mode="native"
elif command -v wsl.exe >/dev/null 2>&1 &&
     wsl.exe -e bash -c "test -x '$(echo "$OCAML" | sed 's|^/c/|/mnt/c/|')'" 2>/dev/null; then
  ocaml_mode="wsl"
fi

run_ocaml() {  # flags... in out
  case "$ocaml_mode" in
    native) "$OCAML" "$@" ;;
    wsl)
      local args=""
      for a in "$@"; do args="$args '$(echo "$a" | sed 's|^/c/|/mnt/c/|')'"; done
      wsl.exe -e bash -c "'$(echo "$OCAML" | sed 's|^/c/|/mnt/c/|')'$args" ;;
    *) return 99 ;;
  esac
}

for name in counter multitoken jobs; do
  echo "== $name =="
  if ! "$PY" "$here/../pnml2cpn.py" "$here/$name.pnml" "$out/$name.json"; then
    report "import" "FAILED"; fail=1; continue
  fi
  report "import" "ok"

  for flag in "" "--list"; do
    sfx=""; [ -n "$flag" ] && sfx=".list"
    ref="$root/Implementation/Lean/out/$name$sfx.mcrl2"

    for t in lean dafny ocaml; do
      target="$out/$name$sfx.$t.mcrl2"
      case "$t" in
        lean)  "$LEAN"  $flag "$out/$name.json" "$target" >/dev/null 2>&1; rc=$? ;;
        dafny) "$DAFNY" $flag "$out/$name.json" "$target" >/dev/null 2>&1; rc=$? ;;
        ocaml) run_ocaml $flag "$out/$name.json" "$target" >/dev/null 2>&1; rc=$? ;;
      esac
      if [ "$rc" = 99 ]; then report "$t$sfx" "skipped (no OCaml runtime)"; continue; fi
      if [ "$rc" != 0 ]; then report "$t$sfx" "TRANSLATE FAILED"; fail=1; continue; fi
      if [ ! -f "$ref" ]; then report "$t$sfx" "no reference text at $ref"; fail=1; continue; fi
      if cmp -s "$target" "$ref"; then
        report "$t$sfx" "byte-identical to the fixture's output"
      elif [ "$name" = jobs ]; then
        report "$t$sfx" "differs (expected: see ../README.md 3.3)"
      else
        report "$t$sfx" "DIFFERS from $ref"
        fail=1
      fi
    done
  done

  # jobs is checked up to bisimilarity instead, which is the whole of what standard
  # PNML can deliver for it.
  if [ "$name" = jobs ] && [ -n "$MCRL2_BIN" ]; then
    if "$MCRL2_BIN/mcrl22lps" -q "$out/jobs.lean.mcrl2" "$out/jobs.lps" 2>/dev/null &&
       "$MCRL2_BIN/lps2lts" -q "$out/jobs.lps" "$out/jobs.aut" 2>/dev/null &&
       "$MCRL2_BIN/ltscompare" -ebisim "$root/Implementation/Lean/fixtures/jobs.aut" \
          "$out/jobs.aut" >/dev/null 2>&1; then
      report "bisimilar" "to the jobs golden LTS"
    else
      report "bisimilar" "NOT bisimilar to the jobs golden LTS"
      fail=1
    fi
  fi
done

# Item 3 of Tests/docs/Plan.md 3.1: anything outside InputFormat.md 4.1 is refused by
# name, outside the trust boundary, rather than mistranslated inside it.
for bad in "$here"/rejected/*.pnml; do
  [ -e "$bad" ] || continue
  echo "== $(basename "$bad" .pnml) (must be rejected) =="
  if msg="$("$PY" "$here/../pnml2cpn.py" "$bad" 2>&1 >/dev/null)"; then
    report "reject" "IMPORTED a net outside the native language"
    fail=1
  else
    report "reject" "refused"
    printf '%s
' "$msg" | sed 's/^/    /'
  fi
done

echo
if [ "$fail" -eq 0 ]; then echo "round trip green"; else echo "FAILURES"; fi
exit "$fail"
