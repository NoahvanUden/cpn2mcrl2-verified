# Findings

What building the harness found. Recorded as they were found, before being fixed, per
[`Plan.md`](Plan.md) §9.

The first two are the ones that matter: **both are in the checks this repository already had,
and both were found by asking whether the new harness could be made to go red rather than by
running it.** A test that cannot fail is worth exactly nothing, and two of the repository's
existing checks could not fail.

---

## 1. `ltscompare` exits zero whether or not the LTSs are equal

**Severity: high. A check that always passed.**

```
$ ltscompare -ebisim conflict.aut one-step.aut
LTSs are not equal (strong bisimilarity using the O(m log n) algorithm ...)
false
$ echo $?
0
```

The verdict is the last line of stdout — `true` or `false` — and the exit status is 0 either
way. Every harness in this repository was written as

```bash
if "$MCRL2_BIN/ltscompare" -ebisim "fixtures/$name.aut" "out/$name.aut" >/dev/null 2>&1; then
  report "lts" "bisimilar to the golden LTS"
```

which discards the verdict and reports success unconditionally.

**What it affected.** Seven call sites: the T4 golden-LTS check and the T5 refinement check in
each of `Implementation/Lean`, `Implementation/Dafny` and `Implementation/OCaml`, plus the
`jobs` check in `Implementation/tools/roundtrip`. So the two claims those checks back —

> lps2lts gives an LTS strongly bisimilar to the recorded golden one (T4)

> the two encodings are strongly bisimilar to each other (T5, tested)

— were untested since the harness was written, and
[`Implementation/docs/Plan.md`](../../Implementation/docs/Plan.md) §7's "**Held.**
`scripts/check.sh` runs the toolset on every fixture" was true about the toolset being *run* and
not about anything being *checked*.

**Whether the claims were nonetheless true: yes.** Every one of them passes now that the
verdict is read, and the independent oracle of [`Oracle.md`](Oracle.md) agrees with all three
goldens as well. Nothing was hiding behind it. That is luck rather than diligence.

**Fixed** in all four harnesses with

```bash
bisim() {
  [ "$("$MCRL2_BIN/ltscompare" -ebisim "$1" "$2" 2>/dev/null | tail -1)" = "true" ]
}
```

---

## 2. CRLF makes the shape check compare a number to itself and fail

**Severity: medium. A check that always failed, on Windows, and said so unhelpfully.**

```
  shape          expected 4 summands and 3 parameters, got 4 and 3
```

`fixtures/expected.tsv` is checked out with CRLF on Windows, so the last field read from each
row ends in a carriage return and `[ "$got_p" = "$params" ]` compares `3` with `3\r`.

The Lean and Dafny harnesses failed this way on every fixture. The OCaml harness — written last,
at M5 — already carries a comment about it and strips the CR from both sides, so the bug was
found once and fixed in one of three places.

**The two together are worth noticing.** One check could not fail and one could not pass, and
between them the repository's harness reported "all fixtures green" on Linux and "FAILURES" on
Windows for reasons unrelated to either translator.

**Fixed** by filtering the corpus list through `tr -d '\r'` in each harness.

---

## 3. `mcrl22lps` simplifies away the shape the translator emitted

**Severity: low, but it changes what the shape check means.**

[`Target.md`](../../Implementation/docs/Target.md) §2 asks that the linearized process have
$|T| + 1$ summands and $|P|$ parameters — "If not, what was emitted was not an LPE." On the two
degenerate tier-1 nets that is false of a perfectly good emission:

| Net | default | `--no-constelm` | `--no-constelm --no-rewrite` |
| --- | --- | --- | --- |
| `no-init` | 2 summands, **0** parameters | 2, 2 | 2, 2 |
| `dead` | **1** summand, **0** parameters | 1, 2 | 2, 2 |

Constant elimination drops a parameter whose place never changes, and the rewriter deletes a
summand whose guard is `False`. Neither is a defect: both preserve behaviour, and neither says
anything about what the translator wrote.

**What it affected.** Nothing, because no fixture in the repository is degenerate — `counter`,
`jobs` and `multitoken` all have places that change and guards that can hold. Tier 1 exists to
contain exactly this kind of net.

**Fixed** by linearizing twice in `Tests/scripts/check.sh`: `--no-constelm --no-rewrite` for the
shape check and for the marking extraction of leg B2, and a plain run for T0 and for state-space
generation, where the simplifications are welcome.

---

## 4. The three translators disagree about how to signal a refusal

**Severity: low for the translators, high for anything that drives them.**

| Translator | Exit status | Output file |
| --- | --- | --- |
| Lean | 1 | not written |
| OCaml | 1 | not written |
| Dafny | **0** | not written |

A harness that treats exit status as the criterion reports Dafny as having accepted every net in
`corpus/rejected/`, which is what the first run of leg D did. The Dafny harness already checks
for the file rather than the status, so this was known there and nowhere else.

**Fixed** by making "the output file exists" the criterion everywhere, which is right for all
three.

---

## 5. Standard PNML cannot express `jobs`

Recorded in full in [`Implementation/tools/README.md`](../../Implementation/tools/README.md)
§3.3. ISO/IEC 15909-2 has no projection operator on a product sort, so the fixture's
$\mathrm{proj}(j, \textit{state}) = \textit{fresh}$ has to become a tuple *pattern* over two
variables — a different net with the same behaviour. It round-trips to a bisimilar LTS and not
to byte-identical text.

Two smaller ones next to it: product sorts are positional where the native format's records are
named, so field names need a `toolspecific` annotation; and a PNML `<tuple>` carries no sort, so
two product sorts of equal arity make a file ambiguous, which the importer refuses rather than
guesses.

---

## 6. SNAKES' PNML is not standard PNML

The measurement [`Plan.md`](Plan.md) §3 turns on, and it came out against the architecture that
section describes. See [`Oracle.md`](Oracle.md) §3.2 for what SNAKES emits. The consequence is
that the corpus is native JSON and the adapter builds the SNAKES net, so the bridge stays inside
the test's trust boundary and the mitigation is the one §8 names: the adapter is structurally
dumb and computes no behaviour.

M7 was still worth doing first, and its round trip is green — but it serves E6 and the Model
Checking Contest corpus rather than the oracle.

---

## 7. Three errors in `Corpus.md` §5, written before the fixtures were read

The rejected-corpus table mapped the existing fixtures to the wrong checks: `badcolor` is check
5 and not check 2, `shadow` is `namesDisjoint` and not check 7, and `keyword` is a `Target.md`
§1 concern rather than a §4.3 one. Corrected in place. The table was written from
[`InputFormat.md`](../../Implementation/docs/InputFormat.md) §4.3 without opening the fixtures
it claimed to classify.

---

## 8. Two enumerations sharing a constructor name emit text mCRL2 refuses

**Severity: high. A defect in all three translators, found by the random search, and
invisible to every other check in the repository.**

A net may declare two enumerations that share a constructor:

```json
"C2": { "kind": "enum", "ids": ["a", "b"] },
"C3": { "kind": "enum", "ids": ["a", "c"] }
```

Nothing forbids it. Definition 5's colour sets are sets, and two sets may both contain an
element called $a$; [`InputFormat.md`](../../Implementation/docs/InputFormat.md) §4.1 says a
colour is `enum(name, [id, ...])` without any condition relating one enumeration's identifiers
to another's; and none of the seven T1 checks of §4.3 mentions it. All three translators
therefore accept the net and emit

```
sort C2 = struct a | b;
sort C3 = struct a | c;
```

which `mcrl22lps` refuses:

```
[error]   Double declaration of constructor constant a.
[error]   Type checking of data expression failed.
```

**Why nothing caught it.** Leg A is blind by construction — all three translators emit the
same bytes, because all three read the same specification and the specification does not
mention the problem. No fixture in the repository declares two enumerations at all: `counter`
and `multitoken` have only `Int` and `Bool`, and `jobs` has a single `Status`. It took a
generator that does not know what nets are supposed to look like: seven of the first thirty
seeds produced it.

**It is T0, the cheapest tier, and it is exactly what T0 is for.**
[`Plan.md`](../../Implementation/docs/Plan.md) §2 calls `mcrl22lps` acceptance "the honest
ceiling ... cheap and catches everything a printer realistically gets wrong". It did.

**Not fixed here, because the fix is a decision about the project.** Two options, and they are
not equivalent:

1. **T1 gains a check** that constructor names are globally unique, and such nets are refused
   at the boundary. Cheap, and consistent with how `Target.md` §1's reserved-keyword check
   already treats mCRL2's namespace as a constraint on the input. It narrows Definition 5:
   nets that are perfectly good CPNs become unacceptable input.
2. **The printer qualifies constructors per sort** — `C2_a`, `C3_a`. Nothing is refused, and
   Definition 5 is unnarrowed, but every emitted specification changes, so the golden text and
   the T2 proofs about the printer move with it.

Both change all three translators, and [`CLAUDE.md`](../../CLAUDE.md)'s rule is not to fill a
gap like this by assumption, so it was put to the author.

**Resolved: option 1.** All three translators now refuse such a net at T1, with the same
message, and the check is recorded as an **eighth** check in
[`InputFormat.md`](../../Implementation/docs/InputFormat.md) §4.3 — marked as an addition to the
thesis, because Definition 5 does not ask for it and the target does. The precise rule was
measured rather than guessed:

| Collision | `mcrl22lps` |
| --- | --- |
| two enumeration constants | **rejected** |
| a field-less record's constructor against an enumeration constant | **rejected** |
| a record constructor of positive arity against a constant | accepted |
| two records sharing a field name | accepted |
| a field name equal to a constant | accepted |

So the check is on *nullary* constructors only: every enumeration constant, plus the sort name
of any record with no fields. `Net.nullaryCtors` in Lean, `NullaryCtors` in Dafny,
`nullary_ctors` in OCaml.

The net moved from `corpus/known-failing/` — a directory that no longer exists — to
`corpus/rejected/shared-ctor.cpn.json`, where leg D now asserts that all three refuse it. The
generator keeps its disjoint constructors, so the search still explores past this shape rather
than rediscovering it at a quarter of all seeds.

**One gap in the fix, stated rather than hidden.** Z3 is not installed on this machine, so the
Dafny sources were compiled with `--no-verify` and *not re-verified*. The change is additive —
a new conjunct in `Valid`, which only strengthens the hypothesis every downstream proof already
assumes, and `NullaryCtors` is a structurally recursive function on a sequence — so nothing
about the existing proofs should move. "Should" is doing real work in that sentence, and
`dafny verify --standard-libraries src/*.dfy` is the thing that would replace it.

---

## 9. What the oracle confirmed

Not a defect, and the point of the exercise.

- **All three golden LTSs are right.** `counter` (7 states, 6 edges), `jobs` and `multitoken`
  (4 and 4) match SNAKES exactly. Two of the three had never been checked against anything: they
  were derived by hand and committed alongside the harness that checks them.
- **All thirteen tier-1 nets match the counts written down before either machine ran**, and the
  markings match state for state under leg B2.
- **The order problem reproduces over finite colours.** `two-tokens` gives 4 states under the bag
  encoding and 5 under the list encoding, bisimilar anyway — and the oracle independently says 4
  is the right number, which is a stronger statement than the two encodings agreeing with each
  other.
