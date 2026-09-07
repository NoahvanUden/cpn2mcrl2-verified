# Translator #2, Dafny

The same translation as [`Implementation/Lean/`](../Lean/README.md), against the same
specification, with the proof obligations discharged by an SMT solver instead of by tactics. A
Colored Petri Net goes in as a file, an mCRL2 specification comes out as text, and the term it
prints is *proved* to denote the $c_t$ and $g_t$ of Definition 14. Both backends: one `Bag` per
place, and one `List` per place proved to refine it.

The strongest evidence that the two translators agree is not in any proof: all six emitted
specifications — three fixtures, two encodings — are **byte-identical** to the ones the Lean
translator emits, and `scripts/check.sh` rechecks that on every run.

## Running it

Dafny 4.11 with Z3, and .NET 8 or newer.

```bash
cd Implementation/Dafny
dafny build --standard-libraries --target:cs --output cpn2mcrl2 src/*.dfy
./cpn2mcrl2 fixtures/counter.cpn.json
```

That fixture is Example 3 of the thesis, and the output is its Example 9:

```
act t1, t2, t3;

proc Spec(p1 : Bag(Int), p2 : Bag(Int), p3 : Bag(Int)) =
    sum h : Int . (({h: 1} <= p1) && true) -> t1 . Spec(((p1 - {h: 1}) + {:}), ((p2 - {:}) + {(h + 1): 1}), ((p3 - {:}) + {:}))
  + sum h : Int . (({h: 1} <= p2) && (h <= 3)) -> t2 . Spec(((p1 - {:}) + {h: 1}), ((p2 - {h: 1}) + {:}), ((p3 - {:}) + {:}))
  + sum h : Int . (({h: 1} <= p2) && (3 < h)) -> t3 . Spec(((p1 - {:}) + {:}), ((p2 - {h: 1}) + {:}), ((p3 - {:}) + {h: 1}));

init Spec({1: 1}, {:}, {:});
```

`--list` selects the second backend, one `List` per place instead of one `Bag`.

To check the proofs without building anything:

```bash
dafny verify --standard-libraries src/*.dfy
```

266 obligations, about 28 seconds on a laptop.

The test harness needs the [mCRL2 toolset](https://www.mcrl2.org/), and picks up the Lean binary
for the differential test if it has been built:

```bash
MCRL2_BIN=/path/to/mcrl2/bin bash scripts/check.sh
```

It translates every fixture in both encodings, feeds each to `mcrl22lps`, checks the summand and
parameter counts, compares the LTS against a recorded one with `ltscompare -ebisim`, compares
the two encodings, diffs both against the Lean translator's output, and checks that every
fixture under `fixtures/rejected/` is refused.

## The files

The chain of [`Plan.md`](../docs/Plan.md) §2, left to right. Every file has a counterpart of the
same name in [`Implementation/Lean/Cpn2mCrl2/`](../Lean/Cpn2mCrl2), deliberately, so that the
two can be read side by side.

| File | What it holds | Tier |
| --- | --- | --- |
| [`src/Util.dfy`](src/Util.dfy) | duplicate removal, association lookup, string joining | — |
| [`src/Color.dfy`](src/Color.dfy) | the color grammar of [`InputFormat.md`](../docs/InputFormat.md) §4.1, and values | — |
| [`src/Bag.dfy`](src/Bag.dfy) | Definition 1, finitely supported | — |
| [`src/ListOps.dfy`](src/ListOps.dfy) | lists as bags: the multiset operations | — |
| [`src/Expr.dfy`](src/Expr.dfy) | `EXPR`, with `SortOf` inferring rather than indexing | — |
| [`src/Typing.dfy`](src/Typing.dfy) | evaluation preserves sorts | — |
| [`src/Net.dfy`](src/Net.dfy) | Definitions 4 and 5, and `Valid` | T1 |
| [`src/Semantics.dfy`](src/Semantics.dfy) | Definitions 6 to 9 — the reference side | — |
| [`src/Lpe.dfy`](src/Lpe.dfy) | Definitions 13 and 15, syntactically | — |
| [`src/Translate.dfy`](src/Translate.dfy) | Definition 14 | — |
| [`src/Correct.dfy`](src/Correct.dfy) | **the T2 theorems** | T2 |
| [`src/ListEncoding.dfy`](src/ListEncoding.dfy) | the second backend, and **the refinement** | T5 |
| [`src/Print.dfy`](src/Print.dfy) | the mCRL2 encoding of [`Target.md`](../docs/Target.md) §1 | — |
| [`src/PrintList.dfy`](src/PrintList.dfy) | the same for the list encoding | — |
| [`src/Import.dfy`](src/Import.dfy) | the importer — **outside the trust boundary** | T1 |
| [`src/Main.dfy`](src/Main.dfy) | the command line | — |

## What is proved

In [`src/Correct.dfy`](src/Correct.dfy), for any net satisfying `Valid`:

| | |
| --- | --- |
| `ToLpeCond` | the emitted condition holds under a marking and a binding exactly when Definition 6 says the binding element is enabled |
| `ToLpeNext` | the emitted next-state term for a place evaluates to the bag Definition 7 leaves there |
| `ToLpeStep` | consequently, the two transition relations agree |

and in [`src/ListEncoding.dfy`](src/ListEncoding.dfy), the refinement between the two backends:

| | |
| --- | --- |
| `StepOfToLpeListStep` | a step of the list encoding is matched by a step of the bag encoding, with the reached markings still representing the same bags |
| `ToLpeListStepOfStep` | and conversely |
| `ListRelInit` | the two encodings start in markings that represent the same bags |

Neither identity is definitional. One side is a predicate; the other is the *evaluation of a
term* the translation assembled, and they agree only because the term was assembled out of the
right operations.

**No assumptions and no axioms**: every proof is a `lemma` body checked by Z3. Checked for
vacuity with `--warn-contradictory-assumptions`; the one branch that proves something from
contradictory assumptions is marked `{:contradiction}` and is vacuous on purpose — a bag-sorted
variable cannot be color-sorted.

## What is not here

**The composition with Theorem 1.** Theorem 1 is a Lean term in [`Proof/`](../../Proof), and
nothing in Dafny can be an argument to a Lean theorem. This package establishes T1, T2 and T5;
the step from there to "bisimilar to the reachability graph" is prose here where it is a term in
[`Implementation/Lean/Bridge/`](../Lean/Bridge).

That is the honest statement of what a second implementation buys. It does not double the
guarantee. It buys an independent check that the specification in
[`Implementation/docs/`](../docs) is implementable as written, an independent proof of the same
T2 statement, and a differential test with real teeth.

**T0 and T4 are tested, never proved**, for the same reason as in the Lean translator: it would
need a formalized mCRL2 grammar.

**Importers.** Only the native format of [`InputFormat.md`](../docs/InputFormat.md) §4 is read
here; PNML goes through [`Implementation/tools/`](../tools/README.md).

[`Notes.md`](Notes.md) has the design decisions and the language comparison — where SMT helped,
where it did not, and why the prediction that dependent types would matter was wrong in both
directions.

## Sources

- N. van Uden, *Model checking for analysis of BPMN models*, Master Thesis Report, Eindhoven
  University of Technology, April 2025. Definitions 1, 2, 4 to 9 and 13 to 15 are transcribed in
  [`Thesis/docs/`](../../Thesis/docs).
- [`Proof/`](../../Proof), where those definitions are formalized and Theorem 1 is proved, and
  [`Implementation/Lean/`](../Lean), the translator this one is compared against.
- Dafny 4.11 and the Dafny standard libraries — `Std.Wrappers`, `Std.JSON`, `Std.FileIO`.
  [dafny.org](https://dafny.org/)
- mCRL2 toolset 202307.1. [mcrl2.org](https://www.mcrl2.org/)
