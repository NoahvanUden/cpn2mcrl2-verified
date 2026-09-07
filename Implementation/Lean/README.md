# Translator #1, Lean 4

A Colored Petri Net goes in as a file, an mCRL2 specification comes out as text, and the term it
prints is *proved* to denote the $c_t$ and $g_t$ of Definition 14 — and, composed with Theorem 1,
to denote an LTS bisimilar to the net's reachability graph. Two backends: one `Bag` per place,
which is Definition 14 literally, and one `List` per place, which is faster and is proved to
refine it.

There are two Lake packages here, and the split is deliberate. [`Cpn2mCrl2/`](Cpn2mCrl2) is the
translator: no Mathlib, no dependency on [`Proof/`](../../Proof), a clean build in about fifteen
seconds. [`Bridge/`](Bridge) is proof only, produces no code, and depends on both — it is what
makes the composition with Theorem 1 a Lean term rather than an argument in prose.

## Running it

```bash
cd Implementation/Lean
lake build
.lake/build/bin/cpn2mcrl2 fixtures/counter.cpn.json
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

The `- {:}` and `+ {:}` at every place a transition does not touch are Definition 14 written out
literally. `--list` selects the second backend, one `List` per place instead of one `Bag`.

The bridge is built separately, and needs Mathlib — which it shares with
[`Proof/`](../../Proof) rather than downloading a second copy:

```bash
cd Bridge && lake build
```

The test harness needs the [mCRL2 toolset](https://www.mcrl2.org/) on the machine:

```bash
MCRL2_BIN=/path/to/mcrl2/bin bash scripts/check.sh
```

It translates every fixture in both encodings, feeds each to `mcrl22lps`, checks the summand and
parameter counts, compares the LTS against a recorded one with `ltscompare -ebisim`, compares the
two encodings against each other, and checks that every fixture under `fixtures/rejected/` is
refused.

## The files

The chain of [`Plan.md`](../docs/Plan.md) §2, left to right. The Dafny and OCaml translators use
the same filenames, so the three can be read side by side.

| File | What it holds | Tier |
| --- | --- | --- |
| [`Cpn2mCrl2/Util.lean`](Cpn2mCrl2/Util.lean) | duplicate removal, so that nothing outside the toolchain is needed | — |
| [`Cpn2mCrl2/Color.lean`](Cpn2mCrl2/Color.lean) | the color grammar of [`InputFormat.md`](../docs/InputFormat.md) §4.1, and values | — |
| [`Cpn2mCrl2/Bag.lean`](Cpn2mCrl2/Bag.lean) | Definition 1, finitely supported | — |
| [`Cpn2mCrl2/ListOps.lean`](Cpn2mCrl2/ListOps.lean) | lists as bags: the multiset operations | — |
| [`Cpn2mCrl2/Expr.lean`](Cpn2mCrl2/Expr.lean) | `EXPR`, intrinsically typed | — |
| [`Cpn2mCrl2/Typing.lean`](Cpn2mCrl2/Typing.lean) | evaluation preserves sorts | — |
| [`Cpn2mCrl2/Net.lean`](Cpn2mCrl2/Net.lean) | Definitions 4 and 5, and `Net.Valid` | T1 |
| [`Cpn2mCrl2/Semantics.lean`](Cpn2mCrl2/Semantics.lean) | Definitions 6 to 9 — the reference side | — |
| [`Cpn2mCrl2/Lpe.lean`](Cpn2mCrl2/Lpe.lean) | Definitions 13 and 15, syntactically | — |
| [`Cpn2mCrl2/Translate.lean`](Cpn2mCrl2/Translate.lean) | Definition 14 | — |
| [`Cpn2mCrl2/Correct.lean`](Cpn2mCrl2/Correct.lean) | **the T2 theorems** | T2 |
| [`Cpn2mCrl2/ListEncoding.lean`](Cpn2mCrl2/ListEncoding.lean) | the second backend, and **the refinement** | T5 |
| [`Cpn2mCrl2/Print.lean`](Cpn2mCrl2/Print.lean) | the mCRL2 encoding of [`Target.md`](../docs/Target.md) §1 | — |
| [`Cpn2mCrl2/PrintList.lean`](Cpn2mCrl2/PrintList.lean) | the same for the list encoding | — |
| [`Cpn2mCrl2/Json.lean`](Cpn2mCrl2/Json.lean) | the importer — **outside the trust boundary** | T1 |
| [`Main.lean`](Main.lean) | the command line | — |
| [`Cpn2mCrl2/Examples/Counter.lean`](Cpn2mCrl2/Examples/Counter.lean) | Examples 3, 4, 5 and 9, checked | — |

And the bridge, which nothing above depends on:

| File | What it holds |
| --- | --- |
| [`Bridge/Bridge/Lang.lean`](Bridge/Bridge/Lang.lean) | the concrete language as one of `Proof/`'s `ExprLang`s |
| [`Bridge/Bridge/Cpn.lean`](Bridge/Bridge/Cpn.lean) | a validated `Net` as a `Proof/` `CPN` |
| [`Bridge/Bridge/Vars.lean`](Bridge/Bridge/Vars.lean) | arcs against index pairs, and the two readings of $\mathrm{Var}(t)$ |
| [`Bridge/Bridge/Semantics.lean`](Bridge/Bridge/Semantics.lean) | Definitions 6 and 7 on both sides |
| [`Bridge/Bridge/Soundness.lean`](Bridge/Bridge/Soundness.lean) | **T2 composed with Theorem 1** |
| [`Bridge/Bridge/ListSoundness.lean`](Bridge/Bridge/ListSoundness.lean) | **the list backend, composed with Theorem 1** |
| [`Bridge/Bridge/Example.lean`](Bridge/Bridge/Example.lean) | the whole chain, on Example 3 |

## What is proved

In [`Correct.lean`](Cpn2mCrl2/Correct.lean), for any net satisfying `Net.Valid`:

| | |
| --- | --- |
| `Net.toLpe_cond` | the emitted condition holds under a marking and a binding exactly when Definition 6 says the binding element is enabled |
| `Net.toLpe_next` | the emitted next-state term for a place evaluates to the bag Definition 7 leaves there |
| `Net.toLpe_step` | consequently, the two transition relations agree |

and in [`Bridge/`](Bridge), the theorems they compose into:

| | |
| --- | --- |
| `Net.bisimilar_reachabilityGraph_emitted` | for a CPN that passes the T1 validation, the reachability graph of Definition 9 and the LTS denoted by the emitted specification are bisimilar |
| `Net.bisimilar_reachabilityGraph_emittedList` | the same for the list-encoded specification |

Between the two sides of that statement stand `CPN.bisimulation_transRel` — Theorem 1 of the
thesis, proved in [`Proof/`](../../Proof) — and `Net.toLpe_step`, which is T2.
`Cpn2mCrl2.Examples.Counter.bisimilar_emitted` instantiates the whole chain on Example 3.

None of these is `rfl`. One side is a Lean predicate; the other is the *evaluation of a term*
the translation assembled, and they agree only because the term was assembled out of the right
operations.

**No `sorry`.** `#print axioms` reports `propext`, `Quot.sound` and `Classical.choice`, which is
what anything built on Lean's standard library reports.

## What is not here

**T0 and T4 are tested, never proved.** Whether `mcrl22lps` accepts the emitted text, and whether
what it reads back denotes the term that was printed, would need a formalized mCRL2 grammar.
`scripts/check.sh` runs the tool instead, and [`Tests/`](../../Tests/README.md) compares the
result against a Petri net library written by other people.

**Importers.** Only the native format of [`InputFormat.md`](../docs/InputFormat.md) §4 is read
here; PNML goes through [`Implementation/tools/`](../tools/README.md).

[`Notes.md`](Notes.md) has the design decisions behind the above — why the product sort is
avoided rather than added, why extrinsic scoping made the substitution lemma cheap, what
building the bridge cost and the two slips it found, and the order problem in the list backend.

## Sources

- N. van Uden, *Model checking for analysis of BPMN models*, Master Thesis Report, Eindhoven
  University of Technology, April 2025. Definitions 1, 2, 4 to 9 and 13 to 15 are transcribed
  in [`Thesis/docs/`](../../Thesis/docs).
- [`Proof/`](../../Proof), where those definitions are formalized and Theorem 1 is proved.
- mCRL2 toolset 202307.1, which every run of `scripts/check.sh` is against.
  [mcrl2.org](https://www.mcrl2.org/)
