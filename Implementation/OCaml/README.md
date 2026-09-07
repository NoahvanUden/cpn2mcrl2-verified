# Translator #3, OCaml — and why it is not verified

A Colored Petri Net goes in as a file and an mCRL2 specification comes out as text, in both
encodings, byte for byte the same as the other two translators emit. **Nothing about it is
proved**, and that is the result this part of the project delivers rather than a shortfall.

OCaml was chosen because Cameleer verifies GOSPEL-annotated OCaml by translating it to WhyML, so
where it works you get verified code that is also code somebody would have written anyway —
which neither Lean nor Dafny quite gives you. The translator below is code somebody would have
written anyway, and Cameleer cannot read it. [`Notes.md`](Notes.md) is the measurement, and is
the part of this package worth reading if you are choosing a verification stack.

## Running it

OCaml 4.14 and dune. The translator needs nothing else; `yojson` is used only by the importer,
which is outside the trust boundary.

```bash
cd Implementation/OCaml
dune build
./_build/default/bin/main.exe fixtures/counter.cpn.json
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

The test harness needs the [mCRL2 toolset](https://www.mcrl2.org/), and picks up the Lean and
Dafny binaries for the differential test if they have been built:

```bash
bash scripts/check.sh
```

> **On Windows this straddles two operating systems.** The build is an ELF binary inside WSL and mCRL2 is a Windows install, so `scripts/check.sh` runs from Git Bash and reaches the translator through `wsl`; on Linux or macOS nothing special happens.

## The files

The chain of [`Plan.md`](../docs/Plan.md) §2, left to right. Every file has a counterpart of the
same name in [`Implementation/Lean/Cpn2mCrl2/`](../Lean/Cpn2mCrl2) and
[`Implementation/Dafny/src/`](../Dafny/src), so the three can be read side by side.

| File | What it holds | Lines |
| --- | --- | --- |
| [`lib/util.ml`](lib/util.ml) | duplicate removal, association lookup, sorting by key | 39 |
| [`lib/color.ml`](lib/color.ml) | the color grammar of [`InputFormat.md`](../docs/InputFormat.md) §4.1, and values | 54 |
| [`lib/bag.ml`](lib/bag.ml) | Definition 1, finitely supported | 30 |
| [`lib/list_ops.ml`](lib/list_ops.ml) | lists as bags: the multiset operations | 28 |
| [`lib/expr.ml`](lib/expr.ml) | `EXPR`, with `sort_of` inferring rather than indexing | 245 |
| [`lib/net.ml`](lib/net.ml) | Definitions 4 and 5, and the T1 validation | 111 |
| [`lib/semantics.ml`](lib/semantics.ml) | Definitions 6 and 7 — the reference side | 45 |
| [`lib/lpe.ml`](lib/lpe.ml) | Definition 13, as data | 25 |
| [`lib/translate.ml`](lib/translate.ml) | Definition 14 | 55 |
| [`lib/list_encoding.ml`](lib/list_encoding.ml) | the second backend | 86 |
| [`lib/print.ml`](lib/print.ml) | the mCRL2 encoding of [`Target.md`](../docs/Target.md) §1 | 181 |
| [`lib/print_list.ml`](lib/print_list.ml) | the same for the list encoding | 78 |
| [`lib/import.ml`](lib/import.ml) | the importer — **outside the trust boundary** | 449 |
| [`bin/main.ml`](bin/main.ml) | the command line | 33 |

1459 lines, against Lean's 2670 and Dafny's 3517 — but those two carry their proofs and this one
carries none, so the comparison that means anything is in [`Notes.md`](Notes.md).

## What is established, and how

Not by proof. By agreement and by the toolset.

**All six emitted specifications — three fixtures, two encodings — are byte-identical to the
ones [`Implementation/Lean/`](../Lean/README.md) and [`Implementation/Dafny/`](../Dafny/README.md)
emit.** Three translators, no shared code, written against [`Implementation/docs/`](../docs)
rather than against each other, agreeing down to the parenthesization of `((p1 - {h: 1}) + {:})`.

That is worth being exact about. Two of those three are *proved* to emit a term denoting the
$c_t$ and $g_t$ of Definition 14. This one is not, and agreeing with them does not make it so —
it makes it very unlikely to differ from them by accident. What the agreement buys is the other
direction: it is evidence about *them*, because a third independent reading of the same
specification produced the same bytes.

`scripts/check.sh` is green on every fixture in both encodings: `mcrl22lps` accepts the text
(T0), the linearized process has the expected shape, the LTS is strongly bisimilar to the
recorded one (T4), the two encodings are bisimilar to each other, and every fixture under
`fixtures/rejected/` is refused with the name of the check that failed.

## What is not here

**The proofs**, which is the point. [`Notes.md`](Notes.md) records what Cameleer accepts, what
rewriting the core into that fragment cost, and — so that the decision is reversible if the
tooling improves — what finishing the proofs would take.

**The composition with Theorem 1**, for the same reason it is absent from
[`Implementation/Dafny/`](../Dafny/README.md): Theorem 1 is a Lean term.

**T0 and T4 remain tested, never proved**, which is the ceiling
[`Plan.md`](../docs/Plan.md) §2 sets for all three translators.

**Importers.** Only the native format of [`InputFormat.md`](../docs/InputFormat.md) §4 is read
here; PNML goes through [`Implementation/tools/`](../tools/README.md).

## Sources

- N. van Uden, *Model checking for analysis of BPMN models*, Master Thesis Report, Eindhoven
  University of Technology, April 2025.
- M. Pereira and A. Ravara, *Cameleer: a Deductive Verification Tool for OCaml*, CAV 2021.
  [arxiv.org/abs/2104.11050](https://arxiv.org/abs/2104.11050)
- GOSPEL. [github.com/ocaml-gospel/gospel](https://github.com/ocaml-gospel/gospel)
- Why3. [why3.lri.fr](https://why3.lri.fr/)
- mCRL2 toolset 202307.1. [mcrl2.org](https://www.mcrl2.org/)
