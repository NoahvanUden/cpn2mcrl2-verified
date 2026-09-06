# Translator #3, OCaml — and why it is not verified

Milestone **M5** of [`Implementation/docs/Plan.md`](../docs/Plan.md), closed as a negative
result. A Colored Petri Net goes in as a file and an mCRL2 specification comes out as text,
in both encodings, byte for byte the same as the other two translators emit. **Nothing about
it is proved.**

That is not where M5 was meant to land, and the reason it landed there is the finding.
[`Languages.md`](../docs/Languages.md) §3 picks OCaml third for one specific reason:

> Idiomatic OCaml is the natural language for a tree-to-tree translator, and Cameleer verifies GOSPEL-annotated OCaml by translating it to WhyML — where it works, you get verified code that is also code somebody would have written anyway, which neither Lean nor Dafny quite gives you.

The translator below is code somebody would have written anyway. Cameleer cannot read it.
[§4](#4-what-cameleer-accepts) is the measurement, and it is the only part of this package
that is worth reading if you are choosing a verification stack.

---

## 1. Running it

OCaml 4.14 and dune. The translator itself needs nothing else; `yojson` is used only by the
importer, which is outside the trust boundary.

```bash
cd Implementation/OCaml
dune build
./_build/default/bin/main.exe fixtures/counter.cpn.json
```

That fixture is Example 3, and the output is Example 9:

```
act t1, t2, t3;

proc Spec(p1 : Bag(Int), p2 : Bag(Int), p3 : Bag(Int)) =
    sum h : Int . (({h: 1} <= p1) && true) -> t1 . Spec(((p1 - {h: 1}) + {:}), ((p2 - {:}) + {(h + 1): 1}), ((p3 - {:}) + {:}))
  + sum h : Int . (({h: 1} <= p2) && (h <= 3)) -> t2 . Spec(((p1 - {:}) + {h: 1}), ((p2 - {h: 1}) + {:}), ((p3 - {:}) + {:}))
  + sum h : Int . (({h: 1} <= p2) && (3 < h)) -> t3 . Spec(((p1 - {:}) + {:}), ((p2 - {h: 1}) + {:}), ((p3 - {:}) + {h: 1}));

init Spec({1: 1}, {:}, {:});
```

`--list` selects the second backend, one `List` per place instead of one `Bag`.

The harness of [`Target.md`](../docs/Target.md) §4 needs mCRL2 on the machine and picks up
the Lean and Dafny binaries for the differential test if they are built:

```bash
bash scripts/check.sh
```

> **On Windows this straddles two operating systems.** The build is an ELF binary inside WSL and mCRL2 is a Windows install, so `scripts/check.sh` runs from Git Bash and reaches the translator through `wsl`; on Linux or macOS nothing special happens.

---

## 2. The files

The chain of [`Plan.md`](../docs/Plan.md) §2, left to right. Every file has a counterpart of
the same name in [`Implementation/Lean/Cpn2mCrl2/`](../Lean/Cpn2mCrl2) and
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

1459 lines, against Lean's 2670 and Dafny's 3517 — but those two carry their proofs and this
one carries none, so the comparison that means anything is
[§5](#5-what-the-three-way-comparison-showed).

---

## 3. What is established, and how

Not by proof. By agreement and by the toolset.

**All six emitted specifications — three fixtures, two encodings — are byte-identical to the
ones [`Implementation/Lean/`](../Lean) and [`Implementation/Dafny/`](../Dafny) emit.** Three
translators, no shared code, written against [`Implementation/docs/`](../docs) rather than
against each other, agreeing down to the parenthesization of `((p1 - {h: 1}) + {:})`.
`scripts/check.sh` rechecks it on every run.

That is worth being exact about. Two of those three translators are *proved* to emit a term
denoting the $c_t$ and $g_t$ of Definition 14. This one is not, and agreeing with them does
not make it so — it makes it very unlikely to differ from them by accident. What the
agreement does buy is the other direction: it is evidence about *them*, because a third
independent reading of the same specification produced the same bytes.

`scripts/check.sh` is green on every fixture, in both encodings: `mcrl22lps` accepts the text
(T0), the linearized process has |T|+1 summands and |P| parameters, the LTS is strongly
bisimilar to the recorded golden one (T4), the two encodings are bisimilar to each other, and
every fixture under `fixtures/rejected/` is refused with the name of the check that failed.
[`Target.md`](../docs/Target.md) §4.1's prediction shows up a third time: on
`multitoken.cpn.json` and `jobs.cpn.json` the bag encoding gives four states and the list
encoding five, and `ltscompare -ebisim` reports them equal anyway.

---

## 4. What Cameleer accepts

Found by testing, one construct at a time, because none of it is written down. Cameleer 0.1
against Why3 1.8.2, Alt-Ergo 2.6.3 and Z3 4.16.

| | |
| --- | --- |
| `=` in program code | **`int` only.** Not strings, not booleans, not user datatypes |
| `List.for_all`, `List.concat_map`, `List.find_opt`, `Option.map`, `List.stable_sort`, `String.concat` | unknown symbols |
| `List.mem`, `List.map`, `List.filter`, `@`, `^`, `String.equal` | fine |
| records, options, pattern matching, `let rec` | fine |
| `when` guards | "Guarded expressions are not supported" |
| `include` | "Include expressions are not supported yet" |
| a reference to another file | unbound symbol — **it verifies one file at a time** |
| `open` on a module in that same file | read as a *Why3 library* import, so unresolvable |
| every recursive function | needs an explicit `variant` |

Two of those are structural rather than cosmetic:

**Termination through a nested list cannot be discharged naively.** `color_eq` recursing into
`(string * color) list` and back generates a variant-decrease goal that Alt-Ergo cannot close
without a lexicographic measure across the mutual pair. This is the same wall Lean and Dafny
hit at the same place, for two other reasons — Lean derives neither `DecidableEq` nor a usable
recursor for a nested `List (String × Color)`, and Dafny gives the elements of a bare `seq` no
rank below the sequence. **All three tools reject the natural definition of a record color,
each for a different reason.** That the OCaml compiler accepts it is not the same thing, and
this package is where that distinction became visible.

**A recursive call inside a higher-order function cannot be given a variant at all.**
`free_vars` calling itself under `flat_map` is not something Why3 can justify, because
`flat_map`'s specification would have to say "calls `f` only on elements of `l`", which GOSPEL
cannot express for a general function argument. It has to be rewritten into explicit mutual
recursion. Neither Lean nor Dafny ever tempted anyone into this shape, so it is the one
obstacle that is specific to writing the translator the way OCaml is written.

### 4.1 Installing it

Also a finding, and the first one. `cameleer` is **not in the opam repository**, so it comes
from a git pin; the `gospel` commit that pin requires does not compile against `cmdliner` 2.x,
which removed the `Arg.conv` tuple API. Forcing `cmdliner.1.3.0` fixes it. It then pulls in
`why3-ide`, and so GTK development headers, for a tool that is only ever run on the command
line.

---

## 5. What the three-way comparison showed

[`Languages.md`](../docs/Languages.md) §5 says what building the translator more than once is
for:

> which parts of [`Plan.md`](../docs/Plan.md) §4's five obligations does each technology make free, and which does it make expensive?

| # | Obligation | Lean | Dafny | OCaml + Cameleer |
| --- | --- | --- | --- | --- |
| 1 | Sorts gain products, for $D$ and $H_t$ | Not needed | Not needed | Not needed |
| 2 | The Definition 14 operations join the language | Mechanical | Mechanical | Mechanical |
| 3 | The bounded quantifier unfolded at translation time | Mechanical | Mechanical | Mechanical |
| 4 | A substitution lemma | One structural induction | Every case closed by Z3 with no hint | **not reached** |
| 5 | `toLPE_cond` stops being `rfl` | Follows from 2 and 4 | Follows from 2 and 4 | **not reached** |

The plan's question is answered, and it was answered before this package existed. Obligations
1 to 3 are free everywhere, so the automation had nothing to give away; obligation 4 — the one
[`Plan.md`](../docs/Plan.md) §7 rates the project's high risk — cost nothing in Lean, nothing
in Dafny, and nothing in [`Proof/`](../../Proof) at milestone M2, where it is discharged for an
*arbitrary* expression language. Three confirmations, all for the same reason: scoping is
extrinsic, so moving an arc expression into the summand's context is a different restriction of
the same binding rather than a re-indexing of the term.

**The question this package was for is a different one, and it has an answer.**
[`LeanFormalization.md`](../../Thesis/docs/LeanFormalization.md) and
[`Languages.md`](../docs/Languages.md) §5.1 put it as: can the verified artifact also be code
somebody would have written anyway? Measured here: **no, and here is the bill.**

Writing this translator into Cameleer's fragment — commit `30dd240`, since reverted so that the
shipped code is the version a reader would recognise as OCaml — took **+280/−106 lines across
eight files**, and none of it bought a single proof. What it bought was the right to be parsed:

- Every compared type gains a hand-written decidable equality: `string_eq`, `bool_eq`,
  `color_eq`, `value_eq`, `expr_ty_eq`, `denot_eq`, and the option and list liftings of each.
  **This is exactly what Lean derives with `deriving DecidableEq` and Dafny gives away with
  `(==)` on any datatype.** 113 comparison sites.
- `Util` goes from 39 lines to 80, putting back the `for_all`, `find` and `concat_map` that the
  standard library had made unnecessary. It is worth naming the three reasons side by side:
  Lean writes them out to keep Mathlib outside the trust boundary, Dafny because a proof has to
  unfold the definition it is about, and Cameleer because it has never heard of them. Three
  languages, three unrelated reasons, one outcome.
- The ten core modules have to become one file with no `open`, so the module system is not
  available to the verified part.

The **shape** of the code is what the verifier costs, and the shape is the thing OCaml was
picked for. That is the result.

### 5.1 Size

| | Lean | Dafny | OCaml |
| --- | --- | --- | --- |
| Lines of code, excluding comments and blanks | 2670 | 3517 | 1459 |
| Proved | T1, T2, T5, and T3 by composition | T1, T2, T5 | nothing |

The third column is short because it is empty of proof, not because OCaml is concise. The
honest reading of this table is that it does not compare three verified developments; it
compares two verified developments and a program.

---

## 6. What is not here

**Every proof.** [`Plan.md`](../docs/Plan.md) §6.1 records M5 as done and unverified for that
reason, and §6.2 there records the proofs as closed rather than pending. `semantics.ml` exists
so that the T2 statement would have a left-hand side, and it has no right-hand side to be
equated with.

**The composition with Theorem 1**, for the same reason it is absent from
[`Implementation/Dafny/`](../Dafny): Theorem 1 is a Lean term.

**T0 and T4 remain tested, never proved**, which is the ceiling
[`Plan.md`](../docs/Plan.md) §2 sets for all three translators.

**Importers.** Only the native format of [`InputFormat.md`](../docs/InputFormat.md) §4 is read.
PNML and the Model Checking Contest corpus are M7.

### 6.1 What would be needed to finish it

Recorded so that the decision is reversible rather than forgotten. In order: fully qualify the
ten core modules and concatenate them into one file; restructure `color_eq`, `value_of_color`,
`sort_of`, `eval` and `free_vars` so that their recursion is either structural or explicitly
mutual with a lexicographic variant; give every recursive function a `variant`; then write the
GOSPEL specification layer and the T1, T2 and T5 proofs. The first three steps are known work
of known size. The fourth is not, and it is the one that would decide whether Alt-Ergo can do
in Why3 what Z3 did in Dafny.

The reason for stopping before it is that the answer would confirm obligation 4 a fourth time
and would not change anything in [§5](#5-what-the-three-way-comparison-showed).

---

## 7. Sources

- N. van Uden, *Model checking for analysis of BPMN models*, Master Thesis Report, Eindhoven
  University of Technology, April 2025.
- M. Pereira and A. Ravara, *Cameleer: a Deductive Verification Tool for OCaml*, CAV 2021.
  [arxiv.org/abs/2104.11050](https://arxiv.org/abs/2104.11050)
- GOSPEL. [github.com/ocaml-gospel/gospel](https://github.com/ocaml-gospel/gospel)
- Why3. [why3.lri.fr](https://why3.lri.fr/)
- mCRL2 toolset 202307.1. [mcrl2.org](https://www.mcrl2.org/)
