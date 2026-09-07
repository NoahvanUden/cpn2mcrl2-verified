# What Cameleer accepts, and what the three-way comparison showed

The measurement milestone M5 exists to produce: which OCaml a deductive verifier will read,
and what three implementations of one specification cost. Background to
[`README.md`](README.md); nothing here is needed to build or run the translator.

---

## What Cameleer accepts

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

### Installing it

Also a finding, and the first one. `cameleer` is **not in the opam repository**, so it comes
from a git pin; the `gospel` commit that pin requires does not compile against `cmdliner` 2.x,
which removed the `Arg.conv` tuple API. Forcing `cmdliner.1.3.0` fixes it. It then pulls in
`why3-ide`, and so GTK development headers, for a tool that is only ever run on the command
line.

---

## What the three-way comparison showed

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

### Size

| | Lean | Dafny | OCaml |
| --- | --- | --- | --- |
| Lines of code, excluding comments and blanks | 2670 | 3517 | 1459 |
| Proved | T1, T2, T5, and T3 by composition | T1, T2, T5 | nothing |

The third column is short because it is empty of proof, not because OCaml is concise. The
honest reading of this table is that it does not compare three verified developments; it
compares two verified developments and a program.

---

---

## What would be needed to finish the proofs

Recorded so that the decision is reversible rather than forgotten. In order: fully qualify the
ten core modules and concatenate them into one file; restructure `color_eq`, `value_of_color`,
`sort_of`, `eval` and `free_vars` so that their recursion is either structural or explicitly
mutual with a lexicographic variant; give every recursive function a `variant`; then write the
GOSPEL specification layer and the T1, T2 and T5 proofs. The first three steps are known work
of known size. The fourth is not, and it is the one that would decide whether Alt-Ergo can do
in Why3 what Z3 did in Dafny.

The reason for stopping before it is that the answer would confirm obligation 4 a fourth time
and would not change anything in [the comparison above](#what-the-three-way-comparison-showed).
