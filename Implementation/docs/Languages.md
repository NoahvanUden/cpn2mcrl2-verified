# Choosing the languages

Which proof technology to build the translator in, and in what order.

---

## 1. What is actually being selected for

The obligations are fixed by [`Plan.md`](Plan.md) §4, and they are not the obligations a typical
verification exercise has. There are no loops, no aliasing, no concurrency and no resource
bounds. There is one recursive function over a tree, and one theorem saying that what it builds
*denotes* what Definition 14 says it should.

So the criteria are:

| # | Criterion | Why |
| --- | --- | --- |
| **C1** | Algebraic data types and pattern matching | The CPN and the LPE term are trees. Anything without them fights the problem |
| **C2** | A specification logic that can quantify over environments | Obligation 5 says "for every marking and every binding, the emitted term evaluates to `Enabled`". That is a statement about a function, not a value |
| **C3** | Automation for the mechanical obligations | Obligations 1 to 3 are structural bookkeeping and should not cost proof effort |
| **C4** | A real induction over expression syntax | Obligation 4, the substitution lemma, is where automation stops helping |
| **C5** | Produces a runnable binary | It is a translator, not a paper |
| **C6** | Continuity with [`Proof/`](../../Proof) | Definitions 1 to 18 and Theorem 1 already exist in Lean. Rebuilding them is pure cost |

C4 is the discriminator. Almost everything below satisfies C1, C2 and C5; the interesting
differences are how much of C3 a tool gives away for free and how painful C4 becomes when it
does.

---

## 2. The field

| Language | Specification | Proof style | Runs as | C4 | Verdict |
| --- | --- | --- | --- | --- | --- |
| **Lean 4** | Dependent types, Mathlib | Interactive, tactics | Native via C | Natural | **Pick — #1** |
| **Dafny** | Pre/post/invariants, ghost | Auto-active, SMT | C#, Java, Go, Python, JS | Explicit lemma functions | **Pick — #2** |
| **OCaml + GOSPEL/Cameleer** | GOSPEL contracts | SMT via Why3 | Native OCaml | Awkward but possible | **Picked — #3, and it did not carry it. See [§5.2](#52-the-answer-m5-gave-which-is-no)** |
| **F\*** | Dependent types + refinement | SMT with tactic fallback | Extracts to OCaml, F# | Natural | Best single fit, worst learning curve |
| **Why3 (WhyML)** | Contracts | Multi-prover SMT | Extracts to OCaml | Explicit lemmas | The fallback under #3 |
| **Rocq (Coq)** | Dependent types | Interactive | Extracts to OCaml | Natural | Duplicates Lean |
| **Isabelle/HOL** | HOL | Interactive, Isar, sledgehammer | Generates SML, OCaml, Haskell, Scala | Natural | Duplicates Lean |
| **Rust + Creusot** | Contracts | SMT via Why3 | Native | Possible | Friction on tree code |
| **Rust + Verus** | Contracts, `spec` fns | SMT | Native | Possible | Same |
| **OxCaml** | *none* | — | Native OCaml | n/a | **Not a verification language.** See [§4](#4-on-oxcaml) |
| **Agda, Idris 2** | Dependent types | Interactive | Weak backends | Natural | C5 is the problem |
| **SPARK/Ada, Liquid Haskell** | Contracts, refinement types | SMT | Native | Poor fit for C2 | Out |

---

## 3. The three to build

### #1 — Lean 4

The case is C6 and it is close to decisive. [`Proof/`](../../Proof) already contains Definitions
1 to 18, Theorem 1, and the six worked examples. Milestone M2 — making `LPE` syntactic, giving
`ExprLang` the Definition 14 operations with their evaluation equations, and turning
`toLPE_cond` from `rfl` into a theorem — **is a Lean change no matter which language the
translator is written in**, because that is where the definitions live. Once M2 is done, M3 is
mostly the printer plus a `main`.

> **That last sentence is wrong, and the order it assumes did not happen.** M3 was built first and does not depend on M2 at all: it fixes its own concrete expression language rather than changing `Proof/`'s abstract one, and the composition with Theorem 1 goes through a separate `Bridge/` package. M2's value is what it establishes for *every* expression language, not what it saves a translator. See [`Plan.md`](Plan.md) §6.1.

This is also the option that gets the strongest statement. In Lean the translator's correctness
theorem composes directly with `CPN.bisimulation_transRel`; nowhere else does it, and everywhere
else the composition has to be argued informally across a language boundary.

Cost: no SMT. Obligations 1 to 3 are mechanical but must still be written out, and C3 is
unsatisfied. Lean compiles to C and produces a native binary, so C5 is fine.

### #2 — Dafny

The reason to build it a second time in Dafny is not redundancy, it is the contrast. Dafny is
auto-active: you write the program with pre- and postconditions and Z3 discharges what it can.
On obligations 1 to 3 — structural, first-order, finitely many cases — that should be nearly
free, which is precisely where Lean is most tedious. Measuring *how much* of the translation SMT
gets for nothing is the most interesting result the multi-language exercise can produce.

Where it will hurt is C4. The substitution lemma is an induction over expression syntax, and in
Dafny that means writing an explicit recursive `lemma` and trusting the termination checker.
This is a well-worn Dafny idiom rather than a novelty, but it will be longer than it looks, and
the resulting proof will not connect to Theorem 1 except on paper.

C5 is a strength: Dafny compiles to several mainstream backends, so the verified translator can
be dropped into a Java or C# toolchain — which is what OfflineMBT is built in.

### #3 — OCaml, with GOSPEL and Cameleer

The practical one. Idiomatic OCaml is the natural language for a tree-to-tree translator, and
Cameleer verifies GOSPEL-annotated OCaml by translating it to WhyML and discharging the
obligations with SMT. Where it works, you get verified code that is also code somebody would
have written anyway — which neither Lean nor Dafny quite gives you.

The risk is maturity: Cameleer is a research tool still working toward a first release, and
GOSPEL itself is under active development. Two fallbacks, in order of preference:

1. Write the core in **WhyML** and extract to OCaml. Why3's extraction is mature and its
   multi-prover backend is a strength rather than a compromise.
2. Keep the OCaml unverified and rely on differential testing against the Lean binary from #1
   plus the `ltscompare` harness of [`Target.md`](Target.md) §4. Honest, and still useful.

**Write M1's unverified prototype in OCaml.** Then #3 is "add contracts to the prototype"
rather than a fourth implementation from scratch, and M1's output doubles as the differential
oracle for M3 and M4.

> **What happened instead.** M1 was skipped, so #3 started from nothing; the prototype got written at M5 and is [`Implementation/OCaml/`](../OCaml). The maturity risk named above materialised, and the fallback taken is the second one, not the first. But the obstacle was not the one this paragraph anticipates: the difficulty is not that Cameleer is unfinished around the edges, it is that the fragment of OCaml it reads excludes structural equality — so "add contracts to the prototype" is not a thing that can be done to a prototype somebody would have written. See [§5.2](#52-the-answer-m5-gave-which-is-no).

### The runner-up worth naming

**F\*** is arguably the best technical fit in the table: dependent types for C2 and C4, SMT for
C3, and extraction to OCaml for C5. It loses on C6 and on the cost of learning it. If the
exercise were about picking one language rather than comparing several, F\* would deserve a
serious look before Dafny.

---

## 4. On OxCaml

OxCaml is worth being precise about, because it is easy to file under "OCaml with extra
guarantees" and that is the wrong shelf.

OxCaml is Jane Street's open-sourced branch of OCaml. What it adds is **modes** — annotations
such as `local` and `unique` describing how a value may be used — a **kind** system for
specifying unboxed memory layouts, and mode-based tracking of concurrent use for data-race-free
parallelism. All three are type-system extensions aimed at performance and at safety properties
the *type checker* can enforce.

None of that is a specification logic. There is no way in OxCaml to state obligation 5 — that a
term denotes a particular function — let alone prove it. Against the criteria in
[§1](#1-what-is-actually-being-selected-for) it satisfies C1 and C5 and simply does not address
C2, C3 or C4.

That does not make it useless here. Two legitimate roles:

- **The fast unverified reference.** If M1's prototype needs to chew through the Model Checking
  Contest corpus at M7, OxCaml's unboxed types and stack allocation are exactly the right tool,
  and its mode system does buy real memory-safety and data-race guarantees for a parallel run.
- **The runtime for extracted code.** Why3 and Cameleer produce OCaml. If that OCaml is a
  bottleneck, OxCaml is where it goes.

Use it for speed, not for proof. The verified column stays Lean, Dafny and OCaml-with-contracts.

---

## 5. Order of work

| Milestone | Language | What it establishes | Status |
| --- | --- | --- | --- |
| M1 | OCaml, unverified | The output format is right, the harness is green, and there is an oracle | Skipped |
| M2 | Lean 4 | The syntactic `LPE`, and `toLPE_cond` as a theorem | Done, last |
| M3 | Lean 4 | Verified translator #1, composing with Theorem 1 | Done |
| M4 | Dafny | Verified translator #2 — how much SMT gives for free | Done |
| M5 | OCaml + GOSPEL/Cameleer | Verified translator #3 — verified code that is also idiomatic code | Translator done, verification abandoned |
| M7 | OxCaml, optional | Throughput for the corpus run | Not started |

The comparison that makes this worth doing three times is M3 against M4 against M5, on one
question: **which parts of [`Plan.md`](Plan.md) §4's five obligations does each technology make
free, and which does it make expensive?** Obligations 1 to 3 should separate the tools sharply.
Obligation 4 probably will not — it is a real induction in all three, and that is worth
confirming rather than assuming.

### 5.1 The answer, so far

Two of the three are built, and the answer they give is mostly negative.

**Obligations 1 to 3 did not separate the tools**, because there was nothing to separate.
Obligation 1 is not needed by anyone: Definition 13's tuple sorts are only ever bound, so no
product former is required in Lean, in Dafny, or in [`Proof/`](../../Proof). Obligations 2 and
3 are about twenty first-order cases, mechanical in both, and SMT had nothing to give away.

**Obligation 4 did not separate them either — and it is not an induction.** The prediction
above is half right. In all three developments the obligation costs nothing, and the reason is
not the one this page assumed: an expression is evaluated under a binding restricted to its own
free variables, so moving it into the summand's context is not a re-indexing. Scoping is
extrinsic in all three. Had any of them indexed terms by a typing context instead, the cost
would have been real — in *whichever* language.

**Where they did separate is not on [`Plan.md`](Plan.md) §4's list at all.** The T2 file is the
one file that is smaller in Dafny, 175 lines against Lean's 266, because Z3 needs none of the
`show` steps Lean needs to force definitional unfolding. Everything else that differs in size
measures the two standard libraries.
[`Implementation/Dafny/Notes.md`](../Dafny/Notes.md) has the numbers.

**What was left for M5 was therefore a different question.** "How much does the automation give
away" is answered. What OCaml with GOSPEL/Cameleer still tested is C5 in its strongest form:
whether the verified artifact can also be code somebody would have written anyway, which is the
one thing neither Lean nor Dafny delivers.

### 5.2 The answer M5 gave, which is no

[`Implementation/OCaml/`](../OCaml) is a third translator. It emits text byte-identical to both
others on every fixture in both encodings, and **nothing about it is proved**, because Cameleer
cannot read it.

The obstacles are listed in [`Implementation/OCaml/Notes.md`](../OCaml/Notes.md). Three of
them decide the question:

- **`=` in program code is `int` equality.** Not strings, not booleans, not user datatypes. So
  every compared type needs a hand-written decidable equality — which is precisely what Lean
  derives with `deriving DecidableEq` and Dafny gives away with `(==)` on any datatype. The one
  thing this table's §2 does not score, and the one that decided it.
- **Six of the standard-library functions the translator uses are unknown symbols**, so
  `List.for_all`, `List.concat_map` and `List.find_opt` come back as hand-written recursion.
- **It verifies one file at a time, and `open` on a module in that file is read as a Why3
  library import.** The verified part cannot use the module system.

Rewriting the core into the fragment Cameleer does accept cost +280/−106 lines and bought no
proof at all. That rewrite is the measurement: what it deletes is exactly the idiom that made
C1 and C5 worth scoring in the first place.

**The scoring in [§2](#2-the-field) was wrong about where the difficulty is.** C4 was named the
discriminator, on the assumption that obligation 4 would be a real induction everywhere. It is
free everywhere. What actually separates the three tools is a criterion this page does not
have: *how much of the language the prover can see.* Lean and Dafny verify the language they
compile. Cameleer verifies a fragment, and the fragment excludes structural equality — so in
OCaml, alone of the three, the verified program and the natural program are different programs.

One further data point, from before any of that. **Cameleer is not in the opam repository.** It
installs from a git pin whose `gospel` commit does not compile against `cmdliner` 2.x, and it
drags in `why3-ide` and GTK headers for a command-line tool. §3's "research tool still working
toward a first release" was accurate, and the risk table of
[`Plan.md`](Plan.md) §7 rated it correctly at Medium.

---

## 6. Sources

- Lean 4 and Mathlib. [lean-lang.org](https://lean-lang.org/) — and
  [`Proof/`](../../Proof) in this repository.
- Dafny. [dafny.org](https://dafny.org/)
- M. Pereira and A. Ravara, *Cameleer: a Deductive Verification Tool for OCaml*, CAV 2021.
  [arxiv.org/abs/2104.11050](https://arxiv.org/abs/2104.11050)
- *Static and Dynamic Verification of OCaml Programs: The Gospel Ecosystem*.
  [arxiv.org/pdf/2407.17289](https://arxiv.org/pdf/2407.17289)
- Why3. [why3.lri.fr](https://why3.lri.fr/)
- F\*. [fstar-lang.org](https://fstar-lang.org/)
- OxCaml documentation, on modes, kinds and unboxed types.
  [oxcaml.org/documentation](https://oxcaml.org/documentation/) — and Tarides,
  [*Introducing Jane Street's OxCaml Branch*](https://tarides.com/blog/2025-07-09-introducing-jane-street-s-oxcaml-branch/)
- Creusot and Verus, for Rust.
