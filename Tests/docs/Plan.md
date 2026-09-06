# The external validation plan

Testing the three translators against a reachability graph that nobody in this repository
computed.

---

## 1. Why an outside oracle

[`Implementation/`](../../Implementation/README.md) is checked today by two oracles, and both of
them are internal.

**Three translators agreeing byte for byte.** All six emitted specifications — three fixtures,
two encodings — are identical across the Lean, Dafny and OCaml developments. That is a strong
test of the *implementations*, and it is structurally blind to one thing: a shared misreading of
Definition 14. The three were written by one person from
[`Implementation/docs/`](../../Implementation/docs), so a document that says the wrong thing
produces three translators that say the same wrong thing and agree perfectly.

**The golden `.aut` files.** `Implementation/*/fixtures/counter.aut` is the corrected
seven-state chain of Example 5, so it has provenance outside this repository — the thesis.
`multitoken.aut` and `jobs.aut` do not: they were derived by hand and committed in the same
commit as the harness that checks them.

[`Target.md`](../../Implementation/docs/Target.md) §4 draws the check this project actually
wants:

```
   CPN fixture
        |
        +---- reference semantics (Definitions 6-9) ----> reachability graph  --> A.aut
        |
        +---- translator --> mCRL2 --mcrl22lps--> .lps --lps2lts--> B.aut
                                                                        |
                                     ltscompare -ebisim A.aut B.aut  <--+
```

The right-hand branch is automated and green. The left-hand branch is three hand-written files.
§4 there proposes filling it from the Lean's own semantics — which would make the two branches
share a reading of Definitions 6 to 9, and so would test the printer without testing the
reading.

**This directory fills the left branch from outside.** A third-party Petri net library computes
the reachability graph; its authors never read this thesis, and its semantics were fixed before
this project existed. That is the only oracle available that can contradict the documents rather
than the code.

---

## 2. What this can establish, and what it cannot

It proves nothing. Every guarantee here is a test, and its whole value is in what it could
*falsify*:

- **A shared misreading of Definition 14**, which byte-identity cannot see.
- **A native format whose meaning is idiosyncratic** — a net whose semantics under
  [`InputFormat.md`](../../Implementation/docs/InputFormat.md) §4 differ from what a standard CPN
  tool says the same net means. This tests the *documents*, not only the programs.
- **The two hand-derived goldens**, which have never been checked against anything.

In the tier vocabulary of [`Plan.md`](../../Implementation/docs/Plan.md) §2 this is a new row,
and it belongs to the branch no tier currently covers:

> **T6 (proposed).** The reachability graph the fixtures assert is the one an independent implementation of CPN semantics computes. Established by testing, never by proof.

Adding that row is bookkeeping for [E5](#e5--randomised-nets-and-the-bookkeeping), not something
to do in advance of the evidence.

### 2.1 The limit built into the comparison

Definition 14 emits actions with **no parameters** — the action is the bare transition name, and
[`mCRL2.md`](../../Thesis/docs/mCRL2.md) §1.3 records that parameters are reintroduced only where
a property needs data exposed. A CPN library's reachability graph labels each edge with a
transition *and the binding it fired under*.

So the oracle's graph must be relabelled before comparison: erase the binding, keep the
transition name. Two distinct oracle edges can then collapse into parallel identically labelled
edges, which the `.aut` format and bisimilarity both tolerate.

**The consequence is a real limit, and it belongs wherever results are reported: this comparison
cannot distinguish two bindings of the same transition.** A translation that fired the right
transitions under the wrong bindings would pass.
[§6.2](#62-leg-b--the-oracle) recovers most of it on the bag encoding, by comparing markings
rather than only behaviour.

---

## 3. M7 comes first, and it changes the architecture

[`Plan.md`](../../Implementation/docs/Plan.md) §6 has M7 as "PNML importers, and the Model
Checking Contest corpus as a test set", and §6.2 records it as the only open milestone. It is
scheduled first here, and not only because it is outstanding.

**Without M7**, the corpus is written in the native JSON and something has to build the oracle's
net from it. That something is a program in this repository, written by the same person, sitting
*inside* the trust boundary of the test. A bug in it that mirrors a misreading in the translators
produces a false pass, which is the expensive failure mode.

**With M7**, the corpus is written in PNML and both sides read it independently: the oracle
because PNML is an interchange format it already supports, the translators through M7's importer.
The bridge leaves the test's trust boundary, because nothing that reads the corpus was written to
serve this comparison.

```
                      corpus net (PNML)
                     /                 \
     M7 importer (unverified)        oracle reads PNML directly
              |                              |
       native CPN JSON                 marking graph
              |                              |
      three translators              relabel (t,b) |-> t
              |                              |
        six .mcrl2 files                oracle.aut
              |                              |
      mcrl22lps ; lps2lts  ------ ltscompare ------+
```

That shape depends on the chosen oracle reading *standard* PNML rather than a dialect of its own,
which is the first thing [E1](#e1--choose-the-oracle) measures. If it does not, the fallback in
[`Oracle.md`](Oracle.md) §4 applies and the corpus stays JSON. The plan does not stall on it.

### 3.1 What M7 has to deliver here

M7 is one line in the implementation plan. Executed, it is these five things.

1. **A dialect decision.** Coloured PNML means ISO/IEC 15909-2's high-level nets — Symmetric Nets,
   or HLPNG. [`InputFormat.md`](../../Implementation/docs/InputFormat.md) §2.3 already argues that
   Symmetric Nets are close to a formalizable expression language and that HLPNG adds precisely
   the integers Example 3 needs. Pick the smallest dialect covering
   [`Corpus.md`](Corpus.md) tier 1, and write down what was picked.
2. **One converter, not three.** The importer is outside the trust boundary, so it need not exist
   in each translator's language; the three keep their JSON importers unchanged. Its output is
   read by three independent readers, which is a better check on it than any test it could carry
   itself.
3. **Loud rejection.** Anything a PNML file expresses that
   [`InputFormat.md`](../../Implementation/docs/InputFormat.md) §4.1 cannot — user-defined
   functions, quantifiers, sorts outside `Bool`, `Int`, enumerations and records — is rejected by
   name, outside the trust boundary, per §3 there.
4. **A round trip on what already exists.** The three current fixtures, expressed in PNML, must
   import to JSON that the translators accept and emit the same six specifications, byte for byte.
   Until that holds, the importer is not trustworthy enough to build a corpus on.
5. **The measurement §2.3 asks for.** How much of the Model Checking Contest corpus falls inside
   the expression language, counted rather than assumed. That number decides whether
   [E6](#e6--the-corpus-at-scale) is worth running, and it is worth having either way.

---

## 4. The oracle is an interface, not a library

The most important design decision in this plan, and the one that keeps a hurdle from becoming a
blocker: **nothing downstream of the oracle knows which tool the oracle is.**

An oracle is anything that, given a corpus net, produces

- `<name>.oracle.aut` — an LTS in Aldebaran format, edges labelled with bare transition names;
- `<name>.oracle.markings` — optionally, a state-to-marking map, which enables the sharper check
  of [§6.2](#62-leg-b--the-oracle);
- an exit status distinguishing **ok**, **unsupported construct** and **state cap exceeded**.

SNAKES is the first candidate, because it is a mature, independent, scriptable Python library. It
is not the plan. [`Oracle.md`](Oracle.md) states the contract in full, records what the SNAKES
spike found, and lists the alternatives in the order to try them. Swapping the oracle changes one
adapter and no test, no corpus file, and no document but that one.

---

## 5. The corpus starts small, and finite

Full detail is in [`Corpus.md`](Corpus.md). Two rules govern it, and the first is the cheapest
defence against state-space explosion there is.

**Finite colours first.** Tier 1 is `Bool` and enumerations only. A place over a three-value
enumeration holding at most one token has four states; a net with three such places has at most
64 markings, whatever its transitions do. No cap, no timeout and no cleverness — the state space
is small because the colour sets are.

**`Int` is the hazard, and it arrives late.** The `counter` fixture is a seven-state chain only
because a guard bounds it. Integer colours enter at tier 3, always behind a bounding guard, and
never before tiers 1 and 2 are green.

Finite colours are necessary and not sufficient: a transition that produces without consuming
makes the marking set infinite over any colour set. Tier 1 nets are therefore token-conserving or
bounded by construction, and the harness carries a state cap regardless, reported as an outcome
rather than a hang.

---

## 6. The comparison

Four legs. A and C exist today inside the three `scripts/check.sh`; the plan adds B and D and puts
all four behind one command.

### 6.1 Leg A — the three translators agree

Byte-identity of all six emitted specifications. Implemented per-directory today; the harness runs
it *across* directories, which is where it has teeth.

```bash
cmp Implementation/Lean/out/counter.mcrl2 Implementation/Dafny/out/counter.mcrl2
```

### 6.2 Leg B — the oracle

`ltscompare -ebisim` between the oracle's graph and each translator's, in both encodings.

```bash
mcrl22lps -q out/net.mcrl2 out/net.lps
lps2lts   -q out/net.lps   out/net.aut
ltscompare -ebisim Tests/out/net.oracle.aut out/net.aut
```

**B2, markings and not only behaviour.** For the bag encoding the process parameters *are* the
marking, so the correspondence with a marking graph ought to be an isomorphism, and settling for
bisimilarity throws that away. `ltscompare` has no isomorphism equivalence, but `lps2lts -ofsm`
writes the parameter values per state — this is the real output for the `counter` fixture:

```
p1_Spec(4) Bag(Int)  "{1: 1}" "{:}" "{2: 1}" "{3: 1}"
p2_Spec(4) Bag(Int)  "{:}" "{2: 1}" "{3: 1}" "{4: 1}"
p3_Spec(2) Bag(Int)  "{:}" "{4: 1}"
```

Each state line then indexes into those tables, so every state's marking is recoverable as text.
Comparing that against the oracle's markings is strictly sharper than bisimilarity, and it is what
recovers most of the binding-blindness of
[§2.1](#21-the-limit-built-into-the-comparison): a transition fired under the wrong binding lands
in the wrong marking.

Grading: **markings must agree exactly for the bag encoding**; bisimilarity only for the list
encoding, where extra states are expected and proved harmless.

### 6.3 Leg C — the two encodings agree

`ltscompare -ebisim` between the bag and the list output, with both state counts reported.
Implemented today. The oracle anchors it: at present it says the two encodings agree with each
other, and after leg B it says they agree with something outside.

### 6.4 Leg D — the rejected corpus

Every net in `corpus/rejected/` violates a numbered check of
[`InputFormat.md`](../../Implementation/docs/InputFormat.md) §4.3 and must be refused by all three
translators, by name. Where the oracle can also detect the violation, a disagreement about *which*
nets are well-formed is itself a finding worth recording.

---

## 7. Milestones

Each carries a fallback, because the point of the sequencing is that no single hurdle stops the
plan.

| # | Milestone | Depends on | Exit criterion |
| --- | --- | --- | --- |
| **E0** | **M7**: the PNML importer, per [§3.1](#31-what-m7-has-to-deliver-here) | — | The three current fixtures round-trip through PNML to byte-identical output |
| **E1** | Choose the oracle: spike, contract, adapter | E0 | One tier-1 net, two graphs, one `ltscompare` verdict, by hand |
| **E2** | The tier-1 corpus: `Bool` and enumerations, small | E1 | Ten to fifteen nets, each with a hand-computed expected state count |
| **E3** | The harness: legs A to D, one command, CI-shaped | E2 | Green on tier 1, red when a net is deliberately broken |
| **E4** | The existing fixtures, and tier 2 | E3 | `counter`, `jobs` and `multitoken` pass leg B, or the disagreement is written down |
| **E5** | Randomised nets within §4.1, with shrinking | E4 | A generator, a seed corpus of survivors, and the T6 row added to `Plan.md` §2 |
| **E6** | The Model Checking Contest corpus at scale | E0, E5 | The §2.3 measurement, and a run over whatever falls inside the language |

### E0 — M7

Detailed in [§3.1](#31-what-m7-has-to-deliver-here). It is the only milestone here whose work
lands in [`Implementation/`](../../Implementation/README.md) rather than in this directory.

> **Fallback.** If coloured PNML proves too heavy to import in reasonable time, E0 narrows to the dialect tier 1 needs — enumerations and booleans, no integers, no records — and the rest waits for E6. The corpus is then PNML at tier 1 and JSON above it, which costs the plan nothing except that leg B's independence is weaker on the higher tiers, and that gets recorded rather than hidden.

### E1 — Choose the oracle

A timeboxed spike, not a commitment. Evaluate the leading candidate against the contract in
[`Oracle.md`](Oracle.md) §2 on exactly one net — the smallest tier-1 net, two places over one
enumeration and one transition. Produce its marking graph, relabel it, run `ltscompare` against a
translator's output by hand, and write down what the tool did.

The questions the spike answers, in order: does it read the corpus format; does it support several
tokens on one arc, and a colour set per place; can its marking graph be enumerated and exported;
does its notion of enabling and firing match Definitions 6 to 8; and does it install and run on
this machine at all.

> **Fallback.** [`Oracle.md`](Oracle.md) §4 lists the alternatives in order. If none fits, the last resort is an oracle written here directly against [`ColoredPetriNets.md`](../../Thesis/docs/ColoredPetriNets.md) Definitions 6 to 9 — a weaker oracle, because it shares this project's reading, and it must be labelled as such wherever its results appear. It is still worth more than the hand-derived goldens it replaces.

### E2 — The tier-1 corpus

Ten to fifteen nets over `Bool` and enumerations, each small enough to compute by hand, each
exercising one thing; [`Corpus.md`](Corpus.md) §2 enumerates them. The hand-computed state count
is committed next to the net, which gives the first few the same third, independent standing that
`counter.aut` has from the thesis.

> **Fallback.** If hand-computing a net's graph turns out to be error-prone, that net is too big for tier 1. Shrink it rather than trusting either machine.

### E3 — The harness

One script, four legs, per-net reporting in the style of the existing `scripts/check.sh`, and an
exit code. Deliberately breaking a net — flipping a guard, swapping an arc — must turn it red,
which is the only evidence that a green run means anything.

> **Fallback.** If driving three toolchains from one script proves awkward on Windows, the harness runs per-translator and a small aggregator compares the results. Nothing about the legs changes.

### E4 — The existing fixtures, and tier 2

`counter`, `jobs` and `multitoken` under leg B, plus tier 2: records, several in-arcs on one
transition, guards that block, and multi-token places over finite colours.

**A disagreement here is a result, not a defect to be fixed quickly.** If the oracle's graph
differs from the goldens, the finding is written down before anything is changed, and which side
is right is settled against
[`ColoredPetriNets.md`](../../Thesis/docs/ColoredPetriNets.md) Definitions 6 to 9 and the thesis,
not against whichever is more convenient.

> **Fallback.** If the oracle cannot express something tier 2 needs, that construct moves to a documented "not covered by the oracle" list — itself a measurement of how far a standard CPN tool is from Definition 5.

### E5 — Randomised nets, and the bookkeeping

Random small nets within [`InputFormat.md`](../../Implementation/docs/InputFormat.md) §4.1 over
finite colours, with a shrinker that reduces any failure to a minimal net. This is where an
external oracle earns its cost: hand-written fixtures test what their author thought of, and this
does not.

Bookkeeping in the same milestone: the T6 row into
[`Plan.md`](../../Implementation/docs/Plan.md) §2, a line into §6.2 there, and a pointer from the
root [`README.md`](../../README.md).

> **Fallback.** If generation produces mostly trivial or mostly unbounded nets, constrain it: fix the shape — places, transitions, arcs — and randomise only the annotations. A narrow generator that runs is worth more than a general one that does not.

### E6 — The corpus at scale

The prize [`InputFormat.md`](../../Implementation/docs/InputFormat.md) §2.3 names. Gated on the
measurement from E0: if very little of the Model Checking Contest corpus falls inside the
expression language, the honest outcome is to report that number and stop, which is a finding
about the language rather than a failure of the plan.

> **Fallback.** Run on the subset that fits, and report the size of the subset alongside every result.

---

## 8. Risks

| Risk | Severity | Mitigation |
| --- | --- | --- |
| The oracle's semantics differ from Definitions 6 to 9 in a legitimate way | High | Establish it on tier 1, where the graphs are hand-computable, before trusting it anywhere. A mismatch is a finding about both sides, not something to bridge silently |
| The bridge from corpus to oracle is written here, and could mirror our own misreading | High | E0 removes it where PNML allows. Where it survives it stays structurally dumb: it builds places, transitions and arcs, and never computes enabling, binding or firing |
| The chosen oracle turns out not to fit | Medium | The contract of [§4](#4-the-oracle-is-an-interface-not-a-library), and [`Oracle.md`](Oracle.md) §4's ordered alternatives |
| State-space explosion | Medium | Finite colours first, `Int` late and bounded, an explicit cap reported as an outcome |
| The binding-blindness of the label projection | Medium | Leg B2's marking comparison on the bag encoding |
| A new language and dependency, in a repository that needs only mCRL2 and three toolchains | Low | Confined to `Tests/`; the harness reports "oracle unavailable" rather than failing when it is absent |
| The plan ends up testing the importer rather than the translators | Low | E0's round-trip criterion: PNML in, byte-identical output, before any corpus is built on it |

---

## 9. What must not happen

**The oracle is never adjusted to agree with us.** When a comparison fails the possibilities are
that the translators are wrong, that the documents are wrong, that the bridge is wrong, or that
the oracle is wrong — in that order of interest. Editing the bridge until a test passes destroys
the only thing this directory is for, and does it silently.

**A disagreement is recorded before it is resolved.** The repository's convention is that a slip
is transcribed and marked rather than tidied away, and the same applies here. Findings from leg B
belong in writing, with the net that produced them committed to the corpus, whichever side turns
out to be at fault.

**No result is reported without its limit.** Every leg-B verdict carries the binding-blindness of
[§2.1](#21-the-limit-built-into-the-comparison), and a leg-B verdict on a net whose oracle graph
hit the state cap is not a verdict at all.

---

## Sources

- N. van Uden, *Model checking for analysis of BPMN models*, Master Thesis Report, Eindhoven
  University of Technology, April 2025. Definitions 5 to 9 and 14, and Theorem 1, are transcribed
  in [`Thesis/docs/`](../../Thesis/docs).
- mCRL2 toolset 202307.1 — `mcrl22lps`, `lps2lts`, `lpsinfo` and `ltscompare`.
  [mcrl2.org](https://www.mcrl2.org/)
- PNML, the Petri Net Markup Language, ISO/IEC 15909-2; its high-level dialects are Symmetric Nets
  and HLPNG.
- The Model Checking Contest, as a source of coloured models in PNML.
  [mcc.lip6.fr](https://mcc.lip6.fr/)
- Candidate oracles, with what each is and is not, in [`Oracle.md`](Oracle.md) §4.
