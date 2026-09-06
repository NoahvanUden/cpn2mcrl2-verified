# The oracle

What an external reachability-graph generator has to provide, how it is plugged in, and which
tool to reach for when the current one does not fit.

---

## 1. The one property that matters

An oracle is useful here exactly to the extent that **it was not written by us and not written
for this**. Its semantics were fixed before this project existed, by people who never read the
thesis, which is what lets it contradict
[`Implementation/docs/`](../../Implementation/docs) rather than merely re-state it.

Everything else about it — language, licence, speed, ergonomics — is negotiable. That property is
not. A convenience that quietly compromises it (patching the tool's firing rule to match ours,
say, or computing enabling on our side and asking the tool only to apply it) turns the oracle back
into a mirror, and the test stops meaning anything while continuing to pass.

---

## 2. The contract

An oracle adapter is a program. Given one corpus net, it writes two files and exits with a status.

### 2.1 Input

The corpus net, in the corpus's canonical format. [`Plan.md`](Plan.md) §3 wanted that to be
PNML, so that both sides would read one file independently; [§3.2](#32-the-record) settled it
the other way, so it is the native JSON of
[`InputFormat.md`](../../Implementation/docs/InputFormat.md) §4. The adapter is allowed to read
only that file.

### 2.2 Output: `<name>.oracle.aut`

The reachability graph of Definition 9, in Aldebaran format, which is what `ltscompare` reads:

```
des (0,6,7)
(0,"t1",1)
(1,"t2",2)
```

The header is `des (first-state, transitions, states)`. Three requirements:

1. **State 0 is the initial marking.** `.aut` fixes the initial state as the first field of the
   header, and the existing goldens use 0.
2. **Edge labels are bare transition names.** The binding is erased, per
   [`Plan.md`](Plan.md) §2.1. Two edges that differ only in binding become parallel edges with
   the same label, which is correct and is the limit being accepted.
3. **State numbering is arbitrary.** `ltscompare -ebisim` does not care, and the comparison must
   not depend on it.

### 2.3 Output: `<name>.oracle.markings`

Optional, and worth a lot when it is available: one line per state, mapping the state number used
in the `.aut` to the marking it stands for.

```
0  p1={a^1} p2={}
1  p1={} p2={a^1}
```

`value^count`, sorted by value, places sorted by name.

This is what feeds leg B2 of [`Plan.md`](Plan.md) §6.2, where the same information is recovered
from the mCRL2 side with `lps2lts -ofsm`. The two notations will not match textually — one is the
oracle's, the other is mCRL2's `{1: 1}` — so the comparison normalises both into a canonical form
(sorted place names, sorted colour-count pairs) before comparing. That normaliser is the one piece
of the harness that touches semantics, and it should be kept to sorting and nothing else.

An adapter that cannot produce this file is still usable; it costs leg B2, which is stated in the
report rather than skipped silently.

### 2.4 Exit status

| Status | Meaning | How the harness treats it |
| --- | --- | --- |
| `0` | ok | Compare |
| `2` | unsupported construct — the net uses something the oracle cannot express | Not a failure. Recorded, and counted; a rising count is a finding about the oracle |
| `3` | state cap exceeded | Not a verdict. The net is reported as uncompared and belongs in a smaller tier |
| other | the adapter itself failed | Failure |

Statuses 2 and 3 are why the corpus tiers exist. Neither is a red build, and neither may be
reported as a pass.

---

## 3. SNAKES, the first candidate

[SNAKES](https://snakes.ibisc.univ-evry.fr/) is a Python library for high-level Petri nets by
Franck Pommereau, with tokens as arbitrary Python values, an explicit `StateGraph` construction,
and a long history of use in teaching and research. It is the first candidate because it is
independent, mature, scriptable, and its state-graph construction is a documented part of the
library rather than something to be built on top of it.

### 3.1 What the E1 spike must answer

In order, cheapest first. Stop at the first "no" and consult [§4](#4-if-it-does-not-fit).

1. **Does it install and run?** Python 3.12 is what is on this machine, and SNAKES predates it by
   a long way. If it needs an older interpreter, that is a packaging problem and not a
   disqualification — a pinned interpreter is acceptable, an unmaintained fork is not.
2. **Can it read the corpus format?** SNAKES has PNML support, but the question is whether that is
   *standard* PNML or a SNAKES-specific serialisation of Python objects. This is the fact that
   decides the architecture of [`Plan.md`](Plan.md) §3, and it should be settled by reading one
   file it writes, not from documentation.
3. **Multiple tokens on one arc.** Definition 5's arcs are bag-valued. SNAKES has `MultiArc`; the
   question is whether an arc can carry a bag of *distinct* values, which `multitoken` needs.
4. **A colour set per place.** Definition 5 gives each place a colour set and requires
   $E(p,t)$ to land in it. SNAKES types places with a checker rather than a colour set; how close
   that is to Definition 5 is a finding worth writing down either way.
5. **Enabling and firing.** Does its binding search agree with Definitions 6 to 8 on a net where
   one transition has two in-arcs sharing a variable? This is the semantic core, and the tier-1
   net that exercises it is `shared-var` in [`Corpus.md`](Corpus.md) §2.
6. **State graph out.** `StateGraph` enumerated into `.aut`, and markings into
   `.oracle.markings`.

### 3.2 The record

SNAKES 0.9.33, Python 3.12, in `Tests/.venv`. **It is the oracle**, and it answered the six
questions of §3.1 as follows.

**1. It installs and runs.** `pip install snakes` builds a wheel on Python 3.12 without a
patch, despite the library predating it by a decade.

**2. Its PNML is its own, and this is the finding that decided the architecture.** Asked to
serialise a two-place net, it writes

```xml
<pnml>
 <net id="onestep">
  <place id="p1">
   <type domain="universal"/>
   <initialMarking><multiset><item><value>
     <object type="str">a</object>
   </value><multiplicity>1</multiplicity></item></multiset></initialMarking>
```

with no `xmlns`, no `<page>`, no `<declarations>`, and Python objects where ISO/IEC 15909-2 has
sort declarations. That is a serialisation of SNAKES' own data structures, not the interchange
format, so the two sides cannot read one corpus file. **The corpus is native JSON and the
adapter builds the net**, which is the fallback [`Plan.md`](Plan.md) §3 names.

**3. Multiple tokens on one arc: yes.** `MultiArc([Value('a'), Value('b')])` consumes both in a
single firing, and `MultiArc` of two copies of one value handles a multiplicity above one.

**4. A colour set per place: not really, and it does not matter here.** SNAKES types a place
with a `check` predicate rather than with a colour set, so Definition 5's $C(p)$ has no direct
counterpart. The adapter therefore leaves places untyped and lets the *net* constrain what
reaches them, which is sound because the T1 validation has already established
$\mathrm{Type}[E(a)] = C(p)_{\mathrm{MS}}$ before the oracle ever sees the net. The oracle
consequently cannot catch a colour error, and it is not asked to: that is leg D's job.

**5. Enabling and firing agree with Definitions 6 to 8** on every shape tier 1 exercises,
including `shared-var`, where one variable is constrained by two in-arcs at once and only the
colour held by both places may fire.

**6. The state graph comes out.** `StateGraph.build()`, then `successors()` per state, yields
`(target, transition, substitution)` — exactly the contract, with the substitution to be
discarded.

**One divergence worth writing down, which the corpus stays clear of.** SNAKES binds variables
by matching tokens present in the input places, where Definition 6 quantifies over *all*
bindings of $\mathrm{Var}(t)$. The two agree whenever every variable of a transition occurs in
some in-arc expression, which is every net here. A variable appearing only in a guard or only
on an out-arc would be enumerated by Definition 6 and unbindable by SNAKES — so a net like that
is outside what this oracle can judge, and would have to be reported as unsupported rather than
compared.

---

## 4. If it does not fit

In order. Each entry says what it buys and what it gives up; the ordering is by how much
independence survives.

**1. A different high-level Petri net tool.** CPN Tools and its `ASAP`/state-space tools compute
state spaces for CPN ML nets, and are the closest thing to the formalism the thesis is written in
— its Definition 5 is essentially a CPN Tools net. The cost is automation: it is a GUI tool, and
driving it in a harness is the hard part. Worth trying second precisely because it is the most
faithful, and worth trying manually on two or three tier-1 nets even if it never gets automated,
because a handful of hand-checked results from the most faithful tool available is a real
anchor.

**2. A P/T unfolding plus a P/T state-space tool.** Unfold the coloured net over its finite colour
sets into an ordinary place/transition net, then use any of the many mature P/T tools (LoLA,
ITS-Tools, TINA) to build the reachability graph. This is attractive because tier 1 is *already*
finite by construction, so the unfolding is small, and because P/T tooling is far more automatable
than coloured tooling. What it gives up: the unfolding is a program we would write, so some
independence is lost — but strictly less than in a direct bridge, since the unfolding is a
standard construction that can be checked against a published definition, and the state-space
computation itself stays outside.

**3. Another coloured-net library.** Anything that reads standard PNML and enumerates a state
space qualifies; the Model Checking Contest tool set is the natural place to look, and E6 wants a
relationship with those tools anyway.

**4. An oracle written here, against Definitions 6 to 9.** The last resort. It shares this
project's reading of the definitions, so it cannot falsify a misreading — which is the main thing
the plan is for — and it must be labelled as internal wherever its numbers appear. It is still an
improvement on the status quo, because it replaces three hand-derived `.aut` files with a
computation, and because it is a fourth independent *implementation* even if it is not an
independent *reading*.

Falling to option 4 is a partial failure of this plan and should be recorded as one, in
[`Plan.md`](Plan.md) §7's E1 entry, rather than absorbed quietly.

---

## 5. Where the adapter lives

```
Tests/
  oracle/
    contract.md        -- pointer to this file; the adapter's own README
    adapters/
      snakes.py        -- candidate 1
      ...              -- one file per candidate, all satisfying section 2
    run.py             -- picks an adapter, enforces the cap, writes the two files
```

`run.py` is the only thing the harness calls, and it is the only file that knows an adapter exists.
Adding a candidate is a new file in `adapters/` and a line in `run.py`; it touches nothing in
`Tests/corpus/`, nothing in `Tests/scripts/`, and no document but this one.

---

## Sources

- SNAKES, a high-level Petri nets library in Python, by Franck Pommereau.
  [snakes.ibisc.univ-evry.fr](https://snakes.ibisc.univ-evry.fr/)
- CPN Tools, for CPN ML coloured nets and their state spaces. [cpntools.org](https://cpntools.org/)
- The Model Checking Contest, and the tools that compete in it. [mcc.lip6.fr](https://mcc.lip6.fr/)
- mCRL2 toolset 202307.1 — `ltscompare` reads the Aldebaran format this contract specifies.
  [mcrl2.org](https://www.mcrl2.org/)
- Definitions 5 to 9, transcribed in
  [`ColoredPetriNets.md`](../../Thesis/docs/ColoredPetriNets.md).
