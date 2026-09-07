# The corpus

What to test on, in what order, and why the first tier is deliberately tiny.

---

## 1. Two rules

**Finite colours first.** Tier 1 uses `Bool` and enumerations and nothing else. This is the
cheapest defence against state-space explosion available: a place over a two-value enumeration
holding at most one token contributes three markings, and a net with three such places has at most
27, whatever its transitions do. There is no cap to tune and no timeout to wait out, because the
state space is small by construction.

**Finite is not the same as bounded.** A transition that produces without consuming makes the
marking set infinite over any colour set at all. Every tier-1 net is therefore token-conserving —
each transition produces exactly as many tokens as it consumes — or has a source that runs dry.
The harness still carries a state cap, because the rule is a discipline for authors and not
something the corpus format enforces.

`Int` is where both rules break, and it arrives in tier 3. The `counter` fixture is a seven-state
chain only because a guard bounds it.

---

## 2. Tier 1: thirteen nets

Each is small enough to compute by hand, and each exercises one thing. The expected counts are
committed next to the net and are the *third* check in the harness: the oracle and the translators
must agree with each other, and the first few must also agree with a number a person wrote down.

In the shapes below `1'a` is the thesis's ``1`a`` — one token of colour `a` — written with an
apostrophe so that the backtick does not have to be escaped in every cell.

| Net | Shape | States | Edges | What it is for |
| --- | --- | --- | --- | --- |
| `one-step` | `p1 -{1'h}-> t -{1'h}-> p2`, `p1 = {1'a}` | 2 | 1 | The smallest net that moves. The E1 spike net |
| `no-init` | the same, `p1` empty | 1 | 0 | Nothing is enabled; the LTS is one state and no edges |
| `dead` | the same, guard `False` | 1 | 0 | A summand that can never fire, and must still linearize |
| `guard-select` | `p1 = {1'a, 1'b}`, guard `h = a` | 2 | 1 | A guard that selects among bindings rather than blocking all of them |
| `shared-var` | two in-arcs, both `{1'h}`, from `p1 = {1'a, 1'b}` and `p2 = {1'a}` | 2 | 1 | One variable constrained by two arcs at once. **The net that decides whether the oracle's binding search agrees with Definitions 6 to 8** |
| `two-in` | in-arcs `{1'h}` from an enum place and `{1'b}` from a `Bool` place | 2 | 1 | Two in-arcs with *distinct* variables, as against `shared-var` |
| `conflict` | one token, two transitions consuming it | 3 | 2 | Branching. A translation that picked one arm would still be a chain |
| `independent` | two disjoint one-step nets in one file | 4 | 4 | Interleaving. A translation that serialised the two would give a chain, and bisimilarity would catch it |
| `two-tokens` | `p1 = {1'a, 1'b}`, one transition draining it into `p2` | 4 | 4 | The order problem of [`Plan.md`](../../Implementation/docs/Plan.md) §5, over finite colours. Expect **5** states under `--list` and bisimilarity anyway |
| `multiplicity` | arc expression `{2'a}`, `p1 = {2'a}` | 2 | 1 | A multiplicity above one, on both the arc and the marking |
| `multi-arc` | arc expression `{1'a, 1'b}`, `p1 = {1'a, 1'b}` | 2 | 1 | A bag-valued arc over *distinct* colours — question 3 of [`Oracle.md`](Oracle.md) §3.1 |
| `bool-flip` | `p -{1'h}-> t -{1'(!h)}-> p`, `p = {1'true}` | 2 | 2 | **A cycle.** Every golden in the repository today is acyclic — a chain and two diamonds — so this shape has never been tested |
| `enum-cycle` | three transitions, guards `h = a`, `h = b`, `h = c`, each producing the next | 3 | 3 | A longer cycle, and three summands, without needing a successor function the expression language does not have |

Two things to notice about that list.

**`shared-var` is the most valuable net in tier 1.** Everything else tests the translation; that
one tests whether the oracle means the same thing by "enabled" that
[`ColoredPetriNets.md`](../../Thesis/docs/ColoredPetriNets.md) Definitions 6 to 8 do. If the
oracle disagrees there, nothing further it says is usable, and it is better to find out on a
two-state net.

**`bool-flip` and `enum-cycle` cover a shape nothing in the repository covers.** `counter.aut` is
a chain, `jobs.aut` and `multitoken.aut` are diamonds. No fixture has ever had a cycle, and a
translation that got termination wrong — an off-by-one in the guard, a marking that fails to
close the loop — would pass every existing test.

### 2.1 Writing them

The expected counts belong in an `expected.tsv` next to the corpus, in the shape the existing
harness already reads, extended with the two new columns:

```
# net           summands  params  states  edges
one-step        2         2       2       1
two-tokens      2         2       4       4
```

`summands` is $|T| + 1$ and `params` is $|P|$, per
[`Target.md`](../../Implementation/docs/Target.md) §2 — if the linearized process does not have
those, what was emitted was not an LPE. `states` and `edges` are the hand-computed reachability
graph, and they are checked against *both* the oracle and the translators, which is what makes a
person's arithmetic a third opinion rather than a fourth guess.

---

## 3. Tier 2: still finite, no longer tiny

Added once tier 1 is green end to end. Same colour discipline — `Bool` and enumerations — and the
constructs [`InputFormat.md`](../../Implementation/docs/InputFormat.md) §4.1 offers that tier 1
leaves out:

- **Records and projection.** A place over `record(Job, [(id, E), (done, Bool)])`, a guard on
  `proj(h, done)`, an arc building a record from parts.
- **Several places in `pre(t)`,** which is what unfolds the bounded conjunction of
  [`Plan.md`](../../Implementation/docs/Plan.md) §4 obligation 3 into a wide finite conjunction.
- **Boolean connectives in guards**, so that the `&&`, `||` and `!` of §4.1 are exercised rather
  than assumed.
- **A place with three or four tokens**, which is where the list encoding's extra states multiply
  and the refinement of [`Plan.md`](../../Implementation/docs/Plan.md) §5 stops being a two-token
  observation.

Tier 2 nets are still expected to stay in the low hundreds of states. They are no longer
hand-computable, and that is the point at which the oracle stops being checkable and starts being
trusted — which is why tier 1 has to be green first.

---

## 4. Tier 3: the integers, and the fixtures that exist

`counter`, `jobs` and `multitoken` from
[`Implementation/*/fixtures/`](../../Implementation/Lean/fixtures), plus any new net using `Int`.

Every `Int` net must be bounded by a guard, and the bound stated in a comment in the net file. The
`counter` net is the model: it is finite only because `h <= 3` stops it.

Tier 3 is where a disagreement is most likely and most interesting, because `counter.aut` is the
one golden with outside provenance — it is Example 5's corrected chain from the thesis — so a
three-way disagreement between the thesis, the translators and the oracle would be worth a great
deal.

---

## 5. The rejected corpus

Leg D of [`Plan.md`](Plan.md) §6.4. One net per numbered check of
[`InputFormat.md`](../../Implementation/docs/InputFormat.md) §4.3, each of which must be refused by
all three translators, naming the check that failed:

| Check | Net | Violation |
| --- | --- | --- |
| 1 | `dangling-arc` | An out-arc naming a place that does not exist |
| 1 | `name-clash` | A place and a transition sharing a name |
| 2 | `undeclared-color` | A place typed with a colour the net never declares |
| 3 | `untyped-var` | A variable declared at a colour not in $\Sigma$ |
| 4 | `guard-not-bool` | A guard whose type is an enumeration |
| 5 | `badcolor` | An arc expression whose colour is not its place's — **exists today** |
| 6 | `openinit` | An initial marking with a free variable — **exists today** |
| 6 | `init-wrong-color` | An initial marking of the wrong colour |
| 7 | `undeclared-var` | An arc using a variable that is not in $V$ |
| — | `shadow` | A place and a variable sharing a name — `Net.Valid.namesDisjoint`, which is an *addition* to Definition 4 rather than one of the seven — **exists today** |
| — | `keyword` | `val` as an identifier, which is [`Target.md`](../../Implementation/docs/Target.md) §1 rather than a §4.3 check — **exists today** |
| 8 | `shared-ctor` | Two enumerations declaring a constructor of the same name — the check added after [`Findings.md`](Findings.md) §8 |

> **Corrected.** An earlier version of this table put `badcolor` at check 2, `shadow` at check 7, and did not distinguish `keyword` from the §4.3 list. All three were wrong: the table was written from `InputFormat.md` §4.3 without opening the fixtures it classified. See [`Findings.md`](Findings.md) §7.

The four marked ones are the existing `Implementation/*/fixtures/rejected/`, copied here so
that this corpus is self-contained; they stay there too, because each translator's own smoke
test should keep working without this directory being present.

A rejected net is a test of the *validator*, so it needs no oracle. Where the oracle happens to
reject the same net, a disagreement about which nets are well-formed is a finding about how far a
standard tool is from Definition 5 — worth recording under
[`Oracle.md`](Oracle.md) §3.2, not worth resolving.

---

## 6. Layout

```
Tests/
  corpus/
    tier1/         thirteen nets, per section 2
    tier2/         five nets, per section 3
    rejected/      twelve nets, per section 5
    expected.tsv   per section 2.1 -- tier-3 rows point at Implementation/*/fixtures
    fuzz/          nets the random search found and shrunk; committed as regressions
  oracle/          per Oracle.md section 5
  scripts/         check.sh (legs A-D), fuzz.py, mcc.py, markings.py, toolchain.py
  out/             generated; gitignored
```

Tier 3 is not copied here: `counter`, `jobs` and `multitoken` stay in
`Implementation/*/fixtures/`, which is each translator's own smoke test and should keep working
without this directory present, and `expected.tsv` reads its tier-3 rows from there directly.
PNML never joined this corpus — [`Findings.md`](Findings.md) §6 is why — so the round trip lives
entirely in [`Implementation/tools/roundtrip/`](../../Implementation/tools/roundtrip).

---

## Sources

- Definitions 4 to 9, and the reachability graph of Definition 9, transcribed in
  [`ColoredPetriNets.md`](../../Thesis/docs/ColoredPetriNets.md).
- The expression language and the T1 checks these nets are written against:
  [`InputFormat.md`](../../Implementation/docs/InputFormat.md) §4.1 and §4.3.
- The summand and parameter counts of §2.1:
  [`Target.md`](../../Implementation/docs/Target.md) §2.
- The order problem `two-tokens` exercises:
  [`Plan.md`](../../Implementation/docs/Plan.md) §5.
