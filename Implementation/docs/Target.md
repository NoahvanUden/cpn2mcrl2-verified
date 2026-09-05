# The mCRL2 target

What the translator emits, verified against the toolset rather than assumed.

Everything in this file was run against mCRL2 toolset **202307.1**.

---

## 1. Why this needed checking

[`LeanFormalization.md`](../../Thesis/docs/LeanFormalization.md) §5.1 leaves a question open
before the second of its three readings of "well-formed" can be relied on:

> Whether the operations Definition 14 uses are native mCRL2 bag operators should be confirmed against the tool documentation before the second reading is relied on.

It is confirmed. They are all native, and they mean what Definition 14 means.

| Definition 14 writes | mCRL2 | Notes |
| --- | --- | --- |
| $C(p)_{\mathrm{MS}}$ | `Bag(C)` | also `FBag(C)` |
| $\emptyset_{\mathrm{MS}}$ | `{:}` | `{}` is the empty *set*, not the empty bag |
| $\{n`e\}$ | `{e: n}` | element first, multiplicity second — the reverse of the notes' order |
| $m_1 \cup m_2$ | `m1 + m2` | adds coefficients, as operation 2 |
| $m_1 \setminus m_2$ | `m1 - m2` | truncated, as operation 6 |
| $m_1 \subseteq m_2$ | `m1 <= m2` | |
| $s \in m$ | `s in m` | |

One implementation note that will bite a code generator: **`val` is a reserved keyword**, so
record field names taken from a CPN's color definitions must be checked against mCRL2's keyword
list and escaped. This is the kind of thing T2 does not catch and T0 does.

---

## 2. Definition 14, emitted faithfully

Example 9 of [`mCRL2.md`](../../Thesis/docs/mCRL2.md), written out with one `Bag` per place, as
Definition 14 says:

```
act t1, t2, t3;

proc Spec(sp1, sp2, sp3 : Bag(Int)) =
    sum h : Int . ({h: 1} <= sp1)             -> t1 . Spec(sp1 - {h: 1}, sp2 + {(h+1): 1}, sp3)
  + sum h : Int . ({h: 1} <= sp2 && h <= 3)   -> t2 . Spec(sp1 + {h: 1}, sp2 - {h: 1}, sp3)
  + sum h : Int . ({h: 1} <= sp2 && h > 3)    -> t3 . Spec(sp1, sp2 - {h: 1}, sp3 + {h: 1});

init Spec({1: 1}, {:}, {:});
```

`mcrl22lps` accepts it. Two things are worth recording about what comes back.

**The shape survives linearization.** `lpsinfo` reports 3 process parameters — one per place, as
$D = (S_{p_1} \times \ldots \times S_{p_n})$ requires — and 4 summands: one per transition, plus
mCRL2's `delta`. Definition 14 already produces linear form, so `mcrl22lps` has nothing to
linearize. That gives a cheap structural check to run on every fixture:

> Summands after linearization must be exactly $|T| + 1$, and process parameters exactly $|P|$. If not, what was emitted was not an LPE.

**The tool normalizes the condition.** `lpspp` shows `{h: 1} <= sp1` rewritten to
`{h: 1} * sp1 == {h: 1}`. Semantics preserved, syntax not. So a golden-file test must compare
against the *emitted* text or against the LTS, never against `lpspp` output.

### 2.1 It reproduces both recorded corrections

`lps2lts` on the above gives:

```
des (0,6,7)
(0,"t1",1)
(1,"t2",2)
(2,"t1",3)
(3,"t2",4)
(4,"t1",5)
(5,"t3",6)
```

Seven states and the trace $t_1 t_2 t_1 t_2 t_1 t_3$. That is Example 5 as corrected in
[`ColoredPetriNets.md`](../../Thesis/docs/ColoredPetriNets.md), not the eight-state
$t_1 t_2 t_1 t_2 t_1 t_2 t_3$ that Figure 3.4 of the thesis draws. It also depends on the
Example 9 correction in [`mCRL2.md`](../../Thesis/docs/mCRL2.md): with the third summand's
condition on $s_{p_3}$ as printed in the thesis, $t_3$ could never fire and the run would
deadlock at six states.

Both corrections now have a witness outside Lean, produced by the tool the thesis targets. That
is worth keeping as a regression fixture on its own.

---

## 3. What the reference implementation emits instead

`Cpn2mcrl2Generator.xtend` in the
[OfflineMBT repository](https://github.com/dbera/OfflineMBT/tree/mcrl2-model-checking) does not
emit the above. Reading its sources, it emits:

- **`sort token = struct None | Place1(...) | Place2(...);`** — one tagged-union sort shared by
  every place, rather than $C(p)$ per place.
- **`proc CPN(m_place1: List(token), ...)`** — a `List(token)` per place, not a `Bag`.
- **`sort b_TransName = struct b_TransName(...)`** — a `struct` per transition for the binding,
  which is exactly the tuple sort $H_t$ that
  [`LeanFormalization.md`](../../Thesis/docs/LeanFormalization.md) §5.1 identifies as the
  structural blocker in the current `ExprTy`. mCRL2's `struct` is the answer to obligation 1 of
  [`Plan.md`](Plan.md) §4.
- A hand-written `remove_token_from_list` map function, membership as `place(col(b)) in m_place`,
  guards appended with `&&`, and the initial marking read from a JSON configuration.

The list encoding is what [`mCRL2.md`](../../Thesis/docs/mCRL2.md) §4.1 recommends on
performance grounds — 9 seconds against 67 for bags on the thesis's own benchmark. It is also
two refinements away from the object Theorem 1 is about, neither of which is justified anywhere.
[`Plan.md`](Plan.md) §5 treats this as the project's largest open mathematical gap.

Written out for Example 9, the list encoding is:

```
sort Tok = struct tok(v: Int);

map rm : Tok # List(Tok) -> List(Tok);
var t, u : Tok; l : List(Tok);
eqn rm(t, []) = [];
    rm(t, u |> l) = if(t == u, l, u |> rm(t, l));

act t1, t2, t3;

proc Spec(p1, p2, p3 : List(Tok)) =
    sum h : Int . (tok(h) in p1)            -> t1 . Spec(rm(tok(h), p1), p2 <| tok(h+1), p3)
  + sum h : Int . (tok(h) in p2 && h <= 3)  -> t2 . Spec(p1 <| tok(h), rm(tok(h), p2), p3)
  + sum h : Int . (tok(h) in p2 && h > 3)   -> t3 . Spec(p1, rm(tok(h), p2), p3 <| tok(h));

init Spec([tok(1)], [], []);
```

This also produces `des (0,6,7)` with the same trace.

---

## 4. The validation harness

The two encodings can be compared mechanically, and the toolset ships the comparison:

```
ltscompare -ebisim ex9.aut ex9_list.aut
LTSs are equal (strong bisimilarity using the O(m log n) algorithm)
```

Generalize that and it becomes the end-to-end check for the whole project:

```
   CPN fixture
        |
        +---- reference semantics (Definitions 6-9) ----> reachability graph  --> A.aut
        |
        +---- translator --> mCRL2 --mcrl22lps--> .lps --lps2lts--> B.aut
                                                                        |
                                     ltscompare -ebisim A.aut B.aut  <--+
```

**That is Theorem 1, checked on a concrete instance.** It does not prove anything, but it is the
only check available that tests the translation against the actual tool, and it directly closes
the loop [`LeanFormalization.md`](../../Thesis/docs/LeanFormalization.md) §5 says nothing
currently closes:

> nothing here connects the Lean to the translation as it is actually implemented

The reachability-graph side can be produced from the Lean itself once M2 makes the CPN semantics
computable, or from the unverified M1 prototype in the meantime. Either way the harness runs on
every fixture in CI, alongside the `mcrl22lps` acceptance check of T0 and the summand-count check
of [§2](#2-definition-14-emitted-faithfully).

### 4.1 The first thing to test with it

Example 9 never puts more than one token in a place, so its bisimilarity result says nothing
about the order problem of [`Plan.md`](Plan.md) §5. The first genuinely informative fixture is a
net that holds several tokens in one place, produced in different orders. If the list encoding
is going to fail, that is where it fails, and finding out at M1 costs an afternoon where finding
out at M6 costs a milestone.

---

## 5. Sources

- mCRL2 toolset 202307.1, tools `mcrl22lps`, `lps2lts`, `lpsinfo`, `lpspp`, `ltscompare`.
  [mcrl2.org](https://www.mcrl2.org/)
- J. F. Groote and M. R. Mousavi, *Modeling and Analysis of Communicating Systems*, MIT Press,
  2014 — the mCRL2 data language and its bag operators.
- The reference implementation:
  [OfflineMBT, branch `mcrl2-model-checking`](https://github.com/dbera/OfflineMBT/tree/mcrl2-model-checking),
  `bundles/nl.asml.matala.product/src/nl/asml/matala/product/mcrl2/Cpn2mcrl2Generator.xtend`.
- Definition 14, Definition 15 and Example 9 as transcribed in
  [`mCRL2.md`](../../Thesis/docs/mCRL2.md); Example 5 in
  [`ColoredPetriNets.md`](../../Thesis/docs/ColoredPetriNets.md).
