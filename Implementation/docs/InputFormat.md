# The input format

Which Colored Petri Net the translator reads, and in what.

---

## 1. What the input must carry

Definition 5 of [`ColoredPetriNets.md`](../../Thesis/docs/ColoredPetriNets.md) fixes the
content exactly. A CPN is a tuple $(P, T, A, \Sigma, V, C, E, G, I)$, and every component has to
survive the round trip into a file and back:

| Component | What the file must hold |
| --- | --- |
| $P$, $T$ | Finite place and transition names, disjoint |
| $A$ | Arcs, split into $P \times T$ and $T \times P$ |
| $\Sigma$ | A finite set of colors, each with a concrete definition |
| $V$ | Finite typed variables, with $\mathrm{Type}[v] \in \Sigma$ |
| $C$ | A color per place |
| $E$ | An expression per arc, of type $C(p)_{\mathrm{MS}}$ for the attached place $p$ |
| $G$ | A guard per transition, of type $\textit{Bool}$ |
| $I$ | A closed initialization expression per place, of type $C(p)_{\mathrm{MS}}$ |

Two things are **derived, not stored**. $\mathrm{Var}(t)$ is the free-variable set of $G(t)$ and
of the arc expressions at $t$, so it is computed rather than declared;
[`LeanFormalization.md`](../../Thesis/docs/LeanFormalization.md) §4.6 notes that
$\mathrm{Var}(t) \subseteq V$ is provable from the typing but is not currently stated, and in an
implementation it becomes one of the T1 validation checks. $pre(t)$ and $post(t)$ likewise come
from $A$.

The hard part is not the graph. It is $\mathrm{EXPR}$: the file has to carry *expressions*, and
the whole verification story of [`Plan.md`](Plan.md) §4 depends on that expression language
being small enough to formalize.

---

## 2. The candidates

| Format | Expression language | Standardized | Formalizable | Corpus | Verdict |
| --- | --- | --- | --- | --- | --- |
| PNML, P/T package | none — uncolored | ISO/IEC 15909-2 | n/a | large | Not a CPN. Out |
| PNML, Symmetric Nets | Closed and finite: finite and cyclic enumerations, dot, products, and a fixed operator set | ISO/IEC 15909-2 | **Yes** | Model Checking Contest | Strong, but no integers |
| PNML, HLPNG | Adds integers, booleans, strings, lists | ISO/IEC 15909-2 | Mostly | Model Checking Contest | Strong. Covers Example 3 |
| CPN Tools / CPN IDE `.cpn` | CPN ML, a dialect of Standard ML | de facto only | **No** | many published models | Out, see below |
| Matala `.prj` | Xtext DSL, Eclipse-bound | no | n/a | internal | Out, see below |
| Native JSON AST | Whatever [§4](#4-the-native-format) fixes | no | **Yes, by construction** | must be built | The verified core's input |

### 2.1 Why not `.cpn`

CPN Tools is the obvious choice by ubiquity, and its successor
[CPN IDE](https://cpnide.org/) is maintained at TU/e on top of Access/CPN — the same
institution as the thesis — while CPN Tools development itself has stopped. The format is
`.cpn`, an XML file.

It is still the wrong input. Annotations in a `.cpn` file are **CPN ML**, a dialect of Standard
ML with functions, datatypes, pattern matching and a module system. Formalizing enough of
Standard ML to state what $E(p,t)$ *denotes* is a larger project than everything else in
[`Plan.md`](Plan.md) put together, and without that the T2 obligation cannot even be phrased.
A `.cpn` importer that handles a recognized fragment is a reasonable M7 convenience, outside the
trust boundary, and nothing more.

### 2.2 Why not `.prj`

The thesis's own pipeline takes a Matala `.prj` model, and on save produces a CPNServer folder
and an mCRL2 folder. But the CPN in that pipeline is never a file: `generator/PetriNet.xtend`
builds it in memory and `Cpn2mcrl2Generator.xtend` consumes it directly. Reading `.prj` would
mean depending on an Eclipse/Xtext toolchain to obtain a data structure the format does not
actually contain, and it would tie the project to a model of BPMN products that
[`Thesis/docs/`](../../Thesis/docs) explicitly does not cover.

This is worth stating positively rather than as a rejection: **because the reference
implementation has no CPN interchange format, nothing is being broken by choosing a new one.**

### 2.3 Why PNML is the right *importer*, not the right core input

PNML is a real ISO standard with published RELAX NG schemas and a layered type system — the
Symmetric Nets package restricts sorts to finite enumerations, cyclic enumerations, dot and
products with a fixed operator set, and the HLPNG package extends it with integers, booleans,
strings and lists. That layering is unusually well matched to this project: Symmetric Nets are
almost exactly a formalizable $\mathrm{EXPR}$, and HLPNG adds precisely the integers Example 3
needs.

It is still not what the verified core should parse, for one reason: PNML is XML with a
non-trivial schema, and an XML parser inside the trust boundary is a large unverified surface
for no gain. Put PNML outside the boundary, where it belongs, and let it emit the native format.

The prize is the corpus. The Model Checking Contest publishes a large body of colored models in
PNML, and using them as a differential test set at M7 would be worth considerably more than any
hand-written fixture set. How much of that corpus falls inside the expression language of
[§4](#4-the-native-format) should be measured before M7 is scheduled rather than assumed.

**Measured, and the prize is not there.** Over a 30-model sample of the 2024 edition, **0 of 443
files** fall inside §4: 382 are place/transition nets, and all 61 colored ones declare their
colors as *cyclic* enumerations — a finite set plus a wrapping successor — where §4.1 has only
the bare set. Two thirds of them then apply `successor` or `predecessor`, and **not one uses
`<finiteenumeration>`**, the only enumerated sort §4.1 has. The corpus is written that way
because MCC models are parameterized families instantiated at several sizes, which is what a
cyclic enumeration is for. So M7 keeps its other justification — PNML as a standard interchange
format, and an importer outside the trust boundary — and loses this one. Adding cyclic
enumerations would change Definition 5, $\mathrm{EXPR}$, the T2 obligations and all three
translators, so it is a thesis-level decision rather than a patch.
[`Tests/docs/Findings.md`](../../Tests/docs/Findings.md) §10 has the full breakdown and the
command that reproduces it.

---

## 3. The decision

**The verified core reads a native JSON AST that is Definition 5, component for component.
Every other format reaches it through an unverified importer.**

```
   PNML (SN / HLPNG)  --importer-->  |
   CPN Tools .cpn (fragment)  ------>|  native CPN JSON  -->  verified core
   surface syntax, hand-written  --->|
                                     |
        unverified, outside          |        inside the
        the trust boundary           |     trust boundary
```

Three properties make this the right shape.

**Parsing becomes a schema check, not a grammar.** The core reads an AST that is already a tree,
so there is no ambiguity, no precedence, no lexer. What remains is validating that the tree
satisfies Definition 5 — which is T1, and which is a finite list of checks rather than a parser
correctness proof.

**The expression language is fixed by us, not inherited.** This is what makes
[`Plan.md`](Plan.md) §4's obligations statable at all. Anything a source format can express that
the native language cannot is rejected at the importer, loudly, outside the trust boundary.

**Any surface syntax is a convenience.** Writing CPNs as JSON ASTs by hand is unpleasant, so a
readable surface syntax is worth having — but it is an unverified front-end that emits the JSON,
and it is never what the core parses.

---

## 4. The native format

### 4.1 Sorts and expressions

Note the asymmetry, because it keeps the input language small: **the input needs only colors and
bags of colors. Product sorts appear only in the output.** Definition 5 types every variable by
a color and every expression by a color or a bag of a color, which is exactly the two-constructor
`ExprTy` the Lean already has. The product former that
[`Plan.md`](Plan.md) §4 obligation 1 introduces is needed for $D$ and $H_t$, which are
constructed by Definition 14 — they are translation-internal and never appear in a CPN file.

Colors:

```
color ::= Bool
        | Int
        | enum(name, [id, ...])
        | record(name, [(field, color), ...])
```

Expression sorts are then `color` or `Bag(color)`, and nothing else.

Expressions:

```
e ::= var(v)                          -- a variable in V
    | int(n) | bool(b) | ctor(id)     -- literals and enum constructors
    | rec(name, [(field, e), ...])    -- record construction
    | proj(e, field)                  -- record projection
    | e + e | e - e | e * e           -- Int
    | e = e | e <= e | e < e          -- comparison, into Bool
    | e && e | e || e | !e            -- Bool
    | bag([(n, e), ...]) | emptyBag   -- Bag(c), the notes' {n`e}
    | e union e | e diff e            -- Bag(c)
```

Guards are the `Bool` fragment. Arc and initialization expressions are the `Bag(c)` fragment.
This is the smallest language that expresses Example 3 — whose annotations are $\{1`1\}$,
$\{1`h\}$, $\{1`(h+1)\}$, $h \leq 3$ and $h > 3$ — and it is closed under everything Definition
14 assembles.

Two deliberate omissions. There is **no quantifier**: the bounded conjunction over $pre(t)$ is
unfolded at translation time, per [`Plan.md`](Plan.md) §4 obligation 3. And there are **no
user-defined functions**, which is the line that keeps this from becoming CPN ML.

Bags are finitely supported by construction, per [`Plan.md`](Plan.md) §4.1, and every color
carries decidable equality.

### 4.2 The net

```json
{
  "colors": {
    "Int":  { "kind": "int" },
    "Bool": { "kind": "bool" }
  },
  "variables": { "h": "Int" },
  "places": {
    "p1": { "color": "Int", "init": ["bag", [[1, ["int", 1]]]] },
    "p2": { "color": "Int", "init": ["emptyBag"] },
    "p3": { "color": "Int", "init": ["emptyBag"] }
  },
  "transitions": {
    "t1": { "guard": ["bool", true] },
    "t2": { "guard": ["<=", ["var", "h"], ["int", 3]] },
    "t3": { "guard": ["<",  ["int", 3], ["var", "h"]] }
  },
  "inArcs": [
    { "place": "p1", "transition": "t1", "expr": ["bag", [[1, ["var", "h"]]]] },
    { "place": "p2", "transition": "t2", "expr": ["bag", [[1, ["var", "h"]]]] },
    { "place": "p2", "transition": "t3", "expr": ["bag", [[1, ["var", "h"]]]] }
  ],
  "outArcs": [
    { "transition": "t1", "place": "p2",
      "expr": ["bag", [[1, ["+", ["var", "h"], ["int", 1]]]]] },
    { "transition": "t2", "place": "p1", "expr": ["bag", [[1, ["var", "h"]]]] },
    { "transition": "t3", "place": "p3", "expr": ["bag", [[1, ["var", "h"]]]] }
  ]
}
```

That is Example 3, and it should be the first fixture committed. It is the net whose reachability
graph is Example 5 — the seven-state chain, with the thesis's eighth state corrected away — and
whose translation is Example 9, so a single input exercises the whole pipeline against three
worked examples at once, two of which carry recorded corrections.

### 4.3 The T1 validation checks

Everything Definition 5 requires but JSON cannot enforce, checked once at the boundary and then
available as hypotheses to the T2 proof. These are exactly the side conditions
[`LeanFormalization.md`](../../Thesis/docs/LeanFormalization.md) §4.5 records as currently inert:

1. $P$ and $T$ are finite and disjoint, and every arc names an existing place and transition.
2. Every color referenced is declared, and $\Sigma$ is finite — `finiteColors`, `colorMem`.
3. $\mathrm{Type}[v] \in \Sigma$ for every variable — `varTypeMem`.
4. $\mathrm{Type}[G(t)] = \textit{Bool}$ — `boolMem`.
5. $\mathrm{Type}[E(a)] = C(p)_{\mathrm{MS}}$ for the place $p$ attached to $a$.
6. $\mathrm{Type}[I(p)] = C(p)_{\mathrm{MS}}$, and $I(p)$ is closed.
7. $\mathrm{Var}(t) \subseteq V$, the inclusion of
   [`LeanFormalization.md`](../../Thesis/docs/LeanFormalization.md) §4.6.

Checks 4 to 6 are a type checker for [§4.1](#41-sorts-and-expressions), and are what let the
core hold an intrinsically typed AST from that point on.

8. The **nullary constructors of $\Sigma$ are distinct**: no two enumerations declare a
   constructor of the same name, and no field-less record shares its name with one.

> **Addition to the thesis.** Definition 5 requires nothing of the kind — colour sets are sets, and two of them may perfectly well both contain an element spelled $a$. Check 8 is imposed by the *target*, exactly as [`Target.md`](Target.md) §1's reserved keywords are: an enumeration prints as `struct a | b` and a field-less record as `struct R`, so both put constants into one mCRL2 namespace, and `mcrl22lps` refuses two constants of the same name even in different sorts. Without the check all three translators emit text the toolset rejects. Found by the random search of [`Tests/`](../../Tests/README.md); see [`Tests/docs/Findings.md`](../../Tests/docs/Findings.md) §8.

---

## 5. Sources

- ISO/IEC 15909-2:2011, *Systems and software engineering — High-level Petri nets — Part 2:
  Transfer format*. Reference material and RELAX NG schemas at
  [pnml.org](https://www.pnml.org/).
- L. M. Hillah et al., *A primer on the Petri Net Markup Language and ISO/IEC 15909-2*.
  [pnml.org/papers/pnnl76.pdf](https://www.pnml.org/papers/pnnl76.pdf)
- CPN Tools, and its TU/e successor CPN IDE, built on Access/CPN.
  [cpntools.org](https://cpntools.org/), [cpnide.org](https://cpnide.org/)
- S. Dal Zilio, *MCC: a Tool for Unfolding Colored Petri Nets in PNML Format*, on the Model
  Checking Contest colored corpus. [arxiv.org/abs/2003.09134](https://arxiv.org/abs/2003.09134)
- Definition 5 and Examples 3, 5 and 9 as transcribed in
  [`ColoredPetriNets.md`](../../Thesis/docs/ColoredPetriNets.md) and
  [`mCRL2.md`](../../Thesis/docs/mCRL2.md).
