# The PNML importer

The three translators read one native JSON format that is Definition 5 component for component,
and **every other format reaches them through an unverified importer**. This is that importer,
for PNML — the ISO/IEC 15909-2 interchange format for Petri nets.

```bash
python pnml2cpn.py net.pnml out.cpn.json
```

It is one converter rather than three because it sits outside the trust boundary: its output is
read by three independent implementations that share no code, which is a better check on it than
any test it could carry itself. Python is used so that no translator's toolchain becomes a
prerequisite for reading a format none of them trust; nothing in `Implementation/Lean`,
`Implementation/Dafny` or `Implementation/OCaml` depends on it.

## What it reads

High-level nets — Symmetric Nets and HLPNG — restricted to the fragment that maps onto the
expression language of [`InputFormat.md`](../docs/InputFormat.md) §4.1.

| PNML | Native |
| --- | --- |
| `<namedsort>` with `<bool/>` | `{"kind": "bool"}` |
| `<namedsort>` with `<integer/>`, `<natural/>`, `<positive/>` | `{"kind": "int"}` |
| `<namedsort>` with `<finiteenumeration>` | `{"kind": "enum", "ids": [...]}` |
| `<namedsort>` with `<productsort>` | `{"kind": "record", "fields": [...]}` |
| `<variabledecl>` | an entry in `variables` |
| `<place>` with `<type>` and `<hlinitialMarking>` | a place, its colour and `I(p)` |
| `<transition>` with `<condition>` | a transition and its guard `G(t)` |
| `<arc>` with `<hlinscription>` | an in- or out-arc and its `E(a)` |
| `<numberof>`, `<add>`, `<empty>` | the bag fragment: `["bag", …]`, `["emptyBag"]` |
| `<variable>`, `<useroperator>`, `<booleanconstant>`, `<numberconstant>`, `<tuple>` | `var`, `ctor`, `bool`, `int`, `rec` |
| `<equality>`, `<lessthan>`, `<lessthanorequal>`, `<and>`, `<or>`, `<not>`, `<addition>`, `<subtraction>`, `<multiplication>` | the operators of §4.1 |
| `<greaterthan>`, `<greaterthanorequal>`, `<inequality>` | the same relations, arguments flipped or negated |

Everything else is refused with the reason named. Exit code **3** means the file is good PNML
that this project's language cannot express; **4** means it is not the PNML this reads.
`rejected/` holds one file per category, and the check asserts each is refused.

## Running the check

```bash
bash roundtrip/check.sh
```

It imports each `roundtrip/*.pnml`, runs all three translators on the result in both encodings,
compares against the text the committed fixtures produce, checks `jobs` up to bisimilarity with
`ltscompare`, and asserts every file in `roundtrip/rejected/` is refused. A translator it cannot
run is reported as skipped rather than failing the build.

## Three things PNML and the native format do not agree about

Found by building the round trip, and recorded rather than smoothed over.

### 1. Product sorts are positional, records are named

[`InputFormat.md`](../docs/InputFormat.md) §4.1's records have named fields; ISO/IEC 15909-2's
`<productsort>` has positional components and no field names anywhere in the standard. Components
are therefore named `f1`, `f2`, … unless the `<productsort>` carries

```xml
<toolspecific tool="cpn2mcrl2" version="1">
  <fieldnames><field name="num"/><field name="state"/></fieldnames>
</toolspecific>
```

> **Addition to the thesis.** Nothing in Definition 5 or in `InputFormat.md` §4 mentions a tool-specific annotation. This one exists because a record's field names appear in the emitted mCRL2 text, so importing without them would make the output depend on a naming convention rather than on the input.

### 2. A `<tuple>` carries no sort

PNML tuples are untyped at the point of use, so the importer recovers the product sort from the
number of components. Two product sorts of the same arity therefore make a file ambiguous, and it
is refused rather than guessed.

### 3. There is no projection, and `jobs` is the casualty

The `jobs` fixture's guard is $\mathrm{proj}(j, \textit{state}) = \textit{fresh}$, and its out-arc
rebuilds a record from a projection. **ISO/IEC 15909-2 has no projection operator on a product
sort.** A Symmetric Net takes a tuple apart by binding a *tuple of variables* on the in-arc, which
is a pattern rather than a projection.

So `jobs.pnml` is not the `jobs` fixture. It is a different net — two variables, no projection —
with the same behaviour, and it is the closest standard PNML can come:

| Fixture | Through PNML |
| --- | --- |
| `counter` | byte-identical, all three translators, both encodings |
| `multitoken` | byte-identical, all three translators, both encodings |
| `jobs` | text differs; the LTS is **strongly bisimilar** to the recorded `jobs.aut` |

Twelve byte-identical comparisons and one bisimulation, which is the whole of what a round-trip
criterion can mean for a format that cannot express the input.

## What is not here

**Any proof.** This is outside the trust boundary by design. What it produces is checked by the
T1 validation of all three translators, which is the arrangement
[`InputFormat.md`](../docs/InputFormat.md) §3 argues for.

**An exporter.** Nothing here writes PNML.

**A corpus to run it on.** The importer was built partly to open up the Model Checking Contest's
published models. That measurement has since been made, and the answer is 0 of 443 files: every
coloured model there uses cyclic enumerations, which this expression language has no term for.
See [`Tests/docs/Findings.md`](../../Tests/docs/Findings.md) §10.

## Sources

- PNML, the Petri Net Markup Language, ISO/IEC 15909-2; the high-level dialects are Symmetric
  Nets and HLPNG. [pnml.org](http://www.pnml.org/)
- Definition 5 and the native format it is transcribed into:
  [`InputFormat.md`](../docs/InputFormat.md) §4.
