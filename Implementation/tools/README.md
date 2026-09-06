# The PNML importer

Milestone **M7** of [`docs/Plan.md`](../docs/Plan.md) §6, scoped by
[`Tests/docs/Plan.md`](../../Tests/docs/Plan.md) §3.1.

[`InputFormat.md`](../docs/InputFormat.md) §3 fixes the shape: the verified core reads a native
JSON AST that is Definition 5 component for component, and **every other format reaches it
through an unverified importer**. This is that importer, for PNML.

```bash
python pnml2cpn.py net.pnml out.cpn.json
```

---

## 1. Why one converter and not three

The importer is outside the trust boundary, so it does not have to exist in each translator's
language, and the three keep their JSON importers unchanged. Its output is read by three
independent implementations that share no code — which is a better check on it than any test it
could carry itself, and is why writing it once in Python costs nothing in guarantee.

It is written in Python because that is what
[`Tests/`](../../Tests/README.md) uses, and because no translator's toolchain should become a
prerequisite for reading a file format none of them trust.

> **A note on the dependency.** [`Tests/docs/Plan.md`](../../Tests/docs/Plan.md) §8 rates "a new language and dependency" as a low risk mitigated by confining Python to `Tests/`. This file breaks that confinement, deliberately: M7 is an `Implementation/` milestone and its output belongs next to the format it produces. Nothing in `Implementation/Lean`, `Implementation/Dafny` or `Implementation/OCaml` depends on it.

---

## 2. What it reads

ISO/IEC 15909-2 high-level nets — Symmetric Nets and HLPNG — restricted to the fragment that maps
onto [`InputFormat.md`](../docs/InputFormat.md) §4.1.

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

Everything else is refused with the reason named, per
[`Tests/docs/Plan.md`](../../Tests/docs/Plan.md) §3.1 item 3. Exit code **3** means the file is
good PNML that this project's language cannot express; exit code **4** means it is not the PNML
this reads. `rejected/` holds one file per category, and `check.sh` asserts each is refused.

---

## 3. Three things PNML and the native format do not agree about

Found by building the round trip, and worth recording rather than smoothing over.

### 3.1 Product sorts are positional, records are named

[`InputFormat.md`](../docs/InputFormat.md) §4.1's records have named fields. ISO/IEC 15909-2 has
`<productsort>`, whose components are positional — there is no field name anywhere in the
standard. Components are therefore named `f1`, `f2`, … unless the `<productsort>` carries

```xml
<toolspecific tool="cpn2mcrl2" version="1">
  <fieldnames><field name="num"/><field name="state"/></fieldnames>
</toolspecific>
```

> **Addition to the thesis.** Nothing in Definition 5 or in `InputFormat.md` §4 mentions a tool-specific annotation. This one exists because a record's field names are part of the emitted mCRL2 text, so importing without them would make the output depend on a naming convention rather than on the input.

### 3.2 A `<tuple>` carries no sort

PNML tuples are untyped at the point of use, so the importer recovers the product sort from the
number of components. Two product sorts with the same arity therefore make a file ambiguous, and
it is refused rather than guessed.

### 3.3 There is no projection, and `jobs` is the casualty

The `jobs` fixture's guard is $\mathrm{proj}(j, \textit{state}) = \textit{fresh}$, and its
out-arc rebuilds a record from a projection. **ISO/IEC 15909-2 has no projection operator on a
product sort.** A Symmetric Net takes a tuple apart by binding a *tuple of variables* on the
in-arc, which is a pattern rather than a projection.

So `jobs.pnml` is not the `jobs` fixture. It is a different net — two variables, no projection —
that happens to have the same behaviour, and it is the closest standard PNML can come. The
consequence for the round-trip criterion is measured rather than asserted:

| Fixture | Through PNML |
| --- | --- |
| `counter` | byte-identical, all three translators, both encodings |
| `multitoken` | byte-identical, all three translators, both encodings |
| `jobs` | text differs; the LTS is **strongly bisimilar** to the golden `jobs.aut` |

That is twelve byte-identical comparisons and one bisimulation, and it is the whole of what the
criterion can mean for a format that cannot express the input.

---

## 4. Running the check

```bash
bash roundtrip/check.sh
```

Imports each `roundtrip/*.pnml`, runs all three translators on the result in both encodings,
compares against the text the committed fixtures produce, checks `jobs` up to bisimilarity with
`ltscompare`, and asserts every file in `roundtrip/rejected/` is refused.

The OCaml translator is a Linux binary on this machine, so the script runs it through `wsl.exe`
when it is not directly executable, and reports it as skipped when neither works — a missing
toolchain is a reported gap, not a red build.

---

## 5. What is not here

**The Model Checking Contest corpus.** M7's second half, and E6 of
[`Tests/docs/Plan.md`](../../Tests/docs/Plan.md) §7. The measurement §2.3 of
[`InputFormat.md`](../docs/InputFormat.md) asks for — how much of that corpus falls inside the
expression language — needs this importer plus the corpus, and is gated on it rather than on
anything here.

**Any proof.** This is outside the trust boundary by design. What it produces is checked by the
T1 validation of all three translators, which is exactly the arrangement
[`InputFormat.md`](../docs/InputFormat.md) §3 argues for.

**An exporter.** Nothing here writes PNML. The corpus in [`Tests/`](../../Tests/README.md) is
native JSON, for the reason recorded in
[`Tests/docs/Oracle.md`](../../Tests/docs/Oracle.md) §3.2.

---

## Sources

- PNML, the Petri Net Markup Language, ISO/IEC 15909-2; the high-level dialects are Symmetric
  Nets and HLPNG. [pnml.org](http://www.pnml.org/)
- Definition 5 and the native format it is transcribed into:
  [`InputFormat.md`](../docs/InputFormat.md) §4.
- The round-trip criterion: [`Tests/docs/Plan.md`](../../Tests/docs/Plan.md) §3.1.
