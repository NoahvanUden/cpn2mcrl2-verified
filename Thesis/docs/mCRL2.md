# mCRL2

The mCRL2 language is a formal specification language built upon the rich literature of
process algebras [8]. In this project, the mCRL2 toolset is used as a **verification
back-end** for [Colored Petri Nets](ColoredPetriNets.md). This allows for model checking of
CPNs, and thus also for BPMN models.

This page contains the syntax and semantics of the mCRL2 fragment used in the thesis
*Model checking for analysis of BPMN models* (N. van Uden, TU/e, 2025), Chapters 5 and 6:
the **Linear Process Equation** (the specification format), its semantics as a
[Labeled Transition System](LabeledTransitionSystems.md), and the **modal $\mu$-calculus**
(the property language).

Shared notation (bags, expressions, bindings) is defined in
[CommonDefinitions.md](CommonDefinitions.md).

---

## 1. Linear Process Equations

To use mCRL2 as a verification back-end, a translation from CPN to a format accepted by the
mCRL2 model checker is necessary. The format chosen is the **Linear Process Equation (LPE)**.
An LPE is an mCRL2 process of restricted form. For a process, a set of actions, with possible
parameters, $Act$ is assumed.

### 1.1 Syntax

**Definition 13 (Linear Process Equation (LPE) [8]).**
A Linear Process Equation is a specification of the following shape:

$$Spec(d : D) = \sum_{k \in K} \; \sum_{h_k : H_k} \; c_k(d, h_k) \rightarrow a_k(d, h_k) \cdot Spec(g_k(d, h_k))$$

Where $Spec$ is the name of the process,

- $D$ is a datatype,
- $d$ is a variable of type $D$,
- $K$ is an index set and for all $k \in K$:
  - $H_k$ is a datatype,
  - $h_k$ is a variable of type $H_k$,
  - $c_k : D \times H_k \rightarrow \textit{Bool}$ is a **condition**,
  - $a_k \in Act$ is an **action label**,
  - $g_k : D \times H_k \rightarrow D$ is the **next state**.

### 1.2 Notation

The notation $\sum_{k \in K} p_k$ is used as a shorthand for $p_{k_1} + \ldots + p_{k_n}$
for all $k_1, \ldots, k_n \in K$.

### 1.3 Translating CPN models to an LPE

To model a [CPN](ColoredPetriNets.md) using an LPE, the LPE must keep track of the state of
the CPN. For a CPN the state is a function mapping places to bags of tokens. In the LPE the
state, $D$, is modeled as an $n$-tuple of bags of tokens, where $n$ is equal to the number of
places in the CPN. Thus in the LPE, similarly as in the CPN, for each place a bag of tokens
is stored.

Additionally, the LPE should model the same transitions as the CPN. Since transitions in
CPNs do not carry data, the type of the transition and the functions producing the data in
the resulting LPE can be omitted. In a CPN, a transition can occur if there exists a binding
such that the guard of the transition evaluates to True, and the input places of the
transition have tokens, see Definition 6. To model this in the LPE, the guard of a transition
$t \in T$, $c_t$ should evaluate to True, if and only if the same conditions as in the CPN
hold.

Finally, when a transition occurs in a CPN, the tokens in the input places are removed, and
new tokens are placed in the output places, according to the update expressions in the
transition, see Definition 7. In the LPE, the same should be modeled in the update function
$g_t$ for a transition $t \in T$.

**Definition 14 (Translation).**
Given a CPN $(P, T, A, \Sigma, V, C, E, G, I)$, produce an LPE:

$$Spec(d : D) = \sum_{k \in K} \; \sum_{h_k : H_k} \; c_k(d, h_k) \rightarrow a_k \cdot Spec(g_k(d, h_k))$$

Where:

- $K = T$,
- $D = (S_{p_1} \times \ldots \times S_{p_n})$, for all $p_1, \ldots, p_n \in P$, where for
  each $p \in P$, $S_p$ is a bag such that $\mathrm{Type}[S_p] = C(p)_{\mathrm{MS}}$.

And for all $t \in T$:

- $H_t = (\mathrm{Type}[v_1] \times \ldots \times \mathrm{Type}[v_n])$, for all
  $v_1, \ldots, v_n \in \mathrm{Var}(t)$
- $a_t = t$, where $a_t$ has no parameters,

And for $d = (s_{p_1}, \ldots, s_{p_n})$ for all $p_1, \ldots, p_n \in P$:

$$
\begin{aligned}
c_t(d, h_t) &= \big(\forall p \in pre(t) : E(p,t) \subseteq s_p\big) \land G(t) \\[4pt]
g_t(d, h_t) &= \big( (s_{p_1} \setminus E(p_1, t)) \cup E(t, p_1), \ldots, (s_{p_n} \setminus E(p_n, t)) \cup E(t, p_n) \big)
\end{aligned}
$$

For a CPN the initial state is defined as $M_0$, therefore the initial state of the LPE,
$d_0$, is defined for all $p_1, \ldots, p_n \in P$ as:

$$d_0 = (M_0(p_1), \ldots, M_0(p_n))$$

> Note that the action $a_k$ produced by the translation carries **no parameters**, unlike the general shape $a_k(d, h_k)$ of Definition 13. Actions with parameters are re-introduced only where a property requires data to be exposed; that is described in Chapters 6 and 7 of the thesis, which are not covered on this page.

**Example 9.**
Consider the CPN as defined in Example 3 of [ColoredPetriNets.md](ColoredPetriNets.md),
after translation the resulting LPE becomes:

$$
\begin{aligned}
&Spec\big((s_{p_1}, s_{p_2}, s_{p_3}) : (Int_{\mathrm{MS}} \times Int_{\mathrm{MS}} \times Int_{\mathrm{MS}})\big) = \\
&\quad \phantom{+} \sum_{h : Int} (\{1`h\} \subseteq s_{p_1}) \rightarrow t_1 \cdot Spec(s_{p_1} \setminus \{1`h\},\; s_{p_2} \cup \{1`(h+1)\},\; s_{p_3}) \\
&\quad + \sum_{h : Int} (\{1`h\} \subseteq s_{p_2} \land h \leq 3) \rightarrow t_2 \cdot Spec(s_{p_1} \cup \{1`h\},\; s_{p_2} \setminus \{1`h\},\; s_{p_3}) \\
&\quad + \sum_{h : Int} (\{1`h\} \subseteq s_{p_2} \land h > 3) \rightarrow t_3 \cdot Spec(s_{p_1},\; s_{p_2} \setminus \{1`h\},\; s_{p_3} \cup \{1`h\})
\end{aligned}
$$

With initial state $d_0 = (\{1`1\}, \emptyset, \emptyset)$.

> **Deviation from the thesis.** The condition of the third summand is printed in the thesis as $\{1`h\} \subseteq s_{p_3}$. Since $pre(t_3) = \{p_2\}$, Definition 14 yields $\{1`h\} \subseteq s_{p_2}$ — which is also what the update part of that same summand assumes, as it removes the token from $s_{p_2}$. Corrected to $s_{p_2}$ above.

### 1.4 Semantics

The semantics of an LPE is an LTS. Thus, to compare the behavior of the LPE with the
behavior of the CPN, the LPE is instantiated to an LTS. Similarly as for CPNs, to evaluate
expressions variables need to be assigned concrete values. The set of all possible bindings
over a datatype $H$ is denoted by $B[H]$.

**Definition 15 (Semantics of LPE [9]).**
From an LPE resulting from the translation as defined in Definition 14, with a set of
actions $Act$, an LTS with shape $(S, L, \rightarrow, s_0)$ can be induced:

$$
\begin{aligned}
S \;&=\; D \\[4pt]
L \;&=\; Act \\[4pt]
\rightarrow \;&=\; \{\, (d_c, a_k, d') \mid d, d' \in D \land a_k \in Act \\
&\qquad\;\; \land\; \exists b \in B[H_k] : c_k(d, h_k)\langle b \rangle = \textit{True} \\
&\qquad\;\; \land\; d' = g_k(d, h_k)\langle b \rangle \land d_c = d\langle b \rangle \,\} \\[4pt]
s_0 \;&=\; d_0, \text{ for a given } d_0 \in D
\end{aligned}
$$

> **Note.** Definition 15 is stated in the thesis for an LPE that results from the translation of a CPN (Definition 14, [§1.3](#13-translating-cpn-models-to-an-lpe)); in that translation the action $a_k$ has no parameters. The proof that this induced LTS and the reachability graph of the original CPN are bisimilar is in [Bisimiliarity.md](Bisimiliarity.md).

---

## 2. Model checking with mCRL2

With mCRL2, the behavior of an LPE can be checked using formal properties specified in the
**modal $\mu$-calculus**, a language for defining properties over an LTS [8]. In this project,
only a subset of this language is considered.

### 2.1 Syntax of the modal $\mu$-calculus

**Definition 18 (the modal $\mu$-calculus).**
Let $(S, L, \rightarrow, s_0)$ be an LTS, and $Var$ a set of fixpoint variables. The syntax
of $\mu$-calculus in its basic form is given as follows:

$$\phi := \textit{false} \mid \textit{true} \mid \lnot \phi \mid \phi \lor \phi \mid \phi \land \phi \mid \langle a \rangle \phi \mid [a]\phi \mid \mu X.\phi \mid \nu X.\phi \mid X$$

Where $a \in L$ is an action and $X \in Var$ is a fixpoint variable.

### 2.2 Shorthand notation

Let $A \subseteq L$ be a finite set of actions:

$$
\begin{aligned}
\langle A \rangle \phi &= \bigvee_{a \in A} \langle a \rangle \phi
&\qquad
[A]\phi &= \bigwedge_{a \in A} [a]\phi \\
\langle A^{*} \rangle \phi &= \mu X.(\langle A \rangle X \lor \phi)
&\qquad
[A^{*}]\phi &= \nu X.([A]X \land \phi) \\
\langle \overline{A} \rangle \phi &= \langle L \setminus A \rangle \phi
&\qquad
[\overline{A}]\phi &= [L \setminus A]\phi
\end{aligned}
$$

To denote the complete set of actions $L$, *true* is written instead of $A$.

> To ensure that the fixpoints $\mu X.\phi$ and $\nu X.\phi$ exist, any occurrence of $X$ in $\phi$ must be preceded by an even number of negations.

**Example 10.**
Let $(S, L, \rightarrow, s_0)$ be an LTS, where $L = \{a, b, c\}$, and $Var = \{X\}$.

| Formula | Meaning |
| --- | --- |
| $\langle a \rangle \langle b \rangle \langle c \rangle \textit{true}$ | From the initial state, a trace of an $a$ action, followed by a $b$ action, followed by a $c$ action is possible. |
| $[\textit{true}^{*}]\langle \textit{true} \rangle \textit{true}$ | After every possible trace, an action is possible, i.e., the model has no deadlocks. |
| $\mu X.([\textit{true}]X)$ | There is only a finite number of steps possible from the initial state, i.e., the model eventually terminates. |

### 2.3 Model checking pipeline

With the mCRL2 tool `lps2pbes` [16], from an LPE and a $\mu$-calculus property a
**Parameterized Boolean Equation System (PBES)** [11] can be generated. Subsequently, with
the tool `pbessolve` [17], the PBES can be solved to produce a Yes/No answer.

```
LPE  ──lps2pbes──>  PBES  ──pbessolve──>  Yes / No
        ▲
     Property
```

Two tools are available to obtain an LPE in the internal format of mCRL2:

| Tool | Use |
| --- | --- |
| `txt2lps` [11, 12] | Parse a file in LPE format to an LPE in the internal format of mCRL2. |
| `mcrl22lps` [13] | Given that the LPE format is a restricted form of the mCRL2 format, the LPE can be stored as an mCRL2 file and then translated to the internal LPE format. This is necessary if additional actions are added to the linear equations. |

---

## 3. Results of model checking

Model checking does not only lead to a Yes/No answer:

- If a property **does not hold**, model checking can provide a **counterexample** showing
  how the property is violated.
- If a property **does hold**, model checking can provide a **witness** showing why the
  property holds.

Counterexamples and witnesses are **sub models** of the model given as input to the model
checker [4].

| Property kind | Shape of the counterexample |
| --- | --- |
| Safety (something bad should not happen) | A trace leading up to the bad thing happening. |
| Liveness (something good should eventually happen) | A **lasso** (a trace ending in a loop), or a trace to a deadlock if the entire model is explored and the good thing never happens. |
| There should exist a future where something good happens | The whole model. |

---

## 4. Encoding notes

These notes concern how CPN concepts are represented in the resulting mCRL2 specification.

### 4.1 Markings

In an LPE resulting from the translation, tokens are stored in **bags**: for each place in
the original CPN, there is a corresponding bag of tokens. Although there are native
implementations for bags in mCRL2, using bags to store tokens does not lead to the best
performance. Replacing bags with a different data structure can improve the performance:

- **Lists** are a good alternative to bags. With lists, the necessary operations of bags,
  such as inserting or removing tokens, and a check if tokens are present, can be done much
  faster.
- If during the execution of a model the number of tokens in a specific place never exceeds
  one, the marking of that place can be replaced by a **single token**, which can
  significantly reduce verification time. However, it must be known beforehand that the
  number of tokens in that place never exceeds one.

Measured on the performance-comparison CPN of the thesis (Figure 5.1, 200 distinct tokens),
checking the property "$t_2$ occurs exactly two hundred times" ten times per implementation:

| Marking representation | Average time |
| --- | --- |
| `Bag` | 67 seconds |
| `FBag` | 60 seconds |
| `List` | 9 seconds |

### 4.2 Strings

In mCRL2 there is no native implementation of strings, however the BPMN language does allow
for strings. If strings are not part of any guard or property, then they do not affect model
checking and can thus be ignored. The simplest way of ignoring the strings is by introducing
a new datatype called `Unit`, with a single constructor `unit`, and replacing every string
with the constructor `unit`.

---

## Sources

- [4] S. Cranen, S. Luttik, and T. Willemse, "Evidence for fixpoint logic," in *24th EACSL
  Annual Conference on Computer Science Logic (CSL 2015), September 7-10, 2015, Berlin,
  Germany*, Leibniz International Proceedings in Informatics (LIPIcs), Schloss Dagstuhl -
  Leibniz-Zentrum für Informatik, 2015.
- [8] J. F. Groote and M. R. Mousavi, *Modeling and Analysis of Communicating Systems*.
  The MIT Press, 08 2014. *(Source of the mCRL2 language, Definition 13 and Definition 18.)*
- [9] B. Ploeger, J. Wesselink, and T. Willemse, "Verification of reactive systems via
  instantiation of parameterised boolean equation systems," *Information and Computation*,
  vol. 209, no. 4, pp. 637–663, 2011. *(Source of Definition 15.)*
- [11] M. Atif and J. Groote, *Understanding Behaviour of Distributed Systems Using mCRL2*.
  Studies in Systems, Decision and Control (SSDC), Germany: Springer, 2023.
- [12] "txt2lps; mCRL2 202407.1 documentation — mcrl2.org."
  <https://mcrl2.org/web/user_manual/tools/release/txt2lps.html>. [Accessed 29-01-2025].
- [13] "mcrl22lps; mCRL2 202407.1 documentation — mcrl2.org."
  <https://mcrl2.org/web/user_manual/tools/release/mcrl22lps.html>. [Accessed 29-01-2025].
- [15] O. Bunte, J. F. Groote, J. J. A. Keiren, M. Laveaux, T. Neele, E. P. de Vink,
  W. Wesselink, A. Wijs, and T. A. C. Willemse, "The mcrl2 toolset for analysing concurrent
  systems," in *Tools and Algorithms for the Construction and Analysis of Systems*
  (T. Vojnar and L. Zhang, eds.), (Cham), pp. 21–39, Springer International Publishing, 2019.
- [16] "lps2pbes; mCRL2 202407.1 documentation — mcrl2.org."
  <https://mcrl2.org/web/user_manual/tools/release/lps2pbes.html>. [Accessed 29-01-2025].
- [17] "pbessolve; mCRL2 202407.1 documentation — mcrl2.org."
  <https://mcrl2.org/web/user_manual/tools/release/pbessolve.html>. [Accessed 29-01-2025].
