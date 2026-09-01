# Common Definitions

Definitions that are shared by the formalisms described in
[ColoredPetriNets.md](ColoredPetriNets.md), [LabeledTransitionSystems.md](LabeledTransitionSystems.md)
and [mCRL2.md](mCRL2.md).

All definitions on this page are taken from Chapter 2 (*Mathematical preliminaries*)
of the thesis *Model checking for analysis of BPMN models* (N. van Uden, TU/e, 2025).

---

## 1. Bags

**Definition 1 (Bag).**
A **bag** $m$ over a non-empty set $S$ is a function $m : S \rightarrow \mathbb{N}$,
where for each $s \in S$, $m(s)$ is the number of appearances of $s$ in $m$, also called
the **coefficient** of $s$ in $m$.

Each unique item in a bag is written with its *coefficient*. So, the bag containing only
the number 1 occurring three times is written as $\{3`1\}$.

### 1.1 Operations

**Membership**, **addition**, **comparison**, **size**, **summation** and **subtraction**
are defined as follows, where $m$ and $m_i$ for all $i \in \mathbb{N}$, are bags over $S$:

1. $\forall s \in S : s \in m \Leftrightarrow m(s) > 0$
2. $\forall s \in S : (m_1 \cup m_2)(s) = m_1(s) + m_2(s)$
3. $m_1 \subseteq m_2 \Leftrightarrow \forall s \in S : m_1(s) \leq m_2(s)$
4. $|m| = \sum_{s \in S} m(s)$
5. $\forall s \in S : \left( \bigcup_{i \in \mathbb{N}} m_i \right)(s) = \sum_{i \in \mathbb{N}} m_i(s)$
6. $\forall s \in S : (m_1 \setminus m_2)(s) = \max(0,\, m_1(s) - m_2(s))$

### 1.2 Notation

| Notation | Meaning |
| --- | --- |
| $S_{\mathrm{MS}}$ | The set of all bags over $S$ |
| $\emptyset_{\mathrm{MS}}$ | The bag containing no elements |
| $\{n`s\}$ | The bag in which $s$ has coefficient $n$ |

---

## 2. Expressions

In the definitions of the mathematical formalisms in this project, data expressions are
modeled. Thus, we assume that the tools in which the mathematical formalisms are modeled,
provide an expression language.

| Notation | Meaning |
| --- | --- |
| $\mathrm{EXPR}$ | The set of expressions provided by the expression language |
| $\mathrm{Type}[e]$ | The type of an expression $e \in \mathrm{EXPR}$ |
| $\mathrm{Type}[e] = C_{\mathrm{MS}}$ | The type of an expression whose evaluation results in multiple values of type $C$ in a bag |
| $\mathrm{VAR}[e]$ | The set of free variables in an expression $e \in \mathrm{EXPR}$ |
| $\mathrm{EXPR}_V$ | The set of expressions $e \in \mathrm{EXPR}$ such that $\mathrm{VAR}[e] \subseteq V$, for a set of variables $V$ |

---

## 3. Bindings and evaluation

**Definition 2 (Binding).**
A **binding** of a set of variables $V$ is a function $b$ that maps each variable
$v \in V$ to a concrete value $b(v)$ with type $\mathrm{Type}[v]$.
The set of all bindings for a set of variables $V$ is denoted by $B[V]$.

Using a binding, the value of an expression with free variables can be evaluated. This is
done by replacing the free variables with the value assigned by the binding and evaluating
the expression with the concrete values. Evaluating an expression $e$ with binding $b$ is
denoted by $e\langle b \rangle$.

**Example 1.**
Consider the set of variables $V = \{n, m\}$, with expression $n + 3 \leq m * 5$.
With binding $\langle n = 9, m = 2 \rangle$, the expression can be evaluated as follows:

$$
\begin{aligned}
(n + 3 \leq m * 5)\langle n = 9, m = 2 \rangle &= 9 + 3 \leq 2 * 5 \\
&= \textit{False}
\end{aligned}
$$

---

## Where these definitions are used

- Bags are used to define the **colors of places**, **arc expressions** and the **marking**
  of a Colored Petri Net, and to define the **state** of the Linear Process Equation that a
  CPN is translated to. See [ColoredPetriNets.md](ColoredPetriNets.md) and [mCRL2.md](mCRL2.md).
- Expressions and bindings are used for the **guards**, **arc expressions** and
  **initialization function** of a Colored Petri Net, and for the **conditions** and
  **next-state functions** of a Linear Process Equation.

---

## Sources

Definitions 1 and 2 are stated in Chapter 2 of the thesis without a citation. The
works below are the sources the thesis uses for the formalisms these definitions serve.

- [3] K. Jensen and L. M. Kristensen, *Coloured Petri Nets: Modelling and Validation of
  Concurrent Systems*. Springer Publishing Company, Incorporated, 1st ed., 2009.
- [8] J. F. Groote and M. R. Mousavi, *Modeling and Analysis of Communicating Systems*.
  The MIT Press, 08 2014.
