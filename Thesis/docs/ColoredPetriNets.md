# Colored Petri Nets (CPN)

Colored Petri Nets (CPNs) are an extension of Petri Nets (PN). CPNs can be used to model
and specify the behavior of concurrent systems [3]. The semantics of CPNs are well studied
and are used in the Matala project to define the semantics of BPMN models.

This page contains the syntax and semantics of Petri Nets and Colored Petri Nets as defined
in Chapter 3 of the thesis *Model checking for analysis of BPMN models*
(N. van Uden, TU/e, 2025).

Shared notation (bags, expressions, bindings) is defined in
[CommonDefinitions.md](CommonDefinitions.md). The semantics of a CPN is given as a
[Labeled Transition System](LabeledTransitionSystems.md).

---

## 1. Petri Nets

A Petri Net (PN) [3] is a mathematical formalism for modelling distributed systems, which
also supports a graphical notation. A PN is a bipartite directed graph, consisting of
**places** and **transitions**, together referred to as **nodes**. Places can be connected
with transitions, and transitions can be connected with places using **arcs**. Petri Nets
are abstract models of processes, where work items are processed by a sequence of events.

### 1.1 Syntax

**Definition 4 (Petri Net (PN)).**
A Petri Net is a triple $(P, T, A)$, where:

- $P$ is a finite set of **places**,
- $T$ is a finite set of **transitions** ($P \cap T = \emptyset$),
- $A \subseteq (P \times T) \cup (T \times P)$ is a set of **arcs** (flow relation).

### 1.2 Graphical notation

| Component | Drawn as |
| --- | --- |
| Place | Oval |
| Place containing a token | Oval with a dot |
| Transition | Rectangle |
| Flow relation | Arrow connecting a place and a transition |

Transitions represent the discrete events that take place in a process and tokens represent
the work items in the process and are visualized as dots in places. Arrows model how the
tokens move through the model.

The distribution of tokens over the places is called the **marking** and represents the
state of the model. As tokens represent the state, they are **not** part of the definition.

---

## 2. Colored Petri Nets

Colored Petri Nets extend Petri Nets with typed data. In a CPN, places are extended with a
type, called a **color**, and tokens carry typed data, where the type of a token is the same
as the type of the place the token is located in. Transitions can have **guards** based on
the data stored in tokens, and **update expressions** to manipulate the data.

> It is assumed that the set of colors of a CPN contains at least the type `Bool`, representing the booleans.

### 2.1 Syntax

**Definition 5 (Colored Petri Net (CPN) [3]).**
A CPN is a tuple $(P, T, A, \Sigma, V, C, E, G, I)$, where:

- $(P, T, A)$ is a Petri Net,
- $\Sigma$ is a finite set of **colors**,
- $V$ is a finite set of typed **variables**, such that $\mathrm{Type}[v] \in \Sigma$ for all
  variables $v \in V$,
- $C : P \rightarrow \Sigma$ is a function that assigns a **color to each place**,
- $G : T \rightarrow \mathrm{EXPR}_V$ is a **guard function** that assigns a guard to each
  transition $t$ such that $\mathrm{Type}[G(t)] = \textit{Bool}$,
- $E : A \rightarrow \mathrm{EXPR}_V$ is an **arc expression function** that assigns an
  expression to each arc $a$ such that $\mathrm{Type}[E(a)] = C(p)_{\mathrm{MS}}$, where $p$
  is the place connected to the arc $a$,
- $I : P \rightarrow \mathrm{EXPR}_{\emptyset}$ is an **initialization function** that assigns
  an initialization expression to each place $p$ such that
  $\mathrm{Type}[I(p)] = C(p)_{\mathrm{MS}}$.

> Note that the type of an arc expression $e$ is equal to the bag of the color of the place $p$ the arc expression is connected to, i.e., $\mathrm{Type}[e] = C(p)_{\mathrm{MS}}$. This means that evaluating an arc expression can result in a bag of values, where the type of all those values is equal to the color of the place the arc is connected to.

### 2.1.1 Convention: arc expressions of non-existing arcs

$E$ is defined only on $A$, but the semantics evaluate $E$ on arbitrary place/transition
pairs: Definition 7 uses both $E(p,t)$ and $E(t,p)$ **for all $p \in P$**, including places
that are not connected to $t$. To make those expressions total, the following convention is
used:

$$E(a)\langle b \rangle = \emptyset_{\mathrm{MS}} \qquad \text{for all } a \notin A \text{ and any binding } b$$

That is, an arc that does not exist evaluates to the empty bag, so it neither consumes nor
produces tokens. With this convention, for a transition $t$ and a place
$p \notin pre(t) \cup post(t)$, Definition 7 reduces to:

$$M'(p) = (M(p) \setminus \emptyset_{\mathrm{MS}}) \cup \emptyset_{\mathrm{MS}} = M(p)$$

i.e. places not connected to $t$ keep their marking when $t$ occurs.

> **Addition to the thesis.** This convention is not stated in the thesis; it closes a gap in Definition 7, which applies $E$ to pairs that need not be in $A$.

### 2.2 Graphical notation

The graphical notation of Colored Petri Nets is the same as the notation for Petri Nets,
with the colors, guards, expressions, and initialization function shown as annotations in
the model:

- the **initialization** expression $I(p)$ is written next to the place $p$;
- the **color** $C(p)$ is written under the place $p$;
- the **arc expressions** $E(a)$ are written next to the arcs;
- the **guard** $G(t)$ is written under the transition $t$.

**Example 3.**
A CPN in which the initial marking of place $P_1$ contains a token with value 1.
Transition $T_1$ consumes a token from place $P_1$ and produces a token in $P_2$ with the
value of the token consumed from $P_1$ incremented by one. If the value of the token in
$P_2$ is less than or equal to three, $T_2$ consumes a token from $P_2$ and produces a token
in $P_1$ with the same value. If the value of the token in $P_2$ is greater than three, $T_3$
consumes a token from $P_2$ and produces a token in $P_3$ with the same value.

| Element | Annotation |
| --- | --- |
| $I(P_1)$ | $\{1`1\}$ |
| $C(P_1) = C(P_2) = C(P_3)$ | `INT` |
| $E(P_1, T_1)$ | $\{1`n\}$ |
| $E(T_1, P_2)$ | $\{1`(n+1)\}$ |
| $G(T_2)$ | $n \leq 3$ |
| $G(T_3)$ | $n > 3$ |

---

## 3. Semantics

For a Colored Petri Net $CPN = (P, T, A, \Sigma, V, C, E, G, I)$, the following concepts are
defined.

### 3.1 Preset, postset and marking

- The **preset** of a transition $t$, denoted by $pre(t)$, is the set of all places that have
  an outgoing arc to $t$:
  $$pre(t) = \{ p \in P \mid (p, t) \in A \}$$
- The **postset** of a transition $t$, denoted by $post(t)$, is the set of all places that
  have an incoming arc from $t$:
  $$post(t) = \{ p \in P \mid (t, p) \in A \}$$
- Similarly as for a PN, the distribution of tokens over the places is called the
  **marking** and represents the state of the model. Formally, the marking is a function $M$
  that maps each place $p \in P$ to a bag of tokens such that $M(p) \in C(p)_{\mathrm{MS}}$.
- The **initial marking** $M_0$ is defined by $M_0(p) = I(p)\langle\rangle$ for all $p \in P$.

### 3.2 Variables, bindings and binding elements

The execution of a CPN is based on the occurring of transitions. Informally, a transition is
**enabled** if each of the places in the preset of the transition contain tokens, and with
the data in the tokens the guard of the transition is satisfied. If a transition is enabled,
it can **occur** and consume tokens from the places in the preset of the transition and
produce new tokens in the places in the postset of the transition, according to the arc
expressions. Arc expressions and guards consist of free variables and in order to assign
values to these free variables, bindings are used.

The **variables of a transition** $t \in T$ are denoted by $\mathrm{Var}(t) \subseteq V$
where:

$$
\mathrm{Var}(t) = \mathrm{VAR}[G(t)] \;\cup\;
\bigcup_{p \in pre(t)} \mathrm{VAR}[E(p,t)] \;\cup\;
\bigcup_{p \in post(t)} \mathrm{VAR}[E(t,p)]
$$

and consist of the free variables appearing in the guard of $t$ and in the arc expressions of
the arcs connected to $t$.

- A **binding** of a transition $t \in T$ is a binding for all free variables in $t$. The set
  of all bindings for a transition $t$ is denoted by the shorthand
  $B(t) = B[\mathrm{Var}(t)]$.
- A **binding element** is a pair $(t, b)$ such that $t \in T$ and $b \in B(t)$.

### 3.3 Enabledness and occurrence

**Definition 6 (Enabled binding element).**
A binding element $(t, b)$ is **enabled** in marking $M$, if and only if the following two
properties are satisfied:

1. $\forall p \in pre(t) : E(p,t)\langle b \rangle \subseteq M(p)$
2. $G(t)\langle b \rangle = \textit{True}$

**Definition 7 (Occurring binding element).**
When binding element $(t, b)$ is enabled in marking $M$, it may **occur**, leading to marking
$M'$, defined by:

$$M'(p) = \big(M(p) \setminus E(p,t)\langle b \rangle\big) \cup E(t,p)\langle b \rangle \quad \text{for all } p \in P$$

Since this ranges over **all** $p \in P$, it applies $E$ to pairs $(p,t)$ and $(t,p)$ that
need not be arcs of the net. Those are read using the convention of
[§2.1.1](#211-convention-arc-expressions-of-non-existing-arcs):
$E(a)\langle b \rangle = \emptyset_{\mathrm{MS}}$ for $a \notin A$, so places outside
$pre(t) \cup post(t)$ are left unchanged.

**Example 4.**
Consider the CPN of Example 3. The free variables in $t_1$ are
$\mathrm{Var}(t_1) = \{n\}$, thus for $t_1$, $b = \langle n = 1 \rangle$ is a valid binding.

$$
\begin{aligned}
G(t_1)\langle n = 1 \rangle &= \textit{True}\langle n = 1 \rangle = \textit{True} \\
E(p_1, t_1)\langle n = 1 \rangle &= (\{1`n\})\langle n = 1 \rangle = \{1`1\} \\
E(t_1, p_2)\langle n = 1 \rangle &= (\{1`(n+1)\})\langle n = 1 \rangle = \{1`(1+1)\} = \{1`2\}
\end{aligned}
$$

Thus, for binding $b$, $G(t_1)\langle b \rangle = \textit{True}$ and
$E(p_1,t_1)\langle b \rangle \subseteq M(p_1)$, so it is enabled and can occur. After it has
occurred, the new markings are:

$$
\begin{aligned}
M(p_1) \setminus E(p_1, t_1) &= \{1`1\} \setminus \{1`1\} = \emptyset_{\mathrm{MS}} \\
M(p_2) \cup E(t_1, p_2) &= \emptyset_{\mathrm{MS}} \cup \{1`2\} = \{1`2\}
\end{aligned}
$$

### 3.4 Reachability

When a CPN has marking $M$ and the binding element $(t, b)$ occurs, resulting in marking
$M'$, as specified in Definition 7, we say that $M'$ is **directly reachable** from $M$, and
denote this as:

$$M \overset{(t,b)}{\twoheadrightarrow} M' \qquad \text{or} \qquad M \twoheadrightarrow M'$$

The latter only indicates that *a* binding element can occur from marking $M$ to $M'$.

**Definition 8 (Reachability).**
A marking $M'$ is **reachable** from marking $M$ if there exist zero or more markings $M_1$
to $M_n$, such that:

$$M \twoheadrightarrow M_1 \twoheadrightarrow \ldots \twoheadrightarrow M_n \twoheadrightarrow M'$$

The set of all reachable markings from $M$ is denoted by $\mathcal{R}(M)$.

### 3.5 Reachability graph

From a CPN a reachability graph as an [LTS](LabeledTransitionSystems.md), see Definition 3,
can be computed. With the reachability graph the behavior of a CPN can be compared with
other modelling formalisms.

**Definition 9 (Reachability graph of a CPN).**
The reachability graph of a CPN $(P, T, A, \Sigma, V, C, E, G, I)$ with initial marking
$M_0$, is an LTS $(S, L, \rightarrow, s_0)$ s.t.:

$$
\begin{aligned}
S \;&=\; \{M_0\} \cup \mathcal{R}(M_0) \\[4pt]
L \;&=\; T \\[4pt]
\rightarrow \;&=\; \left\{ (M, t, M') \in S \times T \times S \;\middle|\; \exists b \in B(t) : M \overset{(t,b)}{\twoheadrightarrow} M' \right\} \\[4pt]
s_0 \;&=\; M_0
\end{aligned}
$$

> **Deviation from the thesis.** The thesis quantifies the transition relation over $\mathcal{R}(M_0) \times T \times \mathcal{R}(M_0)$; corrected to $S \times T \times S$ above. See [§3.5.1](#351-why-the-transition-relation-ranges-over-s) for why.

#### 3.5.1 Why the transition relation ranges over $S$

Under Definition 8, a marking is reachable from $M$ only via **one or more** occurrence
steps: the chain $M \twoheadrightarrow M_1 \twoheadrightarrow \ldots \twoheadrightarrow M_n \twoheadrightarrow M'$ always contains at least the final step, and the "zero or more" refers
to the intermediate markings $M_1 \ldots M_n$. So $\mathcal{R}$ is **not** reflexive:
$M_0 \in \mathcal{R}(M_0)$ only if $M_0$ lies on a cycle. This is exactly why Definition 9
adds $M_0$ to $S$ separately — if $\mathcal{R}(M_0)$ already contained $M_0$, that union would
be redundant.

Given that, restricting $\rightarrow$ to $\mathcal{R}(M_0) \times T \times \mathcal{R}(M_0)$
drops every transition **out of** $M_0$ whenever $M_0 \notin \mathcal{R}(M_0)$: the pair
starts at a state that the product does not range over. The initial state would then be
isolated, with $s_0$ having no outgoing transitions at all.

The CPN of Example 3 shows this: $M_0 = (\{1`1\}, \emptyset_{\mathrm{MS}}, \emptyset_{\mathrm{MS}})$ is never revisited, so $M_0 \notin \mathcal{R}(M_0)$ and the
$T_1$ step leaving $s_0$ would be missing from $\rightarrow$ — the reachability graph of
Example 5 would fall apart into an isolated $s_0$ plus a six-state chain.

Ranging over $S$ instead is also **complete**: $S$ is closed under $\twoheadrightarrow$,
since any marking directly reachable from a marking in $S$ is by Definition 8 in
$\mathcal{R}(M_0) \subseteq S$. So $S \times T \times S$ adds no spurious states and loses
no transitions.

**Example 5.**
For the CPN of Example 3, the reachability graph is a linear LTS with seven states:

$$s_0 \xrightarrow{\;T_1\;} \cdot \xrightarrow{\;T_2\;} \cdot \xrightarrow{\;T_1\;} \cdot \xrightarrow{\;T_2\;} \cdot \xrightarrow{\;T_1\;} \cdot \xrightarrow{\;T_3\;} \cdot$$

Following the markings: $P_1 = \{1`1\}$; after $T_1$, $P_2 = \{1`2\}$; after $T_2$,
$P_1 = \{1`2\}$; after $T_1$, $P_2 = \{1`3\}$; after $T_2$, $P_1 = \{1`3\}$; after $T_1$,
$P_2 = \{1`4\}$. At that point $G(T_2) = n \leq 3$ is no longer satisfied and
$G(T_3) = n > 3$ is, so $T_3$ occurs and $P_3 = \{1`4\}$.

> **Deviation from the thesis.** Figure 3.4 in the thesis draws this reachability graph with an additional $T_2$ step, as $T_1\,T_2\,T_1\,T_2\,T_1\,T_2\,T_3$ (eight states). That extra $T_2$ cannot occur: after the third $T_1$ the token in $P_2$ has value 4, which violates the guard $n \leq 3$ of $T_2$. The trace above is the corrected one.

---

## 4. Relation to the other formalisms

- **BPMN.** In the Matala project the semantics of BPMN models are defined in terms of a
  mapping to Colored Petri Nets. Only **non-hierarchical** Petri Nets are considered; the
  swimlanes of a BPMN model are ignored in the CPN. Tasks in a BPMN model are modeled as
  labeled transitions, control nodes such as gateways as silent transitions in combination
  with places, and data stores and message queues as places. For a formal definition of the
  mapping from BPMN to Colored Petri Nets, see [7].
- **mCRL2.** A CPN is translated to a Linear Process Equation for model checking; the
  translation and the proof that both describe the same behavior are described in
  [mCRL2.md](mCRL2.md) and [Bisimiliarity.md](Bisimiliarity.md).

---

## Sources

- [3] K. Jensen and L. M. Kristensen, *Coloured Petri Nets: Modelling and Validation of
  Concurrent Systems*. Springer Publishing Company, Incorporated, 1st ed., 2009.
  *(Source of Definition 4 and Definition 5.)*
- [7] R. Dijkman, M. Dumas, and C. Ouyang, *Formal semantics and automated analysis of BPMN
  process models*. Technical Report Preprint, Queensland University of Technology, 2007.
  *(Source of the mapping from BPMN to Colored Petri Nets.)*
