# Bisimilarity

To show that the same behavior can be observed from a CPN model as an LPE that is obtained
after translating the CPN model as specified in Definition 14, we prove that the underlying
[LTSs](LabeledTransitionSystems.md) are **bisimilar**.

This page contains Definitions 16 and 17 and Theorem 1 from Section 5.3
(*Semantics and equivalence*) of the thesis *Model checking for analysis of BPMN models*
(N. van Uden, TU/e, 2025).

Prerequisites:

- The reachability graph of a CPN (Definition 9) — [ColoredPetriNets.md](ColoredPetriNets.md)
- The translation from CPN to LPE (Definition 14) and the semantics of an LPE (Definition 15)
  — [mCRL2.md](mCRL2.md)
- Bindings and evaluation — [CommonDefinitions.md](CommonDefinitions.md)

---

## 1. Bisimulation

**Definition 16 (Bisimulation [8]).**
Let $A = (S, L, \rightarrow, s_0)$, and $A' = (S', L', \rightarrow', s_0')$ be two LTSs.
A binary relation $R \subseteq S \times S'$ is called a **bisimulation relation** if and only
if for any two states $s \in S$ and $s' \in S'$ and action $a$:

1. if $s \xrightarrow{a} u$ and $sRs'$ then there exists a state $u' \in S'$ such that
   $s' \xrightarrow{a} u'$ and $uRu'$, and
2. if $s' \xrightarrow{a} u'$ and $sRs'$ then there exists a state $u \in S$ such that
   $s \xrightarrow{a} u$ and $uRu'$.

Two states $s$ and $s'$ are **bisimilar**, denoted by $s \underline{\leftrightarrow} s'$, if
and only if there exists a bisimulation relation $R$, such that $sRs'$. Two LTSs are
bisimilar if and only if their initial states are bisimilar.

---

## 2. The relation between a CPN and its translation

**Definition 17.**
For a reachability graph $LTS = (S, L, \rightarrow, s_0)$ of a CPN
$(P, T, A, \Sigma, V, C, E, G, I)$, and the induced LTS $LTS' = (S', L', \rightarrow', s_0')$
of an LPE resulting from the translation as defined in Definition 14, introduce a relation
$R \subseteq S \times S'$ as follows:

$$R = \{ (M, (M(p_1), \ldots, M(p_n))) \mid M \in S \} \qquad \text{for all } p_1, \ldots, p_n \in P$$

In words: a marking $M$ of the CPN is related to the state of the LPE that stores, for each
place $p_i$, the bag of tokens $M(p_i)$ that $M$ assigns to that place.

---

## 3. Theorem

**Theorem 1.**
For LTSs $LTS$ and $LTS'$, relation $R$, as defined in Definition 17, is a bisimulation
relation.

### Proof

To show that $R$ is a bisimulation relation for $LTS$ and $LTS'$, we will show that
conditions 1 and 2 from Definition 16 hold.

#### Condition 1 (CPN step can be matched by the LPE)

Assume that $(M, (M(p_1), \ldots, M(p_n))) \in R$ and that there exists a $t \in L$ such that
$M \xrightarrow{t} N$. Since $M \xrightarrow{t} N$, there exists a binding $b \in B(t)$ such
that $M \overset{(t,b)}{\twoheadrightarrow} N$. From that, the following holds:

- $G(t)\langle b \rangle = \textit{True}$,
- $\forall p \in pre(t) : E(p,t)\langle b \rangle \subseteq M(p)$, and
- $N(p) = (M(p) \setminus E(p,t)\langle b \rangle) \cup E(t,p)\langle b \rangle$, for all
  $p \in P$.

State $d = (M(p_1), \ldots, M(p_n))$ can match transition $t$ with to
$(N(p_1), \ldots, N(p_n))$ if and only if there exists a binding $b' \in B[H_t]$, such that
$c_t(d, h_t)\langle b' \rangle = \textit{True}$ and
$(N(p_1), \ldots, N(p_n)) = g_t(d, h_t)\langle b' \rangle$.

**a.** Since

$$
c_t(d, h_t)\langle b' \rangle
= \big(\forall p \in pre(t) : E(p,t)\langle b' \rangle \subseteq M(p)\big) \land G(t)\langle b' \rangle
$$

for $b' = b$, $c_t(d, h_t)\langle b' \rangle = \textit{True}$ holds.

**b.** And:

$$
\begin{aligned}
g_t(d, h_t)\langle b' \rangle
&= \big( (M(p_1) \setminus E(p_1,t)\langle b' \rangle) \cup E(t,p_1)\langle b' \rangle, \\
&\phantom{{}={}\big(} \ldots, (M(p_n) \setminus E(p_n,t)\langle b' \rangle) \cup E(t,p_n)\langle b' \rangle \big) \\
&= (N(p_1), \ldots, N(p_n)).
\end{aligned}
$$

Thus, $(M(p_1), \ldots, M(p_n)) \xrightarrow{t} (N(p_1), \ldots, N(p_n))$, and
$(N, (N(p_1), \ldots, N(p_n))) \in R$. So, for all $t$ and all $s$, for any $s'$ such that
$sRs'$: if $s \xrightarrow{t} u$, then there exists a $u'$ such that $s' \xrightarrow{t} u'$
and $s'Ru'$.

#### Condition 2 (LPE step can be matched by the CPN)

Assume that $(M, (M(p_1), \ldots, M(p_n))) \in R$ and that there exists a $t \in L$ such that
$(M(p_1), \ldots, M(p_n)) \xrightarrow{t} (N(p_1), \ldots, N(p_n))$. From this it follows that
there exists a binding $b \in B[H_t]$ such that:

- $c_t\big((M(p_1), \ldots, M(p_n)), h_t\big)\langle b \rangle = \textit{True}$, and
- $(N(p_1), \ldots, N(p_n)) = g_t\big((M(p_1), \ldots, M(p_n)), h_t\big)\langle b \rangle$

State $M$ can match transition $t$ to $N$ if and only if there exists a binding
$b' \in B(t)$ such that $M \overset{(t,b')}{\twoheadrightarrow} N$. To show that exists
a $b'$ such that $M \overset{(t,b')}{\twoheadrightarrow} N$ the following must hold:
$G(t)\langle b' \rangle = \textit{True}$,
$\forall p \in pre(t) : E(p,t)\langle b' \rangle \subseteq M(p)$, and
$N(p) = (M(p) \setminus E(p,t)\langle b' \rangle) \cup E(t,p)\langle b' \rangle$ for all
$p \in P$.

**a.** Since

$$
\begin{aligned}
c_t\big((M(p_1), \ldots, M(p_n)), h_t\big)\langle b \rangle
&= \big(\forall p \in pre(t) : E(p,t)\langle b \rangle \subseteq s_p\big) \\
&\phantom{{}={}} \land\; G(t)\langle b \rangle
\end{aligned}
$$

for $b' = b$ both $G(t)\langle b' \rangle = \textit{True}$ and
$\forall p \in pre(t) : E(p,t)\langle b' \rangle \subseteq M(p)$ hold.

**b.** Since:

$$(N(p_1), \ldots, N(p_n)) = g_t\big((M(p_1), \ldots, M(p_n)), h_t\big)\langle b \rangle$$

for $b' = b$, for all $p \in P$
$N(p) = (M(p) \setminus E(p,t)\langle b' \rangle) \cup E(t,p)\langle b' \rangle$.

So, $M \xrightarrow{t} N$, and $(N, (N(p_1), \ldots, N(p_n))) \in R$. Thus, for all $t$ and
all $s'$, for any $s$ such that $sRs'$: if $s' \xrightarrow{t} u'$, then there exists a $u$
such that $s \xrightarrow{t} u$ and $uRu'$.

#### Conclusion of the proof

Since both conditions of Definition 16 hold, $R$ is a bisimulation relation for LTSs $LTS$
and $LTS'$. $\qquad \square$

---

## 4. Bisimilarity of the two LTSs

The initial state of $LTS$ is $M_0$, and the initial state of $LTS'$ is $d_0$, where for
$p_1, \ldots, p_n \in P$, $d_0 = (M_0(p_1), \ldots, M_0(p_n))$, thus $M_0 R d_0$ and
$M_0 \underline{\leftrightarrow} s_0$. Since $R$ is a bisimulation relation for $LTS$ and
$LTS'$, and the initial state of $LTS$ is bisimilar to the initial state of $LTS'$,

$$LTS \underline{\leftrightarrow} LTS'$$

holds.

### Why this matters

Because the behavior of the CPN model and the mCRL2 specification is exactly the same,
properties checked using the mCRL2 specification hold **if and only if** they hold for the
BPMN models. This is what answers the first research question of the thesis: *"Can a correct
and efficient translation be defined from BPMN specifications to mCRL2 specifications to
allow for model checking?"*

---

## 5. Deviations from the thesis

The proof above is **corrected**. Six places in the printed proof state the enabledness and
occurrence conditions over the wrong set of places, with the wrong operator, or over the
wrong symbol. None of them affects the argument — the correct forms are used everywhere else
in the proof, and the result of Theorem 1 is unchanged — but they are inconsistent with
Definitions 6, 7 and 14. For reference, this is what the thesis prints:

| Location | As printed in the thesis | As corrected here | Per |
| --- | --- | --- | --- |
| Condition 1, second bullet | $\forall p \in post(t) : E(p,t)\langle b \rangle \subseteq M(p)$ | $\forall p \in pre(t) : \ldots$ | Definition 6.1 |
| Condition 1, third bullet | "for all $p \in pre(t)$" | "for all $p \in P$" | Definition 7 |
| Condition 1a | $\forall p \in P : E(p,t)\langle b' \rangle \in M(p)$ | $\forall p \in pre(t) : \ldots \subseteq M(p)$ | Definition 14 ($c_t$) |
| Condition 2, "the following must hold" | $\forall p \in P : E(p,t)\langle b' \rangle \subseteq M(p)$ | $\forall p \in pre(t) : \ldots$ | Definition 6.1 |
| Condition 2a, formula | $\forall p \in P : E(p,t)\langle b \rangle \in S_p$ | $\forall p \in pre(t) : \ldots \subseteq s_p$ | Definition 14 ($c_t$) |
| Condition 2a, conclusion | $\forall p \in P : E(p,t)\langle b' \rangle \subseteq M(p)$ | $\forall p \in pre(t) : \ldots$ | Definition 6.1 |

The last three rows were not among the spots flagged originally; they are the same defect in
the matching positions of Condition 2, corrected together with the rest so the two halves of
the proof stay symmetric.

---

## Sources

- [8] J. F. Groote and M. R. Mousavi, *Modeling and Analysis of Communicating Systems*.
  The MIT Press, 08 2014. *(Source of Definition 16.)*
- [9] B. Ploeger, J. Wesselink, and T. Willemse, "Verification of reactive systems via
  instantiation of parameterised boolean equation systems," *Information and Computation*,
  vol. 209, no. 4, pp. 637–663, 2011. *(Source of Definition 15, on which Definition 17
  depends.)*
