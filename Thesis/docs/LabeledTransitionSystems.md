# Labeled Transition Systems (LTS)

Definition 3 is taken from Chapter 2 (*Mathematical preliminaries*) of the thesis
*Model checking for analysis of BPMN models* (N. van Uden, TU/e, 2025).

A Labeled Transition System (LTS) is a formal model for describing behavior. An LTS is a
directed graph, consisting of states and arcs with action names.

The LTS is the common semantic domain of this project: the semantics of a
[Colored Petri Net](ColoredPetriNets.md) is an LTS (its reachability graph), and the
semantics of an [mCRL2 Linear Process Equation](mCRL2.md) is an LTS (its induced LTS).
Comparing these two LTSs is what makes it possible to relate a CPN model and its
translation, see [Bisimiliarity.md](Bisimiliarity.md).

Shared notation used on this page is defined in [CommonDefinitions.md](CommonDefinitions.md).

---

## 1. Syntax

**Definition 3 (Labeled Transition System (LTS)).**
A Labeled Transition System (LTS) is a four tuple $(S, L, \rightarrow, s_0)$ where

- $S$ is a possibly infinite set of **states**,
- $L$ is a possibly infinite set of **actions**,
- $\rightarrow \;\subseteq\; S \times L \times S$ is a **transition relation**, and
- $s_0 \in S$ is the **initial state**.

### 1.1 Notation

We denote $(s, t, s') \in \rightarrow$ as

$$s \xrightarrow{\;t\;} s'$$

### 1.2 Graphical notation

An LTS is drawn as a directed graph. States are drawn as circles and transitions are drawn
as arrows annotated with the action name. The initial state is shown in green.

---

## 2. Semantics

An LTS *is* the behavioral model; the behavior it describes is the set of paths through the
graph, starting from the initial state $s_0$, where each step $s \xrightarrow{t} s'$ is
labeled with the action $t$ that is performed.

**Example 2.**
Consider the LTS representing a simple coffee and tea machine, with four states
$s_0$, $s_1$, $s_2$, and $s_3$ and the labeled transitions *coin*, *coffee*, *tea*, and
*dispense*. After inserting a coin, the machine gives the choice between coffee and tea,
then the machine dispenses the coffee or tea and goes back to the initial state.

$$
\begin{aligned}
s_0 &\xrightarrow{\;coin\;} s_1 \\
s_1 &\xrightarrow{\;coffee\;} s_2 \\
s_1 &\xrightarrow{\;tea\;} s_3 \\
s_2 &\xrightarrow{\;dispense\;} s_0 \\
s_3 &\xrightarrow{\;dispense\;} s_0
\end{aligned}
$$

---

## 3. LTSs produced by the other formalisms

| Formalism | LTS | Defined in |
| --- | --- | --- |
| Colored Petri Net | Reachability graph of a CPN (Definition 9) | [ColoredPetriNets.md](ColoredPetriNets.md) |
| mCRL2 Linear Process Equation | Semantics of an LPE (Definition 15) | [mCRL2.md](mCRL2.md) |

Properties in the modal $\mu$-calculus are defined over an LTS; see
[mCRL2.md](mCRL2.md).

---

## Sources

Definition 3 is stated in the thesis without a citation. The following works are the
sources used in the thesis for the material that builds directly on the LTS
(bisimulation, the $\mu$-calculus over an LTS, and the LTS induced by an LPE):

- [8] J. F. Groote and M. R. Mousavi, *Modeling and Analysis of Communicating Systems*.
  The MIT Press, 08 2014.
- [9] B. Ploeger, J. Wesselink, and T. Willemse, "Verification of reactive systems via
  instantiation of parameterised boolean equation systems," *Information and Computation*,
  vol. 209, no. 4, pp. 637–663, 2011.
