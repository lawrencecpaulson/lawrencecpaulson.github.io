---
layout: post
title:  "BDDs in HOL: the coolest thing Mike Gordon ever did"
usemathjax: true 
tags: [HOL system, BDDs, MJC Gordon]
---

22 August 2022 marks five years since the death of Mike Gordon, who all but invented hardware verification, made major contributions to proof assistant architecture and showed that higher-order logic was a powerful formalism for verification.
My [biography](http://doi.org/10.1098/rsbm.2018.0019) (also available [here](https://arxiv.org/abs/1806.04002)) describes his main achievements.
But it is almost silent about the coolest thing he ever did: integrating binary decision diagrams (BDDs) with the HOL system.

### Binary decision diagrams (and model checking)

[*Binary decision diagrams*](https://en.wikipedia.org/wiki/Binary_decision_diagram) are a data structure that can represent Boolean formulas compactly and operate on them efficiently.
Each diagram is a decision tree—[dag](https://en.wikipedia.org/wiki/Directed_acyclic_graph), to be precise, because of identical subtrees are shared—embodying
all possible sequences of decisions on the Boolean variables, 
subject to some fixed ordering, ρ.
For a given ρ, the BDD corresponding to a formula is the same for all logically equivalent formulas, regardless of their syntactic form.
A BDD can more properly be regarded as representing a boolean *function* as opposed to a formula.
Converting a formula to a BDD yields a *canonical form* for this function.

Invented in 1986, BDDs were originally used to verify hardware designs, proving agreement between specification and implementation for combinational hardware devices such as adders.
Crucially, in the event of non-agreement, they exhibited counterexamples.
[The original paper](https://doi.org/10.1109/TC.1986.1676819) described experiments involving numerous devices and included a proof that binary multiplication could not be represented efficiently.

[Model checking](https://doi.org/10.1145/5397.5399) is a verification technique based on state enumeration, supporting a temporal logic and ideally suited for checking properties of concurrent systems.
Initially, they had to be reduced by abstraction to a fairly small number of states.
But in 1990, a breakthrough paper appeared: "[Symbolic model checking: $10^{20}$ states and beyond](https://doi.org/10.1109/LICS.1990.113767)".
Thanks to BDDs, model checkers could be turbocharged.

By the mid-1990s, these two powerul, fully automatic technologies were making interactive theorem provers look distinctly feeble.
What to do?

### BDDs in HOL

In his paper "[Reachability Programming in HOL98 Using BDDs](https://rdcu.be/cROox)"

PVS, no!
