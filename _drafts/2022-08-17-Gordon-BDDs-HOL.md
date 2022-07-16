---
layout: post
title:  "BDDs in HOL: the coolest thing Mike Gordon ever did?"
usemathjax: true 
tags: [HOL system, BDDs, MJC Gordon]
---

22 August 2022 marks five years since the death of Mike Gordon, who all but invented hardware verification, made major contributions to proof assistant architecture to his work on LCF, and gave higher-order logic the prominence it has today.
My [biography](http://doi.org/10.1098/rsbm.2018.0019) (also available [here](https://arxiv.org/abs/1806.04002)) describes his main achievements.
But there I said almost nothing about the coolest thing he did: integrating BDDs with the HOL system.

[Binary decision diagrams](https://en.wikipedia.org/wiki/Binary_decision_diagram) are a data structure that can represent Boolean formulas compactly and operate on them efficiently.
Each diagram is a decision tree—[dag](https://en.wikipedia.org/wiki/Directed_acyclic_graph), to be precise, because of identical subtreees are shared—embodying
all possible sequences of decisions on the Boolean variables, 
subject to some fixed ordering, ρ.
For a given ρ, the BDD corresponding to a formula is the same for all logically equivalent formulas, regardless of their syntactic form.
In other words, converting a formula to a BDD yields a *canonical form* and conversion from a Boolean formula to a BBD is a canonicalisation algorithm.

BDDs were originally
[symbolic model checking](https://doi.org/10.1109/LICS.1990.113767)

In his paper "[Reachability Programming in HOL98 Using BDDs](https://rdcu.be/cROox)"

PVS, no!
