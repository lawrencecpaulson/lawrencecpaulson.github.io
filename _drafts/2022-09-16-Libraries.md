---
layout: post
title:  "Porting Libraries of Mathematics Between Proof Assistants"
usemathjax: true 
tags: [general, Isabelle, Archive of Formal Proofs, HOL system, Coq]
---

The value of a proof assistant today is to a large extent determined by its libraries:
[Mathematical Components](https://math-comp.github.io)
for [Coq](https://coq.inria.fr), among others; 
[mathlib](https://leanprover-community.github.io) for
[Lean](https://leanprover.github.io);
the [Archive of Formal Proofs](https://www.isa-afp.org)
for [Isabelle](https://isabelle.in.tum.de).
The [Mizar](http://mizar.org) system has a remarkable mathematical language, but for many researchers the real attraction was its huge and diverse library.
Similarly, John Harrison's [HOL Light](https://www.cl.cam.ac.uk/~jrh13/hol-light/) is equipped with large libraries: 
a [formalisation of Euclidean spaces](https://rdcu.be/cJtGW) 
and formal proofs of many of the ["top 100 theorems"](https://www.cs.ru.nl/~freek/100/).
Wasteful duplication? Can we usefully migrate material from one system to another?
