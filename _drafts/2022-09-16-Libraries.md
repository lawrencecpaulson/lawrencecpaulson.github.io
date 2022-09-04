---
layout: post
title:  "Porting Libraries of Mathematics Between Proof Assistants"
usemathjax: true 
tags: [general, Isabelle, Archive of Formal Proofs, HOL system, Coq]
---

eating own dog food
not making phd students eat your dog food


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

2004

* Proof import: new image HOL4 contains the imported library from
  the HOL4 system with about 2500 theorems. It is imported by
  replaying proof terms produced by HOL4 in Isabelle. The HOL4 image
  can be used like any other Isabelle image.  See
  HOL/Import/HOL/README for more information.

2012

* Session HOL-Import: Re-implementation from scratch is faster,
simpler, and more scalable.  Requires a proof bundle, which is
available as an external component.  Discontinued old (and mostly
dead) Importer for HOL4 and HOL Light.  

Aaron Coble arrived in 2005, after the HOL4 import, never attempted
