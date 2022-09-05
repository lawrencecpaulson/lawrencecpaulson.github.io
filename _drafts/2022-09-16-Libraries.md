---
layout: post
title:  "Porting Libraries of Mathematics Between Proof Assistants"
usemathjax: true 
tags: [general, Isabelle, Archive of Formal Proofs, HOL system, Coq]
---

In 2005, a student arrived who wanted to do PhD involving formalised probability theory.
I advised him to use HOL4, where theories of Lebesgue integration and probability theory had already been formalised; they were not available in Isabelle/HOL.
Ironically, he eventually discovered that the HOL4 theories didn't meet his requirements and he was forced to redo them.
This episode explains why I have since devoted so much effort to porting libraries into Isabelle/HOL.
But note: Isabelle/HOL already had, from 2004, a *full copy* of the HOL4 libraries, translated by importer tools.
I even never thought of using these libraries, and they were withdrawn in 2012.
What is the right way to achieve interoperability between proof assistant libraries?

### Proof assistants and their libraries

The importance of a proof assistant is to a large extent determined by its libraries:

* [Mathematical Components](https://math-comp.github.io)
(among others) for [Coq](https://coq.inria.fr); 
* [mathlib](https://leanprover-community.github.io) for
[Lean](https://leanprover.github.io);
* the [Archive of Formal Proofs](https://www.isa-afp.org)
for [Isabelle](https://isabelle.in.tum.de).
* John Harrison's [Euclidean spaces](https://rdcu.be/cJtGW) 
and ["top 100 theorems"](https://www.cs.ru.nl/~freek/100/)
for [HOL Light](https://www.cl.cam.ac.uk/~jrh13/hol-light/) 
* Although [Mizar](http://mizar.org) introduced a groundbreaking mathematical language, for many researchers the real attraction was its huge library.

The wastefulness of having so much of the same mathematics formalised multiple times attracted many people's notice.
The proprietors of newer systems were naturally covetous of the large libraries of older systems (which obscured their obsolescence). This feeling was particularly strong among the various implementations of higher-order logic, one single formalism if we can ignore the various bells and whistles attached by each of the implementations.
Powerful and efficient importers were built, but they didn't catch on. Despite that, research in this area continues.

I am not optimistic for the prospects of this sort of proof porting, for a simple reason: the proofs themselves are important. All the effort in this area that I have seen involves finding a common formalism to unify two different proof assistants and through that to emulate proofs in one system using proofs in the other. Ideally, corresponding more basic libraries (e.g. of the natural numbers) are identified rather than translated.
Still, the best one can hope for is a list of statements certified by the importer as having been proved somewhere else.
People don't seem to want this. They want actual proofs they can read.

### Porting proofs from HOL Light to Isabelle/HOL

I spent a lot of time between 2015 and 2017 porting material from the HOL Light libraries.
It might seem an odd use of my time. I had spent years away from Isabelle working on MetiTarski and then returned to Isabelle to prove Gödel's incompleteness theorems.



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


(While we should eat our own dog food, we shouldn't force it on our students without compelling reasons.)
