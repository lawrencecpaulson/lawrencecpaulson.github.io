---
layout: post
title:  "Is Zermelo-Fraenkel set theory the foundation of mathematics?"
usemathjax: true 
tags: logic, set theory, axiom of choice
---

Set theory (specifically, ZFC) is said to be the foundation of mathematics. So why isn't it used to formalise mathematics?
How do our various typed formalisms compare to set theory?

### Historical background

Zermelo introduced his axioms for set theory in 1908 as his response to concerns about the foundations of mathematics. These included the notorious axiom of choice in addition to more mundane axioms asserting our ability to form finite sets, take unions and power sets and to specify subsets of an existing set. Finally, the axiom of infinity guarantees the existence of an infinite set.

Remarkably, a form of Zermelo set theory turns out to be equally expressive as higher-order logic. Also notable is that the authors of Bourbaki chose Zermelo set theory as the foundation of their entire project. (This fact was indignantly pointed out by Adrian Matthias.)
Therefore we can safely conclude that Zermelo set theory is perfectly adequate for the vast bulk of "ordinary" mathematics.

What is the exception? Crudely put, the most obvious exception to this rule is set theory itself. Georg Cantor created a paradise of ordinal and cardinal arithmetic that goes well beyond the confines of Zermelo set theory. To reach this paradise, we need the axiom of replacement, a sort of set teleportation device: any set can be copied to a "higher level". Finally, the axiom of foundation became necessary to conform to the idea that sets emerged through an iterative construction.


 Bernays-Gödel and resolution experiments?
 
 hereditarily finite set theory
 
 Zermelo set theory
 
 ZF set theory
 
 [axiom of choice]({% 2021-11-10-Axiom_of_Choice %})
 
 Isabelle/ZF and recent work on forcing
 
 Encoding set theory in type theory for work in Lean and Coq


> Gregory H. Moore, *Zermelo's Axiom of Choice* (Springer, 1982), 64--65.

I