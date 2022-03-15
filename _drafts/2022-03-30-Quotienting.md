---
layout: post
title:  "Equivalence classes and quotienting"
usemathjax: true 
tags: quotient constructions
---

A quotient construction is when a set is partitioned according to an equivalence relation. The members of the partition — known as equivalence classes — are sets of equivalent elements. To use computer science jargon, the construction yields an *abstract type* (the members of the partition) and the elements of those members, sometimes called representatives, belong to an underlying *concrete type*.
For example, pairs of natural numbers can represent integers or nonnegative rationals, depending on the equivalence relation chosen.
However, quotienting has nothing to do with types.

### Some basic definitions

Having set out to write this blog post, I was dismayed to read my own (2006) paper on the topic:

> A quotient construction defines an abstract type from a concrete type, using an equivalence relation to identify elements of the concrete type that are to be regarded as indistinguishable. The elements of a quotient type are equivalence classes: sets of equivalent concrete values.

The idea that types are connected with quotienting seems to be pervasive, especially in computer science, where one of the most important principles is data abstraction.


[Cohen](https://rdcu.be/cI1i6)
pragmatic quotient types in Coq

[Quotients in Lean](https://leanprover.github.io/theorem_proving_in_lean/axioms_and_computation.html#quotients)

> quot.sound
is the axiom that asserts that any two elements of α that are related by r become identified in the quotient. If a theorem or definition makes use of quot.sound, it will show up in the #print axioms command.

[Defining Functions on Equivalence Classes](https://dl.acm.org/doi/10.1145/1183278.1183280) alternative
[source](https://arxiv.org/abs/1907.07591)