---
layout: post
title:  "The hereditarily finite sets"
usemathjax: true 
tags: logic, set theory
---

A set is hereditarily finite if it is finite and all of its elements are hereditarily finite. They can be characterised by the axioms of set theory but negating the axiom of infinity. They are countably many and they are a natural domain for talking about computation. They also allow a clean treatment of Gödel's incompleteness theorems.

### Introduction to the HF sets

The inductive conception of HF sets justifies the recursive definition $f(x)=\sum\, \\{2^{f(y)}\mid y\in x\\}$, yielding a bijection $f:\text{HF}\to \mathbb{N}$  between the HF sets and the natural numbers.
The linear ordering on HF given by $x<y\iff f(x)<f(y)$ extends both the membership and the subset relations.

The HF sets support many standard constructions, even quotients. Equivalence classes are not available in general --- they may be infinite --- but the linear ordering over HF identifies a unique representative.
The integers and rationals can be constructed, with their operations (but not the **set** of integers, obviously).
Świerczkowski [has used HF](https://doi.org/10.4064/DM422-0-1) as the basis for proving Gödel's incompleteness theorems, and I [have formalised his work](https://www.cl.cam.ac.uk/~lp15/papers/Formath/Goedel-logic.pdf) using Isabelle/HOL.





