---
layout: post
title:  "Equivalence classes and quotienting"
usemathjax: true 
tags: quotient constructions
---

A *quotient construction* partitions a set according to an equivalence relation. The *equivalence classes* — members of the partition — are sets of equivalent elements. To use computer science jargon, the construction yields an *abstract type* (the equivalence classes) and the elements of those classes belong to an underlying *concrete type*.
For example, pairs of natural numbers can represent integers or nonnegative rationals, depending on the equivalence relation chosen.
However, quotienting has nothing to do with types.

### A small example

Let's define the set of integers from pairs of natural numbers by quotienting. Our equivalence relation on such pairs is

$$
\begin{align*}
 (a,b) \sim (c,d) &\iff a+d = c+b. 
\end{align*}
$$

It's trivially reflective, symmetric and transitive. Writing $[(a,b)]$ for the equivalence class of $(a,b)$, which is the set of all $(c,d)$ such that $(a,b) \sim (c,d)$, we can define some integer operations quite easily:

$$
\begin{align*}
a &= [(a,0)] \\
-[(a,b)] &= [(b,a)] \\
[(a,b)] + [(c,d)] &= [(a+c,b+d)] 
\end{align*}
$$

As usual, operations on the equivalence classes are defined in terms of operations on the representatives. To be well-defined, those operations must respect the equivalence relation, delivering the same result regardless of which representative was chosen. Another example is a function to map nonnegative integers to natural numbers:

$$
\begin{align*}
[(a,b)] &\mapsto a-b
\end{align*}
$$

The most obvious definitions of equivalence classes, respecting the equivalence relation, etc., work without fuss. My (2006) paper spells through the details with an emphasis on definitions and lemmas allowing the simplest formal proofs.

`the_elem`

### Some basic definitions

Having set out to prove that quotienting has nothing to do with types, I was dismayed to read my own (2006) [paper](https://dl.acm.org/doi/10.1145/1183278.1183280) (also
[here](https://arxiv.org/abs/1907.07591)) on the topic:

> A quotient construction defines an abstract type from a concrete type, using an equivalence relation to identify elements of the concrete type that are to be regarded as indistinguishable. The elements of a quotient type are equivalence classes: sets of equivalent concrete values.

The idea that types are connected with quotienting is pervasive, especially in computer science, where one of the most important principles is data abstraction.
But this view narrows our horizons, and the actual mathematics reported in that paper operates at the level of sets.

### Quotients in dependent type theory

I'm not an expert and what I know I tend to hear indirectly. One thing I hear is that quotienting in type theory involves a *setoid*, a type paired with an explicit equality relation. (See [Barthe et al.](https://doi.org/10.1017/S0956796802004501), also [here](https://hal.archives-ouvertes.fr/hal-01124972).
See also [*setoid hell*](https://www.google.com/search?client=safari&rls=10_15_7&q=setoid+hell&ie=UTF-8&oe=UTF-8).)
Straightforward quotienting is apparently not possible.
Cyril Cohen suggests some [pragmatic techniques](https://rdcu.be/cI1i6) for Coq.
However, [quotients in Lean](https://leanprover.github.io/theorem_proving_in_lean/axioms_and_computation.html#quotients)
are handled differently, with quotients built in and supported by an additional axiom.
I gather that type theory purists are outraged by Lean's approach and would comment that it's a shame that such sophisticated type theories cannot directly support such elementary constructions.


