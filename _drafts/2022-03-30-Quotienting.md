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
a &= [(a,0)] \qquad \text{mapping $\mathbb{N}$ to $\mathbb{Z}$} \\
-[(a,b)] &= [(b,a)] \\
[(a,b)] + [(c,d)] &= [(a+c,b+d)] 
\end{align*}
$$

As usual, operations on the equivalence classes are defined in terms of operations on the representatives. To be well-defined, those operations must *respect the equivalence relation*, delivering the same result regardless of which representative was chosen. Another example is a function to map nonnegative integers to natural numbers:

$$
\begin{align*}
[(a,b)] &\mapsto a-b
\end{align*}
$$

This makes sense because for nonnegative integers, $a\ge b$.
And if $a+d = c+b$ we quickly obtain $c\ge d$ and $a-b=c-d$.

The most obvious definitions of equivalence classes, respecting the equivalence relation, etc., work without fuss. My (2006) [paper](https://dl.acm.org/doi/10.1145/1183278.1183280) (also
[here](https://arxiv.org/abs/1907.07591)) spells out the absolutely straightforward details with an emphasis on definitions and lemmas allowing the simplest formal proofs.


### No need for the axiom of choice (AC)

Many authors seem to dislike equivalence classes, using AC to choose an arbitrary representative. While I accept AC, it's poor taste and overcomplicated to use it without cause. Operations on equivalence classes can be defined simply as the union of all possible results of the corresponding operation on representatives. If the operation respects the equivalence relation, then the union will be trivial, the union of a family of identical sets, and we get our result by $\bigcup\\{x\\} = x$.

You may well ask, what if the desired result isn't a set? This issue does not arise in Isabelle/ZF, where I first did this work and where everything is a set. For Isabelle/HOL a simple trick solves the problem: it's always possible to define your operation to return a singleton set, and finally extract the desired result by calling `the_elem`, which maps $\\{x\\} \mapsto x$.

By the way, referring to such an operation as the "axiom of unique choice" is as oxymoronic as referring to plastic as "vegan leather".

### So what about types?

Having set out to prove that quotienting has nothing to do with types, I was dismayed to read my own paper on the topic:

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


