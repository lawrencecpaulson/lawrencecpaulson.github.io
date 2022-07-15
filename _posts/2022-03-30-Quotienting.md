---
layout: post
title:  "Equivalence classes and quotienting"
usemathjax: true 
tags: [type theory, set theory, quotients]
---

A *quotient construction* partitions a set according to ∼, some equivalence relation. The *equivalence classes* — members of the partition — are maximal sets of ∼-equivalent elements. To use computer science jargon, the construction yields an *abstract type* (the equivalence classes) and the elements of those classes belong to an underlying *concrete type*.
For example, pairs of natural numbers can represent integers or nonnegative rationals, depending on the equivalence relation chosen.
However, quotienting has nothing to do with types.

### A small example

Let's define the set of integers from pairs of natural numbers by quotienting. 
The required equivalence relation on such pairs is

$$
\begin{align*}
 (a,b) \sim (c,d) &\iff a+d = c+b. 
\end{align*}
$$

It's trivially reflective, symmetric and transitive. Writing $[(a,b)]$ for the equivalence class of $(a,b)$, which is the set of all $(c,d)$ such that $(a,b) \sim (c,d)$, we can easily define some integer operations:

$$
\begin{align*}
a &= [(a,0)] \qquad \text{mapping $\mathbb{N}$ to $\mathbb{Z}$} \\
-[(a,b)] &= [(b,a)] \\
[(a,b)] + [(c,d)] &= [(a+c,b+d)] 
\end{align*}
$$

As usual, operations on the equivalence classes are defined in terms of operations on the representatives: pairs of natural numbers. To be well-defined, those operations must *respect the equivalence relation*, delivering the same result regardless of which representative was chosen. Another example is a function to map nonnegative integers to natural numbers:

$$
\begin{align*}
[(a,b)] &\mapsto a-b
\end{align*}
$$

This makes sense because for nonnegative integers, $a\ge b$.
And if $a+d = c+b$ we quickly obtain $c\ge d$ and $a-b=c-d$.

The obvious definitions of the concepts—equivalence relations, equivalence classes, respecting the equivalence relation, etc.—work without fuss. My (2006) [paper](https://dl.acm.org/doi/10.1145/1183278.1183280) (also
[here](https://arxiv.org/abs/1907.07591)) spells out the absolutely straightforward details with an emphasis on definitions and lemmas formulated to allow the simplest machine proofs.


### No need for the axiom of choice (AC)

Many authors seem to dislike equivalence classes, instead using AC to choose an arbitrary representative. While I accept AC, to use it without cause might be seen as lazy. More to the point, reasoning about AC can be delicate, leading to needlessly complicated proofs. Operations on equivalence classes can be defined simply as the *union of all possible results* of the corresponding operation on representatives. If the operation respects the equivalence relation, then the union will be trivial, the union of a family of identical sets, and we get our result by $\bigcup\\{x\\} = x$.

You may well ask, what if the desired result isn't a set? This issue does not arise in Isabelle/ZF, where I first did this work and where everything is a set. For Isabelle/HOL a simple trick solves the problem: it's always possible to define your operation to return a *singleton set*, and finally extract the desired result by calling `the_elem`, which maps $\\{x\\} \mapsto x$.

By the way, referring to an operation like `the_elem` as the "axiom of unique choice" is as oxymoronic as referring to plastic as "vegan leather".
I'd call it "[Hobson's axiom](https://en.wikipedia.org/wiki/Hobson%27s_choice)".

### So what about types?

Having set out to prove that quotienting has nothing to do with types, I was dismayed to read my own paper on the topic:

> A quotient construction defines an abstract type from a concrete type, using an equivalence relation to identify elements of the concrete type that are to be regarded as indistinguishable. The elements of a quotient type are equivalence classes: sets of equivalent concrete values.

The idea that types are connected with quotienting is pervasive, especially 
to those who remember that the key idea underlying [LCF-style proof assistants]({% post_url 2022-01-05-LCF %}) is an abstract data type.
But this view narrows our horizons, and the actual mathematics reported in that paper operates at the level of sets.
And by "sets" here it makes little difference whether we are in ZFC or using the typed sets of higher-order logic.

The techniques in my paper are fine for declaring something like the integers, but demand a lot of repetitious work in the case of a [recursive datatype with equational constraints](https://isabelle.in.tum.de/library/HOL/HOL-Induct/QuoDataType.html) and even more so when there's [nested datatype recursion](https://isabelle.in.tum.de/library/HOL/HOL-Induct/QuoNestedDataType.html):
the number of trivial facts to be stated and proved is quadratic in the number of datatype constructors. 

More automation can be obtained through the [lifting and transfer](https://rdcu.be/cI622) package.
It is powerful, general and modular, but somewhat mysterious and not so easy to learn. And yet I can see nearly 8600 calls to the `transfer` method in the Isabelle distribution and libraries.
It is however, type-based, transferring properties and definitions between concrete and abstract types.
To do a quotient construction on a set, my more direct methods should do the job.


### Quotients in dependent type theory

I'm not an expert on most of these systems, and what I know I tend to hear indirectly. One thing I hear is that quotienting in type theory often involves a *setoid*, a type paired with an explicit equality relation. (See [Barthe et al.](https://doi.org/10.1017/S0956796802004501), also [here](https://hal.archives-ouvertes.fr/hal-01124972).
See also [*setoid hell*](https://www.google.com/search?client=safari&rls=10_15_7&q=setoid+hell&ie=UTF-8&oe=UTF-8).)
Straightforward quotienting is apparently not possible in Coq, 
but Cyril Cohen suggests some [pragmatic techniques](https://rdcu.be/cI1i6).

Quotients in Lean are handled differently, with [quotients built in](https://leanprover.github.io/theorem_proving_in_lean/axioms_and_computation.html#quotients) and supported by an additional axiom.
Nuprl has supported both [subtypes and quotient types](https://doi.org/10.1016/j.jal.2005.10.005) (also available [here](https://www.cs.cornell.edu/courses/cs4860/2018sp/lecture-notes/ICTT.pdf)), for a long time.

I gather that type theory purists are outraged by the Lean and Nuprl approaches.
It's puzzling that such sophisticated type theories struggle with something as trivial as equivalence classes.
