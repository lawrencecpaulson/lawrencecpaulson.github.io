---
layout: post
title:  "The formalisation of nonstandard analysis"
usemathjax: true 
tags: [logic, Jacques Fleuriot, nonstandard analysis]
---

Calculus is concerned with change over infinitesimal intervals. Both Isaac Newton and Wilhelm Leibniz regarded infinitely small quantities as mathematically meaningful, and Leonhard Euler continued to work with 
[infinitesimals](https://plato.stanford.edu/entries/continuity/) even after [Bishop Berkeley](https://en.wikipedia.org/wiki/George_Berkeley) published his [polemic](https://en.wikipedia.org/wiki/The_Analyst) against the practice in 1734.
Not until the 19th century were infinitesimals banished from mathematics by the $\epsilon$-$\delta$ arguments of Bolzano, Weierstraß and others.
And then, in the 1960s, [Abraham Robinson](https://en.wikipedia.org/wiki/Abraham_Robinson) discovered a coherent and rigorous interpretation of infinitesimals.
But is [nonstandard analysis](https://en.wikipedia.org/wiki/Nonstandard_analysis) relevant to formalised mathematics?

### The extended real numbers

In many contexts we see the set of real numbers extended with plus and minus infinity.
This extension can be convenient for talking about situations where a measure or sum is infinite.
But it cannot be done entirely smoothly: there is no way to set up the extended reals so that we get a field.
For surely $\infty+\infty=\infty$, which implies $\infty=0$.
This doesn't matter if we simply want to use infinity as a placeholder to denote an undefined measure or other quantity.
However, it doesn't yield a reasonable treatment of infinitesimals.

### Nonstandard analysis

The most important fact about the non-standard real numbers is that they satisfy exactly the same first-order axioms as the standard real numbers.
That is literally what "non-standard model" means: a model of a particular set of axioms other than the obvious one.
They are guaranteed to exist by upward Loewenheim-Skolem theorem.
The non-standard real numbers contain infinitesimals and infinities, but they satisfy the first-order axioms for a complete ordered field.

You need to extend the signature to be able to "see" the infinitesimals

You get infinities as well. Also for the natruals, complexes, ...

[model theory](https://plato.stanford.edu/entries/model-theory/)

ultrafilter construction

type classes??


[On the mechanization of real analysis in Isabelle/HOL](https://rdcu.be/cRUFK)

[A combination of nonstandard analysis and geometry theorem proving](https://rdcu.be/cM63n)

[Proving Newton's Propositio Kepleriana](https://rdcu.be/cIK7a)

[Mechanising nonstandard real analysis](https://dx.doi.org/10.1112/S1461157000000267)

[Jacques Fleuriot](https://homepages.inf.ed.ac.uk/jdf/)
