---
layout: post
title:  "Formalising an easy proof: Dirichlet's approximation theorem"
usemathjax: true 
tags: [examples, Isar, formalised mathematics]
---
For many, the process of transforming a textbook mathematical proof
into a formal document remains mysterious.
Here, we look at a fairly elementary example:
Dirichlet's approximation theorem, which is concerned with
finding a rational approximation to a given real number,
while keeping the numerator and denominator relatively small.
The proof combines an application of the pigeonhole principle
with some straightforward calculations.
Formalised, it's only about 50 lines long.
There are still a couple of tricky bits to deal with!

### The textbook proof

Consider the problem of approximating π by a rational number.
Any finite decimal representation of π is a rational approximation,
but the denominators are large powers of 10, when we can do much better.
Consider that 355/113 = 3.1415929 approximates π 
to seven significant figures (the true value is 3.1415927).
Dirichlet's approximation theorem guarantees 
the existence of a rational approximation to a given real number
$\theta$: for every integer $N>0$ 
there exist integers $h$ and $k$ with $0<k \le N$ such that
$\vert k\theta-h\vert < 1/N$.
This expresses that $h/k$ is a good approximation to $\theta$.

<img src="/images/Dirichlet-approx-thm.png" width="650"/>



This proof comes from *Modular Functions and Dirichlet Series in Number Theory* by Tom M. Apostol, page 143.
