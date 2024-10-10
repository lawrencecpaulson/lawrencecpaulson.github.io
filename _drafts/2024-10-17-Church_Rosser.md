---
layout: post
title:  "The λ-calculus, 2: Church-Rosser Theorem"
usemathjax: true 
tags: [general, lambda calculus]
---
A well-known technique to speed up computer code is to re-order some steps,
for example to lift a costly operation out of a loop.
In logic, when we can choose what inference to do next,
making the right choices yields an exponentially shorter proof.
Also in the λ-calculus we sometimes have a choice of reduction steps
where the possible outcomes include, at one extreme,
terminating exponentially faster or at the opposite extreme, 
not terminating at all.
But it would certainly be vexing if our computation 
could return different final results.
Church and Rosser proved that that outcome was impossible,
implying the consistency of the λ-calculus 
and giving us some of the tools needed
to study this question in other situations.

### Final values in the λ-calculus

As mentioned last time, basic things like numbers and lists 
are not built into the λ-calculus, but can be encoded.
We'll look at these tricky but rather cool encodings in a later post.
But here is a teaser: it's conventional to represent true and false by
$\lambda x y.x$ and $\lambda xy.y$, respectively.

Note that no reductions can be applied to either of these: 
they are in *normal form*.
(Remember, a reduction is a β or η step; the α-conversions, 
which just rename bound variables, do not count.)
If $M$ is in normal form, then we regarde it as a **value**
rather than as a **computation**.
Conversely, if it is not in normal form then further reductions are possible.
There exist more nuanced notions of value 
that make sense of infinite computations.

### Equality in the λ-calculus

As remarked [last time]({% post_url 2024-09-30-Intro_Lambda_Calculus %}),
$M=M'$ means it is possible to transform $M$ into $M'$
through any series of α, β or η steps, 
possibly within a term and possibly backwards.
So we have the following picture:

$$\let\redd=\twoheadrightarrow$$
<img src="/images/equality-in-lambda-calc.png" alt="chain of reductions for λ-calculus equality" width="500"/>

Note that $\redd$ above indicates possibly multiple reductions.
From the picture alone, it should be easy to see that equality
satisfies many of the basic properties we expect, such as being reflexive, symmetric and transitive.
But how can we show that some things are not equal:
for example, that $\lambda x y.x \not= \lambda xy.y$?

### The Church-Rosser Theorem

The theorem states that if two terms are equal
then they can be made identical using reductions alone.
More formally, if $M=N$ then $M\redd L$ and $N\redd L$ for some $L$.

If you really want the gory details of the proof, see the paper by Rosser
that I cited last time.
Many early proofs were wrong, tripping up over 
Substitution and free/bound variable clashes.
Let's first look at some of the consequences.
* If $M=N$ and $N$ is in normal form, then $M\redd N$: reductions
  alone are enough to reach that normal form.
* If $M$ and $N$ are distinct terms in normal form, then $M\not=N$. For example, $\lambda xy.x\not=\lambda xy.y$.

The latter point above (which ignores bound variable renaming, incidentally) implies the consistency of the λ-calculus and gives us a simple way to recognise that two final values are distinct.