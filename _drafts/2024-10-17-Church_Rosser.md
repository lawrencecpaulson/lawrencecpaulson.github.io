---
layout: post
title:  "The λ-calculus, 2: Church-Rosser Theorem"
usemathjax: true 
tags: [general, lambda calculus]
---
A well-known technique to speed up computer code is to re-order some steps,
for example to lift some operation out of a loop.
In logic, sometimes we can choose what inference to do next
where making the right choices gives us an exponentially shorter proof.
Also in the λ-calculus we sometimes have a choice of reduction steps
Where the possible outcomes include, at one extreme,
terminating exponentially faster or at the opposite extreme, 
not terminating at all.
But it would certainly be vexing if our computation could terminate 
with different answers, depending on our choices.
Church and Rosser proved that that outcome was impossible,
implying the consistency of the λ-calculus 
and giving us some of the tools needed
to study this question in other situations.

### Equality in the λ-calculus

As remarked [last time]({% post_url 2024-09-30-Intro_Lambda_Calculus %}),
$M=M'$ means it is possible to transform $M$ into $M'$
through any series of α, β or η steps, 
possibly within a term and possibly backwards.
So we have the following picture:

$$
\let\redd=\twoheadrightarrow
\let\se\searrow
\let\sw\swarrow
\def\arraycolsep{0pt} 
\begin{equation*}
\begin{array}{cccccccccccccccc}
M&   &   &   &M_1&   &   &   &M_2&\cdots&M_{k-1}&   &   &   &M_k=M'\\
 &\se&   &\sw&   &\se&   &\sw&   &      &       &\se&   &\sw  \\
 &   &N_1&   &   &   &N_2&   &   &\cdots&       &   &N_k
  \end{array}
\end{equation*}
$$

(In fact, all of the arrows above should really be written $\redd$
to indicate possibly multiple reductions, but I don't know how to get a diagonal multi-headed arrow.)

From the picture alone, it should be easy to see that equality
satisfies many of the basic properties we expect, such as being reflexive, symmetric and transitive.
But how can we show that some things are not equal, 
for example, that $\lambda x y.x \not= \lambda xy.y$?

### The Church-Rosser Theorem

The theorem states that if two terms are equal
then they can be made identical using reductions alone.
More formally, if $M=N$ then $M\redd L$ and $N\redd L$ for some $L$.

I am not going to try to prove it here. (I cited a paper by Rosser last time.)
Many early proofs were wrong, tripping up over clashes in bound variables.
But let's look at some of the consequences.