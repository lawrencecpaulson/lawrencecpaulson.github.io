---
layout: post
title:  When is a computer proof a proof?
usemathjax: true
tags: [philosophy, Imre Lakatos]
---

In 1976, Appel and Haken caused delight mixed with consternation by proving
the celebrated four colour theorem, but with heavy reliance on a computer calculation.
An assembly language program was used to check 1936 "reducible configurations"; 
people were rightly concerned about errors in the code.
However, the Appel–Haken proof also required "the investigation by hand
about ten thousand neighbourhoods of countries with positive charge",[^1]
much of which was done by Appel's 13-year-old daughter,
and nobody seemed bothered about the possibility of errors there.
Computer algebra systems were emerging around that time and would eventually
become widely used in many branches of science and engineering,
although I can't imagine a computer algebra calculation being uncritically accepted
by any mathematics journal.
Today, I and others hope to see mathematicians using proof assistants in their work.
Whether machine proofs will be accepted as valid requires serious thought
about the nature of mathematical proof.
We have come a long way since 1976, but many mathematicians still distrust computers,
and many struggle to agree on the computer's precise role.

[^1]: Robin Wilson, *Four Colours Suffice: How the Problem Was Solved* (Princeton, 2002)

### The idea of mathematical certainty

In a [previous post]({% post_url 2022-07-27-Truth_Models %}), I've discussed the difference
between scientific knowledge, which sometimes needs to be revised 
in the light of new evidence, as opposed to with mathematical truth,
which is not evidence-based. I also mentioned 
the work of [Imre Lakatos](https://plato.stanford.edu/entries/lakatos/), a philosopher
who studied a particular theorem 
([Euler’s polyhedron formula](https://www.ams.org/publicoutreach/feature-column/fcarc-eulers-formula)) for which counterexamples
were actually discovered. Lakatos' discussion is largely focused on
strategies for dealing with counterexamples, e.g.

* *monster-barring*: modifying your definition to exclude the counterexamples, regardless of how ad hoc it looks
* *exception-barring*: retreating to an overly conservative but completely safe definition

And I have to remark, when you have one theorem and one definition that you are allowed to change at will, it looks like cheating. More commonly, errors are found in proofs (rather than in definitions) but can be fixed, with the theorem statement at worst marginally affected.

Perhaps we still have in mind a group of students watching Archimedes draw circles
in the sand and all agreeing that his proof is valid. 
We don't have that immediacy any more.
Today, doing mathematics necessarily requires trusting 
tens of thousands of pages of other people's work.
So, how about trusting some software?

### Some fundamental desiderata for proofs

A [recent paper](https://www.degruyter.com/document/doi/10.1515/krt-2022-0015/html)[^2]
discusses some widely accepted characteristics of mathematical proofs:


[^2]: Parshina, Katia. "Philosophical assumptions behind the rejection of computer-based proofs" *KRITERION – Journal of Philosophy*, 2023

1. Proofs are convincing.
2. Proofs are surveyable.
3. Proofs are formalisable. 

I like these because, ipso facto, any proof conducted using a proof assistant
is not merely formalisable but has literally just been formalised,
both in the sense of being expressed in some sort of high-level logical language
and in the sense of having been reduced to primitive logical inferences.
Not all formal proofs are surveyable but some certainly are, 
with both Mizar and Isabelle/HOL's Isar language specifically designed for legibility.
As for convincing: there can be no handwaving in a machine proof.
As a rule, machines are much harder to convince than a knowledgeable mathematician,
and machine proof contains not gaps but rather excessive detail.

Incidentally, and remarkably, the paper explains "convincing" as meaning
"convincing for mathematicians" and mere acceptance by the mathematical community
is sufficient (even if they cannot survey the proof itself).
It sounds a bit like "justification by faith": all we need is for mathematicians to believe
in proof assistants!

In short, formal proofs, provided that they are written to be legible, easily satisfy
all three criteria. Unfortunately, the great majority of formal proofs are not legible.
But as I have shown by [numerous examples](https://lawrencecpaulson.github.io/tag/examples), 
they can be.

### What do we do about super-long proofs?

The Internet tells me that the millionth digit of Pi is 1, and I'm certain
there is no simple proof of that 
(though similar claims would be trivial for rational numbers).
Similarly, [Wikipedia claims](https://en.wikipedia.org/wiki/Largest_known_prime_number) 

> The largest known prime number (as of June 2023) is $2^{82,589,933} − 1$, a number which has 24,862,048 digits.

To assert that this number is prime is essentially no different from asserting that
2 is prime, but the proof is rather longer.
It relies on the theory of Mersenne primes
and on an enormous computer calculation.
Any fact obtained by a calculation is a mathematical statement and it seems clear
that the vast majority of these do not have short proofs.
Fortunately, few of these claims have weighty implications, so it's okay
if we can't survey their proofs.

But not every fact obtained by a monster computation is mathematically trivial.

The [largest ever proof](https://www.cs.utexas.edu/~marijn/ptn/) 
is that of the Boolean Pythagorean Triples problem, which weighs in at 200 terabytes.
(Read the [gory details](https://arxiv.org/abs/1605.00723).)
This proof was generated by a SAT solver, a piece of software capable of
finding a model of a set of assertions written in Boolean logic,
or if no such model exists, proving that fact.
It is without doubt a mathematical proof, one that is overwhelmingly too large
for a human being to survey.
At most we can survey tiny but arbitrary parts of it,
which may be a means of establishing confidence in its correctness.

My favourite example though is the non-existence of a 
[projective plane of order 10](/papers/Lam_finite_Proj_plane_order_10.pdf).
When I was an undergraduate at Caltech, Prof Herbert Ryser stressed the importance of
settling this question. What is strange is that such a plane could be represented
by an incidence matrix of zeros and ones, 111×111. A huge but finite search.
Such a search was carried out and the question settled negatively in 1989,
too late for Ryser, who had died in 1985.
The result has major implications for combinatorics despite the absence
of a surveyable proof. 
It was [confirmed recently](https://arxiv.org/abs/2012.04715) with the help of a SAT solver,
and therefore has been proved in logic, even though the proof is colossal.

People are legitimately uneasy about being wholly dependent on 
a piece of software. This cannot be compared to astronomers using a powerful telescope
to observe stars far too faint for the human eye, because observational error
has always been an inherent part of all empirical science.
Mathematics is supposed to be different.
We have to take this proof at least somewhat on faith, and yet the theorem statement
cannot be dismissed as trivial.

It seems we are forced to be pragmatic and accept the amplification
of human reasoning by machine. This does not mean that mathematics has become empirical:
extensive numerical calculations suggest that the [Riemann hypothesis](https://en.wikipedia.org/wiki/Riemann_hypothesis) is true,
but absolutely nobody accepts that as a proof.


