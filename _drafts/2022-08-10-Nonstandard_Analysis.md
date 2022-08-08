---
layout: post
title:  "The formalisation of nonstandard analysis"
usemathjax: true 
tags: [logic, Jacques Fleuriot, nonstandard analysis]
---

Calculus is concerned with change over infinitesimal intervals. Both Isaac Newton and Wilhelm Leibniz regarded infinitely small quantities as mathematically meaningful, and Leonhard Euler continued to work with 
[infinitesimals](https://plato.stanford.edu/entries/continuity/) and infinities even after [Bishop Berkeley](https://en.wikipedia.org/wiki/George_Berkeley) published his [polemic](https://en.wikipedia.org/wiki/The_Analyst) against the practice in 1734.
To be sure, [Euler's conception of infinitesimals](https://rdcu.be/cSXiN) seemed contradictory. His infinitesimal quantities were definitely and necessarily nonzero, but "vanishing" and therefore "really" equal to zero.
Not until the 19th century were infinitesimals banished from mathematics by the $\epsilon$-$\delta$ arguments of Bolzano, Weierstraß and others.
And then, in the 1960s, [Abraham Robinson](https://en.wikipedia.org/wiki/Abraham_Robinson) discovered a coherent and rigorous interpretation of infinitesimals.
But is [nonstandard analysis](https://en.wikipedia.org/wiki/Nonstandard_analysis) relevant to formalised mathematics?

### The extended real numbers

In many contexts we see the set of real numbers extended with plus and minus infinity.
This extension can be convenient for talking about situations where a measure or sum is infinite.
But it cannot be done entirely smoothly: there is no way to set up the extended reals so that we get a field.
For surely $\infty+\infty=\infty$, which implies $\infty=0$.
This doesn't matter if we simply want to use infinity as a placeholder to denote an undefined measure or limit.

The extended reals are a convenience, but they do not offer a mathematically interesting treatment of infinity, let alone infinitesimals.
Isabelle/HOL provides various [extended numeric types](https://isabelle.in.tum.de/dist/library/HOL/HOL-Library/Extended_Real.html), and they provide utility without drama.
Can we do better?

### The hyperreals

The most important fact about the non-standard real numbers (*hyperreals*) is that they satisfy **exactly the same** first-order axioms as the standard real numbers.
That is literally what ["non-standard model"](https://plato.stanford.edu/entries/model-theory) means: a model of a particular set of axioms other than the obvious one.
They are guaranteed to exist by [upward Löwenheim–Skolem theorem](https://en.wikipedia.org/wiki/Löwenheim–Skolem_theorem).
The hyperreals contain infinitesimals and infinities, but they satisfy the usual first-order axioms for a complete ordered field.

In order to make use of our richer domain, we need to enrich our vocabulary.

* $\mathbb{R}^*$ denotes the hyperreals, with $\mathbb{R}$ for the standard (finite) reals
* $x\approx y$ expresses that $x$ and $y$ are infinitely close, with $x\approx 0$ if $x$ is an *infinitesimal*
* a hyperreal $x$ is *finite* if $\lvert x \rvert\le r$ for some $r\in\mathbb{R}$
* every finite hyperreal $x$ has a *standard part* $\textrm{st}(x)\in\mathbb{R}$ with $x\approx\textrm{st}(x)$

There's not enough space here to go through everything. Suffice it to say that things work reasonably. The infinite numbers turn out to be the reciprocals of nonzero infinitesimals (division by zero still being undefined). If two quantities are infinitely close then so are the results of arithmetic operations. It's all coherent, while at the same time we can construct $\epsilon$ as well as its reciprocal $\omega$ such that $\lvert\epsilon\rvert<1/n$ and $n<\omega$ for all natural numbers $n$.

"What do you mean, *construct*?"

### The ultrafilter construction of the hyperreals

[Jacques Fleuriot](https://homepages.inf.ed.ac.uk/jdf/), 
when he was doing his PhD here at Cambridge, 


[On the mechanization of real analysis in Isabelle/HOL](https://rdcu.be/cRUFK)

[Mechanising nonstandard real analysis](https://dx.doi.org/10.1112/S1461157000000267)


 Also for the naturals, complexes, ...


type classes??



[A combination of nonstandard analysis and geometry theorem proving](https://rdcu.be/cM63n)



### But do infinitesimals actually exist?

People like to question the legitimacy of everything but the counting numbers: positive integers.
The Romans had numerals for nothing else.
But why not zero, when it was possible to own no cattle, and why not negative integers, 
when the Romans were familiar with the concept of debt?
The Greeks, meanwhile, are alleged to have [had a freakout](https://nrich.maths.org/2671)
over the discovery of irrational numbers.
Even today we have to live with the silly terminology of the *real numbers*, as contrasted with *imaginary numbers*.
When we see the complex numbers diagrammed on a plane, they all look equally "real".
And, of course, **all** mathematical entities are imaginary:
if you don't believe me, try to buy the [number five on eBay](https://www.ebay.co.uk/sch/i.html?_nkw=number+five).

The arguments of the 19th Century have left us in the strange position of accepting certain infinities (Cantor's transfinite ordinal and cardinal numbers), while rejecting the infinitesimals.
But all they need to "exist" as useful mathematical entities is a coherent theory, backed by reliable intuitions.
*Pace* Berkeley, Leibniz and Euler knew what they were doing.
Although they never promulgated a theory of infinitesimals, they avoided making serious errors. The following remark by [Bair et al.](https://rdcu.be/cSXiN) seems appropriate:

> Seeing with what dexterity Leibniz and Euler operated on inﬁnite sums as if they were ﬁnite sums, a modern scholar is faced with a stark choice. He can either declare that they didn’t know the difference between ﬁnite and inﬁnite sums, or detect in their procedures a unifying principle (explicit in the case of Leibniz, and more implicit in the case of Euler) that, under suitable circumstances, allows one to operate on inﬁnite sums as on ﬁnite sums.

### Jacques Fleuriot and Newton's *Principia*

On the topic of errors: [Jacques Fleuriot](https://homepages.inf.ed.ac.uk/jdf/), 
when he was doing his PhD here at Cambridge, discovered a flaw in a proof by Isaac Newton, whose famous *Principia Mathematica* expounded his theory of gravitation and the orbits of the planets.
Crucially, Newton's proofs relied on infinitesimal reasoning combined with Euclidean geometry.
Jacques [formalised a theory of infinitesimal geometry](https://rdcu.be/cM63n) in Isabelle in order to reconstruct the proofs in their original form.
In his account of the [proof of the *Propositio Kepleriana*](https://rdcu.be/cIK7a) he is able to follow Newton step by laborious step until Newton proposes to multiply an infinite quantity by an infinitesimal in the hope of obtaining an infinitesimal result, but this does not follow.
Fortunately, Jacques was able to find an alternative route to replace that step.

Jacques' formal development provides an environment in which proofs in the calculus can be conducted using non-standard methods and the results easily transferred from the hyperreals to the reals.
Back then, I imagine that people would welcome the possibility of proving theorems without recourse to adding up fractions of epsilons.
[Some authors claim](https://rdcu.be/cSXiN) that infinitesimals, on their current rigourous basis, are still the best framework for understanding Euler's work.
Instead, sadly, the Isabelle/HOL theory of the hyperreals is hardly used for anything.
I live in hope that somebody will decide to give it a try, if only out of curiosity.



