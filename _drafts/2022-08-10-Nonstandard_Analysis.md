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

The extended reals are a convenience, but they do not offer a reasonable treatment of infinity, let alone infinitesimals.

### The hyperreals

The most important fact about the non-standard real numbers (*hyperreals*) is that they satisfy exactly the same first-order axioms as the standard real numbers.
That is literally what "non-standard model" means: a model of a particular set of axioms other than the obvious one.
They are guaranteed to exist by upward Löwenheim–Skolem theorem.
The hyperreals contain infinitesimals and infinities, but they satisfy the usual first-order axioms for a complete ordered field.

In order to make use of our richer domain, we need a richer vocabulary.

* $\mathbb{R}^*$ denotes the hyperreals, with $\mathbb{R}$ for the standard (finite) reals
* $x\approx y$ expresses that $x$ and $y$ are infinitely close, with $x\approx 0$ if $x$ is an *infinitesimal*
* a hyperreal $x$ is *finite* if $\lvert x \rvert\le r$ for some $r\in\mathbb{R}$
* every finite hyperreal $x$ has a *standard part* $\textrm{st}(x)\in\mathbb{R}$ with $x\approx\textrm{st}(x)$

There's not enough space here to go through everything. Suffice it to say that things work reasonably. The infinite numbers turn out to be the reciprocals of nonzero infinitesimals (division by zero still being undefined). If two quantities are infinitely close then so are the results of arithmetic operations. It's all coherent, while at the same time we can construct $\epsilon$ as well as its reciprocal $\omega$ such that $\lvert\epsilon\rvert<1/n$ and $n<\omega$ for all natural numbers $n$.

"What do you mean, *construct*?"

### The ultrafilter construction of the hyperreals

### But do infinitesimals actually exist?

People like to question the legitimacy of everything but the counting numbers: positive integers.
The Romans had numerals for nothing else.
But why not zero, when it was possible to no olives (or whatever), and why not negative integers, 
when the Romans were familiar with the concept of debt?
The Greeks, meanwhile, are alleged to have [had a freakout](https://nrich.maths.org/2671)
over the discovery of irrational numbers.
Even today we have to live with the silly terminology of the *real numbers*, as contrasted with *imaginary numbers*.
When we see numbers diagrammed on the complex plane, they all look equally "real".
And, of course, **all** mathematical entities are imaginary:
if you don't believe me, try to buy the [number five on eBay](https://www.ebay.co.uk/sch/i.html?_nkw=number+five).

The arguments of the 19th Century have left us in the strange position of accepting certain infinities (Cantor's transfinite ordinal and cardinal numbers), while rejecting the infinitesimals.
But all they need to "exist" as useful mathematical entities is a coherent theory, backed by reliable intuitions.
*Pace* Berkeley, Leibniz and Euler knew what they were doing.
Although they never promulgated a theory of infinitesimals, they avoided making serious errors.

Fleuriot: Newton

 Also for the naturals, complexes, ...

[model theory](https://plato.stanford.edu/entries/model-theory/)


type classes??


[On the mechanization of real analysis in Isabelle/HOL](https://rdcu.be/cRUFK)

[A combination of nonstandard analysis and geometry theorem proving](https://rdcu.be/cM63n)

[Proving Newton's Propositio Kepleriana](https://rdcu.be/cIK7a)

[Mechanising nonstandard real analysis](https://dx.doi.org/10.1112/S1461157000000267)

[Jacques Fleuriot](https://homepages.inf.ed.ac.uk/jdf/)
