---
layout: post
title:  "Is Zermelo-Fraenkel set theory the foundation of mathematics?"
usemathjax: true 
tags: [set theory, type theory, axiom of choice, Ernst Zermelo, Archive of Formal Proofs, higher-order logic]
---

[Set theory](https://plato.stanford.edu/entries/set-theory/) (specifically, ZFC) is said to be the foundation of mathematics. Who says so, and are they right? How do our various typed formalisms compare to set theory?
What about set theory as a branch of mathematics to be mechanised?

### Zermelo set theory

Zermelo introduced his [axioms for set theory](https://plato.stanford.edu/entries/zermelo-set-theory/) in 1908 as his response to concerns about the foundations of mathematics. He included the notorious [*axiom of choice*]({% post_url 2021-11-10-Axiom_of_Choice %})
(AC) in addition to more mundane axioms asserting our ability to form finite sets and form unions and power sets. The *axiom of infinity* guaranteed the existence of an infinite set. 
The crucial *axiom of separation* allowed the specification of a subset of an existing set while avoiding Russell's paradox.
Remarkably, Zermelo proposed this axiom before we possessed any means to express the specification; *Principia Mathematica* would not appear until 1910, and first-order logic [arrived even later](https://plato.stanford.edu/entries/logic-firstorder-emergence/).

A slightly restricted version of Zermelo set theory due to Mac Lane turns out to be [equal in expressiveness and strength](https://doi.org/10.1016/S0168-0072(00)00031-2) to higher-order logic. Also notable is that the authors of Bourbaki chose Zermelo set theory, not ZF, as the foundation of their project (as indignantly [pointed out](https://rdcu.be/cJtBL) by A. R. D. Mathias). Upon this basis, the Bourbaki group wrote careful if not strictly formal developments of great swathes of mathematics.
Therefore, a formalism as strong as Zermelo set theory—such as higher-order logic—might just be adequate 
for the vast bulk of "ordinary" mathematics. 
The wide variety of topics [already formalised](https://www.cs.ru.nl/~freek/100/) 
in Isabelle/HOL and HOL Light is evidence for this view. 
See also under Mathematics and Logic in the [Archive of Formal Proofs](https://www.isa-afp.org/topics/).

### The remaining axioms of ZFC

What sort of mathematics is the exception? Amusingly enough, the chief answer is *set theory itself*. Georg Cantor [created a paradise](https://neugierde.github.io/cantors-attic/) of ordinal and cardinal arithmetic that goes well beyond the confines of Zermelo set theory. To reach his paradise, we need the *axiom of replacement*, a sort of set teleportation device that can "transport" any set to a "higher level". More precisely, it lets us form indexed families of sets $\\{A_i\\}$ for $i\in I$ where $I$ is any existing set,
and therefore indexed unions such as $\bigcup_{\xi<\alpha} A_\xi$.
From such limit constructions we obtain transfinite recursion and the ordinal and cardinal numbers.
And we obtain the $V_\xi$ for each ordinal $\xi$, the levels of the *cumulative hierarchy of sets*.
Finally, the *axiom of foundation* asserts that there are no other sets, affirming the idea that the universe of sets is an iterative construction.

Already $V_\omega$ contains the set of natural numbers. 
Progressing to $V_{\omega+1}$, $V_{\omega+2}$, $\ldots$, we reach 
the reals and higher spaces as well as sets and functions over them. (These are analogous to iterations of function types in simple type theory.)
Only finitely many iterations are allowed, however; in Zermelo set theory we never reach $V_{\omega+\omega}$. 
With ZF we get all of the $V$-levels plus a vast menagerie of unimaginable monstrosities, such as fixedpoints of the aleph operator
(the solutions of $\kappa = \aleph_\kappa$ form a proper class).
As pointed out by George Boolos,

> $\kappa$ seems sufficiently large that the claim that it exists might plausibly be regarded as dubious, $\kappa$ is no gnat; it is a lot to swallow.[^1]

[^1]: George Boolos. [Must We Believe in Set Theory?](https://doi.org/10.1017/CBO9780511570681.013)), in *Between Logic and Intuition* (Cambridge University Press, 2009), p. 258.

Recall that $\aleph_0$ is the cardinality of the natural numbers, 
and the cardinality of the continuum is thought by many to be
$\aleph_1$ or $\aleph_2$; already $\aleph_\omega$ is beyond our comprehension, let alone $\kappa$, which is the limit $\aleph_{\aleph_{\aleph_\ddots}}$.
And yet, as Boolos remarks, this $\kappa$ is positively "teensy" compared with
the large cardinals often assumed in order to extend ZFC; their existence (he argues) must be even more dubious. 

Category theory goes beyond even ZF simply because it adopts, as its starting point, the category **Set** of all ZF sets and functions. To my mind this is like a billionaire's son calling up his father the day after he arrives at university saying, "Dad, I need more money." His father asks what happened to the billion-dollar sum he had been given and the son replies "I spent it all on NFTs". When people demand stronger set theories to serve as a foundation for category theory, we should ask "What is to stop you from forming the category of all sets in that extended set theory?" Also odd is the sort of extension proposed: sometimes just one or two levels of superclasses, sometimes an additional "universe" (a large cardinal, yielding a set model of ZF), sometimes a countable series of such cardinals, sometimes more. All of these extensions are trivial compared with what the axiom of replacement gave us over the Zermelo sets: *transfinitely many* additional levels
above the world of ordinary mathematics.
It's like the kid saying he'd be fine with just $10 extra.

It is tempting to wonder how category theory would have developed (consistently, perhaps?) 
if Mac Lane had adopted his own modest set theory as the basis for his category of sets. 
Would it have affected any applications of category theory?
Also, I'd be interested to hear of mathematical domains that require more than the Zermelo universe of sets without referring to topics explicitly connected with set theory.

### ZF and proof assistants

Here's another answer to my question: ZF set theory turns out to be surprisingly close in strength to the calculus of inductive constructions (CIC), the type theory implemented by Coq and Lean.
[Werner](https://rdcu.be/cJ5NL)
presented encodings of CIC within ZFC and *vice versa*. 
There is a correspondence between the universes of CIC and the inaccessible cardinals that must be assumed in addition to ZFC.
To encode ZFC in CIC it is necessary to assume the axiom of choice, and therefore classical logic.
An outstanding application of Warner's correspondence was Han and van Doorn's [proof in Lean](https://doi.org/10.4230/LIPIcs.ITP.2019.19) of the independence of the continuum hypothesis using Cohen's forcing method.

Isabelle has supported first-order logic and set theory as early as the 1990s. Isabelle/ZF is a separate instance from Isabelle/HOL sharing its interface, proof language, simplifier, etc. It is based on a formalisation of classical first-order logic, asserting the usual ZF axioms and with AC kept optional. Experiments done at Cambridge in the 1990s include formal proofs of many [equivalents of AC](https://arxiv.org/abs/cs/9612104).
Later, I used Gödel's [constructible universe](https://plato.stanford.edu/entries/goedel/#GodWorSetThe) in an [Isabelle/ZF proof](http://journals.cambridge.org/action/displayAbstract?fromPage=online&aid=6560756&fulltextType=RA&fileId=S1461157000000449) of the consistency of the continuum hypothesis.
Isabelle/ZF then languished for many years, but lately a group at the University of Argentina has formalised [a string of major results](https://cs.famaf.unc.edu.ar/~pedro/forcing/) based on forcing.
An astounding feat.
 
The [development of modern set theory](https://plato.stanford.edu/entries/settheory-early/) 
took about a century. It eventually solved most of the foundational problems that had to be addressed, 
but by that time most mathematicians had lost interest. So it goes.

### Postscript added 16-10-2022

It's surely relevant that the market for NFTs has gone [right down the pan](https://www.investmentmonitor.ai/crypto/nft-market-collapse-cryptocurrency-value).
