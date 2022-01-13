---
layout: post
title:  "Is Zermelo-Fraenkel set theory the foundation of mathematics?"
usemathjax: true 
tags: logic, set theory, axiom of choice
---


Set theory (specifically, ZFC) is said to be the foundation of mathematics. Who says so and why? And why isn't it used to formalise mathematics?
How do our various typed formalisms compare to set theory?

### Zermelo set theory

Zermelo introduced his axioms for set theory in 1908 as his response to concerns about the foundations of mathematics. These included the notorious [*axiom of choice*]({% post_url 2021-11-10-Axiom_of_Choice %}),
in addition to more mundane axioms asserting our ability to form finite sets, take unions and power sets and to specify subsets of an existing set. Finally, the *axiom of infinity* guarantees the existence of an infinite set.

Remarkably, a slightly restricted version of Zermelo set theory turns out to be equal in expressiveness and strength to higher-order logic. Also notable is that the authors of Bourbaki chose Zermelo set theory , not ZF, as the foundation of their project (as indignantly [pointed out](http://dx.doi.org/10.1007/BF03025863) by A. R. D. Mathias). Upon this basis, the Bourbaki group wrote careful if not strictly formal developments of great swathes of mathematics.
Therefore we can safely conclude that Zermelo set theory—thus also higher-order logic—is adequate for the vast bulk of "ordinary" mathematics. The huge variety of topics already formalised in Isabelle/HOL and HOL Light is further evidence for this view.

### The remaining axioms of ZFC

What sort of mathematics is the exception? Amusingly enough, the answer is *set theory itself*. Georg Cantor [created a paradise](https://plato.stanford.edu/entries/settheory-early/) of ordinal and cardinal arithmetic that goes well beyond the confines of Zermelo set theory. To reach his paradise, we need the *axiom of replacement*, a sort of set teleportation device that can "transport" any set to a "higher level". More precisely, it lets us form indexed families of sets $\\{A_\xi\\}$ for $\xi\in\alpha$
and therefore indexed unions such as $\bigcup_{\xi\in\alpha} A_\xi$.
From such limit constructions we obtain the transfinite ordinals, the cardinals (the famous series of alephs) and the levels of the cumulative hierarchy of sets.
Finally, the *axiom of foundation* asserts that there are no other sets, affirming the idea that the universe of sets is an iterative construction.

Category theory goes beyond ZF simply because it adopts, as its starting point, the category Set of all ZF sets and functions. To my mind this is like a billionaire's son calling up his father the day after he arrives at university saying, "dad, I need more money." When his father asks what happened to the billion-dollar sum he had been given, the son replies "I spent it all on NFTs". When people demand stronger set theories to serve as a foundation for category theory I am tempted to ask, what is to stop you from forming the category of all sets in that extended set theory? Also odd is the sort of extension proposed: sometimes one or two levels of classes, sometimes an additional "universe" (meaning, a model of ZF) and is sometimes countably many such models. All of these extensions are trivial compared with what the axiom of replacement gave us over the Zermelo sets, namely transfinitely many additional levels.

I'd be interested to hear of topics in mathematics that require beyond the Zermelo universe of sets without referring explicitly to topics connected with ZF set theory.

### Set theory and proof assistants

[Werner](https://link.springer.com/chapter/10.1007/BFb0014566)
We present two mutual encodings, respectively of the Calculus of Inductive Constructions in Zermelo-Fraenkel set theory and the opposite way. 

 Bernays-Gödel and resolution experiments?
 
 hereditarily finite set theory
 
 Zermelo set theory
 
 ZF set theory
 
 
 Isabelle/ZF and recent work on forcing
 
 Encoding set theory in type theory for work in Lean and Coq


> Gregory H. Moore, *Zermelo's Axiom of Choice* (Springer, 1982), 64--65.

I