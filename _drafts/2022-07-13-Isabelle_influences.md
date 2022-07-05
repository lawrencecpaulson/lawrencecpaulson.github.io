---
layout: post
title:  "How Isabelle emerged from the trends of the 1980s"
usemathjax: true 
tags: general, de Bruijn, LCF, AUTOMATH, Martin-Löf type theory
---

The fault lines of today's proof assistant community are striking.
In one corner are researchers into advanced constructive type theories.
I get the impression (if Twitter is at all reliable) that they see their rivals as set theorists, though I'd be surprised if any set theorists were even aware of their work.
Anyway, hardly anybody uses set theory in a proof assistant.
Their true rivals with regard to interactive theorem proving are using classical simple type theory systems, such as Isabelle/HOL. But does anybody recognise the extent to which Isabelle has been influenced by type theories like AUTOMATH and Martin-Löf?

### Isabelle: the beginnings

Isabelle was inspired by what I had learnt at Caltech in the mid-70s, at Cambridge, at INRIA-Rocquencourt and from people studying Martin-Löf type theory at [Chalmers University](https://www.chalmers.se/en/departments/cse/).
At Caltech I had learnt about [AUTOMATH](https://www.cs.ru.nl/~freek/aut/) from de Bruijn, while at Cambridge I was deeply involved with [Edinburgh LCF](https://doi.org/10.1098/rsta.2014.0234).
Through [Mike Gordon](https://www.cl.cam.ac.uk/archive/mjcg/) I established connections with Inria's [Gérard Huet](https://pauillac.inria.fr/~huet/) and the Chalmers group.

During the early 80s I was busy with a variety of projects, including a [reimplementation of LCF](https://www.cambridge.org/gb/academic/subjects/computer-science/programming-languages-and-applied-logic/logic-and-computation-interactive-proof-cambridge-lcf?format=PB). 
But I was deeply taken by [Martin-Löf type theory](http://www.jstor.com/stable/37448) and devoted perhaps a year of intensive work in order to produce [a paper](https://doi.org/10.1016/S0747-7171(86)80002-5) that nobody noticed:
I hadn't understood that in intuitionistic type theory, if you wanted a thing, and didn't fancy [Russell's "honest toil"](https://www.azquotes.com/quote/568414), it was perfectly okay to consult your intuition and simply add the thing you wanted.
Of course, you had to have the *right* intuition or your addition would never get the official imprimatur.

At Chalmers, people were working on an implementation of type theory.
I had a copy of their code and I wasn't impressed. I was sure I could do a better job.
I would follow the LCF approach, but I would take care to be efficient.
In particular, I would definitely represent $\lambda$-binding with de Bruijn indices,
a technique that hadn't caught on yet. ([Nuprl](https://www.nuprl.org) didn't use it either.)
My ambition was to handle a formula that could fill a couple of screens; never in my wildest dreams did I imagine the [huge developments](https://www.isa-afp.org/entries/DPRM_Theorem.html) we have now. [This one](https://www.isa-afp.org/entries/Hermite_Lindemann.html) too.

There I was, applying the LCF architecture to Martin-Löf type theory as it was in the early 1980s, still with extensional equality.
I wanted to apply a powerful technique invented by
[Stefan Sokołowski](http://iis.pwsz.elblag.pl/~stefan/).
His modestly entitled "Note on tactics in LCF" was never published anywhere but he did manage to publish [an application of it](https://doi.org/10.1145/9758.11326).
He had discovered a way to extend the LCF tactic mechanism with unification and combine it with backtracking search. I wanted this too.

The problem was, for unification to be meaningful for Martin-Löf type theory, it had to take account of variable binding. Luckily, I had spent a couple of weeks with Huet at Inria. One day, he had taken me aside to explain higher-order unification.
I probably understood only 2% of what he said, but something must have stuck in my mind.
It was enough for me to locate and study [his paper on the topic](https://doi.org/10.1016/0304-3975(75)90011-0).
It became clear that higher-order unification would indeed do the trick.
And then I realised that the old LCF approach was now obsolete:
no longer did we have to represent an inference rule by a *function* from premises to conclusions, paired with a *tactic* to perform the inverse map and justified by a validation function.
An inference rule could simply be declared, a piece of syntax to be used for forwards or backwards chaining as one wished.
Unifiable *existential variables* would simply work, with no further effort.
Adding a new logic could be as simple as specifying its primitives and typing its rules. 
That was the core idea: Isabelle would be a *generic* proof assistant.


### A Logical framework

My [first paper on Isabelle](https://doi.org/10.1016/0743-1066(86)90015-4) (also [here](https://doi.org/10.48456/tr-82))
describes some of this development, as well as my first experiments using Martin-Löf type theory.
Already this paper describes Isabelle as relying on Martin-Löf's "theory of expressions and arities", originally due to Frege and equivalent to the typed $\lambda$-calculus.

However, the 1986 version of Isabelle used a form of Skolemisation for quantifiers.
It seemed ad-hoc, and it was also inefficient. Inspired by the
[Edinburgh Logical Framework](https://doi.org/10.1145/138027.138060), I decided to create my own version, free of space-wasting proof objects.
I showed my effort to [Thierry Coquand](http://www.cse.chalmers.se/~coquand/), who informed me that I had simply re-invented intuitionistic higher order logic.
That was perfect, because I wouldn't have to puzzle out its theoretical properties. 
(Though I also wouldn't get anything published in *Journal of the ACM*.)
I simply invested in a copy of [Lambek and Scott](https://www.cambridge.org/gb/academic/subjects/mathematics/logic-categories-and-sets/introduction-higher-order-categorical-logic?format=PB&isbn=9780521356534).
In a [new paper](https://rdcu.be/cQnjt), I described Isabelle as it worked with this logical framework. 
Both papers refer extensively to both de Bruijn and Martin-Löf.

### Natural deduction

[*Natural deduction*](https://en.wikipedia.org/wiki/Natural_deduction) refers to a style of presenting a logic as a seet of inference rules, in which each rule refers to one logical symbol only. 
The rules for each connective are then independent of one another.
It may be contrasted with a [*Hilbert system*](https://en.wikipedia.org/wiki/Hilbert_system): one or two general inference rules, plus a system of axioms that typically combine connectives, as in
$(\neg \phi\to\neg\psi)\to(\psi\to\phi)$.
The Hilbert approach yields concise presentations of logic that are fine for developing metatheory but extremely difficult to use as an actual proof system.

One question asked by every Isabelle newbie is, why are there two versions of "implies" (namely $\Longrightarrow$ and $\to$) and two versions of "for all" ($\bigwedge$ and $\forall$)?
No other proof assistant does this: at least, not AUTOMATH, HOL or Coq.
The answer is that it is necessary in a logical framework for natural deduction.

One cannot even express a rule of inference without a notion of implication:
$\Phi\Rightarrow\Psi$.
Certain quantifier rules, and induction rules, take premises that are in effect universally quantified:
$[\bigwedge x.\,\Phi(x)]\Rightarrow\Psi$.
In a logical framework, which is supposed to support the natural deduction style, and for a variety of formalisms, it's essential to maintain a clean separation between the syntax of the formalism being supported (the *object logic*) and the *meta logic* itself.

Martin-Löf type theory as pure development of ND, in particular mathematical induction as the elimination rule for N

$\Sigma$ and $\Pi$

[David Schmidt](https://people.cs.ksu.edu/~schmidt/)??



### Stanford

A curious point: what did I learn from my four and a bit years at Stanford?

* Derek Oppen's [pretty printer](https://www.cs.tufts.edu/~nr/cs257/archive/derek-oppen/prettyprinting.pdf), which found its way into Cambridge LCF and Isabelle
* Nelson and Oppen's [congruence closure](https://dl.acm.org/doi/10.1145/322186.322198), which was nifty to know even though I never used it

People at Stanford had a bizarre obsession with first-order logic, which I, familiar with AUTOMATH, regarded as trivial. They in turn would have regarded with contempt AUTOMATH's punched card interaction model. Much of the work I did at Stanford was genuinely lousy.
