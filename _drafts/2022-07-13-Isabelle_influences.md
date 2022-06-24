---
layout: post
title:  "How Isabelle emerged from the trends of the 1980s"
usemathjax: true 
tags: general, de Bruijn, LCF, AUTOMATH, Martin-Löf type theory
---

The fault lines of today's proof assistant community are striking.
In one corner are researchers into advanced constructive type theories.
I get the impression (if Twitter is at all reliable) that they see their rivals as set theorists, though I'd be surprised if any set theorists were even aware of their work,
and hardly anybody uses set theory in a proof assistant.
Their true rivals with regard to interactive theorem proving are using classical simple type theory systems, such as Isabelle/HOL. But does anybody recognise the extent to which Isabelle has been influenced by Martin-Löf type theory?

### Isabelle: the beginnings

Isabelle was inspired by what I had learnt at Caltech in the mid-70s, at Cambridge, at INRIA-Rocquencourt and from people studying Martin-Löf type theory at [Chalmers University](https://www.chalmers.se/en/departments/cse/).
At Caltech I had learnt about [AUTOMATH](https://www.cs.ru.nl/~freek/aut/) from de Bruijn, while at Cambridge I was deeply involved with [Edinburgh LCF](https://doi.org/10.1098/rsta.2014.0234).
Through [Mike Gordon](https://www.cl.cam.ac.uk/archive/mjcg/) I established connections with Inria's [Gérard Huet](https://pauillac.inria.fr/~huet/) and the Chalmers group.

During the early 80s I was busy with a variety of projects, including a reimplementation of LCF. But I was deeply taken by Martin-Löf type theory and devoted perhaps a year of intensive work in order to produce [a paper](https://doi.org/10.1016/S0747-7171(86)80002-5) that nobody noticed:
I hadn't understood that in intuitionistic type theory, if you wanted a thing, and you couldn't easily get it by Russell's "honest toil", it was perfectly okay to consult your intuition and simply add the thing you wanted.
Of course, you had to have the right intuition or your extension would never get the official imprimatur.

At Chalmers, people were working on an implementation of type theory.
I had a copy of their code and I wasn't impressed. I was sure I could do a better job.
I would follow the LCF approach, but I would take care to be efficient.
In particular, I would definitely represent $\lambda$-binding with de Bruijn indices,
a technique that hadn't caught on yet. ([Nuprl](https://www.nuprl.org) didn't use it either.)

There I was, applying the LCF architecture to Martin-Löf type theory as it was in the early 1980s, still extensional.
I wanted to apply a powerful technique invented by
[Stefan Sokołowski](http://iis.pwsz.elblag.pl/~stefan/).
His modestly entitled "Note on tactics in LCF" was never published anywhere but he did manage to [publish an application of it](https://doi.org/10.1145/9758.11326).
He had discovered a way to extend the LCF tactic mechanism with unification and combine it with backtracking search. I wanted this too.

The problem was, for unification to be meaningful for Martin-Löf type theory, it had to take account of variable binding. Luckily, I had spent a couple of weeks with Huet at Inria. One day, he had taken me aside to explain higher-order unification.
I probably understood only 2% of what he told me, but it was enough for me to locate and study [his paper on the topic](https://doi.org/10.1016/0304-3975(75)90011-0).
It became clear that higher-order unification would indeed do the trick.
And then I realised that the old LCF approach (representing an inference rule by a function that delivered the conclusions given appropriate premises) was now obsolescent: an inference rule could simply be written out as a piece of syntax and used for forward or backward chaining as one wished.
That was the core idea of Isabelle.

###  Logical framework

 intuitionistic higher order logic

Thierry Coquand

Martin-Löf type theory as pure development of ND, in particular mathematical induction as the elimination rule for N

### Stanford

A curious point: what did I learn from my four and a bit years at Stanford?

* Derek Oppen's [pretty printer](https://www.cs.tufts.edu/~nr/cs257/archive/derek-oppen/prettyprinting.pdf), which found its way into Cambridge LCF and Isabelle
* Nelson and Oppen's [congruence closure](https://dl.acm.org/doi/10.1145/322186.322198), which was nifty to know even though I never used it

People at Stanford had a bizarre obsession with first-order logic, which I, familiar with AUTOMATH, regarded as trivial. They in turn would have regarded with contempt AUTOMATH's punched card interaction model. Much of the work I did at Stanford was genuinely lousy.
