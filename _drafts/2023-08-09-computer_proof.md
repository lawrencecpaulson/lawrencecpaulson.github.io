---
layout: post
title:  When is a computer proof a proof?
tags: [philosophy, Imre Lakatos]
---

We have come a long way since the notorious 1976 proof of the four colour theorem
by Appel and Haken, but many mathematicians still distrust computers;
and even those who trust often struggle to agree on the computer's precise role.
In the four colour proof, an assembly language program was used to check 1936 "reducible configurations", and people were rightly concerned about errors in the code.
However, the Appel–Haken proof also required "the investigation by hand
about ten thousand neighbourhoods of countries with positive charge",[^1]
and nobody seemed bothered about the possibility of errors there.
Computer algebra systems were emerging around that time and would eventually
become widely used in many branches of science and engineering,
although I can't imagine a computer algebra calculation being uncritically accepted
by any mathematics journal.
Today, I and others hope to see mathematicians using proof assistants in their work.
Whether machine proofs will be accepted as valid requires serious thought
about the nature of mathematical proof.

[^1]: Robin Wilson, Four Colours Suffice: How the Problem Was Solved (Princeton, 2002)

### The idea of mathematical certainty

In a [previous post]({% post_url 2022-07-27-Truth_Models %}), I've discussed the difference
between scientific knowledge, which sometimes needs to be revised 
in the light of new evidence, contrasted with mathematical truth,
which is not evidenced-based. I also mentioned 
the work of [Imre Lakatos](https://plato.stanford.edu/entries/lakatos/), a philosopher
who studied a particular theorem (Euler’s polyhedron formula) for which counterexamples
were actually discovered. Lakatos' discussion is almost entirely focused on
strategies for dealing with counterexamples, e.g.

* *monster-barring*: modifying your definition to exclude the counterexamples regardless of how ad hoc it looks
* *exception-barring*: retreating to an overly conservative but completely safe definition

And I have to remark, when you have one theorem and one definition that you are allowed to change at will, it looks like cheating! More commonly, errors are found in proofs (rather than in definitions) but can be fixed, with the theorem statement at worst marginally affected.

I wonder if we still have in mind a group of students watching Archimedes draw circles
in the sand and all agreeing that his proof is valid? We don't have that immediacy any more.
Today, doing mathematics necessarily requires trusting 
tens of thousands of pages of other people's work.
So, how about trusting some software?

### The fundamental characteristics for proofs

A [recent paper](https://www.degruyter.com/document/doi/10.1515/krt-2022-0015/html)[^2]
enumerates some widely accepted characteristics of mathematical proofs:
 
1. Proofs are convincing.
2. Proofs are surveyable.
3. Proofs are formalisable. 

I like these because, ipso facto, any proof conducted using a proof assistant
is not merely formalisable but has literally just been formalised,
both in the sense of being expressed in some sort of tactic language
and in the sense of having been reduced to low-level logical inferences.
Not all formal proofs are surveyable with some certainly are, 
with both Mizar and Isabelle/HOL's Isar language specifically designed for legibility.
As for convincing: there can be no handwaving in a machine proof.
As a rule, machines are much harder to convince than a knowledgeable mathematician,
and machine proof contains not gaps but rather excessive detail.

[^2]: Parshina, Katia. "Philosophical assumptions behind the rejection of computer-based proofs" *KRITERION – Journal of Philosophy*, 2023