---
layout: post
title:  "What is the point of formalising mathematics?"
usemathjax: true 
tags: [general, ALEXANDRIA, Mizar, AUTOMATH, type theory, verification, NG de Bruijn, MJC Gordon]
---

Vladimir Voevodsky was a leading proponent of the formalisation of mathematics. Until his death in 2017, he lectured frequently on the risks of errors in complicated technical arguments and the necessity to start using computers to verify the work of mathematicians. The opinions of a Fields Medallist naturally carried weight.
From the other side, the verification world, a major impetus for the formalisation of mathematics was the [floating point division bug](https://en.wikipedia.org/wiki/Pentium_FDIV_bug) in the Pentium, back in 1994.
(See my [prior post]({% post_url 2021-12-08-ALEXANDRIA %}) on the ALEXANDRIA project.)
However, Trybulec started his [Mizar](http://mizar.org) project in 1973,
de Bruijn had created the first version of [AUTOMATH]({% post_url 2021-11-03-AUTOMATH %}) by 1968, 
and [Wang had built an automatic theorem prover]({% post_url 2022-02-02-Formalising_Math_Set_theory %}) already in 1958, in hope of eventually formalising mathematics.
People have been dreaming about this for a long time.
What is the point?

### Pragmatic views at Cambridge

The Cambridge hardware verification group had a pragmatic focus. Until the Pentium division bug, if I recall correctly, our systems didn't even know about negative numbers.
Subsequent formalisations of the real numbers, special functions such as $\exp x$ and probability theory were aligned to specific verification objectives.
My colleagues expressed opinions that seem quite striking now: 

* that it was obvious that all mathematical material could be formalised 
* that doing so, absent an application, was a waste of time

Some expressed outright disdain for such time-wasters, who indulged themselves in the beautiful but useless while ignoring hardware/software verification issues of genuine importance.

I regret to confess that I accepted this view and sometimes discouraged students from working on the formalisation of pure mathematics.
I was even careful to include "verification" in the titles of two papers
([this one](https://rdcu.be/bRiRv) and [that one](https://rdcu.be/bRiRA))
on the formalisation of set theory.
I came up with the slogan that verification forced us to verify mathematics because today's computer systems (those connected with vehicles for example) are specified in terms of models of the real world which are heavily mathematical.

In actual fact, I have never verified anything resembling a real computer system or program in my entire career.

### Views from the AUTOMATH project

NG de Bruijn has [written at length](https://www.win.tue.nl/automath/) on AUTOMATH and his thoughts on mathematics. Curiously, his early papers (such as [AUT001](https://www.win.tue.nl/automath/archive/webversion/aut001/aut001.html): "AUTOMATH, a language for mathematics"
and [AUT002](https://www.win.tue.nl/automath/archive/webversion/aut002/aut002.html), "The mathematical language AUTOMATH"), give away little by means of motivation.
The former paper begins "AUTOMATH is a language intended for expressing detailed mathematical thoughts." Fortunately, his student van Benthem Jutting, in [his PhD thesis](https://pure.tue.nl/ws/files/1710991/23183.pdf), gives some specific reasons:

* "Mechanical verification will increase the reliability of certain kinds of proofs. A need for this may be felt where a proof is extremely long, complicated and tedious."
* "Mechanically verifiable languages set a standard by which informal language may be measured, and may thereby have an influence on the use of language in mathematics generally."
* "The use of such languages gives an insight into the structure of mathematical texts."

These sound like good aims, and incidentally, nobody accepts a PhD thesis that doesn't begin with motivation. Jutting added an additional reason:

> A further motive, for the author, was that the Work involved in the project appealed to him.

It's an excellent reason. John Harrison formalised a mountain of analysis, including the prime number theorem, with no conceivable verification application in mind.
I've done the same.
Formalising mathematics can be addictive!

### What's the formalisation scene like now?

There's an enormous amount of formalisation activity today. Some of it is focused on [univalent foundations](https://ncatlab.org/nlab/show/univalent+foundations+for+mathematics)/homotopy type theory, a field launched by Voevodsky and others (notably [Steve Awodey](https://awodey.github.io)),
about which I shall say little because I know even less.
But my impression is that this work is still foundational as opposed to formalising mathematical papers in quantity.
At the other extreme is the Xena project of
[Kevin Buzzard](https://xenaproject.wordpress.com), 
who has inspired a group of enthusiastic mathematicians:
the [Lean Prover Community](https://leanprover-community.github.io)
has formalised highly advanced mathematics using [Lean](https://leanprover.github.io).
Another angle is the [Formal Abstracts](https://formalabstracts.github.io) project of Thomas Hales (notable for proving the centuries-old [Kepler Conjecture](https://doi.org/10.1017/fmp.2017.1)), aiming to "express the results of mathematical publications in a computer-readable form".

My own [ALEXANDRIA project](https://www.cl.cam.ac.uk/~lp15/Grants/Alexandria/), funded by the ERC, is formalising material in Isabelle/HOL.
Other researchers around the world continue to formalise mathematical material, some of it highly advanced, in a great variety of systems.

### But what's the *scientific* point?

The effort and money being invested in formalisation cannot be justified on utilitarian grounds, but rather in the name of science.
Yes: strangely enough, in formalising mathematics we are doing empirical science.

The texts written and published by mathematicians are real-world phenomena every bit as much as say, whale songs. Empirical projects to test the adequacy of logical systems have been going on since de Bruijn and the formalisation of Landau’s *[Foundations of Analysis](http://homepages.math.uic.edu/~kauffman/Landau.pdf)*. Landau was a highly atypical text—meticulously detailed, accurate and elementary—but appropriate for that first attempt.

Projects such as ALEXANDRIA and Xena test the suitability of logical systems and their accompanying tools to formalise mathematics in all its variety. Buzzard stresses the importance of trying to tackle the most advanced definitions and proofs used by mathematicians today, hence his focus on perfectoid spaces. I’m handicapped by a complete lack of mathematical expertise beyond basic algebra, analysis and set theory, but my colleagues are doing impressive work, mostly in combinatorics and number theory. 

The most basic question being investigated is whether simple types or dependent types are best for formalising mathematics.
I know that much of the research community made up their mind on that issue long ago, but we have been here before.
In the 1980s, when researchers were starting to tackle hardware verification,
Mike Gordon opted for simple type theory while a rival, noting that hardware was full of $n$-bit registers, adders and busses, went for dependent types.
His system never got off the ground.
[PVS](https://pvs.csl.sri.com), with its distinctive version of dependent types, fared better.
Still, PVS never came close to displacing Gordon's HOL, despite being more sophisticated than in every way, and probably better funded.

So what are the advantages of simple types?

1. Simpler, more intuitive formalisms
2. Equality that works, where $A(i-1+1)=A(i)$ if $i\in\mathbb{N}^{+}$
3. Much better automation. And much more easily implemented.

And there seems to be something brittle about today's type theories.
Two definitions that are mathematically equivalent can behave differently to such an extent
that one can be forced to throw away one piece of work and redo it with the other definition, rather than simply proving the alternative form as a theorem and continuing from there.

### A deep problem that de Bruijn foresaw (in 1968!)

Whatever we try to formalise, it is always an experiment. One of the key questions always is, will it work this time? Or is there some sting in the tail?

One example I like to cite is Gödel’s proof of the [relative consistency of the axiom of choice](https://www.pnas.org/doi/pdf/10.1073/pnas.24.12.556) with the axioms of set theory. In his introduction he remarks 

> “What we shall prove is that, if a contradiction from the axiom of choice and the generalised continuum hypothesis were derived in Σ [the system of axioms of set theory], it could be transformed into a contradiction obtained from the axioms of Σ alone. This result is obtained by constructing within Σ …  a model Δ for set theory” 

and he continues by outlining his inner model method. His introduction is followed by some 66 pages (in the Oxford edition of his collected works) of technical results. Yet the headline claim (concerning our ability to effectively transform a contradiction in one system into a contradiction in another) is never even stated rigorously, let alone proved. 

That example is not a criticism of Gödel but simply a reminder of how easily mathematical thought can outstrip any formalism. We observe that Gödel has done all the tough technical work for us and left us to draw the obvious conclusion without going through the pointless tedium of describing the precise transformation he was alluding to. I [formalised some of his work](https://doi.org/10.1112/S1461157000000449) 20 years ago.
Working in Isabelle/ZF, I was able to formalise the class $L$ of constructible sets, to prove that $L$ satisfied $V=L$ (i.e. that $L$ "thinks" that all sets are constructible) and that $V=L$ implied the axiom of choice. Unfortunately, these could not be combined to conclude that $L$ satisfied the axiom of choice because the first claim was formalised by syntactic relativisation with respect to $L$. What I had done was to formalise Gödel’s technical results in a theorem proving environment for set theory, which mostly was natural enough, but to get everything to work it would have been necessary to treat the formalisation of set theory itself as a mathematical object. That would have made much of the work extremely difficult to express with a reasonable effort in any formal logic.

And yet, de Bruijn foresaw this situation:

> As to the question what part of mathematics can be written in AUTOMATH,
> it should first be remarked that we do not possess a workable definition of
> the word "mathematics". 
> Quite often a mathematician jumps from his mathematical language into a kind of metalanguage, obtains results there, and uses these
> results in his original context. It seems to be very hard to create a single
> language in which such things can be done without any restriction. Of course
> it is possible to have a language in which discussions about the language itself can be expressed, but that is not the difficulty. 
> The problem is to extend a given text T1, by means of a metalingual discussion T2
> (T2 talks about T1) and to put T2 in the context of T1, 
> instead of creating a new context where
> both T1 and T2 can take place. For, if T1 is placed in a new context, it is
> not the same text any more; anyway, it is not available at the places where
> the old T1 was available.
(AUT001, p. 4)

### Postscript

The full German text of Landau's *Grundlagen der Analysis* is [available online](https://www.cs.ru.nl/~freek/factor/grundlagen.tex.gz) as a plain TeX document, having apparently been re-typeset in a fit of madness by [Freek Wiedijk](https://www.cs.ru.nl/~freek/).
Take a look at his webpage on the [de Bruijn factor](https://www.cs.ru.nl/~freek/factor/).

Landau's text begins

> Ich setze nur logisches Denken und die deutsche Sprache als bekannt voraus.

"I assume given only logical thinking and the German language."
