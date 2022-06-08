---
layout: post
title:  "What is the point of formalising mathematics?"
usemathjax: true 
tags: general, ALEXANDRIA, AUTOMATH, de Bruijn
---

Vladimir Voevodsky  was a leading proponent of the formalisation of mathematics, lecturing frequently on the risks of errors in complicated technical arguments and the necessity to start using computers to verify the work of mathematicians. The opinions of a Fields Medallist naturally carried weight.
From the other side, the verification world, one impetus for the formalisation of mathematics was the [floating point division bug](https://en.wikipedia.org/wiki/Pentium_FDIV_bug) in the Pentium, back in 1994.
(See my [prior post]({% post_url 2021-12-08-ALEXANDRIA %}) on the ALEXANDRIA project.)
However, de Bruijn had created the first version of [AUTOMATH]({% post_url 2021-11-03-AUTOMATH %}) by 1968, and Wang had built an automatic theorem prover already in 1958, in hope of eventually formalising mathematics.
What is the point?

### Pragmatic views at Cambridge

The Cambridge hardware verification group had a pragmatic focus. Until the Pentium division bug, if I recall correctly, our systems didn't even know about negative numbers.
Subsequent formalisations of the real numbers, special functions such as the exponential and probability theory were aligned to specific verification tasks.
My colleagues expressed opinions that seem quite striking now: that it was obvious that all mathematical results could be formalised and that doing so, absent an application, was a waste of time.
Some indeed expressed disdain for such time wasters, who indulged themselves while ignoring hardware/software verification issues of genuine importance.
I regret to say that I accepted this view and sometimes discouraged students from working on the formalisation of pure mathematics; I even wrote two papers ([this one](https://rdcu.be/bRiRv) and [that one](https://rdcu.be/bRiRA))
about the formalisation of set theory, being careful to include "verification" in the title.
I came up with the slogan that verification forced us to verify mathematics because today's computer systems (those connected with vehicles for example) are specified in terms of models of the real world which are heavily mathematical.

### Views from the AUTOMATH project

NG de Bruijn has [written at length](https://www.win.tue.nl/automath/) on AUTOMATH and his philosophical thoughts on mathematics. Curiously, his early papers (such as [AUT001](https://www.win.tue.nl/automath/archive/webversion/aut001/aut001.html): "AUTOMATH, a language for mathematics"
and [AUT002](https://www.win.tue.nl/automath/archive/webversion/aut002/aut002.html), "The mathematical language AUTOMATH"), give away little by means of motivation.
The former paper begins "AUTOMATH is a language intended for expressing detailed mathematical thoughts." Fortunately, his student van Benthem Jutting, in [his PhD thesis](https://pure.tue.nl/ws/files/1710991/23183.pdf), gives us some hints:

1. "Mechanical verification will increase the reliability of certain kinds of proofs. A need for this may be felt where a proof is extremely long, complicated and tedious."
2. "Mechanically verifiable languages set a standard by which informal language may be measured, and may thereby have an influence on the use of language in mathematics generally."
3. "The use of such languages gives an insight into the structure of mathematical texts."

These sound like good reasons, and incidentally, nobody accepts a PhD thesis that doesn't begin with the motivations. Jutting added an additional reason:

> A further motive, for the author, was that the Work involved in the project appealed to him.

It's an excellent reason when we reflect that John Harrison formalised a mountain of analysis, including the prime number theorem, with no conceivable verification application in mind.

### xxx

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

Mathematical texts as they are published are real-world phenomena every bit as much as say, whale songs. Empirical projects to test the adequacy of logical systems have been going on since de Bruijn and the formalisation of Landau’s Foundations of Analysis. Landau was a highly atypical text—meticulously detailed, accurate and elementary—but appropriate for that first attempt.

What we see today are projects (such as my own ALEXANDRIA, mostly based on Isabelle/HOL, and Kevin Buzzard’s Xena) to test the suitability of logical systems and their accompanying tools to formalise mathematics in all its variety. Buzzard has upped the game by stressing the importance of trying to tackle the kinds of definitions and proofs used by mathematicians today, hence his focus on perfectoid spaces. I’m handicapped by a complete lack of mathematical expertise beyond basic algebra and analysis, but my colleagues are also doing impressive work, mostly in combinatorics and number theory. Whatever we try to formalise, it is always an experiment and one of the key questions always is, will it work this time? Or is there some sting in the tail?

One example I like to cite is Gödel’s proof of the consistency of the axiom of choice with the axioms of set theory. In his introduction he remarks “What we shall prove is that, if a contradiction from the axiom of choice and the generalised continuum hypothesis were derived in Σ [the system of axioms of set theory], it could be transformed into a contradiction obtained from the axioms of Σ alone. This result is obtained by constructing within Σ …  a model Δ for set theory …” and he continues by outlining his inner model method. His introduction is followed by some 66 pages (in the Oxford edition of his collected works) of technical results. Yet the headline claim (concerning our ability to effectively transform a contradiction in one system into a contradiction in another) is never even stated rigorously, let alone proved. 

That example is not a criticism of Gödel but simply a reminder of how easily mathematical thought can outstrip any formalism. We observe that Gödel has done all the tough technical work for us and left us to draw the obvious conclusion without going through the pointless tedium of describing the precise transformation he was alluding to. I formalised some of his work 20 years ago:

https://doi.org/10.1112/S1461157000000449

Working in Isabelle/ZF, I was able to formalise the class L of constructible sets, to prove that L satisfied V=L and that V=L implied the axiom of choice. Unfortunately, these could not be combined to conclude that L satisfied the axiom of choice because the first claim was formalised by syntactic relativisation with respect to L. What I had done was to formalise Gödel’s technical results in a theorem proving environment for set theory, which mostly was natural enough, but to get everything to work it would have been necessary to treat the formalisation of set theory itself as a mathematical object. That would have made much of the work extremely difficult to express with a reasonable effort in any formal logic.
