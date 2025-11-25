---
layout: post
title:  50 years of proof assistants
usemathjax: true 
tags: [memories, LCF, HOL, Isabelle, Coq]
---
Crackpots ranging from billionaire Peter Thiel to random YouTube influencers claim that science has been stagnating for the past 50 years. Of course they admit that computing is an exception: they don't pretend that my personal 32GB laptop is not an advance over the 16MB mainframe that served the whole Caltech community when I was there. Instead they claim that advances in computing were driven solely by industrial research, quite overlooking the role of academia in pushing the VLSI revolution, RISC processor design, networking, hypertext, virtual memory and indeed computers themselves. Most of what was industrial research came from just two "blue sky" institutes – [Bell Labs](https://sites.stat.columbia.edu/gelman/research/published/bell.pdf) 
and [Xerox PARC](https://spectrum.ieee.org/xerox-parc) – that closed a long time ago. Giving away the goods is no way to make a profit, but without academic give-and-take it is hard to make progress. Anyway, let's look at 50 years of progress in LCF-style proof assistants.

### Edinburgh LCF

The first instance of LCF was Stanford LCF, developed by Robin Milner in 1972, but it was not an LCF-style proof assistant. LCF meant "Logic for Computable Functions", a quirky formalism based on Scott domains and intended for reasoning about small functional programs. But "LCF-style proof assistant" means one that, like Edinburgh LCF, was coded in some form of 
the ML programming language
and provided a proof kernel, 
encapsulated in an abstract type definition, to ensure that a theorem could only be generated 
by applying inference rules to axioms or other theorems.

Edinburgh LCF was first announced in 1975, which conveniently is exactly 50 years ago, 
at a *Conference on Proving and Improving Programs* held at Arc-et-Senans. 
(The [user manual](https://link.springer.com/book/10.1007/3-540-09724-4), published in the Springer lecture notes series, came out in 1979.)
Edinburgh LCF had its own version of the ML language.
It supported a fragment of first-order logic containing
the logical symbols $\forall$, $\land$ and $\to$ along with
the relation symbols $\equiv$ and $\sqsubseteq$.
It introduced proof tactics and also *tacticals*:
operators for combining tactics.
Tactics supported goal-directed proof,
but Edinburgh LCF had no notion of the current goal or anything to help the user manage the tree of subgoals.
Its user interface was simply the ML top level and the various theorem-proving primitives were simply ML functions.
ML stood for *metalanguage*, 
since managing the process of proof was its exact job.

Avra Cohn and Robin Milner wrote a [report](https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-20.html) 
on proving the correctness of a parsing algorithm 
using Edinburgh LCF. 
The proof consists of one single induction followed by 
a little simplification and other reasoning.
The report includes a succinct description of Edinburgh LCF and
is a nice snapshot of the state of the art in 1982.

### Cambridge LCF

I arrived at Cambridge in 1982, idealistic and eager.
I was disappointed that we only had $\forall$, $\land$ and $\to$,
so I set out to put in the missing connectives of predicate logic. 
I ended up changing so much 
(backwards compatibility is overrated) that people eventually shamed me into writing my own [user manual](https://www.cambridge.org/fr/universitypress/subjects/computer-science/programming-languages-and-applied-logic/logic-and-computation-interactive-proof-cambridge-lcf).
Cambridge LCF never caught on because, well, 
nobody liked the LCF formalism.
But I used it for a development that seemed big at the time: to [verify the unification algorithm](https://doi.org/10.1016/0167-6423(85)90009-7).
This development was later [ported to Isabelle](https://isabelle.in.tum.de/dist/library/HOL/HOL-ex/Unification.html).
It contains 36 inductions, so we were making progress.
And this takes us to 1985, exactly 40 years ago;
see also [this survey](https://doi.org/10.48456/tr-54) of the state of play.
But there was almost no mathematics: no negative numbers, 
and even to write 2+2=4 you had to use unary notation.

XXXX

I've written much more about these developments 
in an [earlier post]({% post_url 2022-09-28-Cambridge_LCF %}).
