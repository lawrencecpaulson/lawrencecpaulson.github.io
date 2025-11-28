---
layout: post
title:  50 years of proof assistants
usemathjax: true 
tags: [memories, LCF, HOL, Isabelle, Coq, MJC Gordon]
---
Crackpots ranging from billionaire Peter Thiel to random YouTube influencers claim that science has been stagnating for the past 50 years. They admit that computing is an exception: they don't pretend that my personal 32GB laptop is not an advance over the 16MB mainframe that served the whole Caltech community when I was there. Instead they claim that advances in computing were driven solely by industrial research, quite overlooking the role of academia 
and government funding
in pushing the VLSI revolution, RISC processor design, networking, hypertext, virtual memory and indeed computers themselves. As for the industrial research,
most of it came from just two "blue sky" institutes – [Bell Labs](https://sites.stat.columbia.edu/gelman/research/published/bell.pdf) 
and [Xerox PARC](https://spectrum.ieee.org/xerox-parc) – that closed a long time ago. Giving away the goods is no way to make a profit, but without academic give-and-take it is hard to make progress. Anyway, let's look at 50 years of progress in LCF-style proof assistants.

### Edinburgh LCF

The first instance of LCF was Stanford LCF, developed by Robin Milner in 1972, but it was not an LCF-style proof assistant. LCF meant "Logic for Computable Functions", a quirky formalism based on Scott domains and intended for reasoning about small functional programs. But "LCF-style proof assistant" means one that, like Edinburgh LCF, was coded in some form of 
the ML programming language and provided a proof kernel, 
encapsulated in an abstract type definition, to ensure that a theorem could only be generated 
by applying inference rules to axioms or other theorems:

> … the ML type discipline is used… so that—whatever complex procedures are defined—all values of type `thm` must be theorems, as only inferences can compute such values…. This security releases us from the need to preserve whole proofs… — an important practical gain since large proofs tended to clog up the working space… [*Edinburgh LCF*, page IV]

Edinburgh LCF was first announced in 1975, which conveniently is exactly 50 years ago, 
at a *Conference on Proving and Improving Programs* held at Arc-et-Senans. 
The [user manual](https://link.springer.com/book/10.1007/3-540-09724-4), published in the Springer lecture notes series, came out in 1979.
Edinburgh LCF introduced some other principles that people still adhere to today:

* inference rules in the *natural deduction* style, with a dynamic set of assumptions
* a *goal-directed* proof style, where you start with the theorem statement and work backwards
* a structured system of *theories* to organise groups of definitions

Edinburgh LCF had its own version of the ML language.
It supported a fragment of first-order logic containing
the logical symbols $\forall$, $\land$ and $\to$ along with
the relation symbols $\equiv$ and $\sqsubseteq$.
It introduced proof tactics and also *tacticals*:
operators for combining tactics.
Tactics supported goal-directed proof,
but Edinburgh LCF had no notion of the current goal or anything to help the user manage the tree of subgoals.
Its user interface was simply the ML top level and the various theorem-proving primitives were simply ML functions.
ML stood for *metalanguage*, since managing the process of proof was its exact job.

Avra Cohn and Robin Milner wrote a [report](https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-20.html) 
on proving the correctness of a parsing algorithm 
using Edinburgh LCF. 
The proof consists of one single induction followed by 
a little simplification and other reasoning.
The report includes a succinct description of Edinburgh LCF and
is a nice snapshot of the state of the art in 1982.

### Cambridge LCF and HOL

I arrived at Cambridge in 1982, full of youthful enthusiasm, 
to join a project run by Robin Milner and Mike Gordon.
I remember telling Mike that it would be great 
if one day we could formalise the Prime Number Theorem.
I hardly knew what the theorem was about or how to prove it, 
but my college roommate had told me it was really deep.

Disappointed to discover that we only had $\forall$, $\land$ and $\to$,
I set out to fix that, to support full first-order logic. 
I ended up changing so much 
(backwards compatibility is overrated) that people eventually shamed me into writing my own [user manual](https://www.cambridge.org/gb/universitypress/subjects/computer-science/programming-languages-and-applied-logic/logic-and-computation-interactive-proof-cambridge-lcf).
Cambridge LCF never caught on because, well, 
nobody liked the LCF formalism.
But I used it for a development that seemed big at the time: to [verify the unification algorithm](https://doi.org/10.1016/0167-6423(85)90009-7).
This development was later [ported to Isabelle](https://isabelle.in.tum.de/dist/library/HOL/HOL-ex/Unification.html).
It contains 36 inductions, so we were making progress.
And this takes us to 1985, exactly 40 years ago;
see also [this survey](https://doi.org/10.48456/tr-54) of the state of play.
But there was almost no mathematics: no negative numbers and no decimal notation, so you could not even write 2+2=4.

Cambridge LCF was in itself a dead end, but because it included a much faster ML compiler,
it ended up [being incorporated]({% post_url 2022-09-28-Cambridge_LCF %}) into a lot of other proof assistants, notably Mike's [HOL88](https://github.com/theoremprover-museum/HOL88). 
And just like that, [hardware verification]({% post_url 2023-01-04-Hardware_Verification %}) became a reality. 
Although software verification seemed stuck in the doldrums,
a couple of production-ready chip designs were verified!
Mike's explanation was that hardware verification was simply easier.
Another reason, I think, is that code (as opposed to an algorithm) never gets 
frozen the way a chip design does. 
There's never a point you can say "right, this is our target".

Also in 1985, I was working on experiments that would [lead to Isabelle]({% post_url 2022-07-13-Isabelle_influences %}).
It would be like LCF but would support constructive type theory, 
crucially allowing both unification and backtracking, like in Prolog.
But there was no working system yet. And that was the state of play 40 years ago.

### Proof assistants come of age

We confidently approached 1990 with tools that worked, 
including a new standard for the ML language and two compilers for it.
Isabelle was coded in [Standard ML](https://www.lfcs.inf.ed.ac.uk/software/ML/) from the start, while HOL88 was ported from the Cambridge LCF version of ML 
to the new standard, emerging as HOL90.
Versions of HOL were being used in institutes around the world. 
But I am still not certain whether negative numbers were supported (can somebody help me?).
Our weak support for arithmetic may seem odd 
when our research community was aware that the real numbers 
had been [formalised in AUTOMATH]({% post_url 2022-06-22-Why-formalise %}), 
but we didn't seem to need them. 

Then, in 1994, came the Pentium with its [FDIV bug](https://www.techradar.com/news/computing-components/processors/pentium-fdiv-the-processor-bug-that-shook-the-world-1270773): 
a probably insignificant but detectable error in floating-point division that cost Intel nearly half a billion dollars.
John Harrison, a student of Mike's, decided to devote his PhD research
to the verification of floating-point arithmetic.
By June 1996 he had submitted an extraordinary [thesis](https://doi.org/10.48456/tr-408), 
*Theorem Proving with the Real Numbers*,
which described a formidable series of achievements:

* a formalisation of the real member system in HOL
* formalised analysis including metric spaces, sequences and series, limits, continuity and differentiation, power series and transcendental functions, integration
* proper numerals represented internally by symbolic binary, and calculations on them
* computer algebra techniques including a decision procedure for real algebra
* tools and techniques for floating-point verification by reference to the IEEE standard

This thesis, which I had the privilege to examine, won a Distinguished Dissertation Award
and was [published as a book](https://link.springer.com/book/10.1007/978-1-4471-1591-5) by Springer.
So by the middle of the 1990s, which was 30 years ago, 
we had gone from almost no arithmetic to a decent chunk of formalised real analysis
that was good enough to verify actual floating-point algorithms.

Stepping aside from HOL for a moment, other proof assistants had made great progress 
by the mid 1990s.
The addition of inductive definitions to the calculus of constructions
gave us the [calculus of inductive constructions](https://rdcu.be/eR7e8),
which in essence is the formalism used today by Rocq and Lean.
The very first release of Isabelle/HOL [happened in 1991](https://rdcu.be/eR7gl), 
primarily the work of Tobias Nipkow.
Isabelle/ZF, which was my project, formalised axiomatic set theory 
to some [quite deep results](https://arxiv.org/abs/cs/9612104).

This period also saw something of an arms race in automation.
My earlier, Prolog-inspired vision of backtracking search
had led to some [fairly general automation](https://doi.org/10.48456/tr-396) that was effective not just in standard predicate logic 
but with any theorems were expressed in a form suitable for forward or backward chaining.
I had also done experiments with classical automatic techniques such as model elimination, which, although pathetic compared with automatic provers of that era, 
was good enough to troll users on the `hol-info` mailing list.
Soon I had provoked John Harrison to build a superior version of ME for HOL Light.
Later, Joe Hurd built his `metis` superposition prover, which found its way into HOL4.
Not to be outdone, Tobias made Isabelle's simplifier the best in its class incorporating a number of sophisticated refinements, including some great ideas from Nqthm.

Twenty years from the start of this chronology we now had 
several reasonably mature and powerful systems, including Isabelle/ZF, Isabelle/HOL, 
multiple versions of the HOL system, and Coq (now Rocq).[^1]
As the 1990s moved towards their millennial end, we were ready to do big things.

[^1]: Cool things were also done in [LEGO](https://era.ed.ac.uk/handle/1842/504), another type theory proof assistant, but sadly it soon fell by the wayside. And they were sued by some crazy guys from Billund.

### The first great applications

Our next milestone is 2005, just 20 years ago, and the big thing that caught everyone's eye
was [George Gonthier's formalisation](https://rdcu.be/eSgTy) (in Coq) 
of the Four Colour Theorem.
Most educated people had heard of the theorem already, 
and its history is fascinating. 
Numerous proofs had been attempted and rejected since the mid 19th century.
The 1977 proof by Appel and Haken was questioned 
because it relied on a lot of ad-hoc computer code.
Suddenly, despite the still unwelcome involvement of computers, 
no one could doubt the theorem anymore.

At the opposite extreme was [my own formalisation](https://doi.org/10.1112/S1461157000000449) of Gödel's proof of the relative consistency of the axiom of choice in Isabelle/ZF.
This was the apex of my ZF work, technically difficult but incomprehensible to most people.
My early dream of having a formalisation of the Prime Number Theorem came true in 2005
when Jeremy Avigad [formalised](https://arxiv.org/abs/cs/0509025) the theorem in Isabelle.
Somewhat later, John Harrison [formalised a different proof](https://rdcu.be/eShga) in HOL Light.
And there was much more. Without any doubt, our systems were capable of serious mathematics.

What about verification? During this period, 
I did a lot of work on the 
[verification of cryptographic protocols](https://doi.org/10.3233/JCS-1998-61-205), 
also [here](https://doi.org/10.48550/arXiv.2105.06319).
These secure Internet connections and other network communications;
they are valuable when you need to know who is on the other end 
and need to keep messaging secure from eavesdropping and tampering.

Perhaps the most consequential achievement of this period was Mike Gordon's collaboration 
with Graham Birtwistle and Anthony Fox to [verify the ARM6 processor](https://rdcu.be/eShzn).
Graham, at Leeds, formally specified the instruction set architecture of the processor 
(i.e. the assembly language level), while Mike and Anthony at Cambridge verified the implementation of that architecture in terms of lower level hardware components.
Eventually a number of other processors were similarly specified, and some verified.
Without any doubt, our systems were capable of serious verification.

Despite of the focus on applications in this section, 
system development continued in the run-up to 2005.
I am only familiar with Isabelle development, but they were tremendous:
* the *Isar language* for structured, legible proofs
* *axiomatic type classes*, providing principled overloading
* *counterexample finders*: [Quickcheck](https://doi.org/10.1109/SEFM.2004.1347524) and Refute (now Nitpick)
* *code generation* from the executable fragment of higher-order logic, and reflection
* *sledgehammer* was under active development, but only ready a couple of years later.

### The March of formalised mathematics

odd order theorem



[Flyspeck](https://github.com/flyspeck/flyspeck) 2014