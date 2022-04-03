---
layout: post
title:  "Sledgehammer: some history, some tips"
usemathjax: true 
tags: general
---

Sledgehammer is the subsystem that links Isabelle/HOL to automatic theorem provers like Vampire and Z3. It is so much part of the Isabelle user's everyday experience that it can be hard to remember a time before it was there. Let's see if I can dig up some memories, and also come up with some usage tips relevant today.

### The beginnings

My memories are hazy, but I was at a conference (very likely IJCAR 2001, in Siena) sitting on some steps and talking to a representative from Springer. He said something like "How can we increase the circulation of [*Journal of Automated Reasoning*](https://www.springer.com/journal/10817)?" Is it profitable?, I recall asking. "Oh yes!" Then perhaps you could try to hold down the cost of a subscription?

That conversation went nowhere, but I recall bumping into [Andrei Voronkov](http://voronkov.com), the architect of the [Vampire prover](https://vprover.github.io) and one of the tiny elite group of people who know how to make [resolution theorem proving](/papers/bachmair-hbar-resolution.pdf) actually work. It was his idea to see if we could combine our technologies and build something that was greater than both. I forget what happened in the interim, but by the time I received the [relevant grant](https://www.cl.cam.ac.uk/~lp15/Grants/Automation/), I found myself also working with [Christoph Weidenbach](https://www.mpi-inf.mpg.de/departments/automation-of-logic/people/christoph-weidenbach) and his [SPASS prover](https://www.mpi-inf.mpg.de/departments/automation-of-logic/software/spass-workbench).
The Cambridge team included Jia Meng and Claire Quigley, and we already had a [preliminary paper](https://rdcu.be/cKaYp) ready for IJCAR 2004.

### Why automation?

We speak of automatic versus interactive theorem provers, but this dichotomy is misleading. (If there are two tools that do exactly the same thing, and one of them is fully automatic, what is the other one for?) In fact they do quite different things.

* *Automatic theorem provers* solve big, one-shot problems, typically in a fairly weak formalism like first-order logic, perhaps augmented with arithmetic.

* *Interactive theorem provers* are primarily specification editors. Users can build tangled nests of theories and theory libraries, and on the way, prove a variety of facts.

Automation is necessary because proofs reduced to bare logical rules can be unfeasibly long. You are going to struggle unless your prover regards a fact such as this is trivial:

$$ 
\begin{align*}
C\not=\emptyset \quad\Longrightarrow\quad \bigcap_{x\in C} \bigl(A(x) \cap B(x)\bigr) =        
       \bigl(\bigcap_{x\in C} A(x)\bigr)  \cap  \bigl(\bigcap_{x\in C} B(x)\bigr) 
\end{align*}
$$

Isabelle could prove this automatically [already in 1988](https://rdcu.be/cIK8P). What about the proof assistant you use?

### Why resolution?

It was trendy to despise resolution theorem proving in the early 2000s. Other technologies, such as model checkers, BDDs and SAT solvers, were solving tonnes of real problems. Around that time, I had been using Isabelle to [verify cryptographic protocols](https://doi.org/10.3233/JCS-1998-61-205) (also [here](https://www.cl.cam.ac.uk/~lp15/papers/Auth/jcs.pdf)), with considerable success. I was quietly pleased to see an attempt to replicate my work using a Certain Other Ballyhooed System (not type theory based) fail utterly.

There then appeared an automatic protocol verifier called
[TAPS](https://doi.org/10.3233/JCS-2003-11203) (alternative [link](http://laser.inf.ethz.ch/2004/papers/cohen/paper2.pdf)).
Its results were too good to be true, and I'm sorry to confess that I was suspicious. I asked the author, Ernie Cohen, a series of technical questions designed to find out whether TAPS really was giving the right answers.
It was: Cohen possessed some sort of magic bullet. I could not understand his translation from protocol models to first-order logic. But I did note that his system proved theorems using [SPASS](https://www.mpi-inf.mpg.de/departments/automation-of-logic/software/spass-workbench).

### The objectives and the obstacles

The original proposal (written in 2003) said

> Twenty years ago, when many users had to share a single computer, a proof command could realistically take at most a few seconds of processor time. Now that 2GHz processors are commonplace, we should abandon the traditional mode of interaction, where the proof tool does nothing until the user types a command. Background processes (perhaps on several computers) should try to prove the outstanding subgoals. 

It was clearly time to ask the hardware to do the hard work.
By 2005, the objectives had become more clear-cut, as we can see in an
[early paper](https://doi.org/10.1016/j.ic.2005.05.010)
also [here](https://www.cl.cam.ac.uk/~lp15/papers/Automation/info-and-comp.pdf):

* user interaction should be minimal:
 provers should run in the background;
 users should not have to select relevant lemmas
* automatic provers should not be trusted 
* proofs should be delivered in source form 

These criteria came from reading about prior efforts to combine systems, which however impressive tended to require users to do quite a bit of work up front. Not trusting the external prover is intrinsic to our [LCF ethos]({% post_url 2022-01-05-LCF %}).
So part of our task is somehow to *extract* a valid Isabelle/HOL proof from the proof emitted by Vampire or SPASS.
And now we were also using the [E prover](https://wwwlehre.dhbw-stuttgart.de/~sschulz/E/E.html), by [Stephan Schulz](https://wwwlehre.dhbw-stuttgart.de/~sschulz/DHBW_Stephan_Schulz/Stephan_Schulz.html).

The difficulties were already clear in that early paper. It included techniques for encoding the type polymorphism and type classes of Isabelle/HOL in first-order logic, and declared the necessity of techniques to identify relevant lemmas automatically.

### The first working version of sledgehammer

Sledgehammer became fully operational in 2007. Papers from that era described techniques for translating [higher-order problems into first-order clauses](https://rdcu.be/cKr2w) (the published title of this paper is actually a typographical error) and
a simple but workable [relevance filter](https://doi.org/10.1016/j.jal.2007.07.004) (see also [here](https://www.cl.cam.ac.uk/~lp15/papers/Automation/filtering-jal.pdf)).
Both papers were joint with Jia Meng and described techniques that had been refined by expanding vast amounts of computer time on a processor bank.

The task of translating resolution proofs into Isabelle/HOL proofs defeated us. We resorted to importing [Joe Hurd's](http://www.gilith.com) own resolution prover, [Metis](http://www.gilith.com/metis/), which had been designed with the specific aim of being integrated within LCF-style proof assistant (HOL4). Metis was not at all competitive with Vampire or SPASS, but it could do the job if given an absolutely minimal set of axioms, which we could extract from the proof emitted by the external prover. In short, the external prover was being used merely to check that a proof existed and from which specific facts. Someone told me that Christoph Weidenbach was shocked to hear this, but whatever works, works.

So the objective of delivering proofs to the user in source form boiled down to returning a call to `metis` with the appropriate set of lemmas. This [part of the work](https://rdcu.be/cKr4U) was done by another postdoc, Kong Woei Susanto.

### The next generation

I know much less about what happened since 2007. It happened at [TU Munich](https://www.in.tum.de/en/cover-page/), and I was distracted by other research projects.
It's not surprising that others wanted to create a new version of sledgehammer: the original was a prototype, and frankly it was a mess. The single greatest flaw: its translation from Isabelle/HOL into first-order logic was unsound, so "proofs" were regularly returned that could not be run.

The Munich group conducted a big [empirical evaluation](https://rdcu.be/cKr5t) and only a year later it had been extended to also call [SMT solvers](https://rdcu.be/cKr74).
These projects were done by Jasmin Blanchette, Sascha Böhme and Tobias Nipkow.
[Blanchette](https://www.cs.vu.nl/~jbe248/) has gone on to pursue an [extended project](https://matryoshka-project.github.io) related to sledgehammer, including efficient, sound translations (unsoundness is completely gone now), vastly improved proof reconstruction and better support for higher-order logic theorem proving (e.g. through [Zipperposition](https://github.com/sneeuwballen/zipperposition)).

### Usage tips

Although sledgehammer offers configuration free one click invocation, there are some useful tips in the [manual](https://isabelle.in.tum.de/doc/sledgehammer.pdf).
I almost always run sledgehammer using the jEdit panel, but occasionally it's a good idea to create a specialised invocation, and you need to read the manual for that.
I tend to do this when the panel found a proof but a better one might be found if more time was allocated.

The most obvious advice: keep your subgoals simple. A simple tip is to first apply `auto`, then use sledgehammer to prove each of the resulting goals. This proof will be a mess and will require restructuring, but at least you will know that there is a proof.

Goals containing giant set comprehensions can be difficult even for humans, let alone the computer.
Introduce abbreviations judiciously to avoid repeated terms, especially constructions containing bound variables.

If you've done both of those things and sledgehammer still fails, see if you can think of some intermediate fact that follows from your assumptions and that could help to prove your conclusion. If sledgehammer can prove that fact, you have made progress.

### That last snarky remark

One of the reasons I prefer higher-order logic to depend on type theories — apart from simple semantics, equality that works and no need to put everything in the kernel — is that dependent types seem to make automation much more difficult. Groups with access to institutional support and steady, ample resources still don't seem to have duplicated what had been built at Cambridge on a single £250K grant.
And please don't say "dependent type checking makes other automation unnecessary". I keep hearing this.
