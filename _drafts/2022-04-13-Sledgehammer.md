---
layout: post
title:  "Sledgehammer: some history, some tips"
usemathjax: true 
tags: general
---

Sledgehammer is the subsystem that links Isabelle/HOL to automatic theorem provers like Vampire and Z3. It is so much part of the Isabelle user's everyday experience that it can be hard to remember a time before it was there. Let's see if I can dig up some memories, and also come up with some usage tips relevant today.

### The beginnings

My memories are hazy, but I was at a conference (very likely IJCAR 2001, in Siena) sitting on some steps and talking to a representative from Springer. He said something like "How can we increase the circulation of [*Journal of Automated Reasoning*](https://www.springer.com/journal/10817)?" Is it profitable?, I recall asking. "Oh yes!" Then perhaps you could try to hold down the cost of a subscription?

That conversation went nowhere, but I recall bumping into [Andrei Voronkov](http://voronkov.com), the architect of the [Vampire prover](https://vprover.github.io) and one of the tiny elite group of people who know how to make [resolution theorem proving](/papers/bachmair-hbar-resolution.pdf) actually work. It was his idea to see if we could combine our technologies and build something that was greater than both. I forget what happened in the interim, but by the time I received the [relevant grant](https://www.cl.cam.ac.uk/~lp15/Grants/Automation/), I found myself working instead with [Christoph Weidenbach](https://www.mpi-inf.mpg.de/departments/automation-of-logic/people/christoph-weidenbach) and his [SPASS prover](https://www.mpi-inf.mpg.de/departments/automation-of-logic/software/spass-workbench).
The Cambridge team included Jia Meng and Claire Quigley, and we already had a [super-preliminary paper](https://rdcu.be/cKaYp) ready for IJCAR 2004.

### Why automation?

We speak of automatic versus interactive theorem provers, but this dichotomy is misleading. (If there are two tools that do exactly the same thing, and one of them is fully automatic, what is the other one for?) In fact they do quite different things.

* *Automatic theorem provers* solve big, one-shot problems, typically in a fairly weak formalism like first-order logic, perhaps augmented with arithmetic.

* *Interactive theorem provers* are primarily specification editors. Users can build tangled nests of theories and theory libraries, and on the way, prove a variety of facts.

Automation is necessary because proofs reduced to bare logical rules can be unfeasibly long. You are getting nowhere unless your system regards a fact such as the following is trivial:

$$ 
\begin{align*}
C\not=\emptyset \quad\Longrightarrow\quad \bigcap_{x\in C} \bigl(A(x) \cap B(x)\bigr) =        
       \bigl(\bigcap_{x\in C} A(x)\bigr)  \cap  \bigl(\bigcap_{x\in C} B(x)\bigr) 
\end{align*}
$$

Isabelle could prove this automatically [already in 1988](https://rdcu.be/cIK8P). What about the proof assistant you use?

### Why resolution?

It was trendy to despise resolution theorem proving in the early 2000s. Other technologies, such as model checkers, BDDs and SAT solvers, were solving tonnes of real problems. Around that time, I had been using Isabelle to [verify cryptographic protocols](https://doi.org/10.3233/JCS-1998-61-205) (also [here](https://www.cl.cam.ac.uk/~lp15/papers/Auth/jcs.pdf)), with considerable success. I was happy to see an attempt to replicate my work using a Certain Other Ballyhooed System (not type theory based) fail utterly.
But I was stunned by the emergence of an automatic protocol verifier called
[TAPS](https://doi.org/10.3233/JCS-2003-11203), also [here](http://laser.inf.ethz.ch/2004/papers/cohen/paper2.pdf).
Its results were too good to be true, and I'm sorry to confess that my suspicious self asked its author, Ernie Cohen, a series of technical questions designed to see whether TAPS was really giving the right answers.
It was clear that Cohen indeed had access to a magic bullet. I could not understand his translation from protocol models to first-order logic. But I did note that his system relied on [SPASS](https://www.mpi-inf.mpg.de/departments/automation-of-logic/software/spass-workbench).

### The objectives and the obstacles

 