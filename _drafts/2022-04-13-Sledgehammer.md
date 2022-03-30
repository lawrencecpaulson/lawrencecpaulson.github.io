---
layout: post
title:  "Sledgehammer: some history, some tips"
usemathjax: true 
tags: general
---

Sledgehammer is the subsystem that links Isabelle/HOL to automatic theorem provers like Vampire and Z3. It is so much part of the Isabelle user's everyday experience that it can be hard to remember a time before it was there. Let's see if I can dig up some memories, and also come up with some usage tips relevant today.

### The beginnings

My memories are hazy, but I was at a conference (very likely IJCAR 2001, in Siena) sitting on some steps and talking to a representative from Springer. He said something like "How can we increase the circulation of *Journal of Automated Reasoning*?" Is it profitable?, I recall asking. "Oh yes!" Then perhaps you could try to hold down the cost of a subscription?

That conversation went nowhere, but I recall bumping into [Andrei Voronkov](http://voronkov.com), the architect of the [Vampire prover](https://vprover.github.io) and one of the tiny elite group of people who know how to make [resolution theorem proving](/papers/bachmair-hbar-resolution.pdf) actually work. It was his idea to see if we could combine our technologies and build something that was greater than both. I forget what happened in the interim, but by the time I received the [relevant grant](https://www.cl.cam.ac.uk/~lp15/Grants/Automation/), I found myself working instead with [Christoph Weidenbach](https://www.mpi-inf.mpg.de/departments/automation-of-logic/people/christoph-weidenbach) and his [SPASS prover](https://www.mpi-inf.mpg.de/departments/automation-of-logic/software/spass-workbench).
The Cambridge team included Jia Meng and Claire Quigley, and we already had a [super-preliminary paper](https://rdcu.be/cKaYp) ready for IJCAR 2004.

### The objectives and the obstacles