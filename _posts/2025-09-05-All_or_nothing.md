---
layout: post
title:  Program verification is not all-or-nothing
usemathjax: true 
tags: [general, verification]
---
There seems to be a common belief that program verification is 
a task that you toil at for ages until one day you see 
that magic word, VERIFIED.
One seminar speaker made this more explicit, presenting testing
as a process where you gain knowledge over time
(illustrated by a graph gently curving upwards)
and verification as a process where you know nothing until the end,
when you know everything
(illustrated by a graph flatlining until the hoped-for triumph).
Where did people get this dumb idea?

### All-or-nothing things

Some things really are all-or-nothing.
If you attempt to climb Mount Everest 
and give up a short distance from the summit,
you didn't make it: all those brutal weeks of high-altitude climbing,
all that danger and hardship, for nothing.
Despite having performed a truly stupendous feat, 
you may not want to talk about how you got only 99% of the way, 
especially if other people climbed past you and summited.

A similar attitude prevails in mathematics.
Consider [Fermat's Last Theorem](https://www.maths.cam.ac.uk/features/fermats-last-theorem-history-new-mathematics): 
Andrew Wiles announced his proof
in June 1993, but by September a serious error had been found.
As of that moment, he had not proved Fermat's Last Theorem,
and all the mathematical techniques he had developed
to come within 99% of that summit were seemingly as nothing,
such is human psychology.
Luckily, a year later, he found a way around the problem
and was finally credited — along with Richard Taylor — 
with proving this centuries-old conjecture.

The problem in both cases is that the goal is clear and has a name:
Mount Everest; Fermat's Last Theorem.
You have to actually stand on the summit;
you have to prove the theorem without exceptions or doubts.
This also applies to the verification of an algorithm,
which is also a mathematical entity.
The verification of an algorithm may be deep and difficult, but it is fundamentally a problem in mathematics.

### Program verification is different

Program verification is different because 
even the simplest computational task has a messy specification
once we consider real-world constraints.
Suppose our task is to sort an array of records.
Few things are simpler than sorting, yet already we have several correctness properties:

* the output should be a permutation of the input
* the output should be in order
* optionally, the sort should be [stable](https://en.wikipedia.org/wiki/Category:Stable_sorts)

Those are just the abstract mathematical requirements for sorting, but in any real world situation
there will also be performance requirements about the space and time used.
These might be expressed asymptotically, as $O(n\ln n)$, but there could also be real-time constraints.

Now imagine verifying some sorting code. 
The three abstract properties are certainly within the scope of verification,
and if you prove them one at a time, your knowledge is indeed growing as you finish each claim.
Techniques have long existed even for [proving resource bounds](https://doi.org/10.1145/321978.321987) 
for your code.
Real-time constraints are another matter.

### A few real-world case studies

Most verification tasks are open-ended because software systems are vastly more complicated than sorting, 
and people are always coming up with new new features and new properties to prove of those features.
And that is before we even consider any real-world aspects to the specification.
Here are a few examples:

* the [Gordon computer](https://doi.org/10.1007/978-1-4613-2007-4_4) and the [VIPER microprocessor](https://en.wikipedia.org/wiki/VIPER_microprocessor)
* various cryptographic protocols, such as [TLS](https://doi.org/10.1145/322510.322530)
* the seL4 operating system kernel 

Each of these verification projects consisted of milestones that could be proved one at a time,
our knowledge growing at each step.
None can be called 100% complete.
In the case of VIPER, Avra Cohn felt the need to [point out the limitations](https://rdcu.be/eEkVV) 
of her proof, which she felt was being oversold. The design had not been verified down to its lowest level
and the initialisation phase not at all.
In the case of cryptographic protocols, essentially all verification work regards 
the actual cryptographic primitives as abstract and perfect;
real-world TLS has [numerous vulnerabilities](https://www.cloudflare.com/en-gb/learning/ssl/why-use-tls-1.3/).
As for seL4, the [project page](https://sel4.systems/Verification/) helpfully lists the underlying assumptions:
"assembly code, boot code, machine interface, hardware, and DMA".

Things like assembly code and boot code are in principle verifiable; the only question is the cost.
But in none of these examples is there a summit that could be attained, even with unlimited effort.
For VIPER, we could verify the design right down to the bottom,
but the hardware model assumes digital behaviour for what is actually silicon,
saying nothing about problems that could arise due to gate delays, overheating
or other low-level design errors.
For the same reason, the hardware component of seL4 can never be verified 100%.
Any formal model of hardware could be refined 
to a more accurate and detailed model until you get right down to particle physics,
which itself is only a model of reality.
For cryptographic protocols, we simply do not know how to show that specific encryption methods
are unbreakable.

### Let's start climbing Everest

With real-world program verification, we need to be clear about what to prove and what to assume.

* We can prove that our sorting code delivers a sorted permutation of its input
and rely on testing to validate its real-time performance.
* With cryptographic protocols, the main high-level concern is intricate replay attacks, which today's abstract models handle well; implementers still must be careful to choose cryptographic primitives known to be secure.
* A component like seL4 will be [tested anyway](https://docs.sel4.systems/projects/sel4test/) as it is integrated into a larger system. Bugs are not found in the verified sections.

I hope I don't need to point out that testing alone is inadequate.
It's not that long ago that computer crashes were an almost daily occurrence.
Things are better now because of [automated verification tools](https://doi.org/10.1145/1218063.1217943).
Even the mighty Microsoft could not achieve stability through testing alone.

But testing will always have a role to play.
The real world will have to be approximated by some sort of mathematical model.
In the case of verified code, the purpose of testing is to test the model itself.
Increasingly we shall be running verified code on verified hardware designs
while only having to worry about cosmic rays, [low-level attacks](https://meltdownattack.com)
and other phenomena that we cannot model or predict.
We won't be at the summit of Mount Everest, but we'll still be pretty damn high.

