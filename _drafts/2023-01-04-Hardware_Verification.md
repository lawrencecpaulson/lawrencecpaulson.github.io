---
layout: post
title:  "Mike Gordon and Hardware Verification"
usemathjax: true 
tags: []
---

In the late 1960s, breakthrough papers by
[Robert W Floyd](https://people.eecs.berkeley.edu/~necula/Papers/FloydMeaning.pdf)
and [Tony Hoare](https://dl.acm.org/doi/10.1145/363235.363259)
seemed to herald the advent of fully-verified software.
Progress soon slowed however. 
It became clear that the moment you went beyond
a simple flowchart program, once you had to deal with 
the horrors of procedure argument-passing, variable scoping
and aliasing, things were not so simple after all.
I vividly recall that while still a student at Stanford,
I spotted a [PhD dissertation](https://searchworks.stanford.edu/view/982736) boldly entitled *Hardware Verification*,
and thinking that the author (Todd Wagner) had to be out of his mind
to tackle something so difficult. Little did I suspect that
I was to acquire a friend and colleague, Mike Gordon,
who would make hardware verification a reality, and even make it look easy.

### Modelling hardware

Sometime early in the 1980s, after I had joined Mike Gordon's
group at Cambridge, he popped into my office and left a preprint
entitled something like "A very simple model of CMOS".
(I've been unable to locate any publication with a title like that).
Shall we work together on this?, he asked. In a fateful decision,
I said I would prefer to follow my own path (which at the time meant
the automation of type theory), and it's intriguing to speculate what 
might have happened if I had said yes. 
We never published a single joint paper.
Gordon's fundamental discovery, which he had methodically worked towards
for a decade, was that hardware circuits could be modelled easily
using higher order logic. And his approach worked exactly the same
whether the components being combined for individual transistors
or were built of thousands of transistors.
