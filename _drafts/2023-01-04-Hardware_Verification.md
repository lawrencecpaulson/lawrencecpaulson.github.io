---
layout: post
title:  "Mike Gordon and hardware verification"
usemathjax: true 
tags: [MJC Gordon, verification, HOL system]
---

In the late 1960s, breakthrough papers by
[Robert W Floyd](https://people.eecs.berkeley.edu/~necula/Papers/FloydMeaning.pdf)
and [Tony Hoare](https://dl.acm.org/doi/10.1145/363235.363259)
seemed to herald the advent of fully-verified software.
Progress soon slowed however. 
It became clear that once you went beyond
a simple flowchart program and had to deal with 
the horrors of procedures, variable scopes
and aliasing, things were not so simple after all.
I vividly recall, while still a student at Stanford,
spotting a [PhD dissertation](https://searchworks.stanford.edu/view/982736) boldly entitled *Hardware Verification*,
and thinking that the author (Todd Wagner) had to be out of his mind
to tackle something surely so difficult. Little did I suspect that
I was soon to acquire a friend and colleague, 
[Mike Gordon](https://www.cl.cam.ac.uk/archive/mjcg/),
who would make hardware verification a reality, and even make it look easy.

### Modelling hardware

Sometime early in the 1980s, after I had joined Mike Gordon's
group at Cambridge, he popped into my office and left a preprint
entitled something like "A very simple model of CMOS".
(Though I've been unable to locate any publication with a similar title.)
Shall we work together on this?, he asked. In a fateful decision,
I said I would prefer to follow my own path (which at the time meant
the automation of type theory), and it's intriguing to speculate what 
might have happened if I had said yes. 
We never published a single joint paper.
Gordon's fundamental discovery, which he had worked towards methodically
for a decade, was that hardware circuits could be modelled easily
using higher order logic. And his approach worked exactly the same
whether the components being combined for individual transistors
or were built of thousands of transistors.

His idea was simply this: 

* every device modelled by a **relation** on its ports
* no distinction between inputs and outputs
* port values could be **anything**: bits, words, vectors, functions (for time-indexed signals)
* relation describing which combinations of port values are possible


<img src="/images/hw-device.png" alt="hardware device" width="200"/>

<img src="/images/transistor.png" alt="n-channel transistor" width="200"/>

In a [previous post]({% post_url 2022-07-27-Truth_Models %})
I stated some general principles about modelling.

### Postscript

I have written a [scientific biography](http://doi.org/10.1098/rsbm.2018.0019) 
of Mike Gordon (also [here](https://arxiv.org/abs/1806.04002))
covering his discovery of hardware models, among much else. 
He never mentioned the thesis of
Todd Wagner and doesn't appear to have cited it either.
Mike's simple hardware models have held up well, while Glynn Winskel's
[more detailed models](https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-105.html) 
(incorporating signal strength) seem not to have caught on.

