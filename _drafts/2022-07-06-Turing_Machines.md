---
layout: post
title:  "On Turing machines"
usemathjax: true 
tags: general, logic, Turing
---

Every now and then, somebody claims that Turing "invented the computer": because he invented Turing machines. However, Turing machines are not actual machines. They aren't even models of machines. It turns out (we have Turing's own word for it), a TM is a model of a man working at a desk. So why *did* Turing invent TMs, and where did this lead?

### Turing's article "On Computable Numbers"

It's often best to put your textbooks aside and turn to the papers themselves.
These days there is no need to fill out a borrowing card for a journal volume dated 1936 and wait an hour or so for the librarian to fetch it from storage.
Just ask Mr Google while relaxing at home, a glass of single malt at your side.
Turing's paper can be found [online](https://doi.org/10.1112/plms/s2-42.1.230)
(also [here](https://www.cs.virginia.edu/~robins/Turing_Paper_1936.pdf)).
It is a wonderful read, even with its mistakes: as Joel David Hamkins [explains](http://jdh.hamkins.org/alan-turing-on-computable-numbers/), 
Turing's definition of computable real numbers as those having computable decimal expansions doesn't actually work.

Turing states his intentions right in the title: "On Computable Numbers, with an Application to the [Decision Problem]". (The *[Entscheidungsproblem](https://en.wikipedia.org/wiki/Entscheidungsproblem)* asks whether there exists an effective technique for determining whether a given formula of first-order logic is valid, i.e., true in all interpretations.)
Turing expands on his thinking as follows:

> We may compare a man in the process of computing a real number to a machine which is only capable of a finite number of conditions $q_1$, $q_2$, ... $q_R$ ... . The machine is supplied with a " tape" (the analogue of paper) running through it, and divided into sections (called "squares") each capable of bearing a " symbol". ... Some of the symbols written down
> will form the sequence of figures which is the decimal of the real number which is being computed. The others are just rough notes to "assist the memory". It will only be these rough notes which will be liable to erasure.
> It is my contention that these operations include all those which are used in the computation of a number.

Turing proceeds with definitions and proofs, typical of a mathematics article and not at all typical of an engineering article, where one would expect to see a discussion of how to realise some mechanism that had been described.
Turing's main concern, as we see both from his title and from the passage quoted above, is the computation of a *single* real number to an *unlimited* number of decimal places.

The paper makes many other fundamental contributions: 

* the *universal machine*, and with it the idea of *coding* machines in the form of numbers
* the *halting problem* for machines so coded, and its *undecidability* by diagonalisation

And much more. Turing, in this one paper, created a new field of mathematics (recursion theory) as well as launching the field of theoretical computer science.

NO CONSTRUCTION OF UNIVERSAL TM

### Turing and Maurice Wilkes

For a contrary view, here is Maurice Wilkes, [interviewed by David P. Anderson](http://doi.acm.org/10.1145/1562164.1562180):

> **Looking back, what would you say was the significance of Turing's 1936 Entscheidungs-problem paper?**
> 
> I always felt people liked to make a song and dance. Something like the doctrine of the Trinity involved whereas to an engineer you've only got to be told about the stored program idea and you'd say at once "That's absolutely first-rate, that's the way to do it." That was all there was to know.
> 
> There was no distinction in that paper that had any practical significance. He was lucky to get it published at all but I'm very glad he did. I mean [Alonzo] Church had got the same result by other methods.

Um, WTF?? Well, Wilkes was 96 at the time of this interview, and himself a [notable computer pioneer](https://www.theguardian.com/technology/2010/nov/30/sir-maurice-wilkes-obituary), the father of the [EDSAC](https://www.tnmoc.org/edsac). In his bizarre answer we see perhaps his jealousy of Turing's iconic status. The two men clearly didn't get along. We also see Wilkes's lifelong disdain for theory: though the idea of coding machines as numbers anticipates the stored-program computer, Turing's work here is purely mathematical, having no engineering implications whatever.

And what about those remarks about Church?

### Turing and Church at Princeton

[An Unsolvable Problem of Elementary Number Theory](https://doi.org/10.2307/2371045)

