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
Turing's definition of computable real numbers as those having computable decimal expansions doesn't actually work, though a fix is not difficult.

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

And much more. Turing, in this one paper, launched the field of theoretical computer science.

### On the universal machine and the halting problem

We can't be sure what put Turing onto the idea of a universal machine, but once he thought of it, he probably thought that their existence was obvious.
Since the very point of a TM was to simulate a clerk working at a desk, and the operation of a TM was itself clerical—depending on the machine state and tape synmbol, do this or do that according to a given list of transition rules—there was obviously a TM to carry out such a routine task.
Turing's paper is a bit sketchy about how the details of the constrution, but it seems that nobody minded.
(After all, Gödel never did get around to publishing any proof of his second incompleteness theorem; people thought it obvious, and the details turned out to be fiendish.)

Today, we are much more sophisticated. We use a standard bijection between $\mathbb{N}$ and  $\mathbb{N}\times\mathbb{N}$ to pack lists of integers into a single integer.
Then (typically using *register machines* rather than TMs, for simplicity), the full, precise code of a universal machine can fit on a couple of slides, no handwaving.

*FIGURE OF UNIVERSAL MACHINE*

The idea that the halting problem was undecidable was surely also obvious.
Otherwise, many mathematical conjectures would otherwise also be decidable, such as Fermat's last theorem.
It would be trivial to write a program to search for $x$, $y$, $z$, $n>2$ such that
$x^n+y^n = z^n$; such a program would terminate if and only if Fermat's last theorem was false.
But Turing did need to find a proof; the idea to use diagonalisation may have come from Gödel's use of the same technique in 1931 to prove his incompleteness theoerem.

Then it was perhaps that he realised that a positive solution to the decision problem would have to imply a solution to the halting problem as well.
It's a shame we don't know how the ideas involved in his brilliant conception came together.

### Turing and Maurice Wilkes

For a contrary view, here is Maurice Wilkes, [interviewed by David P. Anderson](http://doi.acm.org/10.1145/1562164.1562180):

> **Looking back, what would you say was the significance of Turing's 1936 Entscheidungs-problem paper?**
> 
> I always felt people liked to make a song and dance. Something like the doctrine of the Trinity involved whereas to an engineer you've only got to be told about the stored program idea and you'd say at once "That's absolutely first-rate, that's the way to do it." That was all there was to know.
> 
> There was no distinction in that paper that had any practical significance. He was lucky to get it published at all but I'm very glad he did. I mean [Alonzo] Church had got the same result by other methods.

WTF? Well, Wilkes was 96 at the time of this interview, and himself a [notable computer pioneer](https://www.theguardian.com/technology/2010/nov/30/sir-maurice-wilkes-obituary), the father of the [EDSAC](https://www.tnmoc.org/edsac). In his bizarre answer we see perhaps his jealousy of Turing's iconic status. The two men clearly didn't get along! We also see Wilkes's lifelong disdain for theory: though the idea of coding machines as numbers anticipates the stored-program computer, Turing's work here is purely mathematical, having no engineering implications whatever.
And despite Turing's interest in the engineering of actual computers, his attempts to get involved were repeatedly frustrated.

And what about those remarks about Church?

### Turing and Church at Princeton

Turing was working at the exact moment that many researchers were converging on the idea of "effective calculability". In keeping with my suggestion to read the original papers, let me recommend Church's [An Unsolvable Problem of Elementary Number Theory](https://doi.org/10.2307/2371045).
To be honest, it is a tough read, but it puts you into the context of the time.
Here we find a definition of the $\lambda$-calculus, a definition of recursive function (in the sense of Kleene/Gödel) and some undecidability results for the existence and equivalence of normal forms in the $\lambda$-calculus.
Church and Kleene had already proved the equivalence of the $\lambda$-definable functions and recursive functions; during Turing's time at Princeton, the equivalence between the $\lambda$-definable functions and the Turing-computable was also proved, establishing the Church-Turing thesis: that the effectively computable functions are precisely the functions in those mathematically equivalent classes.

As is often remarked, this claim cannot be proved because "effectively computable" is not a precise concept.
The Turing-computable functions can be regarded as a generous class because they include many functions that cannot be computed in the lifetime of the universe for more than a tiny number of values.
Examples are easily produced with the help of [Ackermann's function]({% post_url 2022-02-09-Ackermann-example %}).
If you define $f(n) = A(n,n)$, you cannot hope to compute even $f(4)$.
And $g(n) = A(4,n)$ is all but impossible to compute despite being primitive recursive.

[History of the Church–Turing thesis](https://en.wikipedia.org/wiki/History_of_the_Church–Turing_thesis)
