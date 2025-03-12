---
layout: post
title:  "Revisiting an early critique of formal verification"
usemathjax: true 
tags: [verification,philosophy,formalised_mathematics,Principia_Mathematica]
---
In 1979, a paper appeared that challenged the emerging field of program verification:
"[Social Processes and Proofs of Theorems and Programs](https://doi.org/10.1145/359104.359106)", 
by Richard De Millo, Richard Lipton and Alan Perlis.
They pointed out that proofs in mathematics bore no resemblance
to the formalisms being developed to verify computer programs.
A mathematical proof, they argued, was an argument intended to persuade other mathematicians.
A proof's acceptance by the mathematical community took place through 
a social, consensual process and not through some sort of mechanical checking.
Proofs of programs are too long, tedious and shallow 
to be checked through such a social process.
In many ways they were right, but their main argument was completely wrong.

### Background

At the end of the 1960s, 
program verification started to emerge, with the publication of Robert W Floyd's 
"Assigning Meanings to Programs" 
and Tony Hoare's "[An axiomatic basis for computer programming](https://doi.org/10.1145/363235.363259)".
In "[Proof of a Program: FIND](https://doi.org/10.1145/362452.362489)", Hoare worked through the correctness conditions by hand.
Automated program verification tools slowly started to appear,
such as [Gypsy](https://doi.org/10.1145/390019.808306) and the Stanford Pascal Verifier
(which I worked with a bit myself).
Such tools were not very capable and some lacked a sound logical basis.

A lot of code was still being written in assembly language,
but new programming languages were emerging regularly:
Pascal and its derivatives, Modula and Ada, 
alongside systems programming languages such as BLISS, BCPL and C.
The UNIX operating system, coded in C, was announced in 1971,
and the Xerox Alto workstation, coded in BCPL, appeared a couple of years later.
Both of these would become hugely influential to the future of computer science.
I'm trying to understand why anyone working in this era would write a paper
asserting (in the abstract)
"It is felt that ease of formal verification should not dominate program language design."

### The core argument

The authors' argument rests on two pillars:

* Formal logic cannot feasibly be used to prove any non-trivial result.
* Mathematicians' traditional method of validating a proof through discussion is the right way to establish the proof of any proposition.

To establish the first claim, they note that Whitehead and Russell's 
*Principia Mathematica* was a "deathblow" for formalisation, because it 
"failed, in three enormous, taxing volumes, to get beyond the elementary facts of arithmetic."
(Curiously, they omitted to note that 362 pages needed to prove 1+1=2.)
They also mention a logician's claim that the formalisation of a certain result 
by Ramanujan would take at least 2000 pages and would be of inconceivable length 
if derived from first principles. Isabelle's Archive of Formal Proofs actually contains
[one of Ramanujan's theorems](https://www.isa-afp.org/entries/Rogers_Ramanujan.html), 
proved in 20 pages.


![Footnotes from Jech](/images/Jech-118-footnotes.png)

### Hindsight?

On the reduction in size of formal logical proofs: consider computers reduced from the size of a room to the size of a desk to the size of a shoebox by 1979; consider that a computer program consisting of many pages of assembly language could also be expressed in a couple of lines of akw.


"So far, there has been little philosophical discussion of making software reliable rather than verifiable."