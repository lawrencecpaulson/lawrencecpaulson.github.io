---
layout: post
title:  "Memories: Edinburgh LCF, Cambridge LCF, HOL88"
usemathjax: true 
tags: [general, Robin Milner, MJC Gordon, LCF, HOL system]
---

Just over 40 years ago, 2 February 1982, I arrived at Heathrow to take up a postdoc under Mike Gordon and Robin Milner to work on Edinburgh LCF.
Mike kindly met me at the airport and drove me to a room that he had organised himself (favours which I have sadly never offered to any of my visitors).
This was the true start of my research career, leaving behind my offbeat PhD project
and ultimately reconnecting with ideas I had picked up from NG de Bruijn: the formalisation of mathematics.
Although I am best known for the development of Isabelle, most of my work in those early years went directly into the HOL system.

### Edinburgh LCF

LCF today is best known for its kernel architecture, described in a 
[previous post]({% post_url 2022-01-05-LCF %});
Talia Ringer has coined the expression *ephemeral proof objects* to describe the operation of its kernel, which never actually creates proof objects but could,
because the section of the code where proofs can be constructed is strictly confined.
Hardly anyone remembers the meaning of the acronym LCF: Logic for Computable Functions.
Edinburgh LCF was created in order to carry out proofs in what was then called fixed point theory and was later subsumed into denotational semantics, where it dropped out of sight.
And it implemented a logic defined by Dana Scott in a paper that he had withdrawn from publication, so you had to get an illicit copy.
(It [finally appeared](https://doi.org/10.1016/0304-3975(93)90095-B) in 1993.)



Here by the way we must distinguish between

1. the *proof document*: the high-level script, written in some tactic language, given to the proof assistant
2. the *proof object*: the low-level formal construction using the rules of the logical calculus

### The LCF architecture

The chief drawback of the de Bruijn criterion was already in 1972 a problem with Robin Milner's proof assistant, Stanford LCF: proof objects easily fill up memory. I am writing on a 32 GB machine while the Stanford AI Lab's PDP-10 could address little more than 1 MB (and was shared by dozens of researchers). However, our proofs have grown as rapidly as our computers and it is still not difficult to run out of memory.

In developing the successor system, Edinburgh LCF, Milner

> had the idea that instead of saving whole proofs, the system should just remember the results of proofs, namely theorems. The steps of a proof would be performed but not recorded, like a mathematics lecturer using a small blackboard who rubs out earlier parts of proofs to make space for later ones. To ensure that theorems could only be created by proof, Milner had the brilliant idea of using an abstract data type whose predeﬁned values were instances of axioms and whose operations were inference rules. Strict typechecking then ensured that the only values that could be created were those that could be obtained from axioms by applying a sequence of inference rules – namely theorems. 

(As told by Michael Gordon in
"From LCF to HOL: a short history",
*[Proof, Language, and Interaction: Essays in Honour of Robin Milner](https://mitpress.mit.edu/books/proof-language-and-interaction)* 169–185.
Quote on p. 170. Available for free [here](https://www.cl.cam.ac.uk/archive/mjcg/papers/HolHistory.pdf).)
