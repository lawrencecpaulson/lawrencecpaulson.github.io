---
layout: post
title:  "Formalising extremal graph theory, I"
usemathjax: true 
tags: [Isabelle, Szemerédi’s regularity lemma]
---

[Chelsea Edmonds](https://www.cst.cam.ac.uk/people/cle47), [Angeliki Koutsoukou-Argyraki](https://www.cst.cam.ac.uk/people/ak2110) and I recently formalised [Roth's theorem on arithmetic progressions](https://www.isa-afp.org/entries/Roth_Arithmetic_Progressions.html).
The project required first formalising [Szemerédi’s regularity lemma](https://www.isa-afp.org/entries/Szemeredi_Regularity.html), which "states that the vertices of every large enough graph can be partitioned into a bounded number of parts so that the edges between different parts behave almost randomly" ([Wikipedia](https://en.wikipedia.org/wiki/Szemerédi_regularity_lemma)).
The mathematics is elementary enough. Our main difficulties were caused by ambiguities, not merely in the proofs but in the statements of the theorems and even the definitions.

### The problem with $\epsilon$-regular pairs

A key definition in extremal graph theory is that of an
*$\epsilon$-regular pair*:

> Let $G$ be a graph and $X$, $Y \subseteq V(G)$. We call $(X, Y)$ an 
> $\epsilon$-regular pair (in $G$) if for all $A \subset X$, $B \subset Y$ with $|A| \geq \epsilon|X|$, $|B| \geq\epsilon|Y|$, one has
> $|\mathrm{d}(A,B) − \mathrm{d}(X,Y) | \leq \epsilon$.

Here $\mathrm{d}(X,Y)$ is a measure of the density of the edges between the vertex sets $X$ and $Y$. The definition is from the [lecture notes](https://yufeizhao.com/gtac/gtac.pdf)
for Yufei Zhao's course "[Graph Theory and Additive Combinatorics](https://yufeizhao.com/gtac/)".
(Fields Medallist Tim Gowers, a leading expert on Szemerédi's regularity lemma, uses the same definition; see §3 of [his notes](https://www.dpmms.cam.ac.uk/~par31/notes/tic.pdf).)
At issue is the use of the strict subset, as in $A \subset X$.

It needs to be strict because we are dealing with partitions of the vertex set, and they will be created (in the *energy boost lemma*) from partitions of the form $\\{A,\, X\setminus A\\}$. By convention, the empty set does not belong to a partition, hence  $A \subset X$ is necessary. That's on page 51 of Zhao's notes. But a mere three pages later we reach the *triangle counting lemma* and at the start of the proof we "obtain a pair of subsets witnessing the irregularity of $(X,Y)$" and one of these so-called subsets is $Y$ itself. Not a strict subset. These issues are not subtle and trying to reconcile them seemed to take as much time as the proofs themselves. 

It didn't help that I was wholly unfamiliar with the subject matter.
I blame my old professor, Caltech's Herbert Ryser. 
He once hinted (ever so discreetly) that graph theory was, well, vulgar.

### Solution attempts

I was pleased to be able to prove that an $\epsilon$-regular pair (as defined above) implies its conclusion for all $A \subseteq X$, $B \subseteq Y$ (non-strict subsets) subject to the clearly necessary but trivial condition that $X$ and $Y$ have at least two elements.
That shouldn't be a problem because we are working with huge graphs, right? Wrong: the vertex set gets partitioned into a huge number (an exponential tower) of parts.
There's no guarantee that each part contains at least two elements. Nor could we complete the triangle counting lemma by finding another proof for the degenerate cases.

The only way to complete the formalisation seemed to require using non-strict subsets in the definition of $\epsilon$-regular pairs. But then the energy boost lemma had to be changed to not always return a two-element partition, with corresponding changes throughout the construction and use of the overall partition in the main lemma (Lemma 3.11 in Zhao). Those changes were not hard; the difficulty lay in realising that they were necessary.

### A matter of attitude

Situations like this illustrate a difference in mentality between mathematics and computer science. In mathematics, you have good intuitions about what you are dealing with, what must be done and what issues are safe to ignore. In computer science, it's not enough to adopt all the appropriate techniques; you have to get every detail right. If the solution is not exactly right, it's wrong. That rocket will explode. 

This difference in the attitude to detail is a real issue in formalisation: if you can't rely on the supplied definitions *exactly* as they appear, you will find yourself hacking your way through a jungle of possible alternatives.
Will the push for formalisation force mathematicians to behave more like computer scientists?

Chelsea, Angeliki and I discussed these matters with mathematicians familiar with the material. One of their responses really sticks in my mind: that in combinatorics, people don't generally bother to distinguish between strict and non-struct subsets, so $A \subset X$ can mean either. Are you kidding me? 
On another occasion, I bumped into [Andrew Thomason](https://www.maths.cam.ac.uk/person/agt2) in my Cambridge College. 
(He lectures on this subject.) I greeted him with, "Exactly what is a regular pair?" 

He burst out laughing.
