---
layout: post
title:  "Formalising mathematics in set theory"
usemathjax: true 
tags: set theory, resolution, Mizar, Isabelle/ZF
---

[Last week's post]({% post_url 2022-01-26-Set_theory %}) mentioned the mechanisation of some major results of ZF set theory in proof assistants. In fact, the use of automated theorem provers with various forms of set theory goes back a long way. Two stronger set theories have attracted interest: above all, von Neumann–Bernays–Gödel (NBG) and Tarski–Grothendieck (TG). All of this work was motivated by the goal of mechanising mathematics.

### Early ambition on mechanising mathematics

The idea that all mathematical knowledge could be reduced to calculation has been around for centuries. For example it is associated with the 17th-century mathematician/philosopher [Leibniz](https://plato.stanford.edu/entries/leibniz/).

In the 20th century, some researchers expressed strikingly bold visions.
Here is Hao Wang in 1958: 

> The original aim of the writer was to take mathematical textbooks such as Landau on the number system, Hardy-Wright on number theory, Hardy on the calculus, Veblen-Young on projective geometry, the volumes by Bourbaki, as outlines and to make the machine formalize all the proofs (fill in the gaps).
(In [Toward Mechanical Mathematics](https://doi.org/10.1147/rd.41.0002), page 15)

What he actually accomplished was impressive enough. He implemented a proof procedure for first-order logic with equality, which he claimed to be complete. He demonstrated its power by proving nearly 400 of the purely logical theorems
of [*Principia Mathematica*](https://plato.stanford.edu/entries/principia-mathematica/). While thinking about that accomplishment, take a moment to examine the specifications of the computer used, an [IBM 704](https://www.ibm.com/ibm/history/exhibits/mainframe/mainframe_PP704.html).
It's notable that the first book mentioned by Wang was Landau’s [Foundations of Analysis](https://homepages.math.uic.edu/~kauffman/Landau.pdf). 
As [already described]({% post_url 2021-11-03-AUTOMATH %}), that book would soon be formalised, using
[AUTOMATH](https://www.win.tue.nl/automath/).
I formalised an example from "Hardy on the calculus" [not long ago]({% post_url 2021-12-22-MVT-example %}).

Here is Art Quaife in 1989:

> $1000 personal computers with the computational power of the human brain should be available by year 2030. The time will come when such crushers as Riemann's hypothesis and
Goldbach's conjecture will be fair game for automated reasoning programs. For those of us who arrange to stick around, endless fun awaits us in the automated development and eventual enrichment of the corpus of mathematics.
[Automated Deduction in von Neumann–Bernays–Gödel Set Theory](https://doi.org/10.1007/BF00263451), page 119--120

2030 isn't far off, so this was a little ambitious (and we didn't get [HAL 9000](https://youtu.be/Wy4EfdnMZ5g) in 2001 either.)
However, in the expression "arrange to stick around", Quaife is referring to life extension technologies (a.k.a. putting the body in the freezer), so possibly we can add a couple of centuries to the deadline.
With a complete proof procedure, a proof will definitely be found if one exists, but the time and space required could make it utterly infeasible, and Gödel incompleteness could also spoil the party.

Quaife did achieve significant results however. He produced the first usable formalisation of axiomatic set theory in an automatic theorem prover.
He used [Otter](https://www.cs.unm.edu/~mccune/otter/), the leading resolution theorem prover of that era.
Such provers are fully automatic, but in practice, a human being needs to develop the material by suggesting lemmas to be proved in the correct order,
and Quaife correctly described his proofs as semiautomatic.
He proved Cantor's theorem and a challenge of that era: that the composition of homomorphisms is a homomorphism. 

The most ambitious proposal to emerge from this era was the [*QED manifesto*](https://www.cs.ru.nl/~freek/qed/qed.html) (anonymous, but was said to be driven by [Robert Boyer](https://www.cs.utexas.edu/people/faculty-researchers/robert-boyer)).

> QED is the very tentative title of a project to build a computer system that effectively represents all important mathematical knowledge and techniques. The QED system will conform to the highest standards of mathematical rigor, including the use of strict formality in the internal representation of knowledge and the use of mechanical methods to check proofs of the correctness of all entries in the system.

### NGB set theory

Quaife used von Neumann–Bernays–Gödel (NBG) set theory.

> It is a surprising fact that ZF, which is widely studied by logicians, cannot be finitely axiomatized. (Cf. [8], p. 320.) Since it cannot be finitely axiomatized, it cannot be input to a resolution-based theorem prover. Fortunately, the vNBG set theory has a finite axiomatization, and is in fact strictly stronger than ZF. How does vNBG avoid the necessity of an infinite number of axioms, which seems inherent in any handling of a schematic notion such as (.x : p(x)), where p ranges over all first-order formulas? Metatheorems describing in detail how this is done occupy the first few pages of Chapter II of [3]. Briefly, here is the trick. We take as primitive a few theoretic operations such as intersection, complementation, extracting the domain of a rela- tion, and taking the converse of a relation. We also take as given the operation of taking the non-ordered pair of two ‘little’ sets, and posit that the pair is itself little. Finally, we take as given {(s, .v) :.YEy}. the set of all ordered pairs of little sets .Yand
J’ such that .Kis in y. We then observe that in any given instance of {.u:p(.u)} the formula p must be built up out of ‘3’, ’ A ‘, ‘l’, and ‘E’. By a simple structural induction on the form ofp, we see how to eliminate the set-builder notation 
                 

Robert Boyer et al.: [Set theory in first-order logic: Clauses for Gödel's axioms](https://doi.org/10.1007/BF02328452)



> It is crucial that a "root logic" be a logic that is agreeable to all practicing mathematicians. The logic will, by necessity, be sufficiently strong to check any explicit computation, but the logic surely must not prejudge any historically debated questions such as the law of the excluded middle or the existence of uncountable sets.

