---
layout: post
title:  "Formalising mathematics in set theory"
usemathjax: true 
tags: set theory, resolution, Mizar, Isabelle/ZF
---

[Last week's post]({% post_url 2022-01-26-Set_theory %}) mentioned the mechanisation of some major results of ZF set theory in proof assistants. In fact, the use of automated theorem provers with various forms of set theory goes back a long way. Two stronger set theories have attracted interest: above all, von Neumann–Bernays–Gödel (NBG) and Tarski–Grothendieck (TG). All of this work was motivated by the goal of mechanising mathematics.

### Early ambition on mechanising mathematics

The idea that all mathematical knowledge could be reduced to calculation has been around for centuries. For example it is associated with the 17th-century mathematician/philosopher [Leibniz](https://plato.stanford.edu/entries/leibniz/), 
who looked forward to a future where

> when there are disputes among persons, we can simply say: Let us calculate, without further ado, and see who is right.

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

Quaife used von Neumann–Bernays–Gödel (NBG) set theory, as recommended in 1986 by Boyer et al., because ZF set theory cannot be finitely axiomatized. 

> [ZF] cannot be input to a resolution-based theorem prover. Fortunately, the vNBG set theory has a finite axiomatization, and is in fact strictly stronger than ZF. 
([Set theory in first-order logic: Clauses for Gödel's axioms](https://doi.org/10.1007/BF02328452), page 288.)

From a syntactic point of view, the problem is that ZF involves terms that contain first-order formulas. 
NBG uses variables ranging over proper classes as surrogates for formulas, bringing them within the mathematical domain of discourse. 
(In ZF, classes are nothing but a convention for referring to collections––of all ordinals, say––that are too large to be sets.)
NBG provides a selection of operations on these classes,
including intersection, complementation and domain of a relation.
From these it is possible to recover the effect of ZF's
separation and replacement axioms.

Unfortunately, rendering first-order formulas into this combinator language is difficult. Belinfante wrote code to automate the translation
and performed a series of experiments, [culminating](https://doi.org/10.1007/978-3-540-45085-6_18)
in the the Schröder-Bernstein theorem.

Note that ZF set theory goes nicely into Isabelle, where the syntactic basis is higher-order and terms that contain formulas are not a problem.

### TG set theory

In order to discuss Tarski–Grothendieck set theory, we need the notion of a universe. The terminology is unfortunate, because the universe refers to everything there is, but here we are using it to refer to very large collections that are not everything there is, and nobody thought of calling them galaxies. 
So, staying informal, a ZF universe is essentially a model of ZF set theory. It's natural to believe that such models exist, because otherwise (by the completeness theorem) ZF must be inconsistent, so why are you using it? Such a model could be a countable set, by the Löwenheim–Skolem theorem: see [Skolem’s Paradox](https://plato.stanford.edu/entries/paradox-skolem/).
However, here we need large models, typically given by large cardinals.




1-inaccessible cardinal (relatively weak for large cardinal axioms)

Tarski's axiom, which states that for each set there is a Grothendieck universe it belongs to (see below). 
	
Tarski's axiom (adapted from Tarski 1939[5]). For every set x, there exists a set y whose members include:
-
x itself;
- every subset of every member of
y;
- the power set of every member of
y;
- every subset of
y of cardinality less than that of y.

Mizar