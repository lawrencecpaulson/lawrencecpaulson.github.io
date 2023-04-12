---
layout: post
title:  "Do Gödel's incompleteness theorems matter?"
usemathjax: true
tags: [general, logic, incompleteness, David Hilbert, Kurt Gödel]
---

Gödel's incompleteness theorems are often regarded as placing strict limits on the power of logic. Don't they immediately imply that any project to formalise mathematics is doomed to fail?

### An overview of Gödel incompleteness

Gödel's *first* incompleteness theorem states that for any "reasonable" formal system $F$ there exists some *undecidable* statement $G_F$, i.e. one that is neither provable nor disprovable in $F$. Moreover, $G_F$ will be true in the standard model for $F$. The *second* incompleteness theorem states that, in particular, no statement implying the consistency of $F$ is provable in $F$. Gödel's theorem was unwelcome when it was announced: it destroyed at a stroke Hilbert's programme for putting mathematics on a sound footing by proving the consistency of strong formal systems (such as Zermelo–Fraenkel set theory) in a weaker system (such as Peano arithmetic). Beyond such technical points as these, most remarks on the consequences of the incompleteness theorems (even by some serious academics) are complete bullshit. [Torkel Franzén](https://philpapers.org/rec/ZACTFG) has written an informative and amusing account of this phenomenon.

Anybody who does anything involving Gödel's theorems quickly gets contacted by cranks who inform them that their work is wrong. There is a website (no link, sorry) enumerating the "elementary logical errors" allegedly made by Gödel and the many logicians after him who studied incompleteness. The emergence of machine formalised proofs, starting with [Shankar's legendary work](https://doi.org/10.1017/CBO9780511569883), simply resulted in additional material to be added to the website, listing alleged errors in those works too. Clearly some people find incompleteness disturbing. The funny thing however: if they don't believe the theorem, one might expect them to try and make contributions to Hilbert's programme. Why don't they publish proofs of the consistency of set theory?

### The implications of incompleteness for mathematics

As a teenager, I learned about many famous unsolved conjectures, such as Fermat's last theorem, the Riemann hypothesis, Goldbach's conjecture and the twin prime conjecture. Of these, all but the first remain unsolved, and occasionally people speculate that these are real-life instances of Gödel incompleteness. Note that such speculations have nothing to do with formalisation.

It's true that in the 19th century mathematicians were sometimes careless about the axiomatic basis for their work. As we have seen in an [earlier post]({% post_url 2021-11-10-Axiom_of_Choice %}), many of the chief opponents of the axiom of choice had themselves relied on it unknowingly. Today we know that certain questions (most notably, the [continuum hypothesis](https://plato.stanford.edu/entries/continuum-hypothesis/)) are indeed independent of the standard axioms for set theory. Therefore any attempt to settle such a proposition must involve the assumption of [new axioms](https://plato.stanford.edu/entries/large-cardinals-determinacy/), such as determinacy. Again, such questions have nothing to do with formalisation.

There was a project to formalise mathematics well before the development of machine logic. Nicolas Bourbaki, a pseudonym for a collective of French mathematicians, wrote a series of texts on a variety of mathematical topics. Their style was absolutely formal with all proofs reduced to logic as much as possible without machine support. These books were highly influential, but the project had its critics too. In [The ignorance of Bourbaki](https://rdcu.be/cJtBL), British logician A. R. D. Mathias wrote that

> They were not ready to face the possibility, strongly suggested by G6del's work, that there are no foundations of mathematics in the sense proposed by Hilbert and embraced by Bourbaki; that there are no ways of grounding mathematics in logic or classes or whatever so that once a basis has thus been given in some primitive ideas, no further thought need be given to them; that though there are indeed foundational issues, they cannot be confined to Chapter One of the Great Book, for they permeate mathematics.

Indeed, as Franzén emphasises, the main consequence of incompleteness for mathematics is its *inexhaustibility*: it is impossible to write down a system of axioms from which all mathematical truths follow. Surely this is a good thing. An example of the opposite is Euclidean geometry, which (as formalised by Tarski) turns out to be decidable and complete. Every question in plane geometry can be settled by an algorithm, and if any mystery remains in this branch of mathematics, it's because that algorithm is super-exponential. We should be glad that the world of mathematics is open and unending.


### The implications of incompleteness for formalisation

A specific aspect of inexhaustibility suggested by the second incompleteness theorem is that, since $F$ cannot prove its own consistency, it can be strengthened by the addition of an axiom implying the consistency of $F$. Such axioms (if not too strong) are easily motivated, since we would not be using $F$ in the first place if we didn't believe it to be consistent. And indeed, the large cardinal axioms typically added to Zermelo–Fraenkel set theory imply the consistency of ZF. The need for such axioms is no obstacle to formalised mathematics, since the axioms themselves can be formalised and used in our proof assistant.

Ironically, Gödel's incompleteness theorem was the first deep, substantial mathematical proof to be formalised by machine. (Results formalised earlier included Cantor's theorem, the Church–Rosser theorem and the fundamental theorem of arithmetic.) Natarajan Shankar [formalised the first incompleteness theorem](https://doi.org/10.1017/CBO9780511569883) for his PhD from the University of Texas at Austin in 1986, using the Boyer/Moore theorem prover ([nqthm](https://www.cs.utexas.edu/users/moore/best-ideas/nqthm/)).

This prover, an ancestor of today's [ACL2](https://www.cs.utexas.edu/users/moore/acl2/), supports a logic whose syntax is a fragment of pure LISP. All functions that are definable in this logic are actually executable. Because most mathematical functions are not executable, such a prover does not appear to be a strong candidate for formalising mathematics, but
Shankar developed a proof fitted to nqthm's strengths.

Shankar defined LISP data structures for the syntax of a first-order logic called Z2. One frequently occurring task in the proof is to demonstrate that various formulas are provable in Z2, and Shankar wrote a function to generate Z2 proofs of any given propositional tautology. The next step was to represent the metatheory of Z2 within itself, and in a tremendous technical feat, he defined a LISP interpreter and showed that it was representable in Z2: and hence, arbitrary computations were representable. This tautology checker and LISP interpreter were not simply coded in the LISP language but were introduced as functions to the nqthm theorem prover, which verified that they terminated. The various properties claimed above were all verified using nqthm. From all that, Shankar could construct Gödel's undecidable sentence.

The incompleteness proofs have been mechanised by a great many authors and this perhaps is the main implication of incompleteness for the machine formalisation of mathematics. But Shankar was first and did it using the hardware and software in the early 1980s, a truly remarkable feat.
