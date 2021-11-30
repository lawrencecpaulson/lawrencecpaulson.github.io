---
layout: post
title:  "Do Gödel's incompleteness theorems matter?"
usemathjax: true 
tags: general, logic, Gödel, incompleteness
---

Gödel's incompleteness theorems are often regarded as placing strict limits on the power of logic. Don't they immediately imply that any project to formalise mathematics is doomed to failure?

### An overview of Gödel incompleteness

Put succinctly, the first incompleteness theorem states that for any "reasonable" formal system $F$ there will be some undecidable statements: true but neither provable nor disprovable. The second incompleteness theorem states that, in particular, no statement implying the consistency of $F$ is provable in $F$. Gödel's theorem was unwelcome when it was announced because it destroyed at a stroke Hilbert's programme for putting mathematics on a sound footing by proving strong formal systems (such as ZF set theory) to be consistent using a much weaker system (such as Peano arithmetic).

Anybody who does anything involving Gödel's theorems quickly gets contacted by cranks who inform them that their work is wrong. There is a website (no link, sorry) enumerating the "elementary logical errors" allegedly made by Gödel and the many logicians after him who studied incompleteness. The emergence of machine formalised proofs, starting with [Shankar's legendary work](https://doi.org/10.1017/CBO9780511569883), simply resulted in additional material to be added to the website, listing alleged errors in those works too. Clearly some people find incompleteness disturbing. The funny thing however: if they don't believe the theorem, one might expect them to try and make contributions to Hilbert's programme. Why don't they publish alleged proofs of the consistency of set theory?

### The implications of incompleteness for mathematics

As a teenager, I learned about many famous unsolved conjectures, such as Fermat's last theorem, the Riemann hypothesis, Goldbach's conjecture and the twin prime conjecture. Of these, all but the first remain unsolved, and occasionally people speculate that these are real-life instances of Gödel incompleteness. Note that such speculations have nothing to do with formalisation.

It's true that in the 19th century mathematicians were sometimes careless about the axiomatic basis for their work. As we have seen in an earlier post, many of the chief opponents of the axiom of choice had relied on it themselves unknowingly. Today it is known that certain propositions (most notably, the continuum hypothesis) are indeed independent of the standard axioms for set theory. Therefore any attempt to settle such a proposition must involve the assumption of [new axioms](https://plato.stanford.edu/entries/large-cardinals-determinacy/), such as determinacy. Again, such questions have nothing to do with formalisation. 

There was a project to formalise mathematics well before the development of machine logic. Nicolas Bourbaki, a pseudonym for a collective of French mathematicians, wrote a series of texts on a variety of mathematical topics. Their style was absolutely formal with all proofs reduced to logic as much as possible without machine support. These books were highly influential, but the project had its enemies too. The British logician A. R. D. Mathias wrote, in [The ignorance of Bourbaki](http://dx.doi.org/10.1007/BF03025863), that

> they were not ready to face the possibility, strongly suggested by G6del's work, that there are no foundations of mathematics in the sense proposed by Hilbert and embraced by Bourbaki; that there are no ways of grounding mathematics in logic or classes or whatever so that once a basis has thus been given in some primitive ideas, no further thought need be given to them; that though there are indeed foundational issues, they cannot be confined to Chapter One of the Great Book, for they permeate mathematics. 




### The implications of incompleteness for formalisation

Those axioms, should we adopt them, can be formalised and used in our proof assistant.
