---
layout: post
title:  "Formalising Gödel's incompleteness theorems, I"
usemathjax: true 
tags: Isabelle/HOL, Gödel, incompleteness, nominal Isabelle
---

[Gödel's incompleteness theorems](https://plato.stanford.edu/entries/goedel-incompleteness/) state limits on formal systems. 
(1) A consistent system strong enough to express the basic properties of integer addition and multiplication must be *incomplete*: there exists a formula that is neither provable nor refutable within the system. (2) Moreover, no such formal system can prove any statement implying its own consistency.
The first theorem is proved by using integer arithmetic to encode logical formulas, operations on them such as substitution, and inference according to the rules of the formal system. A fixedpoint construction to create an explicit formula expressing its own unprovability.
The technical complications of the first theorem are formidable but were overcome already by [Shankar](https://doi.org/10.1017/CBO9780511569883) in the 1980s and again by John Harrison and [Russell O’Connor](https://rdcu.be/cNaig).
This post will describe [my own formalisation](https://www.cl.cam.ac.uk/~lp15/papers/Formath/Goedel-logic.pdf) of the first theorem, using Isabelle/HOL.

### A formal logic and its Isabelle/HOL formalisation

I have [previously commented]({% post_url 2021-12-15-Incompleteness %}) on the relevance of Gödel incompleteness to formalisation.
But I can't resist remarking that a lot of today's work on type theory looks like Hilbert's Programme Reloaded: people are striving to create a formal system in which all mathematics can be done and to prove its consistency syntactically. Gödel's theorem tells us that any such theory will be incomplete, but that's not even the main problem with an outlook that seems to be absolutely mechanical.
We formalise mathematics in the hope that it can be useful to mathematicians, but please let's forego fantasies of capturing the whole of mathematical thought in a formal system.


