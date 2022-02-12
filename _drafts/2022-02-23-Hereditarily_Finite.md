---
layout: post
title:  "The hereditarily finite sets"
usemathjax: true 
tags: logic, set theory
---

A set is hereditarily finite if it is finite and all of its elements are hereditarily finite. They can be characterised by the axioms of set theory but negating the axiom of infinity. They are countably many and they are a natural domain for talking about computation. They also allow a clean treatment of Gödel's incompleteness theorems.

### Introduction to the HF sets

The inductive conception of HF sets justifies the recursive definition $f(x)=\sum\, \lbrace 2^{f(y)}\mid y\in x\rbrace $, yielding a bijection $f:\text{HF}\to \mathbb{N}$  between the HF sets and the natural numbers.
Defining $x<y$ if and only if $f(x)<f(y)$ yields an linear ordering on HF.
It's easy to see that $<$ extends both the membership and the subset relations.

What about the inverse function $g$, mapping natural numbers to sets? 
Clearly $g(0) = \emptyset$. To understand $g(n)$ for $n>0$, imagine $n$ written in binary notation: then from the position of each 1 from right to left we recursively obtain an HF set from the number of 0s to its right. We can work out some values:

$$ \begin{align*}
g(0) &= \phi \\
g(1) &= \lbrace g(0)\rbrace  = \lbrace \phi\rbrace  \\
g(2) &= \lbrace g(1)\rbrace  = \lbrace \lbrace \phi\rbrace \rbrace  \\
g(3) &= \lbrace g(1), g(0)\rbrace  = \lbrace \lbrace \phi\rbrace, \phi\rbrace  \\
g(4) &= \lbrace g(2)\rbrace  = \lbrace \lbrace \lbrace \phi\rbrace \rbrace \rbrace  \\
g(5) &= \lbrace g(2), g(0)\rbrace  = \lbrace \lbrace \lbrace \phi\rbrace \rbrace , \phi\rbrace  \\
g(6) &= \lbrace g(2), g(1)\rbrace  = \lbrace \lbrace \lbrace \phi\rbrace \rbrace , \lbrace \phi\rbrace \rbrace  \\
g(7) &= \lbrace g(2), g(1), g(0)\rbrace = \lbrace \lbrace \lbrace \phi\rbrace \rbrace , \lbrace \phi\rbrace , \phi\rbrace \\
\vdots & \\
g(11) &= \lbrace g(3), g(1), g(0)\rbrace  = \lbrace \lbrace \lbrace \phi\rbrace, \phi\rbrace, \lbrace \phi\rbrace , \phi\rbrace 
\end{align*} $$

Note that 11 is 1011 in binary and that $g(0)$, $g(1)$, $g(3)$ and $g(11)$ are the first four von Neumann ordinals. It seems that if $n$ codes an ordinal then $2^n+n$ codes the next ordinal, so the ordinal 4 is $g(2059)$.

The way $g$ operates on binary strings reminds me of the [Pascal](https://dl.acm.org/doi/10.1145/234286.1057812) 
programming language's *set types*, which provide clean access to the hardware bit level. A Pascal set is a bit string: bitwise “and” performs intersection, bitwise “or” performs union, etc. Pascal was first implemented on a CDC computer with 60-bit words, allowing sets over any type having up to 60 values. 

### Uses for the HF sets

What’s cool about the hereditarily finite sets? They are rich enough to support many familiar constructions: the Cartesian product of two sets, the disjoint sum, function spaces (between finite sets of course), power sets and even quotient constructions. The latter may seem doubtful, since equivalence classes are often infinite, but since the HF sets have a (constructive!) wellordering, canonical representatives can be chosen. The upshot is that the HF sets are perfect for representing the results of computations: natural numbers, integers, rationals and finite data structures over them, but not, for example, arbitrary real numbers.

There is a philosophical question here: the natural numbers are almost invariably used in models of computation, and other data structures can be coded in terms of them. What then is the point of using HF, which is just a less familiar encoding medium? One advantage of the natural numbers is the simplicity having the operations 0, +1 and -1 enough to express computations; the advantage of HF sets, for those who are already comfortable with set theory, is that they are the exact same sets, just fewer of them. Consider ordered pairs: using the natural numbers, the pair $(x,y)$ might be represented by $2^x3^y$, which is no worse than the set theorist’s $\lbrace \lbrace x\rbrace , \lbrace x,y\rbrace \rbrace $. However, the set theorist can happily go on to define $A\times B$ as $\lbrace (x,y) \mid x\in A \land y\in B\rbrace $, and while something similar could be done with the natural number representation, it seems that nobody does, perhaps because they simply don’t have sets on their mind.

### HF sets and Gödel's incompleteness theorems

Świerczkowski [has used HF](https://doi.org/10.4064/DM422-0-1) as the basis for proving Gödel's incompleteness theorems, and I [have formalised his work](https://www.cl.cam.ac.uk/~lp15/papers/Formath/Goedel-logic.pdf) using Isabelle/HOL.
The big advantage of HF here 


### An example: finite automata

The HF sets are a simple route out of the strict typing paradigm that bugs some people so much. Some years ago, Christian Urban published an elegant treatment regular languages avoiding the usual approach in terms of finite automata because of the difficulty of representing state spaces using simple types. But if we use HF sets to denote the state spaces of automata, then we have no problem forming Cartesian products of state spaces when forming the product of two automata, forming the powerset of the state space when transforming a nondeterministic finite automata into a deterministic one, and so forth.

Paper: https://arxiv.org/pdf/1505.01662.pdf

AFP: https://www.isa-afp.org/entries/HereditarilyFinite.html




