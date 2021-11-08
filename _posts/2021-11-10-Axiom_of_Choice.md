---
layout: post
title:  "The axiom of choice and descriptions"
usemathjax: true 
tags: logic, set theory, axiom of choice
---

Few topics in mathematics are more contentious––or misunderstood––than the axiom of choice. We adopt it in the form of Hilbert's ε-operator.

### Introduction to AC

Let $\lbrace B_x\rbrace_{x\in A}$ 
be a family of sets indexed by some set $A$ and consider the set of all functions $f$ such that $f(x)\in B_x$ for all $x\in A$. This set can be written $\prod_{x\in A}\,B_x$, the product of a family of sets. It is essentially the same concept as the product of a family of types, typically written $(\prod x:A)\,B(x)$ in type theory.

If some $B_x$ is empty then $f(x)\in B_x$ cannot hold and the product must be empty. Conversely, if $B_x$ is nonempty for all $x\in A$, then the product *should* be nonempty. This natural assumption is actually the [*axiom of choice*](https://plato.stanford.edu/entries/axiom-choice/) (AC). It presumes the existence of a function $f$ that chooses an element of $B_x$ for all $x\in A$ even if there is no explicit construction of $f$.
We now know that AC is consistent with the other axioms of set theory (proved by Gödel) but cannot be proved from them either (proved by Cohen).

In the 19th century, mathematics was not done on an axiomatic basis and many eminent mathematicians assumed AC without realising it. 
Typically they assumed some "obvious" fact such as that a countable union of countable sets is countable, a claim that is actually equivalent to the axiom of choice.
So when Zermelo promulgated the axiom of choice at the turn of the 20th century, he aroused strong opposition. 

> It is a historic irony that many of the mathematicians who later opposed the Axiom of Choice had used it implicitly in their own researches. This occurred chiefly to those who were pursuing Cantorian set theory or applying it in real analysis. At the turn of the century such analysts included Rene Baire, Emile Borel, and Henri Lebesgue in France, as well as W. H. Young in Germany. ... At times these various mathematicians used [AC]
>  in the guise of infinitely many arbitrary choices, and at times it appeared indirectly via the Countable Union Theorem and similar results. Certainly the indirect uses did not indicate any conscious adoption of non-constructive premises. Yet when infinitely many arbitrary choices occurred in the work of a mathematician such as Borel, they revealed a certain ambivalence toward the methods permissible in mathematics.

> Gregory H. Moore, *Zermelo's Axiom of Choice* (Springer, 1982), 64--65.

In the absence of AC, there exists a model of ZF in which *the set of all real numbers, though uncountable, is a countable union of countable sets*.
In such a model, little survives of the work of Baire and Lebesgue.
The axiom of choice is also necessary for the development of modern alegebra, analysis and particularly set theory. Numerous claims involving infinite cardinalities depend on AC.

### Hilbert's Epsilon-operator

A particularly strong version of the axiom of choice asserts the existence of a global choice function, which we could write $\epsilon(A)$, satisfying $\epsilon(A)\in A$ for every nonempty set $A$. This leads us to [Hilbert's ε-operator](https://plato.stanford.edu/entries/epsilon-calculus/), which is syntactic and gives a formalisation of first-order logic without quantifiers. 
Let now $A$ denote a first-order formula involving the variable $x$
and introduce the syntax $\epsilon x. A$ satisfying the axiom $A(x)\to A(\epsilon x. A)$. Intuitively, provided the property $A$ holds for some $x$, then $A$ also holds for $\epsilon x. A$. This operator is provided by Isabelle/HOL and most versions of the [HOL system](https://hol-theorem-prover.org).

 Hilbert had particular reasons for introducing this symbol, but for machine logic it has a much more fundamental purpose: it gives us a way to refer to something that is defined by a property rather than by name. Such an operator is called a *description* and is analogous to such natural language examples as "somebody older than 18". People who reject the axiom of choice can still use *unique descriptions*. These have the form of $\iota x. A$ and denote the *unique* value satisfying $A$ provided such a thing exists (e.g. "the oldest person in the room"). With either form of description, if the necessary condition is not satisfied, then its value is unspecified. What *that* means is a topic for another post.
 
Descriptions are sometimes necessary, but they can be awkward to reason about due to the duplication of the formula $A$. As Adrian Mathias has [pointed out](https://www.dpmms.cam.ac.uk/~ardm/inefff.pdf), overly enthusiastic use of Hilbert's ε can have remarkable consequences, such as a definition of the number 1 that explodes to 4,523,659,424,929 symbols.
