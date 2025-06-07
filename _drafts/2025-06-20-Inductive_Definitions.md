---
layout: post
title:  Inductive definitions
usemathjax: true 
tags: [inductive definitions]
---
The [previous post]({% post_url 2025-06-04-Definitions %}) 
discussed the simplest sort of definitions,
those that are essentially abbreviations.
An *inductive* definition is conceptionally quite different.
The simplest example is to say that a natural number can be 0
or the successor of another natural number, and that **there are
no other natural numbers**.
This last *minimality property* is the basis for mathematical induction,
for it implies that if some property holds for 0 and is preserved as we move from a natural number to its successor, then all natural numbers have been accounted for.
Inductive definitions are a natural way to specify
recursive datatypes such as lists and trees, 
programming language semantics, inference systems
and much else. 
Proof by induction the axiom of infinitycorresponds (respectively) to
structural induction, induction on program executions, induction over derivations.
Proofs involving inductive definitions are often easy,
with automation taking care of most of the work.

### Core ideas

In typical usage, an inductive definition carves out
a distinguished subset of something we have already.
An inference system distinguishes a given set of formulas as being theorems;
the full set of formulas had been defined previously.
The semantics of a programming language is defined on configurations involving
a fragment of program syntax combined with information about the program state,
distinguishing those state transitions allowed by the language;
the syntax and state space had been defined previously.

Even when we define the set of natural numbers in terms of zero and successor,
we need to have defined zero and successor already.
In set theory, zero is the empty set and the successor of $n$ is $n \cup \\{n\\}$;
The axiom of infinity guarantees the existence of a set closed under these,
and the minimality property can be obtained by a least fixed-point construction,
ultimately a set intersection.
The situation is similar in higher-order logic.
However, dependent-typed theories such as used in Lean need the concept of inductive definition to be primitive to the formalism itself.


In traditional mathematical practice, 
set theory is available (if only in the background)
