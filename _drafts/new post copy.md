---
layout: post
title:  Inductive definitions
usemathjax: true 
tags: [inductive definitions]
---
The previous post discussed the simplest sort of definitions,
those that are essentially abbreviations and can be eliminated.
An *inductive* definition is conceptionally quite different.
The simplest example is to say that a natural number can be 0
or the successor of another natural number, and that **there are
no other natural numbers**.
The latter property is the basis for mathematical induction,
for it implies that if some property holds for 0 and is preserved as we move from a natural number to its successor, then all natural numbers have been accounted for.
Inductive definitions are a natural way to specify program language semantics,
recursive datatypes such as lists and trees, inference systems
and much else. Proofs involving inductive definitions are often easy,
with automation taking care of most of the work.
