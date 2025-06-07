---
layout: post
title:  Inductive definitions
usemathjax: true 
tags: [inductive definitions]
---
The [previous post]({% post_url 2025-06-04-Definitions %}) 
discussed the simplest sort of definitions,
those that are essentially abbreviations.
An [*inductive definition*](https://lawrencecpaulson.github.io/tag/inductive_definitions) is conceptionally quite different.
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

### A tiny example

The very simplest example of an inductive definition would be the natural numbers themselves, but recursive datatypes are treated as a special case with their own syntax.
Instead, let's look at the Isabelle equivalent of the Prolog program 
to append two lists:

```
append([],X,X).
append([X|Y],Z,[X|W]) :- append(Y,Z,W).  
```
In case you don't know Prolog, this defines a ternary relation, `append`.
The first two arguments are the lists to be joined 
and the third argument is the result.
In Prolog, you do not define functions but rather relations that specify
how the output is derived from the inputs.[^1]
The first clause is for joining an empty list, 
while the second joins a list with head $X$ and tail $Y$ to some other list, $Z$.

[^1]: In fact, Prolog does not force us to distinguish inputs from outputs. But that's another story.

This Prolog code is easily expressed in Isabelle.
Note however that the Isabelle definition does not
reproduce Prolog's depth-first execution model. It is simply mathematics.

XXX

Let's prove that Append, although written as a relation, is actually functional:

XXX

Here I deliberately avoid Isar's concise syntax for an induction proof in order to
show precisely what needs to be proved.
Note that the induction appeals to the specific conduction role for
`Append`, namely `Append.induct`. The two sub-proofs both appeal to
case analysis on the definition, namely `Append.cases`.
This is a common feature of proofs involving inductive definitions,
and invites the use of a technique called *rule inversion*:
where we generate simplification rules to handle special cases
of the inductively defined predicate.
For example, if the first argument is the empty list then the second and third arguments must be equal.
And if the first argument is a list with head $X$,
then the third argument will also have head $X$ and a tale obtained through `Append`.

XXX

Isabelle can easily generate these and similar facts by instantiating and then simplifying the relevant case analysis rule.
If you set up rule inversion properly and integrate it with simplification, the combination can be extremely powerful.

### What an inductive definition means mathematically

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

Aczel paper
