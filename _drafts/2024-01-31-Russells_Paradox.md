---
layout: post
title:  "Russell's Paradox: Myth and Fact"
usemathjax: true 
tags: [logic, Bertrand Russell, Principia Mathematica, philosophy]
---

The story of Russell's paradox is well known. 
[Gottlob Frege](https://plato.stanford.edu/entries/frege/) had written a treatise 
on the foundations of arithmetic, a formal logic and a
development of elementary mathematics from first principles. 
Bertrand Russell, upon reading it, wrote to Frege mostly to praise the work, but asking a critical question. Frege replied to express his devastation at seeing his life's work ruined. 
Some later commentators went further, saying that Russell's paradox refuted the entire [logicist approach](https://plato.stanford.edu/entries/logicism/#) 
to the foundations of mathematics (the idea that mathematics can be reduced to logic). 
Much is wrong with this story. 
The impact of Russell's paradox is less than many believe, and greater. 

### What is Russell's paradox?

The paradox can be expressed quite simply in English.
Let $R$ denote the set of all sets that are not members of themselves;
Then, $R$ is a member of itself if and only if it is not a member of itself. 
(In symbols, define $R$ as $\\{x \mid x\not\in x\\}$; then $R\in R$ iff $R\not\in R$.)
Both possibilities lead to a contradiction. 

Faced with such a situation, we need to scrutinise every assumption to identify where the problem lies. The key assumption is clearly the notion of a *set*.
It is an abstraction of various collective nouns in common use, 
such as nation, clan, family. In each of these we deal with units composed of smaller units,
And we even have a hierarchy: a nation can be a collection of clans, 
each of which is a collection of families. 
For further examples we have herds, also armies (with their hierarchy of divisions, regiments, etc).
None of these can be members of themselves, so maybe **that** idea is suspect. 
But if we accept the *universal set* $V$, to which everything belongs, 
then surely $V\in V$: it belongs to itself. 
So maybe the universal set is the root of the problem,
but this insight does not show us the way out. 
Two very different solutions emerged: 

* *Axiomatic set theory*. Unrestricted set comprehension is replaced by the *separation axiom*. 
You cannot just form the set $\\{x\mid\phi(x)\\}$ from an arbitrary property $\phi(x)$; 
you can only form **subsets** of some existing set $A$ as $\\{x\in A\mid\phi(x)\\}$. 
Axioms are provided allowing the construction of sets according to certain specific principles.
Now $R$ cannot be constructed, and there is no universal set. 
For technical purposes, a further axiom is usually assumed: to forbid 
nonterminating membership chains,
such as $x\in y\in x$ and  $\cdots \in x_3\in x_2\in x_1$.
Thus, no set can be a member of itself. 
This route is due to [Zermelo](https://plato.stanford.edu/entries/zermelo-set-theory/) 
and Fraenkel.

* *Type theory*. 
A type hierarchy is introduced to classify all values, and $x\in y$
can only be written if the type of $y$ is higher than that of $x$.
It is thus forbidden to write $x\in x$. 
With types there is no universal set either, but there are universal sets for each type. 
This route is due to Whitehead and Russell, who further complicated their type theory 
to enforce the "[vicious circle principle](https://plato.stanford.edu/entries/russell-paradox/#ERP)", 
which they saw as the root of all paradoxes. 
Their [ramified type theory](https://plato.stanford.edu/entries/type-theory/#RamiHierImprPrin) 
turned out to be unworkable; 
Simplified by [Frank Ramsey](https://plato.stanford.edu/entries/ramsey/) 
and formalised by Alonzo Church, 
it became *higher-order logic* as used today. 
Modern constructive type theories, such as Martin-Löf's, 
amalgamate ideas from both approaches,
providing a richer language of types and giving them a prominent role.

Of other approaches, one must mention 
Quine's [New Foundations](https://plato.stanford.edu/entries/quine-nf/). 
He aimed to have a universal set containing itself as an element. 
In order to prevent Russell's paradox, he introduced the notion of a *stratified* formula,
a kind of local type checking that prohibited $\\{x \mid x\not\in x\\}$.
The problem was, nobody was sure for decades whether NF was consistent or not,
making it a rather scurvy candidate for the foundations of mathematics. 

### What was its impact?

Russell's paradox comes from Cantor's theorem, which states that 
there is no injection from the powerset ${\cal P}(A)$ of a given $A$ into $A$ itself. 
(There is no way to assign each element of ${\cal P}(A)$
a unique element of $A$.) But if $V$ is the universal set, 
then ${\cal P}(V)$ is actually a subset of $V$, contradiction.
Or, to quote Gödel:

> By analyzing the paradoxes to which Cantor's set theory had led, he freed them from all mathematical technicalities, thus bringing to light the amazing fact that our logical intuitions (i.e., intuitions concerning such notions as: truth, concept, being, class, etc.) are self-contradictory.[^1]

[^1]: Kurt Gödel, [Russell's mathematical logic](https://doi.org/10.1017/CBO9781139171519.024). *In*: P Benacerraf, H Putnam (eds), *Philosophy of Mathematics: Selected Readings* (CUP, 1984), 447–469. I have already posted this quotation twice before (on [Wittgenstein]({% post_url 2023-04-12-Wittgenstein %}) and then on the [foundations of mathematics]({% post_url 2023-11-01-Foundations %})).


This was huge. Mathematicians and philosophers have taken for granted that a *concept* 
(i.e., property)
and the corresponding *class* (i.e., set) were more or less interchangeable.
The concept of red could be identified with the class of all red things; 
the concept of an even number could be identified with the class of even numbers. 
The universal class could be defined as the class of all $x$ satisfying $x=x$.
In fact, we can still do this. But people took for granted that these classes 
were entities in themselves, and in particular, could belong to other classes. 
That is what had to be sacrificed. 

As late as the early 20th century, when Whitehead and Russell were writing
[Principia Mathematica](https://plato.stanford.edu/entries/principia-mathematica/),
the words *class* and *set* were synonymous. 
Today, especially in the context of set theory, 
a *class* is the collection of everything satisfying a specific property,
but only sets actually **exist**. 
A reference to some proper class – say the universal class, or the class of ordinals –
is invariably described using the phrase "only a *façon de parler*": 
a manner of speaking, nothing more. 

George Boolos [has pointed out](https://www.jstor.org/stable/4545060) 
that Russell's paradox did not impact 
Frege's work in any significant way. Frege had indeed assumed 
unrestricted set comprehension, the fatal principle that leads to Russell's paradox.
But he used it only once, to derive a much weaker consequence 
that could have been assumed as an axiom instead. The paradox
did not damage Frege's work, which survives today as the predicate calculus. 
However, it devastated his intellectual framework. 

### Wider ramifications

Russell's paradox was about as welcome as a bomb at a wedding. 
Decades later, the dust still had not settled.
Russell collected a list of other paradoxes, the most serious being 
Burali-Forti's: the set $\Omega$ of ordinal numbers is itself an ordinal number, 
and therefore $\Omega\in \Omega$, which implies $\Omega<\Omega$. 

The first part of the 20th century saw the publication of Zermelo's
axioms for set theory, in which he introduced his separation axiom, and much more controversially, his *axiom of choice*. 
In that febrile time, many had no appetite for further risk-taking 
in the form of this radical new axiom.
Whitehead and Russell formalised a significant chunk of mathematics using their type theory. 
Hilbert announced his programme for proving the consistency of mathematics, 
but the incompleteness and undecidability results of the 1930s put an end to such ideas. 
By the 1960s, we had learned that fundamental questions – such as the status of the axiom of choice and the [continuum hypothesis](https://plato.stanford.edu/entries/continuum-hypothesis/) – could not be settled 
using the axioms of Zermelo-Fraenkel set theory. 

Russell's paradox also made its appearance in Alonzo Church's $\lambda$-calculus. 
Church originally conceived his system as a new approach to logic, 
in which sets were encoded by their characteristic functions: $MN$
meant that $N$ was an element of $M$, 
while $\lambda x. M$ denoted unrestricted set comprehension over the predicate $M$.
Church devised techniques for encoding Boolean values and operations 
within the $\lambda$-calculus.
However, Haskell Curry noticed that the Russell sat $R$ 
could be expressed as $\lambda x. \neg (x x)$.
He thereby obtained a contradiction, $RR = \neg(RR)$.
Generalising from negation to an arbitrary function symbol, 
Curry obtained his famous $Y$-combinator.
This gave Church's $\lambda$-calculus tremendous expressivity, 
but rendered his logic inconsistent. 

### However

Ludwig Wittgenstein wasn't much bothered by contradictions. He wrote, with his usual lucidity, 

> If a contradiction were now actually found in arithmetic that would only prove that an arithmetic with such a contradiction in it could render very good service; and it will be better for us to modify our concept of the certainty required, than to say that it would really not yet have been a proper arithmetic.

This means apparently that what you don't know can't hurt you. 
However, that is not actually true. 
