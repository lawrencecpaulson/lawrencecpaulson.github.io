---
layout: post
title:  "Russell's Paradox: Myth and Fact"
usemathjax: true 
tags: [logic, Bertrand Russell, Principia Mathematica, philosophy]
---

The story of Russell's paradox is well known. Gottlob Frege had written a treatise on the foundations of arithmetic, a formal development of basic mathematics from first principles. 
Bertrand Russell, upon reading it, wrote to Frege mostly to praise the work, but asking a critical question. Frege replied to express his devastation at seeing his life's work ruined. 
Some later commentators went further, saying that Russell's paradox refuted the entire [logicist approach](https://plato.stanford.edu/entries/logicism/#) 
to the foundations of mathematics (the idea that mathematics can be reduced to logic). 
Much is wrong with this story. 
The impact of Russell's paradox is less than many believe, and greater. 

### What is Russell's paradox?

The paradox can be expressed quite simply in English.
Let $R$ denote the set of all sets that are not members of themselves;
Then, $R$ is a member of itself if and only if it is not a member of itself. 
(In symbols, define $R$ as $\{x \mid x\not\in x\}$; then $R\in R$ iff $R\not\in R$.)
Both possibilities lead to a contradiction. 

Faced with such a situation, we need to look at every assumption made to identify where the problem lies. The key assumption is clearly the notion of a set.
It is an abstraction of various collective nouns in common use, 
such as nation, clan, family. In each of these we deal with units composed of smaller units,
And we even have a hierarchy: a nation can be a collection of clans, 
each of which is a collection of families. 
For further examples we have herds, armies (and their hierarchy of divisions, regiments, etc).
None of these can be members of themselves, so maybe that idea is suspect. 
But if we conceive of the universal set, to which everything belongs, 
then presumably it belongs to itself. 
This is a big hint that the universal set is the root of the problem,
but this insight does not show us the way out. 
Two very different solutions emerged: 

* *Axiomatic set theory*. There is no universal set. More generally, you cannot just form a set from an arbitrary property; instead, axioms are provided allowing the construction of sets according to certain specific principles. This prevents the construction of $R$. 
For technical purposes, a further axiom is usually assumed, to forbid 
sets being members of themselves and moreover **all** nonterminating membership chains,
such as $x\in y\in x$ and  $\cdots \in x_3\in x_2\in x_1$. 
This route is due to [Zermelo](https://plato.stanford.edu/entries/zermelo-set-theory/) 
and Fraenkel.

* *Type theory*. It is forbidden to write $x\in x$. 
A type hierarchy is introduced to classify all values, and $x\in y$
can only be written if the type of $y$ is higher than that of $x$.
With types there is no universal set either, but there are universal sets for each type. 
This route is due to Whitehead and Russell, who further complicated their type theory 
to enforce the "vicious circle principle", which they saw as the root of all paradoxes. 
Their [ramified type theory](https://plato.stanford.edu/entries/type-theory/#RamiHierImprPrin) 
turned out to be unworkable; 
Simplified by Ramsey and formalised by Church, it became *higher-order logic* as used today. 
Modern constructive type theories amalgamate ideas from both approaches,
providing a richer language of types and giving them a prominent role.
It's notable that Martin-Löf initially referred to his system as Constructive Set Theory. 

Of other approaches, one must mention Quine's New Foundations. 
He aimed to have a universal set with itself as an element. 
In order to prevent Russell's paradox, he introduced the notion of a *stratified* formula,
a kind of local type checking that prohibited $\{x \mid x\not\in x\}$.
The problem was, nobody was sure for decades whether NF was consistent or not,
making it a rather scurvy candidate for the foundations of mathematics. 

### What was its impact?

The best description is due to Gödel.
I am unfortunately forced to repeat myself: I have already posted this quotation
twice before (on [Wittgenstein]({% post_url 2023-04-12-Wittgenstein %})
and then on the [foundations of mathematics]({% post_url 2023-11-01-Foundations %})):

> By analyzing the paradoxes to which Cantor's set theory had led, he freed them from all mathematical technicalities, thus bringing to light the amazing fact that our logical intuitions (i.e., intuitions concerning such notions as: truth, concept, being, class, etc.) are self-contradictory.[^1]

[^1]: Kurt Gödel, [Russell's mathematical logic](https://doi.org/10.1017/CBO9781139171519.024). *In*: P Benacerraf, H Putnam (eds), *Philosophy of Mathematics: Selected Readings* (CUP, 1984), 447–469

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
but only sets actually exist. A reference to the universal class, or the class of ordinals,
etc., is general described using the phrase "only a *façon de parler*": 
a manner of speaking, nothing more. 

George Boolos has pointed out that Russell's paradox did not impact 
Frege's work in any significant way. Frege had indeed assumed 
*unrestricted set comprehension*, the fatal principle that leads to Russell's paradox.
But he used it only once, to derive a much weaker consequence 
that could have been assumed as an axiom instead. The paradox
did not damage Frege's written work, but it devastated his entire intellectual framework. 

### Wider ramifications

XXXX

Y

 