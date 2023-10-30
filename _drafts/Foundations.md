---
layout: post
title:  What do We Mean by "The Foundations of Mathematics"?
usemathjax: true 
tags: [philosophy]
---
The phrase "foundations of mathematics" is bandied about frequently these days,
but it's clear that there is widespread confusion about what it means.
Some say that a proof assistant must be based on a foundation of mathematics,
and therefore that the foundations of mathematics refers to some sort of formal system.
And yet, while set theory is frequently regarded as *the* foundation of mathematics,
none of the mainstream proof assistants are based on set theory.
These days we see everything from category theory to homotopy type theory
described as a possible foundation of mathematics.
There is a lot of wrongness here.

### What we mean by the foundations of mathematics?

N. G. de Bruijn made the remarkable claim

> We do not possess a workable definition of the word "mathematics". (AUT001, p. 4)

He seemed to be referring primarily to the difficulty of defining 
*mathematical reasoning*, but the dictionary definition – "the abstract science of number, quantity, and space" – does not begin to scratch the surface
of the topics studied by mathematicians, such as groups, abstract topologies,
graphs or even finite sets. If we can't define mathematics, neither can we define
the notion of mathematical foundations.

One solution to this difficulty is to say, "I can't define it but I know what it is
when I see it". This has famously been applied to pornography and even there does not 
settle the question in the case of something like 
Titian's [Venus d'Urbino](https://en.wikipedia.org/wiki/Venus_of_Urbino).
Mathematical reasoning can be wrong or doubtful while still being great mathematics;
Newton and Euler used infinitesimals and other methods generally rejected today.
Crank attempts to square the circle or prove the Riemann hypothesis 
often look like mathematics while saying nothing.

The foundations of mathematics is concerned with questions of the form
"does this even make sense"? It seems to be triggered by periodic crises:

* the existence of irrational numbers 
* Berkeley's [criticism of infinitesimals](https://plato.stanford.edu/entries/continuity/)
* the infinite
* Russell's paradox (1901) and many others

The story of Pythagoras trying to suppress the shocking 
discovery of irrational numbers such as $\sqrt2$, 
the hypotenuse of a right triangle, is probably mythical. 
But it seems that [they noticed](https://plato.stanford.edu/entries/dedekind-foundations):

> The Greeks’ response to this startling discovery culminated in Eudoxos’ theory of ratios and proportionality, presented in Chapter V of Euclid’s Elements.

But the nature of the real numbers was not clear in the 19th century.
Richard Dedekind devoted himself to this problem, 
inventing the famous [Dedekind cuts](https://en.wikipedia.org/wiki/Dedekind_cut):
downwards-closed sets of rational numbers. Cantor independently chose to define
real numbers as equivalence classes of Cauchy sequences.
The point is not that a real number either of those things, but simply that
we can present specific constructions exhibiting the behaviour expect of the real numbers.

Cantor's work on set theory is well known. Dedekind also made major contributions, in his
by [*Was Sind und Was Sollen die Zahlen* ](https://plato.stanford.edu/entries/dedekind-foundations/).
Their aim was finally to pin down the precise meaning of concepts such as function,
relation and class, and how to make sense of infinite collections and infinite constructions.

Berkeley's attack on infinitesimals resulted in a concerted effort to banish them
in favour of $\epsilon$-$\delta$, which although frequently hated remind me of
challenge-response protocols. As I've [noted previously]({% post_url 2022-08-10-Nonstandard_Analysis %}) on this blog,
today – thanks to set theory _ we have the theoretical tools to place infinitesimals
on a completely rigorous basis.

### The paradoxes

The [paradoxes of set theory](https://plato.stanford.edu/entries/settheory-early/#CritPeri),
discovered around the turn of the 20th century, aroused huge disquiet. Although I have
posted this quotation [previously]({% post_url 2023-04-12-Wittgenstein %}), there is no better description than Gödel's:

> By analyzing the paradoxes to which Cantor's set theory had led, he freed them from all mathematical technicalities, thus bringing to light the amazing fact that our logical intuitions (i.e., intuitions concerning such notions as: truth, concept, being, class, etc.) are self-contradictory.[^1]

[^1]: Kurt Gödel, [Russell's mathematical logic](https://doi.org/10.1017/CBO9781139171519.024). *In*: P Benacerraf, H Putnam (eds), *Philosophy of Mathematics: Selected Readings* (CUP, 1984), 447-469

It seems clear from the reactions of Frege, Russell, Hilbert, Brouwer and many others
that this was an emergency. I see Russell's "vicious circle principle"
and his solution, namely ramified type theory, Brouwer's intuitionism and Hilbert's formalism
as the equivalent of burning all your clothes and furniture upon the discovery of bedbugs.
That the solution could lie in something as simple as Zermelo's separation axiom
and the conception of the cumulative hierarchy of sets was seemingly not anticipated.
It was a miracle.

### On the existence of mathematical objects

Many had devoted some thought to the meaning of mathematics in prior centuries,
but the crisis brought the issue out into the open. Roughly speaking, there are three main viewpoints:

* The Platonist or realist view: ideal mathematical objects, such as the complex plane, exist objectively and independently of us, though we may deduce their properties. Gödel held this view.
* The intuitionist view: mathematical objects are creations of the human mind.
* The formalist view: mathematics is concerned with symbols, and symbols alone.

