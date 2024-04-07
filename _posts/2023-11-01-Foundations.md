---
layout: post
title:  What do we mean by "the foundations of mathematics"?
usemathjax: true 
tags: [philosophy, logic, type theory, Principia Mathematica, AUTOMATH]
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
* the discovery of non-Euclidean geometries
* Russell's paradox (1901) and many others

The story of Pythagoras trying to suppress the shocking 
discovery of irrational numbers such as $\sqrt2$, 
the ratio of the diagonal of a square to its side, is probably mythical. 
But it seems that [they noticed](https://plato.stanford.edu/entries/dedekind-foundations/):

> The Greeks’ response to this startling discovery culminated in Eudoxos’ theory of ratios and proportionality, presented in Chapter V of Euclid’s Elements.

The nature of the real numbers was still not clear in the 19th century.
Richard Dedekind devoted himself to this problem, 
inventing the famous [Dedekind cuts](https://en.wikipedia.org/wiki/Dedekind_cut):
downwards-closed sets of rational numbers. Cantor independently chose to define
real numbers as equivalence classes of Cauchy sequences.
The point is not that a real number *is* either of those things, but simply that
we can present specific constructions exhibiting the behaviour expected of the real numbers.

Cantor's work on set theory is well known. Dedekind also made major contributions, in his
by [*Was Sind und Was Sollen die Zahlen* ](https://plato.stanford.edu/entries/dedekind-foundations/).
Their aim was finally to pin down the precise meaning of concepts such as function,
relation and class, and how to make sense of infinite collections and infinite constructions.

Berkeley's attack on infinitesimals resulted in a concerted effort to banish them
in favour of $\epsilon$-$\delta$ arguments (hated by many), which remind me of
challenge-response protocols in computer science. As I've [noted previously]({% post_url 2022-08-10-Nonstandard_Analysis %}) on this blog,
today – thanks to set theory – we have the theoretical tools to place infinitesimals
on a completely rigorous basis.

### The paradoxes and the solutions

The [paradoxes of set theory](https://plato.stanford.edu/entries/settheory-early/#CritPeri),
discovered around the turn of the 20th century, aroused huge disquiet. Although I have
posted this exact quote [previously]({% post_url 2023-04-12-Wittgenstein %}), there is no better description than Gödel's:

> By analyzing the paradoxes to which Cantor's set theory had led, he freed them from all mathematical technicalities, thus bringing to light the amazing fact that our logical intuitions (i.e., intuitions concerning such notions as: truth, concept, being, class, etc.) are self-contradictory.[^1]

[^1]: Kurt Gödel, [Russell's mathematical logic](https://doi.org/10.1017/CBO9781139171519.024). *In*: P Benacerraf, H Putnam (eds), *Philosophy of Mathematics: Selected Readings* (CUP, 1984), 447–469

Russell's paradox was seen as a potentially fatal blow to much of the 19th century
foundational work, including that of Frege, Dedekind and Cantor.
Russell (and Whitehead) decided to continue in the spirit of Frege's *Logicist*
programme of reducing mathematics to logic. But does this make sense? I can imagine
De Bruijn saying 

> We do not possess a workable definition of the word "logic". 

The system they created in the multivolume 
[*Principia Mathematica*](https://plato.stanford.edu/entries/principia-mathematica/)
was needlessly complicated and in some respects curiously imprecise.
But it led to today's first-order logic and especially higher-order logic.
Russell and Whitehead formalised some chunks of mathematics in great detail
and with immense tedium, but they could not have predicted how powerful
their system would turn out to be.

Many philosphers had contemplated the essence of mathematics in prior centuries,
but the crisis gave the issues urgency. Roughly speaking, there are three main schools of thought:

* The *Platonist* or *realist* viewpoint: ideal mathematical objects, such as the complex plane, exist objectively and independently of us, though we may deduce their properties. Gödel held this view.
* The *formalist* viewpoint: mathematics is concerned with symbols. For Hilbert,
I think that [his programme](https://plato.stanford.edu/entries/hilbert-program/)
was a technical approach to abolish the paradoxes rather than
an expression of his true beliefs. How can one person adhere to
a [finitary point of view](https://plato.stanford.edu/entries/hilbert-program/#2)
and simultaneously describe Cantor's world of transfinite ordinals and cardinals
as a paradise? But it seems that others, such as Curry, regarded mathematics
as nothing but a symbolic game.
* The [*intuitionists*](https://plato.stanford.edu/entries/intuitionism/) held that mathematical objects were nothing but creations of the human mind.
This gave them a radical attitude to proof and the wholesale rejection of many techniques and concepts regarded by others as indispensable.
Their rejection of the reality of mathematical objects and their stance against
symbolic formulas (other than as a means of communicating ideas) 
set them firmly against the other schools.

It seems clear from the reactions of Frege, Russell, Hilbert, Brouwer and many others
that the paradoxes constituted an emergency. Russell's "vicious circle principle"
and his solution, namely ramified type theory, Brouwer's intuitionism and Hilbert's formalism
– these were the equivalent of burning all your clothes and furniture upon the discovery of bedbugs.
That the solution could lie in something as simple as 
[Zermelo's separation axiom](https://plato.stanford.edu/entries/zermelo-set-theory/)
and the conception of the [cumulative hierarchy of sets](/papers/Boolos-iterative-concept-of-set.pdf)[^2]
was seemingly not anticipated.
It was a miracle.

[^2]: George Boolos, [The iterative concept of set](https://doi.org/10.1017/CBO9781139171519.026). *Ibid*, 486–502

### Modern foundations of mathematics

Today one commonly sees all kinds of things described as "foundations of mathematics",
especially category theory and type theory. Foundational work has definitely been done
within the framework of category theory, but that is not the same thing as saying that
category theory itself is foundational. The objects in category theory are equipped with
structure and the morphisms between objects are structure preserving, just as we have homomorphisms between groups and continuous maps between topological spaces. 
By contrast, classical sets have no notion of structure beyond the membership relation, 
which we might regard as bare metal.
Since a large part of mathematics is concerned with structure, 
category theory is a natural fit. 
That does not mean, however, that it addresses foundational issues.
It tends rather to introduce new ones, especially because of its unfortunate and 
needless habit of assuming the existence of proper classes everywhere. 
Far from replacing set theory, it relies on it.

As to whether type theory is foundational, we need to ask which type theory you are talking about:

* Principia Mathematica: of course, that was its precise purpose. Gödel's essay, [Russell's mathematical logic](/papers/Russells-mathematical-logic.pdf), 
is an indispensable source on this and related topics.
* Church's simple type theory: the granddaughter of PM, it is equally expressive and a lot simpler.
* Automath: absolutely not. De Bruijn consistently referred to it as "a *language* for mathematics". He moreover said it was "like a big restaurant that serves all sorts of food: vegetarian, kosher, or anything else the customer wants".[^3] Automath was, by design, neutral to foundational choices. (Isabelle/Pure is in the same spirit.)
* Martin-Löf type theory: he himself said it was intended as a vehicle for formalising Bishop-style analysis, clearly a foundational claim. But one that rejects the vast majority of modern mathematics.  
* Calculus of inductive constructions (Coq, Lean): the original paper (describing a weaker system) begins "The calculus of constructions is a higher-order formalism for constructive proofs in natural deduction style," and the paper makes no foundational claims. 
Coquand's [retrospective paper](https://www.cse.chalmers.se/~coquand/v1.pdf) makes no such claims either. 
Since it turns out to be significantly stronger than ZF set theory, one could even say it makes foundational assumptions. 

[^3]: N.G. de Bruijn. A Survey of the Project Automath. *In*: R. P. Nederpelt, J. H. Geuvers, & R. C. Vrijer, de (Eds.), *Selected Papers on Automath* (North-Holland, 1994), 144

The world has moved on. People no longer worry about the issues that were 
critical in the 19th century: the role of the real numbers, the role of infinity,
the status of infinitesimals, the very consistency of mathematics.
And the reason is simple: because Herculean work in the 19th and 20th centuries 
largely banished those issues from our minds. 
This achievement doesn't seem to be much appreciated today.
Instead of "each real number can be understood as a set of rational numbers, and more generally, the most sophisticated mathematical constructions can be reduced 
to a handful of simple principles"
people say "we are asked to believe that everything is a set" 
and even "set theory is just another formal system". 
I give up.
