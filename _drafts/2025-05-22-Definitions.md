---
layout: post
title:  "The concept of definition: in mathematics, and in computational logic"
usemathjax: true 
tags: [MJC Gordon, HOL system, Isabelle, philosophy, Imre Lakatos]
---
Definitions are ubiquitous in mathematics, but we don't tend to think about 
them until one gets us into trouble.
When using a proof assistant, definitions can raise practical issues.
Complicated definitions can sometimes impact performance.
More embarrassingly, a formal proof that *all widgets are stable*
isn't good for much if it turns out that there are no widgets 
or that everything is stable: it's essential to check that your definitions are correct at the start of a big proof.
There was even a case, years ago, where a particularly fiendish definition
could allow an Isabelle user to prove 1=0.
(We will take a look at this below.)
Although users do need to take responsibility for their definitions,
and early systems did not check definitions rigorously,
people today expect that no matter how lousy a definition might be,
it will at least not introduce inconsistency.

### Definitions in mathematics

A *pentagon* is a five-sided polygon. 
That's pretty simple, and although it builds on the notion of a polygon,
hence on the notion of a line segment, etc., 
it isn't hard to reduce everything to the primitives 
(points and lines) given by Euclid's axioms.

There are many decisions to be made and some of them may seem arbitrary.
If we allow the length of a side to be zero,
then every triangle and square could also be seen a pentagon: 
what good would that be?
Also, often we care about the angle between adjacent sides, 
which for a zero-length side would be undefined.
So every side of a polygon must have positive length.
The standard definition does allow the sides to cross:
a five pointed star is also a pentagon.

On this theme, recall yet again the study of
[Euler’s polyhedron formula](https://www.ams.org/publicoutreach/feature-column/fcarc-eulers-formula)
by [Imre Lakatos](https://plato.stanford.edu/entries/lakatos/),
mentioned [here before](https://lawrencecpaulson.github.io/tag/Imre_Lakatos),
where what at first sight appears to be a flaw in a proof
turns out to be a dispute about the definition of "polyhedron".
He considers freakish cases such as cylinders and polyhedra containing holes.
Euler’s formula can be generalised 
to [account for holes](https://momath.org/mathmonday/hole-new-polyhedra/), 
but modern treatments prefer alternative generalisations (to multiple dimensions) 
where the objects must be convex.

Definitions of abstractions like groups or topological spaces 
play a huge role in mathematics.
A *group* is a set equipped with product and inverse operations
along with an identity element.
A *topological space* defines the notion of an open set, 
and in terms of that, limits and continuity.
The set of real numbers is a group (although not an interesting one)
and is also a topological space:
such abstract concepts capture just one aspect of a mathematical entity.
The set of permutations over a space and a set of rotations in three dimensions
might seem to have little in common, but both are groups.

By the way, saying "**the** set of real numbers" implies that it is unique,
and yet there are many constructions representing a real number variously as 
a Dedekind cut or a Cauchy sequence. 
The resulting sets of real numbers are not equal, just isomorphic.
Kevin Buzzard has [recently written](https://arxiv.org/pdf/2405.10387)
about mathematicians who define something to be the *canonical* such-and-such,
when "canonical" turns out to be ambiguous or meaningless.
It turns out that the real numbers can be characterised as
a complete Archimedean ordered field, 
where abstract concepts combine to determine something that is unique
(but only up to isomorphism!).

I can't resist mentioning the generalisation of division to $x/0=0$,
which is common in proof assistants.
It causes a great many useful identities to hold unconditionally:
for example, we get $(x+y)/z = x/z+y/z$ without having to prove $z\not=0$.
Such a step is safe because it cannot affect the meaning or truth 
of a formula not containing the division symbol.
In particular, it cannot introduce inconsistency.

### Definitions in proof assistants

The earliest systems, such as AUTOMATH and Boyer–Moore,
provided safe principles where an entity could be defined
in terms of already existing entities. Edinburgh LCF made no distinction
between definitions and arbitrary axioms, 
but for its successor, the HOL system, Mike Gordon
introduced principles for defining 

* a constant to abbreviate a term
* a type comprising of every element of a some other type satisfying a given predicate.

Gordon noted the need for careful checks to ensure that making a definition
preserved consistency.
Most other proof assistants developed around that time also provided for definitions, so LCF was the odd man out here.

Mathematicians know that you seldom prove a theorem
simply by expanding the definitions of the things mentioned therein.
Best is to appeal to previously established high-level facts, 
avoiding any dependency on the possibly arbitrary technicalities 
of a particular definition.
It's therefore odd that many proof assistants expand definitions aggressively.
One notable, not-to-be-named system, actually treated definitions like macros.
They were kept expanded internally, 
but were contracted by the pretty printer (if you were lucky).
With [such an approach](https://doi.org/10.1023/A:1020827725055), 
their users were lucky if any proof step ever terminated, 
and they had enviable hardware too.

**XXXXX SCHEMES monster definitions taking months XXXXX**

### A circular definition accepted by Isabelle 2015

Early versions of Isabelle, following the idea that users should take responsibility 
for their own definitions, allowed constants to be declared in one place 
and defined somewhere else. Any circularities would be the user's fault.
Over time, the definitional principles were made more restrictive,
but in 2015, Kunčar and Popescu 
[found a number of ways](https://eprints.whiterose.ac.uk/id/eprint/191505/1/Consistent_Foundation_IsabelleHOL_JAR_2019.pdf) 
to combine several advanced definitional principles to obtain a circularity.

Since the definition is highly technical, let's skip the Isabelle syntax
and see how it worked:

* Introduce the *overloaded* constant $c : \alpha$, 
which Isabelle will allow to be defined later, different definitions
for different instances of $\alpha$.
* Define the type $\tau$ to contain the values True and $c:{}$bool.
* Finally, $c:{}$bool is defined to denote the value of $\neg(\forall x_\tau y.\,x=y)$.

Now we get a contradiction:

* if $c:{}$bool is true then $\tau$ has one element, 
thus $\forall x_\tau y.\,x=y$ is true
* if $c:{}$bool is false then $\tau$ has two elements
thus $\forall x_\tau y.\,x=y$ is false

This and similar examples made it clear that Isabelle was too freewheeling
in allowing overloaded constants to be defined at any point.
Kunčar and Popescu's paper defines sufficient conditions to detect 
circularities in definitions and proves that they are adequate.
The stricter regime was implemented from Isabelle2016 
and no user developments were lost along the way.