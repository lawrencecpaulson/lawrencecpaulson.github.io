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
(See below.)
Although some early systems did not check definitions rigorously,
people today expect that no matter how lousy a definition might be,
it will at least not introduce inconsistency.
At the same time, users do need to take responsibility for their definitions.


### Definitions in mathematics

A *pentagon* is a five-sided polygon. 
That's pretty simple, and although it builds on the notion of a polygon,
hence on the notion of a line segment, etc., 
it isn't hard to reduce everything to the primitives 
(points and lines) given by Euclid's axioms.
There are many choices to be made, and some of them may seem arbitrary.
If we allow the length of a side to be zero,
then every triangle and square could also be seen a pentagon.
Also, often we care about the angle between adjacent sides, 
which for a zero-length side would be undefined.
For such reasons, we insist that every side of a polygon must have positive length.
The standard definition does allow the sides to cross:
a five pointed star is also a pentagon.

On the theme of definitional choices, recall yet again the study of
[Euler’s polyhedron formula](https://www.ams.org/publicoutreach/feature-column/fcarc-eulers-formula)
by [Imre Lakatos](https://plato.stanford.edu/entries/lakatos/),
mentioned [here before](https://lawrencecpaulson.github.io/tag/Imre_Lakatos),
where what first looks like a flaw in a proof
turns out to be a dispute about the definition of *polyhedron*.
He considers freakish cases such as cylinders and polyhedra containing holes.
Euler’s formula can be generalised 
to [account for holes](https://momath.org/mathmonday/hole-new-polyhedra/), 
but modern treatments prefer alternative generalisations (to multiple dimensions) 
where the objects must be convex.
The essence of his thesis is not the difficulty of getting proofs right, 
but the difficulty of getting definitions right.

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
might seem to have little in common, but both are groups,
and that is precisely the genius of the concept.

By the way, saying "**the** set of real numbers" implies that it is unique,
and yet there are many constructions representing a real number variously as 
a Dedekind cut or a Cauchy sequence. 
The resulting sets of real numbers are not equal, just isomorphic.
Kevin Buzzard has [recently written](https://arxiv.org/pdf/2405.10387)
about mathematicians who define something to be the *canonical* such-and-such,
when "canonical" turns out to be ambiguous or meaningless.
It turns out that the real numbers can be characterised as
a complete Archimedean ordered field, 
where abstract concepts combine to determine something that is unique.
But only up to isomorphism!

I can't resist mentioning the generalisation of division to $x/0=0$,
which is common in proof assistants.
It causes a great many useful identities to hold unconditionally:
for example, we get $(x+y)/z = x/z+y/z$ without having to prove $z\not=0$.
Such a step is safe because it cannot affect the meaning or truth 
of a formula not containing the division symbol.
In particular, it cannot introduce inconsistency.
To be sure of this, we need to know that a definition in a proof assistant can always be eliminated.

### Definitions in proof assistants

The earliest systems, such as [AUTOMATH](http://localhost:4000/tag/AUTOMATH) and [Boyer–Moore](https://dl.acm.org/doi/10.1145/321864.321875),
provided safe principles where an entity could be defined
in terms of already existing entities. [Edinburgh LCF](http://localhost:4000/tag/LCF) made no distinction
between definitions and arbitrary axioms, 
but for its successor, the [HOL system](http://localhost:4000/tag/HOL_system), 
Mike Gordon introduced principles for defining 

* a constant to abbreviate a term
* a type comprising of every element of a some other type satisfying a given predicate.

Gordon noted the need for careful checks to ensure that making a definition
preserved consistency.
Most other proof assistants developed around that time also provided for definitions, so LCF was the odd man out here.

Definitions can become gigantic.
When specifying a computer architecture or programming language semantics,
we might expect this.
But even in pure mathematics, key definitions sometimes involve
so many layers, they take months to formalise.
Consider Grothendieck schemes: they are vital to the study of algebraic geometry,
and when Kevin Buzzard first took an interest in formalising mathematics,
they had not been defined in any proof assistant.
He set a student on the task, Ramon Fernández Mir,
who completed it and wrote up his work as a 56-page [Master's dissertation](https://www.imperial.ac.uk/media/imperial-college/faculty-of-engineering/computing/public/1819-ug-projects/Fernandez-I-MirR-Schemes-in-Lean.pdf)
and later as a [journal article](https://www.tandfonline.com/doi/full/10.1080/10586458.2021.1983489).
In response to various claims that such a feat would be impossible
in Isabelle/HOL, we had to [do it too](https://doi.org/10.1080/10586458.2022.2062073),
despite having no use for schemes.

This leads to the question, how can we check whether a formal definition is correct?
Good practice is to develop a theory of its basic properties
within your proof assistant, capturing both positive and negative properties
(e.g. *X* is a group but *Y* is not a group) and attempting some non-trivial constructions.
Your theory will perform the useful function of providing a of library of basic facts.

Mathematicians know that you seldom prove a theorem
simply by expanding the definitions of the things mentioned therein.
Best is to appeal to your library of basic facts, 
avoiding any dependency on the possibly arbitrary technicalities 
of a particular definition.
It's therefore odd that many proof assistants expand definitions aggressively.
One notable, not-to-be-named system, actually treated definitions like macros.
They were kept expanded internally, 
but were contracted by the pretty printer (if you were lucky).
With [such an approach](https://doi.org/10.1023/A:1020827725055), 
their users were lucky if any proof step ever terminated, 
and they had enviable hardware too.

### A circular definition accepted by Isabelle 2015

Early versions of Isabelle, following the idea that users should take responsibility 
for their own definitions, allowed constants to be declared in one place 
and defined somewhere else. Any circularities would be the user's fault.
Over time, the definitional principles were tightened up somewhat,
but in 2015, Kunčar and Popescu 
[found a number of ways](https://eprints.whiterose.ac.uk/id/eprint/191505/1/Consistent_Foundation_IsabelleHOL_JAR_2019.pdf) 
to combine several advanced definitional principles to obtain a circularity.

Since the definition is highly technical, let's skip the Isabelle syntax
and see how it worked:

* Introduce the *overloaded* constant $c : \alpha$, 
which Isabelle will allow to be defined later, with separate definitions
for different instances of $\alpha$.
* Define the type $\tau$ to consist of the values True and $c:{}$bool.
* Define $c:{}$bool to denote the value of $\neg(\forall x_\tau y_\tau.\,x=y)$.

Now we get a contradiction:

* if $c:{}$bool is True then $\tau$ has one element, 
thus $\forall x_\tau y_\tau.\,x=y$ is True, making $c$ False
* if $c:{}$bool is False then $\tau$ has two elements
thus $\forall x_\tau y_\tau.\,x=y$ is False, making $c$ True

This and similar examples made it clear that Isabelle was too freewheeling
in allowing overloaded constants to be defined at any point.
Kunčar and Popescu's paper defines sufficient conditions to detect 
circularities in definitions and proves that they are adequate.
The stricter regime was implemented from Isabelle2016 
and no user developments were lost along the way.

### Definitions in the real world

In previous posts, I've commented on the philosophical
[problem of induction]({% post_url 2025-03-28-Induction_Fetzer %})
and on [mathematical truth]({% post_url 2022-07-27-Truth_Models %}).
Both of them contrast the empirical world of our senses
with the world of mathematics and how the former can be modelled within the latter.
So we can look at a scene from Dickens' novel 
[*Hard Times*](https://www.victorianlondon.org/etexts/dickens/hard_times-0002.shtml),
where Mr Gradgrind confronts "girl number twenty":

> Give me your definition of a horse.

The girl being rendered speechless, although her father works with horses,
Mr Gradgrind calls upon a boy named Bitzer:

> 'Bitzer,' said Thomas Gradgrind. 'Your definition of a horse.'

The boy replies:

> 'Quadruped. Graminivorous. Forty teeth, namely twenty-four grinders, four eye-teeth, and twelve incisive. Sheds coat in the spring; in marshy countries, sheds hoofs, too. Hoofs hard, but requiring to be shod with iron. Age known by marks in mouth.' Thus (and much more) Bitzer.

The scene ends:

> 'Now girl number twenty,' said Mr. Gradgrind. 'You know what a horse is.'

What's different here, compared with mathematical definitions,
is that horses exist whether we define them or not.
What we have here is not so much a definition as a description.
If we consult a modern dictionary, we again get a description, e.g.
"a large plant-eating domesticated mammal with solid hoofs and a flowing mane and tail". A horse is nothing like a pentagon, 
which we can imagine constructing, and it is certainly not like a group, which is an abstract structure not even dreamt of
until Galois came along. The empirical world being complex and messy,
it can be hard to arrive at definitions that appropriately classify horses, 
ponies, donkeys, mules, zebras, etc. Sometimes this sort of precision is necessary, which is one way lawyers make a living.

On the subject of the existence of mathematical objects,
I am in disagreement with some extremely smart people, such as Kurt Gödel
and Roger Penrose. Gödel claims that mathematical objects enjoy objective existence, and Penrose in his bestselling *The Emperor's New Mind*, 
declares that "the" complex plane definitely exists somewhere.
He must be referring to some sort of ideal complex plane as opposed to one of the numerous different constructions of one.
But his metaphysical imagination must fail when it comes to groups, because there is no ideal group to serve as "the" group.
