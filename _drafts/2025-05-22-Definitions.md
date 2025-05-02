---
layout: post
title:  The concept of definition in mathematics and computational logic
usemathjax: true 
tags: [MJC Gordon, HOL system, Isabelle, philosophy, Imre Lakatos]
---
Definitions are ubiquitous in mathematics, but we don't tend to think about 
the concept of definition until one gets us into trouble.
For example, Kevin Buzzard has [recently written](https://arxiv.org/pdf/2405.10387)
about defining something to be the *canonical* such-and-such,
when the word canonical turns out to be ambiguous or meaningless.
When using a proof assistant, definitions also raise practical issues.
In some situations, complicated definitions can impact performance.
More embarrassingly, a formal proof that *all widgets are stable*
isn't good for much if it turns out that there are no widgets 
or that everything is stable: it's essential to check that your definitions are right at the start of a big proof.
There was even a case, years ago, where a particularly fiendish definition
could allow an Isabelle user to prove 1=0.
Although users do need to take responsibility for their definitions,
and early systems did not check definitions rigorously,
people today expect that no matter how lousy a definition might be,
it will at least not introduce inconsistency.

### Definitions in mathematics

A pentagon is a five-sided polygon. 
That's pretty simple, and although it builds on the notion of a polygon,
hence on the notion of a line segment etc, the process is straightforward.
There are many decisions to be made and some of them may seem arbitrary.
Can the length of a side equal zero?
But then every triangle and square would also be a pentagon,
a generalisation with no obvious benefit.
Also, often we care about the angle between adjacent sides, 
which for a zero-length side would be undefined.
And yet the standard definition does allow the sides to cross:
a five pointed star is also a pentagon.
On this theme recall yet again the study of
[Euler’s polyhedron formula](https://www.ams.org/publicoutreach/feature-column/fcarc-eulers-formula)
by [Imre Lakatos](https://plato.stanford.edu/entries/lakatos/),
mentioned [here before](https://lawrencecpaulson.github.io/tag/Imre_Lakatos),
where what at first sight appears to be a flaw in a proof
turns out to be a dispute about the concept of a polyhedron.
He considers freakish cases such as cylinders and polyhedra containing holes.
Euler’s formula can be generalised to holes, 
but modern treatments prefer alternative generalisations (to multiple dimensions) 
where the objects must be convex.

I can't resist mentioning the generalisation of division to $x/0=0$,
which is common in proof assistants.
It causes a great many useful identities, such as $(x+y)/z = x/z+y/z$,
to hold unconditionally, eliminating the need to prove $z\not=0$.
Such a step is safe because it cannot affect the meaning or truth 
of a formula not containing the division symbol.
In particular, it cannot introduce inconsistency.

### Definitions in proof assistants

The earliest systems, such as AUTOMATH and Boyer–Moore,
provided safe principles where an entity could be defined
in terms of already existing entities. LCF made no distinction
between definitions and arbitrary axioms, 
but for its successor, the HOL system, Mike Gordon
introduced definitional principles, also for types,
noting the need for careful checks to ensure preservation of consistency.
Most other proof assistants developed around that time also provided for definitions, so LCF was the odd man out here.

Most mathematicians know that you seldom prove a theorem
by expanding the definitions of the things mentioned therein,
preferring to appeal to previously established facts at the highest possible level.
It's therefore odd that many proof assistants expand definitions aggressively,
and in one not-to-be-named case, actually treated definitions like macros.
With [such an approach](https://doi.org/10.1023/A:1020827725055), i
t is a wonder that any proof ever terminates.
