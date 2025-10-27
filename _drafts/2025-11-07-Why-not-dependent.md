---
layout: post
title:  Why don't I use dependent types?
usemathjax: true 
tags: [memories, AUTOMATH, LCF, type theory, Martin-Löf type theory, NG de Bruijn]
---
To be fair, nobody asks this question.
But people have regularly asked why there are (in normal usage) 
no proof objects in Isabelle.
The two questions are essentially the same, 
because proof objects are intrinsic to all the usual type theories.
They are also a completely unnecessary and therefore a waste of space.
As described in a [previous post]({% post_url 2022-01-05-LCF %}),
type checking in the *programming language* (not the formalism) 
can ensure that only legitimate proof steps are executed.
Robin Milner had this fundamental insight 50 years ago,
giving us the LCF architecture.
But the best answer to the original question is, 
I did use dependent types, for years.

### My time with AUTOMATH

I was lucky enough to get some personal time with N G de Bruijn
when he came to Caltech in 1977 to lecture about
[AUTOMATH]({% post_url 2021-11-03-AUTOMATH %}).
I never actually used this system.
Back then, researchers used the nascent Internet (the ARPAnet)
not to download software so much as 
to run software directly on the host computer.
Most software was not portable, and AUTOMATH was configured to run on 
[a computer we did not have](https://automath.win.tue.nl/archive/pdf/aut034.pdf):

> Until September 1973, the computer was the Electrologica X8, after that
> Burroughs 6700. In both cases the available multiprogranming systems
> required the use of ALGOL 60.

I did however read many of the research reports, including 
the [PhD dissertation](https://automath.win.tue.nl/archive/pdf/aut046.pdf) by LS Jutting.
This dissertation presents his translation 
of Landau's text *Grundlagen der Analysis* (described [last time]({% post_url 2025-10-15-Proofs-trivial %}))
from German into AUTOMATH.
It is no coincidence that one of my earliest papers
copied the idea of 
[formalising a text](https://doi.org/10.1016/0167-6423(85)90009-7) 
and attempting to be faithful to it

As an aside, note that while AUTOMATH was a system of dependent types,
it did not embody the 
[Curry–Howard correspondence]({% post_url 2023-08-23-Propositions_as_Types %})
(sometimes wrongly called the Curry–Howard–de Bruijn correspondence).
That correspondence involves having a type theory strong enough
to represent the predicate calculus directly in the form of types.
AUTOMATH did not do this, and it is clear that de Bruijn
[did not approve](https://pure.tue.nl/ws/portalfiles/portal/4428179/597611.pdf) 
of the increasingly powerful type theories being developed.
Rather, AUTOMATH was a [logical framework](https://pure.tue.nl/ws/files/1892191/597622.pdf):

> like a big restaurant that serves all sorts of food: vegetarian, kosher, or anything else the customer wants

AUTOMATH provided a weak language, 
including a generalised product construction just
powerful enough to express the inference rules of a variety of formalisms
and to make simple definitions.
Its influence on Isabelle should be obvious, 
because it too provides a weak logical framework 
for expressing inference rules
and aims to be [*generic*](https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-130.html), like the big AUTOMATH restaurant.
It is not my fault that everybody prefers the same cuisine,
higher-order logic, so that Isabelle/HOL has become dominant.
It is also a pity that I last spoke to Dick (as he was known to friends)
when I was putting all my effort into Isabelle/ZF.
He simply loathed set theory and was convinced that mathematics was essentially typed.
He never lived to see the enormous amount of advanced mathematics
that would be formalised using types in Isabelle/HOL.

I annoyed him in another way. I kept asking,
AUTOMATH looks natural, but how do we know that it is right?
He eventually sent me a 300 page volume entitled
[The Language Theory of Automath](https://automath.win.tue.nl/archive/pdf/aut073.pdf).
It describes AUTOMATH's formal properties such as 
strong normalisation and Church–Rosser properties,
but this was not the answer I wanted at all.
I got that answer for a quite different type theory.

### Martin-Löf type theory

In response to kind invitations from Bengt Nordström and Kent Petersson,
I paid a number of visits to Chalmers University in Gothenburg
to learn about Martin-Löf type theory.
I was particularly impressed by its promise 
of a systematic and formal approach to program synthesis,
and had already encountered [intuitionism]({% post_url 2021-11-24-Intuitionism %})
through a course on the philosophy of mathematics at Stanford University.
The "rightness" of Martin-Löf type theory was obvious, 
because it directly embodied the principles of intuition truth
as outlined by Heyting: for example, that
a proof of $A\land B$ consists of a proof of $A$ paired with a proof of $B$.

I devoted several years of research to Martin-Löf type theory.
This included a whole year of intricate hand derivations to produce a 
[paper](https://doi.org/10.1016/S0747-7171(86)80002-5) 
that I once thought would be important,
and the [very first version]({% post_url 2022-07-13-Isabelle_influences %}) 
of Isabelle.
Yes, Isabelle began as an implementation of Martin-Löf type theory,
which is [still included]({% post_url 2022-11-30-CTT_in_Isabelle-II %}) 
in the distribution even today as Isabelle/CTT.
But eventually I felt what seemed to me as a rigid and doctrinaire attitude,
if not a literal cult of personality around Martin-Löf,
and the sudden switch to intentional equality 
(people were not allowed to disagree) wrecked most of my work.

You might ask, what about the calculus of constructions,
which arose during that time and eventually gave us Rocq and Lean?
To me they raised, and continue to raise, the same question I had put to de Bruijn.
Gérard Huet said something like "it is nothing but function application",
which did not convince me (you can say the exact same thing about the λ-calculus).
It's clear that I am being fussy, because thousands of people
find these formalisms perfectly natural and believable.
But it is also true that the calculus of constructions 
underwent numerous changes over the past four decades.
