---
layout: post
title:  "\"Why don't you use dependent types?\""
usemathjax: true 
tags: [memories, AUTOMATH, LCF, type theory, Martin-Löf type theory, NG de Bruijn, ALEXANDRIA]
---
To be fair, nobody asks me this exact question.
But people have regularly asked why Isabelle dispenses with proof objects.
The two questions are essentially the same, 
because proof objects are intrinsic to all the usual type theories.
They are also completely unnecessary and a huge waste of space.
As described in an [earlier post]({% post_url 2022-01-05-LCF %}),
type checking in the *implementation language* (rather than in the logic)
can ensure that only legitimate proof steps are executed.
Robin Milner had this fundamental insight 50 years ago,
giving us the LCF architecture with its proof kernel.
But the best answer to the original question is simply this: 
I did use dependent types, for years.

### My time with AUTOMATH

I was lucky enough to get some personal time with N G de Bruijn
when he came to Caltech in 1977 to lecture about
[AUTOMATH]({% post_url 2021-11-03-AUTOMATH %}).
I never actually got to use this system.
Back then, researchers used the nascent Internet (the ARPAnet)
not to download software so much as 
to run software directly on the host computer, 
since most software was not portable.
But Eindhoven University was not on the ARPAnet,
and AUTOMATH was configured to run on 
[a computer we did not have](https://automath.win.tue.nl/archive/pdf/aut034.pdf):

> Until September 1973, the computer was the Electrologica X8, after that
> Burroughs 6700. In both cases the available multiprogranming systems
> required the use of ALGOL 60.

I did however read many of the research reports, including 
the [PhD dissertation](https://automath.win.tue.nl/archive/pdf/aut046.pdf) by LS Jutting,
where he presents his translation 
of Landau's text *Grundlagen der Analysis* (described [last time]({% post_url 2025-10-15-Proofs-trivial %}))
from German into AUTOMATH.
It is no coincidence that many of my papers, from the
[earliest](https://doi.org/10.1016/0167-6423(85)90009-7)
to the [latest](https://doi.org/10.4230/LIPIcs.ITP.2025.18),
copied the idea of formalising a text
and attempting to be faithful to it, if possible line by line.

As an aside, note that while AUTOMATH was a system of dependent types,
it did not embody the 
[Curry–Howard correspondence]({% post_url 2023-08-23-Propositions_as_Types %})
(sometimes wrongly called the Curry–Howard–de Bruijn correspondence).
That correspondence involves having a type theory strong enough
to represent the predicate calculus directly in the form of types.
In AUTOMATH you had to introduce the symbols and inference rules 
of your desired calculus in the form of axioms, much as you do with Isabelle.
In short, AUTOMATH was a [logical framework](https://pure.tue.nl/ws/files/1892191/597622.pdf):

> like a big restaurant that serves all sorts of food: vegetarian, kosher, or anything else the customer wants

De Bruijn
[did not approve](https://pure.tue.nl/ws/portalfiles/portal/4428179/597611.pdf) 
of the increasingly powerful type theories being developed in the 1990s.
AUTOMATH was a weak language, 
a form of λ-calculus including a general product construction just
powerful enough to express the inference rules of a variety of formalisms
and to make simple definitions, again clearly the inspiration for Isabelle.
Isabelle aims to be [*generic*](https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-130.html), like the big AUTOMATH restaurant.
Only these days everybody prefers the same cuisine,
higher-order logic, so Isabelle/HOL has become dominant.
Unfortunately, I last spoke to Dick (as he was known to friends)
when I was putting all my effort into Isabelle/ZF.
He simply loathed set theory and saw mathematics as essentially typed.
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
of a systematic and formal approach to program synthesis.
I had already encountered [intuitionism]({% post_url 2021-11-24-Intuitionism %})
through a course on the philosophy of mathematics at Stanford University,
as I recall taught by [Ian Hacking](https://www.pet.cam.ac.uk/news/professor-ian-macdougall-hacking-1936-2023).
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
Yes: Isabelle began as an implementation of Martin-Löf type theory,
which is [still included]({% post_url 2022-11-30-CTT_in_Isabelle-II %}) 
in the distribution even today as Isabelle/CTT.
But eventually I got tired of what seemed to me a doctrinaire attitude
bordering on a cult of personality around Per Martin-Löf.
The sudden switch to intensional equality 
(everyone was expected to adopt the new approach) wrecked most of my work.
Screw that.

You might ask, what about the calculus of constructions,
which arose during that time and eventually gave us Rocq and Lean?
(Not to mention [LEGO](https://www.lfcs.inf.ed.ac.uk/reports/92/ECS-LFCS-92-211/).)
To me they raised, and continue to raise, the same question I had put to de Bruijn.
Gérard Huet said something like "it is nothing but function application",
which did not convince me.
It's clear that I am being fussy,[^1]
because thousands of people find these formalisms perfectly natural and believable.
But it is also true that the calculus of constructions 
underwent numerous changes over the past four decades.
There seem to be several optional axioms that people sometimes adopt
while attempting to minimise their use, 
like dieters enjoying an occasional croissant.

[^1]: Especially as regards constructive mathematics. To its founders, intuitionism is a philosophy suspicious of language, which it relegates to the purpose of recording and communicating mathematical thoughts. This is the opposite of today's "constructive mathematics", which refers the use of a formalism satisfying certain syntactic properties.

### Decisions, decisions

We can see all this as an example of the choices we make in research.
People were developing new formalisms. This specific fact was the impetus
for making Isabelle generic in the first place.
But we have to choose whether to spend our time developing formalisms 
or instead to choose a fixed formalism and see how far you can push it.
Both are legitimate research goals.

For example, already in 1985, Mike Gordon 
was using higher-order logic [to verify hardware](https://doi.org/10.48456/tr-77).
He was not distracted by the idea that some dependent type theory might work better
for *n*-bit words and the like.
The formalism that he implemented was essentially the same as the 
[simple theory of types](https://plato.stanford.edu/entries/type-theory-church/) 
outlined by Alonzo Church in 1940.
He made verification history using this venerable formalism, 
and John Harrison later found
a clever way to [encode the dimension](https://doi.org/10.1007/11541868_8)
of vector types including words.
Isabelle/HOL also implements Church's simple type theory,
with one extension: [axiomatic type classes]({% post_url 2022-03-02-Type_classes %}).
Isabella users also derive much power from the [locale concept](https://doi.org/10.1007/s10817-019-09537-9), 
a kind of module system that lies outside any particular logic.

During all this time, both Martin-Löf type theory and the calculus of constructions
went through several stages of evolution. It's remarkable how the Lean community,
by running with a certain version of the calculus,
quickly formalised a [vast amount of mathematics](https://leanprover-community.github.io/mathlib-overview.html).

### Pushing higher-order logic to its limit

I felt exceptionally lucky to win 
[funding from the European Research Council](https://cordis.europa.eu/project/id/742178)
for the advanced grant [ALEXANDRIA]({% post_url 2021-12-08-ALEXANDRIA %}).
When I applied, homotopy type theory was still all the rage,
so [the proposal](https://www.cl.cam.ac.uk/~lp15/Grants/Alexandria/Part-B2.pdf)  emphasised Isabelle's specific advantages: its automation,
its huge libraries and the legibility of its proofs.

The team started work with enthusiasm.
Nevertheless, I fully expected that we would hit a wall, 
reaching mathematical material
that could not easily be formalised in higher-order logic.
Too much of Isabelle's analysis library identified topological spaces
with types.
Isabelle's abstract algebra library was old and crufty.
A number of my research colleagues were convinced
that higher-logic was not adequate for serious mathematics.
But Anthony Bordg took up the challenge, leading a subproject
to [formalise Grothendieck schemes](https://doi.org/10.1080/10586458.2022.2062073).

For some reason I had a particular fear of the field extension $F[a]$,
which extends the field $F$ with some $a$ postulated to be 
a root of some polynomial over $F$.
(For example, the field of complex numbers is precisely $\mathbb{R}[i]$, 
where $i$ is postulated to be a root of $x^2+1=0$.)
And yet an early outcome of ALEXANDRIA was[ a proof](https://rdcu.be/cIK3W),
by Paulo Emílio de Vilhena and Martin Baillon,
that every field admits an algebraically closed extension. 
This was the first proof of that theorem in any proof assistant, 
and its proof involves an infinite series of field extensions.

We never hit any wall.
As our group went on to formalise 
[more and more advanced results](https://www.cl.cam.ac.uk/~lp15/Grants/Alexandria/),
such as the [Balog–Szemerédi–Gowers theorem](https://doi.org/10.1145/3573105.3575680),
people stopped saying "you can't formalise mathematics without dependent types"
and switched to saying "dependent types give you nicer proofs".
But they never proved this claim.

Now that dependent type theory has attained maturity 
and has an excellent tool in the form of Lean, shall I go back to dependent types?
I am not tempted. The only aspects of Lean that I envy are its huge community and
the [Blueprint tool](https://github.com/PatrickMassot/leanblueprint).
I hear too many complaints about Lean's performance.
I've heard of too many cases where dependent types played badly 
with intensional equality – I sat through an entire talk on this topic – or otherwise made life difficult. 
Quite a few people have told me that 
the secret of dependent types is knowing when **not** to use them.
And so, to me, they have too much in common 
with Tesla's [Full Self-Driving](https://electrek.co/2025/10/29/tesla-full-self-driving-v14-disappoints-with-hallucinations-brake-stabbing-speeding/).

*Addendum*: somebody commented on Hacker News that higher-order logic is too weak 
(in terms of proof-theoretic strength) to formalise post-WWII mathematics.
This is not quite right.
It is true that higher-order logic is much, much weaker than ZF set theory.
But one of the most striking findings of ALEXANDRIA is that this is no obstacle
to doing advanced mathematics, say to formalise Grothendieck schemes.
Such elaborate towers of definitions do not seem to ascend especially high
in the set-theoretic hierarchy. I can only recall a couple of proofs
([this one](https://doi.org/10.1080/10586458.2021.1980464), 
and [that one](https://rdcu.be/eNVb6)) 
that required strengthening higher-order logic with the ZF axioms 
(which is easily done). 
These were theorems that referred to ZF entities in their very statements.
