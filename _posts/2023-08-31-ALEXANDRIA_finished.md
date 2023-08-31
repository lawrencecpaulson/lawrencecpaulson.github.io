---
layout: post
title:  "End of the ALEXANDRIA Project"
usemathjax: true 
tags: [general, ALEXANDRIA, Isabelle, Archive of Formal Proofs,]
---

Today marks the final day of the [ALEXANDRIA](https://www.cl.cam.ac.uk/~lp15/Grants/Alexandria/) project.
I outlined with the brief history of the project
[not long ago]({% post_url 2023-04-27-ALEXANDRIA_outcomes %}).
It is nevertheless right to take a moment to thank
the European Research Council
[for funding it](https://cordis.europa.eu/project/id/742178)
and to state, yet again, what the outcomes were.
Six years on, what have we learned?

### How it started

A milestone for the start of the project is the [*Big Proof* programme](https://www.newton.ac.uk/event/bpr/),
organised by the Newton Institute in Cambridge. Its theme mentioned two then recent
and widely-admired achievements:

> Interactive proof assistants have been used to check complicated mathematical proofs such as those for the Kepler’s conjecture and the Feit-Thompson odd order theorem.

It then refers to

> the challenges of bringing proof technology into mainstream mathematical practice

and it lists specifically

1. Novel pragmatic foundations for representing mathematical knowledge and vernacular inspired by set theory, category theory, and type theory.
2.	Large-scale formal mathematical libraries that capture background knowledge spanning a range of domains

A proposal for a programme 
devoted entirely to [homotopy type theory](https://homotopytypetheory.org) (HoTT)
had been rejected, but people from that community were invited to *Big Proof*.
Dependent type theory, whether HoTT or the already established type theory of Coq,
was widely assumed to be the future of the formalisation of mathematics.
I felt very lucky to get funding for a project involving simple type theory
and  [Isabelle/HOL](https://isabelle.in.tum.de).

During the programme, prior formalisation efforts were criticised as lacking sophistication.
As Kevin Buzzard pointedly noted,
researchers had formalised long proofs about simple objects, but no one had formalised
*even the definitions* of more complicated objects used every day, 
such as Grothendieck schemes.
Much existing work formalised 19th-century mathematics.

These complaints would have to be tackled.


### How it went

I  chronicled the project in my [previous post]({% post_url 2023-04-27-ALEXANDRIA_outcomes %}).
Briefly: we formalised heaps of mathematics. 
We also did groundbreaking work on applications of information retrieval and machine learning
to formalisation.
A longer and more formal account can be found [on arXiv](https://arxiv.org/abs/2305.14407).

### How it ended (formalisation of mathematics)

The sheer amount of new formalised material is impressive (and the quality is also high):

- formalisations of advanced mathematics, including the first ever on topics such as additive combinatorics, combinatorial block designs and ordinal partition theory
- showing that dependent types aren't necessary to have sophisticated objects like Grothendieck schemes or ω-categories
- tens of thousands of lines of more basic but necessary library material, e.g. on metric and topological spaces (imported from HOL Light)
- we formalised advanced work from some of the leading mathematicians of the age: Erdős, Gowers, Roth, Szemerédi

We developed some highly fruitful techniques:

- [locales](https://rdcu.be/dkoEr) work exceptionally well for [structuring complicated hierarchies of definitions](https://www.tandfonline.com/doi/full/10.1080/10586458.2022.2062073)
- "dependent" constructions can typically be formalised as families of (typed) sets

We arrived at some surprising conclusions:

- Formalising even advanced mathematics is largely a matter of perseverance.
- Combining material from different branches of mathematics, say probability theory and graph theory or complex analysis and set theory, works fine.
- Dependent types aren't necessary and probably aren't even advantageous. We aren't the ones fighting our formalism.

To be fair, [astonishing progress](https://xenaproject.wordpress.com/2020/12/05/liquid-tensor-experiment/) has also been made by the [Lean](https://leanprover.github.io) community.
They have been extremely active over the same period 
and formalised [mountains of material](https://leanprover-community.github.io).

**We can safely conclude that proof assistants already offer value to mathematicians.**
Although full formalisation is still not really affordable,
neither is it necessary.
You can forego proving the results that you feel confident about,
focusing your formalisation efforts on the problematical parts.


### How it ended (AI techniques)

The proposal included a lot of speculative ideas about search
and auto completion, in particular by somehow mining
the existing libraries for "proof idioms".
Writing the proposal in 2016, I had no idea how such things could be done.
I was lucky to attract people who were prepared to apply their specialised knowledge.
That's how we got

- the [SErAPIS search engine](https://behemoth.cl.cam.ac.uk/search/), a one-of-a-kind tool to search the libraries even on the basis of abstract mathematical concepts
- a tremendous amount of infrastructure to analyse the Isabelle libraries and extract information
- a string of advanced papers on proof synthesis, auto-formalisation, an Isabelle parallel corpus and more

These projects are still at the research stage, but show great promise!

### Spreading the word

For more detail and links relating to everything described above,
you can visit the [ALEXANDRIA](https://www.cl.cam.ac.uk/~lp15/Grants/Alexandria/)  webpage
or read the [project summary](https://arxiv.org/abs/2305.14407).

The team has worked hard to share the knowledge we discovered. We have written

- 13 journal articles, including half (3 out of 6) of a special issue of *Experimental Mathematics*
- 15 articles in conference proceedings
- 2 refereed chapters in a [*Synthese Library* volume](https://link.springer.com/book/10.1007/978-3-030-15655-8)
- 33 formal proof developments accepted to Isabelle’s [*Archive of Formal Proofs*](https://www.isa-afp.org)

More are forthcoming. 
In addition, we've worked on formalisation projects with about two dozen interns and students,
many of whom have gone on to do PhD research. We've given dozens of talks at variety of venues. We are open to collaboration to take our work forward.

