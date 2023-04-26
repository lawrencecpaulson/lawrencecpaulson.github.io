---
layout: post
title:  "The ALEXANDRIA Project: What has been accomplished?"
usemathjax: true 
tags: [general, ALEXANDRIA, Isabelle, Archive of Formal Proofs, HOL Light, Coq]
---

One of the [my first posts]({% post_url 2021-12-08-ALEXANDRIA %})
described [ALEXANDRIA](https://www.cl.cam.ac.uk/~lp15/Grants/Alexandria/),
my [ERC Advanced Grant](https://cordis.europa.eu/project/id/742178) aiming to bring verification technology to professional mathematicians.
This project ends on 30 August 2023 (extended by a year on account of the pandemic),
so it's surely time to update the community on what has been accomplished.
As outlined in the earlier post, our starting point was a growing acceptance
the risk of errors in mathematics and a small body of formal mathematical developments
that had been undertaken in a variety of proof assistance.
We would mainly be using [Isabelle/HOL](https://isabelle.in.tum.de), which had been
designed to be agnostic as regards applications but strongly influenced
by the needs of verification in computer science, not mathematics.
There was a detailed research proposal, as is always required,
but our real strategy was simply to push things as hard as we could
to see what obstacles we would bump into.

### Early days, first formalisations

[The proposal](https://www.cl.cam.ac.uk/~lp15/Grants/Alexandria/Part-B2.pdf) 
called for hiring research mathematicians, who would bring
their knowledge of mathematics as it was practised,
along with their *inexperience* of Isabelle/HOL. Their role would be
to formalise increasingly advanced mathematical material with the twin objectives of
developing formalisation methodologies and identifying deficiencies that might be remedied
by extending Isabelle/HOL somehow. The project started in September 2017.
We hired [Anthony Bordg](https://sites.google.com/site/anthonybordg/) 
and [Angeliki Koutsoukou-Argyraki](https://www.cl.cam.ac.uk/~ak2110/) 
(many thanks to [Mateja Jamnik](https://www.cl.cam.ac.uk/~mj201/) for interviewing with me).
A third postdoc was intended to undertake any necessary Isabelle engineering tasks,
and [Wenda Li](https://www.cst.cam.ac.uk/people/wl302) was hired.

One of the tasks for the first year was simply to reorganise and consolidate
the Isabelle/HOL analysis library, which had mostly been stolen from [HOL Light](https://www.cl.cam.ac.uk/~jrh13/hol-light).
But the team set to work enthusiastically, and already in the first year
they created a number of impressive developments:
* [Projective Geometry](https://www.isa-afp.org/entries/Projective_Geometry.html), including Hessenberg's theorem and Desargues's theorem
* [Quaternions](https://www.isa-afp.org/entries/Quaternions.html) and [Octonions](https://www.isa-afp.org/entries/Octonions.html)
* [Irrational rapidly convergent series](https://www.isa-afp.org/entries/Irrationality_J_Hancl.html), formalising a proof by J. Hančl published in 2002.
* Effectively counting [real](https://www.isa-afp.org/entries/Budan_Fourier.html) and [complex](https://www.isa-afp.org/entries/Count_Complex_Roots.html) roots of polynomials, the Budan-Fourier theorem

Some mathematical proofs rely on calculations, and these can be extremely difficult
to carry out formally. Mathematicians frequently rely on intuition
when calculating limits and integrals, for example.
The root-counting results mentioned above were an early focus of Wenda, 
although he joined in almost every project.
They belong to
[real algebraic geometry](https://en.wikipedia.org/wiki/Real_algebraic_geometry),
and one objective of that work is an efficient, verified decision procedure for deciding
inequalities and inequalities between polynomials.

Angeliki wrote up her reactions to Isabelle/HOL from the perspective of a mathematician in her paper [Formalising Mathematics – in Praxis](https://link.springer.com/article/10.1365/s13291-020-00221-1).

### The next phase: advanced formalisations for *Experimental Mathematics*
 
Around this time, Kevin Buzzard had launched 
[his own project](https://xenaproject.wordpress.com) on formalising mathematics
using Lean. As number theorist, he brought his own perspective to the task.
Earlier researchers had formalised [some huge proofs](https://hal.inria.fr/hal-00816699/document), 
but on the whole they had been working
with simple objects far removed from the sophistication of mathematical practice.
His paper [Formalising perfectoid spaces](https://arxiv.org/abs/1910.12320)
took the viewpoint that before you can even think about proving theorems,
you need to show that you can capture some pretty intricate definitions.

We also understood the need to tackle difficult material, preferably from a wide range
our mathematical subdisciplines. Meanwhile, Angeliki noticed that that the journal
*Experimental Mathematics* had announced a special issue on formalisation. We decided to aim for that, with substantial projects:
 
* [Irrationality and transcendence criteria for infinite series in Isabelle/HOL](https://doi.org/10.1080/10586458.2021.1980465), formalising material from three different research papers: by Erdős and Straus, Hančl, and Hančl and Rucki
* [Formalizing ordinal partition relations using Isabelle/HOL](https://doi.org/10.1080/10586458.2021.1980464), formalising papers by Erdős–Milner, and [Jean Larson](https://people.clas.ufl.edu/jal/) on intricate constructions involving infinitary Ramsey theory.
* [Simple type theory is not too simple: Grothendieck’s schemes without dependent types](https://doi.org/10.1080/10586458.2022.2062073)

We were delighted to see all three papers accepted to the special issue,
taking up fully half of the accepted submissions.

Schemes are a fundamental construction used in number theory.
Buzzard had expressed astonishment that they had not been formalised
in any proof assistant. The problem was simply that a user community 
consisting of computer scientists had never heard of schemes 
and had no idea what they were for. (I still don't.)
Buzzard's [own paper](https://doi.org/10.1080/10586458.2021.1983489) 
in *Experimental Mathematics* described three separate
formalisations of schemes, all using Lean. The first definition had to be discarded
due to technical issues related to Lean's type theory and in particular
the distinction it makes between equality and definitional equality.

Anthony led the formalisation of schemes in Isabelle, in which I took part.
I recall a great many definitions piled one atop the other,
but no technical issues at any point. What's notable is that many well-informed people thought
that schemes could not possibly be formalised in Isabelle/HOL, 
because it lacks dependent types.
The opposite is true: the issues with the first Lean formalisation
were caused by dependent types.

### Advanced library search

In May 2019 we acquired a new postdoc, Yiannos Stathopoulos.


### Machine learning experiments

### Where are we now?


a number of well-known theorems from a [famous list](https://www.cs.ru.nl/~freek/100/).





1. [Szemerédi's Regularity Lemma](https://www.isa-afp.org/entries/Szemeredi_Regularity.html), a landmark result concerning the structure of very large graphs


2. [Combinatorial Design Theory](https://www.isa-afp.org/entries/Design_Theory.html), apparently the first formalisation of block designs, due to Chelsea Edmunds, one of my PhD students

