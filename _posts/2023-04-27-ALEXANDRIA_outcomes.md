---
layout: post
title:  "The ALEXANDRIA Project: what has been accomplished?"
usemathjax: true 
tags: [general, ALEXANDRIA, Isabelle, Archive of Formal Proofs, HOL Light, Principia Mathematica]
---

One of the [my first posts]({% post_url 2021-12-08-ALEXANDRIA %})
described [ALEXANDRIA](https://www.cl.cam.ac.uk/~lp15/Grants/Alexandria/),
my [ERC Advanced Grant](https://cordis.europa.eu/project/id/742178) aiming to bring verification technology to professional mathematicians.
This project ends on 31 August 2023 (extended by a year on account of the pandemic),
so it's surely time to update the community on what has been accomplished.
As outlined in the earlier post, our starting point was a growing acceptance
of the prevalence of errors in mathematics, 
along with a small body of formal mathematical developments
that had been undertaken in a variety of proof assistants.
We would mainly be using [Isabelle/HOL](https://isabelle.in.tum.de), which had been
designed to be agnostic as to applications but strongly influenced
by the verification needs of computer scientists, not mathematicians.
There was a detailed [research proposal](https://www.cl.cam.ac.uk/%7Elp15/Grants/Alexandria/Part-B2.pdf), as is always required,
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
A third postdoc was required to undertake any necessary Isabelle engineering,
and [Wenda Li](https://www.cst.cam.ac.uk/people/wl302) was hired.

One of the tasks for the first year was simply to reorganise and consolidate
the Isabelle/HOL analysis library, which had mostly been stolen from [HOL Light](https://www.cl.cam.ac.uk/~jrh13/hol-light).
But we were also supposed to conduct pilot studies.
The team set to work enthusiastically, and already in the first year
they created a number of impressive developments:
* [Projective Geometry](https://www.isa-afp.org/entries/Projective_Geometry.html), including Hessenberg's theorem and Desargues's theorem
* [Quaternions](https://www.isa-afp.org/entries/Quaternions.html) and [Octonions](https://www.isa-afp.org/entries/Octonions.html)
* [Irrational rapidly convergent series](https://www.isa-afp.org/entries/Irrationality_J_Hancl.html), formalising a proof by J. Hančl published in 2002
* Effectively counting [real](https://www.isa-afp.org/entries/Budan_Fourier.html) and [complex](https://www.isa-afp.org/entries/Count_Complex_Roots.html) roots of polynomials, the Budan-Fourier theorem
* The first formal proof that [every field contains an algebraically closed extension](https://rdcu.be/cIK3W)

Some mathematical proofs rely on calculations, and these can be extremely difficult
to carry out formally. Mathematicians frequently rely on intuition
when calculating limits and integrals, for example.
The root-counting results mentioned above were an early focus of Wenda
(who actually joined in almost every task);
they belong to
[real algebraic geometry](https://en.wikipedia.org/wiki/Real_algebraic_geometry),
and one objective of that work is an efficient, verified decision procedure for deciding
equalities and inequalities between polynomials.

Angeliki wrote up her reactions to Isabelle/HOL from the perspective of a mathematician in her paper [Formalising Mathematics – in Praxis](https://link.springer.com/article/10.1365/s13291-020-00221-1).

### The next phase: advanced formalisations for *Experimental Mathematics*
 
Around this time, Kevin Buzzard had launched 
[his own project](https://xenaproject.wordpress.com) on formalising mathematics
using Lean. As a number theorist, he brought his own perspective.
Earlier researchers had formalised huge proofs such as the
[odd order theorem](https://inria.hal.science/hal-00816699/document), 
but on the whole they had been working
with simple objects far removed from the sophistication of mathematical practice.
His paper [Formalising perfectoid spaces](https://arxiv.org/abs/1910.12320)
took the viewpoint that before you can even think about proving theorems,
you need to show that you can capture some pretty intricate *definitions*.

We also understood the need to tackle difficult material, preferably from a wide range
of mathematical subdisciplines. Meanwhile, Angeliki noticed that that the journal
*Experimental Mathematics* had announced a special issue on formalisation. We decided to aim for that, with substantial projects:
 
* [Irrationality and transcendence criteria for infinite series in Isabelle/HOL](https://doi.org/10.1080/10586458.2021.1980465), formalising material from three different research papers: by Erdős and Straus, Hančl, and Hančl and Rucki
* [Formalizing ordinal partition relations using Isabelle/HOL](https://doi.org/10.1080/10586458.2021.1980464), formalising papers by Erdős–Milner, and [Jean Larson](https://people.clas.ufl.edu/jal/) on intricate constructions involving infinitary Ramsey theory.
* [Simple type theory is not too simple: Grothendieck’s schemes without dependent types](https://doi.org/10.1080/10586458.2022.2062073)

We were delighted to see all three papers accepted to the special issue,
taking up fully half of the accepted submissions.

*Schemes* are a fundamental construction used in number theory.
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

ALEXANDRIA refers to the famous 
[library of Alexandria](https://en.wikipedia.org/wiki/Library_of_Alexandria).
Even at the start of the project, Isabelle's Archive of Formal Proofs (AFP)
held a substantial collection. At the moment there are nearly 4 million lines of formal proofs
and [741 separate entries](https://www.isa-afp.org/statistics/).
The proposal included the goal of supporting intelligent search of large proof repositories
and, more speculatively, somehow using the millions of lines of existing proofs
in conjunction with some sort of machine learning technology to assist in generating
new proofs.
In May 2019 we acquired a new postdoc, [Yiannos Stathopoulos](https://www.cl.cam.ac.uk/~yas23/),
who came with the perfect background to tackle these objectives.
After much labour, he and Angeliki produced the 
[SErAPIS search engine](https://behemoth.cl.cam.ac.uk/search/), which searches
both the pre-installed Isabelle libraries and the AFP, 
offering a [great many search strategies](https://www.researchgate.net/publication/341655872_SErAPIS_A_Concept-Oriented_Search_Engine_for_the_Isabelle_Libraries_Based_on_Natural_Language) 
based on anything from simple keywords
to abstract mathematical concepts. It is a complex area and we don't claim to have solved
all the problems, but SErAPIS has quite a few users.
And Yiannos has much more in the pipeline.
 
### Machine learning experiments

The proposal included the task of Intelligent User Support.
How this could be provided wasn't clear from the outset,
but machine learning was already topical and we had millions of lines
of formal proofs to use as a starting point.

The team applied themselves to this task with great vigour,
aided by other members of the Laboratory, 
notably [Sean Holden](https://www.cl.cam.ac.uk/~sbh11/)
and [Albert Jiang](https://albertqjiang.github.io) and by other collaborators outside Cambridge. It is now clear that language models can generate formal proof skeletons
and translate informal proofs into formal languages (*autoformalisation*).
One of the many outstanding efforts is reported in the paper
[Draft, Sketch, and Prove](https://arxiv.org/abs/2210.12283).
Wenda Li led a separate effort to [generate intermediate assertions](https://openreview.net/forum?id=Pzj6fzU6wkj),
for the automated generation of proofs by refinement.
These two papers are a mere foretaste of the tremendous developments now underway.

### More and more formalisations

Once you get the hang of it, the task of formalisation becomes routine.
Then the choice of the next project is a matter of asking whether one of us
understand the mathematics well enough and whether we have sufficient time.
It actually becomes tedious to list all the results proved.
(There is a complete list on the [ALEXANDRIA website](https://www.cl.cam.ac.uk/~lp15/Grants/Alexandria/).)
For example, we formalised [Szemerédi’s Regularity Lemma](https://doi.org/10.1007/s10817-022-09650-2) 
and the [Balog–Szemerédi–Gowers](https://doi.org/10.1145/3573105.3575680) theorem
with the help of [Chelsea Edmonds](https://www.cst.cam.ac.uk/people/cle47), a PhD student.
She also formalised [Lucas's theorem](https://files.sketis.net/Isabelle_Workshop_2020/Isabelle_2020_paper_10.pdf) 
and [Fisher's inequality](https://doi.org/10.4230/LIPIcs.ITP.2022.11),
and has been building the first formalisation
of combinatorial block design theory. 

Many of the projects described above (and others not mentioned) involved
the work of interns who visited the Computer Laboratory, financially supported by the project
and in many cases by [Cambridge Mathematics Placements](https://www.maths.cam.ac.uk/opportunities/careers-for-mathematicians/summer-research-mathematics/cambridge-mathematics-placements-cmp).

Angeliki has pointed out that "we have formalised results by two Fields medalists 
(Roth and Gowers), an Abel prize winner (Szemerédi) 
and of course [Erdős](https://doi.org/10.1016/j.apal.2023.103246) too!"

### Scientific contributions

The most striking and unexpected discovery was that there really seem to be
essentially no limits to what we can formalise.
I was sure we would run into no-go areas, but this never happened.
We aimed for breadth and found that we could handle combinatorics, extremal graph theory,
algebra, analytic number theory and everything else we tried.

One particular scientific question is the need for dependent types.
Anthony has shown that there are 
[arguments in both directions](https://doi.org/10.1145/3573105.3575679),
presenting straightforward techniques for expressing dependent types
within the simply typed language of Isabelle/HOL. 
Meanwhile, issues caused by intensional equality in Lean continued to show
the brittleness of that framework.

Our work also provides further evidence for the thesis that simple type theory
(and therefore, also [Zermelo set theory](https://en.wikipedia.org/wiki/Zermelo_set_theory)) is adequate to formalise mathematics
excepting that part that refers to set theory explicitly.
Since simple type theory is essentially the [formalism of
Whitehead and Russell](/papers/Russells-mathematical-logic.pdf) 
in their [*Principia Mathematica*](https://plato.stanford.edu/entries/principia-mathematica/),
we reach the surprising conclusion
that they were correct: their logic is indeed strong enough
to formalise more or less the *whole of mathematics*.

The field as a whole has advanced tremendously, driven also by the huge
and enthusiastic Lean community. One sign of progress is the
[famous list](https://www.cs.ru.nl/~freek/100/) of 100 rather arbitrary
but notable theorems. It has taken a long time, but now 99 of the 100 theorems
have been formalised in one system or another, with Isabelle and HOL Light
tied at the top with 87. There's only one left: Fermat's Last Theorem.
