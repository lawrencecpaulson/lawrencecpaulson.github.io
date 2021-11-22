---
layout: post
title:  "ALEXANDRIA: Large-Scale Formal Proof for the Working Mathematician"
usemathjax: true 
tags: general, ALEXANDRIA
---

[ALEXANDRIA](https://cordis.europa.eu/project/id/742178) is an ERC Advanced Grant with the aim of making verification technology — originally designed to verify computer systems — useful in the practice of professional mathematics.
[Another project](https://leanprover-community.github.io) with similar aims has developed around [Lean](https://leanprover.github.io), a proof assistant based on essentially the same type theory as Coq.
Without doubt the idea of doing mathematics by machine is in the air. But why?

### Mathematicians are fallible

Let me begin by referencing [my own proposal](https://www.cl.cam.ac.uk/~lp15/Grants/Alexandria/Part-B2.pdf) for ALEXANDRIA. Simply look at the footnotes of Thomas J. Jech's monograph, *The Axiom of Choice*. (North-Holland, 1973), at the bottom of page 118:

![Footnotes from Jech](/images/Jech-118-footnotes.png)

Let's just say that this list of doubtful outcomes doesn't inspire confidence. My opinion is of no importance however; it was the outspoken concerns of Vladimir Voevodsky, a Fields medallist, that really pushed the question of mathematicians' errors out into the open. Anthony Bordg has described the situation in an article,
 [Replication Crisis in Mathematics?](https://doi.org/10.1007/s00283-020-10037-7), that has recently been published in the *Mathematical Intelligencer*. (Full disclosure: Anthony works for ALEXANDRIA.)
 
### A brief history of formalised mathematics

Most of today's proof assistants were created in the 1980s. The first public release of [Isabelle](https://doi.org/10.1007/BF00248324) took place in 1986, around the same time as Mike Gordon's HOL system and the first version of the [Calculus of Constructions](https://doi.org/10.1016%2F0890-5401%2888%2990005-3), which later turned into Coq.

Of these early systems, HOL was the most practical from the start, having been built with the aim of verifying computer hardware. It was immediately put to use verifying significant chip designs. However, this early work required almost nothing that could be called mathematics. None of these early systems even had negative integers.

The impetus for the formalisation of mathematics in the HOL world was the 1994 floating point division bug that forced Intel to recall millions of Pentium chips. John Harrison, a student of Mike Gordon, decided to focus his research on the verification of floating point hardware. John formalised the real numbers and the elements of basic analysis. He also built his own version of the HOL system: [HOL Light](https://www.cl.cam.ac.uk/~jrh13/hol-light/). Another student of Mike's, Joe Hurd, decided to verify probabilistic algorithms. To make that possible, Joe formalised measure and probability theory. John went on to formalise a substantial amount multivariate analysis and prove a number of well-known theorems from a [famous list](https://www.cs.ru.nl/~freek/100/). In the years after 2010, especially when I found myself without grant money, I devoted my time to stealing great chunks of the HOL Light library for Isabelle/HOL.

As you may recall from an [earlier post]({% post_url 2021-11-03-AUTOMATH %}), AUTOMATH was developed specifically to formalise mathematics, starting in the 1960s. Another great effort in the formalisation of mathematics was the Mizar project, which started in 1973. Unfortunately, people in the West tended to overlook scientific developments in Eastern Europe and Mizar did not get the attention it deserved until the 1990s. Mizar introduced a structured language for expressing mathematical arguments, which was the inspiration for Isabelle's Isar language. Mizar also had an ingenious language for expressing and combining mathematical properties, e.g. finite abelian group, which still seems to be unmatched by any other system.

One event that did attract widespread attention was Georges Gonthier's [formalisation of the four colour theorem](https://www.ams.org/notices/200811/tx081101382p.pdf) in Coq. The original proof of this theorem by Appel and Haken was widely disliked, depending as it did upon hundreds of pages of hand calculations and a computer program written in assembly language to check billions of cases. Georges used Coq's internal programming language to run those checks in a fully verified environment. One could argue that this is merely replaced the need to trust one computer program by the need to trust another one, but for most people it settled the question. Georges went on to lead a much larger project, to [formalise the odd order theorem](https://hal.inria.fr/hal-00816699/document), a major result about finite groups.

