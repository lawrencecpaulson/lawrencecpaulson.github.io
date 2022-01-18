---
layout: post
title:  "Set theory and automated theorem proving"
usemathjax: true 
tags: set theory, resolution, Mizar, Isabelle/ZF
---

[Last week's post]({% post_url 2022-01-26-Set_theory %}) mentioned the mechanisation of some major results of ZF set theory in proof assistants. In fact, the use of automated theorem provers with various forms of set theory goes back a long way. Two stronger set theories have attracted interest: above all, von Neumann–Bernays–Gödel (NBG) and Tarski–Grothendieck (TG).

### 

Hao Wang in 1958: [Toward Mechanical Mathematics](https://doi.org/10.1147/rd.41.0002)

> Results are reported here of a rather successful attempt at proving aU theorems, totalling near 400, of Principia Mathematica which are strictly in the realm of logic, viz., the restricted predicate cal- culus with equality.

> In the more advanced areas of mathematics, we arc not likely to succeed in making the machine imitate the man entirely. Instead of being discouraged by this, however, one should view it as a forceful reason for ex- perimenting with mechanical mathematics. 

> The original aim of the writer was to take mathematical textbooks such as Landau on the number system,:n Hardy-Wright on number theory,~8 Hardy on the calcu- lus,:m Veblen-Young on projective geometry.s? the vol- umes by Bourbaki, as outlines and to make the machine formalize all the proofs (fill in the gaps), The purpose of this paper is to report work done recently on the underlying logic, as a preliminary to that project.



[Quaife](https://doi.org/10.1007/BF00263451)

A clausal version of NGB set theory using the Otter resolution theorem prover. Proved Cantor's theorem and a challenge of that era: that the composition of homomorphisms is a homomorphism. Proofs are semiautomated in that the development is human-guided, although a powerful automatic prover completes each stage.

> The time will come when such crushers as Riemann's hypothesis and
Goldbach's conjecture will be fair game for automated reasoning programs. For those of us who arrange to stick around, endless fun awaits us in the automated development and eventual enrichment of the corpus of mathematics.

