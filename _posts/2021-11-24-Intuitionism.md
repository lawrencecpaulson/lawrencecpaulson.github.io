---
layout: post
title:  "Intuitionism and constructive logic"
usemathjax: true 
tags: logic, intuitionism, constructive logic, axiom of choice
---

Intuitionism was for most of the 20th century a recondite topic in the foundations of mathematics. But in the 1970s, the emergence of constructive type theories, and simultaneously, functional programming languages, brought these topics to the forefront of theoretical computer science. Many practitioners of machine logic (particularly those using [Coq](https://coq.inria.fr)) strive to create constructive (as opposed to classical) proofs.

### Why Intuitionism?

The best introduction to [constructive mathematics](https://plato.stanford.edu/entries/mathematics-constructive/)
 and [intuitionistic logic](https://plato.stanford.edu/entries/logic-intuitionistic/) is through an example.

*Theorem*: There exist irrational numbers $x$ and $y$ such that $x^y$ is rational.

*Proof*: Let $z = \sqrt 2^{\sqrt 2}$. If $z$ is rational then $x=y=\sqrt2$. 
Otherwise put $x=z$ and $y=\sqrt2$. The conclusion holds because both are irrational while 

$$ x^y = {\biggl(\sqrt2^{\sqrt2}\biggr)}^{\sqrt2}
= \sqrt2^{\sqrt2\times\sqrt2} =\sqrt2^2 = 2. $$

Unfortunately, this proof fails to deliver a specific value for $x$. To an intuitionist, this is no proof. Intuitionism demands that

- a proof of $A\lor B$ consists of a proof of $A$ or a proof of $B$ along with an indication of which. So in particular it rejects the *law of the excluded middle* (LEM), which claims $A\lor \neg A$ while providing no proof.

- a proof of $\exists x. B(x)$ consists of a specific witnessing value $a$ paired with proof of $B(a)$. The formula $\neg (\forall x. \neg B(x))$ is not equivalent: refuting $\forall x. \neg B(x)$ does not yield such an $a$.

Continuing the above table for [other connectives](https://plato.stanford.edu/entries/intuitionistic-logic-development/), we have

- a proof of $A\land B$ consists of a proof of $A$ paired with a proof of $B$

- a proof of $A\to B$ consists of a construction that transforms every proof of $A$ into a proof of $B$

- a proof of $\forall x. B(x) $ consists of a construction that transforms every element $x$ into a proof of $B(a)$

The rejection of LEM originated with [L E J Brouwer](https://plato.stanford.edu/entries/brouwer/), while the interpretation of logical connectives sketched above is largely the work of Arend Heyting. Brouwer accepted LEM for finite constructions, e.g. $n$ is prime or $n$ is not prime even for $n$ inconceivably large, because the decision can be calculated *in principle*, even if it's utterly unfeasible. On the other hand, there is no effective test of whether a given real number (like $z$ above) is rational. 

The rejection of LEM implies the rejection of many other familiar laws of Boolean logic, such as $\neg \neg A \to A$ and $\neg(A\land B) \to \neg A \lor \neg B$.
But for computable properties, LEM continues to hold along with those other Boolean laws.
Because of this, proofs of simple properties about computable objects such as integers and lists are not impacted by intuitionism. Coq users will be fully aware that type `bool`, which is the type of booleans, enjoys the LEM and must not be confused with the type `prop` of propositions.

### Intuitionistic type theory

Intuitionistic mathematics is clearly linked with computation and this link strengthens once we notice that both $\exists$ and $\land$ involve ordered pairs and $\forall$ and $\to$ involve computable functions. This suggests a system of types where standard structures also govern these collections of proofs: [propositions as types](https://plato.stanford.edu/entries/type-theory-intuitionistic/#PropType).

- The type $(\Sigma x:A) B(x)$ consists of pairs $\langle a,b \rangle$ where $a:A$ and $b:B(a)$, generalising the binary Cartesian product. It represents proofs of both $(\exists x:A) B(x)$ and $A\land B$.
 
- The type $(\Pi x:A) B(x)$ consists of functions $f$ where $f(a):B(a)$ if $a:A$, generalising the function space. It represents proofs of both $(\forall x:A) B(x)$ and $A\to B$.

- The type $A+B$, the binary disjoint sum, represents proofs of disjunctions.

Continuing in this vein yields Martin-Löf [intuitionistic type theory](https://plato.stanford.edu/entries/type-theory-intuitionistic/), which proved highly influential since its first versions appeared during the 1970s. Today, it is realised in the form of [Agda](https://wiki.portal.chalmers.se/agda/pmwiki.php), which is both a programming language and a proof assistant based on this type theory.


### The axiom of choice

As we have seen in a [previous post]({% post_url 2021-11-10-Axiom_of_Choice%}), 
the [axiom of choice](https://plato.stanford.edu/entries/mathematics-constructive/#AxioChoi)
can be contentious.
It was strongly opposed by a number of prominent mathematicians in the early days, but later gained acceptance even among intuitionists. Errett Bishop, who founded and developed the field of constructive analysis, wrote

> A choice function exists in constructive mathematics, because a choice is *implied by the very meaning of existence*

Michael Dummett, Professor of Logic at Oxford, wrote (continuing for pages with extended examples) that

> It might at first seem surprising that in a system of constructive mathematics we should adopt as an axiom the Axiom of Choice, which has been looked at askance on constructive grounds. The fact is, however, that the axiom is only dubious under a half-hearted platonistic interpretation of the quantifiers.

Martin-Löf designed his type theory with the aim that AC should be provable and in his landmark [Constructive mathematics and computer programming](http://www.jstor.com/stable/37448) presented a detailed derivation of it as his only example. Briefly, if $(\forall x:A) (\exists y:B) C(x,y)$ then  $(\exists f:A\to B) (\forall x:A) C(x,f(x))$.

Spoiling the party was [Diaconescu's proof](https://doi.org/10.2307/2039868) in 1975 that in a certain category-theoretic setting, the axiom of choice implied LEM and therefore classical logic.
His proof is [reproducible](https://plato.stanford.edu/entries/axiom-choice/#AxiChoLog) in the setting of intuitionistic set theory and seems to have driven today's intuitionists to oppose AC.

It's striking that AC was seen not merely as acceptable but clear by the likes of Bishop, Bridges and Dummett. 
Now it is being rejected and the various arguments against it have the look of post-hoc rationalisations. Of course, the alternative would be to reject intuitionism altogether. This is certainly what mathematicians have done: in my experience, the overwhelming majority of constructive mathematicians are not mathematicians at all. They are computer scientists. They are not shy about declaring that the entire world of mathematics is a house of cards. 

Fermat's last theorem is an interesting point for discussion. It has a giant proof using sophisticated methods, classical reasoning throughout. If a constructive mathematician rejects this proof (and they do), then they believe it is possible that a counterexample might exist. Such a counterexample would simply consist of 
positive integers $a$, $b$, $c$ and $n>2$ such that $a^n+b^n = c^n$. Then a finite calculation would yield an outright contradiction to classical mathematics. 

I think they will be waiting a long time.

### Sources for the quotations above

1. Errett Bishop and Douglas Bridges, *Constructive Analysis* (Springer, 1985), p. 12. 

2. Michael Dummett, *Elements of Intuitionism* (Oxford, 1977), 52–54.










