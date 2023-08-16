---
layout: post
title:  "Propositions as types: explained and debunked"
usemathjax: true 
tags: [logic, intuitionism, constructive logic, Martin-Löf type theory, NG de Bruijn]
---

The principle of *propositions as types* is much discussed, but there's a lot of confusion and misinformation.
For example, it is widely believed that propositions as types is the basis of most modern proof assistants; 
even, that it is the necessary foundation 
of any computer implementation of logic.
In fact, propositions as types was found to be unworkable 
as the basis for conducting actual proofs 
the first time it was tried—in the earliest days of the AUTOMATH system.
All of the main proof assistants in use today maintain a clear distinction
between propositions and types.
The principle is nevertheless elegant, beautiful and theoretically fruitful.

### Material implication

The most natural route to propositions as types runs through *material implication*.
"If it rained then the path will be muddy" sounds like a reasonable instance
of logical implication.
"If Caesar was a chain-smoker then mice kill cats" does not sound reasonable, and yet it is deemed to be true,
at least in classical logic, where $A\to B$ is simply an abbreviation for
$\neg A\lor B$.

Many people have thought that $A\to B$ should hold only if there is some sort 
of connection between $A$ and $B$, and many approaches have been tried.
The most convincing explanation comes from the intuitionists,
from their [conception of mathematical truth](https://plato.stanford.edu/entries/intuitionistic-logic-development/#ProoInte) itself:

> A proof of an atomic proposition $A$ is given by presenting a mathematical construction in Brouwer’s sense that makes $A$ true.

Propositions as types is already contained in this principle: we identify
each proposition with the set of the mathematical constructions that make it true.
The word *proof* is often used in place of *mathematical construction*, but there is a risk of confusion with proof in a formal calculus; below I use the word *evidence* for brevity.

In the case of implication, we now have

- evidence for $A\to B$ consists of a construction that transforms evidence for $A$ into evidence for $B$

This surely is the sought-for connection between $A$ and $B$.
And it's enough to see prositions as types in action.
A simple proof system for intuitionistic propositional logic has just two axioms:

- axiom K: $\quad A\to(B\to A)$
- axiom S: $\quad(A\to(B\to C))\to ((A\to B)\to(A\to C))$

And it has one inference rule, modus ponens, which from $A\to B$ and $A$
infers $B$. Here is a proof of $A\to A$:

$$
\begin{align}
  (A\to((D\to A)\to A))\to{} &  \\
  ((A\to (D\to A))\to(A\to A)) & \quad\text{by S}\notag \\[1ex]
  A\to((D\to A)\to A)         & \quad\text{by K} \\
  (A\to (D\to A))\to(A\to A) & \quad\text{by MP, (1), (2)} \\
  A\to (D\to A)                & \quad\text{by K} \\
  A\to A                        & \quad\text{by MP, (3), (4)}
\end{align}
$$

As a proof system, it is terrible. But the propositions as types principle holds: this is essentially the same as the **S**-**K** system of combinators. Function application corresponds to modus ponens,
The combinators correspond to the axioms (which give their types), 
and the derivation of the identity combinator 
as **SKK** corresponds to the proof above (with $A\to A$ as the type of **I**). The system of combinators is equally terrible.

Now if we switch to a natural deduction system, where we can drive
$A\to B$ provided we can prove $B$ from the assumption $A$,
Then we have essentially the same system as the typing rules 
for the λ-calculus, where 

$$ \lambda x. b(x) : A\to B$$

provided $b(x):B$ for arbitrary $x:A$.

In a prior post I have described how other logical symbols are rendered as types, specifically in the context of Martin-Löf type theory.

### AUTOMATH

De Bruijn's AUTOMATH, which I have written about earlier,
is the first proof checker to actually implement propositions as types.
He did this in the literal sense of providing symbols TYPE and PROP,
Which internally were anonymous.	 



[Wadler article](https://homepages.inf.ed.ac.uk/wadler/papers/propositions-as-types/propositions-as-types.pdf)




- evidence for $A\lor B$ consists of evidence for $A$ or evidence for $B$ along with an indication of which. So in particular it rejects the *law of the excluded middle* (LEM), which claims $A\lor \neg A$ while providing no proof.

- evidence for $\exists x. B(x)$ consists of a specific witnessing value $a$ paired with proof of $B(a)$. The formula $\neg (\forall x. \neg B(x))$ is not equivalent: refuting $\forall x. \neg B(x)$ does not yield such an $a$.

Continuing the above table for [other connectives](https://plato.stanford.edu/entries/intuitionistic-logic-development/), we have

- evidence for $A\land B$ consists of evidence for $A$ paired with evidence for $B$

- evidence for $A\to B$ consists of a construction that transforms every proof of $A$ into evidence for $B$

- evidence for $\forall x. B(x) $ consists of a construction that transforms every element $x$ into evidence for $B(a)$

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

> A choice function exists in constructive mathematics, because a choice is *implied by the very meaning of existence*[^1]

[^1]: Errett Bishop and Douglas Bridges, *Constructive Analysis* (Springer, 1985), p. 12. 

Michael Dummett, Professor of Logic at Oxford, wrote (continuing for pages with extended examples) that

> It might at first seem surprising that in a system of constructive mathematics we should adopt as an axiom the Axiom of Choice, which has been looked at askance on constructive grounds. The fact is, however, that the axiom is only dubious under a half-hearted platonistic interpretation of the quantifiers.[^2]

[^2]: Michael Dummett, *Elements of Intuitionism* (Oxford, 1977), 52–54.

Martin-Löf designed his type theory with the aim that AC should be provable and in his landmark [Constructive mathematics and computer programming](http://www.jstor.com/stable/37448) presented a detailed derivation of it as his only example. Briefly, if $(\forall x:A) (\exists y:B) C(x,y)$ then  $(\exists f:A\to B) (\forall x:A) C(x,f(x))$.

Spoiling the party was [Diaconescu's proof](https://doi.org/10.2307/2039868) in 1975 that in a certain category-theoretic setting, the axiom of choice implied LEM and therefore classical logic.
His proof is [reproducible](https://plato.stanford.edu/entries/axiom-choice/#AxiChoLog) in the setting of intuitionistic set theory and seems to have driven today's intuitionists to oppose AC.

It's striking that AC was seen not merely as acceptable but clear by the likes of Bishop, Bridges and Dummett. 
Now it is being rejected and the various arguments against it have the look of post-hoc rationalisations. Of course, the alternative would be to reject intuitionism altogether. This is certainly what mathematicians have done: in my experience, the overwhelming majority of constructive mathematicians are not mathematicians at all. They are computer scientists. They are not shy about declaring that the entire world of mathematics is a house of cards. 

Fermat's last theorem is an interesting point for discussion. It has a giant proof using sophisticated methods, classical reasoning throughout. If a constructive mathematician rejects this proof (and they do), then they believe it is possible that a counterexample might exist. Such a counterexample would simply consist of 
positive integers $a$, $b$, $c$ and $n>2$ such that $a^n+b^n = c^n$. Then a finite calculation would yield an outright contradiction to classical mathematics. 

I think they will be waiting a long time.












