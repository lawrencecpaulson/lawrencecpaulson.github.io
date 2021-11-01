---
layout: post
title:  "Intuitionism and Constructive Logic"
usemathjax: true 
tags: logic, intuitionism, logic
---

### Why Intuitionism?

The best introduction to [intuitionism](https://plato-stanford-edu.ezp.lib.cam.ac.uk/entries/logic-intuitionistic/) is through an example.

*Theorem*: There exist irrational numbers $x$ and $y$ such that $x^y$ is rational.

*Proof*: Let $z = \sqrt 2^{\sqrt 2}$. If $z$ is rational then $x=y=\sqrt2$. 
Otherwise put $x=z$ and $y=\sqrt2$. The conclusion holds because both are irrational while 

$$ x^y = {\biggl(\sqrt2^{\sqrt2}\biggr)}^{\sqrt2}
= \sqrt2^{\sqrt2\times\sqrt2} =\sqrt2^2 = 2. $$

Unfortunately, this proof fails to deliver a specific value for $x$. To an intuitionist, this is no proof. Intuitionism demands that

- a proof of $A\lor B$ consists of a proof of $A$ or a proof of $B$ along with an indication of which. So in particular it rejects the *law of the excluded middle* (LEM), which claims $A\lor \neg A$ while providing no proof.

- a proof of $\exists x. B(x)$ consists of a specific witnessing value $a$ paired with proof of $B(a)$. Refuting $\forall x. \neg B(x)$ does not yield such an $a$.

Continuing the above table for [other connectives](https://plato-stanford-edu.ezp.lib.cam.ac.uk/entries/intuitionistic-logic-development/), we have

- a proof of $A\land B$ consists of a proof of $A$ paired with a proof of $B$

- a proof of $A\to B$ consists of a construction that transforms every proof of $A$ into a proof of $B$

- a proof of $\forall x. B(x) $ consists of a construction that transforms every element $x$ into a proof of $B(a)$

The rejection of LEM originated with [L E J Brouwer](https://plato.stanford.edu/entries/brouwer/), while the interpretation of logical connectives sketched above is largely the work of Arend Heyting. Brouwer accepted LEM for finite constructions, e.g. $n$ is prime even for $n$ inconceivably large, because the decision can be calculated in principle. On the other hand, there is no effective test that our real number $z$ is rational. 
The rejection of LEM implies the rejection of many other familiar laws of Boolean logic, such as $\neg \neg A \to A$ and $\neg(A\land B) \to \neg A \lor \neg B$.
But for computable properties, LEM continues to hold along with those other Boolean laws.
Because of this, proofs of simple properties about computable objects such as integers and lists are not impacted by intuitionism.

### Intuitionistic type theory

Intuitionistic mathematics is clearly linked with computation and this link strengthens once we notice that both $\exists$ and $\land$ involve ordered pairs and $\forall$ and $\to$ involve computable functions.

 $(\exists x:A) B(x)$ and $A\land B$ 
 
 $(\forall x:A) B(x)$ and $A\to B$ 

Martin-Löf type theory; propositions as types

https://plato-stanford-edu.ezp.lib.cam.ac.uk/entries/type-theory-intuitionistic/

### The axiom of choice

the [axiom of choice](https://plato.stanford.edu/entries/mathematics-constructive/#AxioChoi)

[constructive mathematics](https://plato.stanford.edu/entries/mathematics-constructive/)

AC: “A choice function exists in constructive mathematics, because a choice is implied by the very meaning of existence” (Erret Bishop)

Actually provable in Martin-Löf type theory 

If $(\forall x:A) (\exists x:B) C(x,y)$ 

then  $(\exists f:A\to B) (\forall x:A) C(x,f(x))$ 

https://doi-org.ezp.lib.cam.ac.uk/10.1093/comjnl/bxh162

AC implies LEM!

"Hence from the type theoretic point of view AC is a lie. A lie that implies excluded middle ie all propositions are decidable."
