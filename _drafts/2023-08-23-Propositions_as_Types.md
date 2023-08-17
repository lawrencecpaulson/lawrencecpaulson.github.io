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

### Material implication versus intuitionistic truth

The most natural route to propositions as types runs through *material implication*.
"If it rained then the path will be muddy" sounds like a reasonable instance
of logical implication.
"If Caesar was a chain-smoker then mice kill cats" does not sound reasonable, and yet it is deemed to be true,
at least in classical logic, where $A\to B$ is simply an abbreviation for
$\neg A\lor B$.

Many people have thought that $A\to B$ should hold only if there is some sort 
of connection between $A$ and $B$, and many approaches have been tried.
The most convincing explanation comes from the intuitionists,
specifically, from Heyting's 
[conception of mathematical truth](https://plato.stanford.edu/entries/intuitionistic-logic-development/#ProoInte) itself:

> A proof of an atomic proposition $A$ is given by presenting a mathematical construction in Brouwer’s sense that makes $A$ true.

Propositions as types is already contained in this principle: we identify
each proposition with the set of the mathematical constructions that make it true.
The word *proof* is often used in place of *mathematical construction*, but there is a risk of confusion with proof in a formal calculus; below I use the word *evidence* for brevity.

In the case of implication, we now have

- evidence for $A\to B$ consists of a construction that effectively transforms evidence for $A$ into evidence for $B$

This surely is the sought-for connection between $A$ and $B$.

### Prositions as types in action

A simple proof system for intuitionistic propositional logic has just two axioms:

- axiom K: $\quad A\to(B\to A)$
- axiom S: $\quad(A\to(B\to C))\to ((A\to B)\to(A\to C))$

And it has one inference rule, *modus ponens*, which from $A\to B$ and $A$
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

As a proof system, it sucks. But the propositions as types principle holds: this is essentially the same as the **S**-**K** [system of combinators](https://en.wikipedia.org/wiki/Combinatory_logic). 
Function application corresponds to modus ponens,
The combinators correspond to the axioms (which give their types), 
and the derivation of the identity combinator 
as **SKK** corresponds to the proof above (with $A\to A$ as the type of **I**). The system of combinators also sucks.
It can be used to translate any λ-calculus term into combinators, but the blowup is exponential (as with the proof system).

Now suppose we switch to a [natural deduction](https://plato.stanford.edu/entries/natural-deduction/) system, 
where we can derive
$A\to B$ provided we can prove $B$ from the assumption $A$,
Then we have essentially the same system as the typing rules 
for the [λ-calculus](https://en.wikipedia.org/wiki/Simply_typed_lambda_calculus), where 

$$ \lambda x. b(x) : A\to B$$

provided $b(x):B$ for arbitrary $x:A$.

In a [prior post]({% post_url 2021-11-24-Intuitionism %}) I have described how other logical symbols are rendered as types, specifically in the context of Martin-Löf type theory.
In particular, the type $(\Pi x:A) B(x)$ consists of functions $\lambda x. b(x)$ where $b(x):B(x)$ for all $x:A$. The function space $A\to B$ is the special case where $B$ does not depend on $x$. 

We need additional types, namely $(\Sigma x:A) B(x)$ and $A+B$, 
in order to obtain the full intuitionistic predicate calculus. 
De Bruijn's AUTOMATH [provided the $\Pi$ type alone](https://pure.tue.nl/ws/files/4428179/597611.pdf),
but that was enough to get propositions as types.

### AUTOMATH and irrelevance of proofs

De Bruijn's AUTOMATH, which I have 
[written about earlier]({% post_url 2021-11-03-AUTOMATH %}),
is the first proof checker to actually implement propositions as types.
He did this in the literal sense of providing symbols TYPE and PROP,
which internally were synonymous—at first. However

> One of the forms of the logical double negation axiom, written by means of “prop”, turns into the axiom about Hilbert’s $\epsilon$-operator if we replace prop by type. So if we want to do classical logic and do not want to accept the axiom of choice, we need some distinction.[^1]

[^1]: NG de Bruijn, [A Survey of the Project Automath](https://pure.tue.nl/ws/files/1892191/597622.pdf), in: Seldin, J.P. and Hindley, J.R.,eds., To H.B. Curry: Esaays on Combinatory Logic, Lambda Calculus and Formalism (Academic Press, 1980), 152.

It's not surprising that a primitive DN for double-negation,
mapping $\neg\neg A \to A$, would also map a proof that $A$
was nonempty into $A$ itself.
This is the contrapositive of [Diaconescu's result](https://doi.org/10.2307/2039868)  that
the axiom of choice implies the excluded middle (and therefore DN).

But a more compelling reason to distinguish PROP from TYPE
is *irrelevance of proofs*:

> If $x$ is a real number, then $P(x)$ stands for “proof of $x > 0$”. Now we define “$\log$” (the logarithm) in the context [x : real] [y : P(x)],and if we want to talk about $\log 3$ we have to write $\log(3,p)$, where $p$ is some proof for $3 > 0$. Now the $p$ is relevant, and we have some trouble in saying that $\log(3,p)$ does not depend on $p$. ... Some time and some annoyance can be saved if we extend the language by proclaiming that proofs of one and the same proposition are always definitionally equal.[^2]

[^2]: Ibid, p. 159.

As de Bruijn and others comment, irrelevance of proofs is 
mainly pertinent to classical reasoning. For constructivists, it 
utterly destroys Heyting's conception of intuitionistic truth. 
But even proof assistants that are mostly used  constructively, such as Agda and Coq, provide
[definitionally proof-irrelevant propositions](https://agda.readthedocs.io/en/v2.6.0/language/prop.html).

### Intuitionistic predicate logic, continued

Other logical connectives are easily represented by types.
First, the intuitionistic interpretation:

- evidence for $A\land B$ consists of evidence for $A$ paired with evidence for $B$
- evidence for $\exists x. B(x)$ consists of a specific witnessing value $a$, paired with proof of $B(a)$. 
- evidence for $A\lor B$ consists of evidence for $A$ or evidence for $B$ *along with an indication of which*. (So, we don't have $A\lor\neg A$ when we don't know which one holds.) 

The first two cases are handled by type $(\Sigma x:A) B(x)$,
which consists of pairs $\langle a,b \rangle$ where $a:A$ and $b:B(a)$, generalising the binary Cartesian product. The third case
is handled by type $A+B$, the binary disjoint sum.
The most faithful realisation of this scheme is 
[Martin-Löf type theory](https://lawrencecpaulson.github.io/tag/Martin-Löf_type_theory).

As soon as we impose irrelevance of proofs, this beautiful scheme falls apart. The point of the intuitionist interpretation is to capture the structure of the proofs/evidence; with irrelevance, even
$A+B$ can have at most one element.

Proof assistants do not actually use propositions as types
for the same reason that functional programming languages do not 
actually use the λ-calculus: because something that is beautiful in theory need not have any practical value whatever.
It is still possible to take inspiration from the theory.

### Postscript

Phil Wadler has written a hagiographic but still useful
[article](https://homepages.inf.ed.ac.uk/wadler/papers/propositions-as-types/propositions-as-types.pdf)
about the principle. See in particular the appendix 
for its informative discussion with William Howard, 
who is often credited with discovering the entire idea.
