---
layout: post
title:  Set theory with types
usemathjax: true 
tags: [AUTOMATH, NG de Bruijn, type theory, set theory]
---
It is known that mathematics is heavily reliant on set theory,
but no one can agree on what set theory is.
Many people today understand that we have a choice between set theory 
and type theory, but they don't know what type theory is either.
Many think that "type theory" refers to 
some sort of dependent type theory, as found in Lean or Agda,
But prior to 1980 or so, "type theory" generally referred 
to higher order logic and related systems.
In 1973, NG de Bruijn wrote a paper called 
["Set Theory with Type Restrictions"](https://automath.win.tue.nl/archive/pdf/aut032.pdf).
His discussion of set theory with types was intended as motivation for the
[AUTOMATH](https://lawrencecpaulson.github.io/tag/AUTOMATH) language,
a dependent type theory.
His thoughts are fascinating and pertinent today.

### Set theory according to de Bruijn

De Bruijn begins "it has been believed throughout this century that set theory 
is the basis of all mathematics." He specifies this as "Cantor set theory",
or Zermelo–Fraenkel (ZF).
And indeed a lot of people continue to insist on this ZF foundation.
Paradoxically, mathematicians (who are the ones with skin in the game)
are generally the least interested in the technicalities of set theory:
actual set theorists are scarce, and the questions they study
seldom have a direct impact on other branches of mathematics.
De Bruijn continues:

> It seems, however that there is a revolt. Some people have begun to dislike the doctrine "everything is a set", just at the moment that educational modernizers have pushed set theory even into kindergarten. It is not unthinkable that this educational innovation is one of the things that make others try to get rid of set theory's grip for absolute power.

I was one of those who was taught a tiny bit of set theory in school, 
when I was something like eight years old.
I don't think it went beyond unions and intersections of two sets.
They didn't even cover [Aronszajn trees](https://en.wikipedia.org/wiki/Aronszajn_tree).
I don't know who was behind this educational trend, 
but intersections and unions are useful concepts even in everyday life.

De Briujn's main objection seemingly comes from the idea that *everything is set*
and the conclusion that any two mathematical objects,
say some triangle and the number 5, 
both being sets, could even have a non-empty intersection.
He also mentions the possibility of writing $x\in x$,
which seems nonsensical and gave us Russell's paradox.
Also objectionable to many are the numerous coding tricks employed,
where the ordered pair $(x,y)$ becomes $\\{\\{x\\},\\{x,y\\}\\}$
and the natural number $n$ becomes $\\{0, \ldots, n-1\\}$.
He continues:

> The natural, intuitive way to think of a set, is to collect things that belong to a class or type given beforehand. In this way one can try to get theories that stay quite close to their interpretations, that exclude $x\in x$ and are yet rich enough for everyday mathematics.

I like this statement, because it is precisely how sets are used in Isabelle/HOL
and how they could be used (but seldom are) in the HOL family of proof assistants.

I have my own objection to Zermelo–Fraenkel set theory:
it is much, much too large for any imaginable purpose.
It bugs me that people are continuing to grasp for even stronger systems,
notably Tarski–Grothendieck set theory. Towards the end of his paper, de Bruijn says

> The world where we have $\mathbb{N}$, $\mathbb{N}^\mathbb{N}$, $\mathbb{N}^{\mathbb{N}^\mathbb{N}}, \ldots$, but where [the union of all those sets] is "inaccessible", is a world most mathematicians will doubtlessly find big enough to live in. For those who want to have a bigger world..., there is a simple way out: they just take a type SET and provide it with Zermelo–Fraenkel axioms. If they want to have the picture complete, they will not find it hard to embed the types $\mathbb{N}$, $\mathbb{N}^\mathbb{N}$,  $\mathbb{N}^{\mathbb{N}^\mathbb{N}}, \ldots$ into a small portion of their paradise.

The context of this remark is that AUTOMATH, by virtue of its built-in
general product, allows 
$\mathbb{N}$, $\mathbb{N}^\mathbb{N}$,  $\mathbb{N}^{\mathbb{N}^\mathbb{N}}, \ldots$ 
to be constructed while having no way to form their "union"
because it provides no way of indexing over types.
I am impressed that de Bruijn already perceived back in 1973 that such a weak system
was strong enough for most mathematics.
I came to this conclusion only recently, 
after a series of formalisation experiments using Isabelle and higher-order logic.
We can easily use the convenient language of sets in higher-order logic,
and we also have the option to "take a type SET and provide it with Zermelo–Fraenkel axioms".

### Sets in higher-order logic

Higher-order logic is descended from the mysterious, 
never-properly-formalised system of
[Principia Mathematica](https://plato.stanford.edu/entries/principia-mathematica/) (PM).
Whitehead and Russell wrote extensively about *classes*,
which were clearly the same thing as typed sets,
though they were never clear about what their type system actually was.
Higher-order logic as [formalised by Church](https://plato.stanford.edu/entries/type-theory-church/)
is PM done right.
A set is nothing but a boolean-valued function, exactly the same thing as a logical predicate, and the phrase "predicate sets"
is fairly common in the [HOL literature](https://rdcu.be/eQa72).
Nevertheless, we think about sets differently 
from how we think about predicates, 
even in the trivial case of unions and intersections.
Often I have looked at an HOL Light proof and seen a prediate $Q(x)$
defined by $\exists y. P(y) \land x = f(y)$,
which is simply the image under the function $f$ of a set.

### The elements of typed set theory

Typed set theory has everything that you would expect, only typed.
As de Bruijn would wish, we exclude $x\in x$:
we can write $x\in A$ only if the types agree.
That means, if $x$ has type $\tau$ then $A$ has type $\tau\,\texttt{set}$, 
which is also the type of the *comprehension* $\\{x.\,P(x)\\}$ 
if $x$ has type $\tau$. Union, intersection and difference combine two sets of the same type in the obvious way.
We have the universal set and therefore set complement
because our sets are typed:
we have the set of all integers, say,
or of all sets of integers, but never the set of *all* sets.
The power set operator 
(which denotes the set of all subsets of its argument)
takes type $\tau\,\texttt{set}$ to type $(\tau\,\texttt{set})\,\texttt{set}$.

The *image* operator is the set-theoretic version of the "apply to all" operator that's called `map` in programming languages 
from [Standard ML](https://doi.org/10.1145/3386336) to Perl, except in LISP where it's called [`MAPCAR`](https://www.gnu.org/software/emacs/manual/html_node/elisp/Mapping-Functions.html); 
their `MAP` does something weird. 
In Isabelle/HOL, the image of a set `A` under the function `f` is written ``f ` A`` and please accept my apologies for a syntax influenced by PM.
But mathematicians often write $f(A)$ for the set of all $f(x)$ 
for $x\in A$, relying on the presence of a capital letter,
which would never do.
The *inverse image* is written ``f -` A`` and denotes the set of all $x$ 
such that $f(x)\in A$.
Both operators are typed in the obvious way.

This brings us to something crucial: the function space
$A\to B$ and its generalisation to the general product, $\prod_{x\in A}\,B(x)$.
The latter was described as a "dependent function space" 
by Robert Constable but is called the "dependent product"
by people who never bothered to read Constable's papers.
It has been around for much longer than dependent type theory.
In typed set theory, we often need to talk about 
the set of all functions that have domain $A$ and codomain $B$,
and occasionally the greater precision 
of the dependent product is helpful.
Both are trivial to define using set comprehension;
in fact, $f\in A\to B$ if and only if $f(A)\subseteq B$.
There is a complication concerning function extensionality,
which I will not discuss here.
Another complication is that the inverse image 
involving a function in $A\to B$ is generally expected to be a
subset of $A$; the Isabelle/HOL inverse image operator does not 
and cannot accomplish that.

Analogously, we need the binary product space $A\times B$. 
Its generalisation to the general sum, $\sum_{x\in A}\,B(x)$
(Constable's "dependent product") is not especially important 
but does have its uses.
Both are again trivial to define using set comprehension, 
and exactly as in type theory, the "non-dependent"
versions $A\to B$ and $A\times B$ are not even defined separately
but are simply degenerate cases of the full versions.

inj_on, surjective, bij_betw

Ideas of cardinality (through eqpollence)

The [hereditarily finite sets]({% post_url 2022-02-23-Hereditarily_Finite %})


Incorporating [full ZF set theory]({% post_url 2022-04-06-ZFC_in_HOL %})
