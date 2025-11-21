---
layout: post
title:  Set theory with types
usemathjax: true 
tags: [AUTOMATH, NG de Bruijn, type theory, set theory]
---
It is known that mathematics is heavily reliant on set theory,
but no one can agree on what set theory is.
Many people today understand that we have 
a [choice between set theory and type theory]({% post_url 2022-03-16-Types_vs_Sets %}), 
but they don't know what type theory is either.
Many think that type theory refers to 
some sort of dependent type theory, as found in Lean or Agda,
while everything else is set theory.
But prior to 1980 or so, "type theory" generally referred 
to higher-order logic and related systems.
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
[Roger Needham](https://www.cam.ac.uk/news/professor-roger-needham-1935-2003) 
liked to describe unrealistic expectations as 
"an elaborate description of the empty set";
people need to be able to understand such remarks.

De Briujn's chief objection to ZF set theory comes from "the weird idea that *everything is set*":

> In our mathematical culture we have learned to keep things apart.
> If we have a rational number and a set of points in the Euclidean plane, we cannot even
> imagine what it means to form the intersection. The idea that both might have been coded
> in ZF with a coding so crazy that the intersection is *not empty* seems to be ridiculous.[^1]

[^1]: This remark comes from a related paper by de Bruijn: [On the roles of types in mathematics](https://research.tue.nl/en/publications/on-the-roles-of-types-in-mathematics/)

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
though PM was never explicit about what its type system actually was.
Higher-order logic as [formalised by Church](https://plato.stanford.edu/entries/type-theory-church/)
is PM done right.
A set is nothing but a boolean-valued function, exactly the same thing as a logical predicate, and the phrase "predicate sets"
is fairly common in the [literature of the HOL proof assistant](https://rdcu.be/eQa72).
Nevertheless, we think about sets and predicates differently, 
even in the trivial case of unions and intersections.
Often I have looked at an HOL Light proof and seen a prediate $Q(x)$
defined by $\exists y. P(y) \land x = f(y)$,
which is simply the image under the function $f$ of a set.

Early versions of Isabelle/HOL maintained separate types for sets and predicates.
At some point about 20 years ago, somebody had the idea of abolishing the distinction,
presumably to avoid some duplication. This change persisted for a couple of releases
before being laboriously reversed. Sets and predicates are simply not the same.

### The elements of typed set theory

Typed set theory has everything that you would expect, only typed.
As de Bruijn would wish, it excludes $x\in x$:
you can write $x\in A$ only if the types agree.
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
But mathematicians write $f(A)$ for the set of all $f(x)$ 
for $x\in A$, treating $A$ as a set because of its capital letter,
which would never do.
The *inverse image* is written ``f -` A`` and denotes the set of all $x$ 
such that $f(x)\in A$.
Both operators are typed in the obvious way.

This brings us to something crucial: the function space
$A\to B$ and its generalisation to the indexed product, $\prod_{x\in A}\,B(x)$.
The latter was called a "dependent function space" 
by Robert Constable but is called the "dependent product"
by people who never bothered to read Constable's papers.
It has been around for more than a century
due to its close association with the axiom of choice,
which states that $\prod_{x\in A}\,B(x)$ is nonempty provided
$B(x)$ is nonempty for all $x\in A$.
In typed set theory, we often need to talk about 
the set of all functions that have domain $A$ and codomain $B$,
and occasionally the greater precision of the indexed product is helpful.
Both are trivial to define using set comprehension;
in fact, $f\in A\to B$ if and only if $f(A)\subseteq B$.
There is a complication concerning function extensionality,
which I will not discuss here.
Another complication is that the inverse image 
involving a function in $A\to B$ is generally expected to be a
subset of $A$; the Isabelle/HOL inverse image operator does not 
and cannot accomplish that.

Analogously, we need the binary product space $A\times B$. 
Its generalisation $\sum_{x\in A}\,B(x)$,
the indexed sum (Constable's "dependent product"), 
is not especially important but has its uses.
Both are again trivial to define using set comprehension.
As in type theory, the "non-dependent"
versions $A\to B$ and $A\times B$ are not even defined separately
but are simply degenerate cases of the full versions
when $B$ does not depend on $x$.

If $f\in A\to B$ then we may want to know whether $f$ is an *injective* on the set $A$ or
whether it is *surjective* (the image $f(A)$ equals $B$).
If $f$ is both then it is a *bijection* between the two sets.
These properties also can give us an indication of the relative sizes of $A$ and $B$:
if $f$ is an injection then $A$ is "smaller" than $B$ 
(written $A\precsim B$ or $A\prec B$ if $A$ is strictly smaller). 
Then we can also talk about *countable* sets.
Exhibiting a bijection between two sets shows that they are *equinumerous* 
and is often the easiest way 
to show that they have the same *cardinality*.
In the basic Isabelle/HOL library, the cardinality function for sets
returns a natural number, so it is only useful for finite sets,
but we can do much better if necessary.

### Incorporating all of Zermelo–Fraenkel set theory

Typed set theory, as sketched above, meets de Bruijn's desiderata.
It is also simpler and more intuitive than AUTOMATH,
and can express vast swathes of mathematics in a natural manner.
But, for better or worse, set-theoretic notions such as transfinite ordinals and cardinals
sometimes [pop up in odd places](https://rdcu.be/cWkY5).
ZF set theory becomes inescapable once its very language 
finds its way into your theorem statement.
I have [already written]({% post_url 2022-04-06-ZFC_in_HOL %}) on how to incorporate
ZF set theory into higher-order logic. It is done exactly as de Bruijn
suggested: by postulating a type of ZF sets and equipping it with all the ZF axioms.

A possible annoyance with this approach is ending up with two separate mathematical worlds:

* the higher-order logic world, painstakingly constructed by more than 100 Isabelle/HOL theories

* the vast ZF world, with only eight Isabelle/HOL theories mainly concerned with ordinal and cardinal numbers, everything else existing only as possible consequences of the ZF axioms

As I [described earlier]({% post_url 2022-04-06-ZFC_in_HOL %}), 
the AFP entry `ZFC_in_HOL` connects the two worlds using Isabelle's type class system.
It sets up a family of embeddings from the standard Isabelle/HOL type constructors
to suitable ZF analogues. ZF thereby gets things like 
the set of real numbers for free: we don't have to construct it all over again.
Summarising the earlier blog post, it's done by

* defining the type class `embeddable` of types that can be embedded into the ZF universe
* defining the type class `small` of types that can be embedded into some ZF set

An Isabelle library defines a type class of countable types
and proves many basic types to be countable or to preserve countability.
These include `nat`  (the natural numbers) and `rat` (the rational numbers). 
Moreover, `countable` is a subclass of `small`, which is a subclass of `embeddable`. 
It follows immediately that all those basic types are small.
Moreover, the function space type constructor preserves smallness.
To show that there is a ZF set corresponding to the Isabelle/HOL type `real`,
we need to show that `real` belongs to `small`, 
which is trivial because each real number is represented by a set of functions
from `nat` to `rat`. 

### A simpler way to get some set theory

De Bruijn objects to the principle that "everything is a set", 
but it comes in handy when you are trying to define spaces.
Given any two sets $A$ and $B$, you can always construct the things mentioned above: 
unions and intersections, the product $A\times B$, function space $A\to B$, 
also the disjoint sum $A+B$, enumerations like $\\{A,B\\}$,
the indexed sum and product and much more.
This sort of flexibility comes in handy when defining the semantics
of a programming language, where variables can range over a variety of types.
It also comes in handy when talking about finite state machines,
where different ways of combining machines require analogous ways 
of combining sets of machine states.
If you are in a typed world like higher-order logic, 
you may be tempted to reduce everything to natural numbers, 
using embeddings of some sort to get the necessary structures. But that sucks.

The [*hereditarily finite sets*](https://www.isa-afp.org/entries/HereditarilyFinite.html) (type `hf`)
give us everything that ZF does, with the big exception of infinite sets.
Hereditarily finite sets are finite all the way down.
Finitary constructions such as integers, rationals, 
and the obvious data structures are easily represented.
But we have no real numbers (only floating point) 
and cannot use infinite equivalence classes either.
Still, `hf` has everything we need for modelling possible data in a programming language 
or state spaces in the world of [finite state machines](https://arxiv.org/pdf/1505.01662).

The set of all hereditarily finite sets is countable, 
and they [map naturally to the natural numbers]({% post_url 2022-02-23-Hereditarily_Finite %}).
That means, if you use type `hf`, you are essentially using the natural numbers,
but the structural embeddings are hidden 
and you get to use those beloved set-theoretic constructions.
And `hf` is definable in higher-order logic without additional axioms.