---
layout: post
title:  "Axiomatic type classes: some history, some examples"
usemathjax: true 
tags: Isabelle, type classes
---

Type classes now play a major role in all the leading proof assistants: Coq, Lean and of course Isabelle/HOL. They have come a long way from their origins in the world of functional programming languages.
They were mentioned in the [previous post]{% post_url 2022-02-23-Hereditarily_Finite %}, so let's take a closer look.

### Robin Milner and polymorphic type checking

Type polymorphism was one of the numerous contributions by Robin Milner and his colleagues when they created [Edinburgh LCF](https://doi.org/10.1098/rsta.2014.0234), the first modern proof assistant. LCF was designed to be programmable, with its own built-in metalanguage, ML, which became hugely influential in its own right. Among its innovations was a type system that prevented runtime type errors (such as adding a number to a Boolean) while at the same time allowing you to write functions on lists without caring what type of elements were in the list. 
Milner was able to [prove](https://doi.org/10.1016/0022-0000(78)90014-4) (alternative [source](https://homepages.inf.ed.ac.uk/wadler/papers/papers-we-love/milner-type-polymorphism.pdf)) that his notion of type inference prevented runtime errors while assigning to every program a *principal* (most general) type.
To compute the length of a list, the elements could have any type (though all the same type), while to add the elements of a list, they would have to be integers, and the determination of the type was completely automatic.
Key to this process was (largely hidden) *type variables*, which were attached to all terms.

### Type classes and functional programming

One fly in the ointment was that many popular functions on lists, such as the membership test, involved equality. There is no mathematically meaningful way to test arbitrary computable values (such as functions or abstract types) for equality.
The original ML ignored this problem, simply testing equality of the internal representations.
But when the time came to design the next generation language, [Standard ML](https://doi.org/10.1145/3386336), Milner introduced a class of *equality* type variables: for types supporting a meaningful equality test. This was the first type class, identifying those types for which the equality operation was permitted.

Many observers found it ugly to make a special case of equality. The [OCaml](https://ocaml.org) language continued the former treatment of equality.
However, in 1989 [Wadler and Blott](https://dl.acm.org/doi/10.1145/75277.75283) proposed instead to generalise equality types to any collection of desired operations (sometimes called a *signature*).
They gave as examples the overloading of arithmetic operators and the treatment of equality types. Another natural example is types equipped with a total ordering, a type class that could be the basis of polymorphic sorting functions.
Although their suggestion was simply for a programming language feature
––it was incorporated into [Haskell](https://www.haskell.org)––they saw further:

> It is natural to think of adding assertions to the class declaration, specifying properties that each instance must satisfy... It is valid for any proof to rely on these properties, so long as one proves that they hold for each instance declaration. Here the assertions have simply been written as comments; a more sophisticated system could perhaps verify or use such assertions.

### Type classes and Isabelle/HOL

Isabelle had Milner style polymorphism from the beginning, but it wasn't available for defining logics: some mechanism was needed to distinguish between a many sorted first-order logic and higher order logic. [Tobias Nipkow](https://www21.in.tum.de/~nipkow/) recognised that type classes could be this mechanism, governing whether quantification was permitted over truth values and functions. Doing this right required a partial ordering on type classes, so-called order-sorted polymorphism, and his paper (with Prehofer) "[Type checking type classes](https://doi.org/10.1145/158511.158698)" appeared in 1993.

It then fell to [Wenzel](https://sketis.net) to realise Wadler and Blott's remark quoted above.
His 1997 [Type classes and overloading in higher-order logic](https://doi.org/10.1007/BFb0028402)
set out the principles of type class definitions linking axiomatic properties to constant symbols, as well as inheritance from other type classes. A type class could have no axioms (bare overloading) or could extend another type class with additional axioms. One could introduce $\le$ and then graduate to partial orderings, then total orderings. A type could be an instance of a type class, even such apparently tricky cases as the Cartesian product combining two orderings to create another ordering (and even that it would be a total ordering provided both of the constituent orderings were also total). He addressed the necessary theoretical questions as well as outlining the facilities themselves.

### Organising numbers, not groups or rings

If I recall correctly, languished largely unused for quite some time. In particular, many proof assistants including Isabelle/HOL then and HOL Light even now suffered from massive duplication of material for the various numeric types of natural numbers, integers, rationals, real and complex numbers: the same proofs of innumerable basic facts that all depended on just a few common properties.

In the early 2000s, I [tackled this duplication](https://doi.org/10.1007/s10817-004-3997-6) (alternative [source](https://www.cl.cam.ac.uk/~lp15/papers/Reports/TypeClasses.pdf)) by introducing a series of type classes with algebraic names like semiring, ring, ordered_ring, field, ordered_field. (Since that time, the menagerie of algebraic type classes has proliferated hugely.)
The paper is a readable but outdated overview of axiomatic type classes.

It's essential to understand that a type class such as `ring`, though including the ring axioms, will be of no value in reasoning about abstract rings. Type classes constrain types, and the carrier of any interesting group or ring is a *set*, unlikely to be formalisable as a type. Believe me, we all knew this, even in the 1990s. When we show that the integers are a ring we do not imagine that the integers are an *interesting* ring; we are simply making a statement about the behaviour of the operators $+$ and $\times$.

Type classes were introduced to Coq in 2008. Clearly Coq's richer type system makes its type classes more powerful than Isabelle's, but it's worth noting that the tremendous group theory developments done in Coq were based on a [formalisation of finite groups](https://doi.org/10.1007/978-3-540-74591-4_8) where the group carriers were indeed sets, represented by lists.

### Recent history

John Harrison's [formalisation of Euclidean spaces](https://doi.org/10.1007/s10817-012-9250-9) (also [here](https://www.cl.cam.ac.uk/~jrh13/papers/neworleans.html)) in HOL Light covered a vast body of material, but unfortunately restricted to $\mathbb{R}^n$ for results that were typically much more general.
Hölzl et al. [showed how type classes](https://doi.org/10.1007/978-3-642-39634-2_21) could be used to add flexibility to formalised analysis, with results now proved for topological spaces, metric spaces, normed vector spaces and euclidean spaces. So type classes go beyond mere numerical reasoning.
Unfortunately, the carriers of many spaces cannot be formalised as types, so a more general treatment of analysis in terms of sets is necessary.
A start has been made for metric and topological spaces, also in HOL Light, but there is much more to be done.

During the 1990s, the Isabelle developers took the view that definitions were the user's responsibility, not even bothering to check whether definitions were circular. Recently, many people have come to the view that a proof assistant should provide a 100% guarantee against definitions introducing formal inconsistencies. 
Responding to some examples where circular definitions could be made through trickery involving type classes, Kunčar and Popescu [established sufficient conditions](https://doi.org/10.1007/s10817-018-9454-8)
(alternative [source](https://www.andreipopescu.uk/pdf/Consistent_Foundation_IsabelleHOL_JAR_2019.pdf)) for ensuring the non-circularity of any system of overloaded definitions and type definitions. These checks have been incorporated into Isabelle/HOL since 2016.
But you still need to take responsibility for your definitions: if they are wrong, all your conclusions are worthless.

For a modern tutorial on type classes, see Haftmann's ["Haskell-style type classes with Isabelle/Isar"](https://isabelle.in.tum.de/dist/Isabelle2021-1/doc/classes.pdf).
It's distributed with Isabelle and is immediately available from the documentation panel of your jEdit session.

