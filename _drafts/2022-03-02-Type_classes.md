---
layout: post
title:  "Axiomatic type classes: some history, some examples"
usemathjax: true 
tags: Isabelle, type classes
---

Type classes now play a major role in all the leading proof assistants: Coq, Lean and of course Isabelle/HOL. They have come a long way from their origins in the world of functional programming languages.
They were mentioned in the **previous post**, so let's take a closer look.

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
set out the principles of type class definitions linking axiomatic properties to constant symbols, as well as inheritance from other type classes. A type class could have no axioms (bare overloading) or could extend another type class with additional axioms, so we could introduce < and then graduate to partial orderings, then total orderings. A type could be an instance of a type class, even such apparently tricky cases as the Cartesian product combining two orderings to create another ordering. He addressed the necessary theoretical questions as well as outlining the facilities themselves.

### No, not group theory!

Paulson, L.C. [Organizing Numerical Theories Using Axiomatic Type Classes](https://doi.org/10.1007/s10817-004-3997-6). J Autom Reasoning 33, 29–49 (2004).

Hölzl J., Immler F., Huffman B. (2013) [Type Classes and Filters for Mathematical Analysis in Isabelle/HOL](https://doi.org/10.1007/978-3-642-39634-2_21). In: Blazy S., Paulin-Mohring C., Pichardie D. (eds) Interactive Theorem Proving. ITP 2013. 

Kunčar, O., Popescu, A. A Consistent Foundation for Isabelle/HOL. J Autom Reasoning 62, 531–555 (2019). https://doi.org/10.1007/s10817-018-9454-8
https://www.andreipopescu.uk/pdf/Consistent_Foundation_IsabelleHOL_JAR_2019.pdf

[Haskell-style type classes with Isabelle/Isar](https://isabelle.in.tum.de/dist/Isabelle2021-1/doc/classes.pdf)
