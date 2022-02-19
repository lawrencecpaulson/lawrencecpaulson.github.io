---
layout: post
title:  "Axiomatic type classes: some history, some examples"
usemathjax: true 
tags: Isabelle, type classes
---

Type classes now play a major role in all the leading proof assistants: Coq, Lean and of course Isabelle/HOL. They have come a long way from their origins in the world of functional programming languages.
They were mentioned in the previous post, so let's take a closer look.

Type polymorphism was one of the numerous contributions by Robin Milner and his colleagues when they created [Edinburgh LCF](https://doi.org/10.1098/rsta.2014.0234), the first modern proof assistant. LCF was designed to be programmable, with its own built-in metalanguage, ML, which became hugely influential in its own right. Among its innovations was a type system that prevented runtime type errors (such as adding a number to a Boolean) while at the same time allowing you to write functions on lists without caring what type of elements were in the list. To compute the length of a list, the elements could have any type (though all of them the same), while to add the elements of a list, they would have to be integers, and the determination of the type was completely automatic.
Key to this process was (largely hidden) *type variables*, which were attached to all terms.

One fly in the ointment was that many popular functions on lists, such as the membership test, involved equality. There is no mathematically sensible way to test arbitrary computable values for equality.
One "solution" to this conundrum, to ignore the "mathematically sensible" and simply compare the underlying bit patterns, was adopted by OCaml. That was unacceptable to Milner, who introduced a class of *equality* type variables, for types supporting a meaningful equality test. This was the first type class.

[Wadler and Blott](https://dl.acm.org/doi/10.1145/75277.75283) 
1989

Wenzel M. (1997) [Type classes and overloading in higher-order logic](https://doi.org/10.1007/BFb0028402). In: Gunter E.L., Felty A. (eds). TPHOLs 1997.

Paulson, L.C. [Organizing Numerical Theories Using Axiomatic Type Classes](https://doi.org/10.1007/s10817-004-3997-6). J Autom Reasoning 33, 29–49 (2004).

Hölzl J., Immler F., Huffman B. (2013) [Type Classes and Filters for Mathematical Analysis in Isabelle/HOL](https://doi.org/10.1007/978-3-642-39634-2_21). In: Blazy S., Paulin-Mohring C., Pichardie D. (eds) Interactive Theorem Proving. ITP 2013. 

[Haskell-style type classes with Isabelle/Isar](https://isabelle.in.tum.de/dist/Isabelle2021-1/doc/classes.pdf)
