---
layout: post
title:  "Axiomatic type classes: some history, some examples"
usemathjax: true 
tags: Isabelle, type classes
---

Type classes now play a major role in all the leading proof assistants: Coq, Lean and of course Isabelle/HOL. They have come a long way from their origins in the world of functional programming languages.

Type polymorphism was one of the numerous contributions by Robin Milner and his colleagues when they created Edinburgh LCF, the first modern proof assistant. LCF was designed to be programmable, with its own built-in metalanguage, ML, which became hugely influential in its own right. Among its innovations was a type system that prevented runtime type errors (such as adding a number to a Boolean) while at the same time allowing you to write functions on lists without caring what type of elements were in the list. To compute the length of a list, the elements could have any type (though all of them the same), while to add the elements of a list, they would have to be integers, and the determination of the type was completely automatic.