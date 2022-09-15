---
layout: post
title:  "Memories: Edinburgh ML to Standard ML"
usemathjax: true 
tags: [general, Robin Milner, Standard ML]
---

Edinburgh ML

* Huet: Compilation of ML into Lisp but no speed up because of closures
* implementing a sort of lambda-lifting including optimisations for currying, a factor of 20 (?) speed up
* enabling its adoption and other systems (as described in the previous post)

Luca Cardelli

* anecdotes e.g. bouncing Dijkstras and the Dijkstra font?
* "ML under UNIX"

Milner: Standard ML design effort

* A meeting dominated by Dave MacQueen (though I was probably a jerk myself) in which "the French got nothing they wanted"
* I still don't like what they wanted: non-linear patterns, a "where" clause and generally homage to Peter Landin's ISWIM
* MacQueen (and Cardelli?) wanted a logical syntax in which constructs nested well, but which people still find ugly (and MacQueen disliked the "fun" compromise)

Strangely enough, most of the contention was over the ambiguity inherent in the following declaration:

> let f x = ...

With ISWIM, this unambiguously defines the function `f`. That's because ISWIM had no concept of constructor. In OCaml this could define either `x` (if `f` is a constructor) or `f`. If my memory is correct, MacQueen was adamant that we should not overload `let` to such an extent. In Standard ML, the equivalent

> val f x = ...

can only bind `x` (and is an error unless `f` has been declared as a constructor). 

There was no possibility of stopping research into functional languages which would have caused divergences in any case, but it's a tragedy that trying out a different dialect fails the moment you type the simplest function.
It is also hard to argue that the syntax of OCaml is particularly beautiful, certainly not beautiful enough to justify dividing the ML community.
But some people really hated `val`.

I realise the tone of this post is bitter. It's hard to say that anybody did anything wrong, and rather, we should have listened to each other better. On the Standard ML side, a few people took stubborn positions and never relinquished them. On the other hand, the standardisation effort yielded a convincing demonstration of operational semantics applied to a real programming language, and at one point there were at least four independent and perfectly usable implementations of Standard ML (as well as a couple of prototype or reference implementations).


And so much else is ridiculous:

* John Harrison built HOL Light on top of OCaml (apparently for its syntax alone) at a time when all OCaml strings were mutable, so you could trivially break soundness by getting hold of the actual string representing truth, namely `T`, and replace it by `F`. John was also committed to an ML platform that did not allow you to save a core image, so you had to rebuild HOL Light every single time you launched it.
* the syntax of Edinburgh ML was restricted because it used a simple precedence parser that allowed each token to serve only a single purpose. So if anybody asks why OCaml separates list elements by semicolons rather than commas and terminates declarations by double semicolons rather than the conventional semicolon, it's because of the limitations of a parsing technology that was already obsolete 50 years ago.
