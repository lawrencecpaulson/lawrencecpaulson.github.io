---
layout: post
title:  "Memories: Edinburgh ML to Standard ML"
usemathjax: true 
tags: [general, Robin Milner, Standard ML]
---

Dave MacQueen (with Robert Harper and John Reppy) has written a 100-page [History of Standard ML](https://doi.org/10.1145/3386336).
Here I offer my brief, personal and utterly subjective impressions of its early days, 
up to the deeply unfortunate schism that created
what was then called [Caml](https://caml.inria.fr).
[Standard ML](https://cs.lmu.edu/~ray/notes/introml/) was a tragic missed opportunity.
But even today there are still several viable 
implementations: [Poly/ML](https://www.polyml.org), [SML/NJ](https://smlnj.org), 
[Moscow ML](https://mosml.org) and [MLton](http://www.mlton.org).
They are substantially compatible because the language was defined by an operational semantics.
It's sad that well into the 21st Century, Computer Science has so regressed that people no longer distinguish between 
a programming language and its implementation.

### Edinburgh ML

The [previous post]({% post_url 2022-09-28-Cambridge_LCF %})
describes how Edinburgh LCF created a new architecture for theorem proving based on a programmable metalanguage, namely ML.
Execution was slow because ML code was translated into Lisp, then implemented.
Gérard Huet modified the system to emit the Lisp in source form and compile it, but it ran no faster.
As he explained, every ML function was represented by
a closure containing a quoted LAMBDA-expression, 
and quoted Lisp S-expressions do not get compiled into machine instructions.

When it was my turn with LCF, I managed to solve this problem
by what is now called [*λ-lifting*](https://en.wikipedia.org/wiki/Lambda_lifting):
by closure bodies were extracted and declared as top-level Lisp functions.
It was also necessary to optimise the treatment of currying.
As a curried function receives its arguments one after another,
it returns a succession of essentially trivial closures;
by compiling additional functions to cover the common cases of 
a curried function being applied to 2, 3, etc., arguments at once,
this wasteful computation could be eliminated.
I don't remember running benchmarks, but Mike Gordon claimed
a speedup by [a factor of twenty](https://www.cl.cam.ac.uk/archive/mjcg/papers/HolHistory.pdf).).

ML was finally usable. But the arrival of Luca Cardelli's 
"ML under UNIX" changed everything. It was a richer and quite
different language with native-code generation and reasonable
performance. It was to prevent ML splintering as Lisp did
that prompted Robin Milner to launch his standardisation effort.

### The fateful meeting

MacQueen's account lists a series of meetings convened by Milner
in order arrive at a consensus for Standard ML.
I no longer have a clear recollection.
The events sketched below may have happened in June 1984 or April 1983.

The delegate sent by Huet to represent Projet Formel was not like that. A quiet and gentle man, he put through his requests and 
they all were forcefully shot down.
I can't remember them all, but I believe they wanted the following:

* "non-linear patterns", i.e. repeating a pattern variable was permitted and denoted an equality test
* a `where` syntax for local declarations
* more generally, to keep the syntax closer to Edinburgh ML

Clearly Dave and Gérard had different visions of ML, and while
Gérard would have fiercely pressed his demands, Dave got his way.
I actually think he was right on all counts: non-linear patterns
only seem useful for a few little examples, while `where` would
not only be redundant but would introduce new scoping issues
exactly when we were striving for a syntax where all scopes
were delimited. But for the sake of harmony it would have been far
better to have conceded some of those points.
As somebody privately remarked, "the French did not get anything they wanted". We know how that ended.

A colleague who once went in my stead to a much later ML meeting 
remarked that it was "hard to hear over the sound of clashing egos".



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

I hear that OCaml is finally approaching the degree of
support for multithreading that Poly/ML achieved about 
15 years ago despite receiving 1% of the resources.
