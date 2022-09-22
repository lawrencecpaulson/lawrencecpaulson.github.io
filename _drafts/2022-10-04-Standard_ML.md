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
It's sad that well into the 21st Century, Computer Science has so regressed that people no longer see the point of distinguishing
between a programming language and its implementation.

### Edinburgh ML

The [previous post]({% post_url 2022-09-28-Cambridge_LCF %})
describes how Edinburgh LCF created a distinctive new architecture for theorem proving based on a *programmable metalanguage*, namely ML.
Execution was slow because ML code was translated into Lisp to be interpreted there.
Gérard Huet modified the compiler to emit the Lisp in source form to be compiled, but it ran no faster.
As he explained, every ML function was represented by
a closure containing a quoted LAMBDA-expression, 
and the Lisp compiler does not compile S-expressions into 
executable machine instructions.

When Gérard sent the LCF sources back to me, 
I managed to solve this problem
by what is now called [*λ-lifting*](https://en.wikipedia.org/wiki/Lambda_lifting):
by extracting the closure bodies and declaring them as top-level Lisp functions.
Currying also required optimisation.
As a curried function receives its arguments
it returns a succession of trivial closures;
by compiling additional functions to cover the common case of 
a curried function being applied to multiple arguments at once,
this wasteful computation could be eliminated.
I don't remember running any benchmarks, but I surely did.
Mike Gordon reported a speedup by [a factor of twenty](https://www.cl.cam.ac.uk/archive/mjcg/papers/HolHistory.pdf).).

ML was finally usable. But the arrival of Luca Cardelli's 
"ML under UNIX" changed everything. It was a richer and quite
different language with native-code generation and reasonable
performance. The danger that ML could splinter as Lisp did
prompted Robin Milner to launch his standardisation effort.

### The fateful meeting

MacQueen's account lists a series of meetings convened by Milner
in order arrive at a consensus for Standard ML.
I no longer have a clear recollection.
The meeting sketched below may have happened in June 1984 or April 1983.
A colleague who went in my stead to a much later ML meeting 
remarked that it was "hard to hear over the sound of clashing egos".

The delegate sent by Gérard to represent Projet Formel was not like that. A quiet and gentle man (sorry, cannot recall his name), 
he put forward Gérard's proposals and they were all shot down.
I can't remember them all but recall the following:

* "non-linear patterns", i.e. repeating a pattern variable would be permitted and denoted an equality test
* a `where` syntax for local declarations
* more generally, to keep the syntax closer to Edinburgh ML

Clearly Dave and Gérard had different visions of ML, and while
Gérard would have fiercely pressed his demands, 
he wasn't there and Dave got his way.
I actually think he was right on all counts: non-linear patterns
only seem useful for a few little examples, while `where` would
not only be redundant but would introduce new scoping issues
exactly when we were striving for a syntax where all scopes
were delimited. But for the sake of harmony it would have been far
better to have conceded some of those points.
As somebody told me at the time, "the French did not get anything they wanted". We know how that ended.

### Standard ML modules

The other point of contention was [MacQueen's module proposal](https://www.researchgate.net/publication/2477673_Modules_for_Standard_ML)
with its structures, signatures and functors.
(See this article by
[Mads Tofte](https://link.springer.com/content/pdf/10.1007/3-540-61628-4_8.pdf).)
Roughly speaking, *structures* (which contain the executable code) correspond to values and 
satisfy *signatures*, which correspond to types and allow a module
to be specified without reference to any implementation.
*Functors* provide a way to define structures that take other structures as parameters.
In 1984, MacQueen's proposal seemed ludicrously baroque to simple-minded souls like myself (and I believe, to the French group too).
As I recall, Caml launched with basic modules that worked with Unix Makefiles to generate `.o` filtes, which was regarded as a big win.
OCaml modules today [apparently resemble MacQueen's](https://ocaml.org/docs/functors),
if [this guy](https://jozefg.bitbucket.io/posts/2015-01-08-modules.html) is correct.

### Syntactic questions

The tragedy of the split was that there were no disagreements
about the abstract syntax, semantics, applications or general direction of ML. 
It was all about concrete syntax.

Peter Landin's ISWIM was a fairly arbitrary
syntactic sugaring of the typed λ-calculus.
Edinburgh ML was substantially based on that.
Some of its syntactic quirks were imposed by its simple precedence parser, which allowed each token to serve only a single purpose. 
In particular, lists were written $[x;y;z]$ and not $[x,y,z]$ 
because the parser would then not cope with $(x,y)$ for ordered pairs; for the same reason, top-level declarations could not be
terminated by a semicolon, so the double-semicolon was introduced.
I still don't know how they managed to use semicolons to separate
conmands as well as list elements.

the syntax of Edinburgh ML was restricted because it used a simple precedence parser that allowed each token to serve only a single purpose. 



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



Is a 40MB file huge? Large? (a couple of digital photos or half an hour of music in MP3 format)
