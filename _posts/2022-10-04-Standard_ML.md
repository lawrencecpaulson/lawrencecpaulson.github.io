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
As he informed me, every ML function was represented by
a closure containing a quoted LAMBDA-expression, 
and the Lisp compiler cannot compile S-expressions into 
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
Mike Gordon reported a speedup by [a factor of twenty](https://www.cl.cam.ac.uk/archive/mjcg/papers/HolHistory.pdf).

ML was finally usable. But the arrival of [Luca Cardelli](http://lucacardelli.name)'s 
"ML under UNIX" changed everything. It was a rich, powerful language 
with native-code generation and good
performance. The danger that ML could splinter as Lisp did
prompted Robin Milner to launch his standardisation effort.

### The fateful meeting

Dave's account lists a series of meetings convened by Robin
in order arrive at a consensus for Standard ML.
I no longer have a clear recollection.
The meeting sketched below may have happened in June 1984 or April 1983.
A colleague who went in my stead to a much later ML meeting 
remarked that it was "hard to hear over the sound of clashing egos".

The delegate sent by Gérard to represent Projet Formel was not like that. Guy Cousineau was quiet and gentle;
he put forward Gérard's proposals and they were all shot down.
I can't remember them all but recall the following:

* "non-linear patterns", i.e. repeating a pattern variable would be permitted and denoted an equality test
* a `where` syntax for local declarations
* more generally, to keep the syntax closer to Edinburgh ML

Clearly Dave and Gérard had different visions of ML, and while
Gérard would have fiercely pressed his demands, 
he wasn't there and Dave got his way.
I actually think he was right on all counts: non-linear patterns
are harder to implement and
only useful for a few little examples, while `where` would
not only be redundant but would introduce new scoping issues
exactly when we were striving for a syntax where all scopes
were delimited. But for the sake of harmony it would have been far
better to have conceded some of those points.
As somebody told me at the time, "the French did not get anything they wanted". We know how that ended.

### Standard ML modules

The other point of contention was [Dave's module proposal](https://www.researchgate.net/publication/2477673_Modules_for_Standard_ML)
with its structures, signatures and functors.
(Some insights by
[Mads Tofte](https://link.springer.com/content/pdf/10.1007/3-540-61628-4_8.pdf).)
Roughly speaking, *structures* (which contain the executable code) correspond to values and 
satisfy *signatures*, which correspond to types and allow a module
to be specified without reference to any implementation.
*Functors* provide a way to define structures that take other structures as parameters.
In 1984, Dave's proposal seemed ludicrously baroque to simple-minded souls like myself and seemingly to the French group too.
As I recall, Caml launched with basic modules that worked with Unix Makefiles to generate `.o` files, which was regarded as a big win.
OCaml modules today [apparently resemble Standard ML's](https://ocaml.org/docs/functors),
if [this guy](https://jozefg.bitbucket.io/posts/2015-01-08-modules.html) is correct.

### Syntactic questions

Peter Landin's [ISWIM](https://doi.org/10.1145/365230.365257) was a fairly arbitrary
syntactic sugaring of the typed λ-calculus,
and Edinburgh ML was substantially based on that.
Some of its syntactic quirks were imposed by its rather basic
precedence parser, which allowed each token to serve only a single purpose. (Mike told me this.) 
In particular, lists were written $[x;y;z]$ and not $[x,y,z]$ 
because the parser would then not cope with $(x,y)$ for ordered pairs; for the same reason, top-level declarations could not be
terminated by a semicolon, so the bizarre double-semicolon was introduced.
I still don't know how they managed to use semicolons to separate
commands as well as list elements.
Weirdest of all, you could actually omit the brackets in $(x,y,z)$,
which may be the real reason why list elements must be separated by semicolons.

The tragedy of the ML schism was that there were no disagreements
about the abstract syntax, semantics, applications or general direction of ML. 
It was all about concrete syntax.
Gérard preferred to stay close to the ISWIM syntax ("even though Landin was English!"), while Dave wanted a logical and robust syntax.

Much of the contention was over the ambiguity inherent in the following declaration:

> let f x = ...

With ISWIM, this defines `f` to be a function taking argument `x`. 
The same declaration in OCaml similarly declares the function `f`,
**unless** `f` is a *datatype constructor*, when instead it declares `x`
by pattern matching.
The syntax is fine for ISWIM because it has no datatype constructors.
Dave was adamant that ML should not overload `let` to such an extent. He was right.

In Standard ML, the two possibilities have different declaration forms:

> fun f x = ...
> 
> val f x = ...

The later form can only bind `x` and is illegal 
unless `f` has been already declared as a constructor. 

Some people really hated `val`, and still insist that Standard ML
syntax is ugly. Concrete syntax is subjective, but for a functional
language, let's just say it's odd that OCaml doesn't have a 
streamlined syntax for (drum roll) *declaring a function* using pattern-matching.
It's odd that the floating-point
operators are `+.`, `-.`, etc., rather than being overloaded, as they are in almost every
other programming language. (Edinburgh ML had no type of reals.)
And remember, some of the quirks of OCaml's syntax are due to the 
limitations of a parsing technology that was already obsolete 50 years ago.


### Into the 1990s

Going into the 1990s, both camps seemed to be going strong.
The [*Definition of Standard ML*](https://smlfamily.github.io/sml90-defn.pdf) was published, 
a substantially formal document presenting an operational semantics for
both static evaluation (e.g. type checking) and execution.
It was revised in 1997,
with significant improvements to references in particular.
Astonishingly, implementors actually used it, achieving compatibility to such an extent that Isabelle could be compiled
with either Standard ML of New Jersey or Poly/ML with only a small
compatibility file to moderate the small differences (mainly about library functions).
I recall hearing implementors saying things like "your proposal
would violate rule 112". 
Implementations appeared, several of them, decent ones.

The main praise I remember of Caml in the 1990s was "it enjoys institutional support" (certainly true) and "it works with UNIX makefiles" (are you kidding me?).
It definitely needed much less memory than SML/NJ.
Its popularity gradually strengthened while the Standard ML community
– Robin having lost interest – drifted leaderless.
The Standard ML Basis Library, so necessary and almost ready in 1997,
somehow did not get released for another six years.

Also in the 1990s, 
John Harrison built HOL Light on top of Caml.
In this he overlooked two sharp disadvantages:

* All Caml strings were mutable, so you could change any constant, even `T` into `F`. It's now fixed in OCaml, but who could overlook such a point 
when your key objective is soundness?
* With no way to save an image, you had to rebuild HOL Light from sources at every launch (even today). Even Edinburgh LCF was a stand-alone executable.

When I was porting HOL Light libraries, I occasionally had to replay
a proof. I would have to launch OCaml, 
first thing in the morning.
I could load the sources of HOL Light in under a minute.
But the full analysis library would not finish loading until after lunch. 
This is a world-beating system?

John chose Caml for its old-fashioned syntax. Such is the power of nostalgia.

### SML/NJ vs Poly/ML

These are the two main implementations. 
Both are impressive in various respects, 
but one gets far more attention to the other.
So let me put in a few words of praise for David Matthews,
another mild and self-effacing personality, who accomplished so much:

* good performance and fantastic debugging tools
* not merely "saving an image", but sharable executable units, either including the Read-Eval-Print loop or standalone;
* support for one hardware architecture after another (including Apple Silicon)
* [support for multi-threading](https://doi.org/10.1145/1708046.1708058), 
(also [here](/papers/Matthews-parallel.pdf))
— they say that OCaml is finally catching up, 
15 years later, thanks to having 100 times as much funding.

A mystery I shall never understand is the difference in performance
between SML/NJ and Poly/ML. The former enjoyed vastly greater funding
and had a strong team of developers compared with DCJM's one-man show.
Benchmarks I ran for my ML book consistently gave SML/NJ a big performance advantage.
But with Isabelle, the strong performer was Poly/ML.
Once David got parallelism working, Poly/ML's advantage was so
overwhelming that we dropped our long-standing policy of supporting
both compilers.

I think Poly/ML's secret ingredient is its garbage collector.
Somehow SML/NJ could beat Poly/ML provided its garbage collector never
ran, as in my little benchmarks. Isabelle spends about 1/3 of its time
in the Poly/ML garbage collector, according to the Poly/ML profiler.
My guess is that with SML/NJ the proportion was far higher.
But I've no way to know for sure.

