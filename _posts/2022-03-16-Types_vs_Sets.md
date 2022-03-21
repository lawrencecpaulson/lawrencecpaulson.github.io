---
layout: post
title:  "Types versus sets (and what about categories?)"
usemathjax: true 
tags: general, logic, type theory, set theory
---

A recent Twitter thread brought home to me that there is widespread confusion about what types actually are, even among the most prominent researchers. In particular: *are types the same thing as sets*? At the risk of repeating some of my prior posts, perhaps it's time for a little history about type theory, set theory and their respective roles as foundations of mathematics.

### Type theory in two minutes

Type theory was a response to Russell's and other paradoxes. In its earliest form, in [*Principia Mathematica*](https://plato.stanford.edu/entries/principia-mathematica/), it consisted of Byzantine rules (but bizarrely, no visible syntax) governing the use of variables. It created a type hierarchy in which, at each type level, you could define "classes": what we would call typed sets.
Simplified by [Ramsey](https://plato.stanford.edu/entries/ramsey/), codified by [Church](https://plato.stanford.edu/entries/church/) and later christened "higher-order logic",
[simple type theory](https://plato.stanford.edu/entries/type-theory-church/) again offers a hierarchy of types constructed from an arbitrary but infinite type of individuals, a type of truth values and a function type former.
It's notable that [Church's original paper](https://www.jstor.org/stable/2266170?seq=1#metadata_info_tab_contents) repeatedly refers to possible interpretations of his theory, but never once to sets, although Zermelo–Frankel set theory was well established by 1940 and an interpretation of Church's theory in ZF is trivial: function types denote set-theoretic function spaces.

Moving on two decades, de Bruijn's AUTOMATH introduced what he called a [lambda-typed lambda calculus](https://doi.org/10.1016/S0049-237X(08)70213-1).
He certainly had no set-theoretic interpretation in mind. I knew him well enough to understand that he regarded axiomatic set theory with loathing.
In a [previous post]({% post_url 2021-10-27-formalisms %}) you can read
[his remarks](https://mathshistory.st-andrews.ac.uk/Biographies/De_Bruijn/) about how absurd it is that "a rational number and a set of points in the Euclidean plane... might have been coded in ZF with a coding so crazy that the intersection is *not empty* seems to be ridiculous."

As a computer scientist, I don't find it ridiculous: everything on a computer is encoded as a bit string. Let's pursue the analogy: if we have a directory full of devotional icons in some image format, and another directory full of hardcore porn clips in some video format, it's certainly conceivable that the exact same bit string could appear in both directories. On the other hand, it's easy to see why a mathematician would resent being informed that they *are* working in ZFC whether they like it or not. That *is* ridiculous. Like the intuitionists — but unlike Gödel and others — I regard mathematical objects as existing only in our minds. It's good to know that they can be encoded in ZF, just as it's good that images, videos and music can all be coded as bit strings, but imagine how stupid it would be to insist that images, videos and music *were* nothing but bit strings.

Interest in [type theories](https://plato.stanford.edu/entries/type-theory/) had exploded by the 1980s, including System F (developed independently by Girard and Reynolds),
various versions of Martin-Löf's [intuitionistic type theory](https://royalsocietypublishing.org/doi/10.1098/rsta.1984.0073) and finally the [calculus of constructions](https://doi.org/10.1016/0890-5401(88)90005-3) of Coquand and Huet.
In every case, they were created with no interpretation in mind.
They were justified syntactically, for example via proofs of [strong normalisation](https://repository.upenn.edu/cgi/viewcontent.cgi?article=1600&context=cis_reports).
Models came later.

### An analogy with the $\lambda$-calculus

The syntactic essence of type theories is perhaps best understood through something much simpler:
Church's untyped [$\lambda$-calculus](https://plato.stanford.edu/entries/lambda-calculus/). There are only three kinds of term:

- $x$, $y$, ... (variables)
- $\lambda x.M$ (abstractions)
- $M N$ (combinations)

The most basic rule of the $\lambda$-calculus is *$\beta$-reduction*, which replaces $(\lambda x. M)N$ by $M[N/x]$, which denotes a copy of $M$ in which every free occurrence of $x$ has been replaced by $N$.
Obviously, $\lambda x. M$ should be seen as a sort of function, with $(\lambda x. M)N$ the application of that function to the argument $N$. But there is no obvious model for the $\lambda$-calculus.
There is the degenerate model (where all terms denote the same thing) and there are syntactic models (where $\lambda$-terms essentially denote themselves).

A quick flick through Church's [*Calculi of Lambda Conversion*](https://compcalc.github.io/public/church/church_calculi_1941.pdf) makes it clear that this is mathematics at its most formalistic. Indeed, Church's colleague Haskell Curry became a firm [advocate of the formalist school](https://plato.stanford.edu/entries/formalism-mathematics/#TerForCur) of the foundations of mathematics.
This is the view that mathematics is a mechanical game played with meaningless symbols. Absolutely nothing more.
Many advocates of "constructivism" today seem to be playing this formalistic game; they are not practising intuitionism. 
It is striking to see the [Curry-Howard Correspondence](https://plato.stanford.edu/entries/formalism-mathematics/#CurHowCor) covered in the Stanford Encyclopaedia of Philosophy's entry on [Formalism in the Philosophy of Mathematics](https://plato.stanford.edu/entries/formalism-mathematics/).
It barely gets a mention under [Intuitionism](https://plato.stanford.edu/entries/intuitionism/).

For some time there was scepticism as to whether any interesting model could be found to make sense of such horrors as $(\lambda x. xx)(\lambda x. xx)$.
Dana Scott was ultimately successful,
and in [lovely essay](https://doi.org/10.1016/S0049-237X(08)71262-X) (also available [here](/papers/Scott-Models.pdf)) a imagines a 1930s Master's student formulating a new conception of function in set theory, from which the laws of the $\lambda$-calculus would follow as theorems. 
For mortals it's hard to get an intuitive feel for Scott's models, especially his $D_\infty$ construction.
The main lesson from his work is that the "functions" that we get must be *continuous* in a certain complete partial ordering, an insight that had a profound impact on the field of programming language semantics.

What we can't do is claim that $\lambda$-terms are nothing but the names of certain elements of $D_\infty$ just as 0, $\pi$, $\sqrt 2$, etc. are the names of certain real numbers.
The $\lambda$-calculus existed for decades with no imagined model.


### Some thoughts from scientific colleagues

Thierry Coquand, whose *calculus of constructions* evolved into the type theory now used in Coq and Lean, [stated his view](http://www.cse.chalmers.se/~coquand/v1.pdf) clearly:

> One main theme of this work is the importance of *notations* in mathematics and computer science: new questions were asked and solved only because of the use of AUTOMATH notation, itself a variation of λ-notation introduced by A. Church for representing functions. 

Emphasis his. He states the situation clearly: **types are syntax, not semantics**. 

Regarding this syntactic approach, Dana Scott's [criticism of combinatory logic](/papers/Scott-Models.pdf) (which can be regarded as synonymous with the $\lambda$-calculus for our purposes) seems apt:

> I agree that we can regard Group Theory as an analysis of the structure of bijective functions under composition, Boolean Algebra as an analysis of sets under inclusion, Banach Space Theory as an analysis of functions under convergence of infinite series, etc. etc. But Combinatory Logic? It just does not seem to me to be a sound step in analysis to say: “We now permit our functions to be self-applied.” Just lke that. (page 258)

I emailed Neel Krishnaswami for his views on the matter of types versus sets and he replied as follows (there was more):

> A view from I tend to think of the syntactic rules of type theory as giving a "presentation of an algebraic theory".

> When you look at the models of those type theories, though, they will
(a) usually include sets, (b) and also include lots of things which
are not just sets.  So I tend to see statements like "types are sets"
as being wrong in the same way that "rings are polynomials" is wrong
-- polynomials are certainly form a model of the theory of rings, but
there are many rings which are not polynomials.

> Similarly, for most well-behaved type theories (though not the fancy
HoTT ones), types can be interpreted as sets, but there will usually
be other interpretations as well. (One I care about are the
realisability interpretations, because I want to actually compile
programs to run!)

> In the specific case of dependent types, I most often think of them as
a subsystem of set theory. If you take a dependent type theory, add an
impredicative Prop sort à la Coq, and then add axioms for function
extensionality, quotient types and the axiom of unique choice (i.e.,
every functional relation gives rise to a function), then the result
can be interpreted in any topos, in exactly the same way that
intuitionistic bounded ZF can be interpreted in any topos.

In other words, your types can be interpreted in many weird and wonderful ways.
But we need interpretations that make intuitive sense.
Neel informs me that the original calculus of constructions was modified (during the transition to the [calculus of inductive constructions](https://hal.inria.fr/hal-01094195)) in order to make standard set-theoretic models possible.


### What set theory does and what it doesn't

As already remarked, it's wrong to insist that all mathematicians are working in ZFC. This claim completely misrepresents what set theory tells us. Many people are seriously bothered by definitions such as $(x,y) = \\{\\{x\\}, \\{x,y\\}\\}$ and $n = \\{0, \ldots, n-1\\}$.
I would advise them to relax. The point is not that ordered pairs and natural numbers can (let alone must) be coded in that way, but rather that some truly tremendous things (the notion of ordinals, cardinals, transfinite induction, fantastic combinatorial constructions, gigantic hierarchies of spaces) can be justified axiomatically. 
They can even can be justified conceptually, through the idea of the [cumulative hierarchy of sets](https://doi.org/10.2307/2025204).
The point of set theory is the knowledge that you can get away with ambitious constructions such as those in perfect safety.

Axiomatic set theory also gives us a critical warning: **you risk inconsistency if you assume collections that are too big**. 
So when we say that the carrier of a group is a set, it doesn't have to be specifically a ZF set;
but if we imagine collecting up *all groups* as a single entity, that warning light should flash.
It's dangerous to take the collection of all sets as a single entity, then to build on top of that. And yet, that is precisely what is done in category theory, again and again.
Their very starting point, **Set**, is the category of *all Zermelo–Frankel sets*.
What on Earth do they need all of them for? No one has ever told me.
And category theorists are happy to tell you how much they despise ZF set theory, although they have gobbled it up whole. If you despise Spam, do you wrap it in filo pastry with truffle sauce?

