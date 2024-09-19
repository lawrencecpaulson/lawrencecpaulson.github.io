---
layout: post
title:  Introduction to the λ-calculus
usemathjax: true 
tags: [general, logic, lambda calculus]
---
The [λ-calculus](https://plato.stanford.edu/entries/lambda-calculus/) has had a pervasive impact on computer science.
Most functional programming languages can be viewed as extensions 
of the it, and its impact is even evident 
in modern systems programming languages such as [Rust](https://www.rust-lang.org).
Denotational semantics is normally written using a λ-calculus notation.
Both higher-order logic and dependent type theory are extensions of the λ-calculus.
But it is a mysterious beast, let's take a look.

### Syntax of the λ-calculus

Strictly speaking, syntax is all there is: that's why it is called a calculus. 
The λ-calculus is not about "functions" in any real sense.
Dana Scott has written at length about how hard it is
to relate the λ-calculus to any real mathematical objects.[^1]

[^1]: Dana Scott. [Lambda Calculus: Some Models, Some Philosophy](/papers/Scott-Models.pdf). In: J. Barwise, H. J. Keisler and K. Kunen, eds., *The Kleene Symposium* (North-Holland, 1980), 258

We assume given an infinite set of variables. Then a λ-term is defined inductively
to be one of the following, where $M$ and $N$ are already existing λ-terms:

- $x$, $y$, ... (variables)
- $\lambda x.M$ (abstractions)
- $M N$ (combinations)

XXXXX



The most basic rule of the $\lambda$-calculus is *$\beta$-reduction*, which replaces $(\lambda x. M)N$ by $M[N/x]$, which denotes a copy of $M$ in which every free occurrence of $x$ has been replaced by $N$.
Obviously, $\lambda x. M$ should be seen as a sort of function, with $(\lambda x. M)N$ the application of that function to the argument $N$. But there is no obvious model for the $\lambda$-calculus.
There is the degenerate model (where all terms denote the same thing) and there are syntactic models (where $\lambda$-terms essentially denote themselves).

### XXXXXX

Landin ISWIM (1966), Scheme (1975), LISP (1960)

[^2]: J. Barkley Rosser. [Highlights of the History of the Lambda-Calculus](/papers/Rosser-Lambda-Calculus.pdf).

### XXXX An analogy with the $\lambda$-calculus


A quick flick through Church's [*Calculi of Lambda Conversion*](https://compcalc.github.io/public/church/church_calculi_1941.pdf) makes it clear that this is mathematics at its most formalistic. 