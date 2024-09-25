---
layout: post
title:  Introduction to the λ-calculus
usemathjax: true 
tags: [general, logic, lambda calculus]
---
The [λ-calculus](https://plato.stanford.edu/entries/lambda-calculus/) has had a pervasive impact on computer science.
Most functional programming languages can be viewed as extended λ-calculi.
Its impact is evident even
in modern systems programming languages such as [Rust](https://www.rust-lang.org).
[Polymorphic type checking](http://lucacardelli.name/Papers/BasicTypechecking.pdf) emerged in the context of the typed λ-calculus
and now exists (to some extent) in many modern languages.
Turning to theory, denotational semantics is normally expressed within
a form of λ-calculus.
Both higher-order logic and dependent type theories 
are extensions of the λ-calculus.
But it is a mysterious beast: let's take a look.

$$\newcommand\BV{\mathop{\rm BV}}
\newcommand\FV{\mathop{\rm FV}}
$$

### Syntax of the λ-calculus

Strictly speaking, syntax is all there is: that's why it is called a calculus
as opposed to a theory. 
You can express "functions", but the λ-calculus 
is not about functions in any real sense.
Dana Scott has written at length about how hard it is
to relate the λ-calculus to any natural mathematical objects.[^1]

[^1]: Dana Scott. [Lambda Calculus: Some Models, Some Philosophy](/papers/Scott-Models.pdf). In: J. Barwise, H. J. Keisler and K. Kunen, eds., *The Kleene Symposium* (North-Holland, 1980), 258

A λ-term is defined inductively
to be one of the following, where $M$ and $N$ are already existing λ-terms:

- $x$, $y$, ... are the *variables*, which we assume to be given.
- $(\lambda x.M)$ is the *abstraction* of $M$ over the variable $x$.
- $(M N)$ is the *combination* of $M$ and $N$.

Functions take only one argument, which is sufficient thanks to an observation,
due to Frege and Schönfinkel, that multiple arguments are formally unnecessary:
a technique now known as *[currying](https://en.wikipedia.org/wiki/Currying)* 
(according to one rumour, because Dana Scott was fond of curry).

Parentheses are omitted when they are unnecessary, 
so we can write $\lambda xyz.M$ instead of $(\lambda x.(\lambda y.(\lambda z.M)))$
and $MNPQ$ instead of $(((MN)P)Q)$.
These conventions are particularly suitable for curried functions.
But please note that the traditional function notation $f(x,y,z)$
is absolutely unavailable to us.


### A bit of theory for the λ-calculus

Church had originally intended the λ-calculus to be a form of predicate logic, 
but his conception became one of the 
victims of [Russell's paradox]({% post_url 2024-01-31-Russells_Paradox %}).
(He was finally successful, later, using a *typed* λ-calculus.)
And in the beginning, Church insisted that $\lambda x.M$
should only be allowed if $x$ was actually used in $M$:
he did not like the idea of a function that simply ignored its argument.
Such a restriction is barely imaginable today, 
just as our programming languages no longer insist that a **for**-loop
must do at least one iteration.

To be clear about what it means for a variable to be "used",
we need the notions of bound and free variables.
In $\lambda x.M$, the variable $x$ is *bound*.
Variables in a term that are not bound are said to be *free*,
such as the $y$ in $\lambda x.xy$.
To be precise, let's define the sets $\BV$ and $\FV$:

$$\begin{align*}
    \BV(x)           & =  \emptyset \\
    \BV(\lambda x.M) & =  \BV(M) \cup \{x\} \\
    \BV(M N)         & =  \BV(M) \cup \BV(N)
\end{align*}$$

$$\begin{align*}
    \FV(x)           & =  \{x\} \\
    \FV(\lambda x.M) & =  \FV(M) \backslash \{x\} \\
    \FV(M N)         & =  \FV(M) \cup \FV(N)
\end{align*}$$

Computation steps in the λ-calculus work by substitution.
Specifically, we substitute for **free** occurrences
of some variable $y$ in the term $M$.
That's because a λ-binding introduces a nested scope:
the λ-calculus has given us another basic programming language concept: 
*local variables*.

The operation of substituting $L$ for all
free occurrences of $y$ in $M$ is written $M[L/y]$, and is defined as follows:

* For a variable: $x[L/y]$ is $L$ if $x=y$, otherwise $x$.
* For an abstraction: $(\lambda x.M)[L/y]$ is simply $\lambda x.M$ if $x=y$, otherwise $\lambda x.M[L/y]$
* For a combination: $(M N)[L/y]$ is done recursively as $M[L/y]\; N[L/y]$.

Using these definitions, which are not themselves part of the λ-calculus,
we can define computation: the famous *λ-conversions*.

### Computation in the λ-calculus

XXXXX



The most basic rule of the $\lambda$-calculus is *$\beta$-reduction*, which replaces $(\lambda x. M)N$ by $M[N/x]$, which denotes a copy of $M$ in which every free occurrence of $x$ has been replaced by $N$.
Obviously, $\lambda x. M$ should be seen as a sort of function, with $(\lambda x. M)N$ the application of that function to the argument $N$. But there is no obvious model for the $\lambda$-calculus.
There is the degenerate model (where all terms denote the same thing) and there are syntactic models (where $\lambda$-terms essentially denote themselves).

### XXXXXX

Landin ISWIM (1966), Scheme (1975), LISP (1960)

[^2]: J. Barkley Rosser. [Highlights of the History of the Lambda-Calculus](/papers/Rosser-Lambda-Calculus.pdf).

### XXXX An analogy with the $\lambda$-calculus


A quick flick through Church's [*Calculi of Lambda Conversion*](https://compcalc.github.io/public/church/church_calculi_1941.pdf) makes it clear that this is mathematics at its most formalistic. 