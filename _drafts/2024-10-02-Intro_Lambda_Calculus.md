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

### Syntax of the λ-calculus

Strictly speaking, syntax is all there is: that's why it is called a **calculus**
as opposed to a **theory**. 
You can express "functions", but the λ-calculus 
is not about functions in any real sense.
Dana Scott has written at length about how hard it is
to relate the λ-calculus to any natural mathematical objects,
especially because a function can be applied to itself.[^1]

[^1]: Dana Scott. [Lambda Calculus: Some Models, Some Philosophy](/papers/Scott-Models.pdf). In: J. Barwise, H. J. Keisler and K. Kunen, eds., *The Kleene Symposium* (North-Holland, 1980), 258

A *λ-term* is defined inductively
to be one of the following, where $M$ and $N$ are already existing λ-terms:

- $x$, $y$, ... are the *variables*, which we assume to be given.
- $(\lambda x.M)$ is the *abstraction* of $M$ over the variable $x$.
- $(M N)$ is the *combination* of $M$ and $N$.

This may seem too simple.
*Where are the basic values like numbers and booleans?*
Believe it or not, they can be encoded, 
even advanced data structures such as infinite lists.
*Why can functions take only one argument?*
Frege and Schönfinkel had both noticed that 
multiple arguments are formally unnecessary:
a technique now known as *[currying](https://en.wikipedia.org/wiki/Currying)* 
(according to one rumour, because Dana Scott was fond of curry).
Our tiny formal calculus is sufficient to encode the full world 
of computation.

Some parentheses can be omitted.
We can write $\lambda xyz.M$ instead of $(\lambda x.(\lambda y.(\lambda z.M)))$
and $MNPQ$ instead of $(((MN)P)Q)$.
We can write $\lambda x.MN$ instead of $\lambda x.(MN)$.

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
must perform at least one iteration.

What does it mean for a variable to be "used"?
For that, we need the notions of bound and free variables.
In $\lambda x.M$, all occurrences of the variable $x$ are *bound*.
Variable occurrences that are not bound are said to be *free*,
such as the $y$ in $\lambda x.xy$ or even the first $x$ in $x(\lambda x.x)$.
To be precise, let's define the sets BV and FV:

$$\newcommand\BV{\mathop{\rm BV}}
\newcommand\FV{\mathop{\rm FV}}
\begin{align*}
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
free occurrences of $y$ in $M$ is written $M[L/y]$ and is defined as follows:

* For a variable: $x[L/y]$ is $L$ if $x=y$, otherwise $x$.
* For an abstraction: $(\lambda x.M)[L/y]$ is simply $\lambda x.M$ if $x=y$, otherwise $\lambda x.M[L/y]$
* For a combination: $(M N)[L/y]$ is done recursively as $M[L/y]\; N[L/y]$.

Using the theoretical notions defined above, 
which are not themselves part of the λ-calculus,
we can define computation: the famous *λ-conversions*.

### Computation in the λ-calculus

The 1930s saw growing interest in the concept of a computable function.
Alan Turing's paper on computable numbers appeared in 1936 and 
Church was working on related questions at the same time.
The [Church-Turing thesis](https://plato.stanford.edu/entries/church-turing/), 
which identifies the computable functions
as those computable using a Turing machine, or (equivalently!!) the λ-calculus, dates from that year.

However, Church's early writings do not stress computability.
Here is an excerpt from the introduction to his monograph on the λ-calculus.

> A *function* is a rule of correspondence by which when
> anything is given (as *argument*) another thing (the *value* of the
> function for that argument) may be obtained. That is, a function
> is an operation which may be applied on one thing (the
> argument) to yield another thing (the value of the function). 
> ... In particular it is not excluded that one of the elements of
> the range of arguments of a function *f* should be the function
> *f* itself. [^2]

[^2]: Alonzo Church. *[The Calculi of Lambda-Conversion](https://compcalc.github.io/public/church/church_calculi_1941.pdf)*. Princeton University Press, 1941


The most basic rule of the $\lambda$-calculus is *β-reduction*, which replaces $(\lambda x. M)N$ by $M[N/x]$: a copy of $M$ in which every free occurrence of $x$ has been replaced by $N$.
It is only valid provided that substitution does not *capture* 
a free variable within a λ-binding, for which 
$\BV(M)\cap\FV(N)=\emptyset$ is a sufficient condition. 

Here are two examples of β-reduction:
* $(\lambda x.(xx))(yz) \to_\beta ((yz)(yz))$
* $((\lambda z.(zy))(\lambda x.x)) \to_\beta ((\lambda x.x)y)
 \to_\beta y$
 
Strangely enough, this natural rule is not enough to cover 
Church's conception of a function.
For one thing, due to the risk of variable capture, 
we need the ability to rename bound variables.

The *α-conversion* $(\lambda x.M) \to_\alpha (\lambda
y.M[y/x])$ renames the abstraction's bound variable from $x$ to
$y$. It is valid provided $y$ does not occur (free or bound)
in $M$. For example,
$(\lambda x.(xz)) \to_\alpha (\lambda y.(yz))$. 

We are still not finished. For suppose that $M$ and $M'$
enjoy the property that $MN=M'N$ for all $N$.
If we really regard them as rules of correspondence,
and they behave identically, then we must insist that $M=M'$.
(Note that we have not yet defined equality, but rather are trying to do so now.)
This fundamental principle is sometimes called *extensionality of functions*.

The *η-reduction* $(\lambda x.(Mx)) \to_\eta M$ replaces the
trivial function $\lambda x.Mx$ — where $M$ does not depend on $x$ — by $M$. 
Formally, the condition above is $x\not\in\FV(M)$: the
abstraction does nothing but apply $M$ to its argument.
For example,  $(\lambda x.((zy)x)) \to_\eta zy$.

We write $M=N$ if it is possible to transform $M$ into $N$
through any series of α, β or η steps, 
possibly within a term (not just at top level).
Most of the desirable properties of equality can be shown to hold quite easily.
It is an equivalence relation and has the natural substitutivity properties,
for example, if $M'=M$ then $M'N=MN$.

As a small demonstration, here is a proof that η implies extensionality. 
Suppose we have $M$ and $M'$ such that $MN=M'N$ for all $N$.
Then pick a fresh variable $x$ (that is, $x\not\in\FV(MM'\)$.
We have $Mx=M'x$, hence $\lambda x.Mx = \lambda x. M'x$ (by substitutivity)
and hence $M=M'$ (by two η-reductions).

One thing is still missing: a consistency proof.
A theory where $M=N$ for all terms $M$ and $N$ is useless. 
That equality in the λ-calculus is nontrivial was proved by Church and Rosser, through a process both protrected and painful.[^3]

[^3]: J. Barkley Rosser. [Highlights of the History of the Lambda-Calculus](/papers/Rosser-Lambda-Calculus.pdf).

