---
layout: post
title:  Most proofs are trivial
usemathjax: true 
tags: [general,verification,philosophy]
---
Perhaps I have to begin with an apology. 
I am not asserting that mathematics is trivial,
nor am I belittling students who struggle with elementary exercises.
I know how it feels to be told that a problem I cannot solve is trivial.
Nevertheless, the claim of this post is on the one hand obvious and on the other hand profound.
It suggests new ways of thinking about proof assistants and program verification.
But first, I had better prove my point. It will be trivial.

### Discrete mathematics

Many students hate discrete mathematics and find the problems hard.
Consider for example $\mathcal{P} (A\cap B) = \mathcal{P} (A) \cap \mathcal{P} (B)$.
A typical student will ask, "how do I even begin?".
But for many of these problems there is one obvious step you can do:
it doesn't yield an immediate solution, but it leads to another obvious step and another and another.
This heuristic is called "following your nose" and it is a great way to prove trivial theorems.
Remember that two sets are equal if they contain the same elements, so we try

$$ 
\begin{align*}
X \in \mathcal{P} (A\cap B) \iff X \subseteq A\cap B \iff X \subseteq A \land X \subseteq B \iff X \in \mathcal{P} (A) \cap \mathcal{P} (B). 
\end{align*}
$$

Yup, trivial. (Even if some of those steps could have been expanded out a bit more.)
Many problems of discrete mathematics can be solved by following your nose.

### Whitehead and Russell's *Principia Mathematica*

In this [landmark work](https://plato.stanford.edu/entries/principia-mathematica/), 
the authors set out to prove that mathematics could be reduced to logic.
And I would argue that they succeeded, because the formal system they introduced, 
after simplification, became what we know today as higher-order logic.
That logic has been convincingly shown through recent formalisation efforts
to be capable of expressing truly substantial chunks of mathematics.
*PM* is notorious for its horrible notation ([take a look!](https://archive.org/details/alfred-north-whitehead-bertrand-russel-principia-mathematica.-1/Alfred%20North%20Whitehead%2C%20Bertrand%20Russel%20-%20Principia%20Mathematica.%201/page/107/mode/2up)), 
and also for taking 360 pages to prove that 1+1=2.

*PM* contains only trivial proofs.
As I remarked in an [earlier post]({% post_url 2023-01-11-AI_at_Stanford %}), 
these assertions were used as exercises in early theorem proving experiments.
Newell and Simon's heuristic *Logic Theorist* proved 38 theorems from the first two chapters in 1958. 
Shortly afterwards, Hao Wang used his knowledge of logic to implement a powerful algorithm that proved
hundreds of theorems from *PM* in minutes, on a IBM 704.
It is no disparagement of Wang's work to say that he demonstrated that PM presents a list of trivial proofs.
What he did cannot be done even with today's technology for a typical mathematics textbook,
although most problems you find in a discrete mathematics course
can be proved automatically by Isabelle/HOL. And if you don't believe me, here is ChatGPT:

> the “abridged edition” of Principia Mathematica (the one that ends at §56) does not contain any “difficult” theorems in the sense of being mathematically deep or challenging; rather, it consists entirely of extremely elementary logical and propositional results, all proved in excruciating detail.

Full disclosure: I also noticed errors in ChatGPT's output, 
but I'm sure that this bit is right.

### Foundations of Analysis

Edmund Landau's textbook *Grundlagen der Analysis* 
was chosen for the first large-scale experiment
with [AUTOMATH](https://lawrencecpaulson.github.io/tag/AUTOMATH) because, as de Bruijn remarked,
it was nicely detailed right through to the end.
Landau's book develops the complex number system from pure logic, 
so it can be seen as an updated version of *PM*, without the philosophy.

Most of Landau's proofs are trivial.
He introduces the positive natural numbers axiomatically,
including the usual definitions of addition, ordering and multiplication.
The algebraic laws that they enjoy are important mathematical facts, 
but nevertheless their proofs are all trivial inductions.
If Landau had decided to introduce the prime numbers,
he would soon enough reach proofs that could not be called trivial,
such as the *fundamental theorem of arithmetic*: unique factorisation.

Next, he introduces fractions as equivalence classes 
of pairs of natural numbers.
[Equivalence classes]({% post_url 2022-03-30-Quotienting %}) 
can be a challenge, both for students and for some proof assistants.
However, they are mathematically simpler
than identifying rational numbers with reduced fractions,
which would require a theory of greatest common divisors
and tough proofs to show, for example,
that addition of reduced fractions is associative.
Once you are comfortable with the idea that 
a rational number is an equivalence class,
you can obtain such facts as associativity
with little fuss: they are also trivial.
*Proofs become easier 
if you use the right mathematical tools*, 
even if they are more sophisticated than you are used to.

Landau continues by defining Dedekind cuts of rationals,
which yields the positive real numbers.
Theorem 161 on the existence of square roots
is one of the few nontrivial proofs in this chapter.
He proceeds to develop the real and complex number systems straightforwardly.
The "main theorem" of the book is *Dedekind's Fundamental Theorem*,
which expresses the completeness of the reals
and has a detailed proof covering three pages.
But Landau's style is extremely detailed and even this proof cannot be called hard.

One fault with Landau's approach is that he obtains the real numbers 
from the positive reals by a signed-magnitude approach
that causes a massive explosion of case analyses.
Equivalence classes of pairs of positive reals (representing their difference)
is the elegant way to introduce zero and the negative reals.

Few modern textbooks are as detailed as *Grundlagen*.
Authors prefer to present only the hard proofs, leaving the easy ones as exercises.

### Cantor’s theorem

### Operational semantics of programming languages

### Program verification

DeMillo Lipton and Perlis disenchantment with a lengthy proof of something trivial

### implications

e.g. for worst case thinking

For proof assistants

