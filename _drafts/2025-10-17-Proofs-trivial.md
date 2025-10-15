---
layout: post
title:  Most proofs are trivial
usemathjax: true 
tags: [general,verification,philosophy,Isar]
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

Full disclosure: my experience with ChatGPT is patchy, 
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

Landau's obtains the real numbers 
from the positive reals by a signed-magnitude approach
that complicates proofs with a massive explosion of cases.
Equivalence classes of pairs of positive reals (representing their difference)
is the elegant way to introduce zero and the negative reals.
It's hard to see why Landau made such an error.

Few modern textbooks are as detailed as *Grundlagen*.
Authors prefer to present only the hard proofs, 
leaving the easy ones (the majority) as exercises.
Don't be fooled!

### Cantor’s theorem

Cantor’s theorem states that, for any set $A$, 
there exists no surjective function $f : A \to \mathcal{P}(A)$.
The proof, via Russell's paradox, is easy 
and was first [generated automatically](https://www.ijcai.org/Proceedings/77-1/Papers/100.pdf) way back in 1977.
The proof in Isabelle is just a few lines of Isar text.

<pre class="source">
<span class="keyword1 command">theorem</span> Cantors_theorem<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">∄</span></span><span class="bound">f</span><span class="main">.</span></span> <span class="bound">f</span> <span class="main">`</span> <span class="free">A</span> <span class="main">=</span> <span class="const">Pow</span> <span class="free">A</span><span>"</span><span>
</span><span class="keyword1 command">proof</span><span>
  </span><span class="keyword3 command">assume</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">∃</span></span><span class="bound">f</span><span class="main">.</span></span> <span class="bound">f</span> <span class="main">`</span> <span class="free">A</span> <span class="main">=</span> <span class="const">Pow</span> <span class="free">A</span><span>"</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">obtain</span> <span class="skolem skolem">f</span> <span class="keyword2 keyword">where</span> f<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">f</span> <span class="main">`</span></span> <span class="free">A</span> <span class="main">=</span></span> <span class="const">Pow</span> <span class="free">A</span><span>"</span> <span class="keyword1 command">..</span><span>
  </span><span class="keyword1 command">let</span> <span class="var quoted var">?X</span> <span class="main">=</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">{</span><span class="bound bound">a</span> <span class="main">∈</span> <span class="free">A</span><span class="main">.</span> <span class="bound">a</span> <span class="main">∉</span></span> <span class="skolem">f</span> <span class="bound">a</span><span class="main">}</span><span>"</span></span><span>
  </span><span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="var">?X</span> <span class="main">∈</span></span> </span><span class="const">Pow</span> <span class="free">A</span><span>"</span> <span class="keyword1 command">by</span> <span class="operator">blast</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="var">?X</span> <span class="main">∈</span></span> <span class="skolem">f</span> <span class="main">`</span></span> <span class="free">A</span><span>"</span> <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">only</span><span class="main main">:</span> f<span class="main">)</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">obtain</span> <span class="skolem skolem">x</span> <span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">x</span> <span class="main">∈</span></span> <span class="free">A</span><span>"</span></span> <span class="keyword2 keyword">and</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">f</span> <span class="skolem">x</span> <span class="main">=</span></span> <span class="var">?X</span><span>"</span></span> <span class="keyword1 command">by</span> <span class="operator">blast</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="const">False</span> <span class="keyword1 command">by</span> <span class="operator">blast</span><span>
</span><span class="keyword1 command">qed</span>
</pre>

Cantor's theorem is profound and has wide-ranging implications.
It implies that there is no universal set and no greatest cardinal number.
So the *theorem* is not trivial, but methinks the *proof* kinda is.

### Operational semantics of programming languages

Since the 1980s, we have had highly sophisticated techniques
for specifying the semantics of programming languages, both
*static semantics* such as type checking and name resolution, and
*dynamic semantics* or what happens at runtime (including concurrency).
Using such techniques, we can prove that a proposed programming language satisfies
key properties such as 
*progress* (a well typed expression make another step of evaluation)
*type preservation* (such an evaluation step will not change its type),
and *determinacy* (the next evaluation step is unique).

The techniques rely on specifying typing, reduction, etc. as relations 
[defined inductively]({% post_url 2025-06-09-Inductive_Definitions %})),
as I have illustrated in a [previous blogpost]({% post_url 2023-03-08-Fun_Semantics %}).
As mentioned in that blogpost, these proofs are simultaneously highly intricate and trivial: 

* They are intricate because simply to apply the relevant induction rule correctly
generates pages of formulas. They are almost impossible to write out flawlessly by hand.

* They are trivial because the sorts of properties typically proved hold because the language was designed that they would hold. 
Languages are designed such that the type system makes sense, 
evaluation steps don't change integers into strings and 
(in the absence of concurrency) there is only one possible next step.

It's true that some program properties have deep and difficult proofs.
The quintessential example is the Church-Rosser theorem,
which says that different evaluation paths for a particular
λ-calculus expression cannot lead to different values.
This obviously desirable property cannot be said to hold by design
and the first attempts to prove it were incorrect.

This was the category of proofs that led to this blogpost in the first place.
The point is that people feel ripped off if they have to struggle 
to prove something obvious.

### Program verification

DeMillo Lipton and Perlis disenchantment with a lengthy proof of something trivial

e.g. for worst case thinking

### implications


For proof assistants

