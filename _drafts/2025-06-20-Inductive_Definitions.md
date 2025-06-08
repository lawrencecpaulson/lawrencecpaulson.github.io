---
layout: post
title:  Inductive definitions
usemathjax: true 
tags: [inductive definitions]
---
The [previous post]({% post_url 2025-06-04-Definitions %}) 
discussed the simplest sort of definitions,
those that are essentially abbreviations.
An [*inductive definition*](https://lawrencecpaulson.github.io/tag/inductive_definitions) is conceptionally quite different.
The simplest example is to say that a natural number can be 0
or the successor of another natural number, and that **there are
no other natural numbers**.
This last *minimality property* is the basis for mathematical induction,
for it implies that if some property holds for 0 and is preserved as we move from a natural number to its successor, then all natural numbers have been accounted for.
Inductive definitions are a natural way to specify
recursive datatypes such as lists and trees, 
programming language semantics, inference systems
and much else. 
Proof by induction the axiom of infinitycorresponds (respectively) to
structural induction, induction on program executions, induction over derivations.
Proofs involving inductive definitions are often easy,
with automation taking care of most of the work.

### A tiny example

The very simplest example of an inductive definition would be the natural numbers themselves, but recursive datatypes are treated as a special case with their own syntax.
Instead, let's look at the Isabelle equivalent of the Prolog program 
to append two lists:

```
append([],X,X).
append([X|Y],Z,[X|W]) :- append(Y,Z,W).  
```
In case you don't know Prolog, this defines a ternary relation, `append`.
The first two arguments are the lists to be joined 
and the third argument is the result.
In Prolog, you do not define functions but rather relations that specify
how the output is derived from the inputs.[^1]
The first clause is for joining an empty list, 
while the second joins a list with head $X$ and tail $Y$ to some other list, $Z$.

[^1]: In fact, Prolog does not force us to distinguish inputs from outputs. But that's another story.

This Prolog code is easily expressed in Isabelle.
Note however that the Isabelle definition does not
reproduce Prolog's depth-first execution model. It is simply mathematics.

<pre class="source">
<span class="keyword1 command">inductive</span> <span class="entity">Append</span> <span class="main">::</span> <span class="quoted quoted"><span>"</span><span class="main">[</span><span class="tfree">'a</span> <span class="tconst">list</span><span class="main">,</span> <span class="tfree">'a</span> <span class="tconst">list</span><span class="main">,</span> <span class="tfree">'a</span> <span class="tconst">list</span><span class="main">]</span> <span class="main">⇒</span> <span class="tconst">bool</span><span>"</span> <span class="keyword2 keyword">where</span>
    Append_Nil<span class="main">:</span>  <span class="quoted"><span class="quoted"><span>"</span><span class="free">Append</span> <span class="main">[]</span></span> <span class="free bound entity">X</span> <span class="free bound entity">X</span><span>"</span></span>
  <span class="main">|</span> Append_Cons<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">Append</span> <span class="free bound entity">Y</span> <span class="free bound entity">Z</span> <span class="free bound entity">W</span> <span class="main">⟹</span> <span class="free">Append</span> <span class="main">(</span><span class="free bound entity">X</span><span class="main">#</span></span><span class="free bound entity">Y</span><span class="main">)</span> <span class="free bound entity">Z</span> <span class="main">(</span><span class="free bound entity">X</span><span class="main">#</span></span><span class="free bound entity">W</span><span class="main">)</span><span>"</span></span>
</pre>


Let's prove that Append, although written as a relation, is actually functional:

<pre class="source">
<span class="keyword1 command">lemma</span> Append_function<span class="main">:</span> <span class="quoted quoted"><span>"</span><span class="main">⟦</span></span><span class="const">Append</span> <span class="free">X</span> <span class="free">Y</span> <span class="free">Z</span><span class="main">;</span> <span class="const">Append</span> <span class="free">X</span> <span class="free">Y</span> <span class="free">Z'</span><span class="main">⟧</span> <span class="main">⟹</span> <span class="free">Z'</span> <span class="main">=</span> <span class="free">Z</span><span>"</span><span>
</span><span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">induction</span> <span class="quasi_keyword">arbitrary</span><span class="main main">:</span> <span class="quoted free">Z'</span> <span class="quasi_keyword">rule</span><span class="main main">:</span> Append.induct<span class="main">)</span><span>
  </span><span class="keyword3 command">show</span> <span class="quoted quoted"><span>"</span><span class="main">⋀</span><span class="bound">X</span> <span class="bound">Z'</span><span class="main">.</span> </span><span class="const">Append</span> <span class="main">[]</span> <span class="bound">X</span> <span class="bound">Z'</span> <span class="main">⟹</span> <span class="bound">Z'</span> <span class="main">=</span> <span class="bound">X</span><span>"</span><span>
    </span><span class="keyword1 command">using</span> Append.cases <span class="keyword1 command">by</span> <span class="operator">blast</span><span>
</span><span class="keyword1 command">next</span><span>
  </span><span class="keyword3 command">show</span> <span class="quoted quoted"><span>"</span><span class="main">⋀</span><span class="bound">Y</span> <span class="bound">Z</span> <span class="bound">W</span> <span class="bound">X</span> <span class="bound">Z'</span><span class="main">.</span> <span class="main">⟦</span><span class="main">⋀</span><span class="bound">Z'</span><span class="main">.</span> </span><span class="const">Append</span> <span class="bound">Y</span> <span class="bound">Z</span> <span class="bound">Z'</span> <span class="main">⟹</span> <span class="bound">Z'</span><span class="main">=</span><span class="bound">W</span><span class="main">;</span> <span class="const">Append</span> <span class="main">(</span><span class="bound">X</span><span class="main">#</span><span class="bound">Y</span><span class="main">)</span> <span class="bound">Z</span> <span class="bound">Z'</span><span class="main">⟧</span><span>
       </span><span class="main">⟹</span> <span class="bound">Z'</span> <span class="main">=</span> <span class="bound">X</span><span class="main">#</span><span class="bound">W</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> Append.cases list.inject neq_Nil_conv<span class="main">)</span><span>
</span><span class="keyword1 command">qed</span>
</pre>

Here I deliberately avoid Isar's concise syntax for induction to
highlight what needs to be proved.
Note that the induction appeals to the specific induction rule for
`Append`, namely `Append.induct`. The two sub-proofs both appeal to
case analysis on the definition, namely `Append.cases`.
This is a common feature of proofs involving inductive definitions,
and invites the use of a technique called *rule inversion*:
creating new simplification rules to handle special cases
of the inductively defined predicate.
For example, if the first argument is the empty list then the second and third arguments must be equal.
And if the first argument is a list with head $X$,
then the third argument will also have head $X$ and a tail obtained through `Append`.

<pre class="source">
<span class="keyword1 command">inductive_simps</span> Append_Nil_simp <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted quoted">"</span><span class="const">Append</span> <span class="main">[]</span> <span class="free">X</span> <span class="free">Y</span><span>"</span><span>
<span class="keyword1 command">inductive_simps</span> Append_Cons_simp <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted quoted">"</span><span class="const">Append</span> <span class="main">(</span><span class="free">X</span><span class="main">#</span><span class="free">Y</span><span class="main">)</span> <span class="free">Z</span> <span class="free">V</span><span>"</span></span>
</pre>

Isabelle can easily generate these and similar facts by instantiating and then simplifying the relevant case analysis rule.
If you set up rule inversion skilfully and integrate it with simplification, the combination can be extremely powerful.
The proof above becomes only slightly simpler (the metis call needs just
one argument, `Append_Cons_simp`),
but the following similar theorem now gets a one-line proof:

<pre class="source">
<span class="keyword1 command">lemma</span> Append_function2<span class="main">:</span> <span class="quoted quoted"><span>"</span><span class="main">⟦</span></span><span class="const">Append</span> <span class="free">X</span> <span class="free">Y</span> <span class="free">Z</span><span class="main">;</span> <span class="const">Append</span> <span class="free">X</span> <span class="free">Y'</span> <span class="free">Z</span><span class="main">⟧</span> <span class="main">⟹</span> <span class="free">Y'</span> <span class="main">=</span> <span class="free">Y</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">induction</span> <span class="quasi_keyword">rule</span><span class="main main">:</span> Append.induct<span class="main">)</span> <span class="operator">auto</span>
</pre>

The lemma below expresses that append is associative.
It again has a one line proof, thanks to our special simplification rules:

<pre class="source">
<span class="keyword1 command">lemma</span> Append_assoc<span class="main">:</span> <span class="quoted quoted"><span>"</span><span class="main">⟦</span></span><span class="const">Append</span> <span class="free">T</span> <span class="free">U</span> <span class="free">V</span><span class="main">;</span> <span class="const">Append</span> <span class="free">V</span> <span class="free">W</span> <span class="free">X</span><span class="main">;</span> <span class="const">Append</span> <span class="free">U</span> <span class="free">W</span> <span class="free">Y</span><span class="main">⟧</span> <span class="main">⟹</span> <span class="const">Append</span> <span class="free">T</span> <span class="free">Y</span> <span class="free">X</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">induction</span> <span class="quasi_keyword">arbitrary</span><span class="main main">:</span> <span class="quoted free">X</span> <span class="quasi_keyword">rule</span><span class="main main">:</span> Append.induct<span class="main">)</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> Append_function<span class="main">)</span>
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>
<pre class="source">
</pre>
<pre class="source">
</pre>
<pre class="source">
</pre>

### What an inductive definition means mathematically

In typical usage, an inductive definition carves out
a distinguished subset of something we have already.
An inference system distinguishes a given set of formulas as being theorems;
the full set of formulas had been defined previously.
The semantics of a programming language is defined on configurations involving
a fragment of program syntax combined with information about the program state,
distinguishing those state transitions allowed by the language;
the syntax and state space had been defined previously.

Even when we define the set of natural numbers in terms of zero and successor,
we need to have defined zero and successor already.
In set theory, zero is the empty set and the successor of $n$ is $n \cup \\{n\\}$;
The axiom of infinity guarantees the existence of a set closed under these,
and the minimality property can be obtained by a least fixed-point construction,
ultimately a set intersection.
The situation is similar in higher-order logic.
However, dependent-typed theories such as used in Lean need the concept of inductive definition to be primitive to the formalism itself.

Aczel paper
