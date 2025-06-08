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
The simplest example is to say that a natural number can be either 0
or the successor of another natural number, and that **there are
no other natural numbers**.
This last *minimality property* is the basis for mathematical induction,
for it implies that if some property holds for 0 and is preserved as we move from a natural number to its successor, then all natural numbers have been accounted for.
Inductive definitions are a natural way to specify
recursive datatypes such as lists and trees, 
programming language semantics, inference systems
and much else. 
Proof by induction corresponds (respectively) to
structural induction, induction on program executions, induction over derivations.
Proofs involving inductive definitions are often easy,
with automation taking care of most of the work.

### A tiny example

The very simplest example of an inductive definition would be the natural numbers themselves, but most proof assistants treat recursive datatypes 
as a separate, highly specialised case.
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
while the second joins a list with head `X` and tail `Y` to some other list, `Z`.

[^1]: In fact, Prolog does not force us to distinguish inputs from outputs. But that's another story.

This Prolog code is easily expressed in Isabelle.
For this example, let's conform to the Prolog convention that variables
begin with capital letters.
Isabelle is even capable of reasoning using a proof strategy related to Prolog's.
Note, however, that the Isabelle definition itself is simply mathematics and does not
model Prolog's depth-first execution model 
(not to mention its broken treatment of unification).

<pre class="source">
<span class="keyword1 command">inductive</span> <span class="entity">Append</span> <span class="main">::</span> <span class="quoted quoted"><span>"</span><span class="main">[</span><span class="tfree">'a</span> <span class="tconst">list</span><span class="main">,</span> <span class="tfree">'a</span> <span class="tconst">list</span><span class="main">,</span> <span class="tfree">'a</span> <span class="tconst">list</span><span class="main">]</span> <span class="main">⇒</span> <span class="tconst">bool</span><span>"</span> <span class="keyword2 keyword">where</span>
    Append_Nil<span class="main">:</span>  <span class="quoted"><span class="quoted"><span>"</span><span class="free">Append</span> <span class="main">[]</span></span> <span class="free bound entity">X</span> <span class="free bound entity">X</span><span>"</span></span>
  <span class="main">|</span> Append_Cons<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">Append</span> <span class="free bound entity">Y</span> <span class="free bound entity">Z</span> <span class="free bound entity">W</span> <span class="main">⟹</span> <span class="free">Append</span> <span class="main">(</span><span class="free bound entity">X</span><span class="main">#</span></span><span class="free bound entity">Y</span><span class="main">)</span> <span class="free bound entity">Z</span> <span class="main">(</span><span class="free bound entity">X</span><span class="main">#</span></span><span class="free bound entity">W</span><span class="main">)</span><span>"</span></span>
</pre>


Let's prove that Append, although written as a relation, is actually functional
(single-valued).
Note that the induction appeals to the specific induction rule for
`Append`, namely `Append.induct`. 

<pre class="source">
<span class="keyword1 command">lemma</span> Append_function<span class="main">:</span> <span class="quoted quoted"><span>"</span><span class="main">⟦</span></span><span class="const">Append</span> <span class="free">X</span> <span class="free">Y</span> <span class="free">Z</span><span class="main">;</span> <span class="const">Append</span> <span class="free">X</span> <span class="free">Y</span> <span class="free">Z'</span><span class="main">⟧</span> <span class="main">⟹</span> <span class="free">Z'</span> <span class="main">=</span> <span class="free">Z</span><span>"</span><span>
</span><span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">induction</span> <span class="quasi_keyword">arbitrary</span><span class="main main">:</span> <span class="quoted free">Z'</span> <span class="quasi_keyword">rule</span><span class="main main">:</span> Append.induct<span class="main">)</span><span>
  </span><span class="keyword3 command">show</span> <span class="quoted quoted"><span>"</span><span class="main">⋀</span><span class="bound">Y</span> <span class="bound">Z'</span><span class="main">.</span> </span><span class="const">Append</span> <span class="main">[]</span> <span class="bound">Y</span> <span class="bound">Z'</span> <span class="main">⟹</span> <span class="bound">Z'</span> <span class="main">=</span> <span class="bound">Y</span><span>"</span><span>
    </span><span class="keyword1 command">using</span> Append.cases <span class="keyword1 command">by</span> <span class="operator">blast</span><span>
  </span><span class="keyword3 command">show</span> <span class="quoted quoted"><span>"</span><span class="main">⋀</span><span class="bound">X</span> <span class="bound">Y</span> <span class="bound">W</span> <span class="bound">A</span> <span class="bound">Z'</span><span class="main">.</span> <span class="main">⟦</span><span class="main">⋀</span><span class="bound">Z'</span><span class="main">.</span> </span><span class="const">Append</span> <span class="bound">X</span> <span class="bound">Y</span> <span class="bound">Z'</span> <span class="main">⟹</span> <span class="bound">Z'</span><span class="main">=</span><span class="bound">W</span><span class="main">;</span> <span class="const">Append</span> <span class="main">(</span><span class="bound">A</span><span class="main">#</span><span class="bound">X</span><span class="main">)</span> <span class="bound">Y</span> <span class="bound">Z'</span><span class="main">⟧</span><span>
       </span><span class="main">⟹</span> <span class="bound">Z'</span> <span class="main">=</span> <span class="bound">A</span><span class="main">#</span><span class="bound">W</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> Append.cases list.inject neq_Nil_conv<span class="main">)</span><span>
</span><span class="keyword1 command">qed</span>
</pre>

Here I deliberately avoid Isar's concise syntax for induction to
highlight the two cases that must be proved.
In the base case, we need to show that `Append` behaves like a function
when its first argument is `[]`;
in the induction step, the first argument is `X`
and we can assume the induction hypothesis that
`Append` behaves like a function
when its first argument is `X`
(where `X` is fixed and local to this case).

Both proofs appeal to
case analysis on the definition, namely `Append.cases`.
This is a common feature of proofs involving inductive definitions,
and invites the use of a technique called *rule inversion*:
creating new simplification rules to handle special cases
of the inductively defined predicate.
For example, if the first argument is the empty list then the second and third arguments must be equal.
And if the first argument is a list with head `X`,
then the third argument will also have head `X` and a tail obtained through `Append`.

<pre class="source">
<span class="keyword1 command">inductive_simps</span> Append_Nil_simp <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted quoted">"</span><span class="const">Append</span> <span class="main">[]</span> <span class="free">X</span> <span class="free">Y</span><span>"</span><span>
<span class="keyword1 command">inductive_simps</span> Append_Cons_simp <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted quoted">"</span><span class="const">Append</span> <span class="main">(</span><span class="free">X</span><span class="main">#</span><span class="free">Y</span><span class="main">)</span> <span class="free">Z</span> <span class="free">V</span><span>"</span></span>
</pre>

Isabelle automatically generates these and similar facts by instantiating and then simplifying the relevant case analysis rule:
you merely need to specify the special case you are interested in,
which will become the left-hand side of the new rewrite rule.
If you set up rule inversion skilfully and integrate it with simplification, the combination can be extremely powerful.
The proof above becomes only slightly simpler (the metis call needs just
one argument, `Append_Cons_simp`),
but the following similar theorem now gets a one-line proof:

<pre class="source">
<span class="keyword1 command">lemma</span> Append_function2<span class="main">:</span> <span class="quoted quoted"><span>"</span><span class="main">⟦</span></span><span class="const">Append</span> <span class="free">X</span> <span class="free">Y</span> <span class="free">Z</span><span class="main">;</span> <span class="const">Append</span> <span class="free">X</span> <span class="free">Y'</span> <span class="free">Z</span><span class="main">⟧</span> <span class="main">⟹</span> <span class="free">Y'</span> <span class="main">=</span> <span class="free">Y</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">induction</span> <span class="quasi_keyword">rule</span><span class="main main">:</span> Append.induct<span class="main">)</span> <span class="operator">auto</span>
</pre>

The lemma below expresses that append is associative.
It again has a one line proof, thanks to our special simplification rules.
(Otherwise, the proof is a mess.)

<pre class="source">
<span class="keyword1 command">lemma</span> Append_assoc<span class="main">:</span> <span class="quoted quoted"><span>"</span><span class="main">⟦</span></span><span class="const">Append</span> <span class="free">T</span> <span class="free">U</span> <span class="free">V</span><span class="main">;</span> <span class="const">Append</span> <span class="free">V</span> <span class="free">W</span> <span class="free">X</span><span class="main">;</span> <span class="const">Append</span> <span class="free">U</span> <span class="free">W</span> <span class="free">Y</span><span class="main">⟧</span> <span class="main">⟹</span> <span class="const">Append</span> <span class="free">T</span> <span class="free">Y</span> <span class="free">X</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">induction</span> <span class="quasi_keyword">arbitrary</span><span class="main main">:</span> <span class="quoted free">X</span> <span class="quasi_keyword">rule</span><span class="main main">:</span> Append.induct<span class="main">)</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> Append_function<span class="main">)</span>
</pre>

Naturally, the append function `@` is already provided by Isabelle's list library,
and it's time to prove that the `Append` relation coincides with this function.
In other words, the Prolog program really computes list append.

We prove this in two directions.
First, the third argument of `Append` can only be the list computed by `@`.
As before, I've written out the base case and induction step explicitly.

<pre class="source">
<span class="keyword1 command">lemma</span> Append_imp_append<span class="main">:</span> <span class="quoted quoted">"</span><span class="const">Append</span> <span class="free">X</span> <span class="free">Y</span> <span class="free">Z</span> <span class="main">⟹</span> <span class="free">Z</span> <span class="main">=</span> <span class="free">X</span><span class="main">@</span><span class="free">Y</span><span>"</span><span>
</span><span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">induction</span> <span class="quasi_keyword">rule</span><span class="main main">:</span> Append.induct<span class="main">)</span><span>
  </span><span class="keyword3 command">show</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">⋀</span><span class="bound">Y</span><span class="main">.</span> <span class="bound">Y</span> <span class="main">=</span></span> <span class="main">[]</span></span> <span class="main">@</span> <span class="bound">Y</span><span>"</span><span> 
    </span><span class="keyword1 command">by</span> <span class="operator">simp</span><span>
  </span><span class="keyword3 command">show</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">⋀</span><span class="bound">X</span> <span class="bound">Y</span> <span class="bound">Z</span> <span class="bound">A</span><span class="main">.</span> <span class="bound">Z</span> <span class="main">=</span></span> <span class="bound">X</span><span class="main">@</span></span><span class="bound">Y</span> <span class="main">⟹</span> <span class="bound">A</span> <span class="main">#</span> <span class="bound">Z</span> <span class="main">=</span> <span class="main">(</span><span class="bound">A</span> <span class="main">#</span> <span class="bound">X</span><span class="main">)</span> <span class="main">@</span> <span class="bound">Y</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="operator">simp</span><span>
</span><span class="keyword1 command">qed</span>
</pre>

It's vital to note that the property above would also be satisfied
if `Append X Y Z` was always false. To complete the equivalence proof,
it's essential to show that `Append` is true given suitable arguments.
This proof is by list induction.
The induction rule `Append.induct` is not applicable because it requires
some instance of `Append X Y Z` as a fact or assumption.

<pre class="source">
<span class="keyword1 command">lemma</span> Append_append<span class="main">:</span> <span class="quoted quoted">"</span><span class="const">Append</span> <span class="free">X</span> <span class="free">Y</span> <span class="main">(</span><span class="free">X</span><span class="main">@</span><span class="free">Y</span><span class="main">)</span><span>"</span><span>
</span><span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">induction</span> <span class="quoted free">X</span><span class="main">)</span><span>
  </span><span class="keyword3 command">show</span> <span class="quoted quoted">"</span><span class="const">Append</span> <span class="main">[]</span> <span class="free">Y</span> <span class="main">(</span><span class="main">[]</span> <span class="main">@</span> <span class="free">Y</span><span class="main">)</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> Append.intros<span class="main">)</span><span>
  </span><span class="keyword3 command">show</span> <span class="quoted quoted"><span>"</span><span class="main">⋀</span><span class="bound">A</span> <span class="bound">X</span><span class="main">.</span> </span><span class="const">Append</span> <span class="bound">X</span> <span class="free">Y</span> <span class="main">(</span><span class="bound">X</span> <span class="main">@</span> <span class="free">Y</span><span class="main">)</span> <span class="main">⟹</span> <span class="const">Append</span> <span class="main">(</span><span class="bound">A</span> <span class="main">#</span> <span class="bound">X</span><span class="main">)</span> <span class="free">Y</span> <span class="main">(</span><span class="main">(</span><span class="bound">A</span> <span class="main">#</span> <span class="bound">X</span><span class="main">)</span> <span class="main">@</span> <span class="free">Y</span><span class="main">)</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> Append.intros<span class="main">)</span><span>
</span><span class="keyword1 command">qed</span>
</pre>

I've again written out the inductions in great detail to reveal
what has to be proved. In fact, these theorems have one-line proofs.

<pre class="source">
<span class="keyword1 command">lemma</span> <span class="quoted quoted">"</span><span class="const">Append</span> <span class="free">X</span> <span class="free">Y</span> <span class="free">Z</span> <span class="main">⟹</span> <span class="free">Z</span> <span class="main">=</span> <span class="free">X</span><span class="main">@</span><span class="free">Y</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">induction</span> <span class="quasi_keyword">rule</span><span class="main main">:</span> Append.induct<span class="main">)</span> <span class="operator">auto</span>
</pre>

<pre class="source">
<span class="keyword1 command">lemma</span> <span class="quoted quoted">"</span><span class="const">Append</span> <span class="free">X</span> <span class="free">Y</span> <span class="main">(</span><span class="free">X</span><span class="main">@</span><span class="free">Y</span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">induction</span> <span class="quoted free">X</span><span class="main">)</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> Append.intros<span class="main">)</span>
</pre>

The equivalence between `Append` and list append is now trivial:

<pre class="source">
<span class="keyword1 command">lemma</span> Append_iff_append<span class="main">:</span> <span class="quoted quoted">"</span><span class="const">Append</span> <span class="free">X</span> <span class="free">Y</span> <span class="free">Z</span> <span class="main">⟷</span> <span class="free">Z</span> <span class="main">=</span> <span class="free">X</span><span class="main">@</span><span class="free">Y</span><span>"</span><span>
  </span><span class="keyword1 command">using</span> Append_append Append_imp_append <span class="keyword1 command">by</span> <span class="operator">blast</span>
</pre>

And with this fact available, it's now trivial to prove things that might be
quite tricky otherwise, such as this one:

<pre class="source">
<span class="keyword1 command">lemma</span> Append_function1<span class="main">:</span> <span class="quoted quoted"><span>"</span><span class="main">⟦</span></span><span class="const">Append</span> <span class="free">X</span> <span class="free">Y</span> <span class="free">Z</span><span class="main">;</span> <span class="const">Append</span> <span class="free">X'</span> <span class="free">Y</span> <span class="free">Z</span><span class="main">⟧</span> <span class="main">⟹</span> <span class="free">X'</span> <span class="main">=</span> <span class="free">X</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> Append_iff_append<span class="main">)</span>
</pre>

And here's a secret: most of the theorems proved at the stop of this example
become trivial using `Append_iff_append`. Most inductive definitions don't
correspond to functions (what would be the point?), but it's often possible
to prove general theorems relating the arguments, from which more specific
properties follow without further use of induction.

### What an inductive definition means mathematically

The inductive definition of a logical calculus may contain *introduction rules* such 
as these:

* if $A\to B$ and $A$ are theorems then so is $B$
* if $\neg\neg A$ is a theorem then so is $A$
* $x=x$ is a theorem

Note that the preconditions, if any, of an introduction rule may refer to
the relation being defined, but only positively. We cannot have a rule 
containing a negative reference,
such as this:

* if $A$ is **not** a theorem then $\neg A$ is a theorem

Precoditions not referring to the relation being defined may have any form.

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
However, dependent-typed theories — such as used in Lean — need the concept of inductive definition to be primitive to the formalism itself.

Documentation is available in Section 3.5 of [Programming and Proving](https://isabelle.in.tum.de/dist/Isabelle/doc/prog-prove.pdf).
For those of you interested in the full abstract theory of inductive definitions,
Peter Aczel's [chapter](https://doi.org/10.1016/S0049-237X(08)71120-0) (also [here](/papers/Aczel-Inductive-Defs.pdf)) in the *Handbook of Mathematical Logic* is the ultimate account.
