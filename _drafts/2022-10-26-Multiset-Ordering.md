---
layout: post
title:  "Proving Termination with Multiset Orderings"
usemathjax: true
tags: [examples, Isabelle, Ackermann's function]
---

The title of this post is identical to the title of a [seminal paper](https://doi.org/10.1145/359138.359142)
by Nachum Dershowitz and Zohar Manna, whom I knew as a graduate student at Stanford.
(I had the privilege of doing some directed reading under Zohar's supervision.)
A *multiset* is a concept of collection that differs from a set in that
multiple occurrences of elements are significant.
Computer scientists typically encounter them as a way of specifying
the concept of sorting: to transform an input list into an output 
that is correctly ordered but equal to the input when both are regarded as multisets.
Dershowitz and Manna showed that multisets also provided
natural but strong orderings for proving the termination of computer programs.
I had written about the termination of a rewrite system for Ackermann's function
in a [previous post]({% post_url 2022-02-09-Ackermann-example %}). 
I was advised to contact Dershowitz, "a leading
expert on termination", and his reply was that the answer I sought
was already in his 1979 paper!

### Ackermann's function



$$
\begin{align*}
	A(0,n) & = n+1\\
	A(m+1,0) & = A(m,1)\\
	A(m+1,n+1) & = A(m,A(m+1,n)).
\end{align*}
$$




### Ackermann's function as a rewrite system

What's fiendish about the recursion in Ackermann's function is that it is nested. Nevertheless, reducing recursion to iteration is second nature to a computer scientist. The recursion corresponds fairly straightforwardly to a stack computation, or again to a term rewriting system:

$$
\begin{align*}
	\Box \cons n\cons 0\cons L &\longrightarrow \Box \cons \Suc n \cons  L\\
	\Box \cons 0\cons \Suc m\cons L &\longrightarrow \Box \cons 1\cons  m \cons L\\
	\Box \cons \Suc n\cons \Suc m\cons L &\longrightarrow \Box \cons n\cons \Suc m\cons  m \cons L
\end{align*}
$$

(The boxes anchor the rewrite rules to the start of the list. The # operator separates list elements.)



### Defining the functions in Isabelle/HOL

The definition of Ackermann's function can be typed into Isabelle/HOL more-or-less verbatim.
That it's well-defined and terminating is detected automatically, and the recursion equations shown are *proved* from a low-level, non-recursive definition. All that happens automatically.

<pre class="source">
<span class="keyword1"><span class="command">fun</span> <span class="entity">ack</span></span><span> </span><span class="main">::</span><span> </span><span class="quoted quoted"><span>"</span><span class="main">[</span>nat<span class="main">,</span>nat<span class="main">]</span><span> </span><span class="main">⇒</span><span> </span>nat<span>"</span></span><span> </span><span class="keyword2 keyword">where</span><span>
  </span><span class="quoted quoted"><span>"</span><span class="free">ack</span><span> </span><span class="main">0</span><span> </span><span class="free bound entity">n</span><span>             </span><span class="main">=</span><span> </span>Suc<span> </span><span class="free bound entity">n</span><span>"</span></span><span>
</span><span class="main">|</span><span> </span><span class="quoted quoted"><span>"</span><span class="free">ack</span><span> </span><span class="main">(</span>Suc<span> </span><span class="free bound entity">m</span><span class="main">)</span><span> </span><span class="main">0</span><span>       </span><span class="main">=</span><span> </span><span class="free">ack</span><span> </span><span class="free bound entity">m</span><span> </span><span class="main">1</span><span>"</span></span><span>
</span><span class="main">|</span><span> </span><span class="quoted quoted"><span>"</span><span class="free">ack</span><span> </span><span class="main">(</span>Suc<span> </span><span class="free bound entity">m</span><span class="main">)</span><span> </span><span class="main">(</span>Suc<span> </span><span class="free bound entity">n</span><span class="main">)</span><span> </span><span class="main">=</span><span> </span><span class="free">ack</span><span> </span><span class="free bound entity">m</span><span> </span><span class="main">(</span><span class="free">ack</span><span> </span><span class="main">(</span>Suc<span> </span><span class="free bound entity">m</span><span class="main">)</span><span> </span><span class="free bound entity">n</span><span class="main">)</span><span>"</span></span>
</pre>

The rewrite rule system shown above can also be typed in verbatim.
The box symbols are unnecessary, since pattern matching inherently targets the start of the list.
But how does Isabelle/HOL handle the issue of termination?

<pre class="source">
<span class="keyword1 command">function</span><span> </span><span class="entity">ackloop</span><span> </span><span class="main">::</span><span> </span><span class="quoted quoted"><span>"</span>nat<span> </span>list<span> </span><span class="main">⇒</span><span> </span>nat<span>"</span></span><span> </span><span class="keyword2 keyword">where</span><span>
  </span><span class="quoted quoted"><span>"</span><span class="free">ackloop</span><span> </span><span class="main">(</span><span class="free bound entity">n</span><span> </span><span class="main">#</span><span> </span><span class="main">0</span><span> </span><span class="main">#</span><span> </span><span class="free bound entity">l</span><span class="main">)</span><span>         </span><span class="main">=</span><span> </span><span class="free">ackloop</span><span> </span><span class="main">(</span>Suc<span> </span><span class="free bound entity">n</span><span> </span><span class="main">#</span><span> </span><span class="free bound entity">l</span><span class="main">)</span><span>"</span></span><span>
</span><span class="main">|</span><span> </span><span class="quoted quoted"><span>"</span><span class="free">ackloop</span><span> </span><span class="main">(</span><span class="main">0</span><span> </span><span class="main">#</span><span> </span>Suc<span> </span><span class="free bound entity">m</span><span> </span><span class="main">#</span><span> </span><span class="free bound entity">l</span><span class="main">)</span><span>     </span><span class="main">=</span><span> </span><span class="free">ackloop</span><span> </span><span class="main">(</span><span class="main">1</span><span> </span><span class="main">#</span><span> </span><span class="free bound entity">m</span><span> </span><span class="main">#</span><span> </span><span class="free bound entity">l</span><span class="main">)</span><span>"</span></span><span>
</span><span class="main">|</span><span> </span><span class="quoted quoted"><span>"</span><span class="free">ackloop</span><span> </span><span class="main">(</span>Suc<span> </span><span class="free bound entity">n</span><span> </span><span class="main">#</span><span> </span>Suc<span> </span><span class="free bound entity">m</span><span> </span><span class="main">#</span><span> </span><span class="free bound entity">l</span><span class="main">)</span><span> </span><span class="main">=</span><span> </span><span class="free">ackloop</span><span> </span><span class="main">(</span><span class="free bound entity">n</span><span> </span><span class="main">#</span><span> </span>Suc<span> </span><span class="free bound entity">m</span><span> </span><span class="main">#</span><span> </span><span class="free bound entity">m</span><span> </span><span class="main">#</span><span> </span><span class="free bound entity">l</span><span class="main">)</span><span>"</span></span><span>
</span><span class="main">|</span><span> </span><span class="quoted quoted"><span>"</span><span class="free">ackloop</span><span> </span><span class="main">[</span><span class="free bound entity">m</span><span class="main">]</span><span> </span><span class="main">=</span><span> </span><span class="free bound entity">m</span><span>"</span></span><span>
</span><span class="main">|</span><span> </span><span class="quoted quoted"><span>"</span><span class="free">ackloop</span><span> </span><span class="main">[]</span><span> </span><span class="main">=</span><span>  </span><span class="main">0</span><span>"</span></span><span>
  </span><span class="keyword1 command">by</span><span> </span><span class="operator">pat_completeness</span><span> </span><span class="operator">auto</span>
</pre>

[Alex Krauss's](https://www21.in.tum.de/~krauss/) wonderful [function definition package](https://isabelle.in.tum.de/dist/Isabelle/doc/functions.pdf) anticipates such difficult cases.
It allows us to define function `f` first and deal with its termination later.
When prompted by the keyword `domintros`, it defines the predicate `f_dom` expressing the termination of `f` for a given argument. Then arbitrary recursion equations for `f` can be accepted, but the package makes them conditional: they will hold only if `f` terminates on the given argument.
Then our task is to prove that `f_dom` holds on the arguments we are interested in
and even partial recursive functions can be dealt with.
Here we shall prove that `ackloop` is a total function by proving that `ackloop_dom` is always satisfied.

### Proving termination


Now that termination has been proved for all possible arguments, we can point out that fact to Isabelle/HOL:

<pre class="source">
<span class="keyword1 command">termination</span><span> </span><span class="quoted">ackloop</span><span>
  </span><span class="keyword1 command">by</span><span> </span><span class="main">(</span><span class="operator">simp</span><span> </span><span class="quasi_keyword">add</span><span class="main main">:</span><span> </span>ackloop_dom<span class="main">)</span>
</pre>

The effect is to make the recursion equations for `ackloop` unconditional.

### Proving the two definitions equivalent

We are nearly there. Knowing that `ackloop` is a total function, and with the help of its own induction rule, we trivially prove its equivalence to `acklist`.

<pre class="source">
<span class="keyword1 command">lemma</span><span> </span>ackloop_acklist<span class="main">:</span><span> </span><span class="quoted quoted"><span>"</span>ackloop<span> </span><span class="free">l</span><span> </span><span class="main">=</span><span> </span>acklist<span> </span><span class="free">l</span><span>"</span></span><span>
  </span><span class="keyword1 command">by</span><span> </span><span class="main">(</span><span class="operator">induction</span><span> </span><span class="quoted free">l</span><span> </span><span class="quasi_keyword">rule</span><span class="main main">:</span><span> </span>ackloop.induct<span class="main">)</span><span> </span><span class="operator">auto</span>
</pre>

It follows directly that Ackermann's function can be computed with the help of `ackloop`.

<pre class="source">
<span class="keyword1 command">theorem</span><span> </span>ack<span class="main">:</span><span> </span><span class="quoted quoted"><span>"</span>ack<span> </span><span class="free">m</span><span> </span><span class="free">n</span><span> </span><span class="main">=</span><span> </span>ackloop<span> </span><span class="main">[</span><span class="free">n</span><span class="main">,</span><span class="free">m</span><span class="main">]</span><span>"</span></span><span>
  </span><span class="keyword1 command">by</span><span> </span><span class="main">(</span><span class="operator">simp</span><span> </span><span class="quasi_keyword">add</span><span class="main main">:</span><span> </span>ackloop_acklist<span class="main">)</span>
</pre>

This example is unusual in that the formal proofs are all one-liners. More commonly, formal proofs are horrible. And yet there is nothing trivial about the termination of `ackloop`.
The system of rewrite rules for Ackermann's function has been added to the [Termination Problems Data Base](http://termination-portal.org/wiki/TPDB) (TPDB) as 
[`Paulson_20/ackermann_iterative.xml`](https://termcomp.github.io/tpdb.html?ver=11.2&path=TRS_Standard%2FPaulson_20%2Fackermann_iterative.xml).
As of this writing, no termination checker can handle it.

### Odds and ends

I have published a [more thorough treatment](https://doi.org/10.1017/bsl.2021.47) of this example in the *Bulletin of Symbolic Logic*.

You'll find the Isabelle proof text at `src/HOL/Examples/Ackermann.thy` in your downloaded copy of Isabelle, and can also [browse it online](https://isabelle.in.tum.de/dist/library/HOL/HOL-Examples/Ackermann.html).

