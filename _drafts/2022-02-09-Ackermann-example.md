---
layout: post
title:  "Fun with Ackermann's function"
usemathjax: true 
tags: examples, Isabelle, Ackermann's function
---

An undergraduate course on recursion theory typically introduces Turing machines, register machines, general recursive functions and possibly the λ-calculus. They learn about the principle of primitive recursion, which is easy to grasp, and the minimisation operator, which is less so. Ackermann's function is invariably mentioned as an example of a function that is obviously computable but not computable by primitive recursion alone. Unfortunately, it is not easily expressible in the familiar models of computation, although its definition is simplicity itself.

### Ackermann's function

In its modern form (simplified by Rózsa Péter and Raphael Robinson), Ackermann's function is defined as follows:

$$
\begin{align*}
	A(0,n) & = n+1\\
	A(m+1,0) & = A(m,1)\\
	A(m+1,n+1) & = A(m,A(m+1,n)).
\end{align*}
$$

It resembles the calculation of the upper bound of the Ramsey number from the [proof of Ramsey's theorem]({% post_url 2021-12-29-Ramsey-1 %}). Both can easily express unimaginably large numbers.
I was taught this material at Caltech by [Frederick B Thompson](https://www.caltech.edu/about/news/frederick-b-thompson-43160), who as a homework exercise asked his students to write out in full the calculation $A(4,3)$. Nobody did, but one of the students managed to estimate that 

$$ 
\begin{gather*}
A(4,3)\approx 10^{10^{20000}}.
\end{gather*} $$

The first argument determines how rapidly it rises: note that $A(3,4)=125$, and don't even think about $A(125,4)$. 
Oddly enough, physicists regard $10^{80}$ as a big number, greater than the number of neutrinos in the universe. Greater than the diameter of the universe. (In microns. Squared.)
An astronomical number is, mathematically speaking, tiny.

### Expressing Ackermann's function

Ackermann's function is syntactically recursive but that does not help us express it using recursive function theory. Cutland, in [*Computability*](https://doi.org/10.1017/CBO9781139171496) (pages 46–47) devotes an entire page to sketching a laborious construction of a register machine, before remarking that ``a sophisticated proof'' is available using more advanced results. 

One model of computation that can easily express Ackermann's function is the λ-calculus, through the glory of Church numerals (for details, see [my lecture notes](https://www.cl.cam.ac.uk/~lp15/papers/Notes/Founds-FP.pdf), page 17):

 $$
\DeclareMathOperator{\Suc}{Suc}
\DeclareMathOperator{\ack}{ack}
\newcommand{\cons}{\mathbin{\#}}
\begin{align*}
F &\equiv \lambda f n. n f (f \underline{1}) \\
A &\equiv \lambda m. m F \mathbf{suc}
\end{align*}
$$

### Ackermann's function as a rewrite system

What's fiendish about the recursion in Ackermann's function is that it is nested. Nevertheless, reducing recursion to iteration is second nature to a computer scientist. The recursion corresponds fairly straightforwardly to a stack computation, or again to a term rewriting system. (The purpose of the boxes is to anchor the rewrite rules to the left. The # operator separates list elements.)

$$
\begin{align*}
	\Box \cons n\cons 0\cons L &\longrightarrow \Box \cons \Suc n \cons  L\\
	\Box \cons 0\cons \Suc m\cons L &\longrightarrow \Box \cons 1\cons  m \cons L\\
	\Box \cons \Suc n\cons \Suc m\cons L &\longrightarrow \Box \cons n\cons \Suc m\cons  m \cons L
\end{align*}
$$

The point of this version is that it corresponds naturally to a register machine or Turing machine program. The problem is, how can we be sure that it corresponds to Ackermann's function? How do we even know that it terminates? The termination of Ackermann's function itself is trivial, but that proof doesn't work here.

This question is an instance of the halting problem. Although it is undecidable in general, sophisticated techniques and tools exist for proving the termination of a rewrite system. For this one, all existing tools fail. Fortunately, there's a remarkably simple termination proof using Isabelle/HOL, and it illustrates the treatment of tricky recursive functions.

### The Isabelle formalisation

<pre class="source">
<span class="keyword1"><span class="command">fun</span> <span class="entity">ack</span></span><span> </span><span class="main">::</span><span> </span><span class="quoted quoted"><span>"</span><span class="main">[</span><span>nat</span><span class="main">,</span><span>nat</span><span class="main">]</span><span> </span><span class="main">⇒</span><span> </span><span>nat</span><span>"</span></span><span> </span><span class="keyword2 keyword">where</span><span>
  </span><span class="quoted quoted"><span>"</span><span class="free">ack</span><span> </span><span class="main">0</span><span> </span><span class="free bound entity">n</span><span>             </span><span class="main">=</span><span> </span><span>Suc</span><span> </span><span class="free bound entity">n</span><span>"</span></span><span>
</span><span class="main">|</span><span> </span><span class="quoted quoted"><span>"</span><span class="free">ack</span><span> </span><span class="main">(</span><span>Suc</span><span> </span><span class="free bound entity">m</span><span class="main">)</span><span> </span><span class="main">0</span><span>       </span><span class="main">=</span><span> </span><span class="free">ack</span><span> </span><span class="free bound entity">m</span><span> </span><span class="main">1</span><span>"</span></span><span>
</span><span class="main">|</span><span> </span><span class="quoted quoted"><span>"</span><span class="free">ack</span><span> </span><span class="main">(</span><span>Suc</span><span> </span><span class="free bound entity">m</span><span class="main">)</span><span> </span><span class="main">(</span><span>Suc</span><span> </span><span class="free bound entity">n</span><span class="main">)</span><span> </span><span class="main">=</span><span> </span><span class="free">ack</span><span> </span><span class="free bound entity">m</span><span> </span><span class="main">(</span><span class="free">ack</span><span> </span><span class="main">(</span><span>Suc</span><span> </span><span class="free bound entity">m</span><span class="main">)</span><span> </span><span class="free bound entity">n</span><span class="main">)</span><span>"</span></span>
</pre>

Fortunately, the function definition package allows us to define a function and only later identify its domain of termination.
Instead, it makes all the recursion equations conditional on satisfying
the function's domain predicate. Here we shall eventually be able
to show that the predicate is always satisfied.

<pre class="source">
<span class="keyword1 command">function</span><span> </span><span class="main">(</span><span>domintros</span><span class="main">)</span><span> </span><span class="entity">ackloop</span><span> </span><span class="main">::</span><span> </span><span class="quoted quoted"><span>"</span><span>nat</span><span> </span><span>list</span><span> </span><span class="main">⇒</span><span> </span><span>nat</span><span>"</span></span><span> </span><span class="keyword2 keyword">where</span><span>
  </span><span class="quoted quoted"><span>"</span><span class="free">ackloop</span><span> </span><span class="main">(</span><span class="free bound entity">n</span><span> </span><span class="main">#</span><span> </span><span class="main">0</span><span> </span><span class="main">#</span><span> </span><span class="free bound entity">l</span><span class="main">)</span><span>         </span><span class="main">=</span><span> </span><span class="free">ackloop</span><span> </span><span class="main">(</span><span>Suc</span><span> </span><span class="free bound entity">n</span><span> </span><span class="main">#</span><span> </span><span class="free bound entity">l</span><span class="main">)</span><span>"</span></span><span>
</span><span class="main">|</span><span> </span><span class="quoted quoted"><span>"</span><span class="free">ackloop</span><span> </span><span class="main">(</span><span class="main">0</span><span> </span><span class="main">#</span><span> </span><span>Suc</span><span> </span><span class="free bound entity">m</span><span> </span><span class="main">#</span><span> </span><span class="free bound entity">l</span><span class="main">)</span><span>     </span><span class="main">=</span><span> </span><span class="free">ackloop</span><span> </span><span class="main">(</span><span class="main">1</span><span> </span><span class="main">#</span><span> </span><span class="free bound entity">m</span><span> </span><span class="main">#</span><span> </span><span class="free bound entity">l</span><span class="main">)</span><span>"</span></span><span>
</span><span class="main">|</span><span> </span><span class="quoted quoted"><span>"</span><span class="free">ackloop</span><span> </span><span class="main">(</span><span>Suc</span><span> </span><span class="free bound entity">n</span><span> </span><span class="main">#</span><span> </span><span>Suc</span><span> </span><span class="free bound entity">m</span><span> </span><span class="main">#</span><span> </span><span class="free bound entity">l</span><span class="main">)</span><span> </span><span class="main">=</span><span> </span><span class="free">ackloop</span><span> </span><span class="main">(</span><span class="free bound entity">n</span><span> </span><span class="main">#</span><span> </span><span>Suc</span><span> </span><span class="free bound entity">m</span><span> </span><span class="main">#</span><span> </span><span class="free bound entity">m</span><span> </span><span class="main">#</span><span> </span><span class="free bound entity">l</span><span class="main">)</span><span>"</span></span><span>
</span><span class="main">|</span><span> </span><span class="quoted quoted"><span>"</span><span class="free">ackloop</span><span> </span><span class="main">[</span><span class="free bound entity">m</span><span class="main">]</span><span> </span><span class="main">=</span><span> </span><span class="free bound entity">m</span><span>"</span></span><span>
</span><span class="main">|</span><span> </span><span class="quoted quoted"><span>"</span><span class="free">ackloop</span><span> </span><span class="main">[]</span><span> </span><span class="main">=</span><span>  </span><span class="main">0</span><span>"</span></span><span>
  </span><span class="keyword1 command">by</span><span> </span><span class="operator">pat_completeness</span><span> </span><span class="operator">auto</span>
</pre>

Termination is trivial if the length of the list is less then two.
The following lemma is the key to proving termination for longer lists.

<pre class="source">
<span class="keyword1 command">lemma</span><span> </span><span>ackloop_dom_longer</span><span class="main">:</span><span>
  </span><span class="quoted quoted"><span>"</span><span>ackloop_dom</span><span> </span><span class="main">(</span><span>ack</span><span> </span><span class="free">m</span><span> </span><span class="free">n</span><span> </span><span class="main">#</span><span> </span><span class="free">l</span><span class="main">)</span><span> </span><span class="main">⟹</span><span> </span><span>ackloop_dom</span><span> </span><span class="main">(</span><span class="free">n</span><span> </span><span class="main">#</span><span> </span><span class="free">m</span><span> </span><span class="main">#</span><span> </span><span class="free">l</span><span class="main">)</span><span>"</span></span><span>
  </span><span class="keyword1 command">by</span><span> </span><span class="main">(</span><span class="operator">induction</span><span> </span><span class="quoted free">m</span><span> </span><span class="quoted free">n</span><span> </span><span class="quasi_keyword">arbitrary</span><span class="main main">:</span><span> </span><span class="quoted free">l</span><span> </span><span class="quasi_keyword">rule</span><span class="main main">:</span><span> </span><span>ack.induct</span><span class="main">)</span><span> </span><span class="operator">auto</span>
</pre>

This function codifies what ackloop is designed to do.

<pre class="source">
<span class="keyword1 command">fun</span><span> </span><span class="entity">acklist</span><span> </span><span class="main">::</span><span> </span><span class="quoted quoted"><span>"</span><span>nat</span><span> </span><span>list</span><span> </span><span class="main">⇒</span><span> </span><span>nat</span><span>"</span></span><span> </span><span class="keyword2 keyword">where</span><span>
  </span><span class="quoted quoted"><span>"</span><span class="free">acklist</span><span> </span><span class="main">(</span><span class="free bound entity">n</span><span class="main">#</span><span class="free bound entity">m</span><span class="main">#</span><span class="free bound entity">l</span><span class="main">)</span><span> </span><span class="main">=</span><span> </span><span class="free">acklist</span><span> </span><span class="main">(</span><span>ack</span><span> </span><span class="free bound entity">m</span><span> </span><span class="free bound entity">n</span><span> </span><span class="main">#</span><span> </span><span class="free bound entity">l</span><span class="main">)</span><span>"</span></span><span>
</span><span class="main">|</span><span> </span><span class="quoted quoted"><span>"</span><span class="free">acklist</span><span> </span><span class="main">[</span><span class="free bound entity">m</span><span class="main">]</span><span> </span><span class="main">=</span><span> </span><span class="free bound entity">m</span><span>"</span></span><span>
</span><span class="main">|</span><span> </span><span class="quoted quoted"><span>"</span><span class="free">acklist</span><span> </span><span class="main">[]</span><span> </span><span class="main">=</span><span>  </span><span class="main">0</span><span>"</span></span>
</pre>

<pre class="source">
<span class="keyword1 command">lemma</span><span> </span><span>ackloop_dom</span><span class="main">:</span><span> </span><span class="quoted quoted"><span>"</span><span>ackloop_dom</span><span> </span><span class="free">l</span><span>"</span></span><span>
  </span><span class="keyword1 command">by</span><span> </span><span class="main">(</span><span class="operator">induction</span><span> </span><span class="quoted free">l</span><span> </span><span class="quasi_keyword">rule</span><span class="main main">:</span><span> </span><span>acklist.induct</span><span class="main">)</span><span> </span><span class="main">(</span><span class="operator">auto</span><span> </span><span class="quasi_keyword">simp</span><span class="main main">:</span><span> </span><span>ackloop_dom_longer</span><span class="main">)</span>
</pre>

<pre class="source">
<span class="keyword1 command">termination</span><span> </span><span class="quoted">ackloop</span><span>
  </span><span class="keyword1 command">by</span><span> </span><span class="main">(</span><span class="operator">simp</span><span> </span><span class="quasi_keyword">add</span><span class="main main">:</span><span> </span><span>ackloop_dom</span><span class="main">)</span>
</pre>

<pre class="source">
<span class="keyword1 command">lemma</span><span> </span><span>ackloop_acklist</span><span class="main">:</span><span> </span><span class="quoted quoted"><span>"</span><span>ackloop</span><span> </span><span class="free">l</span><span> </span><span class="main">=</span><span> </span><span>acklist</span><span> </span><span class="free">l</span><span>"</span></span><span>
  </span><span class="keyword1 command">by</span><span> </span><span class="main">(</span><span class="operator">induction</span><span> </span><span class="quoted free">l</span><span> </span><span class="quasi_keyword">rule</span><span class="main main">:</span><span> </span><span>ackloop.induct</span><span class="main">)</span><span> </span><span class="operator">auto</span>
</pre>

<pre class="source">
<span class="keyword1 command">theorem</span><span> </span><span>ack</span><span class="main">:</span><span> </span><span class="quoted quoted"><span>"</span><span>ack</span><span> </span><span class="free">m</span><span> </span><span class="free">n</span><span> </span><span class="main">=</span><span> </span><span>ackloop</span><span> </span><span class="main">[</span><span class="free">n</span><span class="main">,</span><span class="free">m</span><span class="main">]</span><span>"</span></span><span>
  </span><span class="keyword1 command">by</span><span> </span><span class="main">(</span><span class="operator">simp</span><span> </span><span class="quasi_keyword">add</span><span class="main main">:</span><span> </span><span>ackloop_acklist</span><span class="main">)</span>
</pre>

More interactive version of this document [available online](https://isabelle.in.tum.de/dist/library/HOL/HOL-Examples/Ackermann.html).

Source file is `src/HOL/Examples/Ackermann.thy` in your downloaded copy of Isabelle.

 [my paper](https://doi.org/10.1017/bsl.2021.47)
 
  [Rosetta code](https://rosettacode.org/wiki/Ackermann_function) for implementations in hundreds of programming languages