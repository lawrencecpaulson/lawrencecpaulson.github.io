---
layout: post
title:  "Formalising a new proof that the square root of two is irrational"
usemathjax: true 
tags: [examples, newbies, Isabelle, Isar]
---

Recently, somebody shared on Twitter a 
[new proof](https://theapproximatepresent.tumblr.com/post/51484587425/a-favourite-proof-of-mine-first-demonstrated-to) 
of the irrationality of √2. Its claimed advantage is that "it requires no knowledge of mathematics above the definition of what it means for a number to be irrational, and can be written almost in one line." 
These claims are dubious: the 
usual proof, which I've formalised in a [previous post]({% post_url 2022-05-04-baby-examples %}),
requires only the natural numbers and 
the notion of divisibility.
The "beautiful" proof involves real numbers, 
potentially infinite sets and the nontrivial claim that the square root of two actually exists. 
Nevertheless, formalising it in Isabelle/HOL is an interesting exercise.
In particular, it illustrates reasoning about the least element of a set. So here we go.

<img src="/images/sqrt2-figure.jpg" alt="beautiful proof that sqrt 2 is irrational" width="800"/>

### A remark about numeric types

Before we begin, it's necessary to explain the meanings of the symbols ℕ, ℤ, ℚ, ℝ
in Isabelle/HOL. They denote sets, not types: namely, they denote the sets of natural numbers,
integers, rationals, real numbers (respectively) as **images** embedded in some larger type.
Here we are mostly going to work within type `real`, where ℕ and ℚ 
will denote sets of real numbers. Through the magic of [type classes]({% post_url 2022-03-02-Type_classes %}), 
these symbols denote the right set for other types, such as `complex`, 
[quaternions](https://www.isa-afp.org/entries/Quaternions.html)
and any other types (including those yet to be defined) that inherit the necessary structure.

We need to be careful with types here. I've used the function `real`, which injects natural numbers into type `real`. Most numeric coercions can be omitted in Isabelle:
they are inserted automatically. 
But things are delicate in this example, so it's better to be explicit.


### Defining $R$ and $k$

We begin with the theorem statement and the two definitions shown in the blackboard figure:

<pre class="source">
<span class="keyword1 command">proposition</span> <span class="quoted"><span class="quoted"><span>"</span>sqrt</span> <span class="numeral">2</span> <span class="main">∉</span></span> <span class="main">ℚ</span><span>"</span><span>
</span><span class="keyword1 command">proof</span><span>
  </span><span class="keyword3 command">define</span> <span class="skolem skolem">R</span> <span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">R</span> <span class="main">≡</span> <span class="main">{</span><span class="bound">n</span><span class="main">.</span> <span class="bound">n</span> <span class="main">&gt;</span></span> <span class="main">0</span></span> <span class="main">∧</span> real <span class="bound">n</span> <span class="main">*</span> sqrt <span class="numeral">2</span> <span class="main">∈</span> <span class="main">ℕ</span><span class="main">}</span><span>"</span><span>
  </span><span class="keyword3 command">define</span> <span class="skolem skolem">k</span> <span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">k</span> <span class="main">≡</span> Inf</span> <span class="skolem">R</span><span>"</span></span>
</pre>

Already an error: 0 is a natural number,
but it needs to be excluded from the set $R$ because otherwise $k=0$
and the argument falls apart.

The traditional proof of irrationality begins by claiming
that there are no integers $p$ and $q$ such that $(\frac{p}{q})^2 = 2$.
The proof involves simply showing that both $p$ and $q$ would have to be even numbers,
while every rational number can be written in the form $\frac{p}{q}$ where $p$ and $q$ 
are coprime.
We could even make a distinction between the rational number $\frac{p}{q}$
and the real quotient $p/q$ in order to prove the theorem in the absence of the reals.

Our proof today begins by finding $p$ and $q$ such that $p/q = \sqrt2$.

<pre class="source">
  <span class="keyword3 command">assume</span> <span class="quoted"><span class="quoted"><span>"</span>sqrt</span> <span class="numeral">2</span> <span class="main">∈</span></span> <span class="main">ℚ</span><span>"</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">obtain</span> <span class="skolem skolem">p</span> <span class="skolem skolem">q</span> <span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">q</span><span class="main">≠</span></span><span class="main">0</span></span><span>"</span> <span class="quoted"><span class="quoted"><span>"</span>real</span> <span class="skolem">p</span> <span class="main">/</span></span> real <span class="skolem">q</span> <span class="main">=</span> <span class="main">¦</span>sqrt <span class="numeral">2</span><span class="main">¦</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> Rats_abs_nat_div_natE<span class="main">)</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">R</span> <span class="main">≠</span></span> <span class="main">{}</span></span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> R_def <span class="dynamic dynamic">field_simps</span><span class="main">)</span> <span class="main">(</span><span class="operator">metis</span> of_nat_in_Nats<span class="main">)</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">k</span> <span class="main">∈</span></span> <span class="skolem">R</span><span>"</span></span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> Inf_nat_def1 k_def<span class="main">)</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword1 command">have</span> kR<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>real</span> <span class="skolem">k</span> <span class="main">*</span></span> sqrt <span class="numeral">2</span> <span class="main">∈</span> <span class="main">ℕ</span><span>"</span> <span class="keyword2 keyword">and</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">k</span> <span class="main">&gt;</span></span> <span class="main">0</span></span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> R_def<span class="main">)</span>
</pre>

We have already defined $k$ to be the infimum of $R$, but for this to be useful
we need to show that the set $R$ is nonempty. It then follows that
$k$ belongs to $R$ and satisfies its characteristic properties.

### Defining $k'$

The informal proof takes advantage of the typelessness of traditional mathematics
(apologies to those offended) by writing the real number $k(\sqrt2-1)$
and showing it to be a natural number: a seamless transition.
The Isabelle script begins by calling this quantity $x$ and then,
having shown it to belong to ℕ, obtains the corresponding natural number: $k'$.
Looking at blackboard carefully, we can see that a few steps have been skipped.

<pre class="source">
  <span class="keyword3 command">define</span> <span class="skolem skolem">x</span> <span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">x</span> <span class="main">≡</span> real</span> <span class="skolem">k</span> <span class="main">*</span></span> <span class="main">(</span>sqrt <span class="numeral">2</span> <span class="main">-</span> <span class="main">1</span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">x</span> <span class="main">∈</span></span> <span class="main">ℕ</span></span><span>"</span><span>
    </span><span class="keyword1 command">using</span> <span class="quoted"><span class="quoted"><span>‹</span><span class="main">0</span></span> <span class="main">&lt;</span></span> <span class="skolem">k</span><span>›</span> <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> kR right_diff_distrib' x_def<span class="main">)</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">obtain</span> <span class="skolem skolem">k'</span> <span class="keyword2 keyword">where</span> k'<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">x</span> <span class="main">=</span></span> real</span> <span class="skolem">k'</span><span>"</span><span>
    </span><span class="keyword1 command">using</span> Nats_cases <span class="keyword1 command">by</span> <span class="operator">blast</span><span>
  </span><span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">k'</span> <span class="main">&gt;</span></span> <span class="main">0</span></span><span>"</span><span>
    </span><span class="keyword1 command">using</span> <span class="quoted"><span class="quoted"><span>‹</span><span class="main">0</span></span> <span class="main">&lt;</span></span> <span class="skolem">k</span><span>›</span> k' of_nat_eq_0_iff x_def <span class="keyword1 command">by</span> <span class="operator">fastforce</span>
</pre>

### Showing $k'\in R$

We have already shown that $k'>0$, but the nontrivial part of our task
is the third line of the blackboard proof. Breaking it up into stages as shown
keeps the proof justifications simple.
We could skip some steps, when [Sledgehammer]({% post_url 2022-04-13-Sledgehammer %}) 
would obligingly find a monster proof.

<pre class="source">
  <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span>real</span> <span class="skolem">k'</span> <span class="main">*</span></span> sqrt <span class="numeral">2</span> <span class="main">=</span> <span class="numeral">2</span> <span class="main">*</span> <span class="skolem">k</span> <span class="main">-</span> <span class="skolem">k</span> <span class="main">*</span> sqrt <span class="numeral">2</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> x_def <span class="dynamic dynamic">algebra_simps</span> <span class="quasi_keyword">flip</span><span class="main main">:</span> k'<span class="main">)</span><span>
  </span><span class="keyword1 command">moreover</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span>real</span> <span class="skolem">k'</span> <span class="main">*</span></span> sqrt <span class="numeral">2</span> <span class="main">≥</span> <span class="main">0</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="operator">simp</span><span>
  </span><span class="keyword1 command">ultimately</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span>real</span> <span class="skolem">k'</span> <span class="main">*</span></span> sqrt <span class="numeral">2</span> <span class="main">∈</span> <span class="main">ℕ</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> kR<span class="main">)</span><span>
  </span><span class="keyword1 command">with</span> R_def <span class="quoted"><span class="quoted"><span>‹</span><span class="main">0</span></span> <span class="main">&lt;</span></span> <span class="skolem">k'</span><span>›</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">k'</span> <span class="main">∈</span></span> <span class="skolem">R</span><span>"</span></span><span>
    </span><span class="keyword1 command">by</span> <span there="operator">blast</span>
</pre>

### Finishing up

Once we can show $k'<k$, the result follows by the minimality of $k$.
 
<pre class="source">
  <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">x</span> <span class="main">&lt;</span></span> real</span> <span class="skolem">k</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> <span class="quoted"><span class="quoted"><span>‹</span><span class="main">0</span></span> <span class="main">&lt;</span></span> <span class="skolem">k</span><span>›</span> sqrt2_less_2 x_def<span class="main">)</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">k'</span> <span class="main">&lt;</span></span> <span class="skolem">k</span><span>"</span></span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> k'<span class="main">)</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="quoted">False</span><span>
    </span><span class="keyword1 command">using</span> <span class="quoted"><span class="quoted"><span>‹</span><span class="skolem">k'</span> <span class="main">∈</span></span> <span class="skolem">R</span><span>›</span></span> k_def linorder_not_less wellorder_Inf_le1 <span class="keyword1 command">by</span> <span class="operator">auto</span><span>
</span><span class="keyword1 command">qed</span>
</pre>

The Isabelle theory file is [available to download](/Isabelle-Examples/Sqrt2_Irrational.thy).
 
### Postscript

This proof assumes a more sophisticated background theory 
than the traditional one, which would have been a problem 30 years ago
when few proof assistants supported the real numbers.
A couple of Isabelle formalisations of the traditional proof 
[are available](https://isabelle.in.tum.de/dist/library/HOL/HOL-Examples/Sqrt.html)
and it's up to you to decide which approach is clearer.

A [previous post]({% post_url 2022-06-08-baby-descriptions %}) 
discussed reasoning about the least element in the more general context
of descriptions, but this example came from the wild (Twitter, anyway).

