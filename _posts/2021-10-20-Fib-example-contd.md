---
layout: post
title:  "More on Fibonacci numbers, with equational reasoning"
usemathjax: true 
tags: general, examples, Isabelle, Fibonacci, gcd
---

The [previous post]({% post_url 2021-10-13-Fib-example %}) introduced a definition of the Fibonacci function along with some simple proofs by induction. We continue our tour with examples of *equational reasoning*.
Chains of equalities and inequalities are common in proofs and a proof assistant should allow them to be written. 


Today our objective is a result involving greatest common divisors.
The lemma below is proved by cases on whether the natural number *m* equals zero or not. The former case is trivial and in the latter case, *m* is written as *Suc k*:

<pre class="source">
<span class="keyword1"><span class="command">lemma</span></span> gcd_fib_add<span class="main">:</span> <span class="quoted"><span class="quoted">"gcd <span class="main">(</span>fib <span class="free">m</span><span class="main">)</span> <span class="main">(</span>fib <span class="main">(</span><span class="free">n</span> <span class="main">+</span> <span class="free">m</span><span class="main">)</span><span class="main">)</span> <span class="main">=</span> gcd <span class="main">(</span>fib <span class="free">m</span><span class="main">)</span> <span class="main">(</span>fib <span class="free">n</span><span class="main">)</span>"</span></span>
<span class="keyword1"><span class="command">proof</span></span> <span class="main">(</span><span class="operator">cases</span> <span class="quoted"><span class="free">m</span></span><span class="main">)</span>
  <span class="keyword3"><span class="command">case</span></span> 0
  <span class="keyword1"><span class="command">then</span></span> <span class="keyword3"><span class="command">show</span></span> <span class="var"><span class="quoted"><span class="var">?thesis</span></span></span> <span class="keyword1"><span class="command">by</span></span> <span class="operator">simp</span>
<span class="keyword1"><span class="command">next</span></span>
  <span class="keyword3"><span class="command">case</span></span> <span class="main">(</span>Suc <span class="skolem">k</span><span class="main">)</span>
  <span class="keyword1"><span class="command">have</span></span> <span class="quoted"><span class="quoted">"gcd <span class="main">(</span>fib <span class="free">m</span><span class="main">)</span> <span class="main">(</span>fib <span class="main">(</span><span class="free">n</span> <span class="main">+</span> <span class="free">m</span><span class="main">)</span><span class="main">)</span>
           <span class="main">=</span> gcd <span class="main">(</span>fib <span class="skolem">k</span> <span class="main">*</span> fib <span class="free">n</span><span class="main">)</span> <span class="main">(</span>fib <span class="main">(</span>Suc <span class="skolem">k</span><span class="main">)</span><span class="main">)</span>"</span></span>
    <span class="keyword1"><span class="command">by</span></span> <span class="main">(</span><span class="operator">metis</span> Suc fib_add gcd.commute gcd_add_mult mult.commute<span class="main">)</span>
  <span class="keyword1"><span class="command">also</span></span> <span class="keyword1"><span class="command">have</span></span> <span class="quoted"><span class="quoted">"<span class="main">…</span> <span class="main">=</span> gcd <span class="main">(</span>fib <span class="free">n</span><span class="main">)</span> <span class="main">(</span>fib <span class="main">(</span>Suc <span class="skolem">k</span><span class="main">)</span><span class="main">)</span>"</span></span>
    <span class="keyword1"><span class="command">using</span></span> coprime_commute coprime_fib_Suc gcd_mult_left_left_cancel <span class="keyword1"><span class="command">by</span></span> <span class="operator">blast</span>
  <span class="keyword1"><span class="command">also</span></span> <span class="keyword1"><span class="command">have</span></span> <span class="quoted"><span class="quoted">"<span class="main">…</span> <span class="main">=</span> gcd <span class="main">(</span>fib <span class="free">m</span><span class="main">)</span> <span class="main">(</span>fib <span class="free">n</span><span class="main">)</span>"</span></span>
    <span class="keyword1"><span class="command">using</span></span> Suc <span class="keyword1"><span class="command">by</span></span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main"><span class="main">:</span></span> <span class="dynamic"><span class="dynamic">ac_simps</span></span><span class="main">)</span>
  <span class="keyword1"><span class="command">finally</span></span> <span class="keyword3"><span class="command">show</span></span> <span class="var"><span class="quoted"><span class="var">?thesis</span></span></span> <span class="keyword1"><span class="command">.</span></span>
<span class="keyword1"><span class="command">qed</span></span>
</pre>

Less usual but convenient is equational reasoning within another expression. In the little proof below, the left hand side of the desired identity is transformed using the addition law proved in the [previous post]({% post_url 2021-10-13-Fib-example %}). Then a subexpression of the result is simplified to *n*. Chaining the two steps (which is the purpose of `finally`) yield the desired result.

<pre class="source">
<span class="keyword1"><span class="command">lemma</span></span> gcd_fib_diff<span class="main">:</span> <span class="quoted"><span class="quoted">"gcd <span class="main">(</span>fib <span class="free">m</span><span class="main">)</span> <span class="main">(</span>fib <span class="main">(</span><span class="free">n</span> <span class="main">-</span> <span class="free">m</span><span class="main">)</span><span class="main">)</span> <span class="main">=</span> gcd <span class="main">(</span>fib <span class="free">m</span><span class="main">)</span> <span class="main">(</span>fib <span class="free">n</span><span class="main">)</span>"</span></span> <span class="keyword2"><span class="keyword">if</span></span> <span class="quoted"><span class="quoted">"<span class="free">m</span> <span class="main">≤</span> <span class="free">n</span>"</span></span>
<span class="keyword1"><span class="command">proof</span></span> <span class="operator">-</span>
  <span class="keyword1"><span class="command">have</span></span> <span class="quoted"><span class="quoted">"gcd <span class="main">(</span>fib <span class="free">m</span><span class="main">)</span> <span class="main">(</span>fib <span class="main">(</span><span class="free">n</span> <span class="main">-</span> <span class="free">m</span><span class="main">)</span><span class="main">)</span> <span class="main">=</span> gcd <span class="main">(</span>fib <span class="free">m</span><span class="main">)</span> <span class="main">(</span>fib <span class="main">(</span><span class="free">n</span> <span class="main">-</span> <span class="free">m</span> <span class="main">+</span> <span class="free">m</span><span class="main">)</span><span class="main">)</span>"</span></span>
    <span class="keyword1"><span class="command">by</span></span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main"><span class="main">:</span></span> gcd_fib_add<span class="main">)</span>
  <span class="keyword1"><span class="command">also</span></span> <span class="keyword1"><span class="command">from</span></span> <span class="quoted"><span class="quoted">‹<span class="free">m</span> <span class="main">≤</span> <span class="free">n</span>›</span></span> <span class="keyword1"><span class="command">have</span></span> <span class="quoted"><span class="quoted">"<span class="free">n</span> <span class="main">-</span> <span class="free">m</span> <span class="main">+</span> <span class="free">m</span> <span class="main">=</span> <span class="free">n</span>"</span></span>
    <span class="keyword1"><span class="command">by</span></span> <span class="operator">simp</span>
  <span class="keyword1"><span class="command">finally</span></span> <span class="keyword3"><span class="command">show</span></span> <span class="var"><span class="quoted"><span class="var">?thesis</span></span></span> <span class="keyword1"><span class="command">.</span></span>
<span class="keyword1"><span class="command">qed</span></span>
</pre>


Another example of chaining equalities involving subexpressions appears below. Operating on a subexpression eliminates the need to copy out the entire context. The ellipsis (…) refers to the previous right-hand side. It works and is clear but I confess this is not my style.


<pre class="source">
<span class="keyword1"><span class="command">lemma</span></span> gcd_fib_mod<span class="main">:</span> <span class="quoted"><span class="quoted">"gcd <span class="main">(</span>fib <span class="free">m</span><span class="main">)</span> <span class="main">(</span>fib <span class="main">(</span><span class="free">n</span> <span class="keyword1">mod</span> <span class="free">m</span><span class="main">)</span><span class="main">)</span> <span class="main">=</span> gcd <span class="main">(</span>fib <span class="free">m</span><span class="main">)</span> <span class="main">(</span>fib <span class="free">n</span><span class="main">)</span>"</span></span> <span class="keyword2"><span class="keyword">if</span></span> <span class="quoted"><span class="quoted">"<span class="main">0</span> <span class="main">&lt;</span> <span class="free">m</span>"</span></span>
<span class="keyword1"><span class="command">proof</span></span> <span class="main">(</span><span class="operator">induction</span> <span class="quoted"><span class="free">n</span></span> <span class="quasi_keyword">rule</span><span class="main"><span class="main">:</span></span> less_induct<span class="main">)</span>
  <span class="keyword3"><span class="command">case</span></span> <span class="main">(</span>less <span class="skolem">n</span><span class="main">)</span>
  <span class="keyword3"><span class="command">show</span></span> <span class="var"><span class="quoted"><span class="var">?case</span></span></span>
  <span class="keyword1"><span class="command">proof</span></span> <span class="operator">-</span>
    <span class="keyword1"><span class="command">have</span></span> <span class="quoted"><span class="quoted">"<span class="skolem">n</span> <span class="keyword1">mod</span> <span class="free">m</span> <span class="main">=</span> <span class="main">(</span><span class="keyword1">if</span> <span class="skolem">n</span> <span class="main">&lt;</span> <span class="free">m</span> <span class="keyword1">then</span> <span class="skolem">n</span> <span class="keyword1">else</span> <span class="main">(</span><span class="skolem">n</span> <span class="main">-</span> <span class="free">m</span><span class="main">)</span> <span class="keyword1">mod</span> <span class="free">m</span><span class="main">)</span>"</span></span>
      <span class="keyword1"><span class="command">by</span></span> <span class="main">(</span><span class="operator">rule</span> mod_if<span class="main">)</span>
    <span class="keyword1"><span class="command">also</span></span> <span class="keyword1"><span class="command">have</span></span> <span class="quoted"><span class="quoted">"gcd <span class="main">(</span>fib <span class="free">m</span><span class="main">)</span> <span class="main">(</span>fib <span class="main">…</span><span class="main">)</span> <span class="main">=</span> gcd <span class="main">(</span>fib <span class="free">m</span><span class="main">)</span> <span class="main">(</span>fib <span class="skolem">n</span><span class="main">)</span>"</span></span>
      <span class="keyword1"><span class="command">using</span></span> gcd_fib_diff less.IH that <span class="keyword1"><span class="command">by</span></span> <span class="operator">fastforce</span>
    <span class="keyword1"><span class="command">finally</span></span> <span class="keyword3"><span class="command">show</span></span> <span class="var"><span class="quoted"><span class="var">?thesis</span></span></span> <span class="keyword1"><span class="command">.</span></span>
  <span class="keyword1"><span class="command">qed</span></span>
<span class="keyword1"><span class="command">qed</span></span>
</pre>


The work that we have done here and in the previous post finally takes us to our conclusion, an amusing theorem relating Fibonacci numbers and greatest common divisors.
A clever step below is the use of `gcd_nat_induct`, which refers to an induction principle for the GCD function. In the induction step, in order to prove $P(m,n)$ for a given property $P$, we have the induction hypothesis $P(n, m \bmod n)$ for all $n>0$. Here it follows immediately with the help of the previous lemma and a fact from Isabelle's built-in GCD library.

<pre class="source">
<span class="keyword1"><span class="command">theorem</span></span> fib_gcd<span class="main">:</span> <span class="quoted"><span class="quoted">"fib <span class="main">(</span>gcd <span class="free">m</span> <span class="free">n</span><span class="main">)</span> <span class="main">=</span> gcd <span class="main">(</span>fib <span class="free">m</span><span class="main">)</span> <span class="main">(</span>fib <span class="free">n</span><span class="main">)</span>"</span></span>
<span class="keyword1"><span class="command">proof</span></span> <span class="main">(</span><span class="operator">induction</span> <span class="quoted"><span class="free">m</span></span> <span class="quoted"><span class="free">n</span></span> <span class="quasi_keyword">rule</span><span class="main"><span class="main">:</span></span> gcd_nat_induct<span class="main">)</span>
  <span class="keyword3"><span class="command">case</span></span> <span class="main">(</span>step <span class="skolem">m</span> <span class="skolem">n</span><span class="main">)</span>
  <span class="keyword1"><span class="command">then</span></span> <span class="keyword3"><span class="command">show</span></span> <span class="var"><span class="quoted"><span class="var">?case</span></span></span>
    <span class="keyword1"><span class="command">by</span></span> <span class="main">(</span><span class="operator">metis</span> gcd.commute gcd_fib_mod gcd_red_nat<span class="main">)</span>
<span class="keyword1"><span class="command">qed</span></span> <span class="operator">auto</span>
</pre>

The proofs presented in this post are due to Gertrud Bauer.
 