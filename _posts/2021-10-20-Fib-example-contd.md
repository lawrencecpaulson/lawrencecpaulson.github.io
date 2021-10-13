---
layout: post
title:  "Introductory example: Fibonacci numbers, continued"
usemathjax: true 
tags: general, examples, Isabelle
---

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



<pre class="source">
<span class="keyword1"><span class="command">theorem</span></span> fib_gcd<span class="main">:</span> <span class="quoted"><span class="quoted">"fib <span class="main">(</span>gcd <span class="free">m</span> <span class="free">n</span><span class="main">)</span> <span class="main">=</span> gcd <span class="main">(</span>fib <span class="free">m</span><span class="main">)</span> <span class="main">(</span>fib <span class="free">n</span><span class="main">)</span>"</span></span>
<span class="keyword1"><span class="command">proof</span></span> <span class="main">(</span><span class="operator">induction</span> <span class="quoted"><span class="free">m</span></span> <span class="quoted"><span class="free">n</span></span> <span class="quasi_keyword">rule</span><span class="main"><span class="main">:</span></span> gcd_nat_induct<span class="main">)</span>
  <span class="keyword3"><span class="command">case</span></span> <span class="main">(</span>step <span class="skolem">m</span> <span class="skolem">n</span><span class="main">)</span>
  <span class="keyword1"><span class="command">then</span></span> <span class="keyword3"><span class="command">show</span></span> <span class="var"><span class="quoted"><span class="var">?case</span></span></span>
    <span class="keyword1"><span class="command">by</span></span> <span class="main">(</span><span class="operator">metis</span> gcd.commute gcd_fib_mod gcd_red_nat<span class="main">)</span>
<span class="keyword1"><span class="command">qed</span></span> <span class="operator">auto</span>
</pre>
