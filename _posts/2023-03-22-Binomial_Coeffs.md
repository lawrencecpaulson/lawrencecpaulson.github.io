---
layout: post
title:  "Small examples involving binomial coefficients"
usemathjax: true
tags: [newbies, recursion, examples, Isar, Fibonacci]
---

The [binomial coefficients](https://en.wikipedia.org/wiki/Binomial_coefficient),
which appear in the [binomial theorem](https://en.wikipedia.org/wiki/Binomial_theorem),
have numerous applications in combinatorics and the analysis of algorithms.
[Donald E Knuth](https://www-cs-faculty.stanford.edu/~knuth/) 
wrote extensively about them in his book 
[*Concrete Mathematics*](https://en.wikipedia.org/wiki/Concrete_Mathematics).
They are the elements of Pascal's triangle and satisfy a great many mathematical identities.
Let's prove some of them using Isabelle/HOL. These and many more
are available built-in.

### Warming up

Let's recall the definition of the binomial coefficient "*n* choose *k*", which denotes how many *k*-element subsets can be chosen from an *n*-element set:

$$\begin{gather*} \binom{n}{k} = \frac{n!}{k!(n-k)!}. \end{gather*}$$

There follow a number of trivial properties, such as

$$\begin{gather*} (n-k)\binom{n}{k} = n\binom{n-1}{k}. \end{gather*}$$

Slightly deeper is the following claim, 
that the sum of a row of Pascal's triangle is a power of 2:

$$\begin{gather*} \sum_{k\le n} \binom{n}{k} = 2^n. \end{gather*}$$

It's trivial for us to prove because the binomial theorem—already available in Isabelle/HOL—expresses $(x+y)^n$ in terms of binomial coefficients.
We can express the desired sum by putting $x=y=1$ in that theorem.
Observe the syntax for instantiating variables in a theorem.

<pre class="source">
<span class="keyword1 command">lemma</span> choose_row_sum<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span><span class="main">∑</span><span class="bound">k</span><span class="main">≤</span><span class="free">n</span><span class="main">.</span> <span class="free">n</span> <span class="keyword1">choose</span></span> <span class="bound">k</span><span class="main">)</span> <span class="main">=</span></span> <span class="numeral">2</span><span class="main">^</span><span class="free">n</span><span>"</span><span>
  </span><span class="keyword1 command">using</span> binomial <span class="main">[</span><span class="operator">of</span> <span class="quoted main">1</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">1</span></span><span>"</span></span> <span class="quoted free">n</span><span class="main">]</span> <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> numeral_2_eq_2<span class="main">)</span>
</pre>

Many other identities are trivial inductions. These two are hardly worth a discussion.

<pre class="source">
<span class="keyword1 command">lemma</span> sum_choose_lower<span class="main">:</span><span>
    </span><span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span><span class="main">∑</span><span class="bound">k</span><span class="main">≤</span><span class="free">n</span><span class="main">.</span> <span class="main">(</span><span class="free">r</span><span class="main">+</span></span><span class="bound">k</span><span class="main">)</span> <span class="keyword1">choose</span></span> <span class="bound">k</span><span class="main">)</span> <span class="main">=</span> Suc <span class="main">(</span><span class="free">r</span><span class="main">+</span><span class="free">n</span><span class="main">)</span> <span class="keyword1">choose</span> <span class="free">n</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">induction</span> <span class="quoted free">n</span><span class="main">)</span> <span class="operator">auto</span>
</pre>

<pre class="source">
<span class="keyword1 command">lemma</span> sum_choose_upper<span class="main">:</span><span>
    </span><span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span><span class="main">∑</span><span class="bound">k</span><span class="main">≤</span><span class="free">n</span><span class="main">.</span> <span class="bound">k</span> <span class="keyword1">choose</span></span> <span class="free">m</span><span class="main">)</span> <span class="main">=</span></span> Suc <span class="free">n</span> <span class="keyword1">choose</span> Suc <span class="free">m</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">induction</span> <span class="quoted free">n</span><span class="main">)</span> <span class="operator">auto</span>
</pre>

### Manipulating a summation

The following little identity does not require induction, since it uses
one of the identities just proved. But its first step is a little tricky:
the index variable, $k$, is replaced by $m-k$. Such manipulations
frequently require the user to tear out their hair.

<pre class="source">
<span class="keyword1 command">lemma</span> sum_choose_diagonal<span class="main">:</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">m</span><span class="main">≤</span></span><span class="free">n</span><span>"</span></span><span>
    </span><span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span><span class="main">∑</span><span class="bound">k</span><span class="main">≤</span><span class="free">m</span><span class="main">.</span> <span class="main">(</span><span class="free">n</span><span class="main">-</span></span><span class="bound">k</span><span class="main">)</span> <span class="keyword1">choose</span></span> <span class="main">(</span><span class="free">m</span><span class="main">-</span><span class="bound">k</span><span class="main">)</span><span class="main">)</span> <span class="main">=</span> Suc <span class="free">n</span> <span class="keyword1">choose</span> <span class="free">m</span><span>"</span><span>
</span><span class="keyword1 command">proof</span> <span class="operator">-</span><span>
  </span><span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span><span class="main">∑</span><span class="bound">k</span><span class="main">≤</span><span class="free">m</span><span class="main">.</span> <span class="main">(</span><span class="free">n</span><span class="main">-</span></span><span class="bound">k</span><span class="main">)</span> <span class="keyword1">choose</span></span> <span class="main">(</span><span class="free">m</span><span class="main">-</span><span class="bound">k</span><span class="main">)</span><span class="main">)</span> <span class="main">=</span> <span class="main">(</span><span class="main">∑</span><span class="bound">k</span><span class="main">≤</span><span class="free">m</span><span class="main">.</span> <span class="main">(</span><span class="free">n</span><span class="main">-</span><span class="free">m</span><span class="main">+</span><span class="bound">k</span><span class="main">)</span> <span class="keyword1">choose</span> <span class="bound">k</span><span class="main">)</span><span>"</span><span>
    </span><span class="keyword1 command">using</span> sum.atLeastAtMost_rev <span class="main">[</span><span class="operator">of</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">λ</span><span class="bound">k</span><span class="main">.</span> <span class="main">(</span><span class="free">n</span> <span class="main">-</span></span> <span class="bound">k</span><span class="main">)</span> <span class="keyword1">choose</span></span> <span class="main">(</span><span class="free">m</span> <span class="main">-</span> <span class="bound">k</span><span class="main">)</span><span>"</span> <span class="quoted main">0</span> <span class="quoted free">m</span><span class="main">]</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> atMost_atLeast0 <span class="quoted"><span class="quoted"><span>‹</span><span class="free">m</span><span class="main">≤</span></span><span class="free">n</span><span>›</span></span><span class="main">)</span><span>
  </span><span class="keyword1 command">also</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">…</span> <span class="main">=</span></span> Suc</span> <span class="main">(</span><span class="free">n</span><span class="main">-</span><span class="free">m</span><span class="main">+</span><span class="free">m</span><span class="main">)</span> <span class="keyword1">choose</span> <span class="free">m</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">rule</span> sum_choose_lower<span class="main">)</span><span>
  </span><span class="keyword1 command">also</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">…</span> <span class="main">=</span></span> Suc</span> <span class="free">n</span> <span class="keyword1">choose</span> <span class="free">m</span><span>"</span> <span class="keyword1 command">using</span> assms<span>
    </span><span class="keyword1 command">by</span> <span class="operator">simp</span><span>
  </span><span class="keyword1 command">finally</span> <span class="keyword3 command">show</span> <span class="var quoted var">?thesis</span> <span class="keyword1 command">.</span><span>
</span><span class="keyword1 command">qed</span>
</pre>

### Proving the *subset of a subset* identity

Intuitively, the identity $\binom{n}{m} \binom{m}{k} = \binom{n}{k} \binom{n-k}{m-k}$ 
concerns the number of ways to choose $k$ elements out of $m$ elements 
that were originally chosen out of $n$. 
It's equivalent to the number of ways of
immediately choosing $k$ out of $n$ times the number of ways of choosing the leftover $m-k$
elements out of the original, unwanted $n-k$ elements. Or something.
Such intuitive arguments are a nightmare to formalise, but fortunately
this proof is a fairly simple calculation.

It relies on a basic divisibility property: 
that $k!(n-k)!$ divides $n!$ provided
$k\le n$. The divisor is precisely $\binom{n}{k}$, a fact proved
in the main library. (And it doesn't follow from the definition
of $\binom{n}{k}$, but rather justifies that definition.)

Now we can prove our identity by expressing binomial coefficients in terms of factorials. It's just a chain of identities, called in Isar a
*calculational proof*.

<pre class="source">
<span class="keyword1 command">lemma</span> choose_mult_lemma<span class="main">:</span><span>
  </span><span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span><span class="main">(</span><span class="free">m</span><span class="main">+</span></span><span class="free">r</span><span class="main">+</span></span><span class="free">k</span><span class="main">)</span> <span class="keyword1">choose</span> <span class="main">(</span><span class="free">m</span><span class="main">+</span><span class="free">k</span><span class="main">)</span><span class="main">)</span> <span class="main">*</span> <span class="main">(</span><span class="main">(</span><span class="free">m</span><span class="main">+</span><span class="free">k</span><span class="main">)</span> <span class="keyword1">choose</span> <span class="free">k</span><span class="main">)</span> <span class="main">=</span> <span class="main">(</span><span class="main">(</span><span class="free">m</span><span class="main">+</span><span class="free">r</span><span class="main">+</span><span class="free">k</span><span class="main">)</span> <span class="keyword1">choose</span> <span class="free">k</span><span class="main">)</span> <span class="main">*</span> <span class="main">(</span><span class="main">(</span><span class="free">m</span><span class="main">+</span><span class="free">r</span><span class="main">)</span> <span class="keyword1">choose</span> <span class="free">m</span><span class="main">)</span><span>"</span><span>
  </span><span class="main">(</span><span class="keyword2 keyword">is</span> <span class="quoted"><span class="quoted"><span>"</span><span class="var">?lhs</span> <span class="main">=</span></span> <span class="main">_</span><span>"</span></span><span class="main">)</span><span>
</span><span class="keyword1 command">proof</span> <span class="operator">-</span><span>
  </span><span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="var">?lhs</span> <span class="main">=</span></span><span>
      </span>fact</span><span class="main">(</span><span class="free">m</span><span class="main">+</span><span class="free">r</span><span class="main">+</span><span class="free">k</span><span class="main">)</span> <span class="keyword1">div</span> <span class="main">(</span>fact<span class="main">(</span><span class="free">m</span><span class="main">+</span><span class="free">k</span><span class="main">)</span> <span class="main">*</span> fact<span class="main">(</span><span class="free">m</span><span class="main">+</span><span class="free">r</span><span class="main">-</span><span class="free">m</span><span class="main">)</span><span class="main">)</span> <span class="main">*</span> <span class="main">(</span>fact<span class="main">(</span><span class="free">m</span><span class="main">+</span><span class="free">k</span><span class="main">)</span> <span class="keyword1">div</span> <span class="main">(</span>fact <span class="free">k</span> <span class="main">*</span> fact <span class="free">m</span><span class="main">)</span><span class="main">)</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> binomial_altdef_nat<span class="main">)</span><span>
  </span><span class="keyword1 command">also</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">…</span> <span class="main">=</span></span> fact</span><span class="main">(</span><span class="free">m</span><span class="main">+</span><span class="free">r</span><span class="main">+</span><span class="free">k</span><span class="main">)</span> <span class="main">*</span> fact<span class="main">(</span><span class="free">m</span><span class="main">+</span><span class="free">k</span><span class="main">)</span> <span class="keyword1">div</span><span>
                 </span><span class="main">(</span>fact<span class="main">(</span><span class="free">m</span><span class="main">+</span><span class="free">k</span><span class="main">)</span> <span class="main">*</span> fact<span class="main">(</span><span class="free">m</span><span class="main">+</span><span class="free">r</span><span class="main">-</span><span class="free">m</span><span class="main">)</span> <span class="main">*</span> <span class="main">(</span>fact <span class="free">k</span> <span class="main">*</span> fact <span class="free">m</span><span class="main">)</span><span class="main">)</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> add_implies_diff add_le_mono1 choose_dvd diff_cancel2 div_mult_div_if_dvd<span>
        </span>le_add1 le_add2<span class="main">)</span><span>
  </span><span class="keyword1 command">also</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">…</span> <span class="main">=</span></span> fact</span><span class="main">(</span><span class="free">m</span><span class="main">+</span><span class="free">r</span><span class="main">+</span><span class="free">k</span><span class="main">)</span> <span class="keyword1">div</span> <span class="main">(</span>fact <span class="free">r</span> <span class="main">*</span> <span class="main">(</span>fact <span class="free">k</span> <span class="main">*</span> fact <span class="free">m</span><span class="main">)</span><span class="main">)</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> <span class="dynamic dynamic">algebra_simps</span> fact_fact_dvd_fact<span class="main">)</span><span>
  </span><span class="keyword1 command">also</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">…</span> <span class="main">=</span></span> <span class="main">(</span>fact</span><span class="main">(</span><span class="free">m</span><span class="main">+</span><span class="free">r</span><span class="main">+</span><span class="free">k</span><span class="main">)</span> <span class="main">*</span> fact<span class="main">(</span><span class="free">m</span><span class="main">+</span><span class="free">r</span><span class="main">)</span><span class="main">)</span> <span class="keyword1">div</span> <span class="main">(</span>fact <span class="free">r</span> <span class="main">*</span> <span class="main">(</span>fact <span class="free">k</span> <span class="main">*</span> fact <span class="free">m</span><span class="main">)</span> <span class="main">*</span> fact<span class="main">(</span><span class="free">m</span><span class="main">+</span><span class="free">r</span><span class="main">)</span><span class="main">)</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="operator">simp</span><span>
  </span><span class="keyword1 command">also</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">…</span> <span class="main">=</span></span><span>
      </span><span class="main">(</span>fact</span><span class="main">(</span><span class="free">m</span><span class="main">+</span><span class="free">r</span><span class="main">+</span><span class="free">k</span><span class="main">)</span> <span class="keyword1">div</span> <span class="main">(</span>fact <span class="free">k</span> <span class="main">*</span> fact<span class="main">(</span><span class="free">m</span><span class="main">+</span><span class="free">r</span><span class="main">)</span><span class="main">)</span> <span class="main">*</span> <span class="main">(</span>fact<span class="main">(</span><span class="free">m</span><span class="main">+</span><span class="free">r</span><span class="main">)</span> <span class="keyword1">div</span> <span class="main">(</span>fact <span class="free">r</span> <span class="main">*</span> fact <span class="free">m</span><span class="main">)</span><span class="main">)</span><span class="main">)</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">smt</span> <span class="main main">(</span>verit<span class="main main">)</span> fact_fact_dvd_fact div_mult_div_if_dvd mult.assoc mult.commute<span class="main">)</span><span>
  </span><span class="keyword1 command">finally</span> <span class="keyword3 command">show</span> <span class="var quoted var">?thesis</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> binomial_altdef_nat mult.commute<span class="main">)</span><span>
</span><span class="keyword1 command">qed</span></pre>

Above, we avoided subtraction in favour of addition,
a trick that frequently simplifies our work.
Now it's trivial to derive the "subset of a subset" identity in its
traditional form, 
$\binom{n}{m} \binom{m}{k} = \binom{n}{k} \binom{n-k}{m-k}$.

<pre class="source">
<span class="keyword1 command">lemma</span> choose_mult<span class="main">:</span><span>
  </span><span class="quoted"><span class="quoted"><span>"</span><span class="free">k</span> <span class="main">≤</span></span> <span class="free">m</span> <span class="main">⟹</span> <span class="free">m</span> <span class="main">≤</span></span> <span class="free">n</span> <span class="main">⟹</span> <span class="main">(</span><span class="free">n</span> <span class="keyword1">choose</span> <span class="free">m</span><span class="main">)</span> <span class="main">*</span> <span class="main">(</span><span class="free">m</span> <span class="keyword1">choose</span> <span class="free">k</span><span class="main">)</span> <span class="main">=</span> <span class="main">(</span><span class="free">n</span> <span class="keyword1">choose</span> <span class="free">k</span><span class="main">)</span> <span class="main">*</span> <span class="main">(</span><span class="main">(</span><span class="free">n</span> <span class="main">-</span> <span class="free">k</span><span class="main">)</span> <span class="keyword1">choose</span> <span class="main">(</span><span class="free">m</span> <span class="main">-</span> <span class="free">k</span><span class="main">)</span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword1 command">using</span> choose_mult_lemma <span class="main">[</span><span class="operator">of</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">m</span><span class="main">-</span></span><span class="free">k</span><span>"</span></span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">n</span><span class="main">-</span></span><span class="free">m</span><span>"</span></span> <span class="quoted free">k</span><span class="main">]</span> <span class="keyword1 command">by</span> <span class="operator">simp</span>
</pre>

### An easy tricky proof

In *Concrete Mathematics*, the authors remark 

> There is a way to partially sum the row elements [of Pascal's triangle] if they have been multiplied by their distance from the centre.

They give the following formula (numbered 5.18):

$$\begin{gather*}
\sum_{k\le m}\binom{r}{k}\left(\frac{r}{2}-k\right) 
= \frac{m+1}{2}\binom{r}{m+1}.
\end{gather*}$$

And they remark, "this formula is easily verified by induction on *m*".
Dangerous words. They certainly provoked me to try formulaic 
induction/simplification steps that exploded the formula into chaos.
When that happens, it's best to try to work out the steps on paper
first. I eventually arrived at the following, which quite possibly
is the proof they omitted.

<pre class="source">
<span class="keyword1 command">lemma</span> choose_row_sum_weighted<span class="main">:</span><span>
  </span><span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span><span class="main">∑</span><span class="bound">k</span><span class="main">≤</span><span class="free">m</span><span class="main">.</span> <span class="main">(</span><span class="free">r</span> <span class="keyword1">choose</span></span> <span class="bound">k</span><span class="main">)</span> <span class="main">*</span></span> <span class="main">(</span><span class="free">r</span><span class="main">/</span><span class="numeral">2</span> <span class="main">-</span> <span class="bound">k</span><span class="main">)</span><span class="main">)</span> <span class="main">=</span> <span class="main">(</span>Suc <span class="free">m</span><span class="main">)</span><span class="main">/</span><span class="numeral">2</span> <span class="main">*</span> <span class="main">(</span><span class="free">r</span> <span class="keyword1">choose</span> <span class="main">(</span>Suc <span class="free">m</span><span class="main">)</span><span class="main">)</span><span>"</span><span>
</span><span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">induction</span> <span class="quoted free">m</span><span class="main">)</span><span>
  </span><span class="keyword3 command">case</span> 0 <span class="keyword3 command">show</span> <span class="var quoted var">?case</span> <span class="keyword1 command">by</span> <span class="operator">simp</span><span>
</span><span class="keyword1 command">next</span><span>
  </span><span class="keyword3 command">case</span> <span class="main">(</span>Suc <span class="skolem">m</span><span class="main">)</span><span>
  </span><span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span><span class="main">∑</span><span class="bound">k</span><span class="main">≤</span>Suc</span> <span class="skolem">m</span><span class="main">.</span> real</span> <span class="main">(</span><span class="free">r</span> <span class="keyword1">choose</span> <span class="bound">k</span><span class="main">)</span> <span class="main">*</span> <span class="main">(</span><span class="free">r</span><span class="main">/</span><span class="numeral">2</span> <span class="main">-</span> <span class="bound">k</span><span class="main">)</span><span class="main">)</span><span>
      </span><span class="main">=</span> <span class="main">(</span><span class="main">(</span><span class="free">r</span> <span class="keyword1">choose</span> Suc <span class="skolem">m</span><span class="main">)</span> <span class="main">*</span> <span class="main">(</span><span class="free">r</span><span class="main">/</span><span class="numeral">2</span> <span class="main">-</span> <span class="main">(</span>Suc <span class="skolem">m</span><span class="main">)</span><span class="main">)</span><span class="main">)</span> <span class="main">+</span> <span class="main">(</span>Suc <span class="skolem">m</span><span class="main">)</span> <span class="main">/</span> <span class="numeral">2</span> <span class="main">*</span> <span class="main">(</span><span class="free">r</span> <span class="keyword1">choose</span> Suc <span class="skolem">m</span><span class="main">)</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> Suc<span class="main">)</span><span>
  </span><span class="keyword1 command">also</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">…</span> <span class="main">=</span></span> <span class="main">(</span><span class="free">r</span> <span class="keyword1">choose</span></span> Suc <span class="skolem">m</span><span class="main">)</span> <span class="main">*</span> <span class="main">(</span>real <span class="free">r</span> <span class="main">-</span> <span class="main">(</span>Suc <span class="skolem">m</span><span class="main">)</span><span class="main">)</span> <span class="main">/</span> <span class="numeral">2</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> <span class="dynamic dynamic">field_simps</span><span class="main">)</span><span>
  </span><span class="keyword1 command">also</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">…</span> <span class="main">=</span></span> Suc</span> <span class="main">(</span>Suc <span class="skolem">m</span><span class="main">)</span> <span class="main">/</span> <span class="numeral">2</span> <span class="main">*</span> <span class="main">(</span><span class="free">r</span> <span class="keyword1">choose</span> Suc <span class="main">(</span>Suc <span class="skolem">m</span><span class="main">)</span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">cases</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">r</span> <span class="main">≥</span></span> Suc</span> <span class="skolem">m</span><span>"</span><span class="main">)</span><span>
    </span><span class="keyword3 command">case</span> True <span class="keyword1 command">with</span> binomial_absorb_comp<span class="main">[</span><span class="operator">of</span> <span class="quoted free">r</span> <span class="quoted"><span class="quoted"><span>"</span>Suc</span> <span class="skolem">m</span><span>"</span></span><span class="main">]</span> <span class="keyword3 command">show</span> <span class="var quoted var">?thesis</span><span>
      </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> binomial_absorption mult.commute of_nat_diff of_nat_mult times_divide_eq_left<span class="main">)</span><span>
  </span><span class="keyword1 command">qed</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> binomial_eq_0<span class="main">)</span><span>
  </span><span class="keyword1 command">finally</span> <span class="keyword3 command">show</span> <span class="var quoted var">?case</span> <span class="keyword1 command">.</span><span>
</span><span class="keyword1 command">qed</span>
</pre>

I can't help but remark that with Certain Other Proof Assistants, 
working out the proof first on paper is standard practice.
Then what value are they getting from their so-called assistant?

### An identity involving Fibonacci numbers

Every time you turn around, the [Fibonacci numbers](https://www.techtarget.com/whatis/definition/Fibonacci-sequence) 
pop up again:

$$\begin{gather*}
\sum_{k\le m}\binom{n-k}{k} = F_{n+1}
\end{gather*}$$

We've seen Fibonacci numbers in a previous post.
Isabelle accepts the recursive definition,

$$\begin{align} F_0 &= 0\\ F_1 &= 1\\ F_{n+2} &= F_n + F_{n+1}, \end{align}$$

[more-or-less verbatim]({% post_url 2021-10-13-Fib-example %}).

We have also seen that when you have to prove something about a recursive function, it's often best to use the induction rule that Isabelle supplies with your function definition. And that is the case here. 

First, we need a couple of trivial lemmas to let us 
adjust the upper bound of the sum, 
deleting a null term and shifting everything down. 

<pre class="source">
<span class="keyword1 command">lemma</span> sum_drop_zero<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span><span class="main">∑</span><span class="bound">k</span><span class="main">≤</span>Suc</span> <span class="free">n</span><span class="main">.</span> <span class="keyword1">if</span></span> <span class="main">0</span><span class="main">&lt;</span><span class="bound">k</span> <span class="keyword1">then</span> <span class="main">(</span><span class="free">f</span> <span class="main">(</span><span class="bound">k</span> <span class="main">-</span> <span class="main">1</span><span class="main">)</span><span class="main">)</span> <span class="keyword1">else</span> <span class="main">0</span><span class="main">)</span> <span class="main">=</span> <span class="main">(</span><span class="main">∑</span><span class="bound">j</span><span class="main">≤</span><span class="free">n</span><span class="main">.</span> <span class="free">f</span> <span class="bound">j</span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">induction</span> <span class="quoted free">n</span><span class="main">)</span> <span class="operator">auto</span>
</pre>

<pre class="source">
<span class="keyword1 command">lemma</span> sum_choose_drop_zero<span class="main">:</span><span>
  </span><span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span><span class="main">∑</span><span class="bound">k</span><span class="main">≤</span>Suc</span> <span class="free">n</span><span class="main">.</span> <span class="keyword1">if</span></span> <span class="bound">k</span> <span class="main">=</span> <span class="main">0</span> <span class="keyword1">then</span> <span class="main">0</span> <span class="keyword1">else</span> <span class="main">(</span>Suc <span class="free">n</span> <span class="main">-</span> <span class="bound">k</span><span class="main">)</span> <span class="keyword1">choose</span> <span class="main">(</span><span class="bound">k</span> <span class="main">-</span> <span class="main">1</span><span class="main">)</span><span class="main">)</span> <span class="main">=</span><span>
    </span><span class="main">(</span><span class="main">∑</span><span class="bound">j</span><span class="main">≤</span><span class="free">n</span><span class="main">.</span> <span class="main">(</span><span class="free">n</span><span class="main">-</span><span class="bound">j</span><span class="main">)</span> <span class="keyword1">choose</span> <span class="bound">j</span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">rule</span> trans <span class="main main">[</span><span class="operator">OF</span> sum.cong sum_drop_zero<span class="main main">]</span><span class="main">)</span> <span class="operator">auto</span>
</pre>

Armed with this fact, the identity is easy to prove.

<pre class="source">
<span class="keyword1 command">lemma</span> ne_diagonal_fib<span class="main">:</span><span>
   </span><span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span><span class="main">∑</span><span class="bound">k</span><span class="main">≤</span><span class="free">n</span><span class="main">.</span> <span class="main">(</span><span class="free">n</span><span class="main">-</span></span><span class="bound">k</span><span class="main">)</span> <span class="keyword1">choose</span></span> <span class="bound">k</span><span class="main">)</span> <span class="main">=</span> fib <span class="main">(</span>Suc <span class="free">n</span><span class="main">)</span><span>"</span><span>
</span><span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">induction</span> <span class="quoted free">n</span> <span class="quasi_keyword">rule</span><span class="main main">:</span> fib.induct<span class="main">)</span><span>
  </span><span class="keyword3 command">case</span> 1 <span class="keyword3 command">show</span> <span class="var quoted var">?case</span> <span class="keyword1 command">by</span> <span class="operator">simp</span><span>
</span><span class="keyword1 command">next</span><span>
  </span><span class="keyword3 command">case</span> 2 <span class="keyword3 command">show</span> <span class="var quoted var">?case</span> <span class="keyword1 command">by</span> <span class="operator">simp</span><span>
</span><span class="keyword1 command">next</span><span>
  </span><span class="keyword3 command">case</span> <span class="main">(</span>3 <span class="skolem">n</span><span class="main">)</span><span>
  </span><span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span><span class="main">∑</span><span class="bound">k</span><span class="main">≤</span>Suc</span> <span class="skolem">n</span><span class="main">.</span> Suc</span> <span class="main">(</span>Suc <span class="skolem">n</span><span class="main">)</span> <span class="main">-</span> <span class="bound">k</span> <span class="keyword1">choose</span> <span class="bound">k</span><span class="main">)</span> <span class="main">=</span><span>
        </span><span class="main">(</span><span class="main">∑</span><span class="bound">k</span><span class="main">≤</span>Suc <span class="skolem">n</span><span class="main">.</span> <span class="main">(</span>Suc <span class="skolem">n</span> <span class="main">-</span> <span class="bound">k</span> <span class="keyword1">choose</span> <span class="bound">k</span><span class="main">)</span> <span class="main">+</span> <span class="main">(</span><span class="keyword1">if</span> <span class="bound">k</span><span class="main">=</span><span class="main">0</span> <span class="keyword1">then</span> <span class="main">0</span> <span class="keyword1">else</span> <span class="main">(</span>Suc <span class="skolem">n</span> <span class="main">-</span> <span class="bound">k</span> <span class="keyword1">choose</span> <span class="main">(</span><span class="bound">k</span> <span class="main">-</span> <span class="main">1</span><span class="main">)</span><span class="main">)</span><span class="main">)</span><span class="main">)</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">rule</span> sum.cong<span class="main">)</span> <span class="main">(</span><span class="operator">simp_all</span> <span class="quasi_keyword">add</span><span class="main main">:</span> choose_reduce_nat<span class="main">)</span><span>
  </span><span class="keyword1 command">also</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">…</span> <span class="main">=</span></span> <span class="main">(</span><span class="main">∑</span><span class="bound">k</span><span class="main">≤</span>Suc</span> <span class="skolem">n</span><span class="main">.</span> Suc <span class="skolem">n</span> <span class="main">-</span> <span class="bound">k</span> <span class="keyword1">choose</span> <span class="bound">k</span><span class="main">)</span> <span class="main">+</span><span>
                   </span><span class="main">(</span><span class="main">∑</span><span class="bound">k</span><span class="main">≤</span>Suc <span class="skolem">n</span><span class="main">.</span> <span class="keyword1">if</span> <span class="bound">k</span><span class="main">=</span><span class="main">0</span> <span class="keyword1">then</span> <span class="main">0</span> <span class="keyword1">else</span> <span class="main">(</span>Suc <span class="skolem">n</span> <span class="main">-</span> <span class="bound">k</span> <span class="keyword1">choose</span> <span class="main">(</span><span class="bound">k</span> <span class="main">-</span> <span class="main">1</span><span class="main">)</span><span class="main">)</span><span class="main">)</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> sum.distrib<span class="main">)</span><span>
  </span><span class="keyword1 command">also</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">…</span> <span class="main">=</span></span> <span class="main">(</span><span class="main">∑</span><span class="bound">k</span><span class="main">≤</span>Suc</span> <span class="skolem">n</span><span class="main">.</span> Suc <span class="skolem">n</span> <span class="main">-</span> <span class="bound">k</span> <span class="keyword1">choose</span> <span class="bound">k</span><span class="main">)</span> <span class="main">+</span> <span class="main">(</span><span class="main">∑</span><span class="bound">j</span><span class="main">≤</span><span class="skolem">n</span><span class="main">.</span> <span class="skolem">n</span> <span class="main">-</span> <span class="bound">j</span> <span class="keyword1">choose</span> <span class="bound">j</span><span class="main">)</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> sum_choose_drop_zero<span class="main">)</span><span>
  </span><span class="keyword1 command">finally</span> <span class="keyword3 command">show</span> <span class="var quoted var">?case</span> <span class="keyword1 command">using</span> 3<span>
    </span><span class="keyword1 command">by</span> <span class="operator">simp</span><span>
</span><span class="keyword1 command">qed</span>
</pre>

### Postscript

As usual, the Isabelle  theory is [available to download](/Isabelle-Examples/Binomial_Coeffs.thy).

Knuth notes that we can generalise binomial coefficients so that the top number is real or complex,
and this general version is also available in Isabelle/HOL.

There's even an [introduction to binomial coefficients](https://nrich.maths.org/7713) aimed at younger mathematicians.
