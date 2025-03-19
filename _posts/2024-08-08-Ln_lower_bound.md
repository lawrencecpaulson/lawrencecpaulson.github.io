---
layout: post
title: A tricky lower bound proof
usemathjax: true 
tags: [examples, Isar, formalised mathematics, analysis]
---
The [previous post]({% post_url 2024-07-25-Numeric_types %}) concerned exact numerical calculations, culminating in an example of establishing – automatically – 
a numerical lower bound for a simple mathematical formula.
Although automation is the key to the success of formal verification,
a numerical approach is not always good enough. In that example,
we could get three significant digits quickly, four significant digits slowly
and the exact lower bound never.
As every calculus student knows, 
to locate a minimum or maximum you take the derivative
and solve for the point at which it vanishes. 
The desired property can then be shown using the main value theorem.
Let's do it!

### A simple problem with surprising complications

Our task is simply to find the minimum of the function $x\ln x$
for $x\ge0$. And the first question is whether $x\ln x$ is even **defined**
when $x=0$. A purist would say that it is not, because $\ln 0$ is undefined
and multiplying $\ln 0$ by $0$ does not help matters.
However, most mathematicians would say that $x\ln x$ has a *removable singularity* at zero.
That means that we can define it at the singularity so that it is continuous.
The function certainly looks continuous:

<img src="/images/plot_x_ln_x.png" alt="graph of the function x ln x" width="400"/>

The derivative of $x\ln x$ is $\ln x+1$, which goes to zero when
$x=1/e$. At that point, $x\ln x$ achieves its minimum, namely $-1/e$.
Proving this fact formally, for all $x\ge0$, is tricky because 
that derivative is certainly undefined when $x=0$.
The way around the problem involves proving that $x\ln x$ is continuous for all $x\ge0$.

### Proving continuity

We prove the continuity of $x\ln x$ in separate stages: first, simply for $x=0$.

<pre class="source">
<span class="keyword1 command">lemma</span> continuous_at_0<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>continuous</span> <span class="main">(</span>at_right</span> <span class="main">0</span><span class="main">)</span> <span class="main">(</span><span class="main">λ</span><span class="bound">x</span><span class="main">::</span>real<span class="main">.</span> <span class="bound">x</span> <span class="main">*</span> ln <span class="bound">x</span><span class="main">)"
  </span><span class="keyword1 command">unfolding</span> continuous_within <span class="keyword1 command">by</span> <span class="operator">real_asymp</span>
</pre>

Unfolding `continuous_within` reduces the continuity claim to the limit claim
$x\ln x \longrightarrow 0\ln 0$, which of course is simply 
$x\ln x\longrightarrow0$. Such limits are trivially proved by
Manuel Eberl's wonderful [`real_asymp` proof method](http://cl-informatik.uibk.ac.at/users/meberl//pubs/real_asymp.html), 
which will surely be the subject
of a future blogpost.
From this result, we can quickly prove continuity for all $x\ge0$.
Incorporating the zero case requires a little black magic (the topological definition of continuity), while the non-zero case is straightforward.


<pre class="source">
<span class="keyword1 command">lemma</span> continuous_nonneg<span class="main">: 
  </span><span class="keyword2 keyword">fixes</span> <span class="free">x</span><span class="main">::</span><span class="quoted">real
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">≥</span></span> <span class="main">0</span>"
  </span><span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span>continuous</span> <span class="main">(</span><span class="keyword1">at</span></span> <span class="free">x</span> <span class="keyword1">within</span> <span class="main">{</span><span class="main">0</span><span class="main">..}</span><span class="main">)</span> <span class="main">(</span><span class="main">λ</span><span class="bound">x</span><span class="main">.</span> <span class="bound">x</span> <span class="main">*</span> ln <span class="bound">x</span><span class="main">)"
</span><span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">cases</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">=</span></span> <span class="main">0</span>"</span><span class="main">)
  </span><span class="keyword3 command">case</span> True <span class="keyword1 command">with</span> continuous_at_0 <span class="keyword3 command">show</span> <span class="var quoted var">?thesis
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">force</span> <span class="quasi_keyword">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> continuous_within_topological less_eq_real_def<span class="main">)
</span><span class="keyword1 command">qed</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">intro</span><span class="main main">!</span><span class="main main">:</span> <span class="dynamic dynamic">continuous_intros</span><span class="main">)</span>
</pre>

This result is then repackaged in a more convenient form for later use,
replacing the "at-within" filter by the obvious closed half-interval.
It would be preferable to incorporate the two lemmas above into the body
of `continuous_on_x_ln`; I have split them up here simply to ease the presentation.


<pre class="source">
<span class="keyword1 command">lemma</span> continuous_on_x_ln<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>continuous_on</span> <span class="main">{</span></span><span class="main">0</span><span class="main">..}</span> <span class="main">(</span><span class="main">λ</span><span class="bound">x</span><span class="main">::</span>real<span class="main">.</span> <span class="bound">x</span> <span class="main">*</span> ln <span class="bound">x</span><span class="main">)"
  </span><span class="keyword1 command">unfolding</span> continuous_on_eq_continuous_within
  <span class="keyword1 command">using</span> continuous_nonneg <span class="keyword1 command">by</span> <span class="operator">blast</span>
</pre>

*Remark*: the identical proof works for the continuity of the function $x\sin(1/x)$, 
but not of $x\exp(1/x)$, even though all three functions 
have a singularity at $x=0$. What is the essential difference?

### Proving the lower bound claim

The first step is to prove that the derivative of $x\ln x$
is indeed $\ln x+1$.
In Isabelle/HOL, calculating a derivative is easy.
If you know the derivative already (perhaps from a computer algebra system), 
then verifying the result is even easier.
The technique, already illustrated in an [earlier post]({% post_url 2022-02-16-Irrationals%}),
relies on Isabelle's inbuilt Prolog-like proof calculus.
Repeated application of rules from the list `derivative_eq_intros`
constructs the derivative and sometimes can simplify it 
or prove that it equals a derivative already supplied.

<pre class="source">
<span class="keyword1 command">lemma</span> xln_deriv<span class="main">:
  </span><span class="keyword2 keyword">fixes</span> <span class="free">x</span><span class="main">::</span><span class="quoted">real
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">&gt;</span></span> <span class="main">0</span>"
  </span><span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span><span class="main">(</span><span class="main">λ</span><span class="bound">u</span><span class="main">.</span> <span class="bound">u</span> <span class="main">*</span></span> ln</span><span class="main">(</span><span class="bound">u</span><span class="main">)</span><span class="main">)</span> <span class="keyword1">has_real_derivative</span> ln <span class="free">x</span> <span class="main">+</span> <span class="main">1</span><span class="main">)</span> <span class="main">(</span><span class="keyword1">at</span> <span class="free">x</span><span class="main">)"
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">rule</span> <span class="dynamic dynamic">derivative_eq_intros</span> refl <span class="main keyword3">|</span> <span class="operator">use</span> assms <span class="keyword2 keyword quasi_keyword">in</span> <span class="operator">force</span><span class="main">)</span><span class="main keyword3">+</span>
</pre>

We will use this derivative in the main proof, 
which for clarity is presented in chunks.
First, here's the theorem statement itself:

<pre class="source">
<span class="keyword1 command">theorem</span> x_ln_lowerbound<span class="main">:
  </span><span class="keyword2 keyword">fixes</span> <span class="free">x</span><span class="main">::</span><span class="quoted">real
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">≥</span></span> <span class="main">0</span>"
  </span><span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">*</span></span> ln</span><span class="main">(</span><span class="free">x</span><span class="main">)</span> <span class="main">≥</span> <span class="main">-</span><span class="main">1</span> <span class="main">/</span> exp <span class="main">1"
</span><span class="keyword1 command">proof</span> <span class="operator">-</span>
</pre>

Next, define `xmin` (the $x$-value of the minimum) to be $1/e$,
then show that it is positive, a fact needed later.

<pre class="source">
  <span class="keyword3 command">define</span> <span class="skolem skolem">xmin</span><span class="main">::</span><span class="quoted">real</span> <span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">xmin</span> <span class="main">≡</span> <span class="main">1</span></span> <span class="main">/</span></span> exp <span class="main">1"
  </span><span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">xmin</span> <span class="main">&gt;</span></span> <span class="main">0</span>"
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> xmin_def<span class="main">)</span>
</pre>

The claimed result requires a case analysis. 
The nontrivial cases are $0\le x<1/e$ and $1/e<x$.
In the first case, the point is that $\ln x+1$ is negative,
with $x\ln x$ decreasing in value to its minimum.

<pre class="source">
  <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">*</span></span> ln</span><span class="main">(</span><span class="free">x</span><span class="main">)</span> <span class="main">&gt;</span> <span class="skolem">xmin</span> <span class="main">*</span> ln<span class="main">(</span><span class="skolem">xmin</span><span class="main">)"</span> <span class="keyword2 keyword">if</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">&lt;</span></span> <span class="skolem">xmin"</span>
  </span><span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">intro</span> DERIV_neg_imp_decreasing_open <span class="main main">[</span><span class="operator">OF</span> that<span class="main main">]</span> exI conjI<span class="main">)
    </span><span class="keyword3 command">fix</span> <span class="skolem">u</span> <span class="main">::</span> <span class="quoted">real
    </span><span class="keyword3 command">assume</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">&lt;</span></span> <span class="skolem">u"</span></span> <span class="keyword2 keyword">and</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">u</span> <span class="main">&lt;</span></span> <span class="skolem">xmin"</span> 
    </span><span class="keyword1 command">then</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span>ln</span> <span class="skolem">u</span> <span class="main">+</span></span> <span class="main">1</span> <span class="main">&lt;</span> ln <span class="main">1"
      </span><span class="keyword1 command">unfolding</span> xmin_def
      <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">smt</span> <span class="main main">(</span>verit<span class="main main">,</span> del_insts<span class="main main">)</span> assms exp_diff exp_less_cancel_iff exp_ln_iff<span class="main">)
    </span><span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="quoted"><span class="quoted"><span>"</span>ln</span> <span class="skolem">u</span> <span class="main">+</span></span> <span class="main">1</span> <span class="main">&lt;</span> <span class="main">0"
      </span><span class="keyword1 command">by</span> <span class="operator">simp
  </span><span class="keyword1 command">next
    </span><span class="keyword3 command">show</span> <span class="quoted"><span class="quoted"><span>"</span>continuous_on</span> <span class="main">{</span></span><span class="free">x</span><span class="main">..</span><span class="skolem">xmin</span><span class="main">}</span> <span class="main">(</span><span class="main">λ</span><span class="bound">u</span><span class="main">.</span> <span class="bound">u</span> <span class="main">*</span> ln <span class="bound">u</span><span class="main">)"
      </span><span class="keyword1 command">using</span> continuous_on_x_ln continuous_on_subset assms <span class="keyword1 command">by</span> <span class="operator">fastforce
  </span><span class="keyword1 command">qed</span> <span class="main">(</span><span class="operator">use</span> assms xln_deriv <span class="keyword2 keyword quasi_keyword">in</span> <span class="operator">auto</span><span class="main">)</span>
</pre>

The second case is symmetric. The derivative is positive,
with $x\ln x$ increasing in value from its minimum.
In both cases, continuity is a requirement.

<pre class="source">
  <span class="keyword1 command">moreover
  </span><span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">*</span></span> ln</span><span class="main">(</span><span class="free">x</span><span class="main">)</span> <span class="main">&gt;</span> <span class="skolem">xmin</span> <span class="main">*</span> ln<span class="main">(</span><span class="skolem">xmin</span><span class="main">)"</span> <span class="keyword2 keyword">if</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">&gt;</span></span> <span class="skolem">xmin"</span>
  </span><span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">intro</span> DERIV_pos_imp_increasing_open <span class="main main">[</span><span class="operator">OF</span> that<span class="main main">]</span> exI conjI<span class="main">)
    </span><span class="keyword3 command">fix</span> <span class="skolem">u
    </span><span class="keyword3 command">assume</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">&gt;</span></span> <span class="skolem">u"</span></span> <span class="keyword2 keyword">and</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">u</span> <span class="main">&gt;</span></span> <span class="skolem">xmin"</span> 
    </span><span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="quoted"><span class="quoted"><span>"</span>ln</span> <span class="skolem">u</span> <span class="main">+</span></span> <span class="main">1</span> <span class="main">&gt;</span> <span class="main">0"
      </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">smt</span> <span class="main main">(</span>verit<span class="main main">,</span> del_insts<span class="main main">)</span> <span class="quoted"><span class="quoted"><span>‹</span><span class="main">0</span></span> <span class="main">&lt;</span></span> <span class="skolem">xmin›</span> exp_minus inverse_eq_divide 
          ln_less_cancel_iff ln_unique xmin_def<span class="main">)
  </span><span class="keyword1 command">next
    </span><span class="keyword3 command">show</span> <span class="quoted"><span class="quoted"><span>"</span>continuous_on</span> <span class="main">{</span></span><span class="skolem">xmin</span><span class="main">..</span><span class="free">x</span><span class="main">}</span> <span class="main">(</span><span class="main">λ</span><span class="bound">u</span><span class="main">.</span> <span class="bound">u</span> <span class="main">*</span> ln <span class="bound">u</span><span class="main">)"
      </span><span class="keyword1 command">using</span> continuous_on_x_ln continuous_on_subset xmin_def <span class="keyword1 command">by</span> <span class="operator">fastforce
  </span><span class="keyword1 command">qed</span> <span class="main">(</span><span class="operator">use</span> <span class="quoted"><span class="quoted"><span>‹</span><span class="main">0</span></span> <span class="main">&lt;</span></span> <span class="skolem">xmin›</span> xln_deriv <span class="keyword2 keyword quasi_keyword">in</span> <span class="operator">auto</span><span class="main">)</span>
</pre>

If $x=1/e$, then the minimum value equals $-1/e$.
Note how the previous results are collected using the keyword <span class="keyword1 command">moreover</span>.

<pre class="source">
  <span class="keyword1 command">moreover</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">xmin</span> <span class="main">*</span></span> ln</span><span class="main">(</span><span class="skolem">xmin</span><span class="main">)</span> <span class="main">=</span> <span class="main">-</span><span class="main">1</span> <span class="main">/</span> exp <span class="main">1</span><span>"</span>
    <span class="keyword1 command">using</span> assms <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> xmin_def ln_div<span class="main">)</span>
</pre>

The keyword <span class="keyword1 command"> ultimately </span> takes the previous result and the earlier two saved by `moreover`, delivering them to the following proof.
As we have covered all the cases for $x$, the conclusion follows immediately.

<pre class="source">
  <span class="keyword1 command">ultimately</span> <span class="keyword3 command">show</span> <span class="var quoted var">?thesis
    </span><span class="keyword1 command">using</span> eq <span class="keyword1 command">by</span> <span class="operator">fastforce
</span><span class="keyword1 command">qed</span>
</pre>

### Finally, a numerical conclusion

In the [previous post]({% post_url 2024-07-25-Numeric_types %}), 
we used the `approximation` proof method (which operates by interval arithmetic) to calculate the minimum as -0.3679, 
and it was slow (19 seconds on my zippy laptop).
Now we can get 17 significant figures more or less instantaneously.

<pre class="source">
<span class="keyword1 command">corollary
  </span><span class="keyword2 keyword">fixes</span> <span class="free">x</span><span class="main">::</span><span class="quoted">real
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">≥</span></span> <span class="main">0</span>"
  </span><span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">*</span></span> ln</span><span class="main">(</span><span class="free">x</span><span class="main">)</span> <span class="main">≥</span> <span class="main">-</span><span class="numeral">0.36787944117144233"</span>  <span class="main">(</span><span class="keyword2 keyword">is</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">_</span> <span class="main">≥</span></span> <span class="var">?rhs"</span></span><span class="main">)
</span><span class="keyword1 command">proof</span> <span class="operator">-
  </span><span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span><span class="main">-</span></span><span class="main">1</span></span><span class="main">::</span>real<span class="main">)</span> <span class="main">/</span> exp <span class="main">1</span> <span class="main">≥</span> <span class="var">?rhs"
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">approximation</span> 60<span class="main">)
  </span><span class="keyword1 command">with</span> x_ln_lowerbound <span class="keyword3 command">show</span> <span class="var quoted var">?thesis
    </span><span class="keyword1 command">using</span> assms <span class="keyword1 command">by</span> <span class="operator">force
</span><span class="keyword1 command">qed</span>
</pre>


If you fancy a challenge, try the same exercise with the function $x\sin(1/x)$.
In many ways it's similar, but the derivative hits zero infinitely often
and the formula, $\sin(1/x) - \cos(1/x)/x$, doesn't look easy to work with.
If any of you tackle this problem, send it to me: 
the first nice solution will be posted here. 
[*Note added 2025-03-19: it is in its [own post]({% post_url 2025-03-19-Trickier_lower_bound %}).]*

The examples for this post are online [here](/Isabelle-Examples/Ln_lower_bound.thy).

Many thanks to Manuel Eberl for the continuity proof!
