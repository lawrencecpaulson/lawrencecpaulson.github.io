---
layout: post
title: Proving a lower bound where the derivative is undefined at an endpoint
usemathjax: true 
tags: [examples, Isar, formalised mathematics]
---
The previous post concerned exact numerical calculations, culminating in an example of establishing a numerical lower bound for a simple mathematical formula, fully automatically.
Although automation is **the** key to the success of formal verification,
a numerical approach is not always good enough. In that example,
We could get three significant digits quickly, four significant digits slowly
and the exact lower bound never.
As every calculus student knows, to locate a minimum or maximum, you take the derivative
and solve for the point at which it vanishes. 
The desired property can then be shown using the main value theorem.

### A simple problem with surprising complications

Our task is simply to find the minimum of the function $x\ln x$
for $x\ge0$. And the first question is whether $x\ln x$ is even **defined**
when $x=0$. A stickler would say that it is not, because $\ln 0$ is undefined
and multiplying $\ln 0$ by $0$ does not help matters. 
And yet, this function is continuous:

FIGURE

<pre class="source">
<span class="keyword1 command">lemma</span> continuous_at_0<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>continuous</span> <span class="main">(</span>at_right</span> <span class="main">0</span><span class="main">)</span> <span class="main">(</span><span class="main">λ</span><span class="bound">x</span><span class="main">::</span>real<span class="main">.</span> <span class="bound">x</span> <span class="main">*</span> ln <span class="bound">x</span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword1 command">unfolding</span> continuous_within <span class="keyword1 command">by</span> <span class="operator">real_asymp</span>
</pre>

<pre class="source">
</span><span class="keyword1 command">lemma</span> continuous_nonneg<span class="main">:</span><span> 
  </span><span class="keyword2 keyword">fixes</span> <span class="free">x</span><span class="main">::</span><span class="quoted">real</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">≥</span></span> <span class="main">0</span></span><span>"</span><span>
  </span><span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span>continuous</span> <span class="main">(</span><span class="keyword1">at</span></span> <span class="free">x</span> <span class="keyword1">within</span> <span class="main">{</span><span class="main">0</span><span class="main">..}</span><span class="main">)</span> <span class="main">(</span><span class="main">λ</span><span class="bound">x</span><span class="main">.</span> <span class="bound">x</span> <span class="main">*</span> ln <span class="bound">x</span><span class="main">)</span><span>"</span><span>
</span><span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">cases</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">=</span></span> <span class="main">0</span></span><span>"</span><span class="main">)</span><span>
  </span><span class="keyword3 command">case</span> True <span class="keyword1 command">with</span> continuous_at_0 <span class="keyword3 command">show</span> <span class="var quoted var">?thesis</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">force</span> <span class="quasi_keyword">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> continuous_within_topological less_eq_real_def<span class="main">)</span><span>
</span><span class="keyword1 command">qed</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">intro</span><span class="main main">!</span><span class="main main">:</span> <span class="dynamic dynamic">continuous_intros</span><span class="main">)</span>
</pre>

<pre class="source">
<span class="keyword1 command">lemma</span> continuous_on_x_ln<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>continuous_on</span> <span class="main">{</span></span><span class="main">0</span><span class="main">..}</span> <span class="main">(</span><span class="main">λ</span><span class="bound">x</span><span class="main">::</span>real<span class="main">.</span> <span class="bound">x</span> <span class="main">*</span> ln <span class="bound">x</span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword1 command">unfolding</span> continuous_on_eq_continuous_within<span>
  </span><span class="keyword1 command">using</span> continuous_nonneg <span class="keyword1 command">by</span> <span class="operator">blast</span>
</pre>

<pre class="source">
<span class="keyword1 command">lemma</span> xln_deriv<span class="main">:</span><span>
  </span><span class="keyword2 keyword">fixes</span> <span class="free">x</span><span class="main">::</span><span class="quoted">real</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">&gt;</span></span> <span class="main">0</span></span><span>"</span><span>
  </span><span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span><span class="main">(</span><span class="main">λ</span><span class="bound">u</span><span class="main">.</span> <span class="bound">u</span> <span class="main">*</span></span> ln</span><span class="main">(</span><span class="bound">u</span><span class="main">)</span><span class="main">)</span> <span class="keyword1">has_real_derivative</span> ln <span class="free">x</span> <span class="main">+</span> <span class="main">1</span><span class="main">)</span> <span class="main">(</span><span class="keyword1">at</span> <span class="free">x</span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">rule</span> <span class="dynamic dynamic">derivative_eq_intros</span> refl <span class="main keyword3">|</span> <span class="operator">use</span> assms <span class="keyword2 keyword quasi_keyword">in</span> <span class="operator">force</span><span class="main">)</span><span class="main keyword3">+</span>
</pre>

<pre class="source">
<span class="keyword1 command">theorem</span> x_ln_lowerbound<span class="main">:</span><span>
  </span><span class="keyword2 keyword">fixes</span> <span class="free">x</span><span class="main">::</span><span class="quoted">real</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">&gt;</span></span> <span class="main">0</span></span><span>"</span><span>
  </span><span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">*</span></span> ln</span><span class="main">(</span><span class="free">x</span><span class="main">)</span> <span class="main">≥</span> <span class="main">-</span><span class="main">1</span> <span class="main">/</span> exp <span class="main">1</span><span>"</span><span>
</span><span class="keyword1 command">proof</span> <span class="operator">-</span>
</pre>

<pre class="source">
  <span class="keyword3 command">define</span> <span class="skolem skolem">xmin</span><span class="main">::</span><span class="quoted">real</span> <span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">xmin</span> <span class="main">≡</span> <span class="main">1</span></span> <span class="main">/</span></span> exp <span class="main">1</span><span>"</span><span>
  </span><span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">xmin</span> <span class="main">&gt;</span></span> <span class="main">0</span></span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> xmin_def<span class="main">)</span><span>
  </span><span class="keyword1 command">have</span> eq<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">-</span></span><span class="main">1</span></span> <span class="main">/</span> exp <span class="main">1</span> <span class="main">=</span> <span class="skolem">xmin</span> <span class="main">*</span> ln<span class="main">(</span><span class="skolem">xmin</span><span class="main">)</span><span>"</span><span>
    </span><span class="keyword1 command">using</span> assms <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> xmin_def ln_div<span class="main">)</span>
</pre>

<pre class="source">
  <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">*</span></span> ln</span><span class="main">(</span><span class="free">x</span><span class="main">)</span> <span class="main">&gt;</span> <span class="skolem">xmin</span> <span class="main">*</span> ln<span class="main">(</span><span class="skolem">xmin</span><span class="main">)</span><span>"</span> <span class="keyword2 keyword">if</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">&lt;</span></span> <span class="skolem">xmin</span><span>"</span></span><span>
  </span><span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">intro</span> DERIV_neg_imp_decreasing_open <span class="main main">[</span><span class="operator">OF</span> that<span class="main main">]</span> exI conjI<span class="main">)</span><span>
    </span><span class="keyword3 command">fix</span> <span class="skolem">u</span> <span class="main">::</span> <span class="quoted">real</span><span>
    </span><span class="keyword3 command">assume</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">&lt;</span></span> <span class="skolem">u</span><span>"</span></span> <span class="keyword2 keyword">and</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">u</span> <span class="main">&lt;</span></span> <span class="skolem">xmin</span><span>"</span></span><span> 
    </span><span class="keyword1 command">then</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span>ln</span> <span class="skolem">u</span> <span class="main">+</span></span> <span class="main">1</span> <span class="main">&lt;</span> ln <span class="main">1</span><span>"</span><span>
      </span><span class="keyword1 command">unfolding</span> xmin_def<span>
      </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">smt</span> <span class="main main">(</span>verit<span class="main main">,</span> del_insts<span class="main main">)</span> assms exp_diff exp_less_cancel_iff exp_ln_iff<span class="main">)</span><span>
    </span><span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="quoted"><span class="quoted"><span>"</span>ln</span> <span class="skolem">u</span> <span class="main">+</span></span> <span class="main">1</span> <span class="main">&lt;</span> <span class="main">0</span><span>"</span><span>
      </span><span class="keyword1 command">by</span> <span class="operator">simp</span><span>
  </span><span class="keyword1 command">next</span><span>
    </span><span class="keyword3 command">show</span> <span class="quoted"><span class="quoted"><span>"</span>continuous_on</span> <span class="main">{</span></span><span class="free">x</span><span class="main">..</span><span class="skolem">xmin</span><span class="main">}</span> <span class="main">(</span><span class="main">λ</span><span class="bound">u</span><span class="main">.</span> <span class="bound">u</span> <span class="main">*</span> ln <span class="bound">u</span><span class="main">)</span><span>"</span><span>
      </span><span class="keyword1 command">using</span> continuous_on_x_ln continuous_on_subset assms <span class="keyword1 command">by</span> <span class="operator">fastforce</span><span>
  </span><span class="keyword1 command">qed</span> <span class="main">(</span><span class="operator">use</span> assms xln_deriv <span class="keyword2 keyword quasi_keyword">in</span> <span class="operator">auto</span><span class="main">)</span>
</pre>

<pre class="source">
  <span class="keyword1 command">moreover</span><span>
  </span><span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">*</span></span> ln</span><span class="main">(</span><span class="free">x</span><span class="main">)</span> <span class="main">&gt;</span> <span class="skolem">xmin</span> <span class="main">*</span> ln<span class="main">(</span><span class="skolem">xmin</span><span class="main">)</span><span>"</span> <span class="keyword2 keyword">if</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">&gt;</span></span> <span class="skolem">xmin</span><span>"</span></span><span>
  </span><span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">intro</span> DERIV_pos_imp_increasing_open <span class="main main">[</span><span class="operator">OF</span> that<span class="main main">]</span> exI conjI<span class="main">)</span><span>
    </span><span class="keyword3 command">fix</span> <span class="skolem">u</span><span>
    </span><span class="keyword3 command">assume</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">&gt;</span></span> <span class="skolem">u</span><span>"</span></span> <span class="keyword2 keyword">and</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">u</span> <span class="main">&gt;</span></span> <span class="skolem">xmin</span><span>"</span></span><span> 
    </span><span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="quoted"><span class="quoted"><span>"</span>ln</span> <span class="skolem">u</span> <span class="main">+</span></span> <span class="main">1</span> <span class="main">&gt;</span> <span class="main">0</span><span>"</span><span>
      </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">smt</span> <span class="main main">(</span>verit<span class="main main">,</span> del_insts<span class="main main">)</span> <span class="quoted"><span class="quoted"><span>‹</span><span class="main">0</span></span> <span class="main">&lt;</span></span> <span class="skolem">xmin</span><span>›</span> exp_minus inverse_eq_divide<span> 
          </span>ln_less_cancel_iff ln_unique xmin_def<span class="main">)</span><span>
  </span><span class="keyword1 command">next</span><span>
    </span><span class="keyword3 command">show</span> <span class="quoted"><span class="quoted"><span>"</span>continuous_on</span> <span class="main">{</span></span><span class="skolem">xmin</span><span class="main">..</span><span class="free">x</span><span class="main">}</span> <span class="main">(</span><span class="main">λ</span><span class="bound">u</span><span class="main">.</span> <span class="bound">u</span> <span class="main">*</span> ln <span class="bound">u</span><span class="main">)</span><span>"</span><span>
      </span><span class="keyword1 command">using</span> continuous_on_x_ln continuous_on_subset xmin_def <span class="keyword1 command">by</span> <span class="operator">fastforce</span><span>
  </span><span class="keyword1 command">qed</span> <span class="main">(</span><span class="operator">use</span> <span class="quoted"><span class="quoted"><span>‹</span><span class="main">0</span></span> <span class="main">&lt;</span></span> <span class="skolem">xmin</span><span>›</span> xln_deriv <span class="keyword2 keyword quasi_keyword">in</span> <span class="operator">auto</span><span class="main">)</span>
</pre>

<pre class="source">
  <span class="keyword1 command">ultimately</span> <span class="keyword3 command">show</span> <span class="var quoted var">?thesis</span><span>
    </span><span class="keyword1 command">using</span> eq <span class="keyword1 command">by</span> <span class="operator">fastforce</span><span>
</span><span class="keyword1 command">qed</span>
</pre>

<pre class="source">
<span class="keyword1 command">corollary</span><span>
  </span><span class="keyword2 keyword">fixes</span> <span class="free">x</span><span class="main">::</span><span class="quoted">real</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">&gt;</span></span> <span class="main">0</span></span><span>"</span><span>
  </span><span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">*</span></span> ln</span><span class="main">(</span><span class="free">x</span><span class="main">)</span> <span class="main">≥</span> <span class="main">-</span><span class="numeral">0.36787944117144233</span><span>"</span>  <span class="main">(</span><span class="keyword2 keyword">is</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">_</span> <span class="main">≥</span></span> <span class="var">?rhs</span><span>"</span></span><span class="main">)</span><span>
</span><span class="keyword1 command">proof</span> <span class="operator">-</span><span>
  </span><span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span><span class="main">-</span></span><span class="main">1</span></span><span class="main">::</span>real<span class="main">)</span> <span class="main">/</span> exp <span class="main">1</span> <span class="main">≥</span> <span class="var">?rhs</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">approximation</span> 60<span class="main">)</span><span>
  </span><span class="keyword1 command">with</span> x_ln_lowerbound <span class="keyword3 command">show</span> <span class="var quoted var">?thesis</span><span>
    </span><span class="keyword1 command">using</span> assms <span class="keyword1 command">by</span> <span class="operator">force</span><span>
</span><span class="keyword1 command">qed</span>
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

<pre class="source">
</pre>

<pre class="source">
</pre>

