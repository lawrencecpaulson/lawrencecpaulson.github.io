---
layout: post
title:  The Dottie Number
usemathjax: true 
tags: [examples,Isar,AI]
---
Once upon a time, [goes the story](/papers/Dottie-Number.pdf), 
a lady named Dottie got bored and started playing with her calculator,
pressing the cosine key over and over again.
At first the numbers fluctuated wildly, 
but over time they always settled down to approximately 0.739085.
(This only works if your calculator is set to radians, not degrees.)
She had discovered the unique fixed point of the cosine function.
The Dottie number has several further properties: it is a global attractor, 
meaning the limit point is the same no matter what number you start with, 
and it is transcendental.
So it is great for showing off a variety of mathematical techniques in Isabelle, 
such as differentiation.
we also calculate its value to 12 decimal places, by proof.


### Getting started

We begin by defining `dottie` to be *the* unique fixed point of `cos`.
But a definition using the definite descriptor `THE` is good for nothing 
until both existence and uniqueness have proved for the specified property.

<pre class="source">
<span class="keyword1 command">definition</span> <span class="entity">dottie</span> <span class="main">::</span> <span class="quoted"><span class="tconst">real</span> <span class="keyword2 keyword">where</span><span>
  </span><span class="quoted"><span class="quoted"><span>"</span><span class="free">dottie</span> <span class="main">≡</span> <span class="keyword1">THE</span></span> <span class="bound">x</span><span class="main">.</span></span> <span class="const">cos</span> <span class="bound">x</span> <span class="main">=</span> <span class="bound">x</span><span>"</span></span>
</pre>

Those properties will be proved with reference to the function $g(x)=\cos x - x$.
We need to show that it has a unique root.
We need a number of facts about $g$ in several different theorems, 
so to avoid duplication we create a locale where we can work with $g$.

<pre class="source">
<span class="keyword1 command">locale</span> Dottie <span class="main">=</span><span>
  </span><span class="keyword2 keyword">fixes</span> <span class="free">g</span> <span class="main">::</span> <span class="quoted quoted">"</span><span class="tconst">real</span> <span class="main">⇒</span> <span class="tconst">real</span><span>"</span><span>
  </span><span class="keyword2 keyword">defines</span> <span class="quoted quoted"><span>"</span><span class="free">g</span> <span class="main">≡</span> <span class="main">λ</span><span class="bound">x</span><span class="main">::</span></span><span class="tconst">real</span><span class="main">.</span> <span class="const">cos</span> <span class="bound">x</span> <span class="main">-</span> <span class="bound">x</span><span>"</span><span>

</span><span class="keyword2 keyword">begin</span>
</pre>

Thanks to the `begin`, we are now working *inside* the locale. 
We have access to the function $g$ and can accumulate facts about it.
Our first task is to investigate its derivative.

<pre class="source">
<span class="keyword1 command">lemma</span> g_has_negative_deriv<span class="main">:</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">¦</span></span><span class="free">t</span><span class="main">¦</span></span> <span class="main">≤</span> <span class="main">1</span><span>"</span><span> 
  </span><span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">∃</span></span><span class="bound">d</span><span class="main">.</span></span> <span class="main">(</span><span class="free">g</span> <span class="keyword1">has_real_derivative</span> <span class="bound">d</span><span class="main">)</span> <span class="main">(</span><span class="keyword1">at</span> <span class="free">t</span><span class="main">)</span> <span class="main">∧</span> <span class="bound">d</span> <span class="main">&lt;</span> <span class="main">0</span><span>"</span><span>
</span><span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">intro</span> exI conjI<span class="main">)</span><span>
  </span><span class="keyword3 command">show</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span><span class="free">g</span> <span class="keyword1">has_real_derivative</span></span> <span class="main">(</span><span class="main">-</span></span> <span class="const">sin</span> <span class="free">t</span> <span class="main">-</span> <span class="main">1</span><span class="main">)</span><span class="main">)</span> <span class="main">(</span><span class="keyword1">at</span> <span class="free">t</span><span class="main">)</span><span>"</span><span>
    </span><span class="keyword1 command">unfolding</span> g_def <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">intro</span><span class="main main">!</span><span class="main main">:</span> <span class="dynamic dynamic">derivative_eq_intros</span><span class="main">)</span><span>
  </span><span class="keyword3 command">show</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">-</span></span> </span><span class="const">sin</span> <span class="free">t</span> <span class="main">-</span> <span class="main">1</span> <span class="main">&lt;</span> <span class="main">0</span><span>"</span><span>
    </span><span class="keyword1 command">using</span> assms pi_gt3 le_arcsin_iff <span class="main">[</span><span class="operator">of</span> <span class="main">_</span> <span class="quoted free">t</span><span class="main">]</span> <span class="keyword1 command">by</span> <span class="operator">fastforce</span><span>
</span><span class="keyword1 command">qed</span>
</pre>

Isabelle is capable of calculating derivatives automatically.
But if you know the derivative already (use a computer algebra system if you must), 
it makes things easier to mention it.
Here we determine that $g(t)$ has the derivative $-\sin t-1$, 
which is strictly negative over the given interval $[-1,1]$.

### Existence

Since $g(0) = 1$ and $g(1) = \cos 1 - 1  < 0$ and $g$ is continuous, 
the intermediate value theorem gives a point $x \in (0, 1)$ where $g(x) = 0$,
which implies $\cos x = x$.

<pre class="source">
<span class="keyword1 command">lemma</span> dottie_exists<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">∃</span></span><span class="bound">x</span><span class="main">::</span></span><span class="tconst">real</span><span class="main">.</span> <span class="main">0</span> <span class="main">&lt;</span> <span class="bound">x</span> <span class="main">∧</span> <span class="bound">x</span> <span class="main">&lt;</span> <span class="main">1</span> <span class="main">∧</span> <span class="const">cos</span> <span class="bound">x</span> <span class="main">=</span> <span class="bound">x</span><span>"</span><span>
</span><span class="keyword1 command">proof</span> <span class="operator">-</span><span>
  </span><span class="comment1"><span>― ‹Apply the IVT to </span><span class="antiquoted"><span class="antiquote">@{</span><span class="operator">term</span> <span class="quoted free">g</span><span class="antiquote">}</span></span><span> on the unit interval at 0.›</span></span><span>
  </span><span class="keyword1 command">have</span> g_cont<span class="main">:</span> <span class="quoted quoted">"</span><span class="const">continuous_on</span> <span class="main">{</span><span class="main">0</span><span class="main">..</span><span class="main">1</span><span class="main">}</span> <span class="free">g</span><span>"</span><span>
    </span><span class="keyword1 command">unfolding</span> g_def <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">intro</span> <span class="dynamic dynamic">continuous_intros</span><span class="main">)</span><span>
  </span><span class="keyword3 command">obtain</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">g</span> <span class="main">0</span></span> <span class="main">=</span></span> <span class="main">1</span><span>"</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">g</span> <span class="main">1</span></span> <span class="main">&lt;</span></span> <span class="main">0</span><span>"</span> <span class="keyword1 command">using</span> cos_1_lt_1 <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> g_def<span class="main">)</span><span>
  </span><span class="keyword1 command">with</span> IVT2'<span class="main">[</span><span class="operator">of</span> <span class="quoted free">g</span> <span class="quoted main">1</span> <span class="quoted main">0</span> <span class="quoted main">0</span><span class="main">]</span> g_cont<span>
  </span><span class="keyword3 command">obtain</span> <span class="skolem skolem">x</span> <span class="keyword2 keyword">where</span> hx<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">0</span></span> <span class="main">≤</span></span> <span class="skolem">x</span><span>"</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">x</span> <span class="main">≤</span></span> <span class="main">1</span></span><span>"</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">g</span> <span class="skolem">x</span> <span class="main">=</span></span> <span class="main">0</span></span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> less_eq_real_def zero_le_one<span class="main">)</span><span>
  </span><span class="keyword1 command">hence</span> cos_eq<span class="main">:</span> <span class="quoted quoted">"</span><span class="const">cos</span> <span class="skolem">x</span> <span class="main">=</span> <span class="skolem">x</span><span>"</span> <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> g_def<span class="main">)</span><span>
  </span><span class="keyword1 command">with</span> hx <span class="keyword3 command">show</span> <span class="var quoted var">?thesis</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> cos_1_lt_1 cos_zero order_less_le<span class="main">)</span><span>
</span><span class="keyword1 command">qed</span>
</pre>

### Uniqueness

The function $g(x) = \cos x - x$ has derivative $g'(x) = -\sin x - 1$, 
which is strictly negative for $x \in [-1,1]$ (since $\sin x \ge 0$ there).  
A function with strictly negative derivative is strictly decreasing, 
so $g$ can have at most one zero. 
We can extend uniqueness to the entire real line.
  
  
<pre class="source">
<span class="keyword1 command">lemma</span> dottie_unique<span class="main">:</span><span>
  </span><span class="keyword2 keyword">fixes</span> <span class="free">x</span> <span class="free">y</span> <span class="main">::</span> <span class="tconst">real</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted quoted">"</span><span class="const">cos</span> <span class="free">x</span> <span class="main">=</span> <span class="free">x</span><span>"</span> <span class="quoted quoted">"</span><span class="const">cos</span> <span class="free">y</span> <span class="main">=</span> <span class="free">y</span><span>"</span><span>
  </span><span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">=</span></span> <span class="free">y</span><span>"</span></span><span>
</span><span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">rule</span> ccontr<span class="main">)</span><span>
  </span><span class="keyword3 command">assume</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">≠</span></span> <span class="free">y</span><span>"</span></span><span>
  </span><span class="keyword1 command">have</span> gx<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">g</span> <span class="free">x</span> <span class="main">=</span></span> <span class="main">0</span></span><span>"</span> <span class="keyword2 keyword">and</span> gy<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">g</span> <span class="free">y</span> <span class="main">=</span></span> <span class="main">0</span></span><span>"</span> <span class="keyword1 command">using</span> assms <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> g_def<span class="main">)</span><span>
  </span><span class="comment1"><span>― ‹The derivative of </span><span class="antiquoted"><span class="antiquote">@{</span><span class="operator">term</span> <span class="quoted free">g</span><span class="antiquote">}</span></span> is <span class="antiquoted"><span class="antiquote">@{</span><span class="operator">term</span> <span class="quoted"><span>"</span><span class="main">λ</span><span class="bound">x</span><span class="main">.</span> <span class="main">-</span></span> </span></span><span class="const">sin</span> <span class="bound">x</span> <span class="main">-</span> <span class="main">1</span><span>"</span><span class="antiquote">}</span><span>, which is negative on </span><span class="antiquoted"><span class="antiquote">@{</span><span class="operator">term</span> <span class="quoted"><span>"</span><span class="main">{</span></span><span class="main">-</span></span><span class="main">1</span><span class="main">..</span><span class="main">1</span><span class="main">}</span><span>"</span><span class="antiquote">}</span><span>.›</span><span>
  </span><span class="keyword3 command">show</span> <span class="const">False</span><span>
  </span><span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">cases</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">¦</span></span><span class="free">x</span><span class="main">¦</span></span> <span class="main">&gt;</span> <span class="main">1</span> <span class="main">∨</span> <span class="main">¦</span><span class="free">y</span><span class="main">¦</span> <span class="main">&gt;</span> <span class="main">1</span><span>"</span><span class="main">)</span><span>
    </span><span class="keyword3 command">case</span> True<span>
    </span><span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="var quoted var">?thesis</span><span>
      </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> assms abs_cos_le_one not_less<span class="main">)</span><span>
  </span><span class="keyword1 command">next</span><span>
    </span><span class="keyword3 command">case</span> False<span>
    </span><span class="keyword1 command">then</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">¦</span></span><span class="free">x</span><span class="main">¦</span></span> <span class="main">≤</span> <span class="main">1</span> <span class="main">∧</span> <span class="main">¦</span><span class="free">y</span><span class="main">¦</span> <span class="main">≤</span> <span class="main">1</span><span>"</span><span>
      </span><span class="keyword1 command">by</span> <span class="operator">simp</span><span>
    </span><span class="keyword1 command">moreover</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">&lt;</span></span> <span class="free">y</span> <span class="main">∨</span></span> <span class="free">y</span> <span class="main">&lt;</span> <span class="free">x</span><span>"</span> <span class="keyword1 command">using</span> <span class="quoted"><span class="quoted"><span>‹</span><span class="free">x</span> <span class="main">≠</span></span> <span class="free">y</span><span>›</span></span> <span class="keyword1 command">by</span> <span class="operator">linarith</span><span>
    </span><span class="keyword1 command">ultimately</span> <span class="keyword3 command">show</span> <span class="var quoted var">?thesis</span><span>
      </span><span class="keyword1 command">using</span> DERIV_neg_imp_decreasing <span class="main">[</span><span class="operator">OF</span> _ g_has_negative_deriv<span class="main">]</span> gx gy<span>
      </span><span class="keyword1 command">by</span> <span class="operator">force</span><span>
  </span><span class="keyword1 command">qed</span><span>
</span><span class="keyword1 command">qed</span>
</pre>


### Approximating its value

We pin down the Dottie number to 12 decimal
  places. Note that $g$ is decreasing. We check that
  $\cos(lb) &gt; lb$ (so the fixed point is above $lb$) and
  $\cos(ub) &lt; u$ (so it is below $ub$).
We are continuing to work in the locale because we need 
the fact that the derivative of $g$ is negative.

<pre class="source">
<span class="keyword1 command">definition</span> <span class="entity">lb</span><span class="main">::</span><span class="tconst">real</span> <span class="keyword2 keyword">where</span> <span class="quoted quoted"><span>"</span><span class="free">lb</span> <span class="main">≡</span> <span class="numeral">0.739085133215</span><span>"</span></span><span>
</span><span class="keyword1 command">definition</span> <span class="entity">ub</span><span class="main">::</span><span class="tconst">real</span> <span class="keyword2 keyword">where</span> <span class="quoted quoted"><span>"</span><span class="free">ub</span> <span class="main">≡</span> <span class="numeral">0.739085133216</span><span>"</span></span>
</pre>

<pre class="source">
<span class="keyword1 command">lemma</span> lb_gt<span class="main">:</span> <span class="quoted quoted">"</span><span class="const">cos</span> <span class="const">lb</span> <span class="main">&gt;</span> <span class="const">lb</span><span>"</span><span>
  </span><span class="keyword1 command">unfolding</span> lb_def<span> </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">approximation</span> 50<span class="main">)</span>

<span class="keyword1 command">lemma</span> ub_lt<span class="main">:</span> <span class="quoted quoted">"</span><span class="const">cos</span> <span class="const">ub</span> <span class="main">&lt;</span> <span class="const">ub</span><span>"</span><span>
  </span><span class="keyword1 command">unfolding</span> ub_def<span> </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">approximation</span> 50<span class="main">)</span>
</pre>

<pre class="source">
<span class="keyword1 command">lemma</span> lb<span class="main">:</span> <span class="quoted quoted">"</span><span class="const">lb</span> <span class="main">&lt;</span> <span class="const">dottie</span><span>"</span><span>
</span><span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">rule</span> ccontr<span class="main">)</span><span>
  </span><span class="keyword3 command">assume</span> neg<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">¬</span></span> </span><span class="const">lb</span> <span class="main">&lt;</span> <span class="const">dottie</span><span>"</span><span>
  </span><span class="keyword1 command">have</span> gd<span class="main">:</span> <span class="quoted quoted"><span>"</span><span class="free">g</span> </span><span class="const">lb</span> <span class="main">&gt;</span> <span class="main">0</span><span>"</span><span> 
    </span><span class="keyword1 command">using</span> facts lb_gt <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> g_def<span class="main">)</span><span>
  </span><span class="keyword3 command">show</span> <span class="const">False</span><span>
    </span><span class="keyword1 command">using</span> DERIV_neg_imp_decreasing <span class="main">[</span><span class="operator">OF</span> _ g_has_negative_deriv<span class="main">]</span> facts neg<span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">smt</span> <span class="main main">(</span>verit<span class="main main">,</span> ccfv_SIG<span class="main main">)</span> cos_le_one cos_monotone_0_pi lb_gt pi_gt3<span class="main">)</span><span>
</span><span class="keyword1 command">qed</span>
</pre>

<pre class="source">
<span class="keyword1 command">lemma</span> ub<span class="main">:</span> <span class="quoted quoted">"</span><span class="const">ub</span> <span class="main">&gt;</span> <span class="const">dottie</span><span>"</span><span>
</span><span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">rule</span> ccontr<span class="main">)</span><span>
  </span><span class="keyword3 command">assume</span> neg<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">¬</span></span> </span><span class="const">ub</span> <span class="main">&gt;</span> <span class="const">dottie</span><span>"</span><span>
  </span><span class="keyword1 command">have</span> gd<span class="main">:</span> <span class="quoted quoted"><span>"</span><span class="free">g</span> </span><span class="const">ub</span> <span class="main">&lt;</span> <span class="main">0</span><span>"</span><span> 
    </span><span class="keyword1 command">using</span> facts ub_lt <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> g_def<span class="main">)</span><span>
  </span><span class="keyword3 command">show</span> <span class="const">False</span><span>
    </span><span class="keyword1 command">using</span> DERIV_neg_imp_decreasing <span class="main">[</span><span class="operator">OF</span> _ g_has_negative_deriv<span class="main">]</span> facts neg<span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">smt</span> <span class="main main">(</span>verit<span class="main main">)</span> cos_ge_minus_one ub_lt gd g_def<span class="main">)</span><span>
</span><span class="keyword1 command">qed</span>
</pre>

At this point, we are finished with the function $g$ and leave the locale.

<pre class="source">
<span class="keyword2 keyword">end</span>
</pre>


### Something trivial

Since $\cos(\mathit{dottie}) = \mathit{dottie}$ and $\mathit{dottie} \in (0,1)$, the
  Pythagorean identity gives $\sin(\mathit{dottie}) = \sqrt{1 - \mathit{dottie}^2}$.
Sledgehammer found this proof.


<pre class="source">
<span class="keyword1 command">lemma</span> sin_dottie<span class="main">:</span> <span class="quoted quoted">"</span><span class="const">sin</span> <span class="const">dottie</span> <span class="main">=</span> <span class="const">sqrt</span> <span class="main">(</span><span class="main">1</span> <span class="main">-</span> <span class="const">dottie</span><span class="main"><span class="hidden">⇧</span><sup>2</sup></span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">smt</span> <span class="main main">(</span>verit<span class="main main">)</span> Dottie.facts pi_gt3 sin_cos_sqrt sin_ge_zero<span class="main">)</span>
</pre>


### The Dottie number is a universal attractor

Iterating cosine from *any* real starting point converges to the
  Dottie number. The key fact is that $\cos$ is a contraction on $[-1,1]$ with
  Lipschitz constant $\sin 1 &lt; 1$ (since $|\cos' x| = |\sin x| \le \sin 1$ there),
  and that $\cos$ maps all of $\mathbb{R}$ into $[-1,1]$.
  
<pre class="source">
<span class="keyword1 command">lemma</span> sin1_bounds<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">0</span></span> <span class="main">&lt;</span></span> <span class="const">sin</span> <span class="main">(</span><span class="main">1</span><span class="main">::</span><span class="tconst">real</span><span class="main">)</span><span>"</span> <span class="quoted quoted">"</span><span class="const">sin</span> <span class="main">(</span><span class="main">1</span><span class="main">::</span><span class="tconst">real</span><span class="main">)</span> <span class="main">&lt;</span> <span class="main">1</span><span>"</span><span>
  </span><span class="keyword1 command">using</span> sin_monotone_2pi<span class="main">[</span><span class="operator">of</span> <span class="quoted main">1</span> <span class="quoted quoted">"</span><span class="const">pi</span><span class="main">/</span><span class="numeral">2</span><span>"</span><span class="main">]</span> pi_gt3 <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> sin_gt_zero_02<span class="main">)</span>
</pre>

<pre class="source">
<span class="keyword1 command">lemma</span> abs_sin_le_sin1<span class="main">:</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">¦</span></span><span class="free">t</span><span class="main">¦</span></span> <span class="main">≤</span> <span class="main">1</span><span>"</span> <span class="keyword2 keyword">shows</span> <span class="quoted quoted"><span>"</span><span class="main">¦</span></span><span class="const">sin</span> <span class="free">t</span><span class="main">¦</span> <span class="main">≤</span> <span class="const">sin</span> <span class="main">(</span><span class="main">1</span><span class="main">::</span><span class="tconst">real</span><span class="main">)</span><span>"</span><span>
</span><span class="keyword1 command">proof</span> <span class="operator">-</span><span>
  </span><span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">1</span></span> <span class="main">&lt;</span></span> <span class="const">pi</span><span class="main">/</span><span class="numeral">2</span><span>"</span> <span class="keyword1 command">using</span> pi_gt3 <span class="keyword1 command">by</span> <span class="operator">simp</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="var quoted var">?thesis</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">smt</span> <span class="main main">(</span>verit<span class="main main">,</span> best<span class="main main">)</span> assms sin_minus sin_monotone_2pi_le<span class="main">)</span><span>
</span><span class="keyword1 command">qed</span>
</pre>

The mean value theorem turns the derivative bound into a Lipschitz bound.


<pre class="source">
<span class="keyword1 command">lemma</span> cos_contraction_lt<span class="main">:</span><span>
  </span><span class="keyword2 keyword">fixes</span> <span class="free">x</span> <span class="free">y</span> <span class="main">::</span> <span class="tconst">real</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">&lt;</span></span> <span class="free">y</span><span>"</span></span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">¦</span></span><span class="free">x</span><span class="main">¦</span></span> <span class="main">≤</span> <span class="main">1</span><span>"</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">¦</span></span><span class="free">y</span><span class="main">¦</span></span> <span class="main">≤</span> <span class="main">1</span><span>"</span><span>
  </span><span class="keyword2 keyword">shows</span> <span class="quoted quoted"><span>"</span><span class="main">¦</span></span><span class="const">cos</span> <span class="free">x</span> <span class="main">-</span> <span class="const">cos</span> <span class="free">y</span><span class="main">¦</span> <span class="main">≤</span> <span class="const">sin</span> <span class="main">1</span> <span class="main">*</span> <span class="main">¦</span><span class="free">x</span> <span class="main">-</span> <span class="free">y</span><span class="main">¦</span><span>"</span><span>
</span><span class="keyword1 command">proof</span> <span class="operator">-</span><span>
  </span><span class="keyword1 command">have</span> cont<span class="main">:</span> <span class="quoted quoted">"</span><span class="const">continuous_on</span> <span class="main">{</span><span class="free">x</span><span class="main">..</span><span class="free">y</span><span class="main">}</span> <span class="const">cos</span><span>"</span> <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">intro</span> <span class="dynamic dynamic">continuous_intros</span><span class="main">)</span><span>
  </span><span class="keyword1 command">have</span> deriv<span class="main">:</span> <span class="quoted quoted"><span>"</span><span class="main">(</span><span class="main">(</span></span><span class="const">cos</span><span class="main">::</span><span class="tconst">real</span><span class="main">⇒</span><span class="tconst">real</span><span class="main">)</span> <span class="keyword1">has_derivative</span> <span class="main">(*)</span> <span class="main">(</span><span class="main">-</span> <span class="const">sin</span> <span class="skolem">u</span><span class="main">)</span><span class="main">)</span> <span class="main">(</span><span class="keyword1">at</span> <span class="skolem">u</span><span class="main">)</span><span>"</span> <span class="keyword2 keyword">for</span> <span class="skolem">u</span> <span class="main">::</span> <span class="tconst">real</span><span>
    </span><span class="keyword1 command">using</span> DERIV_cos<span class="main">[</span><span class="operator">of</span> <span class="quoted skolem">u</span><span class="main">]</span> <span class="keyword1 command">unfolding</span> has_field_derivative_def <span class="keyword1 command">by</span> <span class="operator">simp</span><span>
  </span><span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">∃</span></span><span class="bound">ξ</span> <span class="main">∈</span></span> <span class="main">{</span><span class="free">x</span><span class="main">&lt;..&lt;</span><span class="free">y</span><span class="main">}</span><span class="main">.</span> <span class="const">norm</span> <span class="main">(</span><span class="const">cos</span> <span class="free">y</span> <span class="main">-</span> <span class="const">cos</span> <span class="free">x</span><span class="main">)</span> <span class="main">≤</span> <span class="const">norm</span> <span class="main">(</span><span class="main">(*)</span> <span class="main">(</span><span class="main">-</span> <span class="const">sin</span> <span class="bound">ξ</span><span class="main">)</span> <span class="main">(</span><span class="free">y</span> <span class="main">-</span> <span class="free">x</span><span class="main">)</span><span class="main">)</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">rule</span> mvt_general<span class="main main">[</span><span class="operator">OF</span> <span class="quoted"><span class="quoted"><span>‹</span><span class="free">x</span> <span class="main">&lt;</span></span> <span class="free">y</span><span>›</span></span> cont<span class="main main">]</span><span class="main">)</span> <span class="main">(</span><span class="operator">use</span> deriv <span class="keyword2 keyword quasi_keyword">in</span> <span class="operator">blast</span><span class="main">)</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">obtain</span> <span class="skolem skolem">ξ</span> <span class="keyword2 keyword">where</span> ξ<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">ξ</span> <span class="main">∈</span></span> <span class="main">{</span></span><span class="free">x</span><span class="main">&lt;..&lt;</span><span class="free">y</span><span class="main">}</span><span>"</span> <span class="quoted quoted">"</span><span class="const">norm</span> <span class="main">(</span><span class="const">cos</span> <span class="free">y</span> <span class="main">-</span> <span class="const">cos</span> <span class="free">x</span><span class="main">)</span> <span class="main">≤</span> <span class="const">norm</span> <span class="main">(</span><span class="main">-</span> <span class="const">sin</span> <span class="skolem">ξ</span> <span class="main">*</span> <span class="main">(</span><span class="free">y</span> <span class="main">-</span> <span class="free">x</span><span class="main">)</span><span class="main">)</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="operator">auto</span><span>
  </span><span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">¦</span></span><span class="skolem">ξ</span><span class="main">¦</span></span> <span class="main">≤</span> <span class="main">1</span><span>"</span> <span class="keyword1 command">using</span> ξ assms <span class="keyword1 command">by</span> <span class="operator">auto</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword1 command">have</span> absxi<span class="main">:</span> <span class="quoted quoted"><span>"</span><span class="main">¦</span></span><span class="const">sin</span> <span class="skolem">ξ</span><span class="main">¦</span> <span class="main">≤</span> <span class="const">sin</span> <span class="main">1</span><span>"</span> <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">rule</span> abs_sin_le_sin1<span class="main">)</span><span>
  </span><span class="keyword1 command">have</span> <span class="quoted quoted"><span>"</span><span class="main">¦</span></span><span class="const">cos</span> <span class="free">y</span> <span class="main">-</span> <span class="const">cos</span> <span class="free">x</span><span class="main">¦</span> <span class="main">≤</span> <span class="main">¦</span><span class="const">sin</span> <span class="skolem">ξ</span><span class="main">¦</span> <span class="main">*</span> <span class="main">¦</span><span class="free">y</span> <span class="main">-</span> <span class="free">x</span><span class="main">¦</span><span>"</span><span>
    </span><span class="keyword1 command">using</span> ξ <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> abs_mult<span class="main">)</span><span>
  </span><span class="keyword1 command">also</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main var">…</span> <span class="main">≤</span></span> </span><span class="const">sin</span> <span class="main">1</span> <span class="main">*</span> <span class="main">¦</span><span class="free">y</span> <span class="main">-</span> <span class="free">x</span><span class="main">¦</span><span>"</span><span>
    </span><span class="keyword1 command">using</span> absxi <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> mult_right_mono<span class="main">)</span><span>
  </span><span class="keyword1 command">finally</span> <span class="keyword3 command">show</span> <span class="var quoted var">?thesis</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> abs_minus_commute<span class="main">)</span><span>
</span><span class="keyword1 command">qed</span>
</pre>


<pre class="source">
<span class="keyword1 command">lemma</span> cos_contraction<span class="main">:</span><span>
  </span><span class="keyword2 keyword">fixes</span> <span class="free">x</span> <span class="free">y</span> <span class="main">::</span> <span class="tconst">real</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">¦</span></span><span class="free">x</span><span class="main">¦</span></span> <span class="main">≤</span> <span class="main">1</span><span>"</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">¦</span></span><span class="free">y</span><span class="main">¦</span></span> <span class="main">≤</span> <span class="main">1</span><span>"</span><span>
  </span><span class="keyword2 keyword">shows</span> <span class="quoted quoted"><span>"</span><span class="main">¦</span></span><span class="const">cos</span> <span class="free">x</span> <span class="main">-</span> <span class="const">cos</span> <span class="free">y</span><span class="main">¦</span> <span class="main">≤</span> <span class="const">sin</span> <span class="main">1</span> <span class="main">*</span> <span class="main">¦</span><span class="free">x</span> <span class="main">-</span> <span class="free">y</span><span class="main">¦</span><span>"</span><span>
  </span><span class="keyword1 command">using</span> cos_contraction_lt<span class="main">[</span><span class="operator">of</span> <span class="quoted free">x</span> <span class="quoted free">y</span><span class="main">]</span> cos_contraction_lt<span class="main">[</span><span class="operator">of</span> <span class="quoted free">y</span> <span class="quoted free">x</span><span class="main">]</span> assms<span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">cases</span> <span class="quoted free">x</span> <span class="quoted free">y</span> <span class="quasi_keyword">rule</span><span class="main main">:</span> linorder_cases<span class="main">)</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> abs_minus_commute<span class="main">)</span>
</pre>

<pre class="source">
<span class="keyword1 command">lemma</span> cos_step_to_dottie<span class="main">:</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">¦</span></span><span class="free">w</span><span class="main">¦</span></span> <span class="main">≤</span> <span class="main">1</span><span>"</span><span>
  </span><span class="keyword2 keyword">shows</span> <span class="quoted quoted"><span>"</span><span class="main">¦</span></span><span class="const">cos</span> <span class="free">w</span> <span class="main">-</span> <span class="const">dottie</span><span class="main">¦</span> <span class="main">≤</span> <span class="const">sin</span> <span class="main">1</span> <span class="main">*</span> <span class="main">¦</span><span class="free">w</span> <span class="main">-</span> <span class="const">dottie</span><span class="main">¦</span><span>"</span><span>
  </span><span class="keyword1 command">using</span> Dottie.facts <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> abs_cos_le_one assms cos_contraction<span class="main">)</span>
</pre>

After one step the iteration lands in $[-1,1]$ and stays there.

<pre class="source">
<span class="keyword1 command">lemma</span> cos_funpow_in_pm1<span class="main">:</span><span>
  </span><span class="keyword2 keyword">fixes</span> <span class="free">x0</span> <span class="main">::</span> <span class="tconst">real</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">n</span> <span class="main">≥</span></span> <span class="main">1</span></span><span>"</span><span>
  </span><span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">¦</span></span><span class="main">(</span></span><span class="const">cos</span> <span class="main">^^</span> <span class="free">n</span><span class="main">)</span> <span class="free">x0</span><span class="main">¦</span> <span class="main">≤</span> <span class="main">1</span><span>"</span><span>
</span><span class="keyword1 command">proof</span> <span class="operator">-</span><span>
  </span><span class="keyword1 command">have</span> <span class="quoted quoted"><span>"</span><span class="main">(</span></span><span class="const">cos</span> <span class="main">^^</span> <span class="free">n</span><span class="main">)</span> <span class="free">x0</span> <span class="main">=</span> <span class="const">cos</span> <span class="main">(</span><span class="main">(</span><span class="const">cos</span> <span class="main">^^</span> <span class="main">(</span><span class="free">n</span><span class="main">-</span><span class="main">1</span><span class="main">)</span><span class="main">)</span> <span class="free">x0</span><span class="main">)</span><span>"</span><span>
    </span><span class="keyword1 command">using</span> assms funpow.simps<span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> One_nat_def Suc_diff_le diff_Suc_Suc diff_zero o_apply<span class="main">)</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="var quoted var">?thesis</span> <span class="keyword1 command">by</span> <span class="operator">simp</span><span>
</span><span class="keyword1 command">qed</span>
</pre>

From a start in $[-1,1]$, the distance to the fixed point decays geometrically.

<pre class="source">
<span class="keyword1 command">lemma</span> cos_funpow_bound<span class="main">:</span><span>
  </span><span class="keyword2 keyword">fixes</span> <span class="free">y0</span> <span class="main">::</span> <span class="tconst">real</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">¦</span></span><span class="free">y0</span><span class="main">¦</span></span> <span class="main">≤</span> <span class="main">1</span><span>"</span><span>
  </span><span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">¦</span></span><span class="main">(</span></span><span class="const">cos</span> <span class="main">^^</span> <span class="free">n</span><span class="main">)</span> <span class="free">y0</span> <span class="main">-</span> <span class="const">dottie</span><span class="main">¦</span> <span class="main">≤</span> <span class="main">(</span><span class="const">sin</span> <span class="main">1</span><span class="main">)</span><span class="main">^</span><span class="free">n</span> <span class="main">*</span> <span class="main">¦</span><span class="free">y0</span> <span class="main">-</span> <span class="const">dottie</span><span class="main">¦</span><span>"</span><span>
</span><span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">induction</span> <span class="quoted free">n</span><span class="main">)</span><span>
  </span><span class="keyword3 command">case</span> 0<span>
  </span><span class="keyword3 command">show</span> <span class="var quoted var">?case</span> <span class="keyword1 command">by</span> <span class="operator">simp</span><span>
</span><span class="keyword1 command">next</span><span>
  </span><span class="keyword3 command">case</span> <span class="main">(</span>Suc <span class="skolem">n</span><span class="main">)</span><span>
  </span><span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">¦</span></span><span class="main">(</span></span><span class="const">cos</span> <span class="main">^^</span> <span class="skolem">n</span><span class="main">)</span> <span class="free">y0</span><span class="main">¦</span> <span class="main">≤</span> <span class="main">1</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> funpow_0 less_one not_le cos_funpow_in_pm1<span class="main main">[</span><span class="operator">of</span> <span class="quoted skolem quoted skolem quoted skolem">n</span> <span class="quoted free quoted free quoted free">y0</span><span class="main main">]</span> assms<span class="main">)</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">¦</span></span><span class="main">(</span></span><span class="const">cos</span> <span class="main">^^</span> <span class="const">Suc</span> <span class="skolem">n</span><span class="main">)</span> <span class="free">y0</span> <span class="main">-</span> <span class="const">dottie</span><span class="main">¦</span> <span class="main">≤</span> <span class="const">sin</span> <span class="main">1</span> <span class="main">*</span> <span class="main">¦</span><span class="main">(</span><span class="const">cos</span> <span class="main">^^</span> <span class="skolem">n</span><span class="main">)</span> <span class="free">y0</span> <span class="main">-</span> <span class="const">dottie</span><span class="main">¦</span><span>"</span><span>
    </span><span class="keyword1 command">using</span> cos_step_to_dottie <span class="keyword1 command">by</span> <span class="operator">simp</span><span>
  </span><span class="keyword1 command">also</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main var">…</span> <span class="main">≤</span></span> </span><span class="const">sin</span> <span class="main">1</span> <span class="main">*</span> <span class="main">(</span><span class="main">(</span><span class="const">sin</span> <span class="main">1</span><span class="main">)</span><span class="main">^</span><span class="skolem">n</span> <span class="main">*</span> <span class="main">¦</span><span class="free">y0</span> <span class="main">-</span> <span class="const">dottie</span><span class="main">¦</span><span class="main">)</span><span>"</span><span>
    </span><span class="keyword1 command">using</span> Suc.IH sin1_bounds <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> mult_left_mono<span class="main">)</span><span>
  </span><span class="keyword1 command">also</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main var">…</span> <span class="main">=</span></span> <span class="main">(</span></span><span class="const">sin</span> <span class="main">1</span><span class="main">)</span><span class="main">^</span><span class="main">(</span><span class="const">Suc</span> <span class="skolem">n</span><span class="main">)</span> <span class="main">*</span> <span class="main">¦</span><span class="free">y0</span> <span class="main">-</span> <span class="const">dottie</span><span class="main">¦</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> mult.assoc<span class="main">)</span><span>
  </span><span class="keyword1 command">finally</span> <span class="keyword3 command">show</span> <span class="var quoted var">?case</span> <span class="keyword1 command">.</span><span>
</span><span class="keyword1 command">qed</span>
</pre>

<pre class="source">
<span class="keyword1 command">lemma</span> cos_iter_tendsto_unit<span class="main">:</span><span>
  </span><span class="keyword2 keyword">fixes</span> <span class="free">y0</span> <span class="main">::</span> <span class="tconst">real</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">¦</span></span><span class="free">y0</span><span class="main">¦</span></span> <span class="main">≤</span> <span class="main">1</span><span>"</span><span>
  </span><span class="keyword2 keyword">shows</span> <span class="quoted quoted"><span>"</span><span class="main">(</span><span class="main">λ</span><span class="bound">n</span><span class="main">.</span> <span class="main">(</span></span><span class="const">cos</span> <span class="main">^^</span> <span class="bound">n</span><span class="main">)</span> <span class="free">y0</span><span class="main">)</span> <span class="main">⇢</span> <span class="const">dottie</span><span>"</span><span>
</span><span class="keyword1 command">proof</span> <span class="operator">-</span><span>
  </span><span class="keyword1 command">have</span> pow0<span class="main">:</span> <span class="quoted quoted"><span>"</span><span class="main">(</span><span class="main">λ</span><span class="bound">n</span><span class="main">.</span> <span class="main">(</span></span><span class="const">sin</span> <span class="main">1</span><span class="main">)</span><span class="main">^</span><span class="bound">n</span><span class="main">)</span> <span class="main">⇢</span> <span class="main">(</span><span class="main">0</span><span class="main">::</span><span class="tconst">real</span><span class="main">)</span><span>"</span><span>
    </span><span class="keyword1 command">using</span> sin1_bounds <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">intro</span> LIMSEQ_realpow_zero<span class="main">)</span> <span class="operator">auto</span><span>
  </span><span class="keyword1 command">have</span> null<span class="main">:</span> <span class="quoted quoted"><span>"</span><span class="main">(</span><span class="main">λ</span><span class="bound">n</span><span class="main">.</span> <span class="main">(</span></span><span class="const">sin</span> <span class="main">1</span><span class="main">)</span><span class="main">^</span><span class="bound">n</span> <span class="main">*</span> <span class="main">¦</span><span class="free">y0</span> <span class="main">-</span> <span class="const">dottie</span><span class="main">¦</span><span class="main">)</span> <span class="main">⇢</span> <span class="main">0</span><span>"</span><span>
    </span><span class="keyword1 command">using</span> tendsto_mult<span class="main">[</span><span class="operator">OF</span> pow0 tendsto_const<span class="main">,</span> <span class="operator">of</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">¦</span></span><span class="free">y0</span> <span class="main">-</span></span> <span class="const">dottie</span><span class="main">¦</span><span>"</span><span class="main">]</span> <span class="keyword1 command">by</span> <span class="operator">simp</span><span>
  </span><span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span><span class="main">λ</span><span class="bound">n</span><span class="main">.</span> <span class="main">¦</span></span><span class="main">(</span></span><span class="const">cos</span> <span class="main">^^</span> <span class="bound">n</span><span class="main">)</span> <span class="free">y0</span> <span class="main">-</span> <span class="const">dottie</span><span class="main">¦</span><span class="main">)</span> <span class="main">⇢</span> <span class="main">0</span><span>"</span><span>
    </span><span class="keyword1 command">using</span> tendsto_sandwich<span class="main">[</span><span class="operator">OF</span> _ _ tendsto_const null<span class="main">]</span> cos_funpow_bound<span class="main">[</span><span class="operator">OF</span> assms<span class="main">]</span> <span class="keyword1 command">by</span> <span class="operator">auto</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="var quoted var">?thesis</span><span>
    </span><span class="keyword1 command">using</span> Lim_null tendsto_rabs_zero_iff <span class="keyword1 command">by</span> <span class="operator">blast</span><span>
</span><span class="keyword1 command">qed</span>
</pre>

<pre class="source">
<span class="keyword1 command">theorem</span> cos_iter_tendsto_dottie<span class="main">:</span><span>
  </span><span class="keyword2 keyword">fixes</span> <span class="free">x0</span> <span class="main">::</span> <span class="tconst">real</span><span>
  </span><span class="keyword2 keyword">shows</span> <span class="quoted quoted"><span>"</span><span class="main">(</span><span class="main">λ</span><span class="bound">n</span><span class="main">.</span> <span class="main">(</span></span><span class="const">cos</span> <span class="main">^^</span> <span class="bound">n</span><span class="main">)</span> <span class="free">x0</span><span class="main">)</span> <span class="main">⇢</span> <span class="const">dottie</span><span>"</span><span>
</span><span class="keyword1 command">proof</span> <span class="operator">-</span><span>
  </span><span class="keyword1 command">have</span> <span class="quoted quoted"><span>"</span><span class="main">¦</span></span><span class="const">cos</span> <span class="free">x0</span><span class="main">¦</span> <span class="main">≤</span> <span class="main">1</span><span>"</span> <span class="keyword1 command">by</span> <span class="operator">simp</span><span>
  </span><span class="keyword1 command">from</span> cos_iter_tendsto_unit<span class="main">[</span><span class="operator">OF</span> this<span class="main">]</span><span>
  </span><span class="keyword1 command">have</span> <span class="quoted quoted"><span>"</span><span class="main">(</span><span class="main">λ</span><span class="bound">n</span><span class="main">.</span> <span class="main">(</span></span><span class="const">cos</span> <span class="main">^^</span> <span class="bound">n</span><span class="main">)</span> <span class="main">(</span><span class="const">cos</span> <span class="free">x0</span><span class="main">)</span><span class="main">)</span> <span class="main">⇢</span> <span class="const">dottie</span><span>"</span> <span class="keyword1 command">.</span><span>
  </span><span class="keyword1 command">moreover</span> <span class="keyword1 command">have</span> <span class="quoted quoted"><span>"</span><span class="main">⋀</span><span class="bound">n</span><span class="main">.</span> <span class="main">(</span></span><span class="const">cos</span> <span class="main">^^</span> <span class="bound">n</span><span class="main">)</span> <span class="main">(</span><span class="const">cos</span> <span class="free">x0</span><span class="main">)</span> <span class="main">=</span> <span class="main">(</span><span class="const">cos</span> <span class="main">^^</span> <span class="const">Suc</span> <span class="bound">n</span><span class="main">)</span> <span class="free">x0</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> funpow_swap1<span class="main">)</span><span>
  </span><span class="keyword1 command">ultimately</span> <span class="keyword1 command">have</span> <span class="quoted quoted"><span>"</span><span class="main">(</span><span class="main">λ</span><span class="bound">n</span><span class="main">.</span> <span class="main">(</span></span><span class="const">cos</span> <span class="main">^^</span> <span class="const">Suc</span> <span class="bound">n</span><span class="main">)</span> <span class="free">x0</span><span class="main">)</span> <span class="main">⇢</span> <span class="const">dottie</span><span>"</span> <span class="keyword1 command">by</span> <span class="operator">simp</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="var quoted var">?thesis</span><span>
    </span><span class="keyword1 command">using</span> filterlim_sequentially_Suc <span class="keyword1 command">by</span> <span class="operator">blast</span><span>
</span><span class="keyword1 command">qed</span>
</pre>

### Transcendence

By the Hermite--Lindemann--Weierstra\ss\ theorem, $\cos z$ is transcendental
  for every nonzero algebraic </span><span class="antiquoted"><span class="antiquote">@{</span><span class="operator">term</span> <span class="quoted free">z</span><span class="antiquote">}</span></span><span>. If the Dottie number were algebraic, then
  $\cos(\mathit{dottie}) = \mathit{dottie}$ would be both algebraic and transcendental.

<pre class="source">
<span class="keyword1 command">theorem</span> dottie_transcendental<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">¬</span></span> </span><span class="const">algebraic</span> <span class="const">dottie</span><span>"</span><span>
</span><span class="keyword1 command">proof</span><span>
  </span><span class="keyword3 command">assume</span> alg<span class="main">:</span> <span class="quoted quoted">"</span><span class="const">algebraic</span> <span class="const">dottie</span><span>"</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">¬</span></span> </span><span class="const">algebraic</span> <span class="main">(</span><span class="const">cos</span> <span class="main">(</span><span class="const">complex_of_real</span> <span class="const">dottie</span><span class="main">)</span><span class="main">)</span><span>"</span><span>
    </span><span class="keyword1 command">using</span> Dottie.facts transcendental_cos <span class="keyword1 command">by</span> <span class="operator">auto</span><span> 
  </span><span class="keyword1 command">moreover</span> <span class="keyword1 command">have</span> <span class="quoted quoted">"</span><span class="const">cos</span> <span class="main">(</span><span class="const">complex_of_real</span> <span class="const">dottie</span><span class="main">)</span> <span class="main">=</span> <span class="const">complex_of_real</span> <span class="const">dottie</span><span>"</span><span>
    </span><span class="keyword1 command">using</span> Dottie.facts <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> cos_of_real<span class="main">)</span><span>
  </span><span class="keyword1 command">ultimately</span> <span class="keyword3 command">show</span> <span class="const">False</span> <span class="keyword1 command">using</span> alg <span class="keyword1 command">by</span> <span class="operator">simp</span><span>
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

  
