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
but over time they always settled down to approximately 0.739085.[^1]
She had discovered the unique fixed point of the cosine function.
The Dottie number has several further properties: it is a global attractor, 
meaning the limit point is the same no matter what number you start with, 
and it is transcendental.
So it is great for showing off a variety of mathematical techniques in Isabelle, 
such as differentiation.
we also calculate its value to 12 decimal places, by proof.

[^1]: this only works if your calculator is set to radians, not degrees

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
We need the derivative of $g$ to prove both existence and uniqueness, 
so to avoid duplication we create a locale where we can accumulate facts about $g$.


<pre class="source">
<span class="keyword1 command">locale</span> Dottie <span class="main">=</span><span>
  </span><span class="keyword2 keyword">fixes</span> <span class="free">g</span> <span class="main">::</span> <span class="quoted quoted">"</span><span class="tconst">real</span> <span class="main">⇒</span> <span class="tconst">real</span><span>"</span><span>
  </span><span class="keyword2 keyword">defines</span> <span class="quoted quoted"><span>"</span><span class="free">g</span> <span class="main">≡</span> <span class="main">λ</span><span class="bound">x</span><span class="main">::</span></span><span class="tconst">real</span><span class="main">.</span> <span class="const">cos</span> <span class="bound">x</span> <span class="main">-</span> <span class="bound">x</span><span>"</span><span>

</span><span class="keyword2 keyword">begin</span>
</pre>

Thanks to the `begin`, we are now working *inside* the locale. 
Our first task is to investigate the derivative of $g$.

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

  

### Universal attractor proof

### Transcendence