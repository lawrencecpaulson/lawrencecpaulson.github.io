---
layout: post
title:  The Dottie Number
usemathjax: true 
tags: [examples, Isar, AI, locales, Archive of Formal Proofs]
---
Once upon a time, [goes the story](/papers/Dottie-Number.pdf), 
a lady named Dottie got bored and started playing with her calculator,
pressing the cosine key over and over again.
At first the numbers fluctuated wildly, 
but over time they always settled down to approximately 0.739085.
(This only works if your calculator is set to radians, not degrees.)
She had discovered the unique fixed point of the cosine function.
The Dottie number has several further properties: it is a *global attractor*, 
meaning the limit is the same no matter what number you start with, 
and it is transcendental.
It is a great example for showing off a range of computer algebra techniques in Isabelle, 
such as differentiation and unlimited precision real computations.
Let's prove those properties just mentioned 
and calculate (by proof!) its value to 12 decimal places.

### Getting started

We begin by defining `dottie` to be *the* unique fixed point of `cos`.
But this definition, using the definite descriptor `THE`, will be good for nothing 
until both existence and uniqueness of a fixed point have been proved.

<pre class="source">
<span class="keyword1 command">definition</span> <span class="entity">dottie</span> <span class="main">::</span> <span class="quoted"><span class="tconst">real</span> <span class="keyword2 keyword">where</span><span>
  </span><span class="quoted"><span class="quoted"><span>"</span><span class="free">dottie</span> <span class="main">≡</span> <span class="keyword1">THE</span></span> <span class="bound">x</span><span class="main">.</span></span> <span class="const">cos</span> <span class="bound">x</span> <span class="main">=</span> <span class="bound">x</span><span>"</span></span>
</pre>

Those claims will be proved with the help of the function $g(x)=\cos x - x$.
Note that it slopes downwards.

<img src="/images/Dottie-g.png" alt="graph of the function cos(x)-x" width="500"/>

We can see that it has a unique root near $\frac{\pi}{4}$, but now we have to prove it.
Several different theorems need facts about $g$, 
so to avoid duplication we create a [*locale*]({% post_url 2022-03-23-Locales %}) where we can work with $g$.

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

Isabelle is capable of *calculating* derivatives automatically.
The trick, as we see above, is to hit the goal repeatedly with `derivative_eq_intros`, 
which is a collection of facts about derivatives of various operators.
The effect is practically the same as the schoolbook method.
If you know the derivative already, as here, it makes things easier to mention it.
Here we prove that the derivative of $g(t)$, which is $-\sin t-1$, 
is strictly negative over the given interval $[-1,1]$.

Although computer algebra systems are not always sound, 
we can use them to write correct Isabelle proofs. 
Via the fundamental theorem of calculus, we can handle tough integrals. 
We give the hard work to the computer algebra system; 
Isabelle merely has to take the derivative of the claimed integral 
and compare that with the original integrand.

### Existence

Existence is proved using the [*intermediate value theorem*](https://mathworld.wolfram.com/IntermediateValueTheorem.html), 
which states that 
a function $g$ that is continuous on a given closed interval $[a,b]$ 
attains all the points between $g(a)$ and $g(b)$.
Our $g$ is continuous. Since $g(0) = 1$ and $g(1) = \cos 1 - 1 < 0$, 
the IVT yields a point $x \in (0, 1)$ where $g(x) = 0$,
which implies $\cos x = x$.

<pre class="source">
<span class="keyword1 command">lemma</span> dottie_exists<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">∃</span></span><span class="bound">x</span><span class="main">::</span></span><span class="tconst">real</span><span class="main">.</span> <span class="main">0</span> <span class="main">&lt;</span> <span class="bound">x</span> <span class="main">∧</span> <span class="bound">x</span> <span class="main">&lt;</span> <span class="main">1</span> <span class="main">∧</span> <span class="const">cos</span> <span class="bound">x</span> <span class="main">=</span> <span class="bound">x</span><span>"</span><span>
</span><span class="keyword1 command">proof</span> <span class="operator">-</span><span>
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

In the proof above, we see a trick for proving continuity.
It resembles the trick for taking derivatives, 
only we hit the goal with a different list of theorems, namely `continuous_intros`.
Then we show the $g$ crosses 0 to prove the existence of a fixed point
satisfying $0<x<1$.

### Uniqueness

We proved above that the derivative of $g(x) = \cos x - x$
is strictly negative for $x \in [-1,1]$, i.e. $g$ is strictly decreasing,
so $g$ can have at most one zero on that interval. 
And since $[-1,1]$, is the range of the cosine function, 
uniqueness over the entire real line immediately follows.
  
<pre class="source">
<span class="keyword1 command">lemma</span> dottie_unique<span class="main">:</span><span>
  </span><span class="keyword2 keyword">fixes</span> <span class="free">x</span> <span class="free">y</span> <span class="main">::</span> <span class="tconst">real</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted quoted">"</span><span class="const">cos</span> <span class="free">x</span> <span class="main">=</span> <span class="free">x</span><span>"</span> <span class="quoted quoted">"</span><span class="const">cos</span> <span class="free">y</span> <span class="main">=</span> <span class="free">y</span><span>"</span><span>
  </span><span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">=</span></span> <span class="free">y</span><span>"</span></span><span>
</span><span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">rule</span> ccontr<span class="main">)</span><span>
  </span><span class="keyword3 command">assume</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">≠</span></span> <span class="free">y</span><span>"</span></span><span>
  </span><span class="keyword1 command">have</span> gx<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">g</span> <span class="free">x</span> <span class="main">=</span></span> <span class="main">0</span></span><span>"</span> <span class="keyword2 keyword">and</span> gy<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">g</span> <span class="free">y</span> <span class="main">=</span></span> <span class="main">0</span></span><span>"</span> <span class="keyword1 command">using</span> assms <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> g_def<span class="main">)</span><span>
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

More precisely, given the two claimed fixed points, $x$ and $y$, we first trivially establish that both must lie within the interval $[-1,1]$.
Then, assuming for contradiction that $x\not=y$, one must be less than the other.
So $g(x)<g(y)$ or $g(y)<g(x)$, because the derivative is strictly negative,
but we know $g(x) = g(y) = 0$.


### Approximating its value

This is a good example of using untrusted sources, such as a calculator, 
and validating them by formal proof to get an accurate approximation to Dottie.

<pre class="source">
<span class="keyword1 command">definition</span> <span class="entity">lb</span><span class="main">::</span><span class="tconst">real</span> <span class="keyword2 keyword">where</span> <span class="quoted quoted"><span>"</span><span class="free">lb</span> <span class="main">≡</span> <span class="numeral">0.739085133215</span><span>"</span></span><span>
</span><span class="keyword1 command">definition</span> <span class="entity">ub</span><span class="main">::</span><span class="tconst">real</span> <span class="keyword2 keyword">where</span> <span class="quoted quoted"><span>"</span><span class="free">ub</span> <span class="main">≡</span> <span class="numeral">0.739085133216</span><span>"</span></span>
</pre>

Knowing that the function $g$ is strictly decreasing,
we can determine whether a given estimate is a lower bound or an upper bound. 
We use the `approximation` proof method, which is based on interval arithmetic to investigate the ordering relationships. 

<pre class="source">
<span class="keyword1 command">lemma</span> lb_gt<span class="main">:</span> <span class="quoted quoted">"</span><span class="const">cos</span> <span class="const">lb</span> <span class="main">&gt;</span> <span class="const">lb</span><span>"</span><span>
  </span><span class="keyword1 command">unfolding</span> lb_def<span> </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">approximation</span> 50<span class="main">)</span>

<span class="keyword1 command">lemma</span> ub_lt<span class="main">:</span> <span class="quoted quoted">"</span><span class="const">cos</span> <span class="const">ub</span> <span class="main">&lt;</span> <span class="const">ub</span><span>"</span><span>
  </span><span class="keyword1 command">unfolding</span> ub_def<span> </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">approximation</span> 50<span class="main">)</span>
</pre>

Now we can prove that `lb` is a lower bound, by contradiction and monotonicity reasoning. 

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

And analogously, `ub` is an upper bound. 

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


We have pinned down the Dottie number to 12 decimal places. 
  
### Something trivial

All this time, we were continuing to work in the locale because we needed 
the lemma that the derivative of $g$ is negative.
But now, we are finished with $g$ and leave the locale.
We can refer to facts proved inside the locale using the prefix `Dottie`.

<pre class="source">
<span class="keyword2 keyword">end</span>
</pre>


Since $\cos(\mathit{dottie}) = \mathit{dottie}$ and $\mathit{dottie} \in (0,1)$, and since $\sin^2 x+cos^2x = 1$, we easily get 
$\sin(\mathit{dottie}) = \sqrt{1 - \mathit{dottie}^2}$.
Sledgehammer found this proof automatically.

<pre class="source">
<span class="keyword1 command">lemma</span> sin_dottie<span class="main">:</span> <span class="quoted quoted">"</span><span class="const">sin</span> <span class="const">dottie</span> <span class="main">=</span> <span class="const">sqrt</span> <span class="main">(</span><span class="main">1</span> <span class="main">-</span> <span class="const">dottie</span><span class="main"><span class="hidden">⇧</span><sup>2</sup></span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">smt</span> <span class="main main">(</span>verit<span class="main main">)</span> Dottie.facts pi_gt3 sin_cos_sqrt sin_ge_zero<span class="main">)</span>
</pre>


### The cosine function is a contraction map

The next step is to investigate why iterates of the cosine function 
always converge to the Dottie number.
It's because $\cos$ is a contraction on $[-1,1]$ with
*Lipschitz constant* $\sin 1$, or with less jargon, $\lvert\cos x - \cos y\rvert\le\sin 1\cdot \lvert x-y\rvert$.

Crucially, $0 < \sin 1 < 1$. This is easy to prove, and we could also have used the `approximation` method.
  
<pre class="source">
<span class="keyword1 command">lemma</span> sin1_bounds<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">0</span></span> <span class="main">&lt;</span></span> <span class="const">sin</span> <span class="main">(</span><span class="main">1</span><span class="main">::</span><span class="tconst">real</span><span class="main">)</span><span>"</span> <span class="quoted quoted">"</span><span class="const">sin</span> <span class="main">(</span><span class="main">1</span><span class="main">::</span><span class="tconst">real</span><span class="main">)</span> <span class="main">&lt;</span> <span class="main">1</span><span>"</span><span>
  </span><span class="keyword1 command">using</span> sin_monotone_2pi<span class="main">[</span><span class="operator">of</span> <span class="quoted main">1</span> <span class="quoted quoted">"</span><span class="const">pi</span><span class="main">/</span><span class="numeral">2</span><span>"</span><span class="main">]</span> pi_gt3 <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> sin_gt_zero_02<span class="main">)</span>
</pre>

And $\sin 1$ is the Lipschitz constant for $\cos$ because it is an upper bound on all possible values of $\lvert \sin t\rvert$ when $t\in[-1,1]$.

<pre class="source">
<span class="keyword1 command">lemma</span> abs_sin_le_sin1<span class="main">:</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">¦</span></span><span class="free">t</span><span class="main">¦</span></span> <span class="main">≤</span> <span class="main">1</span><span>"</span> <span class="keyword2 keyword">shows</span> <span class="quoted quoted"><span>"</span><span class="main">¦</span></span><span class="const">sin</span> <span class="free">t</span><span class="main">¦</span> <span class="main">≤</span> <span class="const">sin</span> <span class="main">(</span><span class="main">1</span><span class="main">::</span><span class="tconst">real</span><span class="main">)</span><span>"</span><span>
</span><span class="keyword1 command">proof</span> <span class="operator">-</span><span>
  </span><span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">1</span></span> <span class="main">&lt;</span></span> <span class="const">pi</span><span class="main">/</span><span class="numeral">2</span><span>"</span> <span class="keyword1 command">using</span> pi_gt3 <span class="keyword1 command">by</span> <span class="operator">simp</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="var quoted var">?thesis</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">smt</span> <span class="main main">(</span>verit<span class="main main">,</span> best<span class="main main">)</span> assms sin_minus sin_monotone_2pi_le<span class="main">)</span><span>
</span><span class="keyword1 command">qed</span>
</pre>

If $x<y$ then there exists $\xi\in(x,y)$ such that 
$\lvert\cos x - \cos y\rvert\le\lvert\sin \xi\rvert \cdot \lvert x-y\rvert$,
by the [*mean value theorem*](https://mathworld.wolfram.com/Mean-ValueTheorem.html).
Moreover, $\lvert\sin \xi\rvert\le \sin 1$.

<pre class="source">
<span class="keyword1 command">lemma</span> cos_contraction_lt<span class="main">:</span><span>
  </span><span class="keyword2 keyword">fixes</span> <span class="free">x</span> <span class="free">y</span> <span class="main">::</span> <span class="tconst">real</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">&lt;</span></span> <span class="free">y</span><span>"</span></span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">¦</span></span><span class="free">x</span><span class="main">¦</span></span> <span class="main">≤</span> <span class="main">1</span><span>"</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">¦</span></span><span class="free">y</span><span class="main">¦</span></span> <span class="main">≤</span> <span class="main">1</span><span>"</span><span>
  </span><span class="keyword2 keyword">shows</span> <span class="quoted quoted"><span>"</span><span class="main">¦</span></span><span class="const">cos</span> <span class="free">x</span> <span class="main">-</span> <span class="const">cos</span> <span class="free">y</span><span class="main">¦</span> <span class="main">≤</span> <span class="const">sin</span> <span class="main">1</span> <span class="main">*</span> <span class="main">¦</span><span class="free">x</span> <span class="main">-</span> <span class="free">y</span><span class="main">¦</span><span>"</span><span>
</span><span class="keyword1 command">proof</span> <span class="operator">-</span><span>
  </span><span class="keyword1 command">have</span> cont<span class="main">:</span> <span class="quoted quoted">"</span><span class="const">continuous_on</span> <span class="main">{</span><span class="free">x</span><span class="main">..</span><span class="free">y</span><span class="main">}</span> <span class="const">cos</span><span>"</span><span> 
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">intro</span> <span class="dynamic dynamic">continuous_intros</span><span class="main">)</span><span>
  </span><span class="keyword1 command">have</span> deriv<span class="main">:</span> <span class="quoted quoted"><span>"</span><span class="main">(</span><span class="main">(</span></span><span class="const">cos</span><span class="main">::</span><span class="tconst">real</span><span class="main">⇒</span><span class="tconst">real</span><span class="main">)</span> <span class="keyword1">has_derivative</span> <span class="main">(*)</span> <span class="main">(</span><span class="main">-</span> <span class="const">sin</span> <span class="skolem">u</span><span class="main">)</span><span class="main">)</span> <span class="main">(</span><span class="keyword1">at</span> <span class="skolem">u</span><span class="main">)</span><span>"</span> <span class="keyword2 keyword">for</span> <span class="skolem">u</span> <span class="main">::</span> <span class="tconst">real</span><span>
    </span><span class="keyword1 command">using</span> DERIV_cos<span class="main">[</span><span class="operator">of</span> <span class="quoted skolem">u</span><span class="main">]</span> <span class="keyword1 command">unfolding</span> has_field_derivative_def <span class="keyword1 command">by</span> <span class="operator">simp</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">obtain</span> <span class="skolem skolem">ξ</span> <span class="keyword2 keyword">where</span> ξ<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">ξ</span> <span class="main">∈</span></span> <span class="main">{</span></span><span class="free">x</span><span class="main">&lt;..&lt;</span><span class="free">y</span><span class="main">}</span><span>"</span> <span class="quoted quoted"><span>"</span><span class="main">¦</span></span><span class="const">cos</span> <span class="free">y</span> <span class="main">-</span> <span class="const">cos</span> <span class="free">x</span><span class="main">¦</span> <span class="main">≤</span> <span class="main">¦</span><span class="const">sin</span> <span class="skolem">ξ</span><span class="main">¦</span> <span class="main">*</span> <span class="main">¦</span><span class="free">y</span> <span class="main">-</span> <span class="free">x</span><span class="main">¦</span><span>"</span><span>
    </span><span class="keyword1 command">using</span> mvt_general<span class="main">[</span><span class="operator">OF</span> <span class="quoted"><span class="quoted"><span>‹</span><span class="free">x</span> <span class="main">&lt;</span></span> <span class="free">y</span><span>›</span></span> cont deriv<span class="main">]</span> <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> abs_mult<span class="main">)</span><span>
  </span><span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">¦</span></span><span class="skolem">ξ</span><span class="main">¦</span></span> <span class="main">≤</span> <span class="main">1</span><span>"</span><span> 
    </span><span class="keyword1 command">using</span> ξ assms <span class="keyword1 command">by</span> <span class="operator">auto</span><span>
  </span><span class="keyword1 command">have</span> <span class="quoted quoted"><span>"</span><span class="main">¦</span></span><span class="const">cos</span> <span class="free">y</span> <span class="main">-</span> <span class="const">cos</span> <span class="free">x</span><span class="main">¦</span> <span class="main">≤</span> <span class="main">¦</span><span class="const">sin</span> <span class="skolem">ξ</span><span class="main">¦</span> <span class="main">*</span> <span class="main">¦</span><span class="free">y</span> <span class="main">-</span> <span class="free">x</span><span class="main">¦</span><span>"</span><span>
    </span><span class="keyword1 command">using</span> ξ <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> abs_mult<span class="main">)</span><span>
  </span><span class="keyword1 command">also</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main var">…</span> <span class="main">≤</span></span> </span><span class="const">sin</span> <span class="main">1</span> <span class="main">*</span> <span class="main">¦</span><span class="free">y</span> <span class="main">-</span> <span class="free">x</span><span class="main">¦</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> <span class="quoted"><span class="quoted"><span>‹</span><span class="main">¦</span></span><span class="skolem">ξ</span><span class="main">¦</span></span> <span class="main">≤</span> <span class="main">1</span><span>›</span> abs_sin_le_sin1 mult_mono'<span class="main">)</span><span>
  </span><span class="keyword1 command">finally</span> <span class="keyword3 command">show</span> <span class="var quoted var">?thesis</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> abs_minus_commute<span class="main">)</span><span>
</span><span class="keyword1 command">qed</span>
</pre>

Here, by symmetry, we get rid of the assumption $x<y$. 
This finally establishes $\sin 1$ as the Lipschitz bound.

<pre class="source">
<span class="keyword1 command">lemma</span> cos_contraction<span class="main">:</span><span>
  </span><span class="keyword2 keyword">fixes</span> <span class="free">x</span> <span class="free">y</span> <span class="main">::</span> <span class="tconst">real</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">¦</span></span><span class="free">x</span><span class="main">¦</span></span> <span class="main">≤</span> <span class="main">1</span><span>"</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">¦</span></span><span class="free">y</span><span class="main">¦</span></span> <span class="main">≤</span> <span class="main">1</span><span>"</span><span>
  </span><span class="keyword2 keyword">shows</span> <span class="quoted quoted"><span>"</span><span class="main">¦</span></span><span class="const">cos</span> <span class="free">x</span> <span class="main">-</span> <span class="const">cos</span> <span class="free">y</span><span class="main">¦</span> <span class="main">≤</span> <span class="const">sin</span> <span class="main">1</span> <span class="main">*</span> <span class="main">¦</span><span class="free">x</span> <span class="main">-</span> <span class="free">y</span><span class="main">¦</span><span>"</span><span>
  </span><span class="keyword1 command">using</span> cos_contraction_lt<span class="main">[</span><span class="operator">of</span> <span class="quoted free">x</span> <span class="quoted free">y</span><span class="main">]</span> cos_contraction_lt<span class="main">[</span><span class="operator">of</span> <span class="quoted free">y</span> <span class="quoted free">x</span><span class="main">]</span> assms<span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">cases</span> <span class="quoted free">x</span> <span class="quoted free">y</span> <span class="quasi_keyword">rule</span><span class="main main">:</span> linorder_cases<span class="main">)</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> abs_minus_commute<span class="main">)</span>
</pre>



### The Dottie number is a universal attractor

An [*attractor*](https://en.wikipedia.org/wiki/Attractor) is a set of states towards which a dynamical system tends to evolve if started in some larger set, called the *basin of attraction*.
Iterates of the cosine function converge to the Dottie number starting from *any* real number,
so it is a *universal* attractor.
Since we have established the Lipschitz bound for cosine, it is just a matter of putting some pieces together.

Most of our theorems are confined to the interval $[-1,1]$, but that is no problem.
After one step, the iteration lands in $[-1,1]$ and stays there.

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

Once we are within the interval, applying cosine takes us closer to Dottie.
In fact, not that much closer: since $\sin 1 \approx 0.841$, convergence is sluggish.

<pre class="source">
<span class="keyword1 command">lemma</span> cos_step_to_dottie<span class="main">:</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">¦</span></span><span class="free">w</span><span class="main">¦</span></span> <span class="main">≤</span> <span class="main">1</span><span>"</span><span>
  </span><span class="keyword2 keyword">shows</span> <span class="quoted quoted"><span>"</span><span class="main">¦</span></span><span class="const">cos</span> <span class="free">w</span> <span class="main">-</span> <span class="const">dottie</span><span class="main">¦</span> <span class="main">≤</span> <span class="const">sin</span> <span class="main">1</span> <span class="main">*</span> <span class="main">¦</span><span class="free">w</span> <span class="main">-</span> <span class="const">dottie</span><span class="main">¦</span><span>"</span><span>
  </span><span class="keyword1 command">using</span> Dottie.facts <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> abs_cos_le_one assms cos_contraction<span class="main">)</span>
</pre>

Now we iterate the previous step using the obvious induction.
The distance to the fixed point, namely Dottie, decays geometrically.

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

Hence, the series of iterates converges to Dottie.

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

Most of the previous results hold only for an initial value within the interval $[-1,1]$.
Given an arbitrary initial value $x_0$, noting that $\cos x_0$ lies within that interval 
yields the desired universal attractor result.

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

Finally, let's note that Dottie is *transcendental*: not a root of any polynomial with 
integer coefficients. This turns out to be trivial, thanks to the Archive of Formal Proofs.
By the [Hermite--Lindemann--Weierstraß](https://isa-afp.org/entries/Hermite_Lindemann.html) theorem, $\cos z$ is transcendental
for every nonzero algebraic $z$. And Dottie is nonzero.
If Dottie were algebraic, then $\cos(\mathit{dottie}) = \mathit{dottie}$ 
would be both algebraic and transcendental, contradiction.

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

Sledgehammer can do all this automatically, but the proof above is clearer.

### A remark on AI

The entry resulted from some experiments using Claude.
Claude suggested the Dottie number as a nice simple example.
Claude also supplied the first version of the proofs.
They were correct as far as they went, but were overly detailed and with major omissions.
Notably, Claude forgot to prove that the Dottie number is unique over the entire real line, 
not just over the interval $[-1,1]$. 
So a fair bit of hand polishing has gone into these proofs.
They can be [downloaded](https://isa-afp.org/entries/Dottie_Number.html) from the AFP.
