---
layout: post
title: "Definite integrals, II: improper integrals"
usemathjax: true 
tags: [examples, formalised mathematics, Isar, analysis]
---
[Last time]({% post_url 2025-08-14-Integrals_I %}), 
we worked out a couple of definite integrals involving discontinuities at the endpoints.
They were easy because the antiderivatives were continuous.
Let's make things harder by looking at (apparent) discontinuities
and infinite endpoints, both of which require limit reasoning.
We begin by taking a look at the mysteries of the *extended real numbers*
and *Lebesgue integration*.

### Lebesgue integration; the extended real numbers

The Isabelle/HOL analysis library provides two forms of integration:

* The *Henstock–Kurzweil* or *gauge* integral
* The Lebesgue integral

Although technically messy, the gauge integral can handle a strict superset of the Lebesgue integrable functions.
However, Lebesgue integration, with its associated measure theory and probability theory,
is the elegant foundation upon which much of analysis has been built.
For Isabelle/HOL users, the overlap may be confusing, and
I think it's ugly to use both kinds of integral in a single proof.
It's best not to worry about such trivia.
For difficult improper integrals, Lebesgue is the way to go:
everything you are likely to need is already in the library.

Many of the key lemmas refer to the *extended real numbers*.
These are the real numbers extended with $\infty$ and $-\infty$:
symbols giving us a convenient way to express, for example, 
an integral over an unbounded interval.
The extended reals have type `ereal`, which is also the name of the function
that embeds real numbers into the extended reals.

It's important to stress the extended reals do not give any meaningful treatment of [infinity]({% post_url 2023-02-01-On-the-infinite %}),
such as we get with the [non-standard reals]({% post_url 2022-08-10-Nonstandard_Analysis %}).
The latter is a field and algebraic facts like $x+y - x = y$ 
hold even for infinite and infinitesimal quantities.
With the extended reals,  $\infty+1 - \infty = \infty - \infty = 0$.
All we get (and want) from the extended reals are two tokens $\infty$ and $-\infty$
satisfying the obvious ordering relations. Then we can express various kinds of
infinite intervals just by giving the lower and upper bounds, 
such as $(-\infty,0]$ or $(1,\infty)$ or $(-\infty,\infty)$.

### Redoing the baby example

We actually saw this example in the [previous post]({% post_url 2025-08-14-Integrals_I %}): 

$$\begin{equation*} \int_{-1}^1 \frac{1}{\sqrt{1-x^2}}\, dx = \pi \end{equation*}.
$$

The first time I did this, I obtained the antiderivative
through WolframAlpha as 

$$\begin{equation*}\displaystyle \tan^{-1} \Bigl({\frac{x}{\sqrt{1-x^2}}}\Bigr)  \end{equation*}.$$

This is the same as $\sin^{-1}(x)$ except for the division by zero at the endpoints.
Moreover, it converges continuously to $\pi/2$ as $x$ tends to $1$ and to $-\pi/2$ as $x$ tends to $-1$:
in other words, the singularities are removable.

Because the solution using $\sin^{-1}$ is so simple, 
my first plan was to abandon this example, 
but in every simple alternative I looked at, the removable singularity
had already been removed by others: 
for example, $\sin x/x$ is called the [sinc function](https://en.wikipedia.org/wiki/Sinc_function).
And yet, in harder problems, you may have to tackle removable singularities yourself.

So here is how we deal with this one.
To begin, we need a lemma to replace $x^2>1$ by the disjunction $x<{-1}$ or $x>1$.
(The library already includes the analogous lemma for $x^2=1$.)

<pre class="source">
<span class="keyword1 command">lemma</span> power2_gt_1_iff<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span><span class="main"><span class="hidden">⇧</span><sup>2</sup></span></span> <span class="main">&gt;</span></span> <span class="main">1</span> <span class="main">⟷</span> <span class="free">x</span> <span class="main">&lt;</span> <span class="main">(</span><span class="main">-</span><span class="main">1</span> <span class="main">::</span> <span class="tfree">'a</span> <span class="main">::</span> <span class="tclass">linordered_idom</span><span class="main">)</span> <span class="main">∨</span> <span class="free">x</span> <span class="main">&gt;</span> <span class="main">1</span><span>"</span><span>
  </span><span class="keyword1 command">using</span> power2_ge_1_iff <span class="main">[</span><span class="operator">of</span> <span class="quoted free">x</span><span class="main">]</span> power2_eq_1_iff <span class="main">[</span><span class="operator">of</span> <span class="quoted free">x</span><span class="main">]</span> <span class="keyword1 command">by</span> <span class="operator">auto</span>
</pre>

Now we set up the proof, with two separate theorem statements.
(With the gauge integral, the `has_integral` relation 
expresses both that the integral is defined and its value.)

<pre class="source">
<span class="keyword1 command">lemma</span> <span class="quoted quoted">"</span><span class="const">set_integrable</span> <span class="const">lborel</span> <span class="main">{</span><span class="main">-</span><span class="main">1</span><span class="main">&lt;..&lt;</span><span class="main">1</span><span class="main">}</span> <span class="main">(</span><span class="main">λ</span><span class="bound">x</span><span class="main">.</span> <span class="main">1</span> <span class="main">/</span> <span class="const">sqrt</span> <span class="main">(</span><span class="main">1</span><span class="main">-</span><span class="bound">x</span><span class="main"><span class="hidden">⇧</span><sup>2</sup></span><span class="main">)</span><span class="main">)</span><span>"</span><span>
      </span><span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span><span class="keyword1">LBINT</span></span> <span class="bound">x</span><span class="main">=</span></span><span class="main">-</span><span class="main">1</span><span class="main">..</span><span class="main">1</span><span class="main">.</span> <span class="main">1</span> <span class="main">/</span> <span class="const">sqrt</span> <span class="main">(</span><span class="main">1</span><span class="main">-</span><span class="bound">x</span><span class="main"><span class="hidden">⇧</span><sup>2</sup></span><span class="main">)</span><span class="main">)</span> <span class="main">=</span> <span class="const">pi</span><span>"</span><span>
</span><span class="keyword1 command">proof</span> <span class="operator">-</span>
</pre>

We make three lemmas available to the simplifier (including the one proved above),
and define `f` to abbreviate the antiderivative.

<pre class="source">
  <span class="keyword1 command">note</span> one_ereal_def <span class="main">[</span><span class="operator">simp</span><span class="main">]</span> power2_eq_1_iff <span class="main">[</span><span class="operator">simp</span><span class="main">]</span> power2_gt_1_iff <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span>
  </span><span class="keyword3 command">define</span> <span class="skolem skolem">f</span> <span class="keyword2 keyword">where</span> <span class="quoted quoted"><span>"</span><span class="skolem">f</span> <span class="main">≡</span> <span class="main">λ</span><span class="bound">x</span><span class="main">.</span> </span><span class="const">arctan</span> <span class="main">(</span><span class="bound">x</span> <span class="main">/</span> <span class="const">sqrt</span><span class="main">(</span><span class="main">1</span><span class="main">-</span><span class="bound">x</span><span class="main"><span class="hidden">⇧</span><sup>2</sup></span><span class="main">)</span><span class="main">)</span><span>"</span>
</pre>

Next, we formally verify the antiderivative by taking its derivative again.
Recall that this is an appeal to the *fundamental theorem of calculus* (FTC).
We use a variation on the differentiation technique 
described [last time]({% post_url 2025-08-14-Integrals_I %}),
showing that the extracted derivative equals $\frac{1}{\sqrt{1-x^2}}\$.

<pre class="source">
  <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span><span class="skolem">f</span> <span class="keyword1">has_real_derivative</span></span> <span class="main">1</span></span> <span class="main">/</span> <span class="const">sqrt</span> <span class="main">(</span><span class="main">1</span><span class="skolem">-x</span><span class="main"><span class="hidden">⇧</span><sup>2</sup></span><span class="main">)</span><span class="main">)</span> <span class="main">(</span><span class="keyword1">at</span> <span class="skolem">x</span><span class="main">)</span><span>"</span><span>
    </span><span class="keyword2 keyword">if</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">-</span></span><span class="main">1</span></span> <span class="main">&lt;</span> <span class="skolem">x</span><span>"</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">x</span> <span class="main">&lt;</span></span> <span class="main">1</span></span><span>"</span> <span class="keyword2 keyword">for</span> <span class="skolem">x</span><span>
    </span><span class="keyword1 command">unfolding</span> f_def<span> 
    </span><span class="keyword1 command improper command">apply</span> <span class="main">(</span><span class="operator">rule</span> refl <span class="dynamic dynamic">derivative_eq_intros</span> <span class="main keyword3">|</span> <span class="operator">use</span> that <span class="keyword2 keyword quasi_keyword">in</span> <span class="operator">force</span><span class="main">)</span><span class="main keyword3">+</span><span>
    </span><span class="keyword1 command improper command">apply</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> power2_eq_square <span class="dynamic dynamic">divide_simps</span><span class="main">)</span><span>
    </span><span class="keyword1 command improper command">done</span>
</pre>

Setting aside this result using `moreover`, we prove continuity of the integrand
on the **open** interval $(-1,1)$. (We shall deal with the endpoints later.)
As mentioned last time, proving continuity is trivial 
with the help of the theorem list `continuous_intros`.
The final call to `auto` is to prove that the divisor is nonzero.

<pre class="source">
  <span class="keyword1 command">moreover</span><span>
  </span><span class="keyword1 command">have</span> <span class="quoted quoted">"</span><span class="const">isCont</span> <span class="main">(</span><span class="main">λ</span><span class="bound">x</span><span class="main">.</span> <span class="main">1</span> <span class="main">/</span> <span class="const">sqrt</span> <span class="main">(</span><span class="main">1</span><span class="main">-</span><span class="bound">x</span><span class="main"><span class="hidden">⇧</span><sup>2</sup></span><span class="main">)</span><span class="main">)</span> <span class="skolem">x</span><span>"</span><span>
    </span><span class="keyword2 keyword">if</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">-</span></span><span class="main">1</span></span> <span class="main">&lt;</span> <span class="skolem">x</span><span>"</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">x</span> <span class="main">&lt;</span></span> <span class="main">1</span></span><span>"</span> <span class="keyword2 keyword">for</span> <span class="skolem">x</span><span>
    </span><span class="keyword1 command">using</span> that <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">intro</span> <span class="dynamic dynamic">continuous_intros</span><span class="main">)</span> <span class="operator">auto</span>
</pre>

The next step is trivial but vital.
The version of the FTC I'm using requires the integrand to be nonnegative.
In a moment, we'll look at another example where it isn't.

<pre class="source">
  <span class="keyword1 command">moreover</span>
  <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">0</span></span> <span class="main">≤</span></span> <span class="main">1</span> <span class="main">/</span> <span class="const">sqrt</span> <span class="main">(</span><span class="main">1</span><span class="skolem">-x</span><span class="main"><span class="hidden">⇧</span><sup>2</sup></span><span class="main">)</span><span>"</span><span>
    </span><span class="keyword2 keyword">if</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">-</span></span><span class="main">1</span></span> <span class="main">&lt;</span> <span class="skolem">x</span><span>"</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">x</span> <span class="main">&lt;</span></span> <span class="main">1</span></span><span>"</span> <span class="keyword2 keyword">for</span> <span class="skolem">x</span><span>
    </span><span class="keyword1 command">using</span> that <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> square_le_1<span class="main">)</span>
</pre>

Our version of the FTC deals with discontinuity at the endpoints
using limits. The theorem refers to the extended reals throughout,
which I've managed to conceal so far: Isabelle can usually mediate
between the reals and the extended reals.
They become explicit here. The actual limit reasoning is done by the `real_asymp`
proof method, demonstrated in a [previous post]({% post_url 2024-08-08-Ln_lower_bound %}).

<pre class="source">
  <span class="keyword1 command">moreover</span><span>
  </span><span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span><span class="skolem">f</span> <span class="main">⤏</span></span> <span class="main">-</span></span> <span class="const">pi</span><span class="main">/</span><span class="numeral">2</span><span class="main">)</span> <span class="main">(</span><span class="const">at_right</span> <span class="main">(</span><span class="main">-</span> <span class="main">1</span><span class="main">)</span><span class="main">)</span><span>"</span>  <span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span><span class="skolem">f</span> <span class="main">⤏</span></span> </span><span class="const">pi</span><span class="main">/</span><span class="numeral">2</span><span class="main">)</span> <span class="main">(</span><span class="const">at_left</span> <span class="main">1</span><span class="main">)</span><span>"</span><span>
    </span><span class="keyword1 command">unfolding</span> f_def <span class="keyword1 command">by</span> <span class="operator">real_asymp</span><span class="main keyword3">+</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span><span class="main">(</span><span class="skolem">f</span> <span class="main">∘</span></span> </span><span class="const">real_of_ereal</span><span class="main">)</span> <span class="main">⤏</span> <span class="main">-</span> <span class="const">pi</span><span class="main">/</span><span class="numeral">2</span><span class="main">)</span> <span class="main">(</span><span class="const">at_right</span> <span class="main">(</span><span class="main">-</span> <span class="main">1</span><span class="main">)</span><span class="main">)</span><span>"</span><span>
            </span><span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span><span class="main">(</span><span class="skolem">f</span> <span class="main">∘</span></span> </span><span class="const">real_of_ereal</span><span class="main">)</span> <span class="main">⤏</span> <span class="const">pi</span><span class="main">/</span><span class="numeral">2</span><span class="main">)</span> <span class="main">(</span><span class="const">at_left</span> <span class="main">1</span><span class="main">)</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp_all</span> <span class="quasi_keyword">add</span><span class="main main">:</span> ereal_tendsto_simps1<span class="main">)</span>
</pre>

Now we can conclude the proof. The keyword `ultimately`
brings in all of the facts that had been set aside using `moreover`,
and we insert a specific instance of the FTC, `interval_integral_FTC_nonneg`, 
instantiated with the relevant parameters.
This works because in the previous steps we proved all of its pre-conditions.

<pre class="source">
  <span class="keyword1 command">ultimately</span> <span class="keyword3 command">show</span><span> 
    </span><span class="quoted quoted">"</span><span class="const">set_integrable</span> <span class="const">lborel</span> <span class="main">{</span><span class="main">-</span><span class="main">1</span><span class="main">&lt;..&lt;</span><span class="main">1</span><span class="main">}</span> <span class="main">(</span><span class="main">λ</span><span class="bound">x</span><span class="main">.</span> <span class="main">1</span> <span class="main">/</span> <span class="const">sqrt</span> <span class="main">(</span><span class="main">1</span><span class="main">-</span><span class="bound">x</span><span class="main"><span class="hidden">⇧</span><sup>2</sup></span><span class="main">)</span><span class="main">)</span><span>"</span><span>
    </span><span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span><span class="keyword1">LBINT</span></span> <span class="bound">x</span><span class="main">=</span></span><span class="main">-</span><span class="main">1</span><span class="main">..</span><span class="main">1</span><span class="main">.</span> <span class="main">1</span> <span class="main">/</span> <span class="const">sqrt</span> <span class="main">(</span><span class="main">1</span><span class="main">-</span><span class="bound">x</span><span class="main"><span class="hidden">⇧</span><sup>2</sup></span><span class="main">)</span><span class="main">)</span> <span class="main">=</span> <span class="const">pi</span><span>"</span><span>
    </span><span class="keyword1 command">using</span> interval_integral_FTC_nonneg <span class="main">[</span><span class="operator">of</span> <span class="quoted quoted quoted">"</span><span class="main">-</span><span class="main">1</span><span>"</span> <span class="quoted main">1</span> <span class="quoted skolem quoted skolem">f</span> <span class="quoted quoted quoted"><span>"</span><span class="main main">λ</span><span class="bound bound">x</span><span class="main main">.</span> </span><span class="main">1</span> <span class="main">/</span> <span class="const">sqrt</span> <span class="main main">(</span><span class="main">1</span><span class="main">-</span><span class="bound bound">x</span><span class="main"><span class="hidden">⇧</span><sup>2</sup></span><span class="main main">)</span><span>"</span> <span class="quoted quoted quoted">"</span><span class="main">-</span><span class="const">pi</span><span class="main">/</span><span class="numeral numeral">2</span><span>"</span> <span class="quoted quoted quoted">"</span><span class="const">pi</span><span class="main">/</span><span class="numeral numeral">2</span><span>"</span><span class="main">]</span><span>
    </span><span class="keyword1 command">by</span> <span class="operator">auto</span><span>
</span><span class="keyword1 command">qed</span>
</pre>

### Integration over the entire real line

Our next example is properly improper, because the endpoints are infinite.

$$\begin{equation*} \int_{-\infty}^\infty \frac{1}{t^2+1}\, dt = \pi \end{equation*}$$

Here is its graph. Once again we have a non-negative integrand.

<p style="text-align: center;">
  <img src="/images/integral-3.png" alt="graph of 3rd integral, 1 / (t^2+1)" width="300"/>
</p>

Maple tells us that the antiderivative is $\tan^{-1}t$.
(I have also used Maple for all these graphs.)

Once again, Lebesgue integration is the way to go,
since the necessary machinery has not been set up for gauge integrals.
The formal proof has the same structure as in the previous example.
We verify the antiderivative, show continuity of the integrand
and also show the integrand to be nonnegative.
Finally, we apply the FTC to obtain the two conclusions.

<pre class="source">
<span class="keyword1 command">lemma</span><span>
  </span><span class="keyword2 keyword">defines</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">f'</span> <span class="main">≡</span> <span class="main">λ</span><span class="bound">t</span><span class="main">.</span> <span class="main">1</span></span> <span class="main">/</span></span> <span class="main">(</span><span class="bound">t</span><span class="main"><span class="hidden">⇧</span><sup>2</sup></span><span class="main">+</span><span class="main">1</span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword2 keyword">shows</span><span>
    </span><span class="quoted quoted">"</span><span class="const">set_integrable</span> <span class="const">lborel</span> <span class="main">(</span><span class="const">einterval</span> <span class="main">(</span><span class="main">-</span><span class="main">∞</span><span class="main">)</span> <span class="main">∞</span><span class="main">)</span> <span class="free">f'</span><span>"</span><span>
    </span><span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span><span class="keyword1">LBINT</span></span> <span class="bound">t</span><span class="main">=</span></span><span class="main">-</span><span class="main">∞</span><span class="main">..</span><span class="main">∞</span><span class="main">.</span> <span class="free">f'</span> <span class="bound">t</span><span class="main">)</span> <span class="main">=</span> <span class="const">pi</span><span>"</span><span>
</span><span class="keyword1 command">proof</span> <span class="operator">-</span><span>
  </span><span class="keyword1 command">have</span> <span class="quoted quoted"><span>"</span><span class="main">(</span></span><span class="const">arctan</span> <span class="keyword1">has_real_derivative</span> <span class="free">f'</span> <span class="skolem">t</span><span class="main">)</span> <span class="main">(</span><span class="keyword1">at</span> <span class="skolem">t</span><span class="main">)</span><span>"</span> <span class="keyword2 keyword">for</span> <span class="skolem">t</span><span>
    </span><span class="keyword1 command">unfolding</span> f'_def<span> 
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">rule</span> <span class="dynamic dynamic">derivative_eq_intros</span> <span class="main keyword3">|</span> <span class="operator">force</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> <span class="dynamic dynamic">divide_simps</span><span class="main">)</span><span class="main keyword3">+</span><span>
  </span><span class="keyword1 command">moreover</span><span>
  </span><span class="keyword1 command">have</span> <span class="quoted quoted">"</span><span class="const">isCont</span> <span class="free">f'</span> <span class="skolem">x</span><span>"</span> <span class="keyword2 keyword">for</span> <span class="skolem">x</span><span>
    </span><span class="keyword1 command">unfolding</span> f'_def<span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">intro</span> <span class="dynamic dynamic">continuous_intros</span><span class="main">)</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> add_nonneg_eq_0_iff<span class="main">)</span><span> 
  </span><span class="keyword1 command">moreover</span><span>
  </span><span class="keyword1 command">have</span> <span class="quoted quoted"><span>"</span><span class="main">(</span><span class="main">(</span></span><span class="const">arctan</span> <span class="main">∘</span> <span class="const">real_of_ereal</span><span class="main">)</span> <span class="main">⤏</span> <span class="main">-</span><span class="const">pi</span><span class="main">/</span><span class="numeral">2</span><span class="main">)</span> <span class="main">(</span><span class="const">at_right</span> <span class="main">(</span><span class="main">-</span><span class="main">∞</span><span class="main">)</span><span class="main">)</span><span>"</span><span>
       </span><span class="quoted quoted"><span>"</span><span class="main">(</span><span class="main">(</span></span><span class="const">arctan</span> <span class="main">∘</span> <span class="const">real_of_ereal</span><span class="main">)</span> <span class="main">⤏</span> <span class="const">pi</span><span class="main">/</span><span class="numeral">2</span><span class="main">)</span> <span class="main">(</span><span class="const">at_left</span> <span class="main">∞</span><span class="main">)</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> ereal_tendsto_simps1<span class="main keyword3">,</span> <span class="operator">real_asymp</span><span class="main">)</span><span class="main keyword3">+</span><span>
  </span><span class="keyword1 command">ultimately</span> <span class="keyword3 command">show</span> <span class="quoted quoted">"</span><span class="const">set_integrable</span> <span class="const">lborel</span> <span class="main">(</span><span class="const">einterval</span> <span class="main">(</span><span class="main">-</span><span class="main">∞</span><span class="main">)</span> <span class="main">∞</span><span class="main">)</span> <span class="free">f'</span><span>"</span><span>
    </span><span class="quoted quoted">"</span><span class="const">interval_lebesgue_integral</span> <span class="const">lborel</span> <span class="main">(</span><span class="main">-</span><span class="main">∞</span><span class="main">)</span> <span class="main">∞</span> <span class="free">f'</span> <span class="main">=</span> <span class="const">pi</span><span>"</span><span>
    </span><span class="keyword1 command">using</span> interval_integral_FTC_nonneg <span class="main">[</span><span class="operator">of</span> <span class="quoted quoted quoted">"</span><span class="main">-</span><span class="main">∞</span><span>"</span> <span class="quoted main">∞</span> <span class="const">arctan</span><span class="main">]</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> f'_def<span class="main">)</span><span>
</span><span class="keyword1 command">qed</span>
</pre>

There are a couple of differences from the previous proof.
We do not need an abbreviation for the antiderivative because it is simply
`arctan`.
But this proof features a local definition of the integrand
as `f'`, and we could have done something similar last time.

### Integration of a sign-changing function

If you are unsure why a sign-changing function 
needs a different version of the FTC, consider that $\cos$
is both differentiable and continuous. 
Without the non-negative condition, the FTC would tell us that
$\cos$ could be integrated over the whole real line, which is ridiculous.

And so our final example is to integrate a [damped sinusoid](https://www.statisticshowto.com/calculus-definitions/damped-sine-wave/) 
over the non-negative real numbers.

$$\begin{equation*} \int_0^\infty e^{-t}\cos t\, dt = \frac{1}{2} \end{equation*}$$

Here is the graph. It's hard to see, but this function crosses the $x$-axis infinitely often.

<p style="text-align: center;">
  <img src="/images/integral-4.png" alt="graph of 4th integral, exp(-t)cos(t)" width="300"/>
</p>

Because its sign changes, the integration proof involves two steps: 
1. Show that the integral exists. Since $\lvert e^{-t}\cos t\rvert \le e^{-t}$, 
we need to show that the latter function is integrable.
It is non-negative, so we apply the previous version of the FTC.
2. We apply a signed version of the FTC to verify what the value of the integral
actually is.

Let's do the formal proof.
We start with the theorem statement, including as before
a local definition of the integrand.

<pre class="source">
<span class="keyword1 command">lemma</span><span>
  </span><span class="keyword2 keyword">defines</span> <span class="quoted quoted"><span>"</span><span class="free">f'</span> <span class="main">≡</span> <span class="main">λ</span><span class="bound">t</span><span class="main">.</span> </span><span class="const">exp</span><span class="main">(</span><span class="main">-</span><span class="bound">t</span><span class="main">)</span><span class="main"> * </span><span class="const">cos</span><span class="main">(</span><span class="bound">t</span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword2 keyword">shows</span>  <span class="quoted quoted">"</span><span class="const">set_integrable</span> <span class="const">lborel</span> <span class="main">(</span><span class="const">einterval</span> <span class="main">0</span> <span class="main">∞</span><span class="main">)</span> <span class="free">f'</span><span>"</span><span>
         </span><span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span><span class="keyword1">LBINT</span></span> <span class="bound">t</span><span class="main">=</span></span><span class="main">0</span><span class="main">..</span><span class="main">∞</span><span class="main">.</span> <span class="free">f'</span> <span class="bound">t</span><span class="main">)</span> <span class="main">=</span> <span class="main">1</span><span class="main">/</span><span class="numeral">2</span><span>"</span>
<span class="keyword1 command">proof</span> <span class="operator">-</span>
</pre>

#### The first result

Concerning step 1 above, we show that $e^{-t}$ is integrable.
The proof relies on the FTC for non-negative functions, just as we've already.
Our task this time is slightly simpler because we don't care what the integral actually is.
(It's 1.)
We can therefore ignore the second conclusion of `interval_integral_FTC_nonneg`
and write the proof as follows:

<pre class="source">
  <span class="keyword1 command">have</span> <span class="quoted quoted">"</span><span class="const">set_integrable</span> <span class="const">lborel</span> <span class="main">(</span><span class="const">einterval</span> <span class="main">0</span> <span class="main">∞</span><span class="main">)</span> <span class="main">(</span><span class="main">λ</span><span class="bound">t</span><span class="main">.</span> <span class="const">exp</span><span class="main">(</span><span class="main">-</span><span class="bound">t</span><span class="main">)</span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">rule</span> interval_integral_FTC_nonneg<span class="main">)</span><span>
    </span><span class="keyword3 command">show</span> <span class="quoted quoted"><span>"</span><span class="main">(</span><span class="main">(</span><span class="main">λ</span><span class="bound">t</span><span class="main">.</span> <span class="main">-</span></span><span class="const">exp</span><span class="main">(</span><span class="main">-</span><span class="bound">t</span><span class="main">)</span><span class="main">)</span> <span class="keyword1">has_real_derivative</span> <span class="const">exp</span><span class="main">(</span><span class="main">-</span><span class="skolem">t</span><span class="main">)</span><span class="main">)</span> <span class="main">(</span><span class="keyword1">at</span> <span class="skolem">t</span><span class="main">)</span><span>"</span> <span class="keyword2 keyword">for</span> <span class="skolem">t</span><span>
      </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">rule</span> <span class="dynamic dynamic">derivative_eq_intros</span> <span class="main keyword3">|</span> <span class="operator">force</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> <span class="dynamic dynamic">field_simps</span><span class="main">)</span><span class="main keyword3">+</span><span>
    </span><span class="keyword1 command">have</span> <span class="quoted quoted"><span>"</span><span class="main">(</span><span class="main">(</span><span class="main">(</span><span class="main">λ</span><span class="bound">t</span><span class="main">.</span> <span class="main">-</span></span><span class="const">exp</span> <span class="main">(</span><span class="main">-</span><span class="bound">t</span><span class="main">)</span><span class="main">)</span> <span class="main">∘</span> <span class="const">real_of_ereal</span><span class="main">)</span> <span class="main">⤏</span> <span class="main">-</span><span class="main">1</span><span class="main">)</span> <span class="main">(</span><span class="const">at_right</span> <span class="main">(</span><span class="const">ereal</span> <span class="main">0</span><span class="main">)</span><span class="main">)</span><span>"</span><span>
      </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> ereal_tendsto_simps1<span class="main keyword3">,</span> <span class="operator">real_asymp</span><span class="main">)</span><span>
    </span><span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="quoted quoted"><span>"</span><span class="main">(</span><span class="main">(</span><span class="main">(</span><span class="main">λ</span><span class="bound">t</span><span class="main">.</span> <span class="main">-</span></span><span class="const">exp</span> <span class="main">(</span><span class="main">-</span><span class="bound">t</span><span class="main">)</span><span class="main">)</span> <span class="main">∘</span> <span class="const">real_of_ereal</span><span class="main">)</span> <span class="main">⤏</span> <span class="main">-</span><span class="main">1</span><span class="main">)</span> <span class="main">(</span><span class="const">at_right</span> <span class="main">0</span><span class="main">)</span><span>"</span><span>
      </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> zero_ereal_def<span class="main">)</span><span>
    </span><span class="keyword3 command">show</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span><span class="main">(</span><span class="main">(</span><span class="main">λ</span><span class="bound">t</span><span class="main">.</span> <span class="main">-</span></span> </span><span class="const">exp</span> <span class="main">(</span><span class="main">-</span> <span class="bound">t</span><span class="main">)</span><span class="main">)</span> <span class="main">∘</span> <span class="const">real_of_ereal</span><span class="main">)</span> <span class="main">⤏</span> <span class="main">0</span><span class="main">)</span> <span class="main">(</span><span class="const">at_left</span> <span class="main">∞</span><span class="main">)</span><span>"</span><span>
      </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> ereal_tendsto_simps1<span class="main keyword3">,</span> <span class="operator">real_asymp</span><span class="main">)</span><span>
  </span><span class="keyword1 command">qed</span> <span class="operator">auto</span>
</pre>

Setting this fact aside, we prove a necessary technical condition: 
that the integrand is a *measurable function*
on the closed interval $[0,\infty]$.

<pre class="source">
  <span class="keyword1 command">moreover</span> <span class="keyword1 command">have</span> <span class="quoted quoted">"</span><span class="const">set_borel_measurable</span> <span class="const">lborel</span> <span class="main">(</span><span class="const">einterval</span> <span class="main">0</span> <span class="main">∞</span><span class="main">)</span> <span class="free">f'</span><span>"</span><span>
    </span><span class="keyword1 command">using</span> borel_measurable_continuous_on_indicator<span> 
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> f'_def set_borel_measurable_def<span class="main">)</span>
</pre>

We store this fact as well, and then prove that the integrand is
absolutely bounded by $e^{-t}$.

<pre class="source">
  <span class="keyword1 command">moreover</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">⋀</span><span class="bound">t</span><span class="main">.</span> <span class="main">¦</span></span><span class="free">f'</span> <span class="bound">t</span><span class="main">¦</span></span> <span class="main">≤</span> <span class="const">exp</span><span class="main">(</span><span class="main">-</span><span class="bound">t</span><span class="main">)</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> f'_def abs_mult<span class="main">)</span>
</pre>

Combining the facts proved above, we find that `f'` is indeed integrable over $[0,\infty]$.
This is the first conclusion of the theorem, 
but we also label it because it's needed to prove the second conclusion.

<pre class="source">
  <span class="keyword1 command">ultimately</span> <span class="keyword3 command">show</span> *<span class="main">:</span> <span class="quoted quoted">"</span><span class="const">set_integrable</span> <span class="const">lborel</span> <span class="main">(</span><span class="const">einterval</span> <span class="main">0</span> <span class="main">∞</span><span class="main">)</span> <span class="free">f'</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> <span class="main main">(</span>mono_tags<span class="main main">,</span> lifting<span class="main main">)</span> abs_exp_cancel always_eventually<span>
        </span>real_norm_def set_integrable_bound set_integrable_bound<span class="main">)</span>
</pre>

#### The second result

Now we turn to step 2. We insert a local definition of the antiderivative,
which happens to be $$ e^{-t}\frac{\sin t - \cos t}{2} $$.
To prove the second conclusion, we express the integral as the difference
between two values at the endpoints and apply the more general version of the FTC.

<pre class="source">
  <span class="keyword3 command">define</span> <span class="skolem skolem">f</span> <span class="keyword2 keyword">where</span> <span class="quoted quoted"><span>"</span><span class="skolem">f</span> <span class="main">≡</span> <span class="main">λ</span><span class="bound">t</span><span class="main">::</span></span><span class="tconst">real</span><span class="main">.</span> <span class="const">exp</span><span class="main">(</span><span class="main">-</span><span class="bound">t</span><span class="main">)</span> <span class="main">*</span> <span class="main">(</span><span class="const">sin</span><span class="main">(</span><span class="bound">t</span><span class="main">)</span> <span class="main">-</span> <span class="const">cos</span><span class="main">(</span><span class="bound">t</span><span class="main">)</span><span class="main">)</span><span class="main"> / </span><span class="numeral">2</span><span>"</span><span>
  </span><span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span><span class="keyword1">LBINT</span></span> <span class="bound">t</span><span class="main">=</span></span><span class="main">0</span><span class="main">..</span><span class="main">∞</span><span class="main">.</span> <span class="free">f'</span> <span class="bound">t</span><span class="main">)</span> <span class="main">=</span> <span class="main">0</span> <span class="main">-</span> <span class="main">(</span><span class="main">-</span> <span class="main">1</span><span class="main">/</span><span class="numeral">2</span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">intro</span> interval_integral_FTC_integrable<span class="main">)</span>
</pre>

The next steps should be familiar by now. For an arbitrary real number `t`,
we verify the antiderivative by differentiation and prove the integrand to be continuous.

<pre class="source">
    <span class="keyword3 command">fix</span> <span class="skolem">t</span><span>
    </span><span class="keyword3 command">show</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span><span class="skolem">f</span> <span class="keyword1">has_vector_derivative</span></span> <span class="free">f'</span> <span class="skolem">t</span><span class="main">)</span> <span class="main">(</span><span class="keyword1">at</span></span> <span class="skolem">t</span><span class="main">)</span><span>"</span><span>
      </span><span class="keyword1 command">unfolding</span> f_def f'_def has_real_derivative_iff_has_vector_derivative <span class="main">[</span><span class="operator">symmetric</span><span class="main">]</span><span>
      </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">rule</span> <span class="dynamic dynamic">derivative_eq_intros</span> <span class="main keyword3">|</span> <span class="operator">force</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> <span class="dynamic dynamic">field_simps</span><span class="main">)</span><span class="main keyword3">+</span><span>
    </span><span class="keyword3 command">show</span> <span class="quoted quoted">"</span><span class="const">isCont</span> <span class="free">f'</span> <span class="skolem">t</span><span>"</span><span>
      </span><span class="keyword1 command">unfolding</span> f'_def <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">intro</span> <span class="dynamic dynamic">continuous_intros</span><span class="main">)</span>
</pre>

The FTC requires us to verify the values attained by the antiderivative at the endpoints.
Which we do using the techniques we've seen before, 
in particular, a couple of awkward tricks needed because everything has to be proved in terms of the extended real numbers.

<pre class="source">
  <span class="keyword1 command">next</span><span>
    </span><span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span><span class="main">(</span><span class="skolem">f</span> <span class="main">∘</span></span> </span><span class="const">real_of_ereal</span><span class="main">)</span> <span class="main">⤏</span> <span class="main">-</span><span class="main">1</span><span class="main">/</span><span class="numeral">2</span><span class="main">)</span> <span class="main">(</span><span class="const">at_right</span> <span class="main">(</span><span class="const">ereal</span> <span class="main">0</span><span class="main">)</span><span class="main">)</span><span>"</span><span>
      </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> ereal_tendsto_simps1 f_def<span class="main keyword3">,</span> <span class="operator">real_asymp</span><span class="main">)</span><span>
    </span><span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span><span class="main">(</span><span class="skolem">f</span> <span class="main">∘</span></span> </span><span class="const">real_of_ereal</span><span class="main">)</span> <span class="main">⤏</span> <span class="main">-</span><span class="main">1</span><span class="main">/</span><span class="numeral">2</span><span class="main">)</span> <span class="main">(</span><span class="const">at_right</span> <span class="main">0</span><span class="main">)</span><span>"</span><span>
      </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> zero_ereal_def<span class="main">)</span><span>
    </span><span class="keyword3 command">show</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span><span class="main">(</span><span class="skolem">f</span> <span class="main">∘</span></span> </span><span class="const">real_of_ereal</span><span class="main">)</span> <span class="main">⤏</span> <span class="main">0</span><span class="main">)</span> <span class="main">(</span><span class="const">at_left</span> <span class="main">∞</span><span class="main">)</span><span>"</span><span>
      </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> ereal_tendsto_simps1 f_def<span class="main keyword3">,</span> <span class="operator">real_asymp</span><span class="main">)</span>
</pre>

Now `auto` (given the first result, namely `*`) wraps up the proof.

<pre class="source">
  <span class="keyword1 command">qed</span> <span class="main">(</span><span class="operator">use</span> * <span class="keyword2 keyword quasi_keyword">in</span> <span class="operator">auto</span><span class="main">)</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span><span class="keyword1">LBINT</span></span> <span class="bound">t</span><span class="main">=</span></span><span class="main">0</span><span class="main">..</span><span class="main">∞</span><span class="main">.</span> <span class="free">f'</span> <span class="bound">t</span><span class="main">)</span> <span class="main">=</span> <span class="main">1</span><span class="main">/</span><span class="numeral">2</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="operator">simp</span><span>
</span><span class="keyword1 command">qed</span>
</pre>

### A few concluding remarks

As we have seen, an Isabelle theorem declaration can have multiple conclusions.
In the case of `interval_integral_FTC_nonneg`, it makes sense because
both conclusions depend on the same premises and much of the same reasoning.
In the last example, I did this simply for the sake of uniformity.
In the case of gauge integrals, Isabelle provides `has_integral`
to express that the integral exists and has the given value.
Somewhat similarly, `has_bochner_integral` refers to Lebesgue integrals,
but it is a bit clunky for integrating over the real line.

The Isabelle theory file formalising the examples in this and the previous post 
are [online](/Isabelle-Examples/Improper_Integral.thy).


