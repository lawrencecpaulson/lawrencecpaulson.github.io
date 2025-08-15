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
We will take a look at the mysteries of the extended real numbers
and Lebesgue integration.

### Lebesgue integration; the extended real numbers

The Isabelle/HOL analysis library provides two forms of integration:

* The *Henstock–Kurzweil* or *gauge* integral
* The Lebesgue integral

Although technically messy, the gauge integral can handle a strict superset of the Lebesgue integrable functions.
However, Lebesgue integration, with its associated measure theory and probability theory,
is the elegant foundation upon which much of analysis has been built.
For Isabelle/HOL users, the overlap may be confusing and
it may seem ugly to use both kinds of integral in a single proof.
It's best not to worry about such trivia.
For difficult improper integrals, Lebesgue is the way to go:
everything you are likely to need is already in the library.

Many of the key lemmas refer to the *extended real numbers*.
These are the real numbers extended with $\infty$ and $-\infty$:
symbols giving us a convenient way to express, for example, 
an integral over an unbounded interval.
The extended reals have type `ereal`, which is also the name of the function
that embeds real numbers into the extended reals.

It's important to stress the extended reals do not give any meaningful treatment of infinity,
such as we get with the [non-standard reals]({% post_url 2022-08-10-Nonstandard_Analysis %}).
The latter is a field and the expected algebraic laws 
hold even for infinite and infinitesimal quantities.
That is not what we need just now: instead, simply two tokens $\infty$ and $-\infty$
satisfying the obvious ordering relations so that we can specify various kinds of
infinite intervals just by giving the lower and upper bound, 
such as $(-\infty,0]$ or $(1,\infty)$ or $(-\infty,\infty)$.

### Redoing the baby example

Our first example is actually the same as last time: 
$$\begin{equation*} \int_{-1}^1 \frac{1}{\sqrt{1-x^2}}\, dx = \pi \end{equation*}.
$$
The first time I did this, I obtained the antiderivative
through WolframAlpha as 

$$\begin{equation*}\displaystyle \tan^{-1} \Bigl({\frac{x}{\sqrt{1-x^2}}}\Bigr)  \end{equation*}.$$

This is the same as $\sin^{-1}(x)$ except for the division by zero at the endpoints.
Moreover, it converges to $\pi/2$ as $x$ tends to $1$ and to $-\pi/2$ as $x$ tends to $-1$,
or in other words, the singularities are removable.

Because the solution using $\sin^{-1}$ is so simple, 
my first plan was to abandon this example, 
but in every simple exercise I looked at, the removable singularity
had already been removed by others: 
for example, $\sin x/x$ is the [sinc function](https://en.wikipedia.org/wiki/Sinc_function).
And yet, in harder problems, you may have to tackle removable singularities yourself.

So here is how we deal with this one.

To begin, we'll need a lemma to replace $x^2>1$ by the disjunction $x<{-1}$ or $x>1$.
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
And define `f` to abbreviate the antiderivative.

<pre class="source">
  <span class="keyword1 command">note</span> one_ereal_def <span class="main">[</span><span class="operator">simp</span><span class="main">]</span> power2_eq_1_iff <span class="main">[</span><span class="operator">simp</span><span class="main">]</span> power2_gt_1_iff <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span>
  </span><span class="keyword3 command">define</span> <span class="skolem skolem">f</span> <span class="keyword2 keyword">where</span> <span class="quoted quoted"><span>"</span><span class="skolem">f</span> <span class="main">≡</span> <span class="main">λ</span><span class="bound">x</span><span class="main">.</span> </span><span class="const">arctan</span> <span class="main">(</span><span class="bound">x</span> <span class="main">/</span> <span class="const">sqrt</span><span class="main">(</span><span class="main">1</span><span class="main">-</span><span class="bound">x</span><span class="main"><span class="hidden">⇧</span><sup>2</sup></span><span class="main">)</span><span class="main">)</span><span>"</span>
</pre>

Next, we formally verify the antiderivative by taking its derivative again.
Recall that this is an appeal to the fundamental theorem of calculus (FTC).
We use a variation on the technique 
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
As mentioned last time, proving continuity is trivial, 
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
Through explicit limits. It is stated for the extended reals throughout,
but I've managed to conceal this so far because in most cases Isabelle can mediate
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

### An example of integration over the entire real line

$$\begin{equation*} \int_{-\infty}^\infty \frac{1}{t^2+1}\, dt = \pi \end{equation*}$$

antiderivative is $\tan^{-1}t$


<p style="text-align: center;">
  <img src="/images/integral-3.png" alt="graph of 3rd integral, 1 / (t^2+1)" width="300"/>
</p>


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

<pre class="source">
</pre>

<pre class="source">
</pre>



$$\begin{equation*} \int_0^\infty e^{-t}\cos t\, dt = \frac{1}{2} \end{equation*}$$

antiderivative is $$ e^{-t}\frac{\sin t - \cos t}{2} $$

<p style="text-align: center;">
  <img src="/images/integral-4.png" alt="graph of 4th integral, exp(-t)cos(t)" width="300"/>
</p>
