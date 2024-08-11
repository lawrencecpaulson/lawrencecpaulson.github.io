---
layout: post
title:  Probabilistic reasoning and formal proof
usemathjax: true 
tags: [Paul Erdős, example, Isar]
---

Many are the pitfalls awaiting anybody trying to formalise a proof,
but the worst are appeals to intuition.
These are typically a sign that the author can't be bothered to outline 
a calculation or argument, perhaps because the claim is obvious
(to them and maybe not to you).
Probabilistic claims, say about drawing coloured balls from a sack, may look particularly dubious.
But as [Paul Erdős](https://www.scientificamerican.com/article/this-nomadic-eccentric-was-the-most-prolific-mathematician-in-history/) has shown, such arguments are both powerful
and absolutely rigorous.
To formalise them simply requires a bit of measure theory boilerplate.

### A simple example

Let's consider an example from the website [Cut the Knot](https://www.cut-the-knot.org/Probability/ProbabilisticMethod.shtml), 
created by Alexander Bogomolny.
He credits the example to a 1963 paper by Erdős 
(I could not work out which one). It goes as follows:

> Let $A_k$, for $k = 1, \ldots, m$, 
> be a family of $n$-element subsets of a set $X$. If $m < 2^{n-1}$, 
> then there exists a bichromatic colouring[^1] of $X$ such that no $A_k$ is monochromatic.

[^1]: A *bichromatic colouring* of $X$ means to imagine each element of $X$ to be coloured red or blue, and a monochromatic subset would be entirely one colour.

And here's the proof, as presented by Bogomolny:

> Let $\cal F$ be a collection of $n$-sets (sets with exactly $n$ elements), and assume that $\vert\cal F\vert = m < 2^{n-1}$. Colour $X$ randomly with two colours, all colourings being equally likely. For $A\in \cal F$ let $E_A$ be the event that $A$ is monochromatic. Since there are two such colourings and $\|A\| = n$, probability $P(E_A)$ of the event $E_A$ is given by $P(E_A) = 2\times 2^{-n} = 2^{1-n}$.
> 
> Since the events $E_A$ are not necessarily disjoint, $P(\bigcup_{A\in\cal F} E_A) \le \sum_{A\in\cal F} P(E_A) = m\times2^{1-n} < 1$.
> 
> So the probability that at least one $A\in \cal F$ is monochromatic is less than 1. Thus there must be a bichromatic colouring of $X$ with no monochromatic $A\in\cal F$. QED.

This example is clearly a simplified version 
of [Erdős's celebrated proof](https://theoremoftheweek.wordpress.com/2010/05/02/theorem-25-erdoss-lower-bound-for-the-ramsey-numbers/) of a lower bound for Ramsey numbers,
which this often claimed to be the first application of the probabilistic method.
Note that the existence claim is nonconstructive: 
we have shown that the probability of a certain outcome is less than one.
So the opposite outcome has nonzero probability 
and therefore forms a non-empty set.

### Formalising the probability space

The theorem statement assumes the family $\cal F$ of $n$-sets
of the finite set $X$. The family has cardinality 
$\vert \cal F \vert = m<2^{2-1}$.
Necessary is the constraint $0<n\le\vert X\vert$, 
omitted from the problem statement.
As for the conclusion, the required 2-colouring is expressed
as a function from $X$ to the set $\\{0,1\\}$.
The *extensional* function space
<span class="keyword1">→<span class="hidden">⇩</span><sub>E</sub></span>
is required: by constraining the functions outside their domain ($X$)
to some arbitrary fixed value, 
this operator accurately represents the set $X\to\\{0,1\\}$.
It's vital because we are actually counting these functions.

<pre class="source">
<span class="keyword1 command">theorem</span> Erdos_1963<span class="main">:</span>
  <span class="keyword2 keyword">assumes</span> X<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">𝓕</span> <span class="main">⊆</span></span> nsets</span> <span class="free">X</span> <span class="free">n</span><span>"</span> <span class="quoted"><span class="quoted"><span>"</span>finite</span> <span class="free">X</span><span>"</span></span>
    <span class="keyword2 keyword">and</span> <span class="quoted"><span class="quoted"><span>"</span>card</span> <span class="free">𝓕</span> <span class="main">=</span></span> <span class="free">m</span><span>"</span> <span class="keyword2 keyword">and</span> m<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">m</span> <span class="main">&lt;</span></span> <span class="numeral">2</span><span class="main">^</span></span><span class="main">(</span><span class="free">n</span><span class="main">-</span><span class="main">1</span><span class="main">)</span><span>"</span> <span class="keyword2 keyword">and</span> n<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">0</span></span> <span class="main">&lt;</span></span> <span class="free">n</span><span>"</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">n</span> <span class="main">≤</span></span> card</span> <span class="free">X</span><span>"</span>
  <span class="keyword2 keyword">obtains</span> <span class="free">f</span><span class="main">::</span><span class="quoted"><span class="quoted"><span>"</span><span class="tfree">'a</span><span class="main">⇒</span>nat</span><span>"</span></span> <span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">f</span> <span class="main">∈</span></span> <span class="free">X</span> <span class="keyword1">→<span class="hidden">⇩</span><sub>E</sub></span></span> <span class="main">{..&lt;</span><span class="numeral">2</span><span class="main">}</span><span>"</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">⋀</span><span class="bound">F</span> <span class="bound">c</span><span class="main">.</span> <span class="main">⟦</span><span class="bound">F</span> <span class="main">∈</span></span> <span class="free">𝓕</span><span class="main">;</span> <span class="bound">c</span><span class="main">&lt;</span></span><span class="numeral">2</span><span class="main">⟧</span> <span class="main">⟹</span> <span class="main">¬</span> <span class="free">f</span> <span class="main">`</span> <span class="bound">F</span> <span class="main">⊆</span> <span class="main">{</span><span class="bound">c</span><span class="main">}</span><span>"</span>
<span class="keyword1 command">proof</span> <span class="operator">-</span>
</pre>

Now we have to set up the probabilities. 
The *sample space* $\Omega$ is the set of all 2-colourings of $X$.
Then the *probability space* $M$ is the corresponding measure space,
when all colourings have the same probability. 
A non-uniform probability distribution would be a little more work, 
e.g. we'd have to show that the probabilities summed to 1.

<pre class="source">
  <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span>finite</span> <span class="free">𝓕</span><span>"</span></span>
    <span class="keyword1 command">using</span> X finite_imp_finite_nsets finite_subset <span class="keyword1 command">by</span> <span class="operator">blast</span>
  <span class="keyword1 command">let</span> <span class="var quoted var">?two</span> <span class="main">=</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">{..&lt;</span></span><span class="numeral">2</span><span class="main">::</span>nat</span><span class="main">}</span><span>"</span>
  <span class="keyword3 command">define</span> <span class="skolem skolem">Ω</span> <span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">Ω</span> <span class="main">≡</span> <span class="free">X</span> <span class="keyword1">→<span class="hidden">⇩</span><sub>E</sub></span></span> <span class="var">?two</span><span>"</span></span>
  <span class="keyword3 command">define</span> <span class="skolem skolem">M</span> <span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">M</span> <span class="main">≡</span> uniform_count_measure</span> <span class="skolem">Ω</span><span>"</span></span>
</pre>

Next comes some boilerplate relating $\Omega$ and $M$,
allowing the interpretation of the `prob_space` locale.
The tools of probability reasoning are now at our disposal.

<pre class="source">
  <span class="keyword1 command">have</span> space_eq<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>space</span> <span class="skolem">M</span> <span class="main">=</span></span> <span class="skolem">Ω</span><span>"</span>
    <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> M_def space_uniform_count_measure<span class="main">)</span>
  <span class="keyword1 command">have</span> sets_eq<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>sets</span> <span class="skolem">M</span> <span class="main">=</span></span> Pow <span class="skolem">Ω</span><span>"</span>
    <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> M_def sets_uniform_count_measure<span class="main">)</span>
  <span class="keyword1 command">have</span> cardΩ<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>card</span> <span class="skolem">Ω</span> <span class="main">=</span></span> <span class="numeral">2</span> <span class="main">^</span> card <span class="free">X</span><span>"</span>
    <span class="keyword1 command">using</span> <span class="quoted"><span class="quoted"><span>‹</span>finite</span> <span class="free">X</span><span>›</span></span> <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> Ω_def card_funcsetE<span class="main">)</span>
  <span class="keyword1 command">have</span> Ω<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>finite</span> <span class="skolem">Ω</span><span>"</span></span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">Ω</span> <span class="main">≠</span></span> <span class="main">{}</span></span><span>"</span>
    <span class="keyword1 command">using</span> cardΩ less_irrefl <span class="keyword1 command">by</span> <span class="operator">fastforce</span><span class="main keyword3">+</span>
  <span class="keyword1 command">interpret</span> P<span class="main">:</span> prob_space <span class="quoted skolem">M</span>
    <span class="keyword1 command">unfolding</span> M_def <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">intro</span> prob_space_uniform_count_measure Ω<span class="main">)</span>
</pre>

The idea of a colouring being monochromatic on a set is easily expressed in terms of set image.
For any given colour $c$ and set $F$, 
the set of monochromatic maps is an *event* of the probability space.

<pre class="source">
  <span class="keyword3 command">define</span> <span class="skolem skolem">mchrome</span> <span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">mchrome</span> <span class="main">≡</span> <span class="main">λ</span><span class="bound">c</span> <span class="bound">F</span><span class="main">.</span> <span class="main">{</span><span class="bound bound">f</span> <span class="main">∈</span> <span class="skolem">Ω</span><span class="main">.</span> <span class="bound">f</span> <span class="main">`</span></span> <span class="bound">F</span> <span class="main">⊆</span></span> <span class="main">{</span><span class="bound">c</span><span class="main">}</span><span class="main">}</span><span>"</span>
  <span class="keyword1 command">have</span> mchrome<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">mchrome</span> <span class="skolem">c</span> <span class="skolem">F</span> <span class="main">∈</span></span> P.events</span><span>"</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">mchrome</span> <span class="skolem">c</span> <span class="skolem">F</span> <span class="main">⊆</span></span> <span class="skolem">Ω</span><span>"</span></span> <span class="keyword2 keyword">for</span> <span class="skolem">F</span> <span class="skolem">c</span>
    <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> sets_eq mchrome_def Ω_def<span class="main">)</span>
</pre>

### The probability of a monochrome map

The cardinality of a monochrome map 
(for a given $F\in\cal F$ and any fixed colour $c$)
is $2^{\vert X\vert-n}$.
That's because each element of $X$ not in $F$ could
be given either colour. 
The proof defines a bijection between colourings mapping 
the whole of $F$ to $c$ and those that don't colour $F$ at all.
This sort of calculation can get quite a bit more complicated
when the probability distribution is nonuniform.

<pre class="source">
  <span class="keyword1 command">have</span> card_mchrome<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>card</span> <span class="main">(</span><span class="skolem">mchrome</span> <span class="skolem">c</span> <span class="skolem">F</span><span class="main">)</span> <span class="main">=</span></span> <span class="numeral">2</span> <span class="main">^</span> <span class="main">(</span>card <span class="free">X</span> <span class="main">-</span> <span class="free">n</span><span class="main">)</span><span>"</span> <span class="keyword2 keyword">if</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">F</span> <span class="main">∈</span></span> <span class="free">𝓕</span><span>"</span></span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">c</span><span class="main">&lt;</span></span><span class="numeral">2</span><span>"</span></span> <span class="keyword2 keyword">for</span> <span class="skolem">F</span> <span class="skolem">c</span>
  <span class="keyword1 command">proof</span> <span class="operator">-</span>
    <span class="keyword1 command">have</span> F<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>finite</span> <span class="skolem">F</span><span>"</span></span> <span class="quoted"><span class="quoted"><span>"</span>card</span> <span class="skolem">F</span> <span class="main">=</span></span> <span class="free">n</span><span>" <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">F</span> <span class="main">⊆</span></span> <span class="free">X</span><span>"</span></span>
      <span class="keyword1 command">using</span> assms that <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> nsets_def<span class="main">)</span>
    <span class="keyword1 command">with</span> F <span class="quoted"><span class="quoted"><span>‹</span>finite</span> <span class="free">X</span><span>›</span></span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span>card</span> <span class="main">(</span><span class="free">X</span><span class="main">-</span></span><span class="skolem">F</span></span> <span class="keyword1">→<span class="hidden">⇩</span><sub>E</sub></span> <span class="var">?two</span><span class="main">)</span> <span class="main">=</span> <span class="numeral">2</span> <span class="main">^</span> <span class="main">(</span>card <span class="free">X</span> <span class="main">-</span> <span class="free">n</span><span class="main">)</span><span>"</span>
      <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> card_funcsetE card_Diff_subset<span class="main">)</span>
    <span class="keyword1 command">moreover</span>
    <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span>bij_betw</span> <span class="main">(</span><span class="main">λ</span><span class="bound">f</span><span class="main">.</span> restrict</span> <span class="bound">f</span> <span class="main">(</span><span class="free">X</span><span class="main">-</span><span class="skolem">F</span><span class="main">)</span><span class="main">)</span> <span class="main">(</span><span class="skolem">mchrome</span> <span class="skolem">c</span> <span class="skolem">F</span><span class="main">)</span> <span class="main">(</span><span class="free">X</span><span class="main">-</span><span class="skolem">F</span> <span class="keyword1">→<span class="hidden">⇩</span><sub>E</sub></span> <span class="var">?two</span><span class="main">)</span><span>"</span>
    <span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">intro</span> bij_betwI<span class="main">)</span>
      <span class="keyword3 command">show</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span><span class="main">λ</span><span class="bound">g</span> <span class="bound">x</span><span class="main">.</span> <span class="keyword1">if</span></span> <span class="bound">x</span><span class="main">∈</span></span><span class="skolem">F</span> <span class="keyword1">then</span> <span class="skolem">c</span> <span class="keyword1">else</span> <span class="bound">g</span> <span class="bound">x</span><span class="main">)</span> <span class="main">∈</span> <span class="main">(</span><span class="free">X</span><span class="main">-</span><span class="skolem">F</span> <span class="keyword1">→<span class="hidden">⇩</span><sub>E</sub></span> <span class="var">?two</span><span class="main">)</span> <span class="main">→</span> <span class="skolem">mchrome</span> <span class="skolem">c</span> <span class="skolem">F</span><span>"</span>
        <span class="keyword1 command">using</span> that <span class="quoted"><span class="quoted"><span>‹</span><span class="skolem">F</span> <span class="main">⊆</span></span> <span class="free">X</span><span>›</span></span> <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> mchrome_def Ω_def<span class="main">)</span>
    <span class="keyword1 command">qed</span> <span class="main">(</span><span class="operator">fastforce</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> mchrome_def Ω_def<span class="main">)</span><span class="main keyword3">+</span>
    <span class="keyword1 command">ultimately</span> <span class="keyword3 command">show</span> <span class="var quoted var">?thesis</span>
      <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> bij_betw_same_card<span class="main">)</span>
  <span class="keyword1 command">qed</span>
</pre>

The probability calculation is simply $2^{\vert X\vert-n} / 2^{\vert X\vert} = 1 / 2^n$.

<pre class="source">
  have prob_mchrome<span class="main">:</span> <span class="quoted quoted"><span>"</span>P.prob</span> <span class="main">(</span><span class="skolem">mchrome</span> <span class="skolem">c</span> <span class="skolem">F</span><span class="main">)</span> <span class="main">=</span> <span class="main">1</span> <span class="main">/</span> <span class="numeral">2</span><span class="main">^</span><span class="free">n</span><span>"</span>  
    <span class="keyword2 keyword">if</span> <span class="quoted quoted"><span>"</span><span class="skolem">F</span> <span class="main">∈</span></span> <span class="free">ℱ</span><span>"</span> <span class="quoted quoted"><span>"</span><span class="skolem">c</span><span class="main">&lt;</span></span><span class="numeral">2</span><span>"</span> <span class="keyword2 keyword">for</span> <span class="skolem">F</span> <span class="skolem">c</span>
  <span class="keyword1 command">proof</span> <span class="operator">-</span>
    <span class="keyword1 command">have</span> emeasure_eq<span class="main">:</span> <span class="quoted quoted"><span>"</span>emeasure</span> <span class="skolem">M</span> <span class="skolem">U</span> <span class="main">=</span> <span class="main">(</span><span class="keyword1">if</span> <span class="skolem">U</span><span class="main">⊆</span><span class="skolem">Ω</span> <span class="keyword1">then</span> ennreal<span class="main">(</span>card <span class="skolem">U</span> <span class="main">/</span> card <span class="skolem">Ω</span><span class="main">)</span> <span class="keyword1">else</span> <span class="main">0</span><span class="main">)</span><span>"</span> <span class="keyword2 keyword">for</span> <span class="skolem">U</span>
      <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> M_def emeasure_uniform_count_measure_if <span class="quoted quoted"><span>‹</span>finite</span> <span class="skolem">Ω</span><span>›</span><span class="main">)</span>
    <span class="keyword1 command">have</span> <span class="quoted quoted"><span>"</span>emeasure</span> <span class="skolem">M</span> <span class="main">(</span><span class="skolem">mchrome</span> <span class="skolem">c</span> <span class="skolem">F</span><span class="main">)</span> <span class="main">=</span> ennreal <span class="main">(</span><span class="numeral">2</span> <span class="main">^</span> <span class="main">(</span>card <span class="free">X</span> <span class="main">-</span> <span class="free">n</span><span class="main">)</span> <span class="main">/</span> card <span class="skolem">Ω</span><span class="main">)</span><span>"</span>
      <span class="keyword1 command">using</span> that mchrome <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> emeasure_eq card_mchrome<span class="main">)</span>
    <span class="keyword1 command">also</span> <span class="keyword1 command">have</span> <span class="quoted quoted"><span>"</span><span class="main">…</span> <span class="main">=</span></span> ennreal <span class="main">(</span><span class="main">1</span> <span class="main">/</span> <span class="numeral">2</span><span class="main">^</span><span class="free">n</span><span class="main">)</span><span>"</span>
      <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> n power_diff cardΩ<span class="main">)</span>
    <span class="keyword1 command">finally</span> <span class="keyword3 command">show</span> <span class="var quoted var">?thesis</span>
      <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> P.emeasure_eq_measure<span class="main">)</span>
  <span class="keyword1 command">qed</span>
</pre>

### Finishing up the argument

The rest of the proof should be straightforward,
but needs to be annoyingly detailed in Isabelle.
We begin by showing that the union is a subset of $\Omega$, 
and therefore an event.

<pre class="source">
  <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span><span class="main">⋃</span><span class="bound">F</span><span class="main">∈</span><span class="free">𝓕</span><span class="main">.</span> <span class="main">⋃</span><span class="bound">c</span><span class="main">&lt;</span><span class="numeral">2</span><span class="main">.</span> <span class="skolem">mchrome</span> <span class="bound">c</span> <span class="bound">F</span><span class="main">)</span> <span class="main">⊆</span></span> <span class="skolem">Ω</span><span>"</span></span>
    <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> mchrome_def Ω_def<span class="main">)</span>
</pre>

To show that the union is actually a **strict** subset
involves formalising the proof that $P(\bigcup_{A\in\cal F} E_A) < 1$.
<pre class="source">
  <span class="keyword1 command">moreover</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span><span class="main">⋃</span><span class="bound">F</span><span class="main">∈</span><span class="free">𝓕</span><span class="main">.</span> <span class="main">⋃</span><span class="bound">c</span><span class="main">&lt;</span><span class="numeral">2</span><span class="main">.</span> <span class="skolem">mchrome</span> <span class="bound">c</span> <span class="bound">F</span><span class="main">)</span> <span class="main">≠</span></span> <span class="skolem">Ω</span><span>"</span></span>
  <span class="keyword1 command">proof</span> <span class="operator">-</span>
    <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span>P.prob</span> <span class="main">(</span><span class="main">⋃</span><span class="bound">F</span><span class="main">∈</span><span class="free">𝓕</span><span class="main">.</span> <span class="main">⋃</span><span class="bound">c</span><span class="main">&lt;</span><span class="numeral">2</span><span class="main">.</span> <span class="skolem">mchrome</span> <span class="bound">c</span> <span class="bound">F</span><span class="main">)</span> <span class="main">≤</span></span> <span class="main">(</span><span class="main">∑</span><span class="bound">F</span><span class="main">∈</span><span class="free">𝓕</span><span class="main">.</span> P.prob <span class="main">(</span><span class="main">⋃</span><span class="bound">c</span><span class="main">&lt;</span><span class="numeral">2</span><span class="main">.</span> <span class="skolem">mchrome</span> <span class="bound">c</span> <span class="bound">F</span><span class="main">)</span><span class="main">)</span><span>"</span>
      <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">intro</span> measure_UNION_le<span class="main">)</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> countable_Un_Int mchrome <span class="quoted"><span class="quoted"><span>‹</span>finite</span> <span class="free">𝓕</span><span>›</span></span><span class="main">)</span>
    <span class="keyword1 command">also</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">…</span> <span class="main">≤</span></span> <span class="main">(</span><span class="main">∑</span><span class="bound">F</span><span class="main">∈</span><span class="free">𝓕</span><span class="main">.</span> <span class="main">∑</span><span class="bound">c</span><span class="main">&lt;</span><span class="numeral">2</span><span class="main">.</span> P.prob</span> <span class="main">(</span><span class="skolem">mchrome</span> <span class="bound">c</span> <span class="bound">F</span><span class="main">)</span><span class="main">)</span><span>"</span>
      <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">intro</span> sum_mono measure_UNION_le<span class="main">)</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> mchrome<span class="main">)</span>
    <span class="keyword1 command">also</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">…</span> <span class="main">=</span></span> <span class="free">m</span> <span class="main">*</span></span> <span class="numeral">2</span> <span class="main">*</span> <span class="main">(</span><span class="main">1</span> <span class="main">/</span> <span class="numeral">2</span><span class="main">^</span><span class="free">n</span><span class="main">)</span><span>"</span>
      <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> prob_mchrome <span class="quoted"><span class="quoted"><span>‹</span>card</span> <span class="free">𝓕</span> <span class="main">=</span></span> <span class="free">m</span><span>›</span><span class="main">)</span>
    <span class="keyword1 command">also</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">…</span> <span class="main">&lt;</span></span> <span class="main">1</span></span><span>"</span>
    <span class="keyword1 command">proof</span> <span class="operator">-</span>
      <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span>real</span> <span class="main">(</span><span class="free">m</span> <span class="main">*</span></span> <span class="numeral">2</span><span class="main">)</span> <span class="main">&lt;</span> <span class="numeral">2</span> <span class="main">^</span> <span class="free">n</span><span>"</span>
        <span class="keyword1 command">using</span> mult_strict_right_mono <span class="main">[</span><span class="operator">OF</span> m<span class="main">,</span> <span class="operator">of</span> <span class="quoted numeral">2</span><span class="main">]</span> <span class="quoted"><span class="quoted"><span>‹</span><span class="free">n</span><span class="main">&gt;</span></span><span class="main">0</span></span><span>›</span>
        <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> of_nat_less_numeral_power_cancel_iff pos2 power_minus_mult<span class="main">)</span> 
      <span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="var quoted var">?thesis</span>
        <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> <span class="dynamic dynamic">divide_simps</span><span class="main">)</span>
    <span class="keyword1 command">qed</span>
    <span class="keyword1 command">finally</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span>P.prob</span> <span class="main">(</span><span class="main">⋃</span><span class="bound">F</span><span class="main">∈</span><span class="free">𝓕</span><span class="main">.</span> <span class="main">⋃</span><span class="bound">c</span><span class="main">&lt;</span><span class="numeral">2</span><span class="main">.</span> <span class="skolem">mchrome</span> <span class="bound">c</span> <span class="bound">F</span><span class="main">)</span> <span class="main">&lt;</span></span> <span class="main">1</span><span>"</span> <span class="keyword1 command">.</span>
    <span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="var quoted var">?thesis</span>
      <span class="keyword1 command">using</span> P.prob_space space_eq <span class="keyword1 command">by</span> <span class="operator">force</span>
  <span class="keyword1 command">qed</span>
</pre>

The conclusion of the theorem is now immediate.
Recall that <span class="keyword1 command">moreover</span> 
accumulates prior lemmas, 
which <span class="keyword1 command">ultimately</span> 
makes available to the next proof.

<pre class="source">
  <span class="keyword1 command">ultimately</span> <span class="keyword3 command">obtain</span> <span class="skolem skolem">f</span> <span class="keyword2 keyword">where</span> f<span class="main">:</span><span class="quoted"><span class="quoted"><span>"</span><span class="skolem">f</span> <span class="main">∈</span></span> <span class="skolem">Ω</span> <span class="main">-</span></span> <span class="main">(</span><span class="main">⋃</span><span class="bound">F</span><span class="main">∈</span><span class="free">𝓕</span><span class="main">.</span> <span class="main">⋃</span><span class="bound">c</span><span class="main">&lt;</span><span class="numeral">2</span><span class="main">.</span> <span class="skolem">mchrome</span> <span class="bound">c</span> <span class="bound">F</span><span class="main">)</span><span>"</span>
    <span class="keyword1 command">by</span> <span class="operator">blast</span>
  <span class="keyword1 command">with</span> that <span class="keyword3 command">show</span> <span class="var quoted var">?thesis</span>
    <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">fastforce</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> mchrome_def Ω_def<span class="main">)</span>
<span class="keyword1 command">qed</span>
</pre>

### Postscript

The probabilistic method is simply a more intuitive way of presenting
a proof by counting. The original example of such a proof
is claimed to be Erdős's "[Some remarks on the theory of graphs](https://www.ams.org/journals/bull/1947-53-04/S0002-9904-1947-08785-1/S0002-9904-1947-08785-1.pdf)" (1947).
This paper indeed presents a proof of a lower bound for Ramsey numbers,
but it makes no reference to probability and instead 
enumerates the total number of graphs satisfying certain properties.
Presumably he published a probabilistic version of that proof
at a later date.

A recent [paper](/papers/Edmonds-CPP2024.pdf) by Chelsea Edmonds
describes the formalisation of probabilistic proofs in 
considerably more detail.

The examples for this post are online [here](/Isabelle-Examples/Probabilistic_Example_Erdos.thy).
