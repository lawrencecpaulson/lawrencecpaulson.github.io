---
layout: post
title:  For the holidays, some problems about prime divisors
usemathjax: true 
tags: [Isabelle,examples,formalised mathematics]
---
Just in time for the holiday break, here are some small exercises to build your skills. 
The subject matter is the prime numbers: specifically, the maximum exponent of a prime divisor of a number. 
A skeleton Isabelle [theory file](/Isabelle-Examples/Index_ex.thy) is available, containing all statements of the theorems and necessary definitions or boilerplate, but no proofs. 
Your task – when not eating, drinking, or watching movies – is to do the proofs, Some are harder than others.

### Defining the notion of index

First, a simple fact: if $p$ is prime and $p^k$ divides $mn$,
then we can write $k=i+j$ where $p^i$ divides $m$ and $p^j$ divides $n$.
It is trivial because a similar proof is built-in and sledgehammer will find it for you.

<pre class="source">
<span class="keyword1 command">lemma</span> primepow_divides_prod<span class="main">:</span><span>
  </span><span class="keyword2 keyword">fixes</span> <span class="free">p</span><span class="main">::</span><span class="quoted">nat</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span>prime</span> <span class="free">p</span><span>"</span></span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span><span class="free">p</span><span class="main">^</span></span><span class="free">k</span><span class="main">)</span> <span class="keyword1">dvd</span></span> <span class="main">(</span><span class="free">m</span> <span class="main">*</span> <span class="free">n</span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">∃</span></span><span class="bound">i</span> <span class="bound">j</span><span class="main">.</span></span> <span class="main">(</span><span class="free">p</span><span class="main">^</span><span class="bound">i</span><span class="main">)</span> <span class="keyword1">dvd</span> <span class="free">m</span> <span class="main">∧</span> <span class="main">(</span><span class="free">p</span><span class="main">^</span><span class="bound">j</span><span class="main">)</span> <span class="keyword1">dvd</span> <span class="free">n</span> <span class="main">∧</span> <span class="free">k</span> <span class="main">=</span> <span class="bound">i</span> <span class="main">+</span> <span class="bound">j</span><span>"</span><span>
  </span><span class="keyword1 command">sorry</span>
</pre>

To reason about the maximum exponent of a prime divisor,
we need to show that this maximum exists.
It might be helpful to consider the set of all
$k$ such that $p^k$ divides $n$.
A structured proof that establishes a natural series of 
basic facts about this set leads to the conclusion.

<pre class="source">
<span class="keyword1 command">lemma</span> maximum_index<span class="main">:</span><span>
  </span><span class="keyword2 keyword">fixes</span> <span class="free">n</span><span class="main">::</span><span class="quoted">nat</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">n</span> <span class="main">&gt;</span></span> <span class="main">0</span></span><span>"</span> <span class="quoted"><span class="quoted"><span>"</span><span class="numeral">2</span> <span class="main">≤</span></span> <span class="free">p</span><span>"</span></span><span>
  </span><span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">∃</span></span><span class="bound">k</span><span class="main">.</span></span> <span class="free">p</span><span class="main">^</span><span class="bound">k</span> <span class="keyword1">dvd</span> <span class="free">n</span> <span class="main">∧</span> <span class="main">(</span><span class="main">∀</span><span class="bound bound">l</span><span class="main">&gt;</span><span class="bound">k</span><span class="main">.</span> <span class="main">¬</span> <span class="free">p</span><span class="main">^</span><span class="bound">l</span> <span class="keyword1">dvd</span> <span class="free">n</span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword1 command">sorry</span>
</pre>

Having proved that the maximum index exists, 
we could refer to the maximum directly, 
using the function `Max`.
Instead, the definition below refers to
the cardinality of the set of possible non-zero indices.
The practical effect of this choice is probably insignificant.

<pre class="source">
<span class="keyword1 command">definition</span> <span class="entity">index</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>nat</span> <span class="main">⇒</span> nat</span> <span class="main">⇒</span> nat<span>"</span> <span class="keyword2 keyword">where</span><span>
  </span><span class="quoted"><span class="quoted"><span>"</span><span class="free">index</span> <span class="free bound entity">p</span> <span class="free bound entity">n</span><span> 
    </span><span class="main">≡</span> <span class="keyword1">if</span></span> <span class="free bound entity">p</span> <span class="main">≤</span></span> <span class="main">1</span> <span class="main">∨</span> <span class="free bound entity">n</span> <span class="main">=</span> <span class="main">0</span> <span class="keyword1">then</span> <span class="main">0</span> <span class="keyword1">else</span> card <span class="main">{</span><span class="bound">j</span><span class="main">.</span> <span class="main">1</span> <span class="main">≤</span> <span class="bound">j</span> <span class="main">∧</span> <span class="free bound entity">p</span><span class="main">^</span><span class="bound">j</span> <span class="keyword1">dvd</span> <span class="free bound entity">n</span><span class="main">}</span><span>"</span>
</pre>

### Simple consequences of the definition

The next task is to show that our definition satisfies its objective, characterising $p^k \mid n$.
It would make sense to consider carefully the form of the definition, 
dealing with the degenerate cases separately.

<pre class="source">
<span class="keyword1 command">proposition</span> pow_divides_index<span class="main">:</span><span>
  </span><span class="quoted"><span class="quoted"><span>"</span><span class="free">p</span><span class="main">^</span></span><span class="free">k</span> <span class="keyword1">dvd</span></span> <span class="free">n</span> <span class="main">⟷</span> <span class="free">n</span> <span class="main">=</span> <span class="main">0</span> <span class="main">∨</span> <span class="free">p</span> <span class="main">=</span> <span class="main">1</span> <span class="main">∨</span> <span class="free">k</span> <span class="main">≤</span> index <span class="free">p</span> <span class="free">n</span><span>"</span><span>
  </span><span class="keyword1 command">sorry</span>
</pre>

From that key result, a couple of corollaries follow directly:

<pre class="source">
<span class="keyword1 command">corollary</span> le_index<span class="main">:</span><span>
  </span><span class="quoted"><span class="quoted"><span>"</span><span class="free">k</span> <span class="main">≤</span></span> index</span> <span class="free">p</span> <span class="free">n</span> <span class="main">⟷</span> <span class="main">(</span><span class="free">n</span> <span class="main">=</span> <span class="main">0</span> <span class="main">∨</span> <span class="free">p</span> <span class="main">=</span> <span class="main">1</span> <span class="main">⟶</span> <span class="free">k</span> <span class="main">=</span> <span class="main">0</span><span class="main">)</span> <span class="main">∧</span> <span class="free">p</span><span class="main">^</span><span class="free">k</span> <span class="keyword1">dvd</span> <span class="free">n</span><span>"</span><span>
  </span><span class="keyword1 command">sorry</span>
</pre>

<pre class="source">
<span class="keyword1 command">corollary</span> exp_index_divides<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">p</span><span class="main">^</span></span><span class="main">(</span>index</span> <span class="free">p</span> <span class="free">n</span><span class="main">)</span> <span class="keyword1">dvd</span> <span class="free">n</span><span>"</span><span>
  </span><span class="keyword1 command">sorry</span>
</pre>

### And some slightly more difficult problems

The following upper bound for the index of a prime divisor
isn't difficult to prove, but again the degenerate case needs to be treated separately.

<pre class="source">
<span class="keyword1 command">lemma</span> index_trivial_bound<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>index</span> <span class="free">p</span> <span class="free">n</span> <span class="main">≤</span></span> <span class="free">n</span><span>"</span><span>
  </span><span class="keyword1 command">sorry</span>
</pre>

Next, you can prove the following natural law for the index of a product.

<pre class="source">
<span class="keyword1 command">proposition</span> index_mult<span class="main">:</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span>prime</span> <span class="free">p</span><span>"</span></span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">m</span> <span class="main">&gt;</span></span> <span class="main">0</span></span><span>"</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">n</span> <span class="main">&gt;</span></span> <span class="main">0</span></span><span>"</span><span>
  </span><span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span>index</span> <span class="free">p</span> <span class="main">(</span><span class="free">m</span> <span class="main">*</span></span> <span class="free">n</span><span class="main">)</span> <span class="main">=</span> index <span class="free">p</span> <span class="free">m</span> <span class="main">+</span> index <span class="free">p</span> <span class="free">n</span><span>"</span><span>
  </span><span class="keyword1 command">sorry</span>
</pre>

To conclude, the analogous law for the index of a power.

<pre class="source">
<span class="keyword1 command">corollary</span> index_exp<span class="main">:</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span>prime</span> <span class="free">p</span><span>"</span></span><span>
  </span><span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span>index</span> <span class="free">p</span> <span class="main">(</span><span class="free">n</span><span class="main">^</span></span><span class="free">k</span><span class="main">)</span> <span class="main">=</span> <span class="free">k</span> <span class="main">*</span> index <span class="free">p</span> <span class="free">n</span><span>"</span><span>
  </span><span class="keyword1 command">sorry</span>
</pre>

To get started, simply download the [theory file](/Isabelle-Examples/Index_ex.thy),
which also contained the necessary Isabelle boilerplate.
If anybody sends me a particularly nice solution to this problem set, I will happily upload it here.
