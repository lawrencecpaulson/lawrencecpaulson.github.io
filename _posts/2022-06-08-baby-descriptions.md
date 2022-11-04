---
layout: post
title:  "Dealing with descriptions in Isabelle/HOL: least, greatest, whatever"
usemathjax: true
tags: [examples, Isabelle, newbies, descriptions, sledgehammer, David Hilbert]
---

A description is a term that designates "the least", "the greatest" or simply "any" *x* such that Φ(*x*): it describes the desired value (or simply *any suitable* value) in the language of its properties.
The built-in facts governing `Min`, `Max`, etc. are straightforward, but getting what you want from them is often frustrating.
Let's take a look at a few contrived, but (I hope) illustrative examples, leaving all the proofs to [sledgehammer]({% post_url 2022-04-13-Sledgehammer %}).

### The range of description operators

A great variety of functions are available. Here are the main ones:

* `Least`/`Greatest` denote the least/greatest value satisfying a given predicate calculus *formula*. The corresponding Isabelle keyword is `LEAST`/`GREATEST`.
* `Min`/`Max`: these functions are suitable for non-empty, **finite** sets. The underlying type must be linearly ordered (belong to type class `linorder`).
* `Inf`/`Sup` are functions to denote the infimum/supremum of possibly infinite or empty sets. These come in two versions, for complete lattices and for conditionally complete lattices.
* `Eps` is [Hilbert's $\epsilon$-operator]({% post_url 2021-11-10-Axiom_of_Choice %}), which yields the full [axiom of choice]({% post_url 2021-11-10-Axiom_of_Choice %}) (AC). The corresponding Isabelle keyword is `SOME`. Although a *unique* description operator also exists, it has become obsolete: Isabelle/HOL no longer offers the option to work without AC.
(That option remains available in [Isabelle/ZF]({% post_url 2022-01-26-Set_theory %}).)

Unsurprisingly, some of these are defined in terms of others, with `Eps` as the base primitive. Type classes play a major role. For example, a type in class `wellorder` is guaranteed to have suitable `Least` elements for any non-False predicate.


### A silly theorem statement

The following nonsensical "theorem" will be the basis for a couple of simple examples. We are given a set 𝒮 of nonempty open balls (in a metric space) and a set `L` of lists of natural numbers.
Our task is to prove something or other.

<pre class="source">
<span class="keyword1 command">lemma</span><span>
  </span><span class="keyword2 keyword">fixes</span> <span class="free">𝒮</span> <span class="main">::</span> <span class="quoted quoted"><span>"</span><span class="tfree">'a</span><span class="main">::</span>metric_space set set<span>"</span></span> <span class="keyword2 keyword">and</span> <span class="free">L</span> <span class="main">::</span> <span class="quoted quoted"><span>"</span>nat list set<span>"</span></span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted quoted"><span>"</span><span class="free">𝒮</span> <span class="main">⊆</span> <span class="main">{</span>ball <span class="bound">x</span> <span class="bound">r</span> <span class="main">|</span> <span class="bound">x</span> <span class="bound">r</span><span class="main">.</span> <span class="bound">r</span><span class="main">&gt;</span><span class="main">0</span><span class="main">}</span><span>"</span></span> <span class="keyword2 keyword">and</span> <span class="quoted quoted"><span>"</span><span class="free">L</span> <span class="main">≠</span> <span class="main">{}</span><span>"</span></span><span>
  </span><span class="keyword2 keyword">shows</span> <span class="quoted quoted"><span>"</span><span class="free">P</span> <span class="free">𝒮</span> <span class="free">L</span><span>"</span></span>
</pre>

### Example 1: defining the radius and centre of a ball

Every element of 𝒮 has the form `ball x r`, where `x` is its centre and `r` is its necessarily positive radius:

<pre class="source">
  <span class="keyword1 command">have</span> <span class="quoted quoted"><span>"</span><span class="main">⋀</span><span class="bound">B</span><span class="main">.</span> <span class="bound">B</span> <span class="main">∈</span> <span class="free">𝒮</span> <span class="main">⟹</span> <span class="main">∃</span><span class="bound">x</span><span class="main">.</span> <span class="main">∃</span><span class="bound bound">r</span><span class="main">&gt;</span><span class="main">0</span><span class="main">.</span> <span class="bound">B</span> <span class="main">=</span> ball <span class="bound">x</span> <span class="bound">r</span><span>"</span></span><span>
    </span><span class="keyword1 command">using</span> assms <span class="keyword1 command">by</span> <span class="operator">blast</span>
</pre>

Whenever you have such a forall-exists fact, you can transform it into exists-forall, obtaining a function. Note that the transformation from $\forall x.\, \exists y.\, \Phi(x,y)$ into
$\exists f.\, \forall x.\, \Phi(x,\,f(x))$ can require AC, in general.
You could define $f$ explicitly using Hilbert's epsilon, but there's an easier way.
All you have to do is write out the properties you want, as long as they are clearly based on the previous forall-exists result.
For the proof, simply call `metis`.
Here, we get two functions at the same time!

<pre class="source">
  <span class="keyword1 command">then</span> <span class="keyword3 command">obtain</span> <span class="skolem skolem">centre</span> <span class="skolem skolem">rad</span> <span class="keyword2 keyword">where</span> rad<span class="main">:</span> <span class="quoted quoted"><span>"</span><span class="main">⋀</span><span class="bound">B</span><span class="main">.</span> <span class="bound">B</span> <span class="main">∈</span> <span class="free">𝒮</span> <span class="main">⟹</span> <span class="skolem">rad</span> <span class="bound">B</span> <span class="main">&gt;</span> <span class="main">0</span><span>"</span></span><span>
                         </span><span class="keyword2 keyword">and</span> centre<span class="main">:</span> <span class="quoted quoted"><span>"</span><span class="main">⋀</span><span class="bound">B</span><span class="main">.</span> <span class="bound">B</span> <span class="main">∈</span> <span class="free">𝒮</span> <span class="main">⟹</span> <span class="bound">B</span> <span class="main">=</span> ball <span class="main">(</span><span class="skolem">centre</span> <span class="bound">B</span><span class="main">)</span> <span class="main">(</span><span class="skolem">rad</span> <span class="bound">B</span><span class="main">)</span><span>"</span></span><span>
    </span><span class="keyword1 command">by</span> <span class="operator">metis</span>
</pre>

If you try this and the `metis` call hangs, it's likely that your forall-exists formula is too complicated (or just wrong). Simplify it by making definitions.

### Example 2: What is the minimum radius?

The infimum of all the radii of the balls in 𝒮 is easily defined.
It exists because there's a lower bound (zero).
The use of the image operator is typical: this is the simplest way to denote the set of all radii of elements of 𝒮.

<pre class="source">
  <span class="keyword3 command">define</span> <span class="skolem skolem">infrad</span> <span class="keyword2 keyword">where</span> <span class="quoted quoted"><span>"</span><span class="skolem">infrad</span> <span class="main">≡</span> Inf <span class="main">(</span><span class="skolem">rad</span> <span class="main">`</span> <span class="free">𝒮</span><span class="main">)</span><span>"</span></span>
</pre>

The key property of the infimum is that no other ball in 𝒮 has a smaller radius.

<pre class="source">
  <span class="keyword1 command">have</span> <span class="quoted quoted"><span>"</span><span class="skolem">infrad</span> <span class="main">≤</span> <span class="skolem">rad</span> <span class="skolem">B</span><span>"</span></span> <span class="keyword2 keyword">if</span> <span class="quoted quoted"><span>"</span><span class="skolem">B</span> <span class="main">∈</span> <span class="free">𝒮</span><span>"</span></span> <span class="keyword2 keyword">for</span> <span class="skolem">B</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">smt</span> <span class="main main">(</span>verit<span class="main main">,</span> best<span class="main main">)</span> bdd_below.I cINF_lower image_iff infrad_def rad that<span class="main">)</span>
</pre>

It's possible for the infimum of a set to be strictly smaller than every element; for example, the infimum of the set of positive reals is zero.
But if the set is finite and nonempty, its infimum is actually an element.

<pre class="source">
  <span class="keyword1 command">have</span> <span class="quoted quoted"><span>"</span><span class="main">∃</span><span class="bound">B</span> <span class="main">∈</span> <span class="free">𝒮</span><span class="main">.</span> <span class="skolem">rad</span> <span class="bound">B</span> <span class="main">=</span> <span class="skolem">infrad</span><span>"</span></span> <span class="keyword2 keyword">if</span> <span class="quoted quoted"><span>"</span>finite <span class="free">𝒮</span><span>"</span></span> <span class="quoted quoted"><span>"</span><span class="free">𝒮</span> <span class="main">≠</span> <span class="main">{}</span><span>"</span></span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">smt</span> <span class="main main">(</span>verit<span class="main main">)</span> empty_is_image finite_imageI finite_less_Inf_iff imageE infrad_def that<span class="main">)</span>
</pre>


### Example 3: Find a list of minimum length

If you want to grab an element minimising some attribute, obtain the minimum value of the attribute first.
Here, we define the minimum of all the lengths of the lists in `L`.
Note, again, the use of the image operator.

<pre class="source">
  <span class="keyword3 command">define</span> <span class="skolem skolem">minl</span> <span class="keyword2 keyword">where</span> <span class="quoted quoted"><span>"</span><span class="skolem">minl</span> <span class="main">=</span> Inf <span class="main">(</span>length <span class="main">`</span> <span class="free">L</span><span class="main">)</span><span>"</span></span>
</pre>

Now we can obtain an element of `L` of length `minl`.
It exists because the set `L` is non-empty. That set does not have to be finite because *every* set of natural numbers has a least element.

<pre class="source">
  <span class="keyword3 command">obtain</span> <span class="skolem skolem">l0</span> <span class="keyword2 keyword">where</span>  <span class="quoted quoted"><span>"</span><span class="skolem">l0</span> <span class="main">∈</span> <span class="free">L</span><span>"</span></span> <span class="quoted quoted"><span>"</span>length <span class="skolem">l0</span> <span class="main">=</span> <span class="skolem">minl</span><span>"</span></span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> Inf_nat_def1 empty_is_image imageE minl_def <span class="quoted quoted"><span>‹</span><span class="free">L</span> <span class="main">≠</span> <span class="main">{}</span><span>›</span></span><span class="main">)</span>
</pre>

Now we check the key property, namely that the length of `l0` is minimal among the lengths of every element of `L`.

<pre class="source">
  <span class="keyword1 command">then</span> <span class="keyword1 command">have</span> <span class="quoted quoted"><span>"</span>length <span class="skolem">l0</span> <span class="main">≤</span> length <span class="skolem">l</span><span>"</span></span> <span class="keyword2 keyword">if</span> <span class="quoted quoted"><span>"</span><span class="skolem">l</span> <span class="main">∈</span> <span class="free">L</span><span>"</span></span> <span class="keyword2 keyword">for</span> <span class="skolem">l</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> cINF_lower minl_def that<span class="main">)</span>
</pre>

### Final remarks

Novices often seem to let their formulas get too large. Remember to use definitions to keep your formulas small, especially in situations such as these.
You may wonder whether `minl` needed to be defined at all, as it's almost nothing.
And indeed `l0` can still be obtained, but the proof is an order of magnitude slower: simplicity really matters here.
And just a reminder, **every one** of the proofs above was found by sledgehammer.
