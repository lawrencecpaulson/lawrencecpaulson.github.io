---
layout: post
title:  "Dealing with descriptions in Isabelle: choice, least, greatest"
usemathjax: true 
tags: examples, Isabelle, newbies, descriptions
---

A description is a term that designates "the least", "the greatest" or simply "any" *x* such that Φ(*x*): it literally describes the desired (or simply *any suitable*) value in in language of its properties.
The built-in facts governing Min, Max, etc. are straightforward, but getting what you want from them is often frustratingly difficult.
Often it's best to give the job to sledgehammer.
Let's take a look at a few contrived, but (I hope) illustrative examples.

### The range of description operators

A great variety of functions are available. Here are the main ones:

* `Least`/`Greatest` denote the least/greatest value satisfying a given *formula*. The corresponding Isabelle keyword is `LEAST`/`GREATEST`.
* `Min`/`Max`: these are suitable for non-empty, **finite** sets. The underlyibg type must be linearly ordered (belong to type class `linorder`).
* `Inf`/`Sup` denote the infimum/supremum of possibly infinite or empty sets. These come in two versions, for complete lattices and for conditionally complete lattices.
* `Eps` is Hilbert's $\epsilon$-operator, which is a full version of the axiom of choice. The corresponding Isabelle keyword is `SOME`. Although a unique description operator also exists, it's obsolute: Isabelle/HOL no longer offers the option to work without AC.

Unsurprisingly, some of these are defined in terms of others, with `Eps` as the true primitive. Type classes play a major role. For example, a type in class `wellorder` is guaranteed to have suitable `Least` elements for any non-False predicate.


### A dummy theorem statement

<pre class="source">
<span class="keyword1 command">lemma</span><span> 
  </span><span class="keyword2 keyword">fixes</span> <span class="free">𝒮</span> <span class="main">::</span> <span class="quoted quoted"><span>"</span><span class="tfree">'a</span><span class="main">::</span>metric_space set set<span>"</span></span> <span class="keyword2 keyword">and</span> <span class="free">L</span> <span class="main">::</span> <span class="quoted quoted"><span>"</span>nat list set<span>"</span></span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted quoted"><span>"</span><span class="free">𝒮</span> <span class="main">⊆</span> <span class="main">{</span>ball <span class="bound">x</span> <span class="bound">r</span> <span class="main">|</span> <span class="bound">x</span> <span class="bound">r</span><span class="main">.</span> <span class="bound">r</span><span class="main">&gt;</span><span class="main">0</span><span class="main">}</span><span>"</span></span> <span class="keyword2 keyword">and</span> <span class="quoted quoted"><span>"</span><span class="free">L</span> <span class="main">≠</span> <span class="main">{}</span><span>"</span></span><span>
  </span><span class="keyword2 keyword">shows</span> <span class="quoted quoted"><span>"</span><span class="free">P</span> <span class="free">𝒮</span> <span class="free">L</span><span>"</span></span>
</pre>

### Task 1: define the radius and centre of a ball

<pre class="source">
  <span class="keyword1 command">have</span> <span class="quoted quoted"><span>"</span><span class="main">⋀</span><span class="bound">B</span><span class="main">.</span> <span class="bound">B</span> <span class="main">∈</span> <span class="free">𝒮</span> <span class="main">⟹</span> <span class="main">∃</span><span class="bound">x</span><span class="main">.</span> <span class="main">∃</span><span class="bound bound">r</span><span class="main">&gt;</span><span class="main">0</span><span class="main">.</span> <span class="bound">B</span> <span class="main">=</span> ball <span class="bound">x</span> <span class="bound">r</span><span>"</span></span><span>
    </span><span class="keyword1 command">using</span> assms <span class="keyword1 command">by</span> <span class="operator">blast</span>
</pre>


<pre class="source">
  <span class="keyword1 command">then</span> <span class="keyword3 command">obtain</span> <span class="skolem skolem">centre</span> <span class="skolem skolem">rad</span> <span class="keyword2 keyword">where</span> rad<span class="main">:</span> <span class="quoted quoted"><span>"</span><span class="main">⋀</span><span class="bound">B</span><span class="main">.</span> <span class="bound">B</span> <span class="main">∈</span> <span class="free">𝒮</span> <span class="main">⟹</span> <span class="skolem">rad</span> <span class="bound">B</span> <span class="main">&gt;</span> <span class="main">0</span><span>"</span></span><span> 
                         </span><span class="keyword2 keyword">and</span> centre<span class="main">:</span> <span class="quoted quoted"><span>"</span><span class="main">⋀</span><span class="bound">B</span><span class="main">.</span> <span class="bound">B</span> <span class="main">∈</span> <span class="free">𝒮</span> <span class="main">⟹</span> <span class="bound">B</span> <span class="main">=</span> ball <span class="main">(</span><span class="skolem">centre</span> <span class="bound">B</span><span class="main">)</span> <span class="main">(</span><span class="skolem">rad</span> <span class="bound">B</span><span class="main">)</span><span>"</span></span><span>
    </span><span class="keyword1 command">by</span> <span class="operator">metis</span>
</pre>


<pre class="source">
  <span class="keyword3 command">define</span> <span class="skolem skolem">infrad</span> <span class="keyword2 keyword">where</span> <span class="quoted quoted"><span>"</span><span class="skolem">infrad</span> <span class="main">≡</span> Inf <span class="main">(</span><span class="skolem">rad</span> <span class="main">`</span> <span class="free">𝒮</span><span class="main">)</span><span>"</span></span>
</pre>


<pre class="source">
  <span class="keyword1 command">have</span> <span class="quoted quoted"><span>"</span><span class="skolem">infrad</span> <span class="main">≤</span> <span class="skolem">rad</span> <span class="skolem">B</span><span>"</span></span> <span class="keyword2 keyword">if</span> <span class="quoted quoted"><span>"</span><span class="skolem">B</span> <span class="main">∈</span> <span class="free">𝒮</span><span>"</span></span> <span class="keyword2 keyword">for</span> <span class="skolem">B</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">smt</span> <span class="main main">(</span>verit<span class="main main">,</span> best<span class="main main">)</span> bdd_below.I cINF_lower image_iff infrad_def rad that<span class="main">)</span>
</pre>


<pre class="source">
  <span class="keyword1 command">have</span> <span class="quoted quoted"><span>"</span><span class="main">∃</span><span class="bound">B</span> <span class="main">∈</span> <span class="free">𝒮</span><span class="main">.</span> <span class="skolem">rad</span> <span class="bound">B</span> <span class="main">=</span> <span class="skolem">infrad</span><span>"</span></span> <span class="keyword2 keyword">if</span> <span class="quoted quoted"><span>"</span>finite <span class="free">𝒮</span><span>"</span></span> <span class="quoted quoted"><span>"</span><span class="free">𝒮</span> <span class="main">≠</span> <span class="main">{}</span><span>"</span></span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">smt</span> <span class="main main">(</span>verit<span class="main main">)</span> empty_is_image finite_imageI finite_less_Inf_iff imageE infrad_def that<span class="main">)</span>
</pre>


<pre class="source">
</pre>


### Task 2: Find a list of minimum length

<pre class="source">
<span class="keyword3 command">define</span> <span class="skolem skolem">minl</span> <span class="keyword2 keyword">where</span> <span class="quoted quoted"><span>"</span><span class="skolem">minl</span> <span class="main">=</span> Inf <span class="main">(</span>length <span class="main">`</span> <span class="free">L</span><span class="main">)</span><span>"</span></span>
</pre>


<pre class="source">
  <span class="keyword3 command">obtain</span> <span class="skolem skolem">l0</span> <span class="keyword2 keyword">where</span>  <span class="quoted quoted"><span>"</span><span class="skolem">l0</span> <span class="main">∈</span> <span class="free">L</span><span>"</span></span> <span class="quoted quoted"><span>"</span>length <span class="skolem">l0</span> <span class="main">=</span> <span class="skolem">minl</span><span>"</span></span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> Inf_nat_def1 empty_is_image imageE minl_def <span class="quoted quoted"><span>‹</span><span class="free">L</span> <span class="main">≠</span> <span class="main">{}</span><span>›</span></span><span class="main">)</span>
</pre>


<pre class="source">
  <span class="keyword1 command">then</span> <span class="keyword1 command">have</span> <span class="quoted quoted"><span>"</span>length <span class="skolem">l0</span> <span class="main">≤</span> length <span class="skolem">l</span><span>"</span></span> <span class="keyword2 keyword">if</span> <span class="quoted quoted"><span>"</span><span class="skolem">l</span> <span class="main">∈</span> <span class="free">L</span><span>"</span></span> <span class="keyword2 keyword">for</span> <span class="skolem">l</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> cINF_lower minl_def that<span class="main">)</span>
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


