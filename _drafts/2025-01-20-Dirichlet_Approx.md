---
layout: post
title:  "Formalising an easy proof: Dirichlet's approximation theorem"
usemathjax: true 
tags: [examples, Isar, formalised mathematics]
---
For many, the process of transforming a textbook mathematical proof
into a formal document remains mysterious.
Here, we look at a fairly elementary example.
Dirichlet's approximation theorem states that there exists a rational approximation 
to any given real number such that the denominator is relatively small.
The proof combines an application of the pigeonhole principle
with some straightforward calculations.
Formalised, it's only about 50 lines long.
There are still a couple of tricky bits to deal with!

### The textbook proof

Consider the problem of approximating π by a rational number.
Any finite decimal representation of π is rational,
but the denominators are large powers of 10 when we can do much better:
355/113 = 3.1415929 approximates π 
to seven significant figures (the true value is 3.14159265).
Dirichlet's approximation theorem says that given the real number
$\theta$, for every integer $N>0$ 
there exist integers $h$ and $k$ with $0<k \le N$ such that
$\vert k\theta-h\vert < 1/N$.
Thus, $h/k$ is a good approximation to $\theta$.

Here is the proof, which comes from 
*Modular Functions and Dirichlet Series in Number Theory* 
by Tom M. Apostol, page 143.

<img src="/images/Dirichlet-approx-thm.png" width="650"/>

<img src="/images/Dirichlet-approx-thm.png" width="650"/>

### Starting the formalisation

<pre class="source">
<span class="keyword1 command">theorem</span> Dirichlet_approx<span class="main">:</span><span>
  </span><span class="keyword2 keyword">fixes</span> <span class="free">θ</span><span class="main">::</span><span class="tconst">real</span> <span class="keyword2 keyword">and</span> <span class="free">N</span><span class="main">::</span><span class="tconst">nat</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">N</span> <span class="main">&gt;</span></span> <span class="main">0</span></span><span>"</span><span> 
  </span><span class="keyword2 keyword">obtains</span> <span class="free">h</span> <span class="free">k</span> <span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">0</span></span> <span class="main">&lt;</span></span> <span class="free">k</span><span>"</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">k</span> <span class="main">≤</span></span> </span><span class="const">int</span> <span class="free">N</span><span>"</span> <span class="quoted quoted"><span>"</span><span class="main">¦</span></span><span class="const">of_int</span> <span class="free">k</span><span class="main">*</span><span class="free">θ</span> <span class="main">-</span> <span class="const">of_int</span> <span class="free">h</span><span class="main">¦</span> <span class="main">&lt;</span> <span class="main">1</span><span class="main">/</span><span class="free">N</span><span>"</span><span>
</span><span class="keyword1 command">proof</span> <span class="operator">-</span>
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
