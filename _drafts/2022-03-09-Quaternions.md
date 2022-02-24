---
layout: post
title:  "The quaterions––and type classes"
usemathjax: true
tags: examples, Isabelle, quaternions
---

The quaternion number system is an extension of the complex numbers to 4 dimensions, introduced by Hamilton in 1843. I translated the [HOL Light formalisation of quaternions](https://doi.org/10.1007/978-3-319-66107-0_15) into Isabelle/HOL some time ago. One notable feature of the formalisation (taken from the Isabelle/HOL formalisation of the complex numbers, rather than from HOL Light) is that its definition can be regarded as coinductive. Moreover, continuing the previous post about axiomatic type classes, we have a dramatic demonstration of how quickly a new class of numbers can be made native.

### Defining the type

Quaternions have the form $a + b \mathbf{i} + c \mathbf{j} + d \mathbf{k}$
where $a$, $b$, $c$ and $d$ are real numbers and $\mathbf{i}$, $\mathbf{j}$, $\mathbf{k}$ are the primitive quaternions, satisfying a number of laws such as 

$$ \mathbf{i}^2 = \mathbf{j}^2 = \mathbf{k}^2 = \mathbf{i}\mathbf{j}\mathbf{k} = -1. $$

It would be natural to represent quaternions by 4-tuples, but it is even simpler to represent them as a codatatype. (The Isabelle/HOL libraries define the complex numbers similarly.) A codatatype is dual to a datatype; just as the latter is specified by enumerating its constructor functions, the former is specified by enumerating its selector functions. The overall effect is similar to a 4-tuple however.

<pre class="source">
<span class="keyword1 command">codatatype</span> quat <span class="main">=</span> Quat <span class="main">(</span><span class="free entity">Re</span><span class="main">:</span> <span class="quoted">real</span><span class="main">)</span> <span class="main">(</span><span class="free entity">Im1</span><span class="main">:</span> <span class="quoted">real</span><span class="main">)</span> <span class="main">(</span><span class="free entity">Im2</span><span class="main">:</span> <span class="quoted">real</span><span class="main">)</span> <span class="main">(</span><span class="free entity">Im3</span><span class="main">:</span> <span class="quoted">real</span><span class="main">)</span>
</pre>

Note that the selectors for $\mathbf{i}$, $\mathbf{j}$, $\mathbf{k}$ are
`Im1`, `Im2`, `Im3`, respectively, while `Re` returns the real part of a quaternion.
It is trivial to prove that two quaternions are equal if and only if their four components all coincide.

<pre class="source">
<span class="keyword1 command">lemma</span> quat_eq_iff<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">=</span> <span class="free">y</span> <span class="main">⟷</span> Re</span> <span class="free">x</span> <span class="main">=</span> Re</span> <span class="free">y</span> <span class="main">∧</span> Im1 <span class="free">x</span> <span class="main">=</span> Im1 <span class="free">y</span> <span class="main">∧</span> Im2 <span class="free">x</span> <span class="main">=</span> Im2 <span class="free">y</span> <span class="main">∧</span> Im3 <span class="free">x</span> <span class="main">=</span> Im3 <span class="free">y</span><span>"</span>
  <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">intro</span><span class="main main">:</span> quat.expand<span class="main">)</span>
</pre>


### Defining the primitive operators

<pre class="source">
<span class="keyword1 command">primcorec</span> <span class="entity">quat_ii</span> <span class="main">::</span> <span class="quoted">quat</span>  <span class="main">(</span><span class="quoted"><span>"</span><span class="keyword1">𝗂</span><span>"</span></span><span class="main">)</span>
  <span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span>Re</span> <span class="keyword1 free">𝗂</span> <span class="main">=</span> <span class="main">0</span><span>"</span></span> <span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span>Im1</span> <span class="keyword1 free">𝗂</span> <span class="main">=</span> <span class="main">1</span><span>"</span></span> <span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span>Im2</span> <span class="keyword1 free">𝗂</span> <span class="main">=</span> <span class="main">0</span><span>"</span></span> <span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span>Im3</span> <span class="keyword1 free">𝗂</span> <span class="main">=</span> <span class="main">0</span><span>"</span></span>

<span class="keyword1 command">primcorec</span> <span class="entity">quat_jj</span> <span class="main">::</span> <span class="quoted">quat</span>  <span class="main">(</span><span class="quoted"><span>"</span><span class="keyword1">𝗃</span><span>"</span></span><span class="main">)</span>
  <span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span>Re</span> <span class="keyword1 free">𝗃</span> <span class="main">=</span> <span class="main">0</span><span>"</span></span> <span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span>Im1</span> <span class="keyword1 free">𝗃</span> <span class="main">=</span> <span class="main">0</span><span>"</span></span> <span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span>Im2</span> <span class="keyword1 free">𝗃</span> <span class="main">=</span> <span class="main">1</span><span>"</span></span> <span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span>Im3</span> <span class="keyword1 free">𝗃</span> <span class="main">=</span> <span class="main">0</span><span>"</span></span>

<span class="keyword1 command">primcorec</span> <span class="entity">quat_kk</span> <span class="main">::</span> <span class="quoted">quat</span>  <span class="main">(</span><span class="quoted"><span>"</span><span class="keyword1">𝗄</span><span>"</span></span><span class="main">)</span>
  <span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span>Re</span> <span class="keyword1 free">𝗄</span> <span class="main">=</span> <span class="main">0</span><span>"</span></span> <span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span>Im1</span> <span class="keyword1 free">𝗄</span> <span class="main">=</span> <span class="main">0</span><span>"</span></span> <span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span>Im2</span> <span class="keyword1 free">𝗄</span> <span class="main">=</span> <span class="main">0</span><span>"</span></span> <span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span>Im3</span> <span class="keyword1 free">𝗄</span> <span class="main">=</span> <span class="main">1</span><span>"</span></span>
</pre>

### Addition and Subtraction: An Abelian Group

<pre class="source">
<span class="keyword1 command">instantiation</span> quat <span class="main">::</span> <span class="quoted">ab_group_add</span>
<span class="keyword2 keyword">begin</span>

<span class="keyword1 command">primcorec</span> <span class="entity class_parameter">zero_quat</span>
  <span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span>Re</span> <span class="main">0</span> <span class="main">=</span> <span class="main">0</span><span>"</span></span> <span class="main">|</span><span class="quoted"><span class="quoted"><span>"</span>Im1</span> <span class="main">0</span> <span class="main">=</span> <span class="main">0</span><span>"</span></span> <span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span>Im2</span> <span class="main">0</span> <span class="main">=</span> <span class="main">0</span><span>"</span></span> <span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span>Im3</span> <span class="main">0</span> <span class="main">=</span> <span class="main">0</span><span>"</span></span>

<span class="keyword1 command">primcorec</span> <span class="entity class_parameter">plus_quat</span>
  <span class="keyword2 keyword">where</span>
    <span class="quoted"><span class="quoted"><span>"</span>Re</span> <span class="main">(</span><span class="free bound entity">x</span> <span class="main">+</span> <span class="free bound entity">y</span><span class="main">)</span> <span class="main">=</span> Re</span> <span class="free bound entity">x</span> <span class="main">+</span> Re <span class="free bound entity">y</span><span>"</span>
  <span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span>Im1</span> <span class="main">(</span><span class="free bound entity">x</span> <span class="main">+</span> <span class="free bound entity">y</span><span class="main">)</span> <span class="main">=</span> Im1</span> <span class="free bound entity">x</span> <span class="main">+</span> Im1 <span class="free bound entity">y</span><span>"</span>
  <span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span>Im2</span> <span class="main">(</span><span class="free bound entity">x</span> <span class="main">+</span> <span class="free bound entity">y</span><span class="main">)</span> <span class="main">=</span> Im2</span> <span class="free bound entity">x</span> <span class="main">+</span> Im2 <span class="free bound entity">y</span><span>"</span>
  <span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span>Im3</span> <span class="main">(</span><span class="free bound entity">x</span> <span class="main">+</span> <span class="free bound entity">y</span><span class="main">)</span> <span class="main">=</span> Im3</span> <span class="free bound entity">x</span> <span class="main">+</span> Im3 <span class="free bound entity">y</span><span>"</span>

<span class="keyword1 command">primcorec</span> <span class="entity class_parameter">uminus_quat</span>
  <span class="keyword2 keyword">where</span>
    <span class="quoted"><span class="quoted"><span>"</span>Re</span> <span class="main">(</span><span class="main">-</span> <span class="free bound entity">x</span><span class="main">)</span> <span class="main">=</span> <span class="main">-</span> Re</span> <span class="free bound entity">x</span><span>"</span>
  <span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span>Im1</span> <span class="main">(</span><span class="main">-</span> <span class="free bound entity">x</span><span class="main">)</span> <span class="main">=</span> <span class="main">-</span> Im1</span> <span class="free bound entity">x</span><span>"</span>
  <span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span>Im2</span> <span class="main">(</span><span class="main">-</span> <span class="free bound entity">x</span><span class="main">)</span> <span class="main">=</span> <span class="main">-</span> Im2</span> <span class="free bound entity">x</span><span>"</span>
  <span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span>Im3</span> <span class="main">(</span><span class="main">-</span> <span class="free bound entity">x</span><span class="main">)</span> <span class="main">=</span> <span class="main">-</span> Im3</span> <span class="free bound entity">x</span><span>"</span>

<span class="keyword1 command">primcorec</span> <span class="entity class_parameter">minus_quat</span>
  <span class="keyword2 keyword">where</span>
    <span class="quoted"><span class="quoted"><span>"</span>Re</span> <span class="main">(</span><span class="free bound entity">x</span> <span class="main">-</span> <span class="free bound entity">y</span><span class="main">)</span> <span class="main">=</span> Re</span> <span class="free bound entity">x</span> <span class="main">-</span> Re <span class="free bound entity">y</span><span>"</span>
  <span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span>Im1</span> <span class="main">(</span><span class="free bound entity">x</span> <span class="main">-</span> <span class="free bound entity">y</span><span class="main">)</span> <span class="main">=</span> Im1</span> <span class="free bound entity">x</span> <span class="main">-</span> Im1 <span class="free bound entity">y</span><span>"</span>
  <span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span>Im2</span> <span class="main">(</span><span class="free bound entity">x</span> <span class="main">-</span> <span class="free bound entity">y</span><span class="main">)</span> <span class="main">=</span> Im2</span> <span class="free bound entity">x</span> <span class="main">-</span> Im2 <span class="free bound entity">y</span><span>"</span>
  <span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span>Im3</span> <span class="main">(</span><span class="free bound entity">x</span> <span class="main">-</span> <span class="free bound entity">y</span><span class="main">)</span> <span class="main">=</span> Im3</span> <span class="free bound entity">x</span> <span class="main">-</span> Im3 <span class="free bound entity">y</span><span>"</span>

<span class="keyword1 command">instance</span>
  <span class="keyword1 command">by</span> <span class="operator">standard</span> <span class="main">(</span><span class="operator">simp_all</span> <span class="quasi_keyword">add</span><span class="main main">:</span> quat_eq_iff<span class="main">)</span>

<span class="keyword2 keyword">end</span>
</pre>

Now we can already reason about summations

<pre class="source">
<span class="keyword1 command">lemma</span> Re_sum <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>Re</span><span class="main">(</span>sum <span class="free">f</span> <span class="free">S</span><span class="main">)</span> <span class="main">=</span> sum <span class="main">(</span><span class="main">λ</span><span class="bound">x</span><span class="main">.</span>  Re</span><span class="main">(</span><span class="free">f</span> <span class="bound">x</span><span class="main">)</span><span class="main">)</span> <span class="free">S</span><span>"</span> <span class="keyword2 keyword">for</span> <span class="free">f</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span><span class="tfree">'a</span> <span class="main">⇒</span> quat</span><span>"</span></span>
  <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">induct</span> <span class="quoted free">S</span> <span class="quasi_keyword">rule</span><span class="main main">:</span> infinite_finite_induct<span class="main">)</span> <span class="operator">auto</span>
</pre>


### A Vector Space

<pre class="source">
<span class="keyword1 command">instantiation</span> quat <span class="main">::</span> <span class="quoted">real_vector</span>

<span class="keyword2 keyword">begin</span>

<span class="keyword1 command">primcorec</span> <span class="entity class_parameter">scaleR_quat</span>
  <span class="keyword2 keyword">where</span>
    <span class="quoted"><span class="quoted"><span>"</span>Re</span> <span class="main">(</span>scaleR <span class="free bound entity">r</span> <span class="free bound entity">x</span><span class="main">)</span> <span class="main">=</span> <span class="free bound entity">r</span> <span class="main">*</span> Re</span> <span class="free bound entity">x</span><span>"</span>
  <span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span>Im1</span> <span class="main">(</span>scaleR <span class="free bound entity">r</span> <span class="free bound entity">x</span><span class="main">)</span> <span class="main">=</span> <span class="free bound entity">r</span> <span class="main">*</span> Im1</span> <span class="free bound entity">x</span><span>"</span>
  <span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span>Im2</span> <span class="main">(</span>scaleR <span class="free bound entity">r</span> <span class="free bound entity">x</span><span class="main">)</span> <span class="main">=</span> <span class="free bound entity">r</span> <span class="main">*</span> Im2</span> <span class="free bound entity">x</span><span>"</span>
  <span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span>Im3</span> <span class="main">(</span>scaleR <span class="free bound entity">r</span> <span class="free bound entity">x</span><span class="main">)</span> <span class="main">=</span> <span class="free bound entity">r</span> <span class="main">*</span> Im3</span> <span class="free bound entity">x</span><span>"</span>

<span class="keyword1 command">instance</span>
  <span class="keyword1 command">by</span> <span class="operator">standard</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> quat_eq_iff distrib_left distrib_right  scaleR_add_right<span class="main">)</span>

<span class="keyword2 keyword">end</span>
</pre>

### Real algebra with 1

[[Note: not a field!]]

<pre class="source">
<span class="keyword1 command">instantiation</span> quat <span class="main">::</span> <span class="quoted">real_algebra_1</span>

<span class="keyword2 keyword">begin</span>

<span class="keyword1 command">primcorec</span> <span class="entity class_parameter">one_quat</span>
  <span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span>Re</span> <span class="main">1</span> <span class="main">=</span> <span class="main">1</span><span>"</span></span> <span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span>Im1</span> <span class="main">1</span> <span class="main">=</span> <span class="main">0</span><span>"</span></span> <span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span>Im2</span> <span class="main">1</span> <span class="main">=</span> <span class="main">0</span><span>"</span></span> <span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span>Im3</span> <span class="main">1</span> <span class="main">=</span> <span class="main">0</span><span>"</span></span>

<span class="keyword1 command">primcorec</span> <span class="entity class_parameter">times_quat</span>
  <span class="keyword2 keyword">where</span>
    <span class="quoted"><span class="quoted"><span>"</span>Re</span> <span class="main">(</span><span class="free bound entity">x</span> <span class="main">*</span> <span class="free bound entity">y</span><span class="main">)</span> <span class="main">=</span> Re</span> <span class="free bound entity">x</span> <span class="main">*</span> Re <span class="free bound entity">y</span> <span class="main">-</span> Im1 <span class="free bound entity">x</span> <span class="main">*</span> Im1 <span class="free bound entity">y</span> <span class="main">-</span> Im2 <span class="free bound entity">x</span> <span class="main">*</span> Im2 <span class="free bound entity">y</span> <span class="main">-</span> Im3 <span class="free bound entity">x</span> <span class="main">*</span> Im3 <span class="free bound entity">y</span><span>"</span>
  <span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span>Im1</span> <span class="main">(</span><span class="free bound entity">x</span> <span class="main">*</span> <span class="free bound entity">y</span><span class="main">)</span> <span class="main">=</span> Re</span> <span class="free bound entity">x</span> <span class="main">*</span> Im1 <span class="free bound entity">y</span> <span class="main">+</span> Im1 <span class="free bound entity">x</span> <span class="main">*</span>  Re <span class="free bound entity">y</span> <span class="main">+</span> Im2 <span class="free bound entity">x</span> <span class="main">*</span> Im3 <span class="free bound entity">y</span> <span class="main">-</span> Im3 <span class="free bound entity">x</span> <span class="main">*</span> Im2 <span class="free bound entity">y</span><span>"</span>
  <span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span>Im2</span> <span class="main">(</span><span class="free bound entity">x</span> <span class="main">*</span> <span class="free bound entity">y</span><span class="main">)</span> <span class="main">=</span> Re</span> <span class="free bound entity">x</span> <span class="main">*</span> Im2 <span class="free bound entity">y</span> <span class="main">-</span> Im1 <span class="free bound entity">x</span> <span class="main">*</span> Im3 <span class="free bound entity">y</span> <span class="main">+</span> Im2 <span class="free bound entity">x</span> <span class="main">*</span>  Re <span class="free bound entity">y</span> <span class="main">+</span> Im3 <span class="free bound entity">x</span> <span class="main">*</span> Im1 <span class="free bound entity">y</span><span>"</span>
  <span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span>Im3</span> <span class="main">(</span><span class="free bound entity">x</span> <span class="main">*</span> <span class="free bound entity">y</span><span class="main">)</span> <span class="main">=</span> Re</span> <span class="free bound entity">x</span> <span class="main">*</span> Im3 <span class="free bound entity">y</span> <span class="main">+</span> Im1 <span class="free bound entity">x</span> <span class="main">*</span> Im2 <span class="free bound entity">y</span> <span class="main">-</span> Im2 <span class="free bound entity">x</span> <span class="main">*</span> Im1 <span class="free bound entity">y</span> <span class="main">+</span> Im3 <span class="free bound entity">x</span> <span class="main">*</span>  Re <span class="free bound entity">y</span><span>"</span>

<span class="keyword1 command">instance</span>
  <span class="keyword1 command">by</span> <span class="operator">standard</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> quat_eq_iff distrib_left distrib_right Rings.right_diff_distrib Rings.left_diff_distrib<span class="main">)</span>

<span class="keyword2 keyword">end</span>
</pre>

Suddenly by magic we've gained the ability to use *numerals* for quaterions, e.g.

<pre class="source">
<span class="keyword1 command">lemma</span> "(<span class="free">x</span>::<span class="quoted">quat</span>) = <span class="main">3000</span>"
</pre>


### Multiplication and Division: A Real Division Algebra

Note: not a field! 

<pre class="source">
<span class="keyword1 command">instantiation</span> quat <span class="main">::</span> <span class="quoted">real_div_algebra</span>
<span class="keyword2 keyword">begin</span>

<span class="keyword1 command">primcorec</span> <span class="entity class_parameter">inverse_quat</span>
  <span class="keyword2 keyword">where</span>
    <span class="quoted"><span class="quoted"><span>"</span>Re</span> <span class="main">(</span>inverse <span class="free bound entity">x</span><span class="main">)</span> <span class="main">=</span> Re</span> <span class="free bound entity">x</span> <span class="main">/</span> <span class="main">(</span><span class="main">(</span>Re <span class="free bound entity">x</span><span class="main">)</span><span class="main"><span class="hidden">⇧</span><sup>2</sup></span> <span class="main">+</span> <span class="main">(</span>Im1 <span class="free bound entity">x</span><span class="main">)</span><span class="main"><span class="hidden">⇧</span><sup>2</sup></span> <span class="main">+</span> <span class="main">(</span>Im2 <span class="free bound entity">x</span><span class="main">)</span><span class="main"><span class="hidden">⇧</span><sup>2</sup></span> <span class="main">+</span> <span class="main">(</span>Im3 <span class="free bound entity">x</span><span class="main">)</span><span class="main"><span class="hidden">⇧</span><sup>2</sup></span><span class="main">)</span><span>"</span>
  <span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span>Im1</span> <span class="main">(</span>inverse <span class="free bound entity">x</span><span class="main">)</span> <span class="main">=</span> <span class="main">-</span> <span class="main">(</span>Im1</span> <span class="free bound entity">x</span><span class="main">)</span> <span class="main">/</span> <span class="main">(</span><span class="main">(</span>Re <span class="free bound entity">x</span><span class="main">)</span><span class="main"><span class="hidden">⇧</span><sup>2</sup></span> <span class="main">+</span> <span class="main">(</span>Im1 <span class="free bound entity">x</span><span class="main">)</span><span class="main"><span class="hidden">⇧</span><sup>2</sup></span> <span class="main">+</span> <span class="main">(</span>Im2 <span class="free bound entity">x</span><span class="main">)</span><span class="main"><span class="hidden">⇧</span><sup>2</sup></span> <span class="main">+</span> <span class="main">(</span>Im3 <span class="free bound entity">x</span><span class="main">)</span><span class="main"><span class="hidden">⇧</span><sup>2</sup></span><span class="main">)</span><span>"</span>
  <span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span>Im2</span> <span class="main">(</span>inverse <span class="free bound entity">x</span><span class="main">)</span> <span class="main">=</span> <span class="main">-</span> <span class="main">(</span>Im2</span> <span class="free bound entity">x</span><span class="main">)</span> <span class="main">/</span> <span class="main">(</span><span class="main">(</span>Re <span class="free bound entity">x</span><span class="main">)</span><span class="main"><span class="hidden">⇧</span><sup>2</sup></span> <span class="main">+</span> <span class="main">(</span>Im1 <span class="free bound entity">x</span><span class="main">)</span><span class="main"><span class="hidden">⇧</span><sup>2</sup></span> <span class="main">+</span> <span class="main">(</span>Im2 <span class="free bound entity">x</span><span class="main">)</span><span class="main"><span class="hidden">⇧</span><sup>2</sup></span> <span class="main">+</span> <span class="main">(</span>Im3 <span class="free bound entity">x</span><span class="main">)</span><span class="main"><span class="hidden">⇧</span><sup>2</sup></span><span class="main">)</span><span>"</span>
  <span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span>Im3</span> <span class="main">(</span>inverse <span class="free bound entity">x</span><span class="main">)</span> <span class="main">=</span> <span class="main">-</span> <span class="main">(</span>Im3</span> <span class="free bound entity">x</span><span class="main">)</span> <span class="main">/</span> <span class="main">(</span><span class="main">(</span>Re <span class="free bound entity">x</span><span class="main">)</span><span class="main"><span class="hidden">⇧</span><sup>2</sup></span> <span class="main">+</span> <span class="main">(</span>Im1 <span class="free bound entity">x</span><span class="main">)</span><span class="main"><span class="hidden">⇧</span><sup>2</sup></span> <span class="main">+</span> <span class="main">(</span>Im2 <span class="free bound entity">x</span><span class="main">)</span><span class="main"><span class="hidden">⇧</span><sup>2</sup></span> <span class="main">+</span> <span class="main">(</span>Im3 <span class="free bound entity">x</span><span class="main">)</span><span class="main"><span class="hidden">⇧</span><sup>2</sup></span><span class="main">)</span><span>"</span>

<span class="keyword1 command">definition</span> <span class="quoted quoted"><span>"</span><span class="free bound entity">x</span> <span class="keyword1">div</span> <span class="free bound entity">y</span> <span class="main">=</span> <span class="free bound entity">x</span> <span class="main">*</span> inverse <span class="free bound entity">y</span><span>"</span></span> <span class="keyword2 keyword">for</span> <span class="free">x</span> <span class="free">y</span> <span class="main">::</span> <span class="quoted">quat</span>

<span class="keyword1 command">instance</span>
<span class="keyword1 command">proof</span>
  <span class="keyword3 command">show</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">⋀</span><span class="bound">x</span><span class="main">::</span>quat</span><span class="main">.</span> <span class="bound">x</span> <span class="main">≠</span> <span class="main">0</span> <span class="main">⟹</span> inverse <span class="bound">x</span> <span class="main">*</span> <span class="bound">x</span> <span class="main">=</span> <span class="main">1</span><span>"</span></span>
    <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> quat_eq_iff add_nonneg_eq_0_iff
        power2_eq_square add_divide_distrib <span class="main main">[</span><span class="operator">symmetric</span><span class="main main">]</span> diff_divide_distrib <span class="main main">[</span><span class="operator">symmetric</span><span class="main main">]</span><span class="main">)</span>
  <span class="keyword3 command">show</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">⋀</span><span class="bound">x</span><span class="main">::</span>quat</span><span class="main">.</span> <span class="bound">x</span> <span class="main">≠</span> <span class="main">0</span> <span class="main">⟹</span> <span class="bound">x</span> <span class="main">*</span> inverse <span class="bound">x</span> <span class="main">=</span> <span class="main">1</span><span>"</span></span>
    <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> quat_eq_iff add_nonneg_eq_0_iff power2_eq_square add_divide_distrib <span class="main main">[</span><span class="operator">symmetric</span><span class="main main">]</span><span class="main">)</span>
  <span class="keyword3 command">show</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">⋀</span><span class="bound">x</span> <span class="bound">y</span><span class="main">::</span>quat</span><span class="main">.</span> <span class="bound">x</span> <span class="keyword1">div</span> <span class="bound">y</span> <span class="main">=</span> <span class="bound">x</span> <span class="main">*</span> inverse <span class="bound">y</span><span>"</span></span>
    <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> divide_quat_def<span class="main">)</span>
  <span class="keyword3 command">show</span> <span class="quoted"><span class="quoted"><span>"</span>inverse <span class="main">0</span> <span class="main">=</span> <span class="main">(</span><span class="main">0</span><span class="main">::</span>quat</span><span class="main">)</span><span>"</span></span>
    <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> quat_eq_iff<span class="main">)</span>
<span class="keyword1 command">qed</span>

<span class="keyword2 keyword">end</span>
</pre>

So now we have division for quaterions, e.g.

<pre class="source">
<span class="keyword1 command">lemma</span> "(<span class="free">x</span>::<span class="quoted">quat</span>)*<span class="main">1000</span>/<span class="main">1001</span>  = <span class="free">x</span>"
</pre>

And Isabelle can even detect that it's false automatically

Large numerals work

<pre>
Auto Quickcheck found a counterexample:
  x = Quat (real_of_rat (Fract (- 1) 1))
       (real_of_rat (Fract (- 1) 1))
       (real_of_rat (Fract (- 1) 1))
       (real_of_rat (Fract (- 1) 1))
Evaluated terms:
  x * 1000 / 1001 =
    Quat (- (1000 / 1001)) (- (1000 / 1001))
     (- (1000 / 1001)) (- (1000 / 1001))
</pre>



### Real normed division algebra

<pre class="source">
<span class="keyword1 command">instantiation</span> quat <span class="main">::</span> <span class="quoted">real_normed_div_algebra</span>
<span class="keyword2 keyword">begin</span>

<span class="keyword1 command">definition</span> <span class="quoted"><span class="quoted"><span>"</span>norm <span class="free bound entity">z</span> <span class="main">=</span> sqrt <span class="main">(</span><span class="main">(</span>Re</span> <span class="free bound entity">z</span><span class="main">)</span><span class="main"><span class="hidden">⇧</span><sup>2</sup></span> <span class="main">+</span> <span class="main">(</span>Im1</span> <span class="free bound entity">z</span><span class="main">)</span><span class="main"><span class="hidden">⇧</span><sup>2</sup></span> <span class="main">+</span> <span class="main">(</span>Im2 <span class="free bound entity">z</span><span class="main">)</span><span class="main"><span class="hidden">⇧</span><sup>2</sup></span> <span class="main">+</span> <span class="main">(</span>Im3 <span class="free bound entity">z</span><span class="main">)</span><span class="main"><span class="hidden">⇧</span><sup>2</sup></span><span class="main">)</span><span>"</span>

<span class="keyword1 command">definition</span> <span class="quoted quoted"><span>"</span>sgn <span class="free bound entity">x</span> <span class="main">=</span> <span class="free bound entity">x</span> <span class="keyword1">/<span class="hidden">⇩</span><sub>R</sub></span> norm <span class="free bound entity">x</span><span>"</span></span> <span class="keyword2 keyword">for</span> <span class="free">x</span> <span class="main">::</span> <span class="quoted">quat</span>

<span class="keyword1 command">definition</span> <span class="quoted quoted"><span>"</span>dist <span class="free bound entity">x</span> <span class="free bound entity">y</span> <span class="main">=</span> norm <span class="main">(</span><span class="free bound entity">x</span> <span class="main">-</span> <span class="free bound entity">y</span><span class="main">)</span><span>"</span></span> <span class="keyword2 keyword">for</span> <span class="free">x</span> <span class="free">y</span> <span class="main">::</span> <span class="quoted">quat</span>

<span class="keyword1 command">definition</span> <span class="main">[</span><span class="operator">code</span> <span class="quasi_keyword quasi_keyword quasi_keyword">del</span><span class="main">]</span><span class="main">:</span>
  <span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span>uniformity <span class="main">::</span> <span class="main">(</span>quat</span> <span class="main">×</span> quat</span><span class="main">)</span> filter<span class="main">)</span> <span class="main">=</span> <span class="main">(</span><span class="keyword1">INF</span> <span class="bound">e</span><span class="main">∈</span><span class="main">{</span><span class="main">0</span> <span class="main">&lt;..}</span><span class="main">.</span> principal <span class="main">{</span><span class="main">(</span><span class="bound">x</span><span class="main">,</span> <span class="bound">y</span><span class="main">)</span><span class="main">.</span> dist <span class="bound">x</span> <span class="bound">y</span> <span class="main">&lt;</span> <span class="bound">e</span><span class="main">}</span><span class="main">)</span><span>"</span>

<span class="keyword1 command">definition</span> <span class="main">[</span><span class="operator">code</span> <span class="quasi_keyword quasi_keyword quasi_keyword">del</span><span class="main">]</span><span class="main">:</span>
  <span class="quoted"><span class="quoted"><span>"</span>open <span class="main">(</span><span class="free bound entity">U</span> <span class="main">::</span> quat</span> set<span class="main">)</span> <span class="main">⟷</span> <span class="main">(</span><span class="main">∀</span><span class="bound">x</span><span class="main">∈</span><span class="free bound entity">U</span><span class="main">.</span> eventually <span class="main">(</span><span class="main">λ</span><span class="main">(</span><span class="bound">x'</span><span class="main">,</span> <span class="bound">y</span><span class="main">)</span><span class="main">.</span> <span class="bound">x'</span> <span class="main">=</span> <span class="bound">x</span> <span class="main">⟶</span> <span class="bound">y</span> <span class="main">∈</span> <span class="free bound entity">U</span><span class="main">)</span> uniformity<span class="main">)</span><span>"</span></span>

<span class="keyword1 command">lemma</span> norm_eq_L2<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>norm <span class="free">z</span> <span class="main">=</span> L2_set</span> <span class="main">(</span>quat_proj</span> <span class="free">z</span><span class="main">)</span> <span class="main">{..</span><span class="numeral">3</span><span class="main">}</span><span>"</span>
  <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> norm_quat_def L2_set_def numeral_3_eq_3<span class="main">)</span>

<span class="keyword1 command">instance</span>
<span class="keyword1 command">proof</span>
  <span class="keyword3 command">fix</span> <span class="skolem">r</span> <span class="main">::</span> <span class="quoted">real</span> <span class="keyword2 keyword">and</span> <span class="skolem">x</span> <span class="skolem">y</span> <span class="main">::</span> <span class="quoted">quat</span> <span class="keyword2 keyword">and</span> <span class="skolem">S</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>quat</span> set<span>"</span></span>
  <span class="keyword3 command">show</span> <span class="quoted quoted"><span>"</span><span class="main">(</span>norm <span class="skolem">x</span> <span class="main">=</span> <span class="main">0</span><span class="main">)</span> <span class="main">⟷</span> <span class="main">(</span><span class="skolem">x</span> <span class="main">=</span> <span class="main">0</span><span class="main">)</span><span>"</span></span>
    <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> norm_quat_def quat_eq_iff add_nonneg_eq_0_iff<span class="main">)</span>
  <span class="keyword1 command">have</span> eq<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>L2_set</span> <span class="main">(</span>quat_proj</span> <span class="main">(</span><span class="skolem">x</span> <span class="main">+</span> <span class="skolem">y</span><span class="main">)</span><span class="main">)</span> <span class="main">{..</span><span class="numeral">3</span><span class="main">}</span> <span class="main">=</span> L2_set <span class="main">(</span><span class="main">λ</span><span class="bound">i</span><span class="main">.</span> quat_proj <span class="skolem">x</span> <span class="bound">i</span> <span class="main">+</span> quat_proj <span class="skolem">y</span> <span class="bound">i</span><span class="main">)</span> <span class="main">{..</span><span class="numeral">3</span><span class="main">}</span><span>"</span>
    <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">rule</span> L2_set_cong<span class="main">)</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> quat_proj_add<span class="main">)</span>
  <span class="keyword3 command">show</span> <span class="quoted quoted"><span>"</span>norm <span class="main">(</span><span class="skolem">x</span> <span class="main">+</span> <span class="skolem">y</span><span class="main">)</span> <span class="main">≤</span> norm <span class="skolem">x</span> <span class="main">+</span> norm <span class="skolem">y</span><span>"</span></span>
    <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> norm_eq_L2 eq L2_set_triangle_ineq<span class="main">)</span>
  <span class="keyword3 command">show</span> <span class="quoted quoted"><span>"</span>norm <span class="main">(</span>scaleR <span class="skolem">r</span> <span class="skolem">x</span><span class="main">)</span> <span class="main">=</span> <span class="main">¦</span><span class="skolem">r</span><span class="main">¦</span> <span class="main">*</span> norm <span class="skolem">x</span><span>"</span></span>
    <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> norm_quat_def quat_eq_iff power_mult_distrib distrib_left <span class="main main">[</span><span class="operator">symmetric</span><span class="main main">]</span> real_sqrt_mult<span class="main">)</span>
  <span class="keyword3 command">show</span> <span class="quoted quoted"><span>"</span>norm <span class="main">(</span><span class="skolem">x</span> <span class="main">*</span> <span class="skolem">y</span><span class="main">)</span> <span class="main">=</span> norm <span class="skolem">x</span> <span class="main">*</span> norm <span class="skolem">y</span><span>"</span></span>
    <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> norm_quat_def quat_eq_iff real_sqrt_mult <span class="main main">[</span><span class="operator">symmetric</span><span class="main main">]</span>
        power2_eq_square <span class="dynamic dynamic">algebra_simps</span><span class="main">)</span>
<span class="keyword1 command">qed</span> <span class="main">(</span><span class="operator">rule</span> sgn_quat_def dist_quat_def open_quat_def uniformity_quat_def<span class="main">)</span><span class="main keyword3">+</span>

<span class="keyword2 keyword">end</span>
</pre>



### Real inner product space

<pre class="source">
<span class="keyword1 command">instantiation</span> quat <span class="main">::</span> <span class="quoted">real_inner</span>
<span class="keyword2 keyword">begin</span>

<span class="keyword1 command">definition</span> inner_quat_def<span class="main">:</span>
  <span class="quoted"><span class="quoted"><span>"</span>inner</span> <span class="free bound entity">x</span> <span class="free bound entity">y</span> <span class="main">=</span> Re</span> <span class="free bound entity">x</span> <span class="main">*</span> Re <span class="free bound entity">y</span> <span class="main">+</span> Im1 <span class="free bound entity">x</span> <span class="main">*</span> Im1 <span class="free bound entity">y</span> <span class="main">+</span> Im2 <span class="free bound entity">x</span> <span class="main">*</span> Im2 <span class="free bound entity">y</span> <span class="main">+</span> Im3 <span class="free bound entity">x</span> <span class="main">*</span> Im3 <span class="free bound entity">y</span><span>"</span>

<span class="keyword1 command">instance</span>
<span class="keyword1 command">proof</span>
  <span class="keyword3 command">fix</span> <span class="skolem">x</span> <span class="skolem">y</span> <span class="skolem">z</span> <span class="main">::</span> <span class="quoted">quat</span> <span class="keyword2 keyword">and</span> <span class="skolem">r</span> <span class="main">::</span> <span class="quoted">real</span>
  <span class="keyword3 command">show</span> <span class="quoted"><span class="quoted"><span>"</span>inner</span> <span class="skolem">x</span> <span class="skolem">y</span> <span class="main">=</span> inner</span> <span class="skolem">y</span> <span class="skolem">x</span><span>"</span>
    <span class="keyword1 command">unfolding</span> inner_quat_def <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> mult.commute<span class="main">)</span>
  <span class="keyword3 command">show</span> <span class="quoted"><span class="quoted"><span>"</span>inner</span> <span class="main">(</span><span class="skolem">x</span> <span class="main">+</span> <span class="skolem">y</span><span class="main">)</span> <span class="skolem">z</span> <span class="main">=</span> inner</span> <span class="skolem">x</span> <span class="skolem">z</span> <span class="main">+</span> inner <span class="skolem">y</span> <span class="skolem">z</span><span>"</span>
    <span class="keyword1 command">unfolding</span> inner_quat_def <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> distrib_right<span class="main">)</span>
  <span class="keyword3 command">show</span> <span class="quoted"><span class="quoted"><span>"</span>inner</span> <span class="main">(</span>scaleR <span class="skolem">r</span> <span class="skolem">x</span><span class="main">)</span> <span class="skolem">y</span> <span class="main">=</span> <span class="skolem">r</span> <span class="main">*</span> inner</span> <span class="skolem">x</span> <span class="skolem">y</span><span>"</span>
    <span class="keyword1 command">unfolding</span> inner_quat_def <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> distrib_left<span class="main">)</span>
  <span class="keyword3 command">show</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">0</span> <span class="main">≤</span> inner</span> <span class="skolem">x</span> <span class="skolem">x</span><span>"</span></span>
    <span class="keyword1 command">unfolding</span> inner_quat_def <span class="keyword1 command">by</span> <span class="operator">simp</span>
  <span class="keyword3 command">show</span> <span class="quoted"><span class="quoted"><span>"</span>inner</span> <span class="skolem">x</span> <span class="skolem">x</span> <span class="main">=</span> <span class="main">0</span> <span class="main">⟷</span> <span class="skolem">x</span> <span class="main">=</span> <span class="main">0</span><span>"</span></span>
    <span class="keyword1 command">unfolding</span> inner_quat_def <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> add_nonneg_eq_0_iff quat_eq_iff<span class="main">)</span>
  <span class="keyword3 command">show</span> <span class="quoted"><span class="quoted"><span>"</span>norm <span class="skolem">x</span> <span class="main">=</span> sqrt <span class="main">(</span>inner</span> <span class="skolem">x</span> <span class="skolem">x</span><span class="main">)</span><span>"</span></span>
    <span class="keyword1 command">unfolding</span> inner_quat_def norm_quat_def
    <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> power2_eq_square<span class="main">)</span>
<span class="keyword1 command">qed</span>

<span class="keyword2 keyword">end</span>
</pre>

These are topological spaces, so we have limits and continuity for free


Almost nothing has been skipped until now


<pre class="source">
</pre>


<pre class="source">
</pre>

