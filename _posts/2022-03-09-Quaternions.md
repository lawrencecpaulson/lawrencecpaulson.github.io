---
layout: post
title:  "The quaternions—and type classes"
usemathjax: true
tags: examples, Isabelle, quaternions
---

The quaternion number system is an extension of the complex numbers to 4 dimensions, introduced by [Hamilton](https://mathshistory.st-andrews.ac.uk/Biographies/Hamilton/) in 1843. I translated the [HOL Light formalisation of quaternions](https://doi.org/10.1007/978-3-319-66107-0_15) into Isabelle/HOL some time ago. One notable feature of the formalisation (taken from the Isabelle/HOL formalisation of the complex numbers) is that its definition can be regarded as [coinductive](https://doi.org/10.1007/978-3-319-08970-6_7). Moreover, continuing the [previous post]({% post_url 2022-03-02-Type_classes %}) about axiomatic type classes, we have a dramatic demonstration of how quickly a new class of numbers can be made native (so to speak).

### Defining the type

Quaternions have the form $a + b \mathbf{i} + c \mathbf{j} + d \mathbf{k}$
where $a$, $b$, $c$ and $d$ are real numbers and $\mathbf{i}$, $\mathbf{j}$, $\mathbf{k}$ are the primitive quaternions, satisfying a number of laws such as 

$$ \mathbf{i}^2 = \mathbf{j}^2 = \mathbf{k}^2 = \mathbf{i}\mathbf{j}\mathbf{k} = -1. $$

It would be natural to represent quaternions by 4-tuples, but it is even simpler to represent them (like the complex numbers) as a *codatatype*. A codatatype is dual to a datatype; just as the latter is specified by enumerating its constructor functions, the former is specified by enumerating its selector functions (sometimes called destructors or projections). Category theorists should note that codatatypes are terminal coalgebras. Here we get something close to a 4-tuple.

<pre class="source">
<span class="keyword1 command">codatatype</span> quat <span class="main">=</span> Quat <span class="main">(</span><span class="free entity">Re</span><span class="main">:</span> <span class="quoted">real</span><span class="main">)</span> <span class="main">(</span><span class="free entity">Im1</span><span class="main">:</span> <span class="quoted">real</span><span class="main">)</span> <span class="main">(</span><span class="free entity">Im2</span><span class="main">:</span> <span class="quoted">real</span><span class="main">)</span> <span class="main">(</span><span class="free entity">Im3</span><span class="main">:</span> <span class="quoted">real</span><span class="main">)</span>
</pre>

The selectors `Im1`, `Im2`, `Im3` will return the coefficients of to $\mathbf{i}$, $\mathbf{j}$, $\mathbf{k}$, respectively, while `Re` will return the real part of a quaternion.
It is trivial to prove that two quaternions are equal if and only if their four components all coincide.

<pre class="source">
<span class="keyword1 command">lemma</span> quat_eq_iff<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">=</span> <span class="free">y</span> <span class="main">⟷</span> Re</span> <span class="free">x</span> <span class="main">=</span> Re</span> <span class="free">y</span> <span class="main">∧</span> Im1 <span class="free">x</span> <span class="main">=</span> Im1 <span class="free">y</span> <span class="main">∧</span> Im2 <span class="free">x</span> <span class="main">=</span> Im2 <span class="free">y</span> <span class="main">∧</span> Im3 <span class="free">x</span> <span class="main">=</span> Im3 <span class="free">y</span><span>"</span>
  <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">intro</span><span class="main main">:</span> quat.expand<span class="main">)</span>
</pre>


### Defining the primitive operators

It is now possible to define the primitive quaternions, $\mathbf{i}$, $\mathbf{j}$ and $\mathbf{k}$.
With corecursion, new entities are defined in terms of the behaviour of the selectors. For example, the quaternion $\mathbf{i}$ yields zero for all selectors except `Im1`. 
The quaternions $\mathbf{j}$ and $\mathbf{k}$ are defined analogously.

<pre class="source">
<span class="keyword1 command">primcorec</span> <span class="entity">quat_ii</span> <span class="main">::</span> <span class="quoted">quat</span>  <span class="main">(</span><span class="quoted"><span>"</span><span class="keyword1">𝗂</span><span>"</span></span><span class="main">)</span>
  <span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span>Re</span> <span class="keyword1 free">𝗂</span> <span class="main">=</span> <span class="main">0</span><span>"</span></span> <span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span>Im1</span> <span class="keyword1 free">𝗂</span> <span class="main">=</span> <span class="main">1</span><span>"</span></span> <span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span>Im2</span> <span class="keyword1 free">𝗂</span> <span class="main">=</span> <span class="main">0</span><span>"</span></span> <span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span>Im3</span> <span class="keyword1 free">𝗂</span> <span class="main">=</span> <span class="main">0</span><span>"</span></span>

<span class="keyword1 command">primcorec</span> <span class="entity">quat_jj</span> <span class="main">::</span> <span class="quoted">quat</span>  <span class="main">(</span><span class="quoted"><span>"</span><span class="keyword1">𝗃</span><span>"</span></span><span class="main">)</span>
  <span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span>Re</span> <span class="keyword1 free">𝗃</span> <span class="main">=</span> <span class="main">0</span><span>"</span></span> <span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span>Im1</span> <span class="keyword1 free">𝗃</span> <span class="main">=</span> <span class="main">0</span><span>"</span></span> <span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span>Im2</span> <span class="keyword1 free">𝗃</span> <span class="main">=</span> <span class="main">1</span><span>"</span></span> <span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span>Im3</span> <span class="keyword1 free">𝗃</span> <span class="main">=</span> <span class="main">0</span><span>"</span></span>

<span class="keyword1 command">primcorec</span> <span class="entity">quat_kk</span> <span class="main">::</span> <span class="quoted">quat</span>  <span class="main">(</span><span class="quoted"><span>"</span><span class="keyword1">𝗄</span><span>"</span></span><span class="main">)</span>
  <span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span>Re</span> <span class="keyword1 free">𝗄</span> <span class="main">=</span> <span class="main">0</span><span>"</span></span> <span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span>Im1</span> <span class="keyword1 free">𝗄</span> <span class="main">=</span> <span class="main">0</span><span>"</span></span> <span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span>Im2</span> <span class="keyword1 free">𝗄</span> <span class="main">=</span> <span class="main">0</span><span>"</span></span> <span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span>Im3</span> <span class="keyword1 free">𝗄</span> <span class="main">=</span> <span class="main">1</span><span>"</span></span>
</pre>

### Addition and subtraction: an abelian group

The development now proceeds by showing that quaternions are an instance of one type class after another. The first is `ab_group_add`, the class of abelian groups with the signature $(0, {+}, {-})$. For this instance declaration to be accepted, definitions must be provided for zero, addition, unary minus and subtraction, and they must be shown to satisfy the usual group axioms. The proofs of the latter turn out to take a single line. The definitions again use corecursion, and as we can see below, these operations are all defined componentwise.

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

This <span class="keyword1 command">instantiation</span> declaration not only makes the entire library of facts about `ab_group_add` available to quaternions, but also any associated operators. This particular lemma (which actually appears later in the theory) states that `Re` distributes over finite summations.

<pre class="source">
<span class="keyword1 command">lemma</span> Re_sum <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>Re</span><span class="main">(</span>sum <span class="free">f</span> <span class="free">S</span><span class="main">)</span> <span class="main">=</span> sum <span class="main">(</span><span class="main">λ</span><span class="bound">x</span><span class="main">.</span>  Re</span><span class="main">(</span><span class="free">f</span> <span class="bound">x</span><span class="main">)</span><span class="main">)</span> <span class="free">S</span><span>"</span> <span class="keyword2 keyword">for</span> <span class="free">f</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span><span class="tfree">'a</span> <span class="main">⇒</span> quat</span><span>"</span></span>
  <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">induct</span> <span class="quoted free">S</span> <span class="quasi_keyword">rule</span><span class="main main">:</span> infinite_finite_induct<span class="main">)</span> <span class="operator">auto</span>
</pre>


### Scalar multiplication: a vector space

The development continues, following the HOL Light original while continually looking for opportunities to instantiate an appropriate type class. Next is to show that quaternions are a vector space, so we instantiate `real_vector`. The (overloaded) scalar multiplication operator is called `scaleR` and its corecursive definition is self-explanatory.
The required properties (which amount to linearity) have a one line proof.

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
  <span class="keyword1 command">by</span> <span class="operator">standard</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> quat_eq_iff distrib_left distrib_right scaleR_add_right<span class="main">)</span>

<span class="keyword2 keyword">end</span>
</pre>

### Multiplication: real algebra with unit

According to legend, Hamilton struggled for years to define a well-behaved multiplication operation for the three-dimensional space he was working on, suddenly realising that it could be done if he introduced a fourth component. As always, corecursion defines the operations (1 and $\times$) in terms of the four selector functions.
A real algebra with unit satisfies the axioms of a ring and the multiplication also commutes with scalar multiplication. However, quaternion multiplication is not commutative. I was pleased to find that all the necessary type classes for this development were already available in Isabelle/HOL.


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
  <span class="keyword1 command">by</span> <span class="operator">standard</span>
     <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> quat_eq_iff distrib_left distrib_right right_diff_distrib left_diff_distrib<span class="main">)</span>

<span class="keyword2 keyword">end</span>
</pre>

Suddenly by magic we've gained the ability to use *numerals* to denote quaterions.
Numerals can be hundreds of digits long, represented internally by a symbolic binary notation. Arithmetic on them is surprisingly efficient.
This type class instantiation has also given us the functions `of_nat`, `of_int`, `of_real`, injecting other numeric types (the natural numbers, integers, reals) into the quaternions.


### And now division: a real division algebra

The next instantiation, to the type class `real_div_algebra`—the quaternions do not form a field—requires us to define the multiplicative inverse and then (trivially) division. For the first time, justification of the type class axioms is not trivial, hence the four <span class="keyword3 command">show</span> commands below.


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

Here is a trivial example illustrating the use of both numerals and division for quaternions:

<pre class="source">
<span class="keyword1 command">lemma</span> "(<span class="free">x</span>::<span class="quoted">quat</span>)*<span class="main">1000</span>/<span class="main">1001</span> = <span class="free">x</span>"
</pre>

And here's another thing. If we type in the line above, Isabelle instantly and automatically detects that the claim is false, producing the following message:

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

It also works with much larger numbers. Counterexample detection is not always possible, but it works in [much more sophisticated situations](https://doi.org/10.1007/978-3-642-35308-6_10) than the one shown, and it is a tremendous time saver.
[Nitpick](http://dx.doi.org/10.1007/978-3-642-14052-5_11) is another counterexample finder, working on different principles from Quickcheck and also highly effective.

### Real normed division algebra

Now we define a norm on quaternions, instantiating the type class `real_normed_div_algebra`. The norm of $a + b \mathbf{i} + c \mathbf{j} + d \mathbf{k}$ is
simply $\sqrt{a^2+b^2+c^2+d^2}$. This type class requires definitions of associated operators such as `dist`, the metric space distance function.
The declaration explicitly proves some required properties of `norm`, such as the triangle inequality, while the properties of the derived operations are trivial by definition.

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

Having done this instantiation, Isabelle knows that quaternions are a topological space.
Quaternions now enjoy the full vocabulary of open and closed sets, limits and continuity, derivatives and infinite sums. Because HOL Light does not have type classes, its formalisation of quaternions includes whole files of library material, copied and pasted with the obvious type substitutions.


### Real inner product space

Our final instantiation is to `real_inner`, the type class of real-valued inner product spaces.
This step unlocks additional library material, for dot products.
Five necessary properties of the given definition of inner products, such as the commutative and distributive laws, are shown explicitly.

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


Up to this point I have hidden essentially nothing from the [full quaternion development](https://www.isa-afp.org/browser_info/current/AFP/Quaternions/Quaternions.html).
There's only one small technical lemma and some commands to prevent syntactic ambiguities between our <span class="keyword1">𝗂</span> and the version of <span class="keyword1">𝗂</span> belonging to the complex numbers. Starting from a few basic definitions, we issued six <span class="keyword1 command">instantiation</span> declarations to put at our disposal the material from three decades of library construction.

That's only the beginning. The quaternion development goes on to derive specific properties and applications of quaternions, all "borrowed" from the HOL Light original.
There's also a development of [Octonions](https://www.isa-afp.org/entries/Octonions.html) by 
Angeliki Koutsoukou-Argyraki.

The point of this example is simply to see how much we can accomplish with type classes alone.
What can't be done with type classes can possibly be done using *locales*, which are strictly more general, but that's a topic for another time.

