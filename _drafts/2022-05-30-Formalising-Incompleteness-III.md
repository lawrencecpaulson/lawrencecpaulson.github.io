---
layout: post
title:  "Formalising Gödel's incompleteness theorems, III: Coding and Bound Variables"
usemathjax: true
tags: Isabelle/HOL, Gödel, incompleteness, nominal Isabelle
---

Gödel's proof uses arithmetic (or in our case, hereditarily finite sets) to encode logical syntax, rules of inference, and therefore theorems of the internal calculus.
Coding techniques are ubiquitous in computation theory, complexity theory and elsewhere in logic under the general heading of problem reduction:
showing that something is impossible because it could otherwise be used to solve another problem already known to be impossible.
A complication is that our calculus involves variable binding, with the attendant horrors of name clashes and renaming.
As described in a [previous post]({% post_url 2022-05-18-Formalising-Incompleteness-I %}), the Isabelle/HOL formalisation of HF deals with variable binding through the nominal package, but when coding HF in itself we shall be forced to use a simpler technique, due to de Bruijn.

### de Bruijn indices

Briefly, [de Bruijn's technique](https://en.wikipedia.org/wiki/De_Bruijn_index) is to eliminate bound variable names altogether.
Bound variables become nonnegative integers, where 0 refers to the innermost binder and greater integers refer to binders further out. It destroys readability, but that is no problem for coding.
De Bruijn's [own exposition](/papers/deBruijn-nameless-dummies.pdf)
include remarks on the application of his technique to [AUTOMATH]({% post_url 2021-11-03-AUTOMATH %}), and today it is ubiquitous in proof assistants. 

The definition of coding is via an intermediate representation of HF terms and formulas, which uses de Bruijn indices rather than nominal for variable binding. Even these definitions must be done using the nominal package, as they involve the type `name`. Proving the fidelity of the translation between the two representations is nontrivial.

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






I have [previously commented]({% post_url 2021-12-15-Incompleteness %}) on the relevance of Gödel incompleteness to formalisation.


