---
layout: post
title:  "Formalising Gödel's incompleteness theorems, III: Coding and Bound Variables"
usemathjax: true
tags: Isabelle/HOL, Gödel, incompleteness, nominal Isabelle
---

The key to Gödel's proof is using arithmetic (or in our case, hereditarily finite sets) to encode logical syntax, rules of inference, and therefore theorems of the internal calculus.
Such techniques are ubiquitous in computation theory, complexity theory and elsewhere in logic under the general heading of problem reduction:
showing that something is impossible because it could otherwise be used to solve another problem already known to be impossible.
A big complication is that the syntax of our logic involves variable binding, with the attendant horrors of name clashes that complicate many proofs.
As described in a [previous post]({% post_url 2022-05-18-Formalising-Incompleteness-I %}), the Isabelle/HOL formalisation of HF deals with variable binding through the nominal package, but when coding HF in itself we shall be forced to use a simpler technique, due to de Bruijn.

### de Bruijn indices

Briefly, [de Bruijn's technique](https://en.wikipedia.org/wiki/De_Bruijn_index) is to eliminate bound variable names altogether.
Bound variables become nonnegative integers, where 0 refers to the innermost binder and greater integers refer to binders further out. It utterly destroys readability, but that is no problem for coding.
De Bruijn's [own exposition](/papers/deBruijn-nameless-dummies.pdf)
include remarks on the application of his technique to [AUTOMATH]({% post_url 2021-11-03-AUTOMATH %})). 

To formalise the process of coding, it seems simplest to define a second formalisation of HF terms and formulas, using de Bruijn indices. Even this must be done using the nominal package, as it involves the type `name`, and proving the faithfulness of the translation between the two representations is nontrivial.

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


