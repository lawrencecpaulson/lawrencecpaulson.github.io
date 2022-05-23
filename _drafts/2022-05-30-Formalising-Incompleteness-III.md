---
layout: post
title:  "Formalising Gödel's incompleteness theorems, III: Coding and Bound Variables"
usemathjax: true
tags: Isabelle/HOL, Gödel, incompleteness, nominal Isabelle
---

Gödel's proof uses arithmetic (or in our case, [hereditarily finite sets]({% post_url 2022-02-23-Hereditarily_Finite %})) to encode logical syntax, rules of inference, and therefore theorems of the internal calculus.
Coding techniques are ubiquitous in computation theory, complexity theory and elsewhere in logic under the general heading of *problem reduction*:
showing that something is impossible because it could otherwise be used to solve another problem already known to be impossible.
A complication is that our calculus involves variable binding, with the attendant horrors of name clashes and renaming.
As described in a [previous post]({% post_url 2022-05-18-Formalising-Incompleteness-I %}), the Isabelle/HOL formalisation of HF deals with variable binding through the nominal package, but when coding HF in itself we shall be forced to use a simpler technique, due to de Bruijn.

### de Bruijn indices

Briefly, [de Bruijn's technique](https://en.wikipedia.org/wiki/De_Bruijn_index) is to eliminate bound variable names altogether.
Bound variables become nonnegative integers, where 0 refers to the innermost binder and greater integers refer to binders further out. It destroys readability, but that is no problem for coding.
De Bruijn's [own exposition](/papers/deBruijn-nameless-dummies.pdf)
include remarks on the application of his technique to [AUTOMATH]({% post_url 2021-11-03-AUTOMATH %}), and today it is ubiquitous in proof assistants. 

The definition of coding is via an intermediate representation of HF terms and formulas, which uses de Bruijn indices rather than nominal for variable binding. Even these definitions must be done using the nominal package, as they involve the type `name`. Proving the fidelity of the translation between the two representations is nontrivial.

### Isabelle definitions terms and formulas, using de Bruijn indices

We begin with terms. Free variables are identified by their names, as before, while bound variables are identified by their de Bruijn index.

<pre class="source">
<span class="keyword1 command">nominal_datatype</span> dbtm <span class="main">=</span> DBZero <span class="main">|</span> DBVar <span class="quoted">name</span> <span class="main">|</span> DBInd <span class="quoted">nat</span> <span class="main">|</span> DBEats <span class="quoted">dbtm</span> <span class="quoted">dbtm</span>
</pre>

The datatype for de Bruijn formulas is different only in the last constructor, because existential quantification no longer mentions a variable name.

<pre class="source">
<span class="keyword1 command">nominal_datatype</span> dbfm <span class="main">=</span><span>
    </span>DBMem <span class="quoted">dbtm</span> <span class="quoted">dbtm</span><span>
  </span><span class="main">|</span> DBEq <span class="quoted">dbtm</span> <span class="quoted">dbtm</span><span>
  </span><span class="main">|</span> DBDisj <span class="quoted">dbfm</span> <span class="quoted">dbfm</span><span>
  </span><span class="main">|</span> DBNeg <span class="quoted">dbfm</span><span>
  </span><span class="main">|</span> DBEx <span class="quoted">dbfm</span>
</pre>

The translation from nominal terms to de Bruijn terms has at its heart the following function, which looks up a name in an *environment* of distinct names (representing the variable binding context), returning the appropriate index if the name is found.

<pre class="source">
<span class="keyword1 command">fun</span> <span class="entity">lookup</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>name</span> list <span class="main">⇒</span> nat <span class="main">⇒</span> name</span> <span class="main">⇒</span> dbtm<span>"</span><span>
  </span><span class="keyword2 keyword">where</span><span>
    </span><span class="quoted"><span class="quoted"><span>"</span><span class="free">lookup</span> <span class="main">[]</span> <span class="free bound entity">n</span> <span class="free bound entity">x</span> <span class="main">=</span> DBVar</span> <span class="free bound entity">x</span><span>"</span></span><span>
  </span><span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">lookup</span> <span class="main">(</span><span class="free bound entity">y</span> <span class="main">#</span> <span class="free bound entity">ys</span><span class="main">)</span> <span class="free bound entity">n</span> <span class="free bound entity">x</span> <span class="main">=</span> <span class="main">(</span><span class="keyword1">if</span> <span class="free bound entity">x</span> <span class="main">=</span> <span class="free bound entity">y</span> <span class="keyword1">then</span> DBInd</span> <span class="free bound entity">n</span> <span class="keyword1">else</span> <span class="main">(</span><span class="free">lookup</span> <span class="free bound entity">ys</span> <span class="main">(</span>Suc <span class="free bound entity">n</span><span class="main">)</span> <span class="free bound entity">x</span><span class="main">)</span><span class="main">)</span><span>"</span></span>
</pre>

The translation itself is the obvious recursive traversal, calling the function above.
The argument `e` is the environment in which variables are interpreted.

<pre class="source">
<span class="keyword1 command">nominal_function</span> <span class="entity">trans_tm</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>name</span> list <span class="main">⇒</span> tm</span> <span class="main">⇒</span> dbtm<span>"</span><span>
  </span><span class="keyword2 keyword">where</span><span>
   </span><span class="quoted"><span class="quoted"><span>"</span><span class="free">trans_tm</span> <span class="free bound entity">e</span> Zero</span> <span class="main">=</span> DBZero</span><span>"</span><span>
 </span><span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">trans_tm</span> <span class="free bound entity">e</span> <span class="main">(</span>Var</span> <span class="free bound entity">k</span><span class="main">)</span> <span class="main">=</span> lookup</span> <span class="free bound entity">e</span> <span class="main">0</span> <span class="free bound entity">k</span><span>"</span><span>
 </span><span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">trans_tm</span> <span class="free bound entity">e</span> <span class="main">(</span>Eats</span> <span class="free bound entity">t</span> <span class="free bound entity">u</span><span class="main">)</span> <span class="main">=</span> DBEats</span> <span class="main">(</span><span class="free">trans_tm</span> <span class="free bound entity">e</span> <span class="free bound entity">t</span><span class="main">)</span> <span class="main">(</span><span class="free">trans_tm</span> <span class="free bound entity">e</span> <span class="free bound entity">u</span><span class="main">)</span><span>"</span>
</pre>

The translation of formulas involves a little trickery that I would rather gloss over, while noting that the condition in the last line requires the quantified variable to be fresh with respect to the environment `e`, which it then extends in the recursive call for translating the body of the quantification.

<pre class="source">
<span class="keyword1 command">nominal_function</span> <span class="main">(</span>invariant <span class="quoted"><span class="quoted"><span>"</span><span class="main">λ</span><span class="main">(</span><span class="bound">xs</span><span class="main">,</span> <span class="main bound">_</span><span class="main">)</span> <span class="bound">y</span><span class="main">.</span> atom</span> <span class="main">`</span> set <span class="bound">xs</span> <span class="main">♯*</span></span> <span class="bound">y</span><span>"</span><span class="main">)</span><span>
  </span><span class="entity">trans_fm</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>name</span> list <span class="main">⇒</span> fm</span> <span class="main">⇒</span> dbfm<span>"</span><span>
  </span><span class="keyword2 keyword">where</span><span>
   </span><span class="quoted"><span class="quoted"><span>"</span><span class="free">trans_fm</span> <span class="free bound entity">e</span> <span class="main">(</span>Mem</span> <span class="free bound entity">t</span> <span class="free bound entity">u</span><span class="main">)</span> <span class="main">=</span> DBMem</span> <span class="main">(</span>trans_tm <span class="free bound entity">e</span> <span class="free bound entity">t</span><span class="main">)</span> <span class="main">(</span>trans_tm <span class="free bound entity">e</span> <span class="free bound entity">u</span><span class="main">)</span><span>"</span><span>
 </span><span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">trans_fm</span> <span class="free bound entity">e</span> <span class="main">(</span>Eq</span> <span class="free bound entity">t</span> <span class="free bound entity">u</span><span class="main">)</span>  <span class="main">=</span> DBEq</span> <span class="main">(</span>trans_tm <span class="free bound entity">e</span> <span class="free bound entity">t</span><span class="main">)</span> <span class="main">(</span>trans_tm <span class="free bound entity">e</span> <span class="free bound entity">u</span><span class="main">)</span><span>"</span><span>
 </span><span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">trans_fm</span> <span class="free bound entity">e</span> <span class="main">(</span>Disj</span> <span class="free bound entity">A</span> <span class="free bound entity">B</span><span class="main">)</span> <span class="main">=</span> DBDisj</span> <span class="main">(</span><span class="free">trans_fm</span> <span class="free bound entity">e</span> <span class="free bound entity">A</span><span class="main">)</span> <span class="main">(</span><span class="free">trans_fm</span> <span class="free bound entity">e</span> <span class="free bound entity">B</span><span class="main">)</span><span>"</span><span>
 </span><span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">trans_fm</span> <span class="free bound entity">e</span> <span class="main">(</span>Neg</span> <span class="free bound entity">A</span><span class="main">)</span>   <span class="main">=</span> DBNeg</span> <span class="main">(</span><span class="free">trans_fm</span> <span class="free bound entity">e</span> <span class="free bound entity">A</span><span class="main">)</span><span>"</span><span>
 </span><span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span>atom</span> <span class="free bound entity">k</span> <span class="main">♯</span></span> <span class="free bound entity">e</span> <span class="main">⟹</span> <span class="free">trans_fm</span> <span class="free bound entity">e</span> <span class="main">(</span>Ex <span class="free bound entity">k</span> <span class="free bound entity">A</span><span class="main">)</span> <span class="main">=</span> DBEx <span class="main">(</span><span class="free">trans_fm</span> <span class="main">(</span><span class="free bound entity">k</span><span class="main">#</span><span class="free bound entity">e</span><span class="main">)</span> <span class="free bound entity">A</span><span class="main">)</span><span>"</span>
</pre>

These translations turn out to be injective. The proof is a simple induction on `t` followed by case analysis on `u`.

<pre class="source">
<span class="keyword1 command">lemma</span> trans_tm_inject <span class="main">[</span><span class="operator">iff</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span>trans_tm</span> <span class="free">e</span> <span class="free">t</span> <span class="main">=</span> trans_tm</span> <span class="free">e</span> <span class="free">u</span><span class="main">)</span> <span class="main">⟷</span> <span class="free">t</span> <span class="main">=</span> <span class="free">u</span><span>"
</pre>

Translations of formulas are also injective, by a largely similar proof.
The existential case requires about 20 lines of reasoning, referring to nominal primitives, to show that the translation yields the same result regardless of whether or not the bound variables are identical.

<pre class="source">
<span class="keyword1 command">lemma</span> trans_fm_inject <span class="main">[</span><span class="operator">iff</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span>trans_fm</span> <span class="free">e</span> <span class="free">A</span> <span class="main">=</span> trans_fm</span> <span class="free">e</span> <span class="free">B</span><span class="main">)</span> <span class="main">⟷</span> <span class="free">A</span> <span class="main">=</span> <span class="free">B</span><span>"</span>
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


