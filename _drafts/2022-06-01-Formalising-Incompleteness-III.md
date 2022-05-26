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

### Overview of de Bruijn indices

Briefly, [de Bruijn's technique](https://en.wikipedia.org/wiki/De_Bruijn_index) is to eliminate bound variable names altogether.
Bound variables become nonnegative integers, where 0 refers to the innermost binder and greater integers refer to binders further out. It destroys readability, but that is no problem for coding.
De Bruijn's [own exposition](/papers/deBruijn-nameless-dummies.pdf)
include remarks on the application of his technique to [AUTOMATH]({% post_url 2021-11-03-AUTOMATH %}), and today it is ubiquitous in proof assistants. 

The definition of coding is via an intermediate representation of HF terms and formulas, which uses de Bruijn indices rather than nominal for variable binding. Even these definitions must be done using the nominal package, as they involve the type `name`. Proving the fidelity of the translation between the two representations is nontrivial.

### Isabelle definitions terms and formulas, using de Bruijn indices

We begin with terms. Free variables are identified by their names, [as before]({% post_url 2022-05-18-Formalising-Incompleteness-I %}), while bound variables are identified by their de Bruijn index.

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

The translation itself is the obvious recursive traversal, calling the lookup function above.
The argument `e` is the *environment* in which variables are interpreted.

<pre class="source">
<span class="keyword1 command">nominal_function</span> <span class="entity">trans_tm</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>name</span> list <span class="main">⇒</span> tm</span> <span class="main">⇒</span> dbtm<span>"</span><span>
  </span><span class="keyword2 keyword">where</span><span>
   </span><span class="quoted"><span class="quoted"><span>"</span><span class="free">trans_tm</span> <span class="free bound entity">e</span> Zero</span> <span class="main">=</span> DBZero</span><span>"</span><span>
 </span><span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">trans_tm</span> <span class="free bound entity">e</span> <span class="main">(</span>Var</span> <span class="free bound entity">k</span><span class="main">)</span> <span class="main">=</span> lookup</span> <span class="free bound entity">e</span> <span class="main">0</span> <span class="free bound entity">k</span><span>"</span><span>
 </span><span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">trans_tm</span> <span class="free bound entity">e</span> <span class="main">(</span>Eats</span> <span class="free bound entity">t</span> <span class="free bound entity">u</span><span class="main">)</span> <span class="main">=</span> DBEats</span> <span class="main">(</span><span class="free">trans_tm</span> <span class="free bound entity">e</span> <span class="free bound entity">t</span><span class="main">)</span> <span class="main">(</span><span class="free">trans_tm</span> <span class="free bound entity">e</span> <span class="free bound entity">u</span><span class="main">)</span><span>"</span>
</pre>

The translation of formulas involves a little trickery that I would rather gloss over
(Christian Urban did this, and only he properly understands it).
Note that the condition in the last line requires the quantified variable to be fresh with respect to the environment `e`, which it then extends in the recursive call for translating the body of the quantification.

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
<span class="keyword1 command">lemma</span> trans_tm_inject <span class="main">[</span><span class="operator">iff</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span>trans_tm</span> <span class="free">e</span> <span class="free">t</span> <span class="main">=</span> trans_tm</span> <span class="free">e</span> <span class="free">u</span><span class="main">)</span> <span class="main">⟷</span> <span class="free">t</span> <span class="main">=</span> <span class="free">u</span><span>"</span>
</pre>

Translations of formulas are also injective, by a mostly similar proof.
The existential case requires about 20 lines of reasoning, referring to nominal primitives, to show that the translation yields the same result regardless of whether or not the bound variables are identical.

<pre class="source">
<span class="keyword1 command">lemma</span> trans_fm_inject <span class="main">[</span><span class="operator">iff</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span>trans_fm</span> <span class="free">e</span> <span class="free">A</span> <span class="main">=</span> trans_fm</span> <span class="free">e</span> <span class="free">B</span><span class="main">)</span> <span class="main">⟷</span> <span class="free">A</span> <span class="main">=</span> <span class="free">B</span><span>"</span>
</pre>

###  Abstraction and substitution on de Bruijn formulas

Abstraction and substitution are key operations in the de Bruijn representation. 
Abstraction takes a name, an index number and a term, replacing every occurrence of the named variable by the given index. Here is the version for terms:

<pre class="source">
<span class="keyword1 command">nominal_function</span> <span class="entity">abst_dbtm</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>name</span> <span class="main">⇒</span> nat <span class="main">⇒</span> dbtm</span> <span class="main">⇒</span> dbtm<span>"</span><span>
  </span><span class="keyword2 keyword">where</span><span>
   </span><span class="quoted"><span class="quoted"><span>"</span><span class="free">abst_dbtm</span> <span class="free bound entity">name</span> <span class="free bound entity">i</span> DBZero</span> <span class="main">=</span> DBZero</span><span>"</span><span>
 </span><span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">abst_dbtm</span> <span class="free bound entity">name</span> <span class="free bound entity">i</span> <span class="main">(</span>DBVar</span> <span class="free bound entity">name'</span><span class="main">)</span> <span class="main">=</span> <span class="main">(</span><span class="keyword1">if</span> <span class="free bound entity">name</span> <span class="main">=</span> <span class="free bound entity">name'</span> <span class="keyword1">then</span> DBInd</span> <span class="free bound entity">i</span> <span class="keyword1">else</span> DBVar <span class="free bound entity">name'</span><span class="main">)</span><span>"</span><span>
 </span><span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">abst_dbtm</span> <span class="free bound entity">name</span> <span class="free bound entity">i</span> <span class="main">(</span>DBInd</span> <span class="free bound entity">j</span><span class="main">)</span> <span class="main">=</span> DBInd</span> <span class="free bound entity">j</span><span>"</span><span>
 </span><span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">abst_dbtm</span> <span class="free bound entity">name</span> <span class="free bound entity">i</span> <span class="main">(</span>DBEats</span> <span class="free bound entity">t1</span> <span class="free bound entity">t2</span><span class="main">)</span> <span class="main">=</span> DBEats</span> <span class="main">(</span><span class="free">abst_dbtm</span> <span class="free bound entity">name</span> <span class="free bound entity">i</span> <span class="free bound entity">t1</span><span class="main">)</span> <span class="main">(</span><span class="free">abst_dbtm</span> <span class="free bound entity">name</span> <span class="free bound entity">i</span> <span class="free bound entity">t2</span><span class="main">)</span><span>"</span>
</pre>

Substitution replaces a (necessarily free) occurrence of a named variable by a term.
The term version looks almost the same as abstraction, but wait until we get to formulas.

<pre class="source">
<span class="keyword1 command">nominal_function</span> <span class="entity">subst_dbtm</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>dbtm</span> <span class="main">⇒</span> name</span> <span class="main">⇒</span> dbtm <span class="main">⇒</span> dbtm<span>"</span><span>
  </span><span class="keyword2 keyword">where</span><span>
   </span><span class="quoted"><span class="quoted"><span>"</span><span class="free">subst_dbtm</span> <span class="free bound entity">u</span> <span class="free bound entity">x</span> DBZero</span> <span class="main">=</span> DBZero</span><span>"</span><span>
 </span><span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">subst_dbtm</span> <span class="free bound entity">u</span> <span class="free bound entity">x</span> <span class="main">(</span>DBVar</span> <span class="free bound entity">name</span><span class="main">)</span> <span class="main">=</span> <span class="main">(</span><span class="keyword1">if</span> <span class="free bound entity">x</span> <span class="main">=</span> <span class="free bound entity">name</span> <span class="keyword1">then</span> <span class="free bound entity">u</span> <span class="keyword1">else</span> DBVar</span> <span class="free bound entity">name</span><span class="main">)</span><span>"</span><span>
 </span><span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">subst_dbtm</span> <span class="free bound entity">u</span> <span class="free bound entity">x</span> <span class="main">(</span>DBInd</span> <span class="free bound entity">j</span><span class="main">)</span> <span class="main">=</span> DBInd</span> <span class="free bound entity">j</span><span>"</span><span>
 </span><span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">subst_dbtm</span> <span class="free bound entity">u</span> <span class="free bound entity">x</span> <span class="main">(</span>DBEats</span> <span class="free bound entity">t1</span> <span class="free bound entity">t2</span><span class="main">)</span> <span class="main">=</span> DBEats</span> <span class="main">(</span><span class="free">subst_dbtm</span> <span class="free bound entity">u</span> <span class="free bound entity">x</span> <span class="free bound entity">t1</span><span class="main">)</span> <span class="main">(</span><span class="free">subst_dbtm</span> <span class="free bound entity">u</span> <span class="free bound entity">x</span> <span class="free bound entity">t2</span><span class="main">)</span><span>"</span>
</pre>


The following fact relates the translation of the term in an extended environment with translating the same term without the extension, then abstracting over an additional name. The proof is another trivial induction.
 
<pre class="source">
<span class="keyword1 command">lemma</span> trans_tm_abs<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>trans_tm</span> <span class="main">(</span><span class="free">e</span><span class="main">@</span><span class="main">[</span><span class="free">name</span><span class="main">]</span><span class="main">)</span> <span class="free">t</span> <span class="main">=</span> abst_dbtm</span> <span class="free">name</span> <span class="main">(</span>length <span class="free">e</span><span class="main">)</span> <span class="main">(</span>trans_tm <span class="free">e</span> <span class="free">t</span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">induct</span> <span class="quoted free">t</span> <span class="quasi_keyword">rule</span><span class="main main">:</span> tm.induct<span class="main">)</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> lookup_notin lookup_append<span class="main">)</span>
</pre>

Abstraction over formulas satisfies the corresponding property.
Its definition is the obvious structural recursion **except** for the last line, which increments the index. The point is that a quantifier binds a new variable.

<pre class="source">
<span class="keyword1 command">nominal_function</span> <span class="entity">abst_dbfm</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>name</span> <span class="main">⇒</span> nat <span class="main">⇒</span> dbfm</span> <span class="main">⇒</span> dbfm<span>"</span><span>
  </span><span class="keyword2 keyword">where</span><span>
   </span><span class="quoted"><span class="quoted"><span>"</span><span class="free">abst_dbfm</span> <span class="free bound entity">name</span> <span class="free bound entity">i</span> <span class="main">(</span>DBMem</span> <span class="free bound entity">t1</span> <span class="free bound entity">t2</span><span class="main">)</span> <span class="main">=</span> DBMem</span> <span class="main">(</span>abst_dbtm <span class="free bound entity">name</span> <span class="free bound entity">i</span> <span class="free bound entity">t1</span><span class="main">)</span> <span class="main">(</span>abst_dbtm <span class="free bound entity">name</span> <span class="free bound entity">i</span> <span class="free bound entity">t2</span><span class="main">)</span><span>"</span><span>
 </span><span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">abst_dbfm</span> <span class="free bound entity">name</span> <span class="free bound entity">i</span> <span class="main">(</span>DBEq</span> <span class="free bound entity">t1</span> <span class="free bound entity">t2</span><span class="main">)</span> <span class="main">=</span>  DBEq</span> <span class="main">(</span>abst_dbtm <span class="free bound entity">name</span> <span class="free bound entity">i</span> <span class="free bound entity">t1</span><span class="main">)</span> <span class="main">(</span>abst_dbtm <span class="free bound entity">name</span> <span class="free bound entity">i</span> <span class="free bound entity">t2</span><span class="main">)</span><span>"</span><span>
 </span><span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">abst_dbfm</span> <span class="free bound entity">name</span> <span class="free bound entity">i</span> <span class="main">(</span>DBDisj</span> <span class="free bound entity">A1</span> <span class="free bound entity">A2</span><span class="main">)</span> <span class="main">=</span> DBDisj</span> <span class="main">(</span><span class="free">abst_dbfm</span> <span class="free bound entity">name</span> <span class="free bound entity">i</span> <span class="free bound entity">A1</span><span class="main">)</span> <span class="main">(</span><span class="free">abst_dbfm</span> <span class="free bound entity">name</span> <span class="free bound entity">i</span> <span class="free bound entity">A2</span><span class="main">)</span><span>"</span><span>
 </span><span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">abst_dbfm</span> <span class="free bound entity">name</span> <span class="free bound entity">i</span> <span class="main">(</span>DBNeg</span> <span class="free bound entity">A</span><span class="main">)</span> <span class="main">=</span> DBNeg</span> <span class="main">(</span><span class="free">abst_dbfm</span> <span class="free bound entity">name</span> <span class="free bound entity">i</span> <span class="free bound entity">A</span><span class="main">)</span><span>"</span><span>
 </span><span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">abst_dbfm</span> <span class="free bound entity">name</span> <span class="free bound entity">i</span> <span class="main">(</span>DBEx</span> <span class="free bound entity">A</span><span class="main">)</span> <span class="main">=</span> DBEx</span> <span class="main">(</span><span class="free">abst_dbfm</span> <span class="free bound entity">name</span> <span class="main">(</span><span class="free bound entity">i</span><span class="main">+</span><span class="main">1</span><span class="main">)</span> <span class="free bound entity">A</span><span class="main">)</span><span>"</span>
</pre>

Substitution for free variables in a formula is different from abstraction, because the quantifier case is treated exactly like all the others.

<pre class="source">
<span class="keyword1 command">nominal_function</span> <span class="entity">subst_dbfm</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>dbtm</span> <span class="main">⇒</span> name</span> <span class="main">⇒</span> dbfm <span class="main">⇒</span> dbfm<span>"</span><span>
  </span><span class="keyword2 keyword">where</span><span>
   </span><span class="quoted"><span class="quoted"><span>"</span><span class="free">subst_dbfm</span> <span class="free bound entity">u</span> <span class="free bound entity">x</span> <span class="main">(</span>DBMem</span> <span class="free bound entity">t1</span> <span class="free bound entity">t2</span><span class="main">)</span> <span class="main">=</span> DBMem</span> <span class="main">(</span>subst_dbtm <span class="free bound entity">u</span> <span class="free bound entity">x</span> <span class="free bound entity">t1</span><span class="main">)</span> <span class="main">(</span>subst_dbtm <span class="free bound entity">u</span> <span class="free bound entity">x</span> <span class="free bound entity">t2</span><span class="main">)</span><span>"</span><span>
 </span><span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">subst_dbfm</span> <span class="free bound entity">u</span> <span class="free bound entity">x</span> <span class="main">(</span>DBEq</span> <span class="free bound entity">t1</span> <span class="free bound entity">t2</span><span class="main">)</span> <span class="main">=</span>  DBEq</span> <span class="main">(</span>subst_dbtm <span class="free bound entity">u</span> <span class="free bound entity">x</span> <span class="free bound entity">t1</span><span class="main">)</span> <span class="main">(</span>subst_dbtm <span class="free bound entity">u</span> <span class="free bound entity">x</span> <span class="free bound entity">t2</span><span class="main">)</span><span>"</span><span>
 </span><span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">subst_dbfm</span> <span class="free bound entity">u</span> <span class="free bound entity">x</span> <span class="main">(</span>DBDisj</span> <span class="free bound entity">A1</span> <span class="free bound entity">A2</span><span class="main">)</span> <span class="main">=</span> DBDisj</span> <span class="main">(</span><span class="free">subst_dbfm</span> <span class="free bound entity">u</span> <span class="free bound entity">x</span> <span class="free bound entity">A1</span><span class="main">)</span> <span class="main">(</span><span class="free">subst_dbfm</span> <span class="free bound entity">u</span> <span class="free bound entity">x</span> <span class="free bound entity">A2</span><span class="main">)</span><span>"</span><span>
 </span><span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">subst_dbfm</span> <span class="free bound entity">u</span> <span class="free bound entity">x</span> <span class="main">(</span>DBNeg</span> <span class="free bound entity">A</span><span class="main">)</span> <span class="main">=</span> DBNeg</span> <span class="main">(</span><span class="free">subst_dbfm</span> <span class="free bound entity">u</span> <span class="free bound entity">x</span> <span class="free bound entity">A</span><span class="main">)</span><span>"</span><span>
 </span><span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">subst_dbfm</span> <span class="free bound entity">u</span> <span class="free bound entity">x</span> <span class="main">(</span>DBEx</span> <span class="free bound entity">A</span><span class="main">)</span> <span class="main">=</span> DBEx</span> <span class="main">(</span><span class="free">subst_dbfm</span> <span class="free bound entity">u</span> <span class="free bound entity">x</span> <span class="free bound entity">A</span><span class="main">)</span><span>"</span>
</pre>

The term being substituted must be entirely without the `DBInd` constructor.
The time has come to talk about the concept of a de Bruijn term or formula being well-formed.

### Well-formed de Bruijn terms and formulas

A de Bruijn index requires a matching binder, and we've a problem if it doesn't exist.
The notion of de Bruijn terms and formulas being *well-formed* is straightforward to formalise.
As always, we begin with the terms:

<pre class="source">
<span class="keyword1 command">inductive</span> <span class="entity">wf_dbtm</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>dbtm</span> <span class="main">⇒</span> bool<span>"</span></span><span>
  </span><span class="keyword2 keyword">where</span><span>
    </span>Zero<span class="main">:</span>  <span class="quoted"><span class="quoted"><span>"</span><span class="free">wf_dbtm</span> DBZero</span><span>"</span></span><span>
  </span><span class="main">|</span> Var<span class="main">:</span>   <span class="quoted"><span class="quoted"><span>"</span><span class="free">wf_dbtm</span> <span class="main">(</span>DBVar</span> <span class="free bound entity">name</span><span class="main">)</span><span>"</span></span><span>
  </span><span class="main">|</span> Eats<span class="main">:</span>  <span class="quoted"><span class="quoted"><span>"</span><span class="free">wf_dbtm</span> <span class="free bound entity">t1</span> <span class="main">⟹</span> <span class="free">wf_dbtm</span> <span class="free bound entity">t2</span> <span class="main">⟹</span> <span class="free">wf_dbtm</span> <span class="main">(</span>DBEats</span> <span class="free bound entity">t1</span> <span class="free bound entity">t2</span><span class="main">)</span><span>"</span></span>
</pre>

This may look strange, because the index constructor (`DBInd`) is simply prohibited.
But this is correct because terms have no binding construct.
The proof that every well formed de Bruijn term is equal to the translation of a nominal term is an elementary induction:

<pre class="source">
<span class="keyword1 command">lemma</span> wf_dbtm_imp_is_tm<span class="main">:</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span>wf_dbtm</span> <span class="free">x</span><span>"</span></span><span>
  </span><span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">∃</span><span class="bound">t</span><span class="main">::</span>tm</span><span class="main">.</span> <span class="free">x</span> <span class="main">=</span> trans_tm</span> <span class="main">[]</span> <span class="bound">t</span><span>"</span>
<span class="keyword1 command">using</span> assms
<span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">induct</span> <span class="quasi_keyword">rule</span><span class="main main">:</span> wf_dbtm.induct<span class="main">)</span><span>
  </span><span class="keyword3 command">case</span> Zero <span class="keyword3 command">thus</span> <span class="var quoted var">?case</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> trans_tm.simps<span class="main main">(</span>1<span class="main main">)</span><span class="main">)</span>
<span class="keyword1 command">next</span><span>
  </span><span class="keyword3 command">case</span> <span class="main">(</span>Var <span class="skolem">i</span><span class="main">)</span> <span class="keyword3 command">thus</span> <span class="var quoted var">?case</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> lookup.simps<span class="main main">(</span>1<span class="main main">)</span> trans_tm.simps<span class="main main">(</span>2<span class="main main">)</span><span class="main">)</span>
<span class="keyword1 command">next</span><span>
  </span><span class="keyword3 command">case</span> <span class="main">(</span>Eats <span class="skolem">dt1</span> <span class="skolem">dt2</span><span class="main">)</span> <span class="keyword3 command">thus</span> <span class="var quoted var">?case</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> trans_tm.simps<span class="main main">(</span>3<span class="main main">)</span><span class="main">)</span>
<span class="keyword1 command">qed</span>
</pre>

The opposite direction, that the translation of a term is always well formed, is an even simpler induction:

<pre class="source">
<span class="keyword1 command">lemma</span> wf_dbtm_trans_tm<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>wf_dbtm</span> <span class="main">(</span>trans_tm</span> <span class="main">[]</span> <span class="free">t</span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">induct</span> <span class="quoted free">t</span> <span class="quasi_keyword">rule</span><span class="main main">:</span> tm.induct<span class="main">)</span> <span class="operator">auto</span>
</pre>

And so we can characterise the well-formed de Bruijn terms *precisely* as the translations of nominal terms.

<pre class="source">
<span class="keyword1 command">theorem</span> wf_dbtm_iff_is_tm<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>wf_dbtm</span> <span class="free">x</span> <span class="main">⟷</span> <span class="main">(</span><span class="main">∃</span><span class="bound">t</span><span class="main">::</span>tm</span><span class="main">.</span> <span class="free">x</span> <span class="main">=</span> trans_tm <span class="main">[]</span> <span class="bound">t</span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> wf_dbtm_imp_is_tm wf_dbtm_trans_tm<span class="main">)</span>
</pre>

A well formed de Bruijn formula is defined in terms of abstraction in the last line, which handles the existential quantifier. The abstraction operation is called with the name of the quantified variable, substituting a de Bruijn index of 0. The abstraction operation will increase this index as it passes through other quantifiers. A lot is going on, and yet the definition is simple.

<pre class="source">
<span class="keyword1 command">inductive</span> <span class="entity">wf_dbfm</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>dbfm</span> <span class="main">⇒</span> bool<span>"</span></span><span>
  </span><span class="keyword2 keyword">where</span><span>
    </span>Mem<span class="main">:</span>   <span class="quoted"><span class="quoted"><span>"</span>wf_dbtm</span> <span class="free bound entity">t1</span> <span class="main">⟹</span> wf_dbtm</span> <span class="free bound entity">t2</span> <span class="main">⟹</span> <span class="free">wf_dbfm</span> <span class="main">(</span>DBMem <span class="free bound entity">t1</span> <span class="free bound entity">t2</span><span class="main">)</span><span>"</span><span>
  </span><span class="main">|</span> Eq<span class="main">:</span>    <span class="quoted"><span class="quoted"><span>"</span>wf_dbtm</span> <span class="free bound entity">t1</span> <span class="main">⟹</span> wf_dbtm</span> <span class="free bound entity">t2</span> <span class="main">⟹</span> <span class="free">wf_dbfm</span> <span class="main">(</span>DBEq <span class="free bound entity">t1</span> <span class="free bound entity">t2</span><span class="main">)</span><span>"</span><span>
  </span><span class="main">|</span> Disj<span class="main">:</span>  <span class="quoted"><span class="quoted"><span>"</span><span class="free">wf_dbfm</span> <span class="free bound entity">A1</span> <span class="main">⟹</span> <span class="free">wf_dbfm</span> <span class="free bound entity">A2</span> <span class="main">⟹</span> <span class="free">wf_dbfm</span> <span class="main">(</span>DBDisj</span> <span class="free bound entity">A1</span> <span class="free bound entity">A2</span><span class="main">)</span><span>"</span></span><span>
  </span><span class="main">|</span> Neg<span class="main">:</span>   <span class="quoted"><span class="quoted"><span>"</span><span class="free">wf_dbfm</span> <span class="free bound entity">A</span> <span class="main">⟹</span> <span class="free">wf_dbfm</span> <span class="main">(</span>DBNeg</span> <span class="free bound entity">A</span><span class="main">)</span><span>"</span></span><span>
  </span><span class="main">|</span> Ex<span class="main">:</span>    <span class="quoted"><span class="quoted"><span>"</span><span class="free">wf_dbfm</span> <span class="free bound entity">A</span> <span class="main">⟹</span> <span class="free">wf_dbfm</span> <span class="main">(</span>DBEx</span> <span class="main">(</span>abst_dbfm</span> <span class="free bound entity">name</span> <span class="main">0</span> <span class="free bound entity">A</span><span class="main">)</span><span class="main">)</span><span>"</span>
</pre>

Application of similar techniques gives us a characterisation of well-formed de Bruijn formulas.

<pre class="source">
<span class="keyword1 command">lemma</span> wf_dbfm_iff_is_fm<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>wf_dbfm</span> <span class="free">x</span> <span class="main">⟷</span> <span class="main">(</span><span class="main">∃</span><span class="bound">A</span><span class="main">::</span>fm</span><span class="main">.</span> <span class="free">x</span> <span class="main">=</span> trans_fm <span class="main">[]</span> <span class="bound">A</span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> wf_dbfm_imp_is_fm wf_dbfm_trans_fm<span class="main">)</span>
</pre>

It's impressive that two absolutely different treatments of variable binding turn out to be exactly equivalent, and with so little effort in the proofs.
The formal specification of well-founded terms and formulas will be needed later in the incompleteness development.

###  A few commutativity properties

The development requires a great many facts relating substitution, abstraction, freshness and the translations between the nominal and de Bruijn levels. Here are just a couple. Thankfully, most of these are easy to prove.

If you have a formula and two distinct names, one of which is fresh for the term `u`, then substitution and abstraction actually commute.
And the proof is a single line!

<pre class="source">
<span class="keyword1 command">lemma</span> dbfm_abst_swap_subst<span class="main">:</span><span>
  </span><span class="quoted"><span class="quoted"><span>"</span><span class="free">name</span> <span class="main">≠</span> <span class="free">name'</span> <span class="main">⟹</span> atom</span> <span class="free">name'</span> <span class="main">♯</span></span> <span class="free">u</span> <span class="main">⟹</span><span>
   </span>subst_dbfm <span class="free">u</span> <span class="free">name</span> <span class="main">(</span>abst_dbfm <span class="free">name'</span> <span class="free">j</span> <span class="free">A</span><span class="main">)</span> <span class="main">=</span> abst_dbfm <span class="free">name'</span> <span class="free">j</span> <span class="main">(</span>subst_dbfm <span class="free">u</span> <span class="free">name</span> <span class="free">A</span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">induct</span> <span class="quoted free">A</span> <span class="quasi_keyword">arbitrary</span><span class="main main">:</span> <span class="quoted free">j</span> <span class="quasi_keyword">rule</span><span class="main main">:</span> dbfm.induct<span class="main">)</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> dbtm_abst_swap_subst<span class="main">)</span>
</pre>

Here, substitution on de Bruijn terms corresponds to substitution on the original nominal terms. The same property holds for formulas. The proof is again easy.

<pre class="source">
<span class="keyword1 command">lemma</span> subst_trans_commute <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span><span>
  </span><span class="quoted"><span class="quoted"><span>"</span>atom</span> <span class="free">i</span> <span class="main">♯</span></span> <span class="free">e</span> <span class="main">⟹</span> subst_dbtm <span class="main">(</span>trans_tm <span class="free">e</span> <span class="free">u</span><span class="main">)</span> <span class="free">i</span> <span class="main">(</span>trans_tm <span class="free">e</span> <span class="free">t</span><span class="main">)</span> <span class="main">=</span> trans_tm <span class="free">e</span> <span class="main">(</span>subst <span class="free">i</span> <span class="free">u</span> <span class="free">t</span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword1 command improper command">apply</span> <span class="main">(</span><span class="operator">induct</span> <span class="quoted free">t</span> <span class="quasi_keyword">rule</span><span class="main main">:</span> tm.induct<span class="main">)</span><span>
  </span><span class="keyword1 command improper command">apply</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> lookup_notin fresh_imp_notin_env<span class="main">)</span><span>
  </span><span class="keyword1 command improper command">apply</span> <span class="main">(</span><span class="operator">metis</span> abst_dbtm_fresh_ignore dbtm_subst_ignore lookup_fresh lookup_notin subst_dbtm.simps<span class="main main">(</span>2<span class="main main">)</span><span class="main">)</span><span>
  </span><span class="keyword1 command improper command">done</span>
</pre>

I imagine that readers have had enough of Gödel for the moment, so I shall have to think of something else for next week!
