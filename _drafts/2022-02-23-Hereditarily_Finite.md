---
layout: post
title:  "The hereditarily finite sets"
usemathjax: true 
tags: logic, set theory
---

A set is *hereditarily finite* if it is finite and all of its elements are hereditarily finite. They satisfy the axioms of set theory with the negation of the axiom of infinity. There are countably many HF sets, and they are a natural domain for formalising computation. They also allow a clean treatment of Gödel's incompleteness theorems.

### Introduction to the HF sets

The inductive conception of HF sets justifies the recursive definition $f(x)=\sum\, \lbrace 2^{f(y)}\mid y\in x\rbrace $, yielding a bijection $f:\text{HF}\to \mathbb{N}$  between the HF sets and the natural numbers.
Defining $x<y$ if and only if $f(x)<f(y)$ yields an linear ordering on HF.
It's easy to see that $<$ extends both the membership and the subset relations.

What about the inverse function $g$, mapping natural numbers to sets? 
Clearly $g(0) = \emptyset$. To understand $g(n)$ for $n>0$, imagine $n$ written in binary notation: then from the position of each 1 from right to left we recursively obtain an HF set from the number of 0s to its right. We can work out some values:

$$ \begin{align*}
g(0) &= \phi \\
g(1) &= \lbrace g(0)\rbrace  = \lbrace \phi\rbrace  \\
g(2) &= \lbrace g(1)\rbrace  = \lbrace \lbrace \phi\rbrace \rbrace  \\
g(3) &= \lbrace g(1), g(0)\rbrace  = \lbrace \lbrace \phi\rbrace, \phi\rbrace  \\
g(4) &= \lbrace g(2)\rbrace  = \lbrace \lbrace \lbrace \phi\rbrace \rbrace \rbrace  \\
g(5) &= \lbrace g(2), g(0)\rbrace  = \lbrace \lbrace \lbrace \phi\rbrace \rbrace , \phi\rbrace  \\
g(6) &= \lbrace g(2), g(1)\rbrace  = \lbrace \lbrace \lbrace \phi\rbrace \rbrace , \lbrace \phi\rbrace \rbrace  \\
g(7) &= \lbrace g(2), g(1), g(0)\rbrace = \lbrace \lbrace \lbrace \phi\rbrace \rbrace , \lbrace \phi\rbrace , \phi\rbrace \\
\vdots & \\
g(11) &= \lbrace g(3), g(1), g(0)\rbrace  = \lbrace \lbrace \lbrace \phi\rbrace, \phi\rbrace, \lbrace \phi\rbrace , \phi\rbrace 
\end{align*} $$

Note that 11 is 1011 in binary and that $g(0)$, $g(1)$, $g(3)$ and $g(11)$ are the first four von Neumann ordinals. It seems that if $n$ codes an ordinal then $2^n+n$ codes the next ordinal, so the ordinal 4 is $g(2059)$.

The way $g$ operates on binary strings reminds me of the [Pascal](https://dl.acm.org/doi/10.1145/234286.1057812) 
programming language's *set types*, which provide clean access to the hardware bit level. A Pascal set is a bit string: bitwise “and” performs intersection, bitwise “or” performs union, etc. Pascal was first implemented on a CDC computer with 60-bit words, allowing sets over any type having up to 60 values. 

[Świerczkowski](https://doi.org/10.4064/DM422-0-1) gives
a first-order theory for HF having a constant 0 (the empty set), a binary
operation symbol $\lhd$ (augmentation, or ``eats''),
a relation symbol $\in$ (membership) as well as equality, satisfying
the following axioms:
$$
\begin{gather}
z=0 \iff \forall x\, (x\not\in z) \\
z=x\lhd y \iff \forall u\, (u\in z\iff u\in x\lor u=y) \\
\phi(0) \land \forall xy\, [\phi(x)\land\phi(y)\to\phi(x\lhd y)]\to \forall x\,\phi(x) 
\end{gather}
$$

Note that $x\lhd y$ inserts a new element $y$ into the set $x$.
The induction principle may seem a bit quirky.

### Uses for the HF sets

What’s cool about the hereditarily finite sets? They are rich enough to support many familiar constructions: the Cartesian product of two sets, the disjoint sum, function spaces (between finite sets of course), power sets and even quotient constructions. The latter may seem doubtful, since equivalence classes are often infinite, but since the HF sets have a (constructive!) wellordering, canonical representatives can be chosen. The upshot is that the HF sets are perfect for representing the results of computations: natural numbers, integers, rationals and finite data structures over them, but not, for example, arbitrary real numbers.

There is a philosophical question: the natural numbers are almost invariably used in models of computation. They are simple, with the operations 0, +1 and -1 enough to express computations, and other data structures can be coded in terms of them. 
What then is the point of using HF, which is just a less familiar encoding medium? 
But if you are already comfortable with set theory, they are the exact same sets, just fewer of them. Consider ordered pairs: using the natural numbers, the pair $(x,y)$ might be represented by $2^x3^y$, which is no more "artificial" than the set theorist’s $\lbrace \lbrace x\rbrace , \lbrace x,y\rbrace \rbrace $. However, the set theorist can happily go on to define $A\times B$ as $\lbrace (x,y) \mid x\in A \land y\in B\rbrace $, and while something similar could be done with the natural number representation, it seems that nobody does, perhaps because they simply don’t have sets on their mind.

### Some applications of HF sets to formalisation

#### Gödel's incompleteness theorems

[Świerczkowski](https://doi.org/10.4064/DM422-0-1) used HF sets as the basis for proving Gödel's incompleteness theorems, and I [formalised his work](https://www.cl.cam.ac.uk/~lp15/papers/Formath/Goedel-logic.pdf) using Isabelle/HOL.
Sets are preferable to natural numbers because encoding ("Gödel numbering) becomes trivial. Pairing schemes based on powers of primes or the Chinese remainder theorem require nontrivial mathematics, which (for the second incompleteness theorem) has to be formalised.
Here we would be looking at a formalisation not in Isabelle/HOL's higher-order logic but in a bare-bones formal calculus defined inductively within that logic.


#### Finite automata

The HF sets are a simple route out of the strict typing paradigm that bugs some people so much. Some years ago, Christian Urban published an elegant treatment regular languages avoiding the usual approach in terms of finite automata because of the difficulty of representing state spaces using simple types. But if we use HF sets to denote the state spaces of automata, then we have no problem forming Cartesian products of state spaces when forming the product of two automata, forming the powerset of the state space when transforming a nondeterministic finite automata into a deterministic one, and so forth.

[Paper](https://arxiv.org/pdf/1505.01662.pdf) published in the proceedings of CADE-25, the 25th International Conference on Automated Deduction, 2015.

### The HF sets in Isabelle/HOL



HOL-Library [Nat_Bijection](https://isabelle.in.tum.de/library/HOL/HOL-Library/Nat_Bijection.html)

<pre class="source">
<span class="keyword1 command">definition</span> <span class="entity">set_encode</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>nat</span> set</span> <span class="main">⇒</span> nat<span>"</span>
  <span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">set_encode</span> <span class="main">=</span></span> sum</span> <span class="main">(</span><span class="main">(^)</span> <span class="numeral">2</span><span class="main">)</span><span>"</span>
</pre>


<pre class="source">
<span class="keyword1 command">definition</span> <span class="entity">set_decode</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>nat</span> <span class="main">⇒</span> nat</span> set<span>"</span>
  <span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">set_decode</span> <span class="free bound entity">x</span> <span class="main">=</span></span> <span class="main">{</span><span class="bound">n</span><span class="main">.</span> odd</span> <span class="main">(</span><span class="free bound entity">x</span> <span class="keyword1">div</span> <span class="numeral">2</span> <span class="main">^</span> <span class="bound">n</span><span class="main">)</span><span class="main">}</span><span>"</span>
</pre>

<pre class="source">
<span class="keyword1 command">typedef</span> hf <span class="main">=</span> <span class="quoted quoted"><span>"</span>UNIV <span class="main">::</span> nat set<span>"</span></span> <span class="keyword1 command">..</span>
</pre>

<pre class="source">
<span class="keyword1 command">definition</span> <span class="entity">hfset</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>hf</span> <span class="main">⇒</span> hf</span> set<span>"</span>
  <span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">hfset</span> <span class="free bound entity">a</span> <span class="main">=</span> Abs_hf</span> <span class="main">`</span> set_decode</span> <span class="main">(</span>Rep_hf <span class="free bound entity">a</span><span class="main">)</span><span>"</span>
</pre>

<pre class="source">
<span class="keyword1 command">definition</span> <span class="entity">HF</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>hf</span> set <span class="main">⇒</span> hf</span><span>"</span>
  <span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">HF</span> <span class="free bound entity">A</span> <span class="main">=</span> Abs_hf</span> <span class="main">(</span>set_encode</span> <span class="main">(</span>Rep_hf <span class="main">`</span> <span class="free bound entity">A</span><span class="main">)</span><span class="main">)</span><span>"</span>
</pre>

<pre class="source">
<span class="keyword1 command">definition</span> <span class="entity">hmem</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>hf</span> <span class="main">⇒</span> hf</span> <span class="main">⇒</span> bool<span>"</span>  <span class="main">(</span><span class="keyword2 keyword">infixl</span> <span class="quoted"><span>"</span><span class="keyword1"><span class="hidden">❙</span><strong>∈</strong></span><span>"</span></span> 50<span class="main">)</span>
  <span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">hmem</span> <span class="free bound entity">a</span> <span class="free bound entity">b</span> <span class="main">⟷</span> <span class="free bound entity">a</span> <span class="main">∈</span> hfset</span> <span class="free bound entity">b</span><span>"</span></span>
</pre>

<pre class="source">
<span class="keyword1 command">instantiation</span> hf <span class="main">::</span> <span class="quoted">zero</span>
<span class="keyword2 keyword">begin</span>
  <span class="keyword1 command">definition</span> Zero_hf_def<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">0</span> <span class="main">=</span> HF</span> <span class="main">{}</span><span>"</span></span>
  <span class="keyword1 command">instance</span> <span class="keyword1 command">..</span>
<span class="keyword2 keyword">end</span>
</pre>

<pre class="source">
<span class="keyword1 command">instantiation</span> hf <span class="main">::</span> <span class="quoted">order</span>
<span class="keyword2 keyword">begin</span>
  <span class="keyword1 command">definition</span> <span class="entity class_parameter">less_eq_hf</span> <span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free bound entity">A</span> <span class="main">≤</span> <span class="free bound entity">B</span> <span class="main">⟷</span> <span class="main">(</span><span class="main">∀</span><span class="bound">x</span><span class="main">.</span> <span class="bound">x</span> <span class="main"><span class="hidden">❙</span><strong>∈</strong></span></span> <span class="free bound entity">A</span> <span class="main">⟶</span> <span class="bound">x</span> <span class="main"><span class="hidden">❙</span><strong>∈</strong></span></span> <span class="free bound entity">B</span><span class="main">)</span><span>"</span>
  <span class="keyword1 command">definition</span> <span class="entity class_parameter">less_hf</span>    <span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free bound entity">A</span> <span class="main">&lt;</span> <span class="free bound entity">B</span> <span class="main">⟷</span> <span class="free bound entity">A</span> <span class="main">≤</span> <span class="free bound entity">B</span> <span class="main">∧</span> <span class="free bound entity">A</span> <span class="main">≠</span> <span class="main">(</span><span class="free bound entity">B</span><span class="main">::</span>hf</span><span class="main">)</span><span>"</span></span>
  <span class="keyword1 command">instance</span> <span class="keyword1 command">by</span> <span class="operator">standard</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> less_eq_hf_def less_hf_def<span class="main">)</span>
<span class="keyword2 keyword">end</span>
</pre>

<pre class="source">
<span class="keyword1 command">instantiation</span> hf <span class="main">::</span> <span class="quoted">distrib_lattice</span>
<span class="keyword2 keyword">begin</span>
  <span class="keyword1 command">instance</span> <span class="keyword1 command">by</span> <span class="operator">standard</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> less_eq_hf_def less_hf_def inf_hf_def<span class="main">)</span>
<span class="keyword2 keyword">end</span>
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

Thanks for Brian Huffman for this development

AFP: https://www.isa-afp.org/entries/HereditarilyFinite.html




