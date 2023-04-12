---
layout: post
title:  "The hereditarily finite sets"
usemathjax: true 
tags: [logic, set theory, Kurt Gödel]
---

A set is *hereditarily finite* if it is finite and all of its elements are hereditarily finite. They satisfy the axioms of set theory with the negation of the axiom of infinity. There are countably many HF sets, and they are a natural domain for formalising computation. They also allow a straightforward treatment of Gödel's incompleteness theorems.

### Introduction to the HF sets

The inductive conception of HF sets, given above, justifies the recursive definition $f(x)=\sum\, \lbrace 2^{f(y)}\mid y\in x\rbrace $, yielding a bijection $f:\text{HF}\to \mathbb{N}$  between the HF sets and the natural numbers.
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
programming language's *set types*, which provide type-safe access to the hardware bit level. A Pascal set is a bit string: bitwise “and” performs intersection, bitwise “or” performs union, etc. Pascal was first implemented on a CDC computer with 60-bit words, allowing sets over any type having up to 60 values. Okay, these are not the same thing after all!

[Świerczkowski](https://doi.org/10.4064/DM422-0-1) gives
a first-order theory for HF having a constant 0 (the empty set), a binary
operation symbol $\lhd$ (augmentation, or "eats"),
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
The induction principle may seem a bit quirky: the induction hypotheses make no distinction between the set being inserted and the set being inserted into.

### Uses for the HF sets

What’s cool about the hereditarily finite sets? They are rich enough to support many familiar constructions: the Cartesian product of two sets, the disjoint sum, function spaces (between finite sets of course), power sets and even quotient constructions. The latter may seem doubtful, since equivalence classes are often infinite, but since the HF sets have a (constructive!) wellordering, canonical representatives can be chosen. The upshot is that the HF sets are perfect for representing the results of computations: natural numbers, integers, rationals and finite data structures over them, but not, for example, arbitrary real numbers.

There is a philosophical question: the natural numbers are almost invariably used in models of computation. They are simple, with the operations 0, +1 and -1 enough to express computations, and other data structures can be coded in terms of them. 
What then is the point of using HF, which is just a less familiar encoding medium? 
But if you are already comfortable with set theory, they are the exact same sets, just fewer of them. Consider ordered pairs: using the natural numbers, the pair $(x,y)$ might be represented by $2^x3^y$, which is no more "artificial" than the set theorist’s $\lbrace \lbrace x\rbrace , \lbrace x,y\rbrace \rbrace $. However, the set theorist can happily go on to define $A\times B$ as $\lbrace (x,y) \mid x\in A \land y\in B\rbrace $, and while something similar could be done with the natural number representation, it seems that nobody does, perhaps because they simply don’t have sets on their mind.

### Some applications of HF sets to formalisation

The HF sets can be used anywhere you need a diversity of possible data structures where no single element can be seen as infinite (such as an arbitrary real number). In particular, they seem natural for programming language semantics, though nobody seems to have tried this.

#### Gödel's incompleteness theorems

[Świerczkowski](https://doi.org/10.4064/DM422-0-1) used HF sets as the basis for proving Gödel's incompleteness theorems, and I [formalised his work](https://arxiv.org/abs/2104.14260) using Isabelle/HOL.
Sets are preferable to natural numbers because encoding ("Gödel numbering") becomes trivial. Pairing schemes based on powers of primes or the Chinese remainder theorem require nontrivial mathematics, which (for the second incompleteness theorem) has to be formalised.
Here we would be looking at a formalisation not in Isabelle/HOL's higher-order logic but in a bare-bones formal calculus defined inductively within that logic.
If you think doing mathematics in a modern proof assistant is difficult, let me remark that doing mathematics in a formalised calculus is a bit like using the kind of proof assistant we had 40 years ago.

#### Finite automata

The HF sets are a simple route out of the strict typing paradigm that bugs some people so much. Some years ago, Wu, Zhang and Urban [published](https://rdcu.be/cJtCW) 
an elegant [formalisation](https://www.isa-afp.org/entries/Myhill-Nerode.html)
of regular language theory, avoiding the usual approach in terms of finite automata, because of the difficulty of representing state spaces using simple types. But if we use HF sets to denote the state spaces of automata, then we have no problem forming Cartesian products of state spaces when forming the product of two automata, forming the powerset of the state space when transforming a nondeterministic finite automata into a deterministic one, and so forth.

I [demonstrated](https://arxiv.org/pdf/1505.01662.pdf) that such results as the
Myhill-Nerode theorem could indeed by [formalised](https://www.isa-afp.org/entries/Finite_Automata_HF.html)
in the traditional manner, without any hacks to get past the type system.

### The HF sets in Isabelle/HOL

Implementing the hereditarily finite sets in Isabelle/HOL makes use of [`Nat_Bijection`](https://isabelle.in.tum.de/library/HOL/HOL-Library/Nat_Bijection.html),
a library of bijections involving the natural numbers. It illustrates many aspects of how new types can be defined.

First is the function to encode a set of natural numbers as a natural number, as a sum of powers of two. The rather concise notation below abbreviates
$\sum\, \lbrace 2^i\mid i\in I\rbrace $:
<pre class="source">
<span class="keyword1 command">definition</span> <span class="entity">set_encode</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>nat</span> set</span> <span class="main">⇒</span> nat<span>"</span>
  <span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">set_encode</span> <span class="main">=</span></span> sum</span> <span class="main">(</span><span class="main">(^)</span> <span class="numeral">2</span><span class="main">)</span><span>"</span>
</pre>

I described the inverse operation above in terms of binary notation and counting 0s from the right. It can be done more concisely in terms of integer division:

<pre class="source">
<span class="keyword1 command">definition</span> <span class="entity">set_decode</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>nat</span> <span class="main">⇒</span> nat</span> set<span>"</span>
  <span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">set_decode</span> <span class="free bound entity">x</span> <span class="main">=</span></span> <span class="main">{</span><span class="bound">n</span><span class="main">.</span> odd</span> <span class="main">(</span><span class="free bound entity">x</span> <span class="keyword1">div</span> <span class="numeral">2</span> <span class="main">^</span> <span class="bound">n</span><span class="main">)</span><span class="main">}</span><span>"</span>
</pre>

With the help of those two library functions, we can go ahead and introduce the type `hf`, of hereditarily finite sets. Note that we need the Isabelle/HOL set type here; it's essential to bear in mind the difference between "HF set" (the type we are creating) and "set", which is built in.

As a general rule, <span class="keyword1 command">typedef</span> defines a new, abstract type as a copy of a nonempty set, in this case the set of all natural numbers. Every HF set will be represented by a unique natural number.

<pre class="source">
<span class="keyword1 command">typedef</span> hf <span class="main">=</span> <span class="quoted quoted"><span>"</span>UNIV <span class="main">::</span> nat set<span>"</span></span> <span class="keyword1 command">..</span>
</pre>

The declaration above introduces two functions, `Abs_hf` and `Rep_hf` to convert to convert between the abstract type and the representing set. For example, here we use `Rep_hf` to map an element of `hf` to the Isabelle/HOL set of its elements.
The given HF set is converted to a natural number and then via `set_decode` to a finite set of natural numbers, whose image under `Abs_hf` is a set of HF sets.

<pre class="source">
<span class="keyword1 command">definition</span> <span class="entity">hfset</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>hf</span> <span class="main">⇒</span> hf</span> set<span>"</span>
  <span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">hfset</span> <span class="free bound entity">a</span> <span class="main">=</span> Abs_hf</span> <span class="main">`</span> set_decode</span> <span class="main">(</span>Rep_hf <span class="free bound entity">a</span><span class="main">)</span><span>"</span>
</pre>

And now for the inverse of the function above. It takes a set `A` of HF sets; their image under `Rep_hf` is a set of natural numbers, which is then encoded as a single HF set. If `A` is infinite, incidentally, then `encode` will return zero, since `sum` can only handle finite summations.

<pre class="source">
<span class="keyword1 command">definition</span> <span class="entity">HF</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>hf</span> set <span class="main">⇒</span> hf</span><span>"</span>
  <span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">HF</span> <span class="free bound entity">A</span> <span class="main">=</span> Abs_hf</span> <span class="main">(</span>set_encode</span> <span class="main">(</span>Rep_hf <span class="main">`</span> <span class="free bound entity">A</span><span class="main">)</span><span class="main">)</span><span>"</span>
</pre>

Now that we can convert between an HF set and the finite set of its elements, it's trivial to define for HF the analogues of the functions on sets that we already have. Here is the example of membership (the difference between the two ∈ symbols, one bold and one not, is unfortunately invisible here):

<pre class="source">
<span class="keyword1 command">definition</span> <span class="entity">hmem</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>hf</span> <span class="main">⇒</span> hf</span> <span class="main">⇒</span> bool<span>"</span>  <span class="main">(</span><span class="keyword2 keyword">infixl</span> <span class="quoted"><span>"</span><span class="keyword1"><span class="hidden">❙</span><strong>∈</strong></span><span>"</span></span> 50<span class="main">)</span>
  <span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">hmem</span> <span class="free bound entity">a</span> <span class="free bound entity">b</span> <span class="main">⟷</span> <span class="free bound entity">a</span> <span class="main">∈</span> hfset</span> <span class="free bound entity">b</span><span>"</span></span>
</pre>

I am grateful to Brian Huffman for the material shown above.
There is much more to the [full development](https://www.isa-afp.org/entries/HereditarilyFinite.html) of HF sets.

### Type class instantiations for type <span class="source">hf</span>

Before winding up, I'd like to highlight some type class instantiations. Their purpose is simply to allow us to reuse some common symbols in a clean way.

First, we arrange that 0 will denote the empty set:

<pre class="source">
<span class="keyword1 command">instantiation</span> hf <span class="main">::</span> <span class="quoted">zero</span>
<span class="keyword2 keyword">begin</span>
  <span class="keyword1 command">definition</span> Zero_hf_def<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">0</span> <span class="main">=</span> HF</span> <span class="main">{}</span><span>"</span></span>
  <span class="keyword1 command">instance</span> <span class="keyword1 command">..</span>
<span class="keyword2 keyword">end</span>
</pre>

The standard ordering relations ($\leq$ and $<$) become available after we instantiate type `hf` to `order`, which is the type class of partial orderings. Here, they will refer to the subset relation on HF sets.

<pre class="source">
<span class="keyword1 command">instantiation</span> hf <span class="main">::</span> <span class="quoted">order</span>
<span class="keyword2 keyword">begin</span>
  <span class="keyword1 command">definition</span> <span class="entity class_parameter">less_eq_hf</span> <span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free bound entity">A</span> <span class="main">≤</span> <span class="free bound entity">B</span> <span class="main">⟷</span> <span class="main">(</span><span class="main">∀</span><span class="bound">x</span><span class="main">.</span> <span class="bound">x</span> <span class="main"><span class="hidden">❙</span><strong>∈</strong></span></span> <span class="free bound entity">A</span> <span class="main">⟶</span> <span class="bound">x</span> <span class="main"><span class="hidden">❙</span><strong>∈</strong></span></span> <span class="free bound entity">B</span><span class="main">)</span><span>"</span>
  <span class="keyword1 command">definition</span> <span class="entity class_parameter">less_hf</span>    <span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free bound entity">A</span> <span class="main">&lt;</span> <span class="free bound entity">B</span> <span class="main">⟷</span> <span class="free bound entity">A</span> <span class="main">≤</span> <span class="free bound entity">B</span> <span class="main">∧</span> <span class="free bound entity">A</span> <span class="main">≠</span> <span class="main">(</span><span class="free bound entity">B</span><span class="main">::</span>hf</span><span class="main">)</span><span>"</span></span>
  <span class="keyword1 command">instance</span> <span class="keyword1 command">by</span> <span class="operator">standard</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> less_eq_hf_def less_hf_def<span class="main">)</span>
<span class="keyword2 keyword">end</span>
</pre>

Several type instantiations later, we are able to overload the generic sup and inf operators ($\sqcup$ and $\sqcap$) to denote union and intersection and prove that they form a distributive lattice. That will make available a library of fundamental results on such lattices.

<pre class="source">
<span class="keyword1 command">instantiation</span> hf <span class="main">::</span> <span class="quoted">distrib_lattice</span>
<span class="keyword2 keyword">begin</span>
  <span class="keyword1 command">instance</span> <span class="keyword1 command">by</span> <span class="operator">standard</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> less_eq_hf_def less_hf_def inf_hf_def<span class="main">)</span>
<span class="keyword2 keyword">end</span>
</pre>

There is much, much more, including specialist material for the incompleteness theorems and a small development of finite automata.
And there's another thing: [addition and multiplication of sets](https://doi.org/10.1002/malq.200610026), extending the corresponding operations for ordinals, due to [Laurence Kirby](http://faculty.baruch.cuny.edu/lkirby/).
While looking him up, I discovered through his webpage (where PDFs of his papers are available) that he is also [a fan of hereditary finite sets.](https://rdcu.be/cJtDL)
