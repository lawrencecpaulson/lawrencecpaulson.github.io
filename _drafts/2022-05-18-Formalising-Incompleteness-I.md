---
layout: post
title:  "Formalising Gödel's incompleteness theorems, I"
usemathjax: true 
tags: Isabelle/HOL, Gödel, incompleteness, nominal Isabelle
---

[Gödel's incompleteness theorems](https://plato.stanford.edu/entries/goedel-incompleteness/) state limits on formal systems. 
(1) A consistent system strong enough to express the basic properties of integer addition and multiplication must be *incomplete*: there exists a formula that is neither provable nor refutable within the system. (2) Moreover, no such formal system can prove any statement implying its own consistency.
The first theorem is proved by using integer arithmetic to encode logical formulas, operations on them such as substitution, and inference according to the rules of the formal system. A fixedpoint construction to create an explicit formula expressing its own unprovability.
The technical complications of the first theorem are formidable but were overcome already by [Shankar](https://doi.org/10.1017/CBO9780511569883) in the 1980s and again by John Harrison and [Russell O’Connor](https://rdcu.be/cNaig).
This post will describe [my own formalisation](https://www.cl.cam.ac.uk/~lp15/papers/Formath/Goedel-logic.pdf) of the first theorem, using Isabelle/HOL.

### Remarks about the informal proof

One difficulty with formalising incompleteness is purely technical: much of the reasoning in the proof is straightforward mathematically, but has to be carried out within the given formal calculus. We've already seen how hard it is to [prove obvious things]({% post_url 2022-01-12-Proving-the-obvious %}) in a theorem prover, despite all its automation; now imagine proving those things in a raw formal calculus, itself nothing more than a data structure formalised in a theorem prover. So here is a spoiler: such proofs were typically hundreds of lines long. I've written a [second paper](https://rdcu.be/bpgqj) that comments extensively on the length of each component of the development.

My formalisation follows a development by [Świerczkowski](https://doi.org/10.4064/DM422-0-1).
He gave a no-handwaving informal proof, a gift for anyone who might come along later to formalise it. He wrote out many details glossed over in textbooks.
He made strategic decisions to minimise the effort needed to reach even the second incompleteness theorem, which had been regarded by many as unattainable.

Świerczkowski chose to rely on the hereditarily finite sets rather than the integers as the basis for coding. Decoding $2^x3^y$ requires the fundamental theorem of arithmetic; an alternative coding option needs the Chinese remainder theorem and neither is tempting to formalise in an internalised first-order calculus. The set theoretic treatment of ordered pairs as $\\{\\{x\\},\\{x,y\\}\\}$ is infinitely simpler. 
He also proved a meta-theorem stating that every true $\Sigma$ formula is provable in the calculus with no need to write out the proofs. A $\Sigma$ formula can begin with any number of existential quantifiers, and they are sufficient to express much of the logic of coding. The standard approach yields a more powerful meta-theorem (where also certain *false* formulas have explicit *disproofs*), but it only works of all quantifiers are bounded, and so actually requires more work than just writing out some formal proofs.

The stages of the proofs of the first theorem are as follows:
1. Formalisation of the internal calculus
2. Meta-theorem stating that every true $\Sigma$ formula is provable
3. Defining a coding system for the terms and formulas of the calculus
4. Defining predicates within the calculus itself to recognise terms, formulas and operations such as substitution; then inference rules and provability itself
5. Exhibiting the actual undecidable formula
 
### On the treatment of bound variables

Formal reasoning about syntax including variable binding is generally fraught with difficulties connected with substitution and variable capture. In Isabelle/HOL we are lucky to have the [nominal package](https://www.isa-afp.org/entries/Nominal2.html), created by [Christian Urban](https://rdcu.be/cNfaC) and based on theoretical work by Jamie Gabbay and Andrew Pitts. The [nominal approach](https://www.cl.cam.ac.uk/~amp12/papers/newaas/newaas-jv.pdf) to variable binding provides a calculus of permutations on variable names, and provides a smooth treatment of syntactic operations that treat bound variables appropriately (which in particular means that all results are independent of which names are chosen for the bound variables). It precisely defines the notion of a variable being fresh and gives you a means of picking fresh variables. You get to assume that variables are magically renamed whenever necessary. 

My formal development of the incompleteness theorems [uses the nominal approach](https://rdcu.be/bpgqj) in formalising the logical calculus: its syntax, syntactic operations and inference rules.
When it comes to coding formulas of the calculus, we need a different approach to variable binding, as attempting to formalise the nominal approach within the formal calculus itself is not to be imagined. Although Swierczkowski used plain variable names, I felt certain that a nameless representation would work better, and the obvious one is [de Bruijn's](https://doi.org/10.1016/1385-7258(72)90034-0) (explanation [on Wikipedia](https://en.wikipedia.org/wiki/De_Bruijn_index)).

The proof requires proving that the encoded operations carry out their intended effect. Happily, there's a simple correspondence between syntax and operations formalised using the nominal approach and their counterparts using de Bruijn indices.

### A formal logic and its Isabelle/HOL formalisation



<pre class="source">
<span class="keyword1 command">nominal_datatype</span> tm <span class="main">=</span> Zero <span class="main">|</span> Var <span class="quoted">name</span> <span class="main">|</span> Eats <span class="quoted">tm</span> <span class="quoted">tm</span>
</pre>

<pre class="source">
<span class="keyword1 command">nominal_datatype</span> fm <span class="main">=</span><span>
    </span>Mem <span class="quoted">tm</span> <span class="quoted">tm</span>    <span class="main">(</span><span class="keyword2 keyword">infixr</span> <span class="quoted"><span>"</span><span class="keyword1 keyword1">IN</span><span>"</span></span> 150<span class="main">)</span><span>
  </span><span class="main">|</span> Eq <span class="quoted">tm</span> <span class="quoted">tm</span>     <span class="main">(</span><span class="keyword2 keyword">infixr</span> <span class="quoted"><span>"</span><span class="keyword1 keyword1">EQ</span><span>"</span></span> 150<span class="main">)</span><span>
  </span><span class="main">|</span> Disj <span class="quoted">fm</span> <span class="quoted">fm</span>   <span class="main">(</span><span class="keyword2 keyword">infixr</span> <span class="quoted"><span>"</span><span class="keyword1 keyword1">OR</span><span>"</span></span> 130<span class="main">)</span><span>
  </span><span class="main">|</span> Neg <span class="quoted">fm</span><span>
  </span><span class="main">|</span> Ex x<span class="main">::</span><span class="quoted">name</span> f<span class="main">::</span><span class="quoted">fm</span> <span class="keyword2 keyword">binds</span> <span class="quoted free">x</span> <span class="keyword2 keyword">in</span> f
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
But I can't resist remarking that a lot of today's work on type theory looks like Hilbert's Programme Reloaded: people are striving to create a formal system in which all mathematics can be done and to prove its consistency syntactically. Gödel's theorem tells us that any such theory will be incomplete, but that's not even the main problem with an outlook that seems to be absolutely mechanical.
We formalise mathematics in the hope that it can be useful to mathematicians, but please let's forego fantasies of capturing the whole of mathematical thought in a formal system.


