---
layout: post
title:  "Formalising Gödel's incompleteness theorems, I"
usemathjax: true 
tags: Isabelle/HOL, Gödel, incompleteness, nominal Isabelle
---

[Gödel's incompleteness theorems](https://plato.stanford.edu/entries/goedel-incompleteness/) state limits on formal systems. 
(1) A consistent system strong enough to express the basic properties of integer addition and multiplication must be *incomplete*: there exists a formula that is neither provable nor refutable within the system. (2) No such formal system can prove its own consistency.
The first theorem is proved by using integer arithmetic to encode logical formulas, operations on them such as substitution, and inference according to the rules of the formal system. A fixedpoint construction yields an explicit formula expressing its own unprovability.
The technical complications of the first theorem are formidable but were overcome already by [Shankar](https://doi.org/10.1017/CBO9780511569883) in the 1980s and again by John Harrison and [Russell O’Connor](https://rdcu.be/cNaig).
This post introduces [my own formalisation](https://www.cl.cam.ac.uk/~lp15/papers/Formath/Goedel-logic.pdf), using Isabelle/HOL. It also demonstrates Christian Urban's *nominal package* for formalising syntax involving variable binding,
and more generally, how to specify the syntax, semantics and proof theory of a formal system.

### Remarks about the informal proof

One difficulty with formalising incompleteness is purely technical: much of the reasoning in the proof is straightforward mathematically, but has to be carried out within the given formal calculus. We've already seen how hard it is to [prove obvious things]({% post_url 2022-01-12-Proving-the-obvious %}) in a theorem prover, despite all its automation; now imagine proving those things in a raw formal calculus, itself nothing more than a data structure formalised in a theorem prover. So here is a spoiler: such proofs were typically hundreds of lines long. I've written a [second paper](https://rdcu.be/bpgqj) that comments extensively on the length of each component of the development.

My formalisation follows a development by [Świerczkowski](https://doi.org/10.4064/DM422-0-1).
He gave a no-handwaving informal proof, a gift for anyone who might come along later to formalise it. He wrote out many details glossed over in textbooks.
He made strategic decisions to minimise the effort needed to reach even the second incompleteness theorem, which had been regarded by many as unattainable.

Świerczkowski chose to rely on the [hereditarily finite sets]({% post_url 2022-02-23-Hereditarily_Finite %}) rather than the integers as the basis for coding. Decoding $2^x3^y$ requires the fundamental theorem of arithmetic; an alternative coding option needs the Chinese remainder theorem and neither is tempting to formalise in an internalised first-order calculus. The set theoretic treatment of ordered pairs as $\\{\\{x\\},\\{x,y\\}\\}$ is infinitely simpler. 
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

Now let's see a few highlights of the [Isabelle formalisation of incompleteness](https://www.isa-afp.org/entries/Incompleteness.html).
A bit of magic (omitted here) sets up the nominal package and creates the type `name` to serve as a type of variable names.
The nominal package provide its own datatype declaration facility.
We can now declare a type for the terms of our formalism. Terms can be variables, 0 or "eats" ($A \lhd x$ for the set whose elements are those of $A$, plus $x$).

<pre class="source">
<span class="keyword1 command">nominal_datatype</span> tm <span class="main">=</span> Zero <span class="main">|</span> Var <span class="quoted">name</span> <span class="main">|</span> Eats <span class="quoted">tm</span> <span class="quoted">tm</span>
</pre>

The formulas provide a bare bones predicate calculus, able to express $x\in y$, $x=y$, $\phi\lor\psi$, $\neg \phi$ and $\exists x.\, \phi$.
The phrase <kbd><span class="keyword2 keyword">binds</span> <span class="quoted free">x</span> <span class="keyword2 keyword">in</span> f</kbd> indicates that the occurrence of `x` is binding.

<pre class="source">
<span class="keyword1 command">nominal_datatype</span> fm <span class="main">=</span><span>
    </span>Mem <span class="quoted">tm</span> <span class="quoted">tm</span>    <span class="main">(</span><span class="keyword2 keyword">infixr</span> <span class="quoted"><span>"</span><span class="keyword1 keyword1">IN</span><span>"</span></span> 150<span class="main">)</span><span>
  </span><span class="main">|</span> Eq <span class="quoted">tm</span> <span class="quoted">tm</span>     <span class="main">(</span><span class="keyword2 keyword">infixr</span> <span class="quoted"><span>"</span><span class="keyword1 keyword1">EQ</span><span>"</span></span> 150<span class="main">)</span><span>
  </span><span class="main">|</span> Disj <span class="quoted">fm</span> <span class="quoted">fm</span>   <span class="main">(</span><span class="keyword2 keyword">infixr</span> <span class="quoted"><span>"</span><span class="keyword1 keyword1">OR</span><span>"</span></span> 130<span class="main">)</span><span>
  </span><span class="main">|</span> Neg <span class="quoted">fm</span><span>
  </span><span class="main">|</span> Ex x<span class="main">::</span><span class="quoted">name</span> f<span class="main">::</span><span class="quoted">fm</span> <span class="keyword2 keyword">binds</span> <span class="quoted free">x</span> <span class="keyword2 keyword">in</span> f
</pre>

This is all we need to define the syntax of our first-order calculus. The next steps will define substitution (necessary to express the rules of inference) and the semantics.

### Defining substitution

Substitution of a term for a variable in another term is trivial. It has no effect on 0; a variable is replaced by the new term if it matches; compound terms (involving $\lhd$) are substituted recursively.
The last line proves that the function uses names legitimately.
It is the last such proof we are going to see: they become gruesome, which is the only real drawback of the nominal package.

<pre class="source">
<span class="keyword1 command">nominal_function</span> <span class="entity">subst</span> <span class="main">::</span> <span class="quoted quoted"><span>"</span>name <span class="main">⇒</span> tm <span class="main">⇒</span> tm <span class="main">⇒</span> tm<span>"</span></span><span>
  </span><span class="keyword2 keyword">where</span><span>
   </span><span class="quoted quoted"><span>"</span><span class="free">subst</span> <span class="free bound entity">i</span> <span class="free bound entity">x</span> Zero       <span class="main">=</span> Zero<span>"</span></span><span>
 </span><span class="main">|</span> <span class="quoted quoted"><span>"</span><span class="free">subst</span> <span class="free bound entity">i</span> <span class="free bound entity">x</span> <span class="main">(</span>Var <span class="free bound entity">k</span><span class="main">)</span>    <span class="main">=</span> <span class="main">(</span><span class="keyword1">if</span> <span class="free bound entity">i</span><span class="main">=</span><span class="free bound entity">k</span> <span class="keyword1">then</span> <span class="free bound entity">x</span> <span class="keyword1">else</span> Var <span class="free bound entity">k</span><span class="main">)</span><span>"</span></span><span>
 </span><span class="main">|</span> <span class="quoted quoted"><span>"</span><span class="free">subst</span> <span class="free bound entity">i</span> <span class="free bound entity">x</span> <span class="main">(</span>Eats <span class="free bound entity">t</span> <span class="free bound entity">u</span><span class="main">)</span> <span class="main">=</span> Eats <span class="main">(</span><span class="free">subst</span> <span class="free bound entity">i</span> <span class="free bound entity">x</span> <span class="free bound entity">t</span><span class="main">)</span> <span class="main">(</span><span class="free">subst</span> <span class="free bound entity">i</span> <span class="free bound entity">x</span> <span class="free bound entity">u</span><span class="main">)</span><span>"</span></span>
<span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> eqvt_def subst_graph_aux_def<span class="main">)</span> <span class="main">(</span><span class="operator">metis</span> tm.strong_exhaust<span class="main">)</span>
</pre>

Substitution over formulas is also pretty straightforward. In most cases it is simply built up recursively.
The line for the existential quantifier says in effect, ensure that the quantified variable is fresh with respect to the variable and term of the substitution, then simply substitute recursively. We can read this as an order to rename the bound variable appropriately to prevent a name clash, and we don't actually care what name is chosen.

<pre class="source">
<span class="keyword1 command">nominal_function</span>  <span class="entity">subst_fm</span> <span class="main">::</span> <span class="quoted quoted"><span>"</span>fm <span class="main">⇒</span> name <span class="main">⇒</span> tm <span class="main">⇒</span> fm<span>"</span></span> <span class="main">(</span><span class="quoted"><span>"</span>_<span class="keyword1">'(</span>_<span class="keyword1">::=</span>_<span class="keyword1">')</span><span>"</span></span> <span class="main">[</span>1000<span class="main">,</span> 0<span class="main">,</span> 0<span class="main">]</span> 200<span class="main">)</span><span>
  </span><span class="keyword2 keyword">where</span><span>
    </span>Mem<span class="main">:</span>  <span class="quoted quoted"><span>"</span><span class="main">(</span>Mem <span class="free bound entity">t</span> <span class="free bound entity">u</span><span class="main">)</span><span class="main free">(</span><span class="free bound entity">i</span><span class="main free">::=</span><span class="free bound entity">x</span><span class="main free">)</span>  <span class="main">=</span> Mem <span class="main">(</span>subst <span class="free bound entity">i</span> <span class="free bound entity">x</span> <span class="free bound entity">t</span><span class="main">)</span> <span class="main">(</span>subst <span class="free bound entity">i</span> <span class="free bound entity">x</span> <span class="free bound entity">u</span><span class="main">)</span><span>"</span></span><span>
  </span><span class="main">|</span> Eq<span class="main">:</span>   <span class="quoted quoted"><span>"</span><span class="main">(</span>Eq <span class="free bound entity">t</span> <span class="free bound entity">u</span><span class="main">)</span><span class="main free">(</span><span class="free bound entity">i</span><span class="main free">::=</span><span class="free bound entity">x</span><span class="main free">)</span>   <span class="main">=</span> Eq  <span class="main">(</span>subst <span class="free bound entity">i</span> <span class="free bound entity">x</span> <span class="free bound entity">t</span><span class="main">)</span> <span class="main">(</span>subst <span class="free bound entity">i</span> <span class="free bound entity">x</span> <span class="free bound entity">u</span><span class="main">)</span><span>"</span></span><span>
  </span><span class="main">|</span> Disj<span class="main">:</span> <span class="quoted quoted"><span>"</span><span class="main">(</span>Disj <span class="free bound entity">A</span> <span class="free bound entity">B</span><span class="main">)</span><span class="main free">(</span><span class="free bound entity">i</span><span class="main free">::=</span><span class="free bound entity">x</span><span class="main free">)</span> <span class="main">=</span> Disj <span class="main">(</span><span class="free bound entity">A</span><span class="main free">(</span><span class="free bound entity">i</span><span class="main free">::=</span><span class="free bound entity">x</span><span class="main free">)</span><span class="main">)</span> <span class="main">(</span><span class="free bound entity">B</span><span class="main free">(</span><span class="free bound entity">i</span><span class="main free">::=</span><span class="free bound entity">x</span><span class="main free">)</span><span class="main">)</span><span>"</span></span><span>
  </span><span class="main">|</span> Neg<span class="main">:</span>  <span class="quoted quoted"><span>"</span><span class="main">(</span>Neg <span class="free bound entity">A</span><span class="main">)</span><span class="main free">(</span><span class="free bound entity">i</span><span class="main free">::=</span><span class="free bound entity">x</span><span class="main free">)</span>    <span class="main">=</span> Neg  <span class="main">(</span><span class="free bound entity">A</span><span class="main free">(</span><span class="free bound entity">i</span><span class="main free">::=</span><span class="free bound entity">x</span><span class="main free">)</span><span class="main">)</span><span>"</span></span><span>
  </span><span class="main">|</span> Ex<span class="main">:</span>   <span class="quoted quoted"><span>"</span>atom <span class="free bound entity">j</span> <span class="main">♯</span> <span class="main">(</span><span class="free bound entity">i</span><span class="main">,</span> <span class="free bound entity">x</span><span class="main">)</span> <span class="main">⟹</span> <span class="main">(</span>Ex <span class="free bound entity">j</span> <span class="free bound entity">A</span><span class="main">)</span><span class="main free">(</span><span class="free bound entity">i</span><span class="main free">::=</span><span class="free bound entity">x</span><span class="main free">)</span> <span class="main">=</span> Ex <span class="free bound entity">j</span> <span class="main">(</span><span class="free bound entity">A</span><span class="main free">(</span><span class="free bound entity">i</span><span class="main free">::=</span><span class="free bound entity">x</span><span class="main free">)</span><span class="main">)</span><span>"</span></span>
</pre>

This simple lemma says that if a variable is fresh for a term (which essentially means it is not free in the term), then substitution has no effect. Its proof is one line: "induction then simplify". Note that $a\mathbin{\sharp} t$ means "$a$ is fresh for $t$.

<pre class="source">
<span class="keyword1 command">lemma</span> forget_subst_tm <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted quoted"><span>"</span>atom <span class="free">a</span> <span class="main">♯</span> <span class="free">tm</span> <span class="main">⟹</span> subst <span class="free">a</span> <span class="free">x</span> <span class="free">tm</span> <span class="main">=</span> <span class="free">tm</span><span>"</span></span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">induct</span> <span class="quoted free">tm</span> <span class="quasi_keyword">rule</span><span class="main main">:</span> tm.induct<span class="main">)</span> <span class="main">(</span><span class="operator">simp_all</span> <span class="quasi_keyword">add</span><span class="main main">:</span> fresh_at_base<span class="main">)</span>
</pre>

This little lemma states that two successive substitutions within a formula are equivalent to a single substitution on the formula, the other substitution taking place in the term. The proof is another one-line induction, where the "avoiding" clause informs the nominal package of the syntactic entities that quantified bound variables must avoid. This sort of proof can be absolutely fiendish with other approaches to variable binding. Nominal requires some effort to justify a function definition, but in return it makes reasoning about the function really easy.

<pre class="source">
<span class="keyword1 command">lemma</span> subst_fm_commute<span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span><span>
  </span><span class="quoted quoted"><span>"</span>atom <span class="free">j</span> <span class="main">♯</span> <span class="free">A</span> <span class="main">⟹</span> <span class="main">(</span><span class="free">A</span><span class="main">(</span><span class="free">i</span><span class="main">::=</span><span class="free">t</span><span class="main">)</span><span class="main">)</span><span class="main">(</span><span class="free">j</span><span class="main">::=</span><span class="free">u</span><span class="main">)</span> <span class="main">=</span> <span class="free">A</span><span class="main">(</span><span class="free">i</span> <span class="main">::=</span> subst <span class="free">j</span> <span class="free">u</span> <span class="free">t</span><span class="main">)</span><span>"</span></span>
  <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">nominal_induct <span class="quoted free">A</span> <span class="quasi_keyword">avoiding</span><span class="main main">:</span> <span class="quoted free">i</span> <span class="quoted free">j</span> <span class="quoted free">t</span> <span class="quoted free">u</span> <span class="quasi_keyword">rule</span><span class="main main">:</span> fm.strong_induct<span class="main">)</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> fresh_at_base<span class="main">)</span></span>
</pre>

### Formal semantics of the calculus

The formal semantics is defined in terms of the existing development of hereditarily finite sets.
Variables are interpreted with respect to an environment, a [finite function](http://www.andreas-lochbihler.de/pub/lochbihler09tphols.pdf) mapping names to `hf` sets.
The corresponding [AFP entry](https://www.isa-afp.org/entries/FinFun.html) is among the most heavily used in the entire Archive.

As before, the definition for terms has a trivial justification (omitted anyway).
The semantics of a term map the HF constructors (Zero and Eats) to the corresponding operators, while the meaning of a variable is looked up in the environment.

<pre class="source">
<span class="keyword1 command">nominal_function</span> <span class="entity">eval_tm</span> <span class="main">::</span> <span class="quoted quoted"><span>"</span><span class="main">(</span>name<span class="main">,</span> hf<span class="main">)</span> finfun <span class="main">⇒</span> tm <span class="main">⇒</span> hf<span>"</span></span><span>
  </span><span class="keyword2 keyword">where</span><span>
   </span><span class="quoted quoted"><span>"</span><span class="free">eval_tm</span> <span class="free bound entity">e</span> Zero <span class="main">=</span> <span class="main">0</span><span>"</span></span><span>
 </span><span class="main">|</span> <span class="quoted quoted"><span>"</span><span class="free">eval_tm</span> <span class="free bound entity">e</span> <span class="main">(</span>Var <span class="free bound entity">k</span><span class="main">)</span> <span class="main">=</span> finfun_apply <span class="free bound entity">e</span> <span class="free bound entity">k</span><span>"</span></span><span>
 </span><span class="main">|</span> <span class="quoted quoted"><span>"</span><span class="free">eval_tm</span> <span class="free bound entity">e</span> <span class="main">(</span>Eats <span class="free bound entity">t</span> <span class="free bound entity">u</span><span class="main">)</span> <span class="main">=</span> <span class="free">eval_tm</span> <span class="free bound entity">e</span> <span class="free bound entity">t</span> <span class="main">◃</span> <span class="free">eval_tm</span> <span class="free bound entity">e</span> <span class="free bound entity">u</span><span>"</span></span>
</pre>

A bit of omitted magic allows us to write the semantics of a term as
<span class="main">⟦</span><span class="free bound entity">t</span><span class="main">⟧</span><span class="free bound entity">e</span> 
instead of 
<span class="free">eval_tm</span> <span class="free bound entity">e</span> <span class="free bound entity">t</span>.
Now for formulas:
given an environment, the semantics of the formula of our calculus is a Boolean. It is a standard [Tarski truth definition](https://plato.stanford.edu/entries/tarski-truth/), in effect an embedding of our calculus into higher-order logic.

<pre class="source">
<span class="keyword1 command">nominal_function</span> <span class="entity">eval_fm</span> <span class="main">::</span> <span class="quoted quoted"><span>"</span><span class="main">(</span>name<span class="main">,</span> hf<span class="main">)</span> finfun <span class="main">⇒</span> fm <span class="main">⇒</span> bool<span>"</span></span><span>
  </span><span class="keyword2 keyword">where</span><span>
   </span><span class="quoted quoted"><span>"</span><span class="free">eval_fm</span> <span class="free bound entity">e</span> <span class="main">(</span><span class="free bound entity">t</span> <span class="keyword1">IN</span> <span class="free bound entity">u</span><span class="main">)</span> <span class="main">⟷</span> <span class="main">⟦</span><span class="free bound entity">t</span><span class="main">⟧</span><span class="free bound entity">e</span> <span class="main"><span class="hidden">❙</span><strong>∈</strong></span> <span class="main">⟦</span><span class="free bound entity">u</span><span class="main">⟧</span><span class="free bound entity">e</span><span>"</span></span><span>
 </span><span class="main">|</span> <span class="quoted quoted"><span>"</span><span class="free">eval_fm</span> <span class="free bound entity">e</span> <span class="main">(</span><span class="free bound entity">t</span> <span class="keyword1">EQ</span> <span class="free bound entity">u</span><span class="main">)</span> <span class="main">⟷</span> <span class="main">⟦</span><span class="free bound entity">t</span><span class="main">⟧</span><span class="free bound entity">e</span> <span class="main">=</span> <span class="main">⟦</span><span class="free bound entity">u</span><span class="main">⟧</span><span class="free bound entity">e</span><span>"</span></span><span>
 </span><span class="main">|</span> <span class="quoted quoted"><span>"</span><span class="free">eval_fm</span> <span class="free bound entity">e</span> <span class="main">(</span><span class="free bound entity">A</span> <span class="keyword1">OR</span> <span class="free bound entity">B</span><span class="main">)</span> <span class="main">⟷</span> <span class="free">eval_fm</span> <span class="free bound entity">e</span> <span class="free bound entity">A</span> <span class="main">∨</span> <span class="free">eval_fm</span> <span class="free bound entity">e</span> <span class="free bound entity">B</span><span>"</span></span><span>
 </span><span class="main">|</span> <span class="quoted quoted"><span>"</span><span class="free">eval_fm</span> <span class="free bound entity">e</span> <span class="main">(</span>Neg <span class="free bound entity">A</span><span class="main">)</span> <span class="main">⟷</span> <span class="main">(</span><span class="main">~</span> <span class="free">eval_fm</span> <span class="free bound entity">e</span> <span class="free bound entity">A</span><span class="main">)</span><span>"</span></span><span>
 </span><span class="main">|</span> <span class="quoted quoted"><span>"</span>atom <span class="free bound entity">k</span> <span class="main">♯</span> <span class="free bound entity">e</span> <span class="main">⟹</span> <span class="free">eval_fm</span> <span class="free bound entity">e</span> <span class="main">(</span>Ex <span class="free bound entity">k</span> <span class="free bound entity">A</span><span class="main">)</span> <span class="main">⟷</span> <span class="main">(</span><span class="main">∃</span><span class="bound">x</span><span class="main">.</span> <span class="free">eval_fm</span> <span class="main">(</span>finfun_update <span class="free bound entity">e</span> <span class="free bound entity">k</span> <span class="bound">x</span><span class="main">)</span> <span class="free bound entity">A</span><span class="main">)</span><span>"</span></span>
</pre>

Omitted once again is an ugly proof that the function definition is legitimate.
The only difficult case refers to the last line above, which the semantics of a quantified formula *provided* the bound variable is fresh in the environment.
It is straightforward to prove that the last line in fact holds unconditionally.

Now for some proofs. And once again, proofs about the functions just defined are simple. This one says that the semantics of a term `t` is unaffected if we update the environment at a variable that is fresh for `t`.

<pre class="source">
<span class="keyword1 command">lemma</span> forget_eval_tm <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted quoted"><span>"</span>atom <span class="free">i</span> <span class="main">♯</span> <span class="free">t</span> <span class="main">⟹</span>  <span class="main">⟦</span><span class="free">t</span><span class="main">⟧</span><span class="main">(</span>finfun_update <span class="free">e</span> <span class="free">i</span> <span class="free">x</span><span class="main">)</span> <span class="main">=</span> <span class="main">⟦</span><span class="free">t</span><span class="main">⟧</span><span class="free">e</span><span>"</span></span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">induct</span> <span class="quoted free">t</span> <span class="quasi_keyword">rule</span><span class="main main">:</span> tm.induct<span class="main">)</span> <span class="main">(</span><span class="operator">simp_all</span> <span class="quasi_keyword">add</span><span class="main main">:</span> fresh_at_base<span class="main">)</span>
</pre>

This lemma is the analogous result for formulas. The proof is once again "induction, then simplify".

<pre class="source">
<span class="keyword1 command">lemma</span> forget_eval_fm <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span><span>
   </span><span class="quoted quoted"><span>"</span>atom <span class="free">k</span> <span class="main">♯</span> <span class="free">A</span> <span class="main">⟹</span> eval_fm <span class="main">(</span>finfun_update <span class="free">e</span> <span class="free">k</span> <span class="free">x</span><span class="main">)</span> <span class="free">A</span> <span class="main">=</span> eval_fm <span class="free">e</span> <span class="free">A</span><span>"</span></span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">nominal_induct <span class="quoted free">A</span> <span class="quasi_keyword">avoiding</span><span class="main main">:</span> <span class="quoted free">k</span> <span class="quoted free">e</span> <span class="quasi_keyword">rule</span><span class="main main">:</span> fm.strong_induct<span class="main">)</span><span>
     </span><span class="main">(</span><span class="operator">simp_all</span> <span class="quasi_keyword">add</span><span class="main main">:</span> fresh_at_base finfun_update_twist<span class="main">)</span></span>
</pre>

The following two lemmas relate syntax with semantics: the effect of syntactic substitution is identical to that of updating the environment with the semantics of the substituted term.

<pre class="source">
<span class="keyword1 command">lemma</span> eval_subst_tm</span><span class="main">:</span> <span class="quoted quoted"><span>"</span><span class="main">⟦</span>subst <span class="free">i</span> <span class="free">t</span> <span class="free">u</span><span class="main">⟧</span><span class="free">e</span> <span class="main">=</span> <span class="main">⟦</span><span class="free">u</span><span class="main">⟧</span><span class="main">(</span>finfun_update <span class="free">e</span> <span class="free">i</span> <span class="main">⟦</span><span class="free">t</span><span class="main">⟧</span><span class="free">e</span><span class="main">)</span><span>"</span></span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">induct</span> <span class="quoted free">u</span> <span class="quasi_keyword">rule</span><span class="main main">:</span> tm.induct<span class="main">)</span> <span class="main">(</span><span class="operator">auto</span><span class="main">)</span>
</pre>

And the same thing for formulas.

<pre class="source">
<span class="keyword1 command">lemma</span> eval_subst_fm<span class="main">:</span> <span class="quoted quoted"><span>"</span>eval_fm <span class="free">e</span> <span class="main">(</span><span class="free">fm</span><span class="main">(</span><span class="free">i</span><span class="main">::=</span> <span class="free">t</span><span class="main">)</span><span class="main">)</span> <span class="main">=</span> eval_fm <span class="main">(</span>finfun_update <span class="free">e</span> <span class="free">i</span> <span class="main">⟦</span><span class="free">t</span><span class="main">⟧</span><span class="free">e</span><span class="main">)</span> <span class="free">fm</span><span>"</span></span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">nominal_induct <span class="quoted free">fm</span> <span class="quasi_keyword">avoiding</span><span class="main main">:</span> <span class="quoted free">i</span> <span class="quoted free">t</span> <span class="quoted free">e</span> <span class="quasi_keyword">rule</span><span class="main main">:</span> fm.strong_induct<span class="main">)</span><span>
     </span><span class="main">(</span><span class="operator">simp_all</span> <span class="quasi_keyword">add</span><span class="main main">:</span> eval_subst_tm finfun_update_twist fresh_at_base<span class="main">)</span></span>
</pre>

Nobody should imagine that such simple proofs could be possible in any approach based on naïve variable names.

### The inference system

The internal calculus is defined by a Hilbert system. Our formulas have only disjunctions, negations and existential quantifiers, so the missing connectives such as conjunctions and universal quantifiers must be defined in the obvious way. 
For Boolean logic, the proof system incorporates the following fairly arbitrary set of axiom schemes.
Formally this is an inductive definition, although there is no recursion, simply because it is easy to write and work with.

<pre class="source">
<span class="keyword1 command">inductive_set</span> <span class="entity">boolean_axioms</span> <span class="main">::</span> <span class="quoted quoted"><span>"</span>fm set<span>"</span></span><span>
  </span><span class="keyword2 keyword">where</span><span>
    </span>Ident<span class="main">:</span>     <span class="quoted quoted"><span>"</span><span class="free bound entity">A</span> <span class="keyword1">IMP</span> <span class="free bound entity">A</span> <span class="main">∈</span> <span class="free">boolean_axioms</span><span>"</span></span><span>
  </span><span class="main">|</span> DisjI1<span class="main">:</span>    <span class="quoted quoted"><span>"</span><span class="free bound entity">A</span> <span class="keyword1">IMP</span> <span class="main">(</span><span class="free bound entity">A</span> <span class="keyword1">OR</span> <span class="free bound entity">B</span><span class="main">)</span> <span class="main">∈</span> <span class="free">boolean_axioms</span><span>"</span></span><span>
  </span><span class="main">|</span> DisjCont<span class="main">:</span>  <span class="quoted quoted"><span>"</span><span class="main">(</span><span class="free bound entity">A</span> <span class="keyword1">OR</span> <span class="free bound entity">A</span><span class="main">)</span> <span class="keyword1">IMP</span> <span class="free bound entity">A</span> <span class="main">∈</span> <span class="free">boolean_axioms</span><span>"</span></span><span>
  </span><span class="main">|</span> DisjAssoc<span class="main">:</span> <span class="quoted quoted"><span>"</span><span class="main">(</span><span class="free bound entity">A</span> <span class="keyword1">OR</span> <span class="main">(</span><span class="free bound entity">B</span> <span class="keyword1">OR</span> <span class="free bound entity">C</span><span class="main">)</span><span class="main">)</span> <span class="keyword1">IMP</span> <span class="main">(</span><span class="main">(</span><span class="free bound entity">A</span> <span class="keyword1">OR</span> <span class="free bound entity">B</span><span class="main">)</span> <span class="keyword1">OR</span> <span class="free bound entity">C</span><span class="main">)</span> <span class="main">∈</span> <span class="free">boolean_axioms</span><span>"</span></span><span>
  </span><span class="main">|</span> DisjConj<span class="main">:</span>  <span class="quoted quoted"><span>"</span><span class="main">(</span><span class="free bound entity">C</span> <span class="keyword1">OR</span> <span class="free bound entity">A</span><span class="main">)</span> <span class="keyword1">IMP</span> <span class="main">(</span><span class="main">(</span><span class="main">(</span>Neg <span class="free bound entity">C</span><span class="main">)</span> <span class="keyword1">OR</span> <span class="free bound entity">B</span><span class="main">)</span> <span class="keyword1">IMP</span> <span class="main">(</span><span class="free bound entity">A</span> <span class="keyword1">OR</span> <span class="free bound entity">B</span><span class="main">)</span><span class="main">)</span> <span class="main">∈</span> <span class="free">boolean_axioms</span><span>"</span></span>
</pre>

The scheme of "special axioms" defines existential quantification. 
In standard notation, these axioms have the form $\phi(t)\to \exists x.\,\phi(x)$, where $t$ is any term.

<pre class="source">
<span class="keyword1 command">inductive_set</span> <span class="entity">special_axioms</span> <span class="main">::</span> <span class="quoted quoted"><span>"</span>fm set<span>"</span></span> <span class="keyword2 keyword">where</span><span>
  </span>I<span class="main">:</span> <span class="quoted quoted"><span>"</span><span class="free bound entity">A</span><span class="main">(</span><span class="free bound entity">i</span><span class="main">::=</span><span class="free bound entity">x</span><span class="main">)</span> <span class="keyword1">IMP</span> <span class="main">(</span>Ex <span class="free bound entity">i</span> <span class="free bound entity">A</span><span class="main">)</span> <span class="main">∈</span> <span class="free">special_axioms</span><span>"</span></span>
</pre>

The induction axioms include every instance of the induction scheme for HF sets.
In standard notation, these axioms have the form
$\phi(0) \land \forall xy\, [\phi(x)\land\phi(y)\to\phi(x\lhd y)]\to \forall x\,\phi(x)$.

<pre class="source">
<span class="keyword1 command">inductive_set</span> <span class="entity">induction_axioms</span> <span class="main">::</span> <span class="quoted quoted"><span>"</span>fm set<span>"</span></span> <span class="keyword2 keyword">where</span><span>
  </span>ind<span class="main">:</span><span>
  </span><span class="quoted quoted"><span>"</span>atom <span class="main">(</span><span class="free bound entity">j</span><span class="main">::</span>name<span class="main">)</span> <span class="main">♯</span> <span class="main">(</span><span class="free bound entity">i</span><span class="main">,</span><span class="free bound entity">A</span><span class="main">)</span><span>
   </span><span class="main">⟹</span> <span class="free bound entity">A</span><span class="main">(</span><span class="free bound entity">i</span><span class="main">::=</span>Zero<span class="main">)</span> <span class="keyword1">IMP</span> <span class="main">(</span><span class="main">(</span>All <span class="free bound entity">i</span> <span class="main">(</span>All <span class="free bound entity">j</span> <span class="main">(</span><span class="free bound entity">A</span> <span class="keyword1">IMP</span> <span class="main">(</span><span class="free bound entity">A</span><span class="main">(</span><span class="free bound entity">i</span><span class="main">::=</span> Var <span class="free bound entity">j</span><span class="main">)</span> <span class="keyword1">IMP</span> <span class="free bound entity">A</span><span class="main">(</span><span class="free bound entity">i</span><span class="main">::=</span> Eats<span class="main">(</span>Var <span class="free bound entity">i</span><span class="main">)</span><span class="main">(</span>Var <span class="free bound entity">j</span><span class="main">)</span><span class="main">)</span><span class="main">)</span><span class="main">)</span><span class="main">)</span><span class="main">)</span><span>
      </span><span class="keyword1">IMP</span> <span class="main">(</span>All <span class="free bound entity">i</span> <span class="free bound entity">A</span><span class="main">)</span><span class="main">)</span><span>
    </span><span class="main">∈</span> <span class="free">induction_axioms</span><span>"</span></span>
</pre>

Further axioms (omitted) describe the properties of the HF operators `Zero` and `Eats`; there are also some standard equality axioms. Finally, there's an unspecified **extra axiom**, standing for any else finite statement we wish to assume. The extra axiom is required to be true in the semantics, and all the other axioms are proved to hold, so this proof calculus will be consistent by construction. 

We are finally ready to behold the inference system itself.
Because it is a Hilbert system, $\Gamma\vdash\phi$ means that $\phi$ follows from the given set of assumptions, $\Gamma$.
The first line is the trivial inclusion and the next six lines state that the various axioms are theorems.

<pre class="source">
<span class="keyword1 command">inductive</span> <span class="entity">hfthm</span> <span class="main">::</span> <span class="quoted quoted"><span>"</span>fm set <span class="main">⇒</span> fm <span class="main">⇒</span> bool<span>"</span></span> <span class="main">(</span><span class="keyword2 keyword">infixl</span> <span class="quoted"><span>"</span><span class="keyword1">⊢</span><span>"</span></span> 55<span class="main">)</span><span>
  </span><span class="keyword2 keyword">where</span><span>
    </span>Hyp<span class="main">:</span>    <span class="quoted quoted"><span>"</span><span class="free bound entity">A</span> <span class="main">∈</span> <span class="free bound entity">H</span> <span class="main">⟹</span> <span class="free bound entity">H</span> <span class="main free">⊢</span> <span class="free bound entity">A</span><span>"</span></span><span>
  </span><span class="main">|</span> Extra<span class="main">:</span>  <span class="quoted quoted"><span>"</span><span class="free bound entity">H</span> <span class="main free">⊢</span> extra_axiom<span>"</span></span><span>
  </span><span class="main">|</span> Bool<span class="main">:</span>   <span class="quoted quoted"><span>"</span><span class="free bound entity">A</span> <span class="main">∈</span> boolean_axioms <span class="main">⟹</span> <span class="free bound entity">H</span> <span class="main free">⊢</span> <span class="free bound entity">A</span><span>"</span></span><span>
  </span><span class="main">|</span> Eq<span class="main">:</span>     <span class="quoted quoted"><span>"</span><span class="free bound entity">A</span> <span class="main">∈</span> equality_axioms <span class="main">⟹</span> <span class="free bound entity">H</span> <span class="main free">⊢</span> <span class="free bound entity">A</span><span>"</span></span><span>
  </span><span class="main">|</span> Spec<span class="main">:</span>   <span class="quoted quoted"><span>"</span><span class="free bound entity">A</span> <span class="main">∈</span> special_axioms <span class="main">⟹</span> <span class="free bound entity">H</span> <span class="main free">⊢</span> <span class="free bound entity">A</span><span>"</span></span><span>
  </span><span class="main">|</span> HF<span class="main">:</span>     <span class="quoted quoted"><span>"</span><span class="free bound entity">A</span> <span class="main">∈</span> HF_axioms <span class="main">⟹</span> <span class="free bound entity">H</span> <span class="main free">⊢</span> <span class="free bound entity">A</span><span>"</span></span><span>
  </span><span class="main">|</span> Ind<span class="main">:</span>    <span class="quoted quoted"><span>"</span><span class="free bound entity">A</span> <span class="main">∈</span> induction_axioms <span class="main">⟹</span> <span class="free bound entity">H</span> <span class="main free">⊢</span> <span class="free bound entity">A</span><span>"</span></span><span>
  </span><span class="main">|</span> MP<span class="main">:</span>     <span class="quoted quoted"><span>"</span><span class="free bound entity">H</span> <span class="main free">⊢</span> <span class="free bound entity">A</span> <span class="keyword1">IMP</span> <span class="free bound entity">B</span> <span class="main">⟹</span> <span class="free bound entity">H'</span> <span class="main free">⊢</span> <span class="free bound entity">A</span> <span class="main">⟹</span> <span class="free bound entity">H</span> <span class="main">∪</span> <span class="free bound entity">H'</span> <span class="main free">⊢</span> <span class="free bound entity">B</span><span>"</span></span><span>
  </span><span class="main">|</span> Exists<span class="main">:</span> <span class="quoted quoted"><span>"</span><span class="free bound entity">H</span> <span class="main free">⊢</span> <span class="free bound entity">A</span> <span class="keyword1">IMP</span> <span class="free bound entity">B</span> <span class="main">⟹</span> atom <span class="free bound entity">i</span> <span class="main">♯</span> <span class="free bound entity">B</span> <span class="main">⟹</span> <span class="main">∀</span><span class="bound">C</span> <span class="main">∈</span> <span class="free bound entity">H</span><span class="main">.</span> atom <span class="free bound entity">i</span> <span class="main">♯</span> <span class="bound">C</span> <span class="main">⟹</span> <span class="free bound entity">H</span> <span class="main free">⊢</span> <span class="main">(</span>Ex <span class="free bound entity">i</span> <span class="free bound entity">A</span><span class="main">)</span> <span class="keyword1">IMP</span> <span class="free bound entity">B</span><span>"</span></span>
</pre>

The last two lines above are inference rules: 
1. modus ponens: from $\phi\to\psi$ and $\phi$ infer $\psi$
2. so-called $\exists$-introduction: from $\phi\to\psi$ infer $(\exists x.\,\phi)\to\psi$ provided $x$ is fresh


<pre class="source">
<span class="keyword1 command">theorem</span> hfthm_sound<span class="main">:</span> <span class="keyword2 keyword">assumes</span> <span class="quoted quoted"><span>"</span><span class="free">H</span> <span class="main">⊢</span> <span class="free">A</span><span>"</span></span> <span class="keyword2 keyword">shows</span> <span class="quoted quoted"><span>"</span><span class="main">(</span><span class="main">∀</span><span class="bound">B</span><span class="main">∈</span><span class="free">H</span><span class="main">.</span> eval_fm <span class="free">e</span> <span class="bound">B</span><span class="main">)</span> <span class="main">⟹</span> eval_fm <span class="free">e</span> <span class="free">A</span><span>"</span></span><span>
</span><span class="keyword1 command">using</span> assms<span>
</span><span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">induct</span> <span class="quasi_keyword">arbitrary</span><span class="main main">:</span> <span class="quoted free">e</span><span class="main">)</span><span>
  </span><span class="keyword3 command">case</span> <span class="main">(</span>Hyp <span class="skolem">A</span> <span class="skolem">H</span><span class="main">)</span> <span class="keyword3 command">thus</span> <span class="var quoted var">?case</span><span>
    </span><span class="keyword1 command">by</span> <span class="operator">auto</span><span>
</span><span class="keyword1 command">next</span><span>
  </span><span class="keyword3 command">case</span> <span class="main">(</span>Extra <span class="skolem">H</span><span class="main">)</span> <span class="keyword3 command">thus</span> <span class="var quoted var">?case</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> extra_axiom_holds<span class="main">)</span><span>
</span><span class="keyword1 command">next</span><span>
  </span><span class="keyword3 command">case</span> <span class="main">(</span>Bool <span class="skolem">A</span> <span class="skolem">H</span><span class="main">)</span> <span class="keyword3 command">thus</span> <span class="var quoted var">?case</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> boolean_axioms_hold<span class="main">)</span><span>
</span><span class="keyword1 command">next</span><span>
  </span><span class="keyword3 command">case</span> <span class="main">(</span>Eq <span class="skolem">A</span> <span class="skolem">H</span><span class="main">)</span> <span class="keyword3 command">thus</span> <span class="var quoted var">?case</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> equality_axioms_hold<span class="main">)</span><span>
</span><span class="keyword1 command">next</span><span>
  </span><span class="keyword3 command">case</span> <span class="main">(</span>Spec <span class="skolem">A</span> <span class="skolem">H</span><span class="main">)</span> <span class="keyword3 command">thus</span> <span class="var quoted var">?case</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> special_axioms_hold<span class="main">)</span><span>
</span><span class="keyword1 command">next</span><span>
  </span><span class="keyword3 command">case</span> <span class="main">(</span>HF <span class="skolem">A</span> <span class="skolem">H</span><span class="main">)</span> <span class="keyword3 command">thus</span> <span class="var quoted var">?case</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> HF_axioms_hold<span class="main">)</span><span>
</span><span class="keyword1 command">next</span><span>
  </span><span class="keyword3 command">case</span> <span class="main">(</span>Ind <span class="skolem">A</span> <span class="skolem">H</span><span class="main">)</span> <span class="keyword3 command">thus</span> <span class="var quoted var">?case</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> induction_axioms_hold<span class="main">)</span><span>
</span><span class="keyword1 command">next</span><span>
  </span><span class="keyword3 command">case</span> <span class="main">(</span>MP <span class="skolem">H</span> <span class="skolem">A</span> <span class="skolem">B</span> <span class="skolem">H'</span><span class="main">)</span> <span class="keyword3 command">thus</span> <span class="var quoted var">?case</span><span>
    </span><span class="keyword1 command">by</span> <span class="operator">auto</span><span>
</span><span class="keyword1 command">next</span><span>
  </span><span class="keyword3 command">case</span> <span class="main">(</span>Exists <span class="skolem">H</span> <span class="skolem">A</span> <span class="skolem">B</span> <span class="skolem">i</span> <span class="skolem">e</span><span class="main">)</span> <span class="keyword3 command">thus</span> <span class="var quoted var">?case</span><span>
    </span><span class="keyword1 command">by</span> <span class="operator">auto</span> <span class="main">(</span><span class="operator">metis</span> forget_eval_fm<span class="main">)</span><span>
</span><span class="keyword1 command">qed</span>
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
But I can't resist remarking that a lot of today's work on type theory looks like Hilbert's Programme Reloaded: people are striving to create a formal system in which all mathematics can be done and to prove its consistency syntactically. Gödel's theorem tells us that any such theory will be incomplete, but that's not even the main problem with an outlook that seems to be absolutely mechanical.
We formalise mathematics in the hope that it can be useful to mathematicians, but please let's forego fantasies of capturing the whole of mathematical thought in a formal system.


