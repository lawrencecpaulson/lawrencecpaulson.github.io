---
layout: post
title:  "Formalising Gödel's incompleteness theorems, II"
usemathjax: true
tags: Isabelle/HOL, Gödel, incompleteness, nominal Isabelle
---

Gödel's theorem, more than many other deep results, is burdened with a great many truly tiresome definitions and lemmas. It's necessary to codify in full the axioms and inference rules of HF, the [internal logic]({% post_url 2022-05-18-Formalising-Incompleteness-I %}), as well as a toolbox of derived syntactic primitives needed for expressing and proving HF statements. (It's also necessary to prove that the primitives actually work, a particularly tiresome step that most authors omit.)
Here, let's look at something a bit more interesting: [Świerczkowski's](https://doi.org/10.4064/DM422-0-1) Theorem 2.5, which states that every true Σ-sentence is a theorem.
This turns out to be vital once we set up Gödel encodings of formulas and define a provability predicate, Pf. It will be possible to show that φ is a theorem if and only if Pf⌜φ⌝ is true, for any HF formula φ. The point is that all of these syntactic predicates can be defined as Σ-formulas. Therefore, if Pf⌜φ⌝ is true, we get—for free—that Pf⌜φ⌝ is *formally* provable.
 To get started, we first need to define Σ-formulas.

### Σ-formulas and the main result, informally

Świerczkowski defines the *strict* Σ-formulas syntactically:
1. all formulas of the form $x\in y$, where $x$ and $y$ are variables
2. all formulas of the form $\phi\land\psi$ and $\phi\lor\psi$, where $\phi$ and $\psi$ are strict Σ-formulas
3. all formulas of the form $\forall x\in y.\, \phi$, where $\phi$ is a strict Σ-formula and $y$ is a variable
4. all formulas of the form $\exists x.\, \phi$, where $\phi$ is a strict Σ-formula

Now a *Σ-formula* is any formula provably equivalent in HF to a strict Σ-formula.
With a little work, it's possible to show that all atomic formulas are Σ-formulas, including those of the form $t=u$ and $t\subseteq u$. In particular, the syntactic requirements for variables in (1) and (3) above can be relaxed to any terms.

Intuitively, such formulas are positive. Negation isn't available and universal quantifiers must be bounded. However, existential quantifiers can be unbounded. This class of formulas is expressive enough to simulate recursion and thereby specify the syntactic structure of well-formed terms, formulas and proofs.

The proof of the main theorem is then by induction on the structure of a (generalised) Σ-sentence.
1. Atomic formulas can essentially be evaluated in the logic, because they have no variables.
2. If $\phi\lor\psi$ is true then either $\phi$ or $\psi$ must be true, and by the induction hypothesis, provable in HF. Therefore, $\phi\lor\psi$ itself is provable. Similarly for $\phi\land\psi$.
3. If $\forall x\in t.\, \phi$ is true then the term $t$ denotes a specific HF set and we are dealing with a conjunction.
4. If $\exists x.\, \phi(x)$ is true then $\phi(t)$ is a true Σ-sentence and therefore a theorem by the induction hypothesis. Using the value of $t$ as a witness, the conclusion follows.

Dead simple really. Let's formalise it.

###  Formalising the set of Σ-formulas

The strict Σ-formulas are defined as follows.
This definition references the formal definition of HF from the [previous post]({% post_url 2022-05-18-Formalising-Incompleteness-I %}),
as well as some derived syntactic constructions (`AND` and `All2`) that I have left to the imagination. Occurrences of the `Var` constructor agree with the original text, which permitted variables only.

<pre class="source">
<span class="keyword1 command">inductive</span> <span class="entity">ss_fm</span> <span class="main">::</span> <span class="quoted quoted"><span>"</span>fm <span class="main">⇒</span> bool<span>"</span></span> <span class="keyword2 keyword">where</span><span>
    </span>MemI<span class="main">:</span>  <span class="quoted quoted"><span>"</span><span class="free">ss_fm</span> <span class="main">(</span>Var <span class="free bound entity">i</span> <span class="keyword1">IN</span> Var <span class="free bound entity">j</span><span class="main">)</span><span>"</span></span><span>
  </span><span class="main">|</span> DisjI<span class="main">:</span> <span class="quoted quoted"><span>"</span><span class="free">ss_fm</span> <span class="free bound entity">A</span> <span class="main">⟹</span> <span class="free">ss_fm</span> <span class="free bound entity">B</span> <span class="main">⟹</span> <span class="free">ss_fm</span> <span class="main">(</span><span class="free bound entity">A</span> <span class="keyword1">OR</span> <span class="free bound entity">B</span><span class="main">)</span><span>"</span></span><span>
  </span><span class="main">|</span> ConjI<span class="main">:</span> <span class="quoted quoted"><span>"</span><span class="free">ss_fm</span> <span class="free bound entity">A</span> <span class="main">⟹</span> <span class="free">ss_fm</span> <span class="free bound entity">B</span> <span class="main">⟹</span> <span class="free">ss_fm</span> <span class="main">(</span><span class="free bound entity">A</span> <span class="keyword1">AND</span> <span class="free bound entity">B</span><span class="main">)</span><span>"</span></span><span>
  </span><span class="main">|</span> ExI<span class="main">:</span>   <span class="quoted quoted"><span>"</span><span class="free">ss_fm</span> <span class="free bound entity">A</span> <span class="main">⟹</span> <span class="free">ss_fm</span> <span class="main">(</span>Ex <span class="free bound entity">i</span> <span class="free bound entity">A</span><span class="main">)</span><span>"</span></span><span>
  </span><span class="main">|</span> All2I<span class="main">:</span> <span class="quoted quoted"><span>"</span><span class="free">ss_fm</span> <span class="free bound entity">A</span> <span class="main">⟹</span> atom <span class="free bound entity">j</span> <span class="main">♯</span> <span class="main">(</span><span class="free bound entity">i</span><span class="main">,</span><span class="free bound entity">A</span><span class="main">)</span> <span class="main">⟹</span> <span class="free">ss_fm</span> <span class="main">(</span>All2 <span class="free bound entity">i</span> <span class="main">(</span>Var <span class="free bound entity">j</span><span class="main">)</span> <span class="free bound entity">A</span><span class="main">)</span></span>
</pre>

The definition of a Σ-formula echoes Świerczkowski’s except for a technical condition involving the function `supp` (meaning "support"). The support of an entity is, roughly speaking, its set of free variables. So formally, a Σ-formula is anything provably equivalent to a strict Σ-formula containing no additional free variables.

<pre class="source">
<span class="keyword1 command">definition</span> <span class="entity">Sigma_fm</span> <span class="main">::</span> <span class="quoted quoted"><span>"</span>fm <span class="main">⇒</span> bool<span>"</span></span><span>
  </span><span class="keyword2 keyword">where</span> <span class="quoted quoted"><span>"</span><span class="free">Sigma_fm</span> <span class="free bound entity">A</span> <span class="main">⟷</span> <span class="main">(</span><span class="main">∃</span><span class="bound">B</span><span class="main">.</span> ss_fm <span class="bound">B</span> <span class="main">∧</span> supp <span class="bound">B</span> <span class="main">⊆</span> supp <span class="free bound entity">A</span> <span class="main">∧</span> <span class="main">{}</span> <span class="main">⊢</span> <span class="free bound entity">A</span> <span class="keyword1">IFF</span> <span class="bound">B</span><span class="main">)</span><span>"</span></span>
</pre>

It is straightforward to show that the Σ-formulas are closed according to the same rules as the strict Σ-formulas, and moreover `Fls` (the falsity symbol, $\bot$) is also a Σ-formula (being provably equivalent to $\exists x.\, x\in x$).

### All atomic formulas are Σ-formulas

Our next task is to demonstrate that all atomic formulas are Σ-formulas. This involves a series of fairly elementary proofs, relating various atomic formulas to strict Σ-formulas.
We begin with the terms restricted to variables and gradually strengthen the results to other terms. 
The subset relation, applied to variables, is a Σ-formula simply by its syntactic structure:
$x\subset y \leftrightarrow (\forall j\in x.\, j\in y)$.
The following is a representative example, where $x\subseteq 0 \longleftrightarrow(\forall j\in x.\, \bot)$ is proved in the HF calculus.
Another theorem handles the case $x\subseteq y\lhd z$, and on we go.

<pre class="source">
<span class="keyword1 command">lemma</span> Subset_Zero_sf<span class="main">:</span> <span class="quoted quoted"><span>"</span>Sigma_fm <span class="main">(</span>Var <span class="free">i</span> <span class="keyword1">SUBS</span> Zero<span class="main">)</span><span>"</span></span><span>
</span><span class="keyword1 command">proof</span> <span class="operator">-</span><span>
  </span><span class="keyword3 command">obtain</span> <span class="skolem skolem">j</span><span class="main">::</span><span class="quoted">name</span> <span class="keyword2 keyword">where</span> j<span class="main">:</span> <span class="quoted quoted"><span>"</span>atom <span class="skolem">j</span> <span class="main">♯</span> <span class="free">i</span><span>"</span></span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">rule</span> obtain_fresh<span class="main">)</span><span>
  </span><span class="keyword1 command">hence</span> Subset_Zero_Iff<span class="main">:</span> <span class="quoted quoted"><span>"</span><span class="main">{}</span> <span class="main">⊢</span> Var <span class="free">i</span> <span class="keyword1">SUBS</span> Zero <span class="keyword1">IFF</span> <span class="main">(</span>All2 <span class="skolem">j</span> <span class="main">(</span>Var <span class="free">i</span><span class="main">)</span> Fls<span class="main">)</span><span>"</span></span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">intro</span><span class="main main">!</span><span class="main main">:</span> Subset_I <span class="main main">[</span><span class="operator">of</span> <span class="quoted skolem">j</span><span class="main main">]</span> <span class="quasi_keyword">intro</span><span class="main main">:</span> Eq_Zero_D Subset_Zero_D All2_E <span class="main main">[</span><span class="operator">THEN</span> rotate2<span class="main main">]</span><span class="main">)</span><span>
  </span><span class="keyword3 command">thus</span> <span class="var quoted var">?thesis</span> <span class="keyword1 command">using</span> j<span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> supp_conv_fresh<span>
             </span><span class="quasi_keyword">intro</span><span class="main main">!</span><span class="main main">:</span> Sigma_fm_Iff <span class="main main">[</span><span class="operator">OF</span> Subset_Zero_Iff<span class="main main">]</span> Sigma_fm_All2_Var<span class="main">)</span><span>
</span><span class="keyword1 command">qed</span>
</pre>

Perhaps surprising is that every HF theorem is automatically a Σ-formula. That simply because every theorem is provably equivalent to $\exists x.\, \exists y.\, x\in y$, which is a valid Σ-formula.
The Isabelle proof isn't especially clear and is shown simply to give an impression of what's involved in proving theorems in the HF calculus.
The Isabelle proof begins by grabbing a pair of fresh variable names, then does the HF proof, giving as existential witnesses $0$ and $0\lhd 0$.

<pre class="source">
<span class="keyword1 command">lemma</span> theorem_sf<span class="main">:</span> <span class="keyword2 keyword">assumes</span> <span class="quoted quoted"><span>"</span><span class="main">{}</span> <span class="main">⊢</span> <span class="free">A</span><span>"</span></span> <span class="keyword2 keyword">shows</span> <span class="quoted quoted"><span>"</span>Sigma_fm <span class="free">A</span><span>"</span></span><span>
</span><span class="keyword1 command">proof</span> <span class="operator">-</span><span>
  </span><span class="keyword3 command">obtain</span> <span class="skolem skolem">i</span><span class="main">::</span><span class="quoted">name</span> <span class="keyword2 keyword">and</span> <span class="skolem skolem">j</span><span class="main">::</span><span class="quoted">name</span><span>
    </span><span class="keyword2 keyword">where</span> ij<span class="main">:</span> <span class="quoted quoted"><span>"</span>atom <span class="skolem">i</span> <span class="main">♯</span> <span class="main">(</span><span class="skolem">j</span><span class="main">,</span><span class="free">A</span><span class="main">)</span><span>"</span></span> <span class="quoted quoted"><span>"</span>atom <span class="skolem">j</span> <span class="main">♯</span> <span class="free">A</span><span>"</span></span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> obtain_fresh<span class="main">)</span><span>
  </span><span class="keyword3 command">show</span> <span class="var quoted var">?thesis</span><span>
    </span><span class="keyword1 command improper command">apply</span> <span class="main">(</span><span class="operator">rule</span> Sigma_fm_Iff <span class="main main">[</span><span class="keyword2 keyword operator">where</span> A <span class="main main main">=</span> <span class="quoted"><span class="quoted quoted"><span>"</span>Ex <span class="skolem skolem">i</span> <span class="main main">(</span>Ex <span class="skolem skolem">j</span> <span class="main main">(</span>Var <span class="skolem skolem">i</span> <span class="keyword1"><span class="keyword1">IN</span> Var <span class="skolem skolem">j</span><span class="main main">)</span><span class="main main">)</span><span>"</span></span></span><span class="main main">]</span><span class="main">)</span><span>
    </span><span class="keyword1 command">using</span> ij<span>
    </span><span class="keyword1 command improper command">apply</span> <span class="operator">auto</span></span><span>
    </span><span class="keyword1 command improper command">apply</span> <span class="main">(</span><span class="operator">rule</span> Ex_I <span class="main main">[</span><span class="keyword2 keyword operator">where</span> x<span class="main main main">=</span><span class="quoted"><span class="quoted">Zero</span><span class="main main">]</span><span class="main keyword3">,</span> <span class="operator">simp</span><span class="main">)</span><span>
    </span><span class="keyword1 command improper command">apply</span> <span class="main">(</span><span class="operator">rule</span> Ex_I <span class="main main">[</span><span class="keyword2 keyword operator">where</span> x<span class="main main main">=</span><span class="quoted quoted quoted">"</span>Eats Zero<span>"</span></span></span><span class="main main">]</span><span class="main">)</span><span>
    </span><span class="keyword1 command improper command">apply</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">intro</span><span class="main main">:</span> Mem_Eats_I2 assms thin0<span class="main">)</span><span>
    </span><span class="keyword1 command improper command">done</span><span>
</span><span class="keyword1 command">qed</span>
</pre>

Once we have assembled a collection of results for atomic formulas with all the different combinations of term constructors, we can prove a key lemma: that all atomic formulas, with arbitrarily large terms, are Σ-formulas. The 50 line proof is by complete induction on the combined sizes of the terms.

<pre class="source">
<span class="keyword1 command">lemma</span> Subset_Mem_sf_lemma<span class="main">:</span><span>
  </span><span class="quoted quoted"><span>"</span>size <span class="free">t</span> <span class="main">+</span> size <span class="free">u</span> <span class="main">&lt;</span> <span class="free">n</span> <span class="main">⟹</span> Sigma_fm <span class="main">(</span><span class="free">t</span> <span class="keyword1">SUBS</span> <span class="free">u</span><span class="main">)</span> <span class="main">∧</span> Sigma_fm <span class="main">(</span><span class="free">t</span> <span class="keyword1">IN</span> <span class="free">u</span><span class="main">)</span><span>"</span></span>
</pre>

As a trivial corollary, equality is also a Σ-formula:

<pre class="source">
<span class="keyword1 command">lemma</span> Equality_sf<span class="main">:</span> <span class="quoted quoted"><span>"</span>Sigma_fm <span class="main">(</span><span class="free">t</span> <span class="keyword1">EQ</span> <span class="free">u</span><span class="main">)</span><span>"</span></span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">intro</span><span class="main main">:</span> Sigma_fm_Iff <span class="main main">[</span><span class="operator">OF</span> Extensionality<span class="main main">]</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> supp_conv_fresh<span class="main">)</span>
</pre>

### Every true Σ-sentence is a theorem

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>


<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
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


