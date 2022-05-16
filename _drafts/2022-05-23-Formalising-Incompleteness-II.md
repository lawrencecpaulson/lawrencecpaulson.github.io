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

Intuitively, such formulas are positive. Negation isn't available and universal quantifiers must be bounded. However, existential quantifiers can be unbounded and this language is rich enough for the techniques used to simulate recursion and thereby express the syntactic structure of well-formed terms, formulas and proofs.

The proof of the main theorem is then by induction on the structure of a (generalised) Σ-sentence.
1. Atomic formulas can essentially be evaluated in the logic, because they have no variables.
2. If $\phi\lor\psi$ is true then either $\phi$ or $\psi$ must be true, and by the induction hypothesis, provable in HF. Therefore, $\phi\lor\psi$ itself is provable. Similarly for $\phi\land\psi$.
3. If $\forall x\in t.\, \phi$ is true then the term $t$ denotes a specific HF set and we are dealing with a conjunction.
4. If $\exists x.\, \phi(x)$ is true then $\phi(t)$ is a true Σ-sentence and therefore a theorem by the induction hypothesis. Using the value of $t$ as a witness, the conclusion follows.

Dead simple really. Let's formalise it.


<pre class="source">
<span class="keyword1 command">inductive</span> <span class="entity">ss_fm</span> <span class="main">::</span> <span class="quoted quoted"><span>"</span>fm <span class="main">⇒</span> bool<span>"</span></span> <span class="keyword2 keyword">where</span><span>
    </span>MemI<span class="main">:</span>  <span class="quoted quoted"><span>"</span><span class="free">ss_fm</span> <span class="main">(</span>Var <span class="free bound entity">i</span> <span class="keyword1">IN</span> Var <span class="free bound entity">j</span><span class="main">)</span><span>"</span></span><span>
  </span><span class="main">|</span> DisjI<span class="main">:</span> <span class="quoted quoted"><span>"</span><span class="free">ss_fm</span> <span class="free bound entity">A</span> <span class="main">⟹</span> <span class="free">ss_fm</span> <span class="free bound entity">B</span> <span class="main">⟹</span> <span class="free">ss_fm</span> <span class="main">(</span><span class="free bound entity">A</span> <span class="keyword1">OR</span> <span class="free bound entity">B</span><span class="main">)</span><span>"</span></span><span>
  </span><span class="main">|</span> ConjI<span class="main">:</span> <span class="quoted quoted"><span>"</span><span class="free">ss_fm</span> <span class="free bound entity">A</span> <span class="main">⟹</span> <span class="free">ss_fm</span> <span class="free bound entity">B</span> <span class="main">⟹</span> <span class="free">ss_fm</span> <span class="main">(</span><span class="free bound entity">A</span> <span class="keyword1">AND</span> <span class="free bound entity">B</span><span class="main">)</span><span>"</span></span><span>
  </span><span class="main">|</span> ExI<span class="main">:</span>   <span class="quoted quoted"><span>"</span><span class="free">ss_fm</span> <span class="free bound entity">A</span> <span class="main">⟹</span> <span class="free">ss_fm</span> <span class="main">(</span>Ex <span class="free bound entity">i</span> <span class="free bound entity">A</span><span class="main">)</span><span>"</span></span><span>
  </span><span class="main">|</span> All2I<span class="main">:</span> <span class="quoted quoted"><span>"</span><span class="free">ss_fm</span> <span class="free bound entity">A</span> <span class="main">⟹</span> atom <span class="free bound entity">j</span> <span class="main">♯</span> <span class="main">(</span><span class="free bound entity">i</span><span class="main">,</span><span class="free bound entity">A</span><span class="main">)</span> <span class="main">⟹</span> <span class="free">ss_fm</span> <span class="main">(</span>All2 <span class="free bound entity">i</span> <span class="main">(</span>Var <span class="free bound entity">j</span><span class="main">)</span> <span class="free bound entity">A</span><span class="main">)</span></span>
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
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


