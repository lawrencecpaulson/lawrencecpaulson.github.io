---
layout: post
title:  Two Small Examples by Fields Medallists
usemathjax: true 
tags: [examples,sledgehammer]
---

A couple of weeks ago, Tim Gowers posted on Twitter an unusual characterisation of bijective functions: that they preserve set complements. 
Alex Kontorovich re-tweeted that post accompanied by a Lean proof detailing Gowers' argument. 
I took a look, and lo and behold! Isabelle can prove it with a single sledgehammer call. 
(That one line proof isn't necessarily the best proof, however.
Remember, we want proofs that are easy to read and maintain.) 
And Terrence Tao published a small example on Mastodon; let's look at that one too.

### Gowers' original tweet

Here is the original tweet, a thread in classical Twitter style: 

> I've just noticed that a function f:X->Y is a bijection if and only if it preserves complements, that is, if and only if f(X\A)=Y\f(A) for every subset A of X. Is this a standard fact that has somehow passed me by for four decades? Simple proof in rest of (short) thread.   1/3

> If f is a bijection and B=X\A, then f preserves unions and intersections and f(X)=Y, so f(A) and f(B) are disjoint and have union equal to Y. Conversely, if f preserves complements, then setting A = emptyset, we see that f(X)=Y, so f is a surjection.  2/3

> And for every x we also have that f(X\{x})=Y\{f(x)}. Therefore, if x and y are distinct, then so are f(x) and f(y). So f is an injection as well. 3/3

In standard mathematical notation, the claim is that if a function $f:X\to Y$ is given,
then $f$ is a bijection from $X$ to $Y$ if and only if it preserves complements, i.e. 
if $f[X\setminus A] = Y \setminus f[A]$ for all $A\subseteq X$.
Incidentally, there are various ways of writing the image under a function of a set; 
Here I use square brackets, while Lean and Isabelle provide their own image operators. 

### The Lean formalisation

Kontorovich posted his version as an image: 

<img src="/images/Gowers-example.jpeg" alt="Formalisation of the bijection proof in Lean by Alex Kontorovich"/>

Note that he has written out the argument in detail, 
with plenty of comments to explain what is going on. 

### Investigating the problem in Isabelle

This problem looked intriguing, so I tried it with Isabelle.
The brute force way to tackle such a proof is 

1. try the `auto` proof method to solve or at least break up the problem 
2. invoke [sledgehammer](https://isabelle.in.tum.de/dist/doc/sledgehammer.pdf) 
on the subgoals that are produced. 

The proof you get this way is likely to be horrible. 
However, once you have your first proof, it's easy to get a nicer proof. 
(And you should take the trouble.)
For the current problem, if you type `auto`, you get four ugly subgoals, each of which sledgehammer proves automatically. 
I don't want to show this, but you can try it for yourself. 
The Isabelle theory file is [here](/Isabelle-Examples/Gowers_Bijection.thy).

What I actually tried, first, was to split the logical equivalence into its two directions. 
I was pleased to see that sledgehammer could prove both. 
Then I thought, let's see if it can prove the whole claim at once, and indeed it could!

### The Isabelle proofs 

To begin, a technicality about notation. 
In Isabelle, *set difference* is written with a minus sign, $A-B$,
because the standard backslash character is reserved for other purposes.
The usual set difference symbol can be selected from the Symbols palette 
or typed as `\setminus` (autocomplete will help). 
So let's begin by setting that up, allowing us to use the conventional symbol.
It will be accepted for input and used to display results.

<pre class="source">
<span class="keyword1 command">abbreviation</span> <span class="entity">set_difference</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">[</span><span class="tfree">'a</span> set</span><span class="main">,</span><span class="tfree">'a</span> set</span><span class="main">]</span> <span class="main">⇒</span> <span class="tfree">'a</span> set<span>"</span> <span class="main">(</span><span class="keyword2 keyword">infixl</span> <span class="quoted"><span>"</span><span class="keyword1">∖</span><span>"</span></span> 65<span class="main">)</span><span>
  </span><span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free bound entity">A</span> <span class="main free">∖</span> <span class="free bound entity">B</span> <span class="main">≡</span> <span class="free bound entity">A</span><span class="main">-</span></span><span class="free bound entity">B</span><span>"</span></span>
</pre>

The following is the nicest of the one-shot proofs found by sledgehammer. 
This problem turned out to be relatively easy; three of the constituent provers 
solved it. 

<pre class="source">
<span class="keyword1 command">lemma</span> <span class="quoted"><span class="quoted"><span>"</span>bij_betw</span> <span class="free">f</span> <span class="free">X</span> <span class="free">Y</span> <span class="main">⟷</span></span> <span class="main">(</span><span class="main">∀</span><span class="bound">A</span><span class="main">.</span> <span class="bound">A</span><span class="main">⊆</span><span class="free">X</span> <span class="main">⟶</span> <span class="free">f</span> <span class="main">`</span> <span class="main">(</span><span class="free">X</span><span class="main">∖</span><span class="bound">A</span><span class="main">)</span> <span class="main">=</span> <span class="free">Y</span> <span class="main">∖</span> <span class="free">f</span><span class="main">`</span><span class="bound">A</span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> Diff_empty Diff_eq_empty_iff Diff_subset bij_betw_def image_is_empty<span> 
            </span>inj_on_image_set_diff subset_antisym subset_image_inj<span class="main">)</span>
</pre>

I don't actually recommend that you allow proofs of this sort 
to accumulate in your development. 
It leaves us completely in the dark as to why the claim holds. 
Moreover, if you want your development to be maintainable, 
it needs to be resilient in the presence of change. 
I'm always having to make corrections and adjustments (because I'm always making mistakes), 
And while rerunning the proofs can be an anxious moment, usually they all work fine.
At worst, they can be fixed by another sledgehammer call. 
Opaque proofs like the one above will be hard to fix when they break. 


The simplest way to get a clearer proof for this particular problem
is by separately treating the left-to-right and right-to-left directions. 
This is also an opportunity to see the `is` mechanism for matching a pattern to a formula. 
An arbitrary pattern is permitted, and here we set up `?L` and `?R`
to denote the left and right hand sides. 

<pre class="source">
<span class="keyword1 command">lemma</span> <span class="quoted"><span class="quoted"><span>"</span>bij_betw</span> <span class="free">f</span> <span class="free">X</span> <span class="free">Y</span> <span class="main">⟷</span></span> <span class="main">(</span><span class="main">∀</span><span class="bound">A</span><span class="main">.</span> <span class="bound">A</span><span class="main">⊆</span><span class="free">X</span> <span class="main">⟶</span> <span class="free">f</span> <span class="main">`</span> <span class="main">(</span><span class="free">X</span><span class="main">∖</span><span class="bound">A</span><span class="main">)</span> <span class="main">=</span> <span class="free">Y</span> <span class="main">∖</span> <span class="free">f</span><span class="main">`</span><span class="bound">A</span><span class="main">)</span><span>"</span>  <span class="main">(</span><span class="keyword2 keyword">is</span> <span class="quoted"><span class="quoted"><span>"</span><span class="var">?L</span><span class="main">=</span></span><span class="var">?R</span><span>"</span></span><span class="main">)</span><span>
</span><span class="keyword1 command">proof</span><span>
  </span><span class="keyword3 command">show</span> <span class="quoted quoted"><span>"</span><span class="var">?L</span> <span class="main">⟹</span> <span class="var">?R</span><span>"</span></span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> Diff_subset bij_betw_def inj_on_image_set_diff<span class="main">)</span><span>
  </span><span class="keyword3 command">assume</span> <span class="var quoted var">?R</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span>inj_on</span> <span class="free">f</span> <span class="free">X</span><span>"</span></span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">f</span> <span class="main">`</span></span> <span class="free">X</span> <span class="main">=</span></span> <span class="free">Y</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> inj_on_def<span class="main">)</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="var quoted var">?L</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> bij_betw_def<span class="main">)</span><span>
</span><span class="keyword1 command">qed</span>
</pre>

This proof is much clearer. The left to write proof requires only three previous facts.
The right to left proof is practically automatic. 
You might argue that even here, the actual reasoning is still opaque.
However, this proof tells us that the right to left direction 
is essentially a calculation from the definitions, 
while the opposite direction is the consequence of three facts (rather than eight, as before). 
This sort of proof will be much easier to maintain.

A further Isabelle bonus: note that both the Lean proof and Gowers' informal argument 
begin by assuming $f:X\to Y$.
The Isabelle version states unconditionally that 
$f$ is a bijection from $X$ to $Y$ if and only if it preserves complements.
The implicit typing of $f$ ensures only that it is a function:
over arbitrary types that we don't even mention. 

### Tao's example

Unfortunately, I wasn't able to locate Tao's original post. 
But he stated a nice little problem and gave a formalisation using Lean, and again I couldn't help trying it out in Isabelle. I liked my proof more. 

We are given a decreasing real-valued sequence $\\{a_k\\}$
and a family of non-negative reals $\\{D_k\\}$
such that $a_k\le D_k - D_{k+1}$ for all $k$.
The task is to prove $a_k \le \frac{D_0}{k+1}$.

<pre class="source">
<span class="keyword1 command">lemma</span><span>
  </span><span class="keyword2 keyword">fixes</span> <span class="free">a</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>nat</span> <span class="main">⇒</span> real</span><span>"</span><span>
  </span><span class="keyword2 keyword">assumes</span> a<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>decseq</span> <span class="free">a</span><span>"</span></span> <span class="keyword2 keyword">and</span> D<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">⋀</span><span class="bound">k</span><span class="main">.</span> <span class="free">D</span> <span class="bound">k</span> <span class="main">≥</span></span> <span class="main">0</span></span><span>"</span> <span class="keyword2 keyword">and</span> aD<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">⋀</span><span class="bound">k</span><span class="main">.</span> <span class="free">a</span> <span class="bound">k</span> <span class="main">≤</span></span> <span class="free">D</span> <span class="bound">k</span> <span class="main">-</span></span> <span class="free">D</span><span class="main">(</span>Suc <span class="bound">k</span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">a</span> <span class="free">k</span> <span class="main">≤</span></span> <span class="free">D</span> <span class="main">0</span></span> <span class="main">/</span> <span class="main">(</span>Suc <span class="free">k</span><span class="main">)</span><span>"</span><span>
</span><span class="keyword1 command">proof</span> <span class="operator">-</span><span>
  </span><span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">a</span> <span class="free">k</span> <span class="main">=</span></span> <span class="main">(</span><span class="main">∑</span><span class="bound">i</span><span class="main">≤</span><span class="free">k</span><span class="main">.</span> <span class="free">a</span> <span class="free">k</span><span class="main">)</span> <span class="main">/</span></span> <span class="main">(</span>Suc <span class="free">k</span><span class="main">)</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="operator">simp</span><span>
  </span><span class="keyword1 command">also</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">…</span> <span class="main">≤</span></span> <span class="main">(</span><span class="main">∑</span><span class="bound">i</span><span class="main">≤</span><span class="free">k</span><span class="main">.</span> <span class="free">a</span> <span class="bound">i</span><span class="main">)</span> <span class="main">/</span></span> <span class="main">(</span>Suc <span class="free">k</span><span class="main">)</span><span>"</span><span>
    </span><span class="keyword1 command">using</span> a sum_mono<span class="main">[</span><span class="operator">of</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">{..</span></span><span class="free">k</span><span class="main">}</span></span><span>"</span> <span class="quoted quoted"><span>"</span><span class="main">λ</span><span class="bound">i</span><span class="main">.</span> <span class="free">a</span> <span class="free">k</span><span>"</span></span> <span class="quoted free">a</span><span class="main">]</span><span> 
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> monotone_def <span class="dynamic dynamic">divide_simps</span> mult.commute<span class="main">)</span><span>
  </span><span class="keyword1 command">also</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">…</span> <span class="main">≤</span></span> <span class="main">(</span><span class="main">∑</span><span class="bound">i</span><span class="main">≤</span><span class="free">k</span><span class="main">.</span> <span class="free">D</span> <span class="bound">i</span> <span class="main">-</span></span> <span class="free">D</span><span class="main">(</span>Suc <span class="bound">i</span><span class="main">)</span><span class="main">)</span> <span class="main">/</span> <span class="main">(</span>Suc <span class="free">k</span><span class="main">)</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> aD divide_right_mono sum_mono<span class="main">)</span><span>
  </span><span class="keyword1 command">also</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">…</span> <span class="main">≤</span></span> <span class="free">D</span> <span class="main">0</span></span> <span class="main">/</span> <span class="main">(</span>Suc <span class="free">k</span><span class="main">)</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> sum_telescope D divide_right_mono<span class="main">)</span><span>
  </span><span class="keyword1 command">finally</span> <span class="keyword3 command">show</span> <span class="var quoted var">?thesis</span> <span class="keyword1 command">.</span><span>
</span><span class="keyword1 command">qed</span>
</pre>

Isabelle's calculational style is perfect for this sort of inequality chain. 

### Final remarks 

**Always** break up your problem 
into its constituents – probably by calling `auto` – before calling sledgehammer.
The effort needed to prove all the separate parts 
is generally much less than that needed prove the whole in one go. 
Besides which, part of your problem may simply be too difficult for sledgehammer.
Better to isolate that part to work on later, while disposing of the easier bits. 

The Isabelle theory file is available to [download](/Isabelle-Examples/Gowers_Bijection.thy).
