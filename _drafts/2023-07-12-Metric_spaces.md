---
layout: post
title:  "Porting the HOL Light metric space library"
usemathjax: true 
tags: [general, Isabelle, sledgehammer, locales, HOL Light]
---

I'm sorry that there have been no posts since April. I've been busy with a side project: porting the [HOL Light metric space library](https://doi.org/10.1007/s10817-017-9412-x
) 
to Isabelle in time for the upcoming release. It was a big job: the chunk I grabbed initially comprised some 1335 lemmas, over 24K lines and nearly 1.2M bytes. Some of the lemmas turned out to have been ported previously, or otherwise turned out to be unnecessary; on the other hand, quite a few additional lemmas were needed. The material included metric spaces and many associated concepts, also advanced material about toplogical spaces, the relationships among different kinds of spaces, 
and also closure properties, especially under general products. 
Major contributions include Urysohn's lemma and the Tietze extension theorem, the Baire Category Theorem and the Banach Fixed-Point Theorem.

### But what about the existing typeclass for metric spaces?

It's worth recalling that Isabelle/HOL already includes a huge amount of material [ported from HOL Light]({% post_url 2022-09-14-Libraries %}), a lot of it about metric spaces and including results bearing the names of Urysohn and Tietze. These relate to the metric space type class, which governs **types** that can be seen as metric spaces, including real norned vector spaces and Euclidean spaces, and in particular $\mathbb{R}^n$.
However, [type classes]({% post_url 2022-03-02-Type_classes %}) only work for types, and many interesting metric spaces cannot be expressed as types. By working more abstractly, we can work with metric spaces over arbitrary carrier sets.

### Declaring metric spaces as a locale

The HOL Light version defines an abstract type of metric spaces, which is given as an argument to the numerous metric space operations.
This approach is flexible when we need to mix several metric space constructions. However, it's clunky when working within a single metric space, which is so often done. The best way to handle that situation is through a [*locale*]({% post_url 2022-03-23-Locales %}): 
a packaged context that can be re-entered at any time.
The metric space locale declares the carrier set (M) and the distance function (d).

<pre class="source">
<span class="keyword1 command">locale</span> Metric_space <span class="main">=
  </span><span class="keyword2 keyword">fixes</span> <span class="free">M</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span><span class="tfree">'a</span> set"</span></span> <span class="keyword2 keyword">and</span> <span class="free">d</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span><span class="tfree">'a</span> <span class="main">⇒</span> <span class="tfree">'a</span> <span class="main">⇒</span> real"</span>
  </span><span class="keyword2 keyword">assumes</span> nonneg <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">⋀</span><span class="bound">x</span> <span class="bound">y</span><span class="main">.</span> <span class="main">0</span></span> <span class="main">≤</span></span> <span class="free">d</span> <span class="bound">x</span> <span class="bound">y"
  </span><span class="keyword2 keyword">assumes</span> commute<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">⋀</span><span class="bound">x</span> <span class="bound">y</span><span class="main">.</span> <span class="free">d</span> <span class="bound">x</span> <span class="bound">y</span> <span class="main">=</span></span> <span class="free">d</span> <span class="bound">y</span> <span class="bound">x"</span>
  </span><span class="keyword2 keyword">assumes</span> zero <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">⋀</span><span class="bound">x</span> <span class="bound">y</span><span class="main">.</span> <span class="main">⟦</span><span class="bound">x</span> <span class="main">∈</span></span> <span class="free">M</span><span class="main">;</span> <span class="bound">y</span> <span class="main">∈</span></span> <span class="free">M</span><span class="main">⟧</span> <span class="main">⟹</span> <span class="free">d</span> <span class="bound">x</span> <span class="bound">y</span> <span class="main">=</span> <span class="main">0</span> <span class="main">⟷</span> <span class="bound">x</span><span class="main">=</span><span class="bound">y"
  </span><span class="keyword2 keyword">assumes</span> triangle<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">⋀</span><span class="bound">x</span> <span class="bound">y</span> <span class="bound">z</span><span class="main">.</span> <span class="main">⟦</span><span class="bound">x</span> <span class="main">∈</span></span> <span class="free">M</span><span class="main">;</span> <span class="bound">y</span> <span class="main">∈</span></span> <span class="free">M</span><span class="main">;</span> <span class="bound">z</span> <span class="main">∈</span> <span class="free">M</span><span class="main">⟧</span> <span class="main">⟹</span> <span class="free">d</span> <span class="bound">x</span> <span class="bound">z</span> <span class="main">≤</span> <span class="free">d</span> <span class="bound">x</span> <span class="bound">y</span> <span class="main">+</span> <span class="free">d</span> <span class="bound">y</span> <span class="bound">z"</span>
</pre>


Working within the locale, declaring concepts such as open balls is straightforward:
<pre class="source">
<span class="keyword1 command">definition</span> <span class="entity">mball</span> <span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">mball</span> <span class="free bound entity">x</span> <span class="free bound entity">r</span> <span class="main">≡</span> <span class="main">{</span><span class="bound">y</span><span class="main">.</span> <span class="free bound entity">x</span> <span class="main">∈</span></span> <span class="free">M</span> <span class="main">∧</span></span> <span class="bound">y</span> <span class="main">∈</span> <span class="free">M</span> <span class="main">∧</span> <span class="free">d</span> <span class="free bound entity">x</span> <span class="bound">y</span> <span class="main">&lt;</span> <span class="free bound entity">r</span>"

<span class="keyword1 command">lemma</span> centre_in_mball_iff <span class="main">[</span><span class="operator">iff</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">∈</span></span> mball</span> <span class="free">x</span> <span class="free">r</span> <span class="main">⟷</span> <span class="free">x</span> <span class="main">∈</span> <span class="free">M</span> <span class="main">∧</span> <span class="main">0</span> <span class="main">&lt;</span> <span class="free">r"
  </span><span class="keyword1 command">using</span> in_mball mdist_zero <span class="keyword1 command">by</span> <span class="operator">force</span>

<span class="keyword1 command">lemma</span> mball_subset_mspace<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>mball</span> <span class="free">x</span> <span class="free">r</span> <span class="main">⊆</span></span> <span class="free">M"
  </span><span class="keyword1 command">by</span> <span class="operator">auto</span>
</pre>


It also works for rather more sophisticated proofs, such as the uniqueness of fixed points of a contraction mapping.
The theorem statement is surprisingly natural, and the proof shown below 
can be found (thanks to [sledgehammer]({% post_url 2022-04-13-Sledgehammer %})) 
by a single mouse click.

<pre class="source">
<span class="keyword1 command">lemma</span> <span class="main">(</span><span class="keyword2 keyword">in</span> Metric_space<span class="main">)</span> contraction_imp_unique_fixpoint<span class="main">:
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">f</span> <span class="free">x</span> <span class="main">=</span></span> <span class="free">x"</span></span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">f</span> <span class="free">y</span> <span class="main">=</span></span> <span class="free">y"</span>
    </span><span class="keyword2 keyword">and</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">f</span> <span class="main">∈</span></span> <span class="free">M</span> <span class="main">→</span></span> <span class="free">M"
    </span><span class="keyword2 keyword">and</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">k</span> <span class="main">&lt;</span></span> <span class="main">1</span>"
    </span><span class="keyword2 keyword">and</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">⋀</span><span class="bound">x</span> <span class="bound">y</span><span class="main">.</span> <span class="main">⟦</span><span class="bound">x</span> <span class="main">∈</span></span> <span class="free">M</span><span class="main">;</span> <span class="bound">y</span> <span class="main">∈</span></span> <span class="free">M</span><span class="main">⟧</span> <span class="main">⟹</span> <span class="free">d</span> <span class="main">(</span><span class="free">f</span> <span class="bound">x</span><span class="main">)</span> <span class="main">(</span><span class="free">f</span> <span class="bound">y</span><span class="main">)</span> <span class="main">≤</span> <span class="free">k</span> <span class="main">*</span> <span class="free">d</span> <span class="bound">x</span> <span class="bound">y"
    </span><span class="keyword2 keyword">and</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">∈</span></span> <span class="free">M"</span></span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">y</span> <span class="main">∈</span></span> <span class="free">M"</span>
  </span><span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">=</span></span> <span class="free">y"</span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">smt</span> <span class="main main">(</span>verit<span class="main main">,</span> ccfv_SIG<span class="main mdist_pos_less mult_le_cancel_right1 assms<span class="main">)</span>
</pre>


Locales nest naturally, as when we introduce the notion of a subspace of a metric space:

<pre class="source">
<span class="keyword1 command">locale</span> Submetric <span class="main">=</span> Metric_space <span class="main">+ 
  </span><span class="keyword2 keyword">fixes</span> <span class="free">A
  </span><span class="keyword2 keyword">assumes</span> subset<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">A</span> <span class="main">⊆</span></span> <span class="free">M"</span>

</span><span class="keyword1 command">sublocale</span> Submetric <span class="main">⊆</span> sub<span class="main">:</span> Metric_space <span class="quoted free">A</span> <span class="quoted free">d
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> subset subspace<span class="main">)</span>
</pre>

The declaration above state that every submetric can be viewed as a metric space in its own right.

### An abstract type of metric spaces

Although the locale-based approach is general – you work outside the locale merely by quoting the desired values of `M` and `d` every time – it can get tedious, especially when working with multiple metric spaces. 
So it's helpful to follow HOL Light in also declaring an *abstract type* of metric spaces.

<pre class="source">
<span class="keyword1 command">typedef</span> <span class="tfree">'a</span> metric <span class="main">=</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">{</span><span class="main">(</span><span class="bound">M</span><span class="main">::</span><span class="tfree">'a</span> set</span><span class="main">,</span><span class="bound">d</span><span class="main">)</span><span class="main">.</span> Metric_space</span> <span class="bound">M</span> <span class="bound">d</span><span class="main">}"
  </span><span class="keyword2 keyword">morphisms</span> <span class="quoted"><span>"</span>dest_metric"</span> <span class="quoted"><span>"</span>metric"
</span><span class="keyword1 command">proof</span> <span class="operator">-
  </span><span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span>Metric_space</span> <span class="main">{}</span></span> <span class="main">(</span><span class="main">λ</span><span class="bound">x</span> <span class="bound">y</span><span class="main">.</span> <span class="main">0</span><span class="main">)"
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> Metric_space_def<span class="main">)
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="var quoted var">?thesis
    </span><span class="keyword1 command">by</span> <span class="operator">blast
</span><span class="keyword1 command">qed

</span><span class="keyword1 command">definition</span> <span class="entity">mspace</span> <span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">mspace</span> <span class="free bound entity">m</span> <span class="main">≡</span> fst</span> <span class="main">(</span>dest_metric</span> <span class="free bound entity">m</span><span class="main">)"

</span><span class="keyword1 command">definition</span> <span class="entity">mdist</span> <span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">mdist</span> <span class="free bound entity">m</span> <span class="main">≡</span> snd</span> <span class="main">(</span>dest_metric</span> <span class="free bound entity">m</span><span class="main">)"</span>
</pre>

We can prove a few results linking the two levels. It's then easy
to switch back to the locale approach at any point in a proof,
starting with any available metric space.

<pre class="source">
<span class="keyword1 command">lemma</span> Metric_space_mspace_mdist <span class="main">[</span><span class="operator">iff</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>Metric_space</span> <span class="main">(</span>mspace</span> <span class="free">m</span><span class="main">)</span> <span class="main">(</span>mdist <span class="free">m</span><span class="main">)"
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> Product_Type.Collect_case_prodD dest_metric mdist_def mspace_def<span class="main">)

</span><span class="keyword1 command">lemma</span> <span class="main">(</span><span class="keyword2 keyword">in</span> Metric_space<span class="main">)</span> mspace_metric<span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">: 
  </span><span class="quoted"><span class="quoted"><span>"</span>mspace</span> <span class="main">(</span>metric</span> <span class="main">(</span><span class="free">M</span><span class="main">,</span><span class="free">d</span><span class="main">)</span><span class="main">)</span> <span class="main">=</span> <span class="free">M"
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> mspace_def Metric_space_axioms metric_inverse<span class="main">)

</span><span class="keyword1 command">lemma</span> <span class="main">(</span><span class="keyword2 keyword">in</span> Metric_space<span class="main">)</span> mdist_metric<span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">: 
  </span><span class="quoted"><span class="quoted"><span>"</span>mdist</span> <span class="main">(</span>metric</span> <span class="main">(</span><span class="free">M</span><span class="main">,</span><span class="free">d</span><span class="main">)</span><span class="main">)</span> <span class="main">=</span> <span class="free">d"
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> mdist_def Metric_space_axioms metric_inverse<span class="main">)</span>
</pre>

Declaring a few of the most frequently used concepts (here, the associated topology) for the abstract type makes it even easier to work at the most appropriate level:

<pre class="source">
<span class="keyword1 command">definition</span> <span class="entity">mtopology_of</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span><span class="tfree">'a</span> metric</span> <span class="main">⇒</span> <span class="tfree">'a</span> topology"
  </span><span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">mtopology_of</span> <span class="main">≡</span> <span class="main">λ</span><span class="bound">m</span><span class="main">.</span> Metric_space.mtopology</span> <span class="main">(</span>mspace</span> <span class="bound">m</span><span class="main">)</span> <span class="main">(</span>mdist <span class="bound">m</span><span class="main">)"

</span><span class="keyword1 command">lemma</span> topspace_mtopology_of <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>topspace</span> <span class="main">(</span>mtopology_of</span> <span class="free">m</span><span class="main">)</span> <span class="main">=</span> mspace <span class="free">m"
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> Metric_space.topspace_mtopology Metric_space_mspace_mdist mtopology_of_def<span class="main">)</span>
</pre>

I must confess, I was not always certain which way was best. 
Fortunately, such decisions are not committal, and I frequently started by proving a theorem within the locale, from which the abstract type analogue could immediately be optained.

### Interoperability with the type class level

Having declared the `Metric_space` locale, my development immediately
interprets it using the type class version.
What's going on not obvious; the clue is `dist`, which is the distance function for the type class. 
We've just established that anything involving the `metric_space` type class now applies as well to the more general locale framework.

<pre class="source">
<span class="keyword1 command">interpretation</span> Met_TC<span class="main">:</span> Metric_space <span class="quoted">UNIV</span> <span class="quoted">dist
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> dist_commute dist_triangle Metric_space.intro<span class="main">)</span></pre>

Now the equivalence between the type class and locale concepts is proved trivially:

<pre class="source">
<span class="keyword1 command">lemma</span> mball_eq_ball <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>Met_TC.mball</span> <span class="main">=</span></span> ball<span>"
  </span><span class="keyword1 command">by</span> <span class="operator">force

</span><span class="keyword1 command">lemma</span> mopen_eq_open <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>Met_TC.mopen</span> <span class="main">=</span></span> open<span>"
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">force</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> open_contains_ball Met_TC.mopen_def<span class="main">)

</span><span class="keyword1 command">lemma</span> limitin_iff_tendsto <span class="main">[</span><span class="operator">iff</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>limitin</span> Met_TC.mtopology</span> <span class="free">σ</span> <span class="free">x</span> <span class="free">F</span> <span class="main">=</span> tendsto <span class="free">σ</span> <span class="free">x</span> <span class="free">F"
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> Met_TC.mtopology_def<span class="main">)

</span><span class="keyword1 command">lemma</span> mtopology_is_euclidean <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>Met_TC.mtopology</span> <span class="main">=</span></span> euclidean<span>"
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> Met_TC.mtopology_def<span class="main">)</span>
</pre>

And so, simplification alone will drop us from the locale level to the type class level whenever this is possible.

The role of type classes is a key difference between simply typed and dependent typed formalisms. Type classes play a bigger role in the latter (but with the risk of performance issues and problems with multiple inheritance); with the former, we may be stuck with having to duplicate some proofs.


### On the horrors of HOL Light proofs

I commented on the tribulations [last time]({% post_url 2022-09-14-Libraries %}).
But seriously:

* Why would you use `x` as a Cauchy sequence and a real number in the same formula, just because you can?
* Why would you generate an induction formula through an opaque series of transformations when you could simply type it in?
* Why would you instantiate a lemma by applying syntactic functions to the current goal when you could simply type in the necessary terms?
* Why unfold all definitions at once, turning your nice concise goal into a full page of formulas?

Well, in HOL Light that's how you roll. 

A ubiquitous horror is [MP_TAC](https://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/MP_TAC.html), 
introduced by yours truly around 1984. It stuffs a given theorem $T$ 
into the current goal $G$ to create the implication $T\Longrightarrow G$.
Typically $T$ would have been produced from something else, by instantiation at least, and is about to undergo rewriting and other transformations.
(In HOL Light, as in its predecessors, the simplifier never altered a goal's *assumptions*, which is why we want $T$ in the goal formula itself.) 
Having simplified $T$ to say $T_1\land T_2$, a proof might move one of them to the assumptions (via [ASSUME_TAC](https://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/ASSUME_TAC.html))
and put back the other, via another MP_TAC call, to work on some more.
It's basically a stack machine computation, slowly massaging the goal into `T` (true).
Some of them are grimly incomprehensible.
Then the next proof might consist of a pleasant string of [SUBGOAL_TAC](https://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/SUBGOAL_TAC.html) calls,
almost as nice as an Isabelle proof.

Sometimes I was able to port proofs just by eyeballing the HOL Light versions, but often I had to run them in a HOL Light session, 
occasionally line by line.
Sledgehammer did most of the work, and half the time I had no idea what the actual argument was. Well, I don't really need to know.


