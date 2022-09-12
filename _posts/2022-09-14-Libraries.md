---
layout: post
title:  "Porting Libraries of Mathematics Between Proof Assistants"
usemathjax: true 
tags: [general, Isabelle, Archive of Formal Proofs, HOL system, HOL Light, Coq]
---

In 2005, a student arrived who wanted to do a PhD involving formalised probability theory.
I advised him to use HOL4, where theories of Lebesgue integration and probability theory had [already been formalised](https://doi.org/10.48456/tr-566); they were not available in Isabelle/HOL.
Ironically, he eventually discovered that the HOL4 theories didn't meet his requirements and he was forced to redo them.
This episode explains why I have since devoted so much effort to porting libraries into Isabelle/HOL.
But note: Isabelle/HOL already had, from 2004, a *full copy* of the HOL4 libraries, translated by importer tools.
I never even thought of using these libraries, and they were quietly withdrawn in 2012.
Why was that? And what is the right way to achieve interoperability between proof assistant libraries?

### Libraries of mathematics

Just as the significance of a platform is determined by its application base, the significance of a proof assistant is largely determined by its libraries:

* [Mathematical Components](https://math-comp.github.io)
(among others) for [Coq](https://coq.inria.fr); 
* [mathlib](https://leanprover-community.github.io) for
[Lean](https://leanprover.github.io);
* the [Archive of Formal Proofs](https://www.isa-afp.org)
for [Isabelle](https://isabelle.in.tum.de).
* John Harrison's [Euclidean spaces](https://rdcu.be/cJtGW) 
and ["top 100 theorems"](https://www.cs.ru.nl/~freek/100/)
for [HOL Light](https://www.cl.cam.ac.uk/~jrh13/hol-light/) 
* Although [Mizar](http://mizar.org) introduced a groundbreaking mathematical language, for many researchers the real attraction was the huge Mizar Mathematical Library.

Many people thought it wasteful to have so many overlapping but incompatible libraries.
The proprietors of newer systems were naturally covetous of the accumulated wealth of older systems. This feeling was particularly strong among the various implementations of higher-order logic, one single formalism if we ignore each implementation's bells and whistles.
Powerful and efficient importers were built, e.g. by [Obua and Skalberg](https://rdcu.be/cUZ2i), but they didn't catch on. Despite that, research in this area continues.

I am not optimistic for the prospects of this sort of library porting, for a simple reason: we need the **actual proofs**. All the attempts that I have seen involve finding a lowest-common-denominator calculus for two different proof assistants and thus to emulate proofs in one system using proofs in the other. Ideally, corresponding basic libraries (e.g. of the natural numbers) are identified and matched rather than translated.
Still, the very best one can hope for is a list of statements certified by the importer as having been proved somewhere, somehow.
This isn't satisfying.

### Porting proofs from HOL Light to Isabelle/HOL

HOL Light is famous for its huge multivariate analysis library: nearly 300,000 lines of code and 13,000 theorems. 
I spent a lot of time between 2015 and 2017 porting great chunks of this material.
It might seem an odd use of my time. I had spent years away from Isabelle working on [MetiTarski](https://www.cl.cam.ac.uk/~lp15/papers/Arith/), then returned to Isabelle to prove [Gödel's incompleteness theorems](https://rdcu.be/cUZ4e),
and then—with a couple of big grant proposals falling short—found myself at a loose end.

The HOL Light library was definitely valuable, or so people told me. Regrettably, my knowledge of multivariate analysis is minimal, and please don't utter the word "homology".
I was ideally suited to this porting task: HOL Light is astonishingly retro, hardly different from [Cambridge LCF](https://github.com/kohlhase/CambridgeLCF) as I left it in 1984.
Aspects of the work could be automated through Perl scripts and the porting of routine material was actually kind of relaxing, like doing a crossword (only much easier).
And oh! The nostalgia of seeing `REPEAT GEN_TAC` (which dates to Edinburgh LCF)
and "conversions" and "theorem continuations" (my own weird babies).
I seldom had to actually run HOL Light in order to see what was going on in a proof except for a few exceptionally long, ghastly or treacherous HOL Light scripts.
Two variables called `x` but with different types? No problem.
I could even figure out such horrors as
<pre class="source">
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET)
</pre>

The Isabelle analysis library today contains approximately 10,000 named theorems, including Cauchy’s integral and residue theorems, the Liouville theorem, the open mapping and domain invariance theorems, the maximum modulus principle and the Krein-Milman theorem.
This represents 100-200K lines of HOL Light proofs (the wretched homology development alone is 11,400 lines).
The material was ported by a variety of people. 
But for my sins, I think I ported the bulk of it.

### Working through an example

At 50 lines, the following HOL Light proof counts as medium-sized. It's not trivial, but neither is it in any way difficult.
 RuthlesslyAll you need is persistence.

<pre class="source">
let HOMEOMORPHIC_PUNCTURED_SPHERE_AFFINE_GEN = prove
 (`!s:real^N->bool t:real^M->bool a.
        convex s /\ bounded s /\ a IN relative_frontier s /\
        affine t /\ aff_dim s = aff_dim t + &1
        ==> (relative_frontier s DELETE a) homeomorphic t`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_SIMP_TAC[AFF_DIM_EMPTY; AFF_DIM_GE; INT_ARITH
   `--(&1):int <= s ==> ~(--(&1) = s + &1)`] THEN
  MP_TAC(ISPECL [`(:real^N)`; `aff_dim(s:real^N->bool)`]
    CHOOSE_AFFINE_SUBSET) THEN REWRITE_TAC[SUBSET_UNIV] THEN
  REWRITE_TAC[AFF_DIM_GE; AFF_DIM_LE_UNIV; AFF_DIM_UNIV; AFFINE_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(t:real^N->bool = {})` MP_TAC THENL
   [ASM_MESON_TAC[AFF_DIM_EQ_MINUS1]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `z:real^N`) THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`s:real^N->bool`; `ball(z:real^N,&1) INTER t`]
        HOMEOMORPHIC_RELATIVE_FRONTIERS_CONVEX_BOUNDED_SETS) THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `ball(z:real^N,&1)`]
        (ONCE_REWRITE_RULE[INTER_COMM] AFF_DIM_CONVEX_INTER_OPEN)) THEN
  MP_TAC(ISPECL [`ball(z:real^N,&1)`; `t:real^N->bool`]
        RELATIVE_FRONTIER_CONVEX_INTER_AFFINE) THEN
  ASM_SIMP_TAC[CONVEX_INTER; BOUNDED_INTER; BOUNDED_BALL; CONVEX_BALL;
               AFFINE_IMP_CONVEX; INTERIOR_OPEN; OPEN_BALL;
               FRONTIER_BALL; REAL_LT_01] THEN
  SUBGOAL_THEN `~(ball(z:real^N,&1) INTER t = {})` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `z:real^N` THEN ASM_REWRITE_TAC[CENTRE_IN_BALL; REAL_LT_01];
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN SIMP_TAC[]] THEN
  REWRITE_TAC[homeomorphic; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`h:real^N->real^N`; `k:real^N->real^N`] THEN
  STRIP_TAC THEN REWRITE_TAC[GSYM homeomorphic] THEN
  TRANS_TAC HOMEOMORPHIC_TRANS
    `(sphere(z,&1) INTER t) DELETE (h:real^N->real^N) a` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[homeomorphic] THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^N`; `k:real^N->real^N`] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HOMEOMORPHISM]) THEN
    REWRITE_TAC[HOMEOMORPHISM] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; DELETE_SUBSET];
      ASM SET_TAC[];
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; DELETE_SUBSET];
      ASM SET_TAC[];
      ASM SET_TAC[];
      ASM SET_TAC[]];
    MATCH_MP_TAC HOMEOMORPHIC_PUNCTURED_AFFINE_SPHERE_AFFINE THEN
    ASM_REWRITE_TAC[REAL_LT_01; GSYM IN_INTER] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HOMEOMORPHISM]) THEN
    ASM SET_TAC[]]);;
</pre>

I should mention that I often had little grasp of the mathematics.
Convex and bounded sets are simple enough. Affine? No idea. Affine dimension presumably has something to do with dimensions in linear algebra, and at the start of this work I had never come across the word *homeomorphism*. I did manage to learn bits and pieces while porting all this material, and I'm pretty sure that this particular theorem generalises the well-known fact that a punctured sphere can be continuously flattened to a plane: the so-called [stereographic projection](https://en.wikipedia.org/wiki/Stereographic_projection).

The proof script is typical of HOL Light.
Formidable though it appears, every proof is a combination of backward reasoning from the goal and forward reasoning from the assumptions, and a close look will reveal these steps.
However, the lack of a structured language means that the same effect might be obtained in strikingly different ways. 
We see in the first line case analysis on whether the set `s` is empty, though in reality the assumptions imply that it is nonempty. Calls to `MP_TAC` typically involve inserting instances of previous theorems into the list of assumptions (I invented this technique, may God forgive me), when our task is to find the corresponding theorem in the Isabelle library
(porting it if it is not there) and first proving the corresponding instances of its premises, which can be read off from the explicit instance given here by `ISPECL`. 
The line beginning `DISCH_THEN(X_CHOOSE_THEN` notes an existential claim from the theorem just instantiated. (Those are theorem continuations.)
Sometimes the proofs are nested but we can keep going, hoping that an induction formula is not being generated dynamically, because then you often can't see what the induction is all about.

This process is largely mechanical, which is why I could port proofs that I didn't understand.
That's why I believe that the future of proof porting must involve the porting of proofs **at a high level**, where we can see the structure of the result—and not by translating the primitive inferences of a calculus.

For this example, the result of my largely ignorant and mechanical translation at least resembles mathematics:

<pre class="source">
<span class="keyword1 command">proposition</span> homeomorphic_punctured_sphere_affine_gen<span class="main">:</span><span>
  </span><span class="keyword2 keyword">fixes</span> <span class="free">a</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span><span class="tfree">'a</span> <span class="main">::</span> euclidean_space</span><span>"</span></span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span>convex</span> <span class="free">S</span><span>"</span></span> <span class="quoted"><span class="quoted"><span>"</span>bounded</span> <span class="free">S</span><span>"</span></span> <span class="keyword2 keyword">and</span> a<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">a</span> <span class="main">∈</span></span> rel_frontier</span> <span class="free">S</span><span>"</span><span>
      </span><span class="keyword2 keyword">and</span> <span class="quoted"><span class="quoted"><span>"</span>affine</span> <span class="free">T</span><span>"</span></span> <span class="keyword2 keyword">and</span> affS<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>aff_dim</span> <span class="free">S</span> <span class="main">=</span></span> aff_dim <span class="free">T</span> <span class="main">+</span> <span class="main">1</span><span>"</span><span>
    </span><span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span>rel_frontier</span> <span class="free">S</span> <span class="main">-</span></span> <span class="main">{</span><span class="free">a</span><span class="main">}</span> <span class="keyword1">homeomorphic</span> <span class="free">T</span><span>"</span><span>
</span><span class="keyword1 command">proof</span> <span class="operator">-</span><span>
  </span><span class="keyword3 command">obtain</span> <span class="skolem skolem">U</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span><span class="tfree">'a</span> set</span><span>"</span></span> <span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span>affine</span> <span class="skolem">U</span><span>"</span></span> <span class="quoted"><span class="quoted"><span>"</span>convex</span> <span class="skolem">U</span><span>"</span></span> <span class="keyword2 keyword">and</span> affdS<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>aff_dim</span> <span class="skolem">U</span> <span class="main">=</span></span> aff_dim <span class="free">S</span><span>"</span><span>
    </span><span class="keyword1 command">using</span> choose_affine_subset <span class="main">[</span><span class="operator">OF</span> affine_UNIV aff_dim_geq<span class="main">]</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">meson</span> aff_dim_affine_hull affine_affine_hull affine_imp_convex<span class="main">)</span><span>
  </span><span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">S</span> <span class="main">≠</span></span> <span class="main">{}</span></span><span>"</span> <span class="keyword1 command">using</span> assms <span class="keyword1 command">by</span> <span class="operator">auto</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">obtain</span> <span class="skolem skolem">z</span> <span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">z</span> <span class="main">∈</span></span> <span class="skolem">U</span><span>"</span></span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> aff_dim_negative_iff equals0I affdS<span class="main">)</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword1 command">have</span> bne<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>ball</span> <span class="skolem">z</span> <span class="main">1</span></span> <span class="main">∩</span> <span class="skolem">U</span> <span class="main">≠</span> <span class="main">{}</span><span>"</span> <span class="keyword1 command">by</span> <span class="operator">force</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword1 command">have</span> <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>aff_dim</span><span class="main">(</span>ball</span> <span class="skolem">z</span> <span class="main">1</span> <span class="main">∩</span> <span class="skolem">U</span><span class="main">)</span> <span class="main">=</span> aff_dim <span class="skolem">U</span><span>"</span><span>
    </span><span class="keyword1 command">using</span> aff_dim_convex_Int_open <span class="main">[</span><span class="operator">OF</span> <span class="quoted"><span class="quoted"><span>‹</span>convex</span> <span class="skolem">U</span><span>›</span></span> open_ball<span class="main">]</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">fastforce</span> <span class="quasi_keyword">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> Int_commute<span class="main">)</span><span>
  </span><span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span>rel_frontier</span> <span class="free">S</span> <span class="keyword1">homeomorphic</span></span> rel_frontier <span class="main">(</span>ball <span class="skolem">z</span> <span class="main">1</span> <span class="main">∩</span> <span class="skolem">U</span><span class="main">)</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">rule</span> homeomorphic_rel_frontiers_convex_bounded_sets<span class="main">)</span><span>
       </span><span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> <span class="quoted"><span class="quoted"><span>‹</span>affine</span> <span class="skolem">U</span><span>›</span></span> affine_imp_convex convex_Int affdS assms<span class="main">)</span><span>
  </span><span class="keyword1 command">also</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">...</span> <span class="main">=</span></span> sphere</span> <span class="skolem">z</span> <span class="main">1</span> <span class="main">∩</span> <span class="skolem">U</span><span>"</span><span>
    </span><span class="keyword1 command">using</span> convex_affine_rel_frontier_Int <span class="main">[</span><span class="operator">of</span> <span class="quoted"><span class="quoted"><span>"</span>ball</span> <span class="skolem">z</span> <span class="main">1</span></span><span>"</span> <span class="quoted skolem">U</span><span class="main">]</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> <span class="quoted"><span class="quoted"><span>‹</span>affine</span> <span class="skolem">U</span><span>›</span></span> bne<span class="main">)</span><span>
  </span><span class="keyword1 command">finally</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span>rel_frontier</span> <span class="free">S</span> <span class="keyword1">homeomorphic</span></span> sphere <span class="skolem">z</span> <span class="main">1</span> <span class="main">∩</span> <span class="skolem">U</span><span>"</span> <span class="keyword1 command">.</span><span> 
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">obtain</span> <span class="skolem skolem">h</span> <span class="skolem skolem">k</span> <span class="keyword2 keyword">where</span> him<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">h</span> <span class="main">`</span></span> rel_frontier</span> <span class="free">S</span> <span class="main">=</span> sphere <span class="skolem">z</span> <span class="main">1</span> <span class="main">∩</span> <span class="skolem">U</span><span>"</span><span>
                    </span><span class="keyword2 keyword">and</span> kim<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">k</span> <span class="main">`</span></span> <span class="main">(</span>sphere</span> <span class="skolem">z</span> <span class="main">1</span> <span class="main">∩</span> <span class="skolem">U</span><span class="main">)</span> <span class="main">=</span> rel_frontier <span class="free">S</span><span>"</span><span>
                    </span><span class="keyword2 keyword">and</span> hcon<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>continuous_on</span> <span class="main">(</span>rel_frontier</span> <span class="free">S</span><span class="main">)</span> <span class="skolem">h</span><span>"</span><span>
                    </span><span class="keyword2 keyword">and</span> kcon<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>continuous_on</span> <span class="main">(</span>sphere</span> <span class="skolem">z</span> <span class="main">1</span> <span class="main">∩</span> <span class="skolem">U</span><span class="main">)</span> <span class="skolem">k</span><span>"</span><span>
                    </span><span class="keyword2 keyword">and</span> kh<span class="main">:</span>  <span class="quoted"><span class="quoted"><span>"</span><span class="main">⋀</span><span class="bound">x</span><span class="main">.</span> <span class="bound">x</span> <span class="main">∈</span></span> rel_frontier</span> <span class="free">S</span> <span class="main">⟹</span> <span class="skolem">k</span><span class="main">(</span><span class="skolem">h</span><span class="main">(</span><span class="bound">x</span><span class="main">)</span><span class="main">)</span> <span class="main">=</span> <span class="bound">x</span><span>"</span><span>
                    </span><span class="keyword2 keyword">and</span> hk<span class="main">:</span>  <span class="quoted"><span class="quoted"><span>"</span><span class="main">⋀</span><span class="bound">y</span><span class="main">.</span> <span class="bound">y</span> <span class="main">∈</span></span> sphere</span> <span class="skolem">z</span> <span class="main">1</span> <span class="main">∩</span> <span class="skolem">U</span> <span class="main">⟹</span> <span class="skolem">h</span><span class="main">(</span><span class="skolem">k</span><span class="main">(</span><span class="bound">y</span><span class="main">)</span><span class="main">)</span> <span class="main">=</span> <span class="bound">y</span><span>"</span><span>
    </span><span class="keyword1 command">unfolding</span> homeomorphic_def homeomorphism_def <span class="keyword1 command">by</span> <span class="operator">auto</span><span>
  </span><span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span>rel_frontier</span> <span class="free">S</span> <span class="main">-</span></span> <span class="main">{</span><span class="free">a</span><span class="main">}</span> <span class="keyword1">homeomorphic</span> <span class="main">(</span>sphere <span class="skolem">z</span> <span class="main">1</span> <span class="main">∩</span> <span class="skolem">U</span><span class="main">)</span> <span class="main">-</span> <span class="main">{</span><span class="skolem">h</span> <span class="free">a</span><span class="main">}</span><span>"</span><span>
  </span><span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">rule</span> homeomorphicI<span class="main">)</span><span>
    </span><span class="keyword3 command">show</span> h<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">h</span> <span class="main">`</span></span> <span class="main">(</span>rel_frontier</span> <span class="free">S</span> <span class="main">-</span> <span class="main">{</span><span class="free">a</span><span class="main">}</span><span class="main">)</span> <span class="main">=</span> sphere <span class="skolem">z</span> <span class="main">1</span> <span class="main">∩</span> <span class="skolem">U</span> <span class="main">-</span> <span class="main">{</span><span class="skolem">h</span> <span class="free">a</span><span class="main">}</span><span>"</span><span>
      </span><span class="keyword1 command">using</span> him a kh <span class="keyword1 command">by</span> <span class="operator">auto</span> <span class="operator">metis</span><span>
    </span><span class="keyword3 command">show</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">k</span> <span class="main">`</span></span> <span class="main">(</span>sphere</span> <span class="skolem">z</span> <span class="main">1</span> <span class="main">∩</span> <span class="skolem">U</span> <span class="main">-</span> <span class="main">{</span><span class="skolem">h</span> <span class="free">a</span><span class="main">}</span><span class="main">)</span> <span class="main">=</span> rel_frontier <span class="free">S</span> <span class="main">-</span> <span class="main">{</span><span class="free">a</span><span class="main">}</span><span>"</span><span>
      </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">force</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> h <span class="main main">[</span><span class="operator">symmetric</span><span class="main main">]</span> image_comp o_def kh<span class="main">)</span><span>
  </span><span class="keyword1 command">qed</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">intro</span><span class="main main">:</span> continuous_on_subset hcon kcon <span class="quasi_keyword">simp</span><span class="main main">:</span> kh hk<span class="main">)</span><span>
  </span><span class="keyword1 command">also</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">...</span> <span class="keyword1">homeomorphic</span></span> <span class="free">T</span><span>"</span></span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">rule</span> homeomorphic_punctured_affine_sphere_affine<span class="main">)</span><span>
       </span><span class="main">(</span><span class="operator">use</span> a him <span class="keyword2 keyword quasi_keyword">in</span> <span class="quoted"><span>‹</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> affS</span> affdS <span class="quoted"><span class="quoted"><span>‹</span>affine</span> <span class="free">T</span><span>›</span></span> <span class="quoted"><span class="quoted"><span>‹</span>affine</span> <span class="skolem">U</span><span>›</span></span> <span class="quoted"><span class="quoted"><span>‹</span><span class="skolem">z</span> <span class="main">∈</span></span> <span class="skolem">U</span><span>›</span></span><span>›</span><span class="main">)</span><span>
  </span><span class="keyword1 command">finally</span> <span class="keyword3 command">show</span> <span class="var quoted var">?thesis</span> <span class="keyword1 command">.</span><span>
</span><span class="keyword1 command">qed</span>
</pre>

In the Isabelle proof, we can see that the first step is to obtain an affine and convex set `U`. We prove the set `S` to be nonempty and from that obtain a specific element `z` belonging to `U`.
The argument continues with intelligible steps:
a chain of sets all homeomorphic to one another.
The ported proof is not only more legible than the original but it's actually shorter, at 42 lines instead of 50; this doesn't always happen.


### A WLOG example

Many proofs contain the phrase *without loss of generality*.
Sometimes it's a mere appeal to symmetry: if $x\not=y$ then it is okay to assume that in fact $x<y$, provided the claim being proved is unchanged when $x$ and $y$ are swapped.
The concept of WLOG is impossible to make precise; it involves an intuitive feeling that the essence of the proof of some statement is also present in the proof of some similar statement.
Remember, *all* theorems are equivalent.

John Harrison's paper ["Without Loss of Generality"](https://rdcu.be/cU7YV)
describes a suite of tactics in HOL Light for handling common cases of WLOG reasoning, with a focus on geometry.
They are powerful tools in the hands of a HOL Light user and a nasty surprise to somebody trying to port these proofs.
They transform the goal in a way that is often hard to work out in your head, creating one of the few occasions when it's really necessary to launch HOL Light to figure out what is going on.

The following example states that a connected set in Euclidean space
is uncountable if it contains two distinct points $a$ and $b$.
The first step assumes that $b$ lies on the Origin, and the second step assumes that $a$ lies on the unit circle. Damn.

<pre class="source">
let CARD_EQ_CONNECTED = prove
 (`!s a b:real^N.
        connected s /\ a IN s /\ b IN s /\ ~(a = b) ==> s =_c (:real)`,
  GEOM_ORIGIN_TAC `b:real^N` THEN GEOM_NORMALIZE_TAC `a:real^N` THEN
  REWRITE_TAC[NORM_EQ_SQUARE; REAL_POS; REAL_POW_ONE] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM CARD_LE_ANTISYM] THEN CONJ_TAC THENL
   [TRANS_TAC CARD_LE_TRANS `(:real^N)` THEN
    SIMP_TAC[CARD_LE_UNIV; CARD_EQ_EUCLIDEAN; CARD_EQ_IMP_LE];
    TRANS_TAC CARD_LE_TRANS `interval[vec 0:real^1,vec 1]` THEN CONJ_TAC THENL
     [MATCH_MP_TAC(ONCE_REWRITE_RULE[CARD_EQ_SYM] CARD_EQ_IMP_LE) THEN
      SIMP_TAC[UNIT_INTERVAL_NONEMPTY; CARD_EQ_INTERVAL];
      REWRITE_TAC[LE_C] THEN EXISTS_TAC `\x:real^N. lift(a dot x)` THEN
      SIMP_TAC[FORALL_LIFT; LIFT_EQ; IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC CONNECTED_IVT_HYPERPLANE THEN
      MAP_EVERY EXISTS_TAC [`vec 0:real^N`; `a:real^N`] THEN
      ASM_REWRITE_TAC[DOT_RZERO]]]);;
</pre>

This is one of those occasions when it's best to give up.
Because I could understand what the theorem was claiming, I could find another proof.
It's actually more general than the original, holding for all metric spaces.
It relies on the fact that the function $d(a,{-})$, which maps an arbitrary $x$ to its distance $d(a,x)$ from $a$ is continuous, reducing the uncountability of $S$ to that of the closed interval $[0,d(a,b)]$.
Remember that the operator ( \` ) denotes image, so 
<span class="source">dist</span> <span class="free">a</span>&ensp;`&ensp;S
denotes the image of $d(a,{-})$ under $S$.
This image is uncountable, so the conclusion follows.

<pre class="source">
<span class="keyword1 command">lemma</span> connected_uncountable<span class="main">:</span><span>
  </span><span class="keyword2 keyword">fixes</span> <span class="free">S</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span><span class="tfree">'a</span><span class="main">::</span>metric_space</span> set</span><span>"</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span>connected</span> <span class="free">S</span><span>"</span></span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">a</span> <span class="main">∈</span></span> <span class="free">S</span><span>"</span></span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">b</span> <span class="main">∈</span></span> <span class="free">S</span><span>"</span></span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">a</span> <span class="main">≠</span></span> <span class="free">b</span><span>"</span></span> <span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span>uncountable</span> <span class="free">S</span><span>"</span></span><span>
</span><span class="keyword1 command">proof</span> <span class="operator">-</span><span>
  </span><span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span>continuous_on</span> <span class="free">S</span> <span class="main">(</span>dist</span> <span class="free">a</span><span class="main">)</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">intro</span> <span class="dynamic dynamic">continuous_intros</span><span class="main">)</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span>connected</span> <span class="main">(</span>dist</span> <span class="free">a</span> <span class="main">`</span> <span class="free">S</span><span class="main">)</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> connected_continuous_image <span class="quoted"><span class="quoted"><span>‹</span>connected</span> <span class="free">S</span><span>›</span></span><span class="main">)</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span>closed_segment</span> <span class="main">0</span></span> <span class="main">(</span>dist <span class="free">a</span> <span class="free">b</span><span class="main">)</span> <span class="main">⊆</span> <span class="main">(</span>dist <span class="free">a</span> <span class="main">`</span> <span class="free">S</span><span class="main">)</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> assms closed_segment_subset is_interval_connected_1 is_interval_convex<span class="main">)</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span>uncountable</span> <span class="main">(</span>dist</span> <span class="free">a</span> <span class="main">`</span> <span class="free">S</span><span class="main">)</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> <span class="quoted"><span class="quoted"><span>‹</span><span class="free">a</span> <span class="main">≠</span></span> <span class="free">b</span><span>›</span></span> countable_subset dist_eq_0_iff uncountable_closed_segment<span class="main">)</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="var quoted var">?thesis</span><span>
    </span><span class="keyword1 command">by</span> <span class="operator">blast</span><span>
</span><span class="keyword1 command">qed</span>
</pre>

### Concluding thoughts

A big drawback of these analysis libraries, both the HOL Light originals
and the ported versions, is that the use of types was focused much more on convenience than flexibility.
Already HOL Light include some attempts to generalise the material beyond $\mathbb{R}^n$, and the same is needed in Isabelle/HOL.
Fortunately, because the ported proofs have a legible structure, the effort needed to do this might not be too great.
Anybody who wants to steal the Isabelle/HOL library will have the advantage (compared with stealing from HOL Light) that the mathematical argument is right in front of their eyes.

As for the story that started this blog post, some people have asked me how I could allow one of my own students to use something other than Isabelle. The reason is this: while we researchers should eat our own dog food, we shouldn't force it on others.
