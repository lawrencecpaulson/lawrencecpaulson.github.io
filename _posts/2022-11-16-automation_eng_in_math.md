---
layout: post
title:  "Automation and engineering in mathematics, by Pedro Sánchez Terraf"
usemathjax: true
tags: [Isar, formalised mathematics, proof documents, automation]
---

The interaction between Mathematics and Computer Science has grown
deeper, even philosophically, with the use of proof assistants. The
bonds made apparent by this connection highlight important lessons
that we mathematicians have to learn from CS; and it is also important
to discuss how different coding styles might help (or hinder)
consolidating formalisation technology as a tool for the present and
future generations of researchers and teachers of mathematics.

### Acknowledging engineering

Formalisation of mathematics serves many purposes—some of them have been
discussed in [this blog]({% post_url 2022-06-22-Why-formalise %}).  As
a mathematician, it helped me to realise a bit of “computer science
illiteracy” we suffer: We have to come into terms with the idea that
the development and, even more importantly, the **presentation** of a
complex piece of mathematics requires similar engineering skills as
those needed to conduct a large software project.

Preparing material in order to make a formal version of it exposes
many issues of this sort; I believe it is enlightening to put your own
mathematical prose to this test. This goes beyond math typos or subtle
(and gross) omissions, which are the first things that pop to the eye
of the proof assistant; failures in the coherence of structure and
organisation will backfire in the worst possible ways.

In summary, I believe we mathematicians have to learn engineering from
computer scientists; it is a kind of discipline that some people
naturally develop, but it should be made explicit in our education.

### The Devil is in the details

The lack of acknowledgement of the extent of engineering issues involved
in mathematical writing seems to be commonplace. The second practice I
am about to criticise is hopefully restricted to a rather smaller (and
elder) subset of our community: The deliberate concealing of details.

I have sadly heard, more than once, that some arguments in research
papers should be omitted with the sole purpose of “not looking dumb”
to the referees. There is a shared responsibility here; some reviewers
reinforce this situation by declaring “trivial” those results that
follow by a slick argument, rather than trying the author's shoes and
traverse the circuitous path that lead to that proof.

The coding of mathematics in proof assistants is in tension between
two related forces. One responds to the eagerness to formalise as swiftly
as possible; the other aims to produce libraries that are closer to
the human reader. *Isar*, the Isabelle dialect for writing
“declarative” proofs, is one of the greatest achievements that
facilitates the latter goal. The main point of the *proof documents*
obtained using Isar is that the very same formalisation provides an
exposition of the mathematical arguments; if written with care, you
won't need to add more explanations than the typical informal comments
included in a journal paper.

Isabelle also offers tools to fulfil the goal of fast formalisation,
through its extremely powerful automation; the main feature is the
seamless integration of automated theorem provers through the
Sledgehammer tool. Actually, the previous assertion must be qualified:
“Isabelle,” literally, is a *generic* proof assistant, capable of
supporting a variety of logics. By a huge advantage, HOL is the most
popular one, and hammers and counterexample synthesis is (to this day)
only available for that logic.

### Against automation

I am obviously overacting this section's title. But there is a bit of
truth in it, regarding the goal of building readable or *didactic*
libraries of formalised mathematics.

Sometimes, the ability of powerful automation to find proofs can
surprise a human prover (at least, it has surprised me). My experience
is mostly restricted to [Isabelle/ZF]({% post_url 2022-01-26-Set_theory %}),
where support for `sledgehammer` has not
arrived yet. Nevertheless, Isabelle-wide tools like `auto` and `blast`
(brainchilds of the [creator of this
blog](https://www.cl.cam.ac.uk/~lp15/)) work great.

I would like to discuss to this effect a
[result](https://www.isa-afp.org/theories/independence_ch/#Forcing_Theorems.html#Forcing_Theorems.forcing_data1.strengthening_eq|fact)
that is part of
[a development](https://arxiv.org/abs/2210.15609) of
the set-theoretic technique of *forcing* (a joint work with Gunther,
Pagano, and Steinberg).

I need to say that in forcing we
work with a partial (quasi)ordered set
$\langle\mathbb{P},\preccurlyeq\rangle$ whose elements codify partial information of
a (first-order) model one is trying to approximate. The relation $r
\preccurlyeq p$ is to be read “$r$ carries more information than $p$” (in
that order!). Then, intuitively, once we know that the *condition* $p$
yields $t_1 = t_2$, (“*forces*” it to hold in the target model), it
must be true that $r$ also forces $t_1 = t_2$. That's the content of
the aforementioned result:

<pre class="source">
<span class="keyword1 command">lemma</span> strengthening_eq<span class="main">:</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted quoted"><span>"</span><span class="free">p</span> <span class="main">∈</span> <span class="main free">ℙ</span><span>"</span></span> <span class="quoted quoted"><span>"</span><span class="free">r</span> <span class="main">∈</span> <span class="main free">ℙ</span><span>"</span></span> <span class="quoted quoted"><span>"</span><span class="free">r</span> <span class="main">≼</span> <span class="free">p</span><span>"</span></span> <span class="quoted quoted"><span>"</span><span class="free">p</span> <span class="keyword1">forces<span class="hidden">⇩</span><sub>a</sub></span> <span class="main">(</span><span class="free">t1</span> <span class="main">=</span> <span class="free">t2</span><span class="main">)</span><span>"</span></span><span>
  </span><span class="keyword2 keyword">shows</span> <span class="quoted quoted"><span>"</span><span class="free">r</span> <span class="keyword1">forces<span class="hidden">⇩</span><sub>a</sub></span> <span class="main">(</span><span class="free">t1</span> <span class="main">=</span> <span class="free">t2</span><span class="main">)</span><span>"</span></span>
</pre>The variables $t_1$ and $t_2$ actually stand for *names* (which are sets of ordered pairs with second component in $\mathbb{P}$) of elements of the target model, and what is actually forced is the equality of the elements named by them. The definition of the forcing relation is one of the most delicate issues in this topic. Forcing an equality is defined in terms of the forcing of a membership relation (it is a mutual recursion):
  <pre class="source">
<span class="keyword1 command">lemma</span> def_forces_eq<span class="main">:</span> <span class="quoted quoted"><span>"</span><span class="free">p</span><span class="main">∈</span><span class="main free">ℙ</span> <span class="main">⟹</span> <span class="free">p</span> <span class="keyword1">forces<span class="hidden">⇩</span><sub>a</sub></span> <span class="main">(</span><span class="free">t1</span> <span class="main">=</span> <span class="free">t2</span><span class="main">)</span> <span class="main">⟷</span><span>
  </span><span class="main">(</span><span class="main">∀</span><span class="bound">s</span><span class="main">∈</span>domain<span class="main">(</span><span class="free">t1</span><span class="main">)</span> <span class="main">∪</span> domain<span class="main">(</span><span class="free">t2</span><span class="main">)</span><span class="main">.</span> <span class="main">∀</span><span class="bound">q</span><span class="main">.</span> <span class="bound">q</span><span class="main">∈</span><span class="main free">ℙ</span> <span class="main">∧</span> <span class="bound">q</span> <span class="main">≼</span> <span class="free">p</span> <span class="main">⟶</span><span>
  </span><span class="main">(</span><span class="bound">q</span> <span class="keyword1">forces<span class="hidden">⇩</span><sub>a</sub></span> <span class="main">(</span><span class="bound">s</span> <span class="main">∈</span> <span class="free">t1</span><span class="main">)</span> <span class="main">⟷</span> <span class="bound">q</span> <span class="keyword1">forces<span class="hidden">⇩</span><sub>a</sub></span> <span class="main">(</span><span class="bound">s</span> <span class="main">∈</span> <span class="free">t2</span><span class="main">)</span><span class="main">)</span><span class="main">)</span><span>"</span></span>
</pre>Hence, to prove that some $r$ forces $t_1 = t_2$, we have to prove that for all $s$ in the union of those domains, the $q$s below $r$ that force the respective memberships are the same. Now, the proof of `strengthening_eq`:
  <pre class="source">
<span class="keyword1 command">proof</span> <span class="operator">-</span><span>
  </span><span class="keyword1 command">{</span><span>
    </span><span class="keyword3 command">fix</span> <span class="skolem">s</span> <span class="skolem">q</span><span>
    </span><span class="keyword3 command">assume</span> <span class="quoted quoted"><span>"</span><span class="skolem">q</span> <span class="main">≼</span> <span class="free">r</span><span>"</span></span> <span class="quoted quoted"><span>"</span><span class="skolem">q</span> <span class="main">∈</span> <span class="main free">ℙ</span><span>"</span></span>
</pre>Since we are assuming that $r$ is below $p$,
  <pre class="source">
    <span class="keyword1 command">with</span> assms
    <span class="keyword1 command">have</span> <span class="quoted quoted"><span>"</span><span class="skolem">q</span> <span class="main">≼</span> <span class="free">p</span><span>"</span></span><span>
      </span><span class="keyword1 command">using</span> leq_preord <span class="keyword1 command">unfolding</span> preorder_on_def trans_on_def <span class="keyword1 command">by</span> <span class="operator">blast</span>
</pre>then $q$ must be below $p$ by transitivity.
  <pre class="source">
    <span class="keyword1 command">moreover</span><span>
    </span><span class="keyword1 command">note</span> <span class="quoted quoted"><span>‹</span><span class="skolem">q</span> <span class="main">∈</span> <span class="main free">ℙ</span><span>›</span></span> assms<span>
    </span><span class="keyword1 command">moreover</span><span>
    </span><span class="keyword3 command">assume</span> <span class="quoted quoted"><span>"</span><span class="skolem">s</span> <span class="main">∈</span> domain<span class="main">(</span><span class="free">t1</span><span class="main">)</span> <span class="main">∪</span> domain<span class="main">(</span><span class="free">t2</span><span class="main">)</span><span>"</span></span>
</pre>An application of `def_forces_eq` for arguments `p`, `t1`, and `t2` allows to
  <pre class="source">
    <span class="keyword1 command">ultimately</span><span>
    </span><span class="keyword1 command">have</span> <span class="quoted quoted"><span>"</span><span class="skolem">q</span> <span class="keyword1">forces<span class="hidden">⇩</span><sub>a</sub></span> <span class="main">(</span><span class="skolem">s</span> <span class="main">∈</span> <span class="free">t1</span><span class="main">)</span> <span class="main">⟷</span> <span class="skolem">q</span> <span class="keyword1">forces<span class="hidden">⇩</span><sub>a</sub></span> <span class="main">(</span><span class="skolem">s</span> <span class="main">∈</span> <span class="free">t2</span><span class="main">)</span><span>"</span></span><span>
      </span><span class="keyword1 command">using</span> def_forces_eq<span class="main">[</span><span class="operator">of</span> <span class="quoted free">p</span> <span class="quoted free">t1</span> <span class="quoted free">t2</span><span class="main">]</span> <span class="keyword1 command">by</span> <span class="operator">simp</span><span>
  </span><span class="keyword1 command">}</span>
</pre>and another one, this time for `r`, gives us the conclusion:
  <pre class="source">
  <span class="keyword1 command">with</span> <span class="quoted quoted"><span>‹</span><span class="free">r</span><span class="main">∈</span><span class="main free">ℙ</span><span>›</span></span><span>
  </span><span class="keyword3 command">show</span> <span class="var quoted var">?thesis</span> <span class="keyword1 command">using</span> def_forces_eq<span class="main">[</span><span class="operator">of</span> <span class="quoted free">r</span> <span class="quoted free">t1</span> <span class="quoted free">t2</span><span class="main">]</span> <span class="keyword1 command">by</span> <span class="operator">blast</span><span>
</span><span class="keyword1 command">qed</span>
</pre>This is actually the first proof I wrote of this lemma. It is rather verbose, and I tried to simplify it a bit. At last, I arrived to the following,
  <pre class="source">
<span class="keyword1 command">lemma</span> strengthening_eq<span class="main">:</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted quoted"><span>"</span><span class="free">p</span> <span class="main">∈</span> <span class="main free">ℙ</span><span>"</span></span> <span class="quoted quoted"><span>"</span><span class="free">r</span> <span class="main">∈</span> <span class="main free">ℙ</span><span>"</span></span> <span class="quoted quoted"><span>"</span><span class="free">r</span> <span class="main">≼</span> <span class="free">p</span><span>"</span></span> <span class="quoted quoted"><span>"</span><span class="free">p</span> <span class="keyword1">forces<span class="hidden">⇩</span><sub>a</sub></span> <span class="main">(</span><span class="free">t1</span> <span class="main">=</span> <span class="free">t2</span><span class="main">)</span><span>"</span></span><span>
  </span><span class="keyword2 keyword">shows</span> <span class="quoted quoted"><span>"</span><span class="free">r</span> <span class="keyword1">forces<span class="hidden">⇩</span><sub>a</sub></span> <span class="main">(</span><span class="free">t1</span> <span class="main">=</span> <span class="free">t2</span><span class="main">)</span><span>"</span></span><span>
  </span><span class="keyword1 command">using</span> assms def_forces_eq<span class="main">[</span><span class="operator">of</span> <span class="main">_</span> <span class="quoted free">t1</span> <span class="quoted free">t2</span><span class="main">]</span> leq_transD <span class="keyword1 command">by</span> <span class="operator">blast</span>
</pre>where the transitivity part is now handled by `leq_transD`:
  <pre class="source">
<span class="keyword1 command">lemma</span> leq_transD<span class="main">:</span>  <span class="quoted quoted"><span>"</span><span class="free">a</span><span class="main">≼</span><span class="free">b</span> <span class="main">⟹</span> <span class="free">b</span><span class="main">≼</span><span class="free">c</span> <span class="main">⟹</span> <span class="free">a</span> <span class="main">∈</span> <span class="main free">ℙ</span><span class="main">⟹</span> <span class="free">b</span> <span class="main">∈</span> <span class="main free">ℙ</span><span class="main">⟹</span> <span class="free">c</span> <span class="main">∈</span> <span class="main free">ℙ</span><span class="main">⟹</span> <span class="free">a</span><span class="main">≼</span><span class="free">c</span><span>"</span></span><span>
  </span><span class="keyword1 command">using</span> leq_preord trans_onD <span class="keyword1 command">unfolding</span> preorder_on_def <span class="keyword1 command">by</span> <span class="operator">blast</span>
</pre>

The second proof of `strengthening_eq` is much shorter. We could also
say that it is more elegant. The only objection is that if we also aim
that this text might be used for a first exposition to forcing, it
would be better if all the details were spelled out.

I believe that the builders of grand libraries of formalised
mathematics should take this point into account in a serious way. My
heart feeling is that those libraries should not aim for the shortest
or quickest *code*, but instead for the best *text*. I hope that other
proof assistants follow the lead of Isabelle/Isar by favouring proof
scripts that explain themselves over the usual “commented, cryptic
code” which is more popular in other programming languages. Only in
this way, formalised mathematics might serve greater purposes directly
for human mathematicians, and not only as a intermediary to other
technologies.

*This is a guest post by [Pedro Sánchez Terraf](https://cs.famaf.unc.edu.ar/~pedro). 
Please let me know if you are interested in contributing a post of your own.*
