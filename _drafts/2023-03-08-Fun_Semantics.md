---
layout: post
title:  "Semantics of a simple functional language"
usemathjax: true 
tags: [examples, Isabelle]
---

[*Concrete Semantics*](http://www.concrete-semantics.org)




* The GCD of $x$ and 0 is $x$.
* If the GCD of $x$ and $y$ is $z$, then the GCD of $2x$ and $2y$ is $2z$.
* The GCD of $2x$ and $y$ is the same as that of $x$ and $y$ if $y$ is odd.
* The GCD of $x$ and $y$ is the same as that of $x-y$ and $y$ if $y\le x$.
* The GCD of $x$ and $y$ is the same as the GCD of $y$ and $x$.

This system of rules corresponds precisely to an Isabelle/HOL inductive definition. Note that we are defining a 3-argument relation
rather than a 2-argument function.
That's because frequently more than one of these cases is
applicable, so it is not immediately obvious that they express a
function. 

<pre class="source">
<span class="keyword1 command">datatype</span> exp <span class="main">=</span> T <span class="main">|</span> F <span class="main">|</span> Zero <span class="main">|</span> Succ <span class="quoted">exp</span> <span class="main">|</span> IF <span class="quoted">exp</span> <span class="quoted">exp</span> <span class="quoted">exp</span> <span class="main">|</span> EQ <span class="quoted">exp</span> <span class="quoted">exp</span>
</pre>

<pre class="source">
<span class="keyword1 command">inductive</span> <span class="entity">Eval</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>exp</span> <span class="main">⇒</span> exp</span> <span class="main">⇒</span> bool<span>"</span> <span class="main">(</span><span class="keyword2 keyword">infix</span> <span class="quoted"><span>"</span><span class="keyword1">⇛</span><span>"</span></span> 50<span class="main">)</span> <span class="keyword2 keyword">where</span><span>
    </span>IF_T<span class="main">:</span>    <span class="quoted"><span class="quoted"><span>"</span>IF</span> T</span> <span class="free bound entity">x</span> <span class="free bound entity">y</span> <span class="main free">⇛</span> <span class="free bound entity">x</span><span>"</span><span>
  </span><span class="main">|</span> IF_F<span class="main">:</span>    <span class="quoted"><span class="quoted"><span>"</span>IF</span> F</span> <span class="free bound entity">x</span> <span class="free bound entity">y</span> <span class="main free">⇛</span> <span class="free bound entity">y</span><span>"</span><span>
  </span><span class="main">|</span> IF_Eval<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free bound entity">p</span> <span class="main free">⇛</span> <span class="free bound entity">q</span> <span class="main">⟹</span> IF</span> <span class="free bound entity">p</span> <span class="free bound entity">x</span> <span class="free bound entity">y</span> <span class="main free">⇛</span> IF</span> <span class="free bound entity">q</span> <span class="free bound entity">x</span> <span class="free bound entity">y</span><span>"</span><span>
  </span><span class="main">|</span> Succ_Eval<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free bound entity">x</span> <span class="main free">⇛</span> <span class="free bound entity">y</span> <span class="main">⟹</span> Succ</span> <span class="free bound entity">x</span> <span class="main free">⇛</span> Succ</span> <span class="free bound entity">y</span><span>"</span><span>
  </span><span class="main">|</span> EQ_same<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>EQ</span> <span class="free bound entity">x</span> <span class="free bound entity">x</span> <span class="main free">⇛</span> T</span><span>"</span><span>
  </span><span class="main">|</span> EQ_S0<span class="main">:</span>   <span class="quoted"><span class="quoted"><span>"</span>EQ</span> <span class="main">(</span>Succ</span> <span class="free bound entity">x</span><span class="main">)</span> Zero <span class="main free">⇛</span> F<span>"</span><span>
  </span><span class="main">|</span> EQ_0S<span class="main">:</span>   <span class="quoted"><span class="quoted"><span>"</span>EQ</span> Zero</span> <span class="main">(</span>Succ <span class="free bound entity">y</span><span class="main">)</span> <span class="main free">⇛</span> F<span>"</span><span>
  </span><span class="main">|</span> EQ_SS<span class="main">:</span>   <span class="quoted"><span class="quoted"><span>"</span>EQ</span> <span class="main">(</span>Succ</span> <span class="free bound entity">x</span><span class="main">)</span> <span class="main">(</span>Succ <span class="free bound entity">y</span><span class="main">)</span> <span class="main free">⇛</span> EQ <span class="free bound entity">x</span> <span class="free bound entity">y</span><span>"</span><span>
  </span><span class="main">|</span> EQ_Eval1<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free bound entity">x</span> <span class="main free">⇛</span> <span class="free bound entity">z</span> <span class="main">⟹</span> EQ</span> <span class="free bound entity">x</span> <span class="free bound entity">y</span> <span class="main free">⇛</span> EQ</span> <span class="free bound entity">z</span> <span class="free bound entity">y</span><span>"</span><span>
  </span><span class="main">|</span> EQ_Eval2<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free bound entity">y</span> <span class="main free">⇛</span> <span class="free bound entity">z</span> <span class="main">⟹</span> EQ</span> <span class="free bound entity">x</span> <span class="free bound entity">y</span> <span class="main free">⇛</span> EQ</span> <span class="free bound entity">x</span> <span class="free bound entity">z</span><span>"</span>
</pre>

<pre class="source">
<span class="keyword1 command">inductive_simps</span> T_simp <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>T</span> <span class="main">⇛</span></span> <span class="free">z</span><span>"</span><span>
</span><span class="keyword1 command">inductive_simps</span> F_simp <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>F</span> <span class="main">⇛</span></span> <span class="free">z</span><span>"</span><span>
</span><span class="keyword1 command">inductive_simps</span> Zero_simp <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>Zero</span> <span class="main">⇛</span></span> <span class="free">z</span><span>"</span><span>
</span><span class="keyword1 command">inductive_simps</span> Succ_simp <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>Succ</span> <span class="free">x</span> <span class="main">⇛</span></span> <span class="free">z</span><span>"</span><span>
</span><span class="keyword1 command">inductive_simps</span> IF_simp <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>IF</span> <span class="free">p</span> <span class="free">x</span> <span class="free">y</span> <span class="main">⇛</span></span>  <span class="free">z</span><span>"</span><span>
</span><span class="keyword1 command">inductive_simps</span> EQ_simp <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>EQ</span> <span class="free">x</span> <span class="free">y</span> <span class="main">⇛</span></span> <span class="free">z</span><span>"</span>
</pre>

<pre class="source">
<span class="keyword1 command">datatype</span> tp <span class="main">=</span> bool <span class="main">|</span> num
</pre>

<pre class="source">
<span class="keyword1 command">inductive</span> <span class="entity">TP</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>exp</span> <span class="main">⇒</span> tp</span> <span class="main">⇒</span> bool<span>"</span> <span class="keyword2 keyword">where</span><span>
  </span>T<span class="main">:</span>    <span class="quoted"><span class="quoted"><span>"</span><span class="free">TP</span> T</span> bool</span><span>"</span><span>
</span><span class="main">|</span> F<span class="main">:</span>    <span class="quoted"><span class="quoted"><span>"</span><span class="free">TP</span> F</span> bool</span><span>"</span><span>
</span><span class="main">|</span> Zero<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">TP</span> Zero</span> num</span><span>"</span><span>
</span><span class="main">|</span> IF<span class="main">:</span>   <span class="quoted"><span class="quoted"><span>"</span><span class="main">⟦</span><span class="free">TP</span> <span class="free bound entity">p</span> bool</span><span class="main">;</span> <span class="free">TP</span> <span class="free bound entity">x</span> <span class="free bound entity">t</span><span class="main">;</span> <span class="free">TP</span> <span class="free bound entity">y</span> <span class="free bound entity">t</span><span class="main">⟧</span> <span class="main">⟹</span> <span class="free">TP</span> <span class="main">(</span>IF</span> <span class="free bound entity">p</span> <span class="free bound entity">x</span> <span class="free bound entity">y</span><span class="main">)</span> <span class="free bound entity">t</span><span>"</span><span>
</span><span class="main">|</span> Succ<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">TP</span> <span class="free bound entity">x</span> num</span> <span class="main">⟹</span> <span class="free">TP</span> <span class="main">(</span>Succ</span> <span class="free bound entity">x</span><span class="main">)</span> num<span>"</span><span>
</span><span class="main">|</span> EQ<span class="main">:</span>   <span class="quoted"><span class="quoted"><span>"</span><span class="main">⟦</span><span class="free">TP</span> <span class="free bound entity">x</span> <span class="free bound entity">t</span><span class="main">;</span> <span class="free">TP</span> <span class="free bound entity">y</span> <span class="free bound entity">t</span><span class="main">⟧</span> <span class="main">⟹</span> <span class="free">TP</span> <span class="main">(</span>EQ</span> <span class="free bound entity">x</span> <span class="free bound entity">y</span><span class="main">)</span> bool</span><span>"</span>
</pre>

<pre class="source">
<span class="keyword1 command">inductive_simps</span> TP_IF <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>TP</span> <span class="main">(</span>IF</span> <span class="free">p</span> <span class="free">x</span> <span class="free">y</span><span class="main">)</span> <span class="free">t</span><span>"</span><span>
</span><span class="keyword1 command">inductive_simps</span> TP_Succ <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>TP</span> <span class="main">(</span>Succ</span> <span class="free">x</span><span class="main">)</span> <span class="free">t</span><span>"</span><span>
</span><span class="keyword1 command">inductive_simps</span> TP_EQ <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>TP</span> <span class="main">(</span>EQ</span> <span class="free">x</span> <span class="free">y</span><span class="main">)</span> <span class="free">t</span><span>"</span>
</pre>

<pre class="source">
<span class="keyword1 command">fun</span> <span class="entity">evl</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>exp</span> <span class="main">⇒</span> nat</span><span>"</span><span>
  </span><span class="keyword2 keyword">where</span><span>
    </span><span class="quoted"><span class="quoted"><span>"</span><span class="free">evl</span> T</span> <span class="main">=</span></span> <span class="main">1</span><span>"</span><span>
  </span><span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">evl</span> F</span> <span class="main">=</span></span> <span class="main">0</span><span>"</span><span>
  </span><span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">evl</span> Zero</span> <span class="main">=</span></span> <span class="main">0</span><span>"</span><span>
  </span><span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">evl</span> <span class="main">(</span>Succ</span> <span class="free bound entity">x</span><span class="main">)</span> <span class="main">=</span></span> <span class="free">evl</span> <span class="free bound entity">x</span> <span class="main">+</span> <span class="main">1</span><span>"</span><span>
  </span><span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">evl</span> <span class="main">(</span>IF</span> <span class="free bound entity">x</span> <span class="free bound entity">y</span> <span class="free bound entity">z</span><span class="main">)</span> <span class="main">=</span></span> <span class="main">(</span><span class="keyword1">if</span> <span class="free">evl</span> <span class="free bound entity">x</span> <span class="main">=</span> <span class="main">1</span> <span class="keyword1">then</span> <span class="free">evl</span> <span class="free bound entity">y</span> <span class="keyword1">else</span> <span class="free">evl</span> <span class="free bound entity">z</span><span class="main">)</span><span>"</span><span>
  </span><span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">evl</span> <span class="main">(</span>EQ</span> <span class="free bound entity">x</span> <span class="free bound entity">y</span><span class="main">)</span> <span class="main">=</span></span> <span class="main">(</span><span class="keyword1">if</span> <span class="free">evl</span> <span class="free bound entity">x</span> <span class="main">=</span> <span class="free">evl</span> <span class="free bound entity">y</span> <span class="keyword1">then</span> <span class="main">1</span> <span class="keyword1">else</span> <span class="main">0</span><span class="main">)</span><span>"</span>
</pre>

<pre class="source">
<span class="keyword1 command">proposition</span> type_preservation<span class="main">:</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">⇛</span></span> <span class="free">y</span><span>"</span></span> <span class="quoted"><span class="quoted"><span>"</span>TP</span> <span class="free">x</span> <span class="free">t</span><span>"</span></span> <span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span>TP</span> <span class="free">y</span> <span class="free">t</span><span>"</span></span><span>
  </span><span class="keyword1 command">using</span> assms<span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">induction</span> <span class="quoted free">x</span> <span class="quoted free">y</span> <span class="quasi_keyword">arbitrary</span><span class="main main">:</span> <span class="quoted free">t</span> <span class="quasi_keyword">rule</span><span class="main main">:</span> Eval.induct<span class="main">)</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> TP.intros<span class="main">)</span>
</pre>

<pre class="source">
<span class="keyword1 command">lemma</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span>TP</span> <span class="free">x</span> <span class="free">t</span><span>"</span></span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">t</span> <span class="main">=</span></span> bool</span><span>"</span> <span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span>evl</span> <span class="free">x</span> <span class="main">&lt;</span></span> <span class="numeral">2</span><span>"</span><span>
  </span><span class="keyword1 command">using</span> assms <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">induction</span> <span class="quoted free">x</span> <span class="quoted free">t</span><span class="main keyword3">;</span> <span class="operator">force</span><span class="main">)</span>
</pre>

<pre class="source">
<span class="keyword1 command">proposition</span> value_preservation<span class="main">:</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">⇛</span></span> <span class="free">y</span><span>"</span></span> <span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span>evl</span> <span class="free">x</span> <span class="main">=</span></span> evl <span class="free">y</span><span>"</span><span>
  </span><span class="keyword1 command">using</span> assms <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">induction</span> <span class="quoted free">x</span> <span class="quoted free">y</span><span class="main keyword3">;</span> <span class="operator">force</span><span class="main">)</span>
</pre>

<pre class="source">
<span class="keyword1 command">text</span> <span class="quoted plain_text"><span>‹</span><span>This doesn't hold</span><span>›</span></span><span>
</span><span class="keyword1 command">lemma</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">⇛</span></span> <span class="free">y</span><span>"</span></span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">⇛</span></span> <span class="free">z</span><span>"</span></span> <span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">∃</span></span><span class="bound">u</span><span class="main">.</span></span> <span class="free">y</span> <span class="main">⇛</span> <span class="bound">u</span> <span class="main">∧</span> <span class="free">z</span> <span class="main">⇛</span> <span class="bound">u</span><span>"</span><span>
  </span><span class="keyword1 command">nitpick</span><span>
  </span><span class="keyword1 command">oops</span>
</pre>

<pre class="source">
<span class="keyword1 command">inductive</span> <span class="entity">EvalStar</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>exp</span> <span class="main">⇒</span> exp</span> <span class="main">⇒</span> bool<span>"</span> <span class="main">(</span><span class="keyword2 keyword">infix</span> <span class="quoted"><span>"</span><span class="keyword1">⇛*</span><span>"</span></span> 50<span class="main">)</span> <span class="keyword2 keyword">where</span><span>
    </span>Id<span class="main">:</span> <span class="quoted quoted"><span>"</span><span class="free bound entity">x</span> <span class="main free">⇛*</span> <span class="free bound entity">x</span><span>"</span></span><span>
  </span><span class="main">|</span> Step<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free bound entity">x</span> <span class="main">⇛</span></span> <span class="free bound entity">y</span> <span class="main">⟹</span> <span class="free bound entity">y</span> <span class="main free">⇛*</span> <span class="free bound entity">z</span> <span class="main">⟹</span> <span class="free bound entity">x</span> <span class="main free">⇛*</span> <span class="free bound entity">z</span><span>"</span></span>
</pre>

<pre class="source">
<span class="keyword1 command">inductive_simps</span> T_EvalStar <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>T</span> <span class="main">⇛*</span></span> <span class="free">u</span><span>"</span><span>
</span><span class="keyword1 command">inductive_simps</span> F_EvalStar <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>F</span> <span class="main">⇛*</span></span> <span class="free">u</span><span>"</span>
</pre>

<pre class="source">
<span class="keyword1 command">proposition</span> type_preservation_Star<span class="main">:</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">⇛*</span></span> <span class="free">y</span><span>"</span></span> <span class="quoted"><span class="quoted"><span>"</span>TP</span> <span class="free">x</span> <span class="free">t</span><span>"</span></span> <span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span>TP</span> <span class="free">y</span> <span class="free">t</span><span>"</span></span><span>
  </span><span class="keyword1 command">using</span> assms<span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">induction</span> <span class="quoted free">x</span> <span class="quoted free">y</span><span class="main">)</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> type_preservation<span class="main">)</span>
</pre>

<pre class="source">
<span class="keyword1 command">lemma</span> Succ_EvalStar<span class="main">:</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">⇛*</span></span> <span class="free">y</span><span>"</span></span> <span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span>Succ</span> <span class="free">x</span> <span class="main">⇛*</span></span> Succ <span class="free">y</span><span>"</span><span>
  </span><span class="keyword1 command">using</span> assms <span class="keyword1 command">by</span> <span class="operator">induction</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">intro</span><span class="main main">:</span> Succ_Eval EvalStar.intros<span class="main">)</span>
</pre>

<pre class="source">
<span class="keyword1 command">lemma</span> IF_EvalStar<span class="main">:</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">p</span> <span class="main">⇛*</span></span> <span class="free">q</span><span>"</span></span> <span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span>IF</span> <span class="free">p</span> <span class="free">x</span> <span class="free">y</span> <span class="main">⇛*</span></span> IF <span class="free">q</span> <span class="free">x</span> <span class="free">y</span><span>"</span><span>
  </span><span class="keyword1 command">using</span> assms <span class="keyword1 command">by</span> <span class="operator">induction</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">intro</span><span class="main main">:</span> IF_Eval EvalStar.intros<span class="main">)</span>
</pre>

<pre class="source">
<span class="keyword1 command">lemma</span> EQ_EvalStar1<span class="main">:</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">⇛*</span></span> <span class="free">z</span><span>"</span></span> <span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span>EQ</span> <span class="free">x</span> <span class="free">y</span> <span class="main">⇛*</span></span> EQ <span class="free">z</span> <span class="free">y</span><span>"</span><span>
  </span><span class="keyword1 command">using</span> assms <span class="keyword1 command">by</span> <span class="operator">induction</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">intro</span><span class="main main">:</span> EQ_Eval1 EvalStar.intros<span class="main">)</span>
</pre>

<pre class="source">
<span class="keyword1 command">lemma</span> EQ_EvalStar2<span class="main">:</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">y</span> <span class="main">⇛*</span></span> <span class="free">z</span><span>"</span></span> <span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span>EQ</span> <span class="free">x</span> <span class="free">y</span> <span class="main">⇛*</span></span> EQ <span class="free">x</span> <span class="free">z</span> <span>"</span><span>
  </span><span class="keyword1 command">using</span> assms <span class="keyword1 command">by</span> <span class="operator">induction</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">intro</span><span class="main main">:</span> EQ_Eval2 EvalStar.intros<span class="main">)</span>
</pre>

<pre class="source">
<span class="keyword1 command">proposition</span> diamond<span class="main">:</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">⇛</span></span> <span class="free">y</span><span>"</span></span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">⇛</span></span> <span class="free">z</span><span>"</span></span> <span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">∃</span></span><span class="bound">u</span><span class="main">.</span></span> <span class="free">y</span> <span class="main">⇛*</span> <span class="bound">u</span> <span class="main">∧</span> <span class="free">z</span> <span class="main">⇛*</span> <span class="bound">u</span><span>"</span><span>
  </span><span class="keyword1 command">using</span> assms<span>
</span><span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">induction</span> <span class="quoted free">x</span> <span class="quoted free">y</span> <span class="quasi_keyword">arbitrary</span><span class="main main">:</span> <span class="quoted free">z</span><span class="main">)</span><span>
  </span><span class="keyword3 command">case</span> <span class="main">(</span>IF_Eval <span class="skolem">p</span> <span class="skolem">q</span> <span class="skolem">x</span> <span class="skolem">y</span><span class="main">)</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="var quoted var">?case</span><span>
    </span><span class="keyword1 command">by</span> <span class="operator">simp</span> <span class="main">(</span><span class="operator">meson</span> F_simp IF_EvalStar T_simp<span class="main">)</span><span>
</span><span class="keyword1 command">next</span><span>
  </span><span class="keyword3 command">case</span> <span class="main">(</span>EQ_SS <span class="skolem">x</span> <span class="skolem">y</span><span class="main">)</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="var quoted var">?case</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">auto</span><span class="main keyword3">;</span> <span class="operator">metis</span> Eval.intros EvalStar.intros<span class="main">)</span><span>
</span><span class="keyword1 command">next</span><span>
  </span><span class="keyword3 command">case</span> <span class="main">(</span>EQ_Eval1 <span class="skolem">x</span> <span class="skolem">u</span> <span class="skolem">y</span><span class="main">)</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="var quoted var">?case</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">auto</span><span class="main keyword3">;</span> <span class="operator">metis</span> EQ_EvalStar1 Eval.intros EvalStar.intros<span class="main">)</span><span class="main keyword3">+</span><span>
</span><span class="keyword1 command">next</span><span>
    </span><span class="keyword3 command">case</span> <span class="main">(</span>EQ_Eval2 <span class="skolem">y</span> <span class="skolem">u</span> <span class="skolem">x</span><span class="main">)</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="var quoted var">?case</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">auto</span><span class="main keyword3">;</span> <span class="operator">metis</span> EQ_EvalStar2 Eval.intros EvalStar.intros<span class="main">)</span><span class="main keyword3">+</span><span>
</span><span class="keyword1 command">qed</span> <span class="main">(</span><span class="operator">force</span> <span class="quasi_keyword">intro</span><span class="main main">:</span> Succ_EvalStar Eval.intros EvalStar.intros<span class="main">)</span><span class="main keyword3">+</span>
</pre>

The inductive definition is abstract, but the corresponding
algorithm isn't hard to see.
If one operand is zero, then return the other;
if both operands are even, then divide by two, obtain the GCD recursively
and then double it; 
if only one of the operands is even then divide it by 2;
if both of the operands are odd, then subtract the smaller from the larger. Testing whether an integer is even or odd, and dividing it by two,
is a trivial binary shift.

This example is based on an assignment set in 2010 for my late,
lamented MPhil course, [Interactive Formal Verification](https://www.cl.cam.ac.uk/teaching/2122/L21/).
The Isabelle theory file [can be downloaded](/Isabelle-Examples/Fun_Semantics.thy).


