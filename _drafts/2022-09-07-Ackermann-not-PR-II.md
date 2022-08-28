---
layout: post
title:  "Ackermann's function is not primitive recursive, II"
usemathjax: true
tags: [examples, Isabelle, Ackermann's function, inductive definitions]
---

The [previous post]({% post_url 2022-08-31-Ackermann-not-PR-I %})
presented the first half of the proof that Ackermann's function $A(i,j)$ is not primitive recursive: a series of inequalities describing how the function grows with various arguments.
In this post, we'll see how to define the [primitive recursive functions](https://plato.stanford.edu/entries/recursive-functions/#PrimRecuFuncPR) inductively.
Using the aforementioned inequalities, it will be straightforward to prove
(by induction on the construction of some PR function *f*) that we can always find an argument to dominate *f*.
This celebrated result has an easy proof, and it provides a distinctive example
of an inductive definition.


### The primitive recursive functions

I'm assuming that you have already encountered the PR functions in some course on computation theory. If not, the [Wikipedia article](https://en.wikipedia.org/wiki/Primitive_recursive_function)
is an excellent overview.
They are a family of $k$-ary functions over the natural numbers, for all $k$, including the following:

* The *successor function* $S:\mathbb{N}\to\mathbb{N}$ such that
$S(x)=x+1$
* *Constant functions* $C^k_n:\mathbb{N}^k\to\mathbb{N}$ such that
$C^k_n(x_1,\ldots,x_k)=n$
* *Projection functions* $P^k_i:\mathbb{N}^k\to\mathbb{N}$ such that
$P^k_i(x_1,\ldots,x_k)=x_i$

The primitive recursive functions are closed under the following two operations:

* The *composition* $h\circ(g_1,\ldots,g_m)$ of an $m$-ary function $h$ and $k$-ary functions $g_1,\ldots,g_m$ denotes some $f$ such that
$$ f(x_1,\ldots,x_k)=h(g_1(x_1,\ldots ,x_k),\ldots ,g_m(x_1,\ldots ,x_k)). $$
* Primitive recursion is, of course, the key idea. Given the $k$-ary function $g(x_1,\ldots ,x_k)$ and the $(k + 2)$-ary function $h(y,z,x_1,\ldots ,x_k)$,
we obtain the $(k+1)$-ary function $f$ defined by 

$$\begin{aligned}
f(0,x_1,\ldots ,x_k)&=g(x_1,\ldots ,x_k)\\f(S(y),x_1,\ldots ,x_k)&=h(y,f(y,x_1,\ldots ,x_k),x_1,\ldots ,x_k).\end{aligned}
$$

Our initial task is to formalise these ideas in higher-order logic.

<pre class="source">
<span class="keyword1 command">primrec</span> <span class="entity">hd0</span> <span class="main">::</span> <span class="quoted quoted"><span>"</span>nat list <span class="main">⇒</span> nat<span>"</span></span> <span class="keyword2 keyword">where</span><span>
  </span><span class="quoted quoted"><span>"</span><span class="free">hd0</span> <span class="main">[]</span> <span class="main">=</span> <span class="main">0</span><span>"</span></span><span>
</span><span class="main">|</span> <span class="quoted quoted"><span>"</span><span class="free">hd0</span> <span class="main">(</span><span class="free bound entity">m</span> <span class="main">#</span> <span class="free bound entity">ms</span><span class="main">)</span> <span class="main">=</span> <span class="free bound entity">m</span><span>"</span></span>
</pre>

<pre class="source">
<span class="keyword1 command">definition</span> <span class="entity">SC</span> <span class="main">::</span> <span class="quoted quoted"><span>"</span>nat list <span class="main">⇒</span> nat<span>"</span></span><span>
  </span><span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">SC</span> <span class="free bound entity">l</span> <span class="main">=</span> Suc <span class="main">(</span>hd0</span> <span class="free bound entity">l</span><span class="main">)</span><span>"</span></span>
</pre>


<pre class="source">
<span class="keyword1 command">definition</span> <span class="entity">CONSTANT</span> <span class="main">::</span> <span class="quoted quoted"><span>"</span>nat <span class="main">⇒</span> nat list <span class="main">⇒</span> nat<span>"</span></span><span>
  </span><span class="keyword2 keyword">where</span> <span class="quoted quoted"><span>"</span><span class="free">CONSTANT</span> <span class="free bound entity">k</span> <span class="free bound entity">l</span> <span class="main">=</span> <span class="free bound entity">k</span><span>"</span></span>
</pre>


<pre class="source">
<span class="keyword1 command">definition</span> <span class="entity">PROJ</span> <span class="main">::</span> <span class="quoted quoted"><span>"</span>nat <span class="main">⇒</span> nat list <span class="main">⇒</span> nat<span>"</span></span><span>
  </span><span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">PROJ</span> <span class="free bound entity">i</span> <span class="free bound entity">l</span> <span class="main">=</span> hd0</span> <span class="main">(</span>drop <span class="free bound entity">i</span> <span class="free bound entity">l</span><span class="main">)</span><span>"</span></span>
</pre>

<pre class="source">
<span class="keyword1 command">definition</span> <span class="entity">COMP</span> <span class="main">::</span> <span class="quoted quoted"><span>"</span><span class="main">[</span>nat list <span class="main">⇒</span> nat<span class="main">,</span> <span class="main">(</span>nat list <span class="main">⇒</span> nat<span class="main">)</span> list<span class="main">,</span> nat list<span class="main">]</span> <span class="main">⇒</span> nat<span>"</span></span><span>
  </span><span class="keyword2 keyword">where</span> <span class="quoted quoted"><span>"</span><span class="free">COMP</span> <span class="free bound entity">g</span> <span class="free bound entity">fs</span> <span class="free bound entity">l</span> <span class="main">=</span> <span class="free bound entity">g</span> <span class="main">(</span>map <span class="main">(</span><span class="main">λ</span><span class="bound">f</span><span class="main">.</span> <span class="bound">f</span> <span class="free bound entity">l</span><span class="main">)</span> <span class="free bound entity">fs</span><span class="main">)</span><span>"</span></span>
</pre>


<pre class="source">
<span class="keyword1 command">fun</span> <span class="entity">PREC</span> <span class="main">::</span> <span class="quoted quoted"><span>"</span><span class="main">[</span>nat list <span class="main">⇒</span> nat<span class="main">,</span> nat list <span class="main">⇒</span> nat<span class="main">,</span> nat list<span class="main">]</span> <span class="main">⇒</span> nat<span>"</span></span><span>
  </span><span class="keyword2 keyword">where</span><span>
    </span><span class="quoted quoted"><span>"</span><span class="free">PREC</span> <span class="free bound entity">f</span> <span class="free bound entity">g</span> <span class="main">[]</span> <span class="main">=</span> <span class="main">0</span><span>"</span></span><span>
  </span><span class="main">|</span> <span class="quoted quoted"><span>"</span><span class="free">PREC</span> <span class="free bound entity">f</span> <span class="free bound entity">g</span> <span class="main">(</span><span class="free bound entity">x</span> <span class="main">#</span> <span class="free bound entity">l</span><span class="main">)</span> <span class="main">=</span> rec_nat <span class="main">(</span><span class="free bound entity">f</span> <span class="free bound entity">l</span><span class="main">)</span> <span class="main">(</span><span class="main">λ</span><span class="bound">y</span> <span class="bound">r</span><span class="main">.</span> <span class="free bound entity">g</span> <span class="main">(</span><span class="bound">r</span> <span class="main">#</span> <span class="bound">y</span> <span class="main">#</span> <span class="free bound entity">l</span><span class="main">)</span><span class="main">)</span> <span class="free bound entity">x</span><span>"</span></span>
</pre>

Note that <span class="antiquoted"><span class="operator"><span class="hidden">\&lt;^</span><span class="control">term</span><span class="hidden">&gt;</span></span><span class="quoted"><span>‹</span><span class="free">g</span><span>›</span></span></span> is applied first to <span class="antiquoted"><span class="operator"><span class="hidden">\&lt;^</span><span class="control">term</span><span class="hidden">&gt;</span></span><span class="quoted"><span>‹</span><span class="free">PREC</span> <span class="free">f</span> <span class="free">g</span> <span class="free">y</span><span>›</span></span></span> and then to <span class="antiquoted"><span class="operator"><span class="hidden">\&lt;^</span><span class="control">term</span><span class="hidden">&gt;</span></span><span class="quoted"><span>‹</span><span class="free">y</span><span>›</span></span></span><span>!</span><span>›</span></span>

### Inductive definition 

<pre class="source">
<span class="keyword1 command">inductive</span> <span class="entity">PRIMREC</span> <span class="main">::</span> <span class="quoted quoted"><span>"</span><span class="main">(</span>nat list <span class="main">⇒</span> nat<span class="main">)</span> <span class="main">⇒</span> bool<span>"</span></span> <span class="keyword2 keyword">where</span><span>
  </span>SC<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">PRIMREC</span> SC</span><span>"</span></span><span>
</span><span class="main">|</span> CONSTANT<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">PRIMREC</span> <span class="main">(</span>CONSTANT</span> <span class="free bound entity">k</span><span class="main">)</span><span>"</span></span><span>
</span><span class="main">|</span> PROJ<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">PRIMREC</span> <span class="main">(</span>PROJ</span> <span class="free bound entity">i</span><span class="main">)</span><span>"</span></span><span>
</span><span class="main">|</span> COMP<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">PRIMREC</span> <span class="free bound entity">g</span> <span class="main">⟹</span> <span class="main">∀</span><span class="bound">f</span> <span class="main">∈</span> set <span class="free bound entity">fs</span><span class="main">.</span> <span class="free">PRIMREC</span> <span class="bound">f</span> <span class="main">⟹</span> <span class="free">PRIMREC</span> <span class="main">(</span>COMP</span> <span class="free bound entity">g</span> <span class="free bound entity">fs</span><span class="main">)</span><span>"</span></span><span>
</span><span class="main">|</span> PREC<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">PRIMREC</span> <span class="free bound entity">f</span> <span class="main">⟹</span> <span class="free">PRIMREC</span> <span class="free bound entity">g</span> <span class="main">⟹</span> <span class="free">PRIMREC</span> <span class="main">(</span>PREC</span> <span class="free bound entity">f</span> <span class="free bound entity">g</span><span class="main">)</span><span>"</span></span>
</pre>

### Useful special cases of evaluation

<pre class="source">
<span class="keyword1 command">lemma</span> SC <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>SC</span> <span class="main">(</span><span class="free">x</span> <span class="main">#</span> <span class="free">l</span><span class="main">)</span> <span class="main">=</span> Suc <span class="free">x</span><span>"</span></span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> SC_def<span class="main">)</span>
</pre>

<pre class="source">
<span class="keyword1 command">lemma</span> PROJ_0 <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>PROJ</span> <span class="main">0</span> <span class="main">(</span><span class="free">x</span> <span class="main">#</span> <span class="free">l</span><span class="main">)</span> <span class="main">=</span> <span class="free">x</span><span>"</span></span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> PROJ_def<span class="main">)</span>
</pre>


<pre class="source">
<span class="keyword1 command">lemma</span> COMP_1 <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>COMP</span> <span class="free">g</span> <span class="main">[</span><span class="free">f</span><span class="main">]</span> <span class="free">l</span> <span class="main">=</span> <span class="free">g</span> <span class="main">[</span><span class="free">f</span> <span class="free">l</span><span class="main">]</span><span>"</span></span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> COMP_def<span class="main">)</span>
</pre>


<pre class="source">
<span class="keyword1 command">lemma</span> PREC_0<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>PREC</span> <span class="free">f</span> <span class="free">g</span> <span class="main">(</span><span class="main">0</span> <span class="main">#</span> <span class="free">l</span><span class="main">)</span> <span class="main">=</span> <span class="free">f</span> <span class="free">l</span><span>"</span></span><span>
  </span><span class="keyword1 command">by</span> <span class="operator">simp</span>
</pre>


<pre class="source">
<span class="keyword1 command">lemma</span> PREC_Suc <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>PREC</span> <span class="free">f</span> <span class="free">g</span> <span class="main">(</span>Suc <span class="free">x</span> <span class="main">#</span> <span class="free">l</span><span class="main">)</span> <span class="main">=</span> <span class="free">g</span> <span class="main">(</span>PREC</span> <span class="free">f</span> <span class="free">g</span> <span class="main">(</span><span class="free">x</span> <span class="main">#</span> <span class="free">l</span><span class="main">)</span> <span class="main">#</span> <span class="free">x</span> <span class="main">#</span> <span class="free">l</span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="operator">auto</span>
</pre>

### Now for the inductive proof itself

#### The base cases

<pre class="source">
<span class="keyword1 command">lemma</span> SC_case<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>SC</span> <span class="free">l</span> <span class="main">&lt;</span> ack</span> <span class="main">1</span> <span class="main">(</span>sum_list <span class="free">l</span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword1 command">unfolding</span> SC_def<span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">induct</span> <span class="quoted free">l</span><span class="main">)</span> <span class="main">(</span><span class="operator">simp_all</span> <span class="quasi_keyword">add</span><span class="main main">:</span> le_add1 le_imp_less_Suc<span class="main">)</span>
</pre>


<pre class="source">
<span class="keyword1 command">lemma</span> CONSTANT_case<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>CONSTANT</span> <span class="free">k</span> <span class="free">l</span> <span class="main">&lt;</span> ack</span> <span class="free">k</span> <span class="main">(</span>sum_list <span class="free">l</span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> CONSTANT_def<span class="main">)</span>
</pre>

<pre class="source">
<span class="keyword1 command">lemma</span> PROJ_case<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>PROJ</span> <span class="free">i</span> <span class="free">l</span> <span class="main">&lt;</span> ack</span> <span class="main">0</span> <span class="main">(</span>sum_list <span class="free">l</span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword1 command">unfolding</span> PROJ_def<span>
</span><span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">induct</span> <span class="quoted free">l</span> <span class="quasi_keyword">arbitrary</span><span class="main main">:</span> <span class="quoted free">i</span><span class="main">)</span><span>
  </span><span class="keyword3 command">case</span> Nil<span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="var quoted var">?case</span><span>
    </span><span class="keyword1 command">by</span> <span class="operator">simp</span><span>
</span><span class="keyword1 command">next</span><span>
  </span><span class="keyword3 command">case</span> <span class="main">(</span>Cons <span class="skolem">a</span> <span class="skolem">l</span><span class="main">)</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="var quoted var">?case</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> ack.simps<span class="main main">(</span>1<span class="main main">)</span> add.commute <span>drop_Cons'</span> hd0.simps<span class="main main">(</span>2<span class="main main">)</span> leD leI lessI not_less_eq sum_list.Cons trans_le_add2<span class="main">)</span><span>
</span><span class="keyword1 command">qed</span>
</pre>

#### The COMP case

<pre class="source">
<span class="keyword1 command">lemma</span> COMP_map_aux<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">∀</span><span class="bound">f</span> <span class="main">∈</span> set <span class="free">fs</span><span class="main">.</span> PRIMREC</span> <span class="bound">f</span> <span class="main">∧</span> <span class="main">(</span><span class="main">∃</span><span class="bound">kf</span><span class="main">.</span> <span class="main">∀</span><span class="bound">l</span><span class="main">.</span> <span class="bound">f</span> <span class="bound">l</span> <span class="main">&lt;</span> ack</span> <span class="bound">kf</span> <span class="main">(</span>sum_list <span class="bound">l</span><span class="main">)</span><span class="main">)</span><span>
  </span><span class="main">⟹</span> <span class="main">∃</span><span class="bound">k</span><span class="main">.</span> <span class="main">∀</span><span class="bound">l</span><span class="main">.</span> sum_list <span class="main">(</span>map <span class="main">(</span><span class="main">λ</span><span class="bound">f</span><span class="main">.</span> <span class="bound">f</span> <span class="bound">l</span><span class="main">)</span> <span class="free">fs</span><span class="main">)</span> <span class="main">&lt;</span> ack <span class="bound">k</span> <span class="main">(</span>sum_list <span class="bound">l</span><span class="main">)</span><span>"</span><span>
</span><span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">induct</span> <span class="quoted free">fs</span><span class="main">)</span><span>
  </span><span class="keyword3 command">case</span> Nil<span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="var quoted var">?case</span><span>
    </span><span class="keyword1 command">by</span> <span class="operator">auto</span><span>
</span><span class="keyword1 command">next</span><span>
  </span><span class="keyword3 command">case</span> <span class="main">(</span>Cons <span class="skolem">a</span> <span class="skolem">fs</span><span class="main">)</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="var quoted var">?case</span><span>
    </span><span class="keyword1 command">by</span> <span class="operator">simp</span> <span class="main">(</span><span class="operator">blast</span> <span class="quasi_keyword">intro</span><span class="main main">:</span> add_less_mono ack_add_bound less_trans<span class="main">)</span><span>
</span><span class="keyword1 command">qed</span>
</pre>

<pre class="source">
<span class="keyword1 command">lemma</span> COMP_case<span class="main">:</span><span>
  </span><span class="keyword2 keyword">assumes</span> 1<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">∀</span><span class="bound">l</span><span class="main">.</span> <span class="free">g</span> <span class="bound">l</span> <span class="main">&lt;</span> ack</span> <span class="free">kg</span> <span class="main">(</span>sum_list <span class="bound">l</span><span class="main">)</span><span>"</span></span><span>
      </span><span class="keyword2 keyword">and</span> 2<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">∀</span><span class="bound">f</span> <span class="main">∈</span> set <span class="free">fs</span><span class="main">.</span> PRIMREC</span> <span class="bound">f</span> <span class="main">∧</span> <span class="main">(</span><span class="main">∃</span><span class="bound">kf</span><span class="main">.</span> <span class="main">∀</span><span class="bound">l</span><span class="main">.</span> <span class="bound">f</span> <span class="bound">l</span> <span class="main">&lt;</span> ack</span> <span class="bound">kf</span> <span class="main">(</span>sum_list <span class="bound">l</span><span class="main">)</span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">∃</span><span class="bound">k</span><span class="main">.</span> <span class="main">∀</span><span class="bound">l</span><span class="main">.</span> COMP</span> <span class="free">g</span> <span class="free">fs</span>  <span class="bound">l</span> <span class="main">&lt;</span> ack</span> <span class="bound">k</span> <span class="main">(</span>sum_list <span class="bound">l</span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword1 command">unfolding</span> COMP_def<span>
  </span><span class="keyword1 command">using</span> 1 COMP_map_aux <span class="main">[</span><span class="operator">OF</span> 2<span class="main">]</span> <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">meson</span> ack_less_mono2 ack_nest_bound less_trans<span class="main">)</span>
</pre>

#### The PREC case

<pre class="source">
<span class="keyword1 command">lemma</span> PREC_case_aux<span class="main">:</span><span>
  </span><span class="keyword2 keyword">assumes</span> f<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">⋀</span><span class="bound">l</span><span class="main">.</span> <span class="free">f</span> <span class="bound">l</span> <span class="main">+</span> sum_list <span class="bound">l</span> <span class="main">&lt;</span> ack</span> <span class="free">kf</span> <span class="main">(</span>sum_list <span class="bound">l</span><span class="main">)</span><span>"</span></span><span>
      </span><span class="keyword2 keyword">and</span> g<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">⋀</span><span class="bound">l</span><span class="main">.</span> <span class="free">g</span> <span class="bound">l</span> <span class="main">+</span> sum_list <span class="bound">l</span> <span class="main">&lt;</span> ack</span> <span class="free">kg</span> <span class="main">(</span>sum_list <span class="bound">l</span><span class="main">)</span><span>"</span></span><span>
  </span><span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span>PREC</span> <span class="free">f</span> <span class="free">g</span> <span class="free">l</span> <span class="main">+</span> sum_list <span class="free">l</span> <span class="main">&lt;</span> ack</span> <span class="main">(</span>Suc <span class="main">(</span><span class="free">kf</span> <span class="main">+</span> <span class="free">kg</span><span class="main">)</span><span class="main">)</span> <span class="main">(</span>sum_list <span class="free">l</span><span class="main">)</span><span>"</span><span>
</span><span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">cases</span> <span class="quoted free">l</span><span class="main">)</span><span>
  </span><span class="keyword3 command">case</span> Nil<span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="var quoted var">?thesis</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> Suc_lessD<span class="main">)</span><span>
</span><span class="keyword1 command">next</span><span>
  </span><span class="keyword3 command">case</span> <span class="main">(</span>Cons <span class="skolem">m</span> <span class="skolem">l</span><span class="main">)</span><span>
  </span><span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span>rec_nat <span class="main">(</span><span class="free">f</span> <span class="skolem">l</span><span class="main">)</span> <span class="main">(</span><span class="main">λ</span><span class="bound">y</span> <span class="bound">r</span><span class="main">.</span> <span class="free">g</span> <span class="main">(</span><span class="bound">r</span> <span class="main">#</span> <span class="bound">y</span> <span class="main">#</span> <span class="skolem">l</span><span class="main">)</span><span class="main">)</span> <span class="skolem">m</span> <span class="main">+</span> <span class="main">(</span><span class="skolem">m</span> <span class="main">+</span> sum_list <span class="skolem">l</span><span class="main">)</span> <span class="main">&lt;</span> ack</span> <span class="main">(</span>Suc <span class="main">(</span><span class="free">kf</span> <span class="main">+</span> <span class="free">kg</span><span class="main">)</span><span class="main">)</span> <span class="main">(</span><span class="skolem">m</span> <span class="main">+</span> sum_list <span class="skolem">l</span><span class="main">)</span><span>"</span></span><span>
  </span><span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">induct</span> <span class="quoted skolem">m</span><span class="main">)</span><span>
    </span><span class="keyword3 command">case</span> 0<span>
    </span><span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="var quoted var">?case</span><span>
      </span><span class="keyword1 command">using</span> ack_less_mono1_aux f less_trans <span class="keyword1 command">by</span> <span class="operator">fastforce</span><span>
  </span><span class="keyword1 command">next</span><span>
    </span><span class="keyword3 command">case</span> <span class="main">(</span>Suc <span class="skolem">m</span><span class="main">)</span><span>
    </span><span class="keyword1 command">let</span> <span class="var quoted var">?r</span> <span class="main">=</span> <span class="quoted quoted"><span>"</span>rec_nat <span class="main">(</span><span class="free">f</span> <span class="skolem">l</span><span class="main">)</span> <span class="main">(</span><span class="main">λ</span><span class="bound">y</span> <span class="bound">r</span><span class="main">.</span> <span class="free">g</span> <span class="main">(</span><span class="bound">r</span> <span class="main">#</span> <span class="bound">y</span> <span class="main">#</span> <span class="skolem">l</span><span class="main">)</span><span class="main">)</span> <span class="skolem">m</span><span>"</span></span><span>
    </span><span class="keyword1 command">have</span> <span class="quoted quoted"><span>"</span><span class="main">¬</span> <span class="free">g</span> <span class="main">(</span><span class="var">?r</span> <span class="main">#</span> <span class="skolem">m</span> <span class="main">#</span> <span class="skolem">l</span><span class="main">)</span> <span class="main">+</span> sum_list <span class="main">(</span><span class="var">?r</span> <span class="main">#</span> <span class="skolem">m</span> <span class="main">#</span> <span class="skolem">l</span><span class="main">)</span> <span class="main">&lt;</span> <span class="free">g</span> <span class="main">(</span><span class="var">?r</span> <span class="main">#</span> <span class="skolem">m</span> <span class="main">#</span> <span class="skolem">l</span><span class="main">)</span> <span class="main">+</span> <span class="main">(</span><span class="skolem">m</span> <span class="main">+</span> sum_list <span class="skolem">l</span><span class="main">)</span><span>"</span></span><span>
      </span><span class="keyword1 command">by</span> <span class="operator">force</span><span>
    </span><span class="keyword1 command">then</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">g</span> <span class="main">(</span><span class="var">?r</span> <span class="main">#</span> <span class="skolem">m</span> <span class="main">#</span> <span class="skolem">l</span><span class="main">)</span> <span class="main">+</span> <span class="main">(</span><span class="skolem">m</span> <span class="main">+</span> sum_list <span class="skolem">l</span><span class="main">)</span> <span class="main">&lt;</span> ack</span> <span class="free">kg</span> <span class="main">(</span>sum_list <span class="main">(</span><span class="var">?r</span> <span class="main">#</span> <span class="skolem">m</span> <span class="main">#</span> <span class="skolem">l</span><span class="main">)</span><span class="main">)</span><span>"</span></span><span>
      </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">meson</span> assms<span class="main main">(</span>2<span class="main main">)</span> leI less_le_trans<span class="main">)</span><span>
    </span><span class="keyword1 command">moreover</span><span>
    </span><span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">...</span> <span class="main">&lt;</span> ack</span> <span class="main">(</span><span class="free">kf</span> <span class="main">+</span> <span class="free">kg</span><span class="main">)</span> <span class="main">(</span>ack</span> <span class="main">(</span>Suc <span class="main">(</span><span class="free">kf</span> <span class="main">+</span> <span class="free">kg</span><span class="main">)</span><span class="main">)</span> <span class="main">(</span><span class="skolem">m</span> <span class="main">+</span> sum_list <span class="skolem">l</span><span class="main">)</span><span class="main">)</span><span>"</span><span>
      </span><span class="keyword1 command">using</span> Suc.hyps <span class="keyword1 command">by</span> <span class="operator">simp</span> <span class="main">(</span><span class="operator">meson</span> ack_le_mono1 ack_less_mono2 le_add2 le_less_trans<span class="main">)</span><span>
    </span><span class="keyword1 command">ultimately</span> <span class="keyword3 command">show</span> <span class="var quoted var">?case</span><span>
      </span><span class="keyword1 command">by</span> <span class="operator">auto</span><span>
  </span><span class="keyword1 command">qed</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="var quoted var">?thesis</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> local.Cons<span class="main">)</span><span>
</span><span class="keyword1 command">qed</span>
</pre>

<pre class="source">
<span class="keyword1 command">proposition</span> PREC_case<span class="main">:</span><span>
  </span><span class="quoted"><span class="quoted"><span>"</span><span class="main">⟦</span><span class="main">⋀</span><span class="bound">l</span><span class="main">.</span> <span class="free">f</span> <span class="bound">l</span> <span class="main">&lt;</span> ack</span> <span class="free">kf</span> <span class="main">(</span>sum_list <span class="bound">l</span><span class="main">)</span><span class="main">;</span> <span class="main">⋀</span><span class="bound">l</span><span class="main">.</span> <span class="free">g</span> <span class="bound">l</span> <span class="main">&lt;</span> ack</span> <span class="free">kg</span> <span class="main">(</span>sum_list <span class="bound">l</span><span class="main">)</span><span class="main">⟧</span><span>
  </span><span class="main">⟹</span> <span class="main">∃</span><span class="bound">k</span><span class="main">.</span> <span class="main">∀</span><span class="bound">l</span><span class="main">.</span> PREC <span class="free">f</span> <span class="free">g</span> <span class="bound">l</span> <span class="main">&lt;</span> ack <span class="bound">k</span> <span class="main">(</span>sum_list <span class="bound">l</span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> le_less_trans <span class="main main">[</span><span class="operator">OF</span> le_add1 PREC_case_aux<span class="main main">]</span> ack_add_bound2<span class="main">)</span>
</pre>

### The main result

<pre class="source">
<span class="keyword1 command">lemma</span> ack_bounds_PRIMREC<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>PRIMREC</span> <span class="free">f</span> <span class="main">⟹</span> <span class="main">∃</span><span class="bound">k</span><span class="main">.</span> <span class="main">∀</span><span class="bound">l</span><span class="main">.</span> <span class="free">f</span> <span class="bound">l</span> <span class="main">&lt;</span> ack</span> <span class="bound">k</span> <span class="main">(</span>sum_list <span class="bound">l</span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">erule</span> PRIMREC.induct<span class="main">)</span> <span class="main">(</span><span class="operator">blast</span> <span class="quasi_keyword">intro</span><span class="main main">:</span> SC_case CONSTANT_case PROJ_case COMP_case PREC_case<span class="main">)</span><span class="main keyword3">+</span><span>
</pre>

<pre class="source">
<span class="keyword1 command">theorem</span> ack_not_PRIMREC<span class="main">:</span><span>
  </span><span class="quoted"><span class="quoted"><span>"</span><span class="main">¬</span> PRIMREC</span> <span class="main">(</span><span class="main">λ</span><span class="bound">l</span><span class="main">.</span> <span class="keyword1">case</span> <span class="bound">l</span> <span class="keyword1">of</span> <span class="main">[]</span> <span class="main">⇒</span> <span class="main">0</span> <span class="main">|</span> <span class="bound">x</span> <span class="main">#</span> <span class="bound">l'</span> <span class="main">⇒</span> ack</span> <span class="bound">x</span> <span class="bound">x</span><span class="main">)</span><span>"</span><span>
</span><span class="keyword1 command">proof</span><span>
  </span><span class="keyword3 command">assume</span> <span>*</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>PRIMREC</span> <span class="main">(</span><span class="main">λ</span><span class="bound">l</span><span class="main">.</span> <span class="keyword1">case</span> <span class="bound">l</span> <span class="keyword1">of</span> <span class="main">[]</span> <span class="main">⇒</span> <span class="main">0</span> <span class="main">|</span> <span class="bound">x</span> <span class="main">#</span> <span class="bound">l'</span> <span class="main">⇒</span> ack</span> <span class="bound">x</span> <span class="bound">x</span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">obtain</span> <span class="skolem skolem">m</span> <span class="keyword2 keyword">where</span> m<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">⋀</span><span class="bound">l</span><span class="main">.</span> <span class="main">(</span><span class="keyword1">case</span> <span class="bound">l</span> <span class="keyword1">of</span> <span class="main">[]</span> <span class="main">⇒</span> <span class="main">0</span> <span class="main">|</span> <span class="bound">x</span> <span class="main">#</span> <span class="bound">l'</span> <span class="main">⇒</span> ack</span> <span class="bound">x</span> <span class="bound">x</span><span class="main">)</span> <span class="main">&lt;</span> ack</span> <span class="skolem">m</span> <span class="main">(</span>sum_list <span class="bound">l</span><span class="main">)</span><span>"</span><span>
    </span><span class="keyword1 command">using</span> ack_bounds_PRIMREC <span class="keyword1 command">by</span> <span class="operator">metis</span><span>
  </span><span class="keyword3 command">show</span> <span class="quoted">False</span><span>
    </span><span class="keyword1 command">using</span> m <span class="main">[</span><span class="operator">of</span> <span class="quoted quoted"><span>"</span><span class="main">[</span><span class="skolem">m</span><span class="main">]</span><span>"</span></span><span class="main">]</span> <span class="keyword1 command">by</span> <span class="operator">simp</span><span>
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



The [full development](https://www.isa-afp.org/entries/Ackermanns_not_PR.html) can be found in Isabelle's Archive of Formal Proofs.


Although the final result is remarkable and deep, it's easy to formalise, 
which is why people were able to do with the early 90s.


Peter Aczel [has written](https://doi.org/10.1016/S0049-237X(08)71120-0) (also [here](/papers/Aczel-Inductive-Defs.pdf))
a comprehensive paper on inductive definitions


By the way, if you are looking for a function that is not primitive recursive and has a practical application, the answer is, any programming language interpreter.
An interpreter takes a program (encoded somehow) and runs it, so it can easily run forever.
PR functions necessarily terminate.
And an interpreter for a programming language of PR functions will always terminate (because PR functions always terminate) but cannot be PR itself (by the obvious diagonalisation argument).


