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

Primitive recursive can be combined as follows:

* The *composition* $g\circ(f_1,\ldots,f_m)$ of an $m$-ary function $g$ and $k$-ary functions $f_1,\ldots,f_m$ denotes a function mapping
$$ (x_1,\ldots,x_k) \mapsto g(f_1(x_1,\ldots ,x_k),\ldots ,f_m(x_1,\ldots ,x_k)). $$
* *Primitive recursion* combines the $k$-ary function $g(x_1,\ldots ,x_k)$ and the $(k + 2)$-ary function $h(y,z,x_1,\ldots ,x_k)$
to obtain the $(k+1)$-ary function $f$ defined by

$$\begin{aligned}
f(0,x_1,\ldots ,x_k)&=g(x_1,\ldots ,x_k)\\f(S(y),x_1,\ldots ,x_k)&=h(f(y,x_1,\ldots ,x_k),y,x_1,\ldots ,x_k).\end{aligned}
$$

Finally, and crucially, there are no primitive recursive functions other than those specified above.
Our initial task is to formalise these ideas in higher-order logic.

### Formalising the set of PR functions

If we regard the constructions above as a programming language, it's absolutely minimalist, even by comparison with the pure $\lambda$-calculus.
Every recursion must be bounded by a precomputed integer.
Worse, the arguments in the recursion are not allowed to vary, so a typical functional programming style is impossible.
Division, for example, is tricky to code.
It isn't defined in the Wikipedia article and I can't see a better algorithm than explicit inversion of multiplication, i.e.,
trying ever larger "quotients" and stopping before they get too large.

But we are not defining a language at all but rather a *predicate* identifying those functions
in $\bigcup_{k\ge0}\,\mathbb{N}^k\to\mathbb{N}$ that are primitive recursive.

Our first decision is how to formalise the tuples of arguments $(x_1,\ldots,x_k)$. Szasz, using ALF (and apparently just adding the desired rules to Martin-Löf type theory) defines a set $T(k)$ of $k$-tuples of natural numbers.
Such a dependently-typed option isn't available in Isabelle/HOL, and anyway,
it seems simpler to use lists.

#### The base cases

Following Szasz, let's define a version of the built-in function `hd` that
returns zero for the empty list and otherwise the first element:

<pre class="source">
<span class="keyword1 command">primrec</span> <span class="entity">hd0</span> <span class="main">::</span> <span class="quoted quoted"><span>"</span>nat list <span class="main">⇒</span> nat<span>"</span></span> <span class="keyword2 keyword">where</span><span>
  </span><span class="quoted quoted"><span>"</span><span class="free">hd0</span> <span class="main">[]</span> <span class="main">=</span> <span class="main">0</span><span>"</span></span><span>
</span><span class="main">|</span> <span class="quoted quoted"><span>"</span><span class="free">hd0</span> <span class="main">(</span><span class="free bound entity">m</span> <span class="main">#</span> <span class="free bound entity">ms</span><span class="main">)</span> <span class="main">=</span> <span class="free bound entity">m</span><span>"</span></span>
</pre>

Now for the successor function (which returns 1 for the empty list):

<pre class="source">
<span class="keyword1 command">definition</span> <span class="entity">SC</span> <span class="main">::</span> <span class="quoted quoted"><span>"</span>nat list <span class="main">⇒</span> nat<span>"</span></span><span>
  </span><span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">SC</span> <span class="free bound entity">l</span> <span class="main">=</span> Suc <span class="main">(</span>hd0</span> <span class="free bound entity">l</span><span class="main">)</span><span>"</span></span>
</pre>

We have the functions `CONSTANT n` for each `n`, by [currying](https://en.wikipedia.org/wiki/Currying):

<pre class="source">
<span class="keyword1 command">definition</span> <span class="entity">CONSTANT</span> <span class="main">::</span> <span class="quoted quoted"><span>"</span>nat <span class="main">⇒</span> nat list <span class="main">⇒</span> nat<span>"</span></span><span>
  </span><span class="keyword2 keyword">where</span> <span class="quoted quoted"><span>"</span><span class="free">CONSTANT</span> <span class="free bound entity">n</span> <span class="free bound entity">l</span> <span class="main">=</span> <span class="free bound entity">n</span><span>"</span></span>
</pre>

Projection is expressed with the help of `drop`, a function to remove a given number of elements from the front of a list:

<pre class="source">
<span class="keyword1 command">definition</span> <span class="entity">PROJ</span> <span class="main">::</span> <span class="quoted quoted"><span>"</span>nat <span class="main">⇒</span> nat list <span class="main">⇒</span> nat<span>"</span></span><span>
  </span><span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">PROJ</span> <span class="free bound entity">i</span> <span class="free bound entity">l</span> <span class="main">=</span> hd0</span> <span class="main">(</span>drop <span class="free bound entity">i</span> <span class="free bound entity">l</span><span class="main">)</span><span>"</span></span>
</pre>

Now for a confession: here, tuples are indexed from zero and should properly be written $(x_0,\ldots,x_{k-1})$.

#### Operations to combine PR functions

Szasz defined the dependent type $TPR(n,m)$ to represent (the codes of) functions from $n$-tuples to $m$-tuples, i.e. functions $\mathbb{N}^n\to\mathbb{N}^m$.
By working with such tupled functions, Szasz can specify function composition
as combining elements of $TPR(k,m)$ and $TPR(n,k)$ to yield $TPR(n,m)$.
The Isabelle/HOL equivalent composes a function `g` with a **list** `fs` of functions.
Given an argument list `l`, each element `f` of the list `fs` is applied to `l` and the result is presented to `g`.
I would argue that this approach is simpler.

<pre class="source">
<span class="keyword1 command">definition</span> <span class="entity">COMP</span> <span class="main">::</span> <span class="quoted quoted"><span>"</span><span class="main">[</span>nat list <span class="main">⇒</span> nat<span class="main">,</span> <span class="main">(</span>nat list <span class="main">⇒</span> nat<span class="main">)</span> list<span class="main">,</span> nat list<span class="main">]</span> <span class="main">⇒</span> nat<span>"</span></span><span>
  </span><span class="keyword2 keyword">where</span> <span class="quoted quoted"><span>"</span><span class="free">COMP</span> <span class="free bound entity">g</span> <span class="free bound entity">fs</span> <span class="free bound entity">l</span> <span class="main">=</span> <span class="free bound entity">g</span> <span class="main">(</span>map <span class="main">(</span><span class="main">λ</span><span class="bound">f</span><span class="main">.</span> <span class="bound">f</span> <span class="free bound entity">l</span><span class="main">)</span> <span class="free bound entity">fs</span><span class="main">)</span><span>"</span></span>
</pre>

Primitive recursion itself is delegated to `rec_nat`, a low-level function for recursion over the natural numbers.
Provided the argument list is nonempty, its tail (namely `l`) represents the tuple $(x_1,\ldots,x_k)$ while `y` ranges over the predecessors of `x` and `r` represents the inner recursive call.
The function `g` is applied first to `PREC f g y` and then to `y`.
And the first line of the definition below handles the degenerate case,
because primitive recursion is actually undefined for the empty list.

<pre class="source">
<span class="keyword1 command">fun</span> <span class="entity">PREC</span> <span class="main">::</span> <span class="quoted quoted"><span>"</span><span class="main">[</span>nat list <span class="main">⇒</span> nat<span class="main">,</span> nat list <span class="main">⇒</span> nat<span class="main">,</span> nat list<span class="main">]</span> <span class="main">⇒</span> nat<span>"</span></span><span>
  </span><span class="keyword2 keyword">where</span><span>
    </span><span class="quoted quoted"><span>"</span><span class="free">PREC</span> <span class="free bound entity">f</span> <span class="free bound entity">g</span> <span class="main">[]</span> <span class="main">=</span> <span class="main">0</span><span>"</span></span><span>
  </span><span class="main">|</span> <span class="quoted quoted"><span>"</span><span class="free">PREC</span> <span class="free bound entity">f</span> <span class="free bound entity">g</span> <span class="main">(</span><span class="free bound entity">x</span> <span class="main">#</span> <span class="free bound entity">l</span><span class="main">)</span> <span class="main">=</span> rec_nat <span class="main">(</span><span class="free bound entity">f</span> <span class="free bound entity">l</span><span class="main">)</span> <span class="main">(</span><span class="main">λ</span><span class="bound">y</span> <span class="bound">r</span><span class="main">.</span> <span class="free bound entity">g</span> <span class="main">(</span><span class="bound">r</span> <span class="main">#</span> <span class="bound">y</span> <span class="main">#</span> <span class="free bound entity">l</span><span class="main">)</span><span class="main">)</span> <span class="free bound entity">x</span><span>"</span></span>
</pre>


#### Special cases of evaluation

The following five claims were present in the development, but are not actually used. They simply present special cases of the definitions above in the more legible form, especially in the case of composition. The last two show the operation of primitive recursion.

<pre class="source">
<span class="keyword1 command">lemma</span> SC<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>SC</span> <span class="main">(</span><span class="free">x</span> <span class="main">#</span> <span class="free">l</span><span class="main">)</span> <span class="main">=</span> Suc <span class="free">x</span><span>"</span></span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> SC_def<span class="main">)</span>
</pre>

<pre class="source">
<span class="keyword1 command">lemma</span> PROJ_0<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>PROJ</span> <span class="main">0</span> <span class="main">(</span><span class="free">x</span> <span class="main">#</span> <span class="free">l</span><span class="main">)</span> <span class="main">=</span> <span class="free">x</span><span>"</span></span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> PROJ_def<span class="main">)</span>
</pre>


<pre class="source">
<span class="keyword1 command">lemma</span> COMP_1<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>COMP</span> <span class="free">g</span> <span class="main">[</span><span class="free">f</span><span class="main">]</span> <span class="free">l</span> <span class="main">=</span> <span class="free">g</span> <span class="main">[</span><span class="free">f</span> <span class="free">l</span><span class="main">]</span><span>"</span></span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> COMP_def<span class="main">)</span>
</pre>


<pre class="source">
<span class="keyword1 command">lemma</span> PREC_0<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>PREC</span> <span class="free">f</span> <span class="free">g</span> <span class="main">(</span><span class="main">0</span> <span class="main">#</span> <span class="free">l</span><span class="main">)</span> <span class="main">=</span> <span class="free">f</span> <span class="free">l</span><span>"</span></span><span>
  </span><span class="keyword1 command">by</span> <span class="operator">simp</span>
</pre>


<pre class="source">
<span class="keyword1 command">lemma</span> PREC_Suc<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>PREC</span> <span class="free">f</span> <span class="free">g</span> <span class="main">(</span>Suc <span class="free">x</span> <span class="main">#</span> <span class="free">l</span><span class="main">)</span> <span class="main">=</span> <span class="free">g</span> <span class="main">(</span>PREC</span> <span class="free">f</span> <span class="free">g</span> <span class="main">(</span><span class="free">x</span> <span class="main">#</span> <span class="free">l</span><span class="main">)</span> <span class="main">#</span> <span class="free">x</span> <span class="main">#</span> <span class="free">l</span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="operator">auto</span>
</pre>


#### The actual inductive definition

Having defined all the basic functions and operations to combine them, the inductive definition itself is trivial. Several of these functions are simple enough that they could have been written in line, but it's convenient to have names such as `SC` available separately.
It's notable that Szasz did in fact formalise a language of PR functions, which she interpreted in a separate step.

<pre class="source">
<span class="keyword1 command">inductive</span> <span class="entity">PRIMREC</span> <span class="main">::</span> <span class="quoted quoted"><span>"</span><span class="main">(</span>nat list <span class="main">⇒</span> nat<span class="main">)</span> <span class="main">⇒</span> bool<span>"</span></span> <span class="keyword2 keyword">where</span><span>
  </span>SC<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">PRIMREC</span> SC</span><span>"</span></span><span>
</span><span class="main">|</span> CONSTANT<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">PRIMREC</span> <span class="main">(</span>CONSTANT</span> <span class="free bound entity">k</span><span class="main">)</span><span>"</span></span><span>
</span><span class="main">|</span> PROJ<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">PRIMREC</span> <span class="main">(</span>PROJ</span> <span class="free bound entity">i</span><span class="main">)</span><span>"</span></span><span>
</span><span class="main">|</span> COMP<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">PRIMREC</span> <span class="free bound entity">g</span> <span class="main">⟹</span> <span class="main">∀</span><span class="bound">f</span> <span class="main">∈</span> set <span class="free bound entity">fs</span><span class="main">.</span> <span class="free">PRIMREC</span> <span class="bound">f</span> <span class="main">⟹</span> <span class="free">PRIMREC</span> <span class="main">(</span>COMP</span> <span class="free bound entity">g</span> <span class="free bound entity">fs</span><span class="main">)</span><span>"</span></span><span>
</span><span class="main">|</span> PREC<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">PRIMREC</span> <span class="free bound entity">f</span> <span class="main">⟹</span> <span class="free">PRIMREC</span> <span class="free bound entity">g</span> <span class="main">⟹</span> <span class="free">PRIMREC</span> <span class="main">(</span>PREC</span> <span class="free bound entity">f</span> <span class="free bound entity">g</span><span class="main">)</span><span>"</span></span>
</pre>

This declaration causes Isabelle to define the named predicate, expressing the recursion through a fixed point construction. The given closure properties, regarded as introduction rules, are derived automatically. The corresponding induction principle, an elimination rule, Is also proved.
A basic introduction and examples are available in the [documentation](https://isabelle.in.tum.de/dist/Isabelle/doc/prog-prove.pdf).

For those of you interested in an abstract and theoretical development,
Peter Aczel's [chapter](https://doi.org/10.1016/S0049-237X(08)71120-0) (also [here](/papers/Aczel-Inductive-Defs.pdf)) in the *Handbook of Mathematical Logic* is the ultimate account.

### Now for the inductive proof itself

To prove that Ackermann's function is not primitive recursive, we show that for each PR function $f$ we can find some bound $k$, in the sense that $A(k,{-})$ grows strictly faster than $f$.
To build up to this result, we work through all the ways of constructing a PR function. It's only a matter of style that we prove these cases as separate lemmas rather than as one big induction.

#### The base cases

For the successor function, the desired $k$ is simply 1.
Incidentally, the function `sum_list` denotes the sum of the elements of a list.

<pre class="source">
<span class="keyword1 command">lemma</span> SC_case<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>SC</span> <span class="free">l</span> <span class="main">&lt;</span> ack</span> <span class="main">1</span> <span class="main">(</span>sum_list <span class="free">l</span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword1 command">unfolding</span> SC_def<span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">induct</span> <span class="quoted free">l</span><span class="main">)</span> <span class="main">(</span><span class="operator">simp_all</span> <span class="quasi_keyword">add</span><span class="main main">:</span> le_add1 le_imp_less_Suc<span class="main">)</span>
</pre>

For the constant function for $n$, the desired $k$ is $n$.

<pre class="source">
<span class="keyword1 command">lemma</span> CONSTANT_case<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>CONSTANT</span> <span class="free">n</span> <span class="free">l</span> <span class="main">&lt;</span> ack</span> <span class="free">n</span> <span class="main">(</span>sum_list <span class="free">l</span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> CONSTANT_def<span class="main">)</span>
</pre>

For any projection function, the desired $k$ is actually zero!

<pre class="source">
<span class="keyword1 command">lemma</span> PROJ_case<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>PROJ</span> <span class="free">i</span> <span class="free">l</span> <span class="main">&lt;</span></span> ack <span class="main">0</span> <span class="main">(</span>sum_list <span class="free">l</span><span class="main">)</span><span>"</span>
<span class="keyword1 command">proof</span> <span class="operator">-</span>
  <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span>hd0</span> <span class="main">(</span>drop</span> <span class="free">i</span> <span class="free">l</span><span class="main">)</span> <span class="main">≤</span> sum_list <span class="free">l</span><span>"</span>
    <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">induct</span> <span class="quoted free">l</span> <span class="quasi_keyword">arbitrary</span><span class="main main">:</span> <span class="quoted free">i</span><span class="main">)</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> drop_Cons' trans_le_add2<span class="main">)</span>
  <span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="var quoted var">?thesis</span>
    <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> PROJ_def<span class="main">)</span>
<span class="keyword1 command">qed</span>
</pre>

#### The COMP case

The case for function composition is complicated because the function $g$ is composed with a list
of functions $f$. So we begin with a lemma that finds a single bound $k$ covering all the functions in the list,
assuming the existence of separate bounds for each individual function.
It's a simple induction over the list. To combine the bounds, we use the lemma `ack_add_bound`,
proved in the [previous post]({% post_url 2022-08-31-Ackermann-not-PR-I %}).

<pre class="source">
<span class="keyword1 command">lemma</span> COMP_map_aux<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">∀</span><span class="bound">f</span> <span class="main">∈</span> set</span> <span class="free">fs</span><span class="main">.</span> <span class="main">∃</span></span><span class="bound">kf</span><span class="main">.</span> <span class="main">∀</span><span class="bound">l</span><span class="main">.</span> <span class="bound">f</span> <span class="bound">l</span> <span class="main">&lt;</span> ack <span class="bound">kf</span> <span class="main">(</span>sum_list <span class="bound">l</span><span class="main">)</span>
        <span class="main">⟹</span> <span class="main">∃</span><span class="bound">k</span><span class="main">.</span> <span class="main">∀</span><span class="bound">l</span><span class="main">.</span> sum_list <span class="main">(</span>map <span class="main">(</span><span class="main">λ</span><span class="bound">f</span><span class="main">.</span> <span class="bound">f</span> <span class="bound">l</span><span class="main">)</span> <span class="free">fs</span><span class="main">)</span> <span class="main">&lt;</span> ack <span class="bound">k</span> <span class="main">(</span>sum_list <span class="bound">l</span><span class="main">)</span><span>"</span>
<span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">induct</span> <span class="quoted free">fs</span><span class="main">)</span>
  <span class="keyword3 command">case</span> Nil
  <span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="var quoted var">?case</span>
    <span class="keyword1 command">by</span> <span class="operator">auto</span>
<span class="keyword1 command">next</span>
  <span class="keyword3 command">case</span> <span class="main">(</span>Cons <span class="skolem">a</span> <span class="skolem">fs</span><span class="main">)</span>
  <span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="var quoted var">?case</span>
    <span class="keyword1 command">by</span> <span class="operator">simp</span> <span class="main">(</span><span class="operator">blast</span> <span class="quasi_keyword">intro</span><span class="main main">:</span> add_less_mono ack_add_bound less_trans<span class="main">)</span>
<span class="keyword1 command">qed</span>
</pre>

For function composition itself, the assumptions refer to the existence of bounds for $g$ and for each $f$.
We use the lemma above in conjunction with the inequality `ack_nest_bound`.

<pre class="source">
<span class="keyword1 command">lemma</span> COMP_case<span class="main">:</span>
  <span class="keyword2 keyword">assumes</span> 1<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">∀</span></span><span class="bound">l</span><span class="main">.</span></span> <span class="free">g</span> <span class="bound">l</span> <span class="main">&lt;</span> ack <span class="free">kg</span> <span class="main">(</span>sum_list <span class="bound">l</span><span class="main">)</span><span>"</span>
      <span class="keyword2 keyword">and</span> 2<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">∀</span><span class="bound">f</span> <span class="main">∈</span> set</span> <span class="free">fs</span><span class="main">.</span> <span class="main">∃</span></span><span class="bound">kf</span><span class="main">.</span> <span class="main">∀</span><span class="bound">l</span><span class="main">.</span> <span class="bound">f</span> <span class="bound">l</span> <span class="main">&lt;</span> ack <span class="bound">kf</span> <span class="main">(</span>sum_list <span class="bound">l</span><span class="main">)</span><span>"</span>
  <span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">∃</span></span><span class="bound">k</span><span class="main">.</span></span> <span class="main">∀</span><span class="bound">l</span><span class="main">.</span> COMP <span class="free">g</span> <span class="free">fs</span>  <span class="bound">l</span> <span class="main">&lt;</span> ack <span class="bound">k</span> <span class="main">(</span>sum_list <span class="bound">l</span><span class="main">)</span><span>"</span>
  <span class="keyword1 command">unfolding</span> COMP_def
  <span class="keyword1 command">using</span> 1 COMP_map_aux <span class="main">[</span><span class="operator">OF</span> 2<span class="main">]</span> <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">meson</span> ack_less_mono2 ack_nest_bound less_trans<span class="main">)</span>
</pre>

#### The PREC case

Primitive recursion itself has the most complicated proof. We assume a nonempty argument list
(the other case is degenerate) and use induction on the actual integer on which the recursion is done.
The unusual form of the induction statement (adding `sum_list l` on the left) allows the relatively simple proof below.

<pre class="source">
<span class="keyword1 command">lemma</span> PREC_case_aux<span class="main">:</span>
  <span class="keyword2 keyword">assumes</span> f<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">⋀</span><span class="bound">l</span><span class="main">.</span> <span class="free">f</span> <span class="bound">l</span> <span class="main">+</span></span> sum_list</span> <span class="bound">l</span> <span class="main">&lt;</span> ack <span class="free">kf</span> <span class="main">(</span>sum_list <span class="bound">l</span><span class="main">)</span><span>"</span>
    <span class="keyword2 keyword">and</span> g<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">⋀</span><span class="bound">l</span><span class="main">.</span> <span class="free">g</span> <span class="bound">l</span> <span class="main">+</span></span> sum_list</span> <span class="bound">l</span> <span class="main">&lt;</span> ack <span class="free">kg</span> <span class="main">(</span>sum_list <span class="bound">l</span><span class="main">)</span><span>"</span>
  <span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span>PREC</span> <span class="free">f</span> <span class="free">g</span> <span class="main">(</span><span class="free">m</span><span class="main">#</span></span><span class="free">l</span><span class="main">)</span> <span class="main">+</span> sum_list <span class="main">(</span><span class="free">m</span><span class="main">#</span><span class="free">l</span><span class="main">)</span> <span class="main">&lt;</span> ack <span class="main">(</span>Suc <span class="main">(</span><span class="free">kf</span> <span class="main">+</span> <span class="free">kg</span><span class="main">)</span><span class="main">)</span> <span class="main">(</span>sum_list <span class="main">(</span><span class="free">m</span><span class="main">#</span><span class="free">l</span><span class="main">)</span><span class="main">)</span><span>"</span>
<span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">induct</span> <span class="quoted free">m</span><span class="main">)</span>
  <span class="keyword3 command">case</span> 0
  <span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="var quoted var">?case</span>
    <span class="keyword1 command">using</span> ack_less_mono1_aux f less_trans <span class="keyword1 command">by</span> <span class="operator">fastforce</span>
<span class="keyword1 command">next</span>
  <span class="keyword3 command">case</span> <span class="main">(</span>Suc <span class="skolem">m</span><span class="main">)</span>
  <span class="keyword1 command">let</span> <span class="var quoted var">?r</span> <span class="main">=</span> <span class="quoted"><span class="quoted"><span>"</span>PREC</span> <span class="free">f</span> <span class="free">g</span> <span class="main">(</span><span class="skolem">m</span><span class="main">#</span></span><span class="free">l</span><span class="main">)</span><span>"</span>
  <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">¬</span></span> <span class="free">g</span> <span class="main">(</span><span class="var">?r</span> <span class="main">#</span></span> <span class="skolem">m</span> <span class="main">#</span> <span class="free">l</span><span class="main">)</span> <span class="main">+</span> sum_list <span class="main">(</span><span class="var">?r</span> <span class="main">#</span> <span class="skolem">m</span> <span class="main">#</span> <span class="free">l</span><span class="main">)</span> <span class="main">&lt;</span> <span class="free">g</span> <span class="main">(</span><span class="var">?r</span> <span class="main">#</span> <span class="skolem">m</span> <span class="main">#</span> <span class="free">l</span><span class="main">)</span> <span class="main">+</span> <span class="main">(</span><span class="skolem">m</span> <span class="main">+</span> sum_list <span class="free">l</span><span class="main">)</span><span>"</span>
    <span class="keyword1 command">by</span> <span class="operator">force</span>
  <span class="keyword1 command">then</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">g</span> <span class="main">(</span><span class="var">?r</span> <span class="main">#</span></span> <span class="skolem">m</span> <span class="main">#</span></span> <span class="free">l</span><span class="main">)</span> <span class="main">+</span> <span class="main">(</span><span class="skolem">m</span> <span class="main">+</span> sum_list <span class="free">l</span><span class="main">)</span> <span class="main">&lt;</span> ack <span class="free">kg</span> <span class="main">(</span>sum_list <span class="main">(</span><span class="var">?r</span> <span class="main">#</span> <span class="skolem">m</span> <span class="main">#</span> <span class="free">l</span><span class="main">)</span><span class="main">)</span><span>"</span>
    <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">meson</span> g leI less_le_trans<span class="main">)</span>
  <span class="keyword1 command">moreover</span>
    <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">…</span> <span class="main">&lt;</span></span> ack</span> <span class="main">(</span><span class="free">kf</span> <span class="main">+</span> <span class="free">kg</span><span class="main">)</span> <span class="main">(</span>ack <span class="main">(</span>Suc <span class="main">(</span><span class="free">kf</span> <span class="main">+</span> <span class="free">kg</span><span class="main">)</span><span class="main">)</span> <span class="main">(</span><span class="skolem">m</span> <span class="main">+</span> sum_list <span class="free">l</span><span class="main">)</span><span class="main">)</span><span>"</span>
    <span class="keyword1 command">using</span> Suc.hyps <span class="keyword1 command">by</span> <span class="operator">simp</span> <span class="main">(</span><span class="operator">meson</span> ack_le_mono1 ack_less_mono2 le_add2 le_less_trans<span class="main">)</span>
  <span class="keyword1 command">ultimately</span> <span class="keyword3 command">show</span> <span class="var quoted var">?case</span>
    <span class="keyword1 command">by</span> <span class="operator">auto</span>
<span class="keyword1 command">qed</span>
</pre>

The previous result is generalised to cover the degenerate case of an empty argument list.

<pre class="source">
<span class="keyword1 command">lemma</span> <span>PREC_case_aux'</span><span class="main">:</span>
  <span class="keyword2 keyword">assumes</span> f<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">⋀</span><span class="bound">l</span><span class="main">.</span> <span class="free">f</span> <span class="bound">l</span> <span class="main">+</span></span> sum_list</span> <span class="bound">l</span> <span class="main">&lt;</span> ack <span class="free">kf</span> <span class="main">(</span>sum_list <span class="bound">l</span><span class="main">)</span><span>"</span>
    <span class="keyword2 keyword">and</span> g<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">⋀</span><span class="bound">l</span><span class="main">.</span> <span class="free">g</span> <span class="bound">l</span> <span class="main">+</span></span> sum_list</span> <span class="bound">l</span> <span class="main">&lt;</span> ack <span class="free">kg</span> <span class="main">(</span>sum_list <span class="bound">l</span><span class="main">)</span><span>"</span>
  <span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span>PREC</span> <span class="free">f</span> <span class="free">g</span> <span class="free">l</span> <span class="main">+</span></span> sum_list <span class="free">l</span> <span class="main">&lt;</span> ack <span class="main">(</span>Suc <span class="main">(</span><span class="free">kf</span> <span class="main">+</span> <span class="free">kg</span><span class="main">)</span><span class="main">)</span> <span class="main">(</span>sum_list <span class="free">l</span><span class="main">)</span><span>"</span>
  <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">smt</span> <span class="main main">(</span>verit<span class="main main">,</span> best<span class="main main">)</span> PREC.elims PREC_case_aux add.commute add.right_neutral f g less_ack2<span class="main">)</span>
</pre>

To obtain the PR case in the form we need for the main induction, other inequalities involving Ackermann's function are brought in.

<pre class="source">
<span class="keyword1 command">proposition</span> PREC_case<span class="main">:</span>
  <span class="quoted"><span class="quoted"><span>"</span><span class="main">⟦</span><span class="main">⋀</span><span class="bound">l</span><span class="main">.</span> <span class="free">f</span> <span class="bound">l</span> <span class="main">&lt;</span></span> ack</span> <span class="free">kf</span> <span class="main">(</span>sum_list <span class="bound">l</span><span class="main">)</span><span class="main">;</span> <span class="main">⋀</span><span class="bound">l</span><span class="main">.</span> <span class="free">g</span> <span class="bound">l</span> <span class="main">&lt;</span> ack <span class="free">kg</span> <span class="main">(</span>sum_list <span class="bound">l</span><span class="main">)</span><span class="main">⟧</span>
  <span class="main">⟹</span> <span class="main">∃</span><span class="bound">k</span><span class="main">.</span> <span class="main">∀</span><span class="bound">l</span><span class="main">.</span> PREC <span class="free">f</span> <span class="free">g</span> <span class="bound">l</span> <span class="main">&lt;</span> ack <span class="bound">k</span> <span class="main">(</span>sum_list <span class="bound">l</span><span class="main">)</span><span>"</span>
  <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> le_less_trans <span class="main main">[</span><span class="operator">OF</span> le_add1 PREC_case_aux'<span class="main main">]</span> ack_add_bound2<span class="main">)</span>
</pre>

### The main result

The result is by induction on the construction of a given primitive recursive function $f$,
but the machine proof is now trivial because we have proved all the cases of the induction above.

<pre class="source">
<span class="keyword1 command">lemma</span> ack_bounds_PRIMREC<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>PRIMREC</span> <span class="free">f</span> <span class="main">⟹</span> <span class="main">∃</span><span class="bound">k</span><span class="main">.</span> <span class="main">∀</span><span class="bound">l</span><span class="main">.</span> <span class="free">f</span> <span class="bound">l</span> <span class="main">&lt;</span> ack</span> <span class="bound">k</span> <span class="main">(</span>sum_list <span class="bound">l</span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">erule</span> PRIMREC.induct<span class="main">)</span> <span class="main">(</span><span class="operator">blast</span> <span class="quasi_keyword">intro</span><span class="main main">:</span> SC_case CONSTANT_case PROJ_case COMP_case PREC_case<span class="main">)</span><span class="main keyword3">+</span>
</pre>

The actual function that is not primitive recursive is Ackermann's function along its own diagonal.

<pre class="source">
<span class="keyword1 command">theorem</span> ack_not_PRIMREC<span class="main">:</span>
  <span class="quoted"><span class="quoted"><span>"</span><span class="main">¬</span></span> PRIMREC</span> <span class="main">(</span><span class="main">λ</span><span class="bound">l</span><span class="main">.</span> ack <span class="main">(</span>hd0 <span class="bound">l</span><span class="main">)</span> <span class="main">(</span>hd0 <span class="bound">l</span><span class="main">)</span><span class="main">)</span><span>"</span>
<span class="keyword1 command">proof</span>
  <span class="keyword3 command">assume</span> <span>*</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>PRIMREC</span> <span class="main">(</span><span class="main">λ</span><span class="bound">l</span><span class="main">.</span> ack</span> <span class="main">(</span>hd0 <span class="bound">l</span><span class="main">)</span> <span class="main">(</span>hd0 <span class="bound">l</span><span class="main">)</span><span class="main">)</span><span>"</span>
  <span class="keyword1 command">then</span> <span class="keyword3 command">obtain</span> <span class="skolem skolem">m</span> <span class="keyword2 keyword">where</span> m<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">⋀</span><span class="bound">l</span><span class="main">.</span> ack</span> <span class="main">(</span>hd0</span> <span class="bound">l</span><span class="main">)</span> <span class="main">(</span>hd0 <span class="bound">l</span><span class="main">)</span> <span class="main">&lt;</span> ack <span class="skolem">m</span> <span class="main">(</span>sum_list <span class="bound">l</span><span class="main">)</span><span>"</span>
    <span class="keyword1 command">using</span> ack_bounds_PRIMREC <span class="keyword1 command">by</span> <span class="operator">blast</span>
  <span class="keyword3 command">show</span> <span class="quoted">False</span>
    <span class="keyword1 command">using</span> m <span class="main">[</span><span class="operator">of</span> <span class="quoted quoted"><span>"</span><span class="main">[</span><span class="skolem">m</span><span class="main">]</span><span>"</span></span><span class="main">]</span> <span class="keyword1 command">by</span> <span class="operator">simp</span>
<span class="keyword1 command">qed</span>
</pre>


The [full development](https://www.isa-afp.org/entries/Ackermanns_not_PR.html) can be found in Isabelle's Archive of Formal Proofs.
I tidied it considerably in the course of writing this blog post. The new version
will remain hidden in the development branch of the AFP until Isabelle 2022 is released, around October.
Although the theorem is remarkable and deep, it's formal proof is concise: a mere 300 lines.

By the way, if you are looking for a function that is not primitive recursive and has a practical application, the answer is, any programming language interpreter.
An interpreter takes a source program (encoded somehow) and executes it, so it can easily run forever.
PR functions necessarily terminate.
And an interpreter for (a programming language of) PR functions will always terminate, because PR functions always terminate.
It cannot itself be PR (by the obvious diagonalisation argument).

