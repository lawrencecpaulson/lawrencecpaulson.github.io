---
layout: post
title:  "Ackermann's function is not primitive recursive, I"
usemathjax: true
tags: [examples, Isabelle, Ackermann's function]
---

A university-level course on computation theory will invariably cover [recursive functions](https://plato.stanford.edu/entries/recursive-functions/): the model of computation developed by Gödel and Kleene.
Students learn about the *primitive recursive* (PR) functions, a fairly natural idea, but also learn that in themselves they are inadequate.
The PR functions include many that cannot be regarded as feasibly computable because they grow unimaginably. (And do not, not say "exponential" here: exponential growth is negligible in this world.)
And yet, in three simple lines, we can define a function that grows faster than any PR function.
It is, of course, [Ackermann's function](https://plato.stanford.edu/entries/recursive-functions/#AckePeteFunc).


### The Ackermann-Péter function

As I have mentioned in a [previous post]({% post_url 2022-02-09-Ackermann-example %}),
Ackermann's "generalised exponential" (simplified by Rózsa Péter) is as follows:

$$
\begin{align*}
	A(0,n) & = n+1\\
	A(m+1,0) & = A(m,1)\\
	A(m+1,n+1) & = A(m,A(m+1,n)).
\end{align*}
$$

Its first argument determines the rate of growth.
Arguments of 0 and 1 yield trivial functions, but things get nasty from 4 onwards.
The proof that Ackermann's function is not primitive recursive begins with a series of results about its grown through various arguments.
Then we define the primitive recursive functions themselves, inductively, in order to prove by induction (on the construction of some PR function *f*) that we can always find an argument to dominate *f*.

### Expressing Ackermann's function

As mentioned in that previous post, Isabelle/HOL provides a package that accepts a wide variety of recursive function definitions, in most cases dealing automatically with issues such as pattern matching termination.
We can define Ackermann's function as follows:

<pre class="source">
<span class="keyword1"><span class="command">fun</span> <span class="entity">ack</span></span><span> </span><span class="main">::</span><span> </span><span class="quoted quoted"><span>"</span><span class="main">[</span>nat<span class="main">,</span>nat<span class="main">]</span><span> </span><span class="main">⇒</span><span> </span>nat<span>"</span></span><span> </span><span class="keyword2 keyword">where</span><span>
  </span><span class="quoted quoted"><span>"</span><span class="free">ack</span><span> </span><span class="main">0</span><span> </span><span class="free bound entity">n</span><span>             </span><span class="main">=</span><span> </span>Suc<span> </span><span class="free bound entity">n</span><span>"</span></span><span>
</span><span class="main">|</span><span> </span><span class="quoted quoted"><span>"</span><span class="free">ack</span><span> </span><span class="main">(</span>Suc<span> </span><span class="free bound entity">m</span><span class="main">)</span><span> </span><span class="main">0</span><span>       </span><span class="main">=</span><span> </span><span class="free">ack</span><span> </span><span class="free bound entity">m</span><span> </span><span class="main">1</span><span>"</span></span><span>
</span><span class="main">|</span><span> </span><span class="quoted quoted"><span>"</span><span class="free">ack</span><span> </span><span class="main">(</span>Suc<span> </span><span class="free bound entity">m</span><span class="main">)</span><span> </span><span class="main">(</span>Suc<span> </span><span class="free bound entity">n</span><span class="main">)</span><span> </span><span class="main">=</span><span> </span><span class="free">ack</span><span> </span><span class="free bound entity">m</span><span> </span><span class="main">(</span><span class="free">ack</span><span> </span><span class="main">(</span>Suc<span> </span><span class="free bound entity">m</span><span class="main">)</span><span> </span><span class="free bound entity">n</span><span class="main">)</span><span>"</span></span>
</pre>

A4

<pre class="source">
<span class="keyword1 command">lemma</span> less_ack2 <span class="main">[</span><span class="operator">iff</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">j</span> <span class="main">&lt;</span> ack</span> <span class="free">i</span> <span class="free">j</span><span>"</span></span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">induct</span> <span class="quoted free">i</span> <span class="quoted free">j</span> <span class="quasi_keyword">rule</span><span class="main main">:</span> ack.induct<span class="main">)</span> <span class="operator">simp_all</span>
</pre>

The following three results prove (strict) monotonicity in the second argument.
First, a single step version of the property.

<pre class="source">
<span class="keyword1 command">lemma</span> ack_less_ack_Suc2 <span class="main">[</span><span class="operator">iff</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>ack</span> <span class="free">i</span> <span class="free">j</span> <span class="main">&lt;</span> ack</span> <span class="free">i</span> <span class="main">(</span>Suc <span class="free">j</span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">induct</span> <span class="quoted free">i</span> <span class="quoted free">j</span> <span class="quasi_keyword">rule</span><span class="main main">:</span> ack.induct<span class="main">)</span> <span class="operator">simp_all</span>
</pre>

A5

<pre class="source">
<span class="keyword1 command">lemma</span> ack_less_mono2<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">j</span> <span class="main">&lt;</span> <span class="free">k</span> <span class="main">⟹</span> ack</span> <span class="free">i</span> <span class="free">j</span> <span class="main">&lt;</span> ack</span> <span class="free">i</span> <span class="free">k</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> lift_Suc_mono_less<span class="main">)</span>
</pre>


<pre class="source">
<span class="keyword1 command">lemma</span> ack_le_mono2<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">j</span> <span class="main">≤</span> <span class="free">k</span> <span class="main">⟹</span> ack</span> <span class="free">i</span> <span class="free">j</span> <span class="main">≤</span> ack</span> <span class="free">i</span> <span class="free">k</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> ack_less_mono2 less_mono_imp_le_mono<span class="main">)</span>
</pre>

A6

<pre class="source">
<span class="keyword1 command">lemma</span> ack2_le_ack1 <span class="main">[</span><span class="operator">iff</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>ack</span> <span class="free">i</span> <span class="main">(</span>Suc <span class="free">j</span><span class="main">)</span> <span class="main">≤</span> ack</span> <span class="main">(</span>Suc <span class="free">i</span><span class="main">)</span> <span class="free">j</span><span>"</span><span>
</span><span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">induct</span> <span class="quoted free">j</span><span class="main">)</span><span>
  </span><span class="keyword3 command">case</span> 0 <span class="keyword3 command">show</span> <span class="var quoted var">?case</span> <span class="keyword1 command">by</span> <span class="operator">simp</span><span>
</span><span class="keyword1 command">next</span><span>
  </span><span class="keyword3 command">case</span> <span class="main">(</span>Suc <span class="skolem">j</span><span class="main">)</span> <span class="keyword3 command">show</span> <span class="var quoted var">?case</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> Suc ack.simps<span class="main main">(</span>3<span class="main main">)</span> ack_le_mono2 le_trans less_ack2 less_eq_Suc_le<span class="main">)</span><span>
</span><span class="keyword1 command">qed</span>
</pre>


<pre class="source">
<span class="keyword1 command">lemma</span> ack_less_ack_Suc1 <span class="main">[</span><span class="operator">iff</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>ack</span> <span class="free">i</span> <span class="free">j</span> <span class="main">&lt;</span> ack</span> <span class="main">(</span>Suc <span class="free">i</span><span class="main">)</span> <span class="free">j</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">blast</span> <span class="quasi_keyword">intro</span><span class="main main">:</span> ack_less_mono2 less_le_trans<span class="main">)</span>
</pre>

extra lemma

<pre class="source">
<span class="keyword1 command">lemma</span> less_ack1 <span class="main">[</span><span class="operator">iff</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">i</span> <span class="main">&lt;</span> ack</span> <span class="free">i</span> <span class="free">j</span><span>"</span></span><span>
</span><span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">induct</span> <span class="quoted free">i</span><span class="main">)</span><span>
  </span><span class="keyword3 command">case</span> 0<span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="var quoted var">?case</span><span>
    </span><span class="keyword1 command">by</span> <span class="operator">simp</span><span>
</span><span class="keyword1 command">next</span><span>
  </span><span class="keyword3 command">case</span> <span class="main">(</span>Suc <span class="skolem">i</span><span class="main">)</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="var quoted var">?case</span><span>
    </span><span class="keyword1 command">using</span> less_trans_Suc <span class="keyword1 command">by</span> <span class="operator">blast</span><span>
</span><span class="keyword1 command">qed</span>
</pre>

A8

<pre class="source">
<span class="keyword1 command">lemma</span> ack_1 <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>ack</span> <span class="main">(</span>Suc <span class="main">0</span><span class="main">)</span> <span class="free">j</span> <span class="main">=</span> <span class="free">j</span> <span class="main">+</span> <span class="numeral">2</span><span>"</span></span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">induct</span> <span class="quoted free">j</span><span class="main">)</span> <span class="operator">simp_all</span>
</pre>

A9

<pre class="source">
<span class="keyword1 command">lemma</span> ack_2 <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>ack</span> <span class="main">(</span>Suc <span class="main">(</span>Suc <span class="main">0</span><span class="main">)</span><span class="main">)</span> <span class="free">j</span> <span class="main">=</span> <span class="numeral">2</span> <span class="main">*</span> <span class="free">j</span> <span class="main">+</span> <span class="numeral">3</span><span>"</span></span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">induct</span> <span class="quoted free">j</span><span class="main">)</span> <span class="operator">simp_all</span>
</pre>

Not needed but interesting

<pre class="source">
<span class="keyword1 command">lemma</span> ack_3<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>ack</span> <span class="main">(</span>Suc <span class="main">(</span>Suc <span class="main">(</span>Suc <span class="main">0</span><span class="main">)</span><span class="main">)</span><span class="main">)</span> <span class="free">j</span> <span class="main">=</span> <span class="numeral">2</span> <span class="main">^</span> <span class="main">(</span><span class="free">j</span><span class="main">+</span><span class="numeral">3</span><span class="main">)</span> <span class="main">-</span> <span class="numeral">3</span><span>"</span></span><span>
</span><span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">induct</span> <span class="quoted free">j</span><span class="main">)</span><span>
  </span><span class="keyword3 command">case</span> 0<span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="var quoted var">?case</span> <span class="keyword1 command">by</span> <span class="operator">simp</span><span>
</span><span class="keyword1 command">next</span><span>
  </span><span class="keyword3 command">case</span> <span class="main">(</span>Suc <span class="skolem">j</span><span class="main">)</span><span>
  </span><span class="keyword1 command">with</span> less_le_trans <span class="keyword3 command">show</span> <span class="var quoted var">?case</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">fastforce</span> <span class="quasi_keyword">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> power_add <span class="dynamic dynamic">algebra_simps</span><span class="main">)</span><span>
</span><span class="keyword1 command">qed</span><</pre>

A7

<pre class="source">
<span class="keyword1 command">lemma</span> ack_less_mono1_aux<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>ack</span> <span class="free">i</span> <span class="free">k</span> <span class="main">&lt;</span> ack</span> <span class="main">(</span>Suc <span class="main">(</span><span class="free">i</span><span class="main">+</span><span class="free">j</span><span class="main">)</span><span class="main">)</span> <span class="free">k</span><span>"</span><span>
</span><span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">induct</span> <span class="quoted free">i</span> <span class="quoted free">k</span> <span class="quasi_keyword">rule</span><span class="main main">:</span> ack.induct<span class="main">)</span><span>
  </span><span class="keyword3 command">case</span> <span class="main">(</span>1 <span class="skolem">n</span><span class="main">)</span> <span class="keyword3 command">show</span> <span class="var quoted var">?case</span><span>
    </span><span class="keyword1 command">using</span> less_le_trans <span class="keyword1 command">by</span> <span class="operator">auto</span><span>
</span><span class="keyword1 command">next</span><span>
  </span><span class="keyword3 command">case</span> <span class="main">(</span>2 <span class="skolem">m</span><span class="main">)</span> <span class="keyword3 command">thus</span> <span class="var quoted var">?case</span> <span class="keyword1 command">by</span> <span class="operator">simp</span><span>
</span><span class="keyword1 command">next</span><span>
  </span><span class="keyword3 command">case</span> <span class="main">(</span>3 <span class="skolem">m</span> <span class="skolem">n</span><span class="main">)</span> <span class="keyword3 command">thus</span> <span class="var quoted var">?case</span><span>
    </span><span class="keyword1 command">using</span> ack_less_mono2 less_trans <span class="keyword1 command">by</span> <span class="operator">fastforce</span><span>
</span><span class="keyword1 command">qed</span>
</pre>


<pre class="source">
<span class="keyword1 command">lemma</span> ack_less_mono1<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">i</span> <span class="main">&lt;</span> <span class="free">j</span> <span class="main">⟹</span> ack</span> <span class="free">i</span> <span class="free">k</span> <span class="main">&lt;</span> ack</span> <span class="free">j</span> <span class="free">k</span><span>"</span><span>
  </span><span class="keyword1 command">using</span> ack_less_mono1_aux less_iff_Suc_add <span class="keyword1 command">by</span> <span class="operator">auto</span>
</pre>

A7'

<pre class="source">
<span class="keyword1 command">lemma</span> ack_le_mono1<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">i</span> <span class="main">≤</span> <span class="free">j</span> <span class="main">⟹</span> ack</span> <span class="free">i</span> <span class="free">k</span> <span class="main">≤</span> ack</span> <span class="free">j</span> <span class="free">k</span><span>"</span><span>
  </span><span class="keyword1 command">using</span> ack_less_mono1 le_eq_less_or_eq <span class="keyword1 command">by</span> <span class="operator">auto</span>
</pre>

A10

<pre class="source">
<span class="keyword1 command">lemma</span> ack_nest_bound<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>ack</span> <span class="free">i1</span> <span class="main">(</span>ack</span> <span class="free">i2</span> <span class="free">j</span><span class="main">)</span> <span class="main">&lt;</span> ack <span class="main">(</span><span class="numeral">2</span> <span class="main">+</span> <span class="main">(</span><span class="free">i1</span> <span class="main">+</span> <span class="free">i2</span><span class="main">)</span><span class="main">)</span> <span class="free">j</span><span>"</span><span>
</span><span class="keyword1 command">proof</span> <span class="operator">-</span><span>
  </span><span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span>ack</span> <span class="free">i1</span> <span class="main">(</span>ack</span> <span class="free">i2</span> <span class="free">j</span><span class="main">)</span> <span class="main">&lt;</span> ack <span class="main">(</span><span class="free">i1</span> <span class="main">+</span> <span class="free">i2</span><span class="main">)</span> <span class="main">(</span>ack <span class="main">(</span>Suc <span class="main">(</span><span class="free">i1</span> <span class="main">+</span> <span class="free">i2</span><span class="main">)</span><span class="main">)</span> <span class="free">j</span><span class="main">)</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">meson</span> ack_le_mono1 ack_less_mono1 ack_less_mono2 le_add1 le_trans less_add_Suc2 not_less<span class="main">)</span><span>
  </span><span class="keyword1 command">also</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">...</span> <span class="main">=</span> ack</span> <span class="main">(</span>Suc <span class="main">(</span><span class="free">i1</span> <span class="main">+</span> <span class="free">i2</span><span class="main">)</span><span class="main">)</span> <span class="main">(</span>Suc <span class="free">j</span><span class="main">)</span><span>"</span></span><span>
    </span><span class="keyword1 command">by</span> <span class="operator">simp</span><span>
  </span><span class="keyword1 command">also</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">...</span> <span class="main">≤</span> ack</span> <span class="main">(</span><span class="numeral">2</span> <span class="main">+</span> <span class="main">(</span><span class="free">i1</span> <span class="main">+</span> <span class="free">i2</span><span class="main">)</span><span class="main">)</span> <span class="free">j</span><span>"</span></span><span>
    </span><span class="keyword1 command">using</span> ack2_le_ack1 add_2_eq_Suc <span class="keyword1 command">by</span> <span class="operator">presburger</span><span>
  </span><span class="keyword1 command">finally</span> <span class="keyword3 command">show</span> <span class="var quoted var">?thesis</span> <span class="keyword1 command">.</span><span>
</span><span class="keyword1 command">qed</span>
</pre>

A11

<pre class="source">
<span class="keyword1 command">lemma</span> ack_add_bound<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>ack</span> <span class="free">i1</span> <span class="free">j</span> <span class="main">+</span> ack</span> <span class="free">i2</span> <span class="free">j</span> <span class="main">&lt;</span> ack <span class="main">(</span><span class="numeral">4</span> <span class="main">+</span> <span class="main">(</span><span class="free">i1</span> <span class="main">+</span> <span class="free">i2</span><span class="main">)</span><span class="main">)</span> <span class="free">j</span><span>"</span><span>
</span><span class="keyword1 command">proof</span> <span class="operator">-</span><span>
  </span><span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span>ack</span> <span class="free">i1</span> <span class="free">j</span> <span class="main">≤</span> ack</span> <span class="main">(</span><span class="free">i1</span> <span class="main">+</span> <span class="free">i2</span><span class="main">)</span> <span class="free">j</span><span>"</span> <span class="quoted"><span class="quoted"><span>"</span>ack</span> <span class="free">i2</span> <span class="free">j</span> <span class="main">≤</span> ack</span> <span class="main">(</span><span class="free">i1</span> <span class="main">+</span> <span class="free">i2</span><span class="main">)</span> <span class="free">j</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp_all</span> <span class="quasi_keyword">add</span><span class="main main">:</span> ack_le_mono1<span class="main">)</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span>ack</span> <span class="free">i1</span> <span class="free">j</span> <span class="main">+</span> ack</span> <span class="free">i2</span> <span class="free">j</span> <span class="main">&lt;</span> ack <span class="main">(</span>Suc <span class="main">(</span>Suc <span class="main">0</span><span class="main">)</span><span class="main">)</span> <span class="main">(</span>ack <span class="main">(</span><span class="free">i1</span> <span class="main">+</span> <span class="free">i2</span><span class="main">)</span> <span class="free">j</span><span class="main">)</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="operator">simp</span><span>
  </span><span class="keyword1 command">also</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">...</span> <span class="main">&lt;</span> ack</span> <span class="main">(</span><span class="numeral">4</span> <span class="main">+</span> <span class="main">(</span><span class="free">i1</span> <span class="main">+</span> <span class="free">i2</span><span class="main">)</span><span class="main">)</span> <span class="free">j</span><span>"</span></span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> ack_nest_bound add.assoc numeral_2_eq_2 numeral_Bit0<span class="main">)</span><span>
  </span><span class="keyword1 command">finally</span> <span class="keyword3 command">show</span> <span class="var quoted var">?thesis</span> <span class="keyword1 command">.</span><span>
</span><span class="keyword1 command">qed</span>
</pre>

A12

<pre class="source">
<span class="keyword1 command">lemma</span> ack_add_bound2<span class="main">:</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">i</span> <span class="main">&lt;</span> ack</span> <span class="free">k</span> <span class="free">j</span><span>"</span></span> <span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">i</span> <span class="main">+</span> <span class="free">j</span> <span class="main">&lt;</span> ack</span> <span class="main">(</span><span class="numeral">4</span> <span class="main">+</span> <span class="free">k</span><span class="main">)</span> <span class="free">j</span><span>"</span></span><span>
</span><span class="keyword1 command">proof</span> <span class="operator">-</span><span>
  </span><span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">i</span> <span class="main">+</span> <span class="free">j</span> <span class="main">&lt;</span> ack</span> <span class="free">k</span> <span class="free">j</span> <span class="main">+</span> ack</span> <span class="main">0</span> <span class="free">j</span><span>"</span><span>
    </span><span class="keyword1 command">using</span> assms <span class="keyword1 command">by</span> <span class="operator">auto</span><span>
  </span><span class="keyword1 command">also</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">...</span> <span class="main">&lt;</span> ack</span> <span class="main">(</span><span class="numeral">4</span> <span class="main">+</span> <span class="free">k</span><span class="main">)</span> <span class="free">j</span><span>"</span></span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> ack_add_bound add.right_neutral<span class="main">)</span><span>
  </span><span class="keyword1 command">finally</span> <span class="keyword3 command">show</span> <span class="var quoted var">?thesis</span> <span class="keyword1 command">.</span><span>
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



The[full development](https://www.isa-afp.org/entries/Ackermanns_not_PR.html)  
can be found in Isabelle's Archive of Formal Proofs.
