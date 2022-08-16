---
layout: post
title:  "Ackermann's function is not primitive recursive, I"
usemathjax: true
tags: [examples, Isabelle, Ackermann's function]
---

A university-level course on computation theory will invariably cover [recursive functions](https://plato.stanford.edu/entries/recursive-functions/): the model of computation developed by Gödel and Kleene.
Students learn about the [*primitive recursive*](https://en.wikipedia.org/wiki/Primitive_recursive_function) (PR) functions, a fairly natural idea, but also learn that the PR functions are insufficient.
True, these functions include all the familiar arithmetic operations,
as well as all the obvious syntactic operations on expressions that have been 
"Gödel-numbered" (coded in terms of arithmetic formulas).
Among the PR functions are many that cannot be regarded as *feasibly* computable because they grow at an utterly unimaginable rate. 
(And do not, not say "exponential" here: exponential growth is negligible in this world.)
The PR functions are insufficient because, in three simple lines, we can define 
an obviously computable function that grows faster than any of them.
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
The proof that Ackermann's function is not primitive recursive begins with a series of results about its growth for various argument patterns.
We'll cover those in today's post.
In a future post, we'll see how to define the primitive recursive functions themselves, inductively, in order to prove by induction (on the construction of some PR function *f*) that we can always find an argument to dominate *f*.

### Expressing Ackermann's function

As mentioned in that previous post, Isabelle/HOL provides a package that accepts a wide variety of recursive function definitions, in most cases dealing automatically with issues such as pattern matching and termination.
We can define Ackermann's function as follows:

<pre class="source">
<span class="keyword1"><span class="command">fun</span> <span class="entity">ack</span></span><span> </span><span class="main">::</span><span> </span><span class="quoted quoted"><span>"</span><span class="main">[</span>nat<span class="main">,</span>nat<span class="main">]</span><span> </span><span class="main">⇒</span><span> </span>nat<span>"</span></span><span> </span><span class="keyword2 keyword">where</span><span>
  </span><span class="quoted quoted"><span>"</span><span class="free">ack</span><span> </span><span class="main">0</span><span> </span><span class="free bound entity">n</span><span>             </span><span class="main">=</span><span> </span>Suc<span> </span><span class="free bound entity">n</span><span>"</span></span><span>
</span><span class="main">|</span><span> </span><span class="quoted quoted"><span>"</span><span class="free">ack</span><span> </span><span class="main">(</span>Suc<span> </span><span class="free bound entity">m</span><span class="main">)</span><span> </span><span class="main">0</span><span>       </span><span class="main">=</span><span> </span><span class="free">ack</span><span> </span><span class="free bound entity">m</span><span> </span><span class="main">1</span><span>"</span></span><span>
</span><span class="main">|</span><span> </span><span class="quoted quoted"><span>"</span><span class="free">ack</span><span> </span><span class="main">(</span>Suc<span> </span><span class="free bound entity">m</span><span class="main">)</span><span> </span><span class="main">(</span>Suc<span> </span><span class="free bound entity">n</span><span class="main">)</span><span> </span><span class="main">=</span><span> </span><span class="free">ack</span><span> </span><span class="free bound entity">m</span><span> </span><span class="main">(</span><span class="free">ack</span><span> </span><span class="main">(</span>Suc<span> </span><span class="free bound entity">m</span><span class="main">)</span><span> </span><span class="free bound entity">n</span><span class="main">)</span><span>"</span></span>
</pre>

Recall that such a specification is automatically transformed to eliminate the recursion, and the desired recursion equations are automatically proved from the hidden, low level definition.
Isabelle's recursion package also returns an induction rule tailored to this specific recursion.

### Properties involving the second argument of *A*

The formal development follows a [1991 paper](https://www.researchgate.net/publication/2662353_A_Machine_Checked_Proof_that_Ackermann's_Function_is_not_Primitive_Recursive)
by Nora Szasz, and the names of properties are hers.
She proved that Ackermann's Function was not PR using ALF, an early implementation of Martin-Löf type theory and a predecessor of [Agda](https://agda.readthedocs.io/en/v2.6.0.1/getting-started/what-is-agda.html). 

The Isabelle development doesn't strictly follow Szasz, and in particular the Ackermann recursion equations are already available to us, so the first property be proved is A4. It's an elementary inequality, proved by Ackermann induction (`Ack.induct`) followed by simplification.

<pre class="source">
<span class="keyword1 command">lemma</span> less_ack2 <span class="main">[</span><span class="operator">iff</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">j</span> <span class="main">&lt;</span> ack</span> <span class="free">i</span> <span class="free">j</span><span>"</span></span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">induct</span> <span class="quoted free">i</span> <span class="quoted free">j</span> <span class="quasi_keyword">rule</span><span class="main main">:</span> ack.induct<span class="main">)</span> <span class="operator">simp_all</span>
</pre>

The main theorem uses currying to freeze the first argument, regarding Ackermann's as a unary function.
We need to know that this function will be strictly monotonic, i.e. that Ackermann's is monotonic in its second argument.
This can be proved first for the successor case, 
again by Ackermann induction.

<pre class="source">
<span class="keyword1 command">lemma</span> ack_less_ack_Suc2 <span class="main">[</span><span class="operator">iff</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>ack</span> <span class="free">i</span> <span class="free">j</span> <span class="main">&lt;</span> ack</span> <span class="free">i</span> <span class="main">(</span>Suc <span class="free">j</span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">induct</span> <span class="quoted free">i</span> <span class="quoted free">j</span> <span class="quasi_keyword">rule</span><span class="main main">:</span> ack.induct<span class="main">)</span> <span class="operator">simp_all</span>
</pre>

Szasz calls this more general monotonicity result A5.

<pre class="source">
<span class="keyword1 command">lemma</span> ack_less_mono2<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">j</span> <span class="main">&lt;</span> <span class="free">k</span> <span class="main">⟹</span> ack</span> <span class="free">i</span> <span class="free">j</span> <span class="main">&lt;</span> ack</span> <span class="free">i</span> <span class="free">k</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> lift_Suc_mono_less<span class="main">)</span>
</pre>

Here's the non-strict version.

<pre class="source">
<span class="keyword1 command">lemma</span> ack_le_mono2<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">j</span> <span class="main">≤</span> <span class="free">k</span> <span class="main">⟹</span> ack</span> <span class="free">i</span> <span class="free">j</span> <span class="main">≤</span> ack</span> <span class="free">i</span> <span class="free">k</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> ack_less_mono2 less_mono_imp_le_mono<span class="main">)</span>
</pre>

### Properties involving the first argument of *A*

Next come a variety of inequalities involving both arguments, and concerned with what happens when we increase the first argument. The first property, A6, holds by a simple mathematical induction.
Note that sledgehammer has generated a proof of the induction step.

<pre class="source">
<span class="keyword1 command">lemma</span> ack2_le_ack1 <span class="main">[</span><span class="operator">iff</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>ack</span> <span class="free">i</span> <span class="main">(</span>Suc <span class="free">j</span><span class="main">)</span> <span class="main">≤</span> ack</span> <span class="main">(</span>Suc <span class="free">i</span><span class="main">)</span> <span class="free">j</span><span>"</span><span>
</span><span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">induct</span> <span class="quoted free">j</span><span class="main">)</span><span>
  </span><span class="keyword3 command">case</span> 0 <span class="keyword3 command">show</span> <span class="var quoted var">?case</span> <span class="keyword1 command">by</span> <span class="operator">simp</span><span>
</span><span class="keyword1 command">next</span><span>
  </span><span class="keyword3 command">case</span> <span class="main">(</span>Suc <span class="skolem">j</span><span class="main">)</span> <span class="keyword3 command">show</span> <span class="var quoted var">?case</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> Suc ack.simps<span class="main main">(</span>3<span class="main main">)</span> ack_le_mono2 le_trans less_ack2 less_eq_Suc_le<span class="main">)</span><span>
</span><span class="keyword1 command">qed</span>
</pre>

From this, we get a basic monotonicity result for the first argument:

<pre class="source">
<span class="keyword1 command">lemma</span> ack_less_ack_Suc1 <span class="main">[</span><span class="operator">iff</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>ack</span> <span class="free">i</span> <span class="free">j</span> <span class="main">&lt;</span> ack</span> <span class="main">(</span>Suc <span class="free">i</span><span class="main">)</span> <span class="free">j</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">blast</span> <span class="quasi_keyword">intro</span><span class="main main">:</span> ack_less_mono2 less_le_trans<span class="main">)</span>
</pre>

And then a result reminiscent of A4:
 
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

Curiously enough, Szasz did not mention requiring any of these results.

### First arguments of 1, 2 and 3

We already know that Ackermann's function, given a first argument of 0, denotes the successor.
Its behaviour for 1 (just adding 2) is Szasz' A8:

<pre class="source">
<span class="keyword1 command">lemma</span> ack_1 <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>ack</span> <span class="main">(</span>Suc <span class="main">0</span><span class="main">)</span> <span class="free">j</span> <span class="main">=</span> <span class="free">j</span> <span class="main">+</span> <span class="numeral">2</span><span>"</span></span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">induct</span> <span class="quoted free">j</span><span class="main">)</span> <span class="operator">simp_all</span>
</pre>

Its behaviour for a first argument of 2 (essentially doubling) is Szasz' A9:

<pre class="source">
<span class="keyword1 command">lemma</span> ack_2 <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>ack</span> <span class="main">(</span>Suc <span class="main">(</span>Suc <span class="main">0</span><span class="main">)</span><span class="main">)</span> <span class="free">j</span> <span class="main">=</span> <span class="numeral">2</span> <span class="main">*</span> <span class="free">j</span> <span class="main">+</span> <span class="numeral">3</span><span>"</span></span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">induct</span> <span class="quoted free">j</span><span class="main">)</span> <span class="operator">simp_all</span>
</pre>

The development doesn't require its behaviour for an argument of 3, but it's instructive to note what happens.
We go from 2 times something to 2 to the power something.
You can imagine what happens with an argument of 4. And you can't imagine what happens with an argument of 11.

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

I'd like to mention a couple of fine points. 

1. We aren't using Ackermann induction any more, but mostly good old mathematical induction.
How do you know which to choose? Mostly it's trial and error. It's often possible to get a proof using the "wrong" induction rule, but with a lot of needless pain.

2. Sometimes we write integer constants as ordinary numbers and sometimes as strings of successors (`Suc`). the successor form is necessary for rewriting by the Ackermann recursion equations. You can't count on Isabelle magically converting from one form to the other is needed.

### Monotonicity in the first argument

The following three lemmas are all related to Szasz' A7.
And I confess to a touch of blindness: monotonicity in Ackermann's first argument should follow easily from `ack_less_ack_Suc1`, but it isn't easy enough for sledgehammer, so we prove it another way.

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

And once again, a non-strict version:

<pre class="source">
<span class="keyword1 command">lemma</span> ack_le_mono1<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">i</span> <span class="main">≤</span> <span class="free">j</span> <span class="main">⟹</span> ack</span> <span class="free">i</span> <span class="free">k</span> <span class="main">≤</span> ack</span> <span class="free">j</span> <span class="free">k</span><span>"</span><span>
  </span><span class="keyword1 command">using</span> ack_less_mono1 le_eq_less_or_eq <span class="keyword1 command">by</span> <span class="operator">auto</span>
</pre>

### Building up the first argument

At risk of repeating myself, the proof that Ackermann's function is not PR involves choosing a suitable first argument. Each of the following results exhibits a suitable first argument $i$ such that $A(i,{-})$ grows faster than some other expression involving Ackermann's function. These will deal with various inductive cases connected with the construction of primitive recursive functions.

This one, A10, deals with nested function calls:

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

This one, A11, deals with the sum of two function calls:

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

I find this last result (A12) rather curious. Adding 4 to the first argument is a super gigantic leap and doesn't seem necessary. 
On the other hand, e can make it as big as we wish, so who cares?
And as stated, the theorem follows quickly from the previous one.


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

The [full development](https://www.isa-afp.org/entries/Ackermanns_not_PR.html) can be found in Isabelle's Archive of Formal Proofs.
You can confirm that nothing has been skipped up to this part of the development.
Although the final result is remarkable and deep, it's easy to formalise, 
which is why people were able to do with the early 90s.

By the way, if you are looking for a function that is not primitive recursive and has a practical application, the answer is, any programming language interpreter.
An interpreter takes a program (encoded somehow) and runs it, so it can easily run forever.
PR functions necessarily terminate.
And an interpreter for a programming language of PR functions will always terminate (because PR functions always terminate) but cannot be PR itself (by the obvious diagonalisation argument).


