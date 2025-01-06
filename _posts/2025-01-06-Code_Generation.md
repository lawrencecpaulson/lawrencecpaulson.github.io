---
layout: post
title:  Computing huge Fibonacci numbers, by proof and by code
usemathjax: true 
tags: [examples, newbies, Isabelle, Fibonacci]
---
One of the key tensions in theorem proving is between reasoning about things and using them in serious computations.
One way to address this tension is through *computational reflection*:
treating logical formulas as executable code, when you can.
The first realisation of this idea was the [Boyer/Moore theorem prover](https://doi.org/10.1145/321864.321875),
which was [initially created](https://doi.org/10.1007/s00165-019-00490-3) 
to verify programs written in Pure lisp.
Its assertion language was also pure Lisp,
so all formulas were automatically executable.
Subsequent proof assistants used much richer logics,
but there always seemed to be an executable sublanguage.
Then it is possible to perform computations within a proof
much more efficiently than by rewriting alone.
Here's an example using Fibonacci numbers.

### Evaluating Fibonacci numbers efficiently

We've now seen the Fibonacci numbers 0, 1, 1, 2, 3 ... 
[several times](https://lawrencecpaulson.github.io/tag/Fibonacci).
Their traditional definition, with its two recursive calls, 
yields an exponential computation.
That's because, e.g., to get $F_9$ you need $F_7$ and $F_8$,
and to get $F_8$ you end up computing $F_7$ a second time
and so on all the way down.

$$\begin{align} F_0 &= 0\\ F_1 &= 1\\ F_{n+2} &= F_n + F_{n+1}, \end{align}$$

But a linear computation is easily achieved: maintain *two*
Fibonacci numbers at a time, since adding them yields the next one.
We simply replace $(j,k)$ by $(k,j+k)$.
If we start with $(F_0,F_1)$, we reach $F_n$ after $n$ iterations.

<pre class="source">
<span class="keyword1 command">fun</span> <span class="entity">itfib</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">[</span>int</span><span class="main">,</span>int</span><span class="main">,</span>int<span class="main">]</span> <span class="main">⇒</span> int<span>"</span> <span class="keyword2 keyword">where</span><span>
  </span><span class="quoted"><span class="quoted"><span>"</span><span class="free">itfib</span> <span class="free bound entity">n</span> <span class="free bound entity">j</span> <span class="free bound entity">k</span> <span class="main">=</span></span> <span class="main">(</span><span class="keyword1">if</span></span> <span class="free bound entity">n</span><span class="main">≤</span><span class="main">1</span> <span class="keyword1">then</span> <span class="free bound entity">k</span> <span class="keyword1">else</span> <span class="free">itfib</span> <span class="main">(</span><span class="free bound entity">n</span><span class="main">-</span><span class="main">1</span><span class="main">)</span> <span class="free bound entity">k</span> <span class="main">(</span><span class="free bound entity">j</span><span class="main">+</span><span class="free bound entity">k</span><span class="main">)</span><span class="main">)</span><span>"</span>
</pre>

And – just like that – we can calculate $F_{200}$ in Isabelle
*by rewriting alone*, in under a second (0.7s):

<pre class="source">
<span class="keyword1 command">lemma</span> <span class="quoted"><span class="quoted"><span>"</span>itfib</span> <span class="numeral">200</span> <span class="main">0</span></span> <span class="main">1</span> <span class="main">=</span> <span class="numeral">280571172992510140037611932413038677189525</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="operator">simp</span>
</pre>

Just to be clear, Isabelle actually calculates that number itself
to verify the identity. It does so *efficiently*, thanks to a 
symbolic binary representation of integers provided by the built-in 
library. This point explains why `itfib` is declared to operate on
integers (type `int`) and not type `nat`: the natural numbers
are built up from 0 by `Suc`, the successor function, 
which could easily force the entire computation to use unary notation.
You can't go far representing numbers by a long string of `Suc`s.

### Proving the relationship with Fibonacci numbers

As we've seen before, the recursive definition above goes
directly into Isabelle. But this time, let's define the Fibonacci function
to yield integers, so that we can compute large integers.
Its argument type is still `nat` because that slightly simplifies 
the definitions and proofs, 
and the largest argument we'll use is only 200.

<pre class="source">
<span class="keyword1 command">fun</span> <span class="entity">fib</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>nat</span> <span class="main">⇒</span> int</span><span>"</span> <span class="keyword2 keyword">where</span><span>
    </span><span class="quoted"><span class="quoted"><span>"</span><span class="free">fib</span> <span class="main">0</span></span> <span class="main">=</span></span> <span class="main">0</span><span>"</span><span>
  </span><span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">fib</span> <span class="main">(</span>Suc</span> <span class="main">0</span></span><span class="main">)</span> <span class="main">=</span> <span class="main">1</span><span>"</span><span>
  </span><span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">fib</span> <span class="main">(</span>Suc</span> <span class="main">(</span>Suc</span> <span class="free bound entity">n</span><span class="main">)</span><span class="main">)</span> <span class="main">=</span> <span class="free">fib</span> <span class="free bound entity">n</span> <span class="main">+</span> <span class="free">fib</span> <span class="main">(</span>Suc <span class="free bound entity">n</span><span class="main">)</span><span>"</span>
</pre>

It's easy to prove the relationship between `itfib` and `fib`
hinted at above. This proof isn't difficult to find in Isabelle,
especially with the help of Sledgehammer.
It's also written up in my book 
[*ML for the Working Programmer*](https://www.cl.cam.ac.uk/~lp15/MLbook/pub-details.html).

<pre class="source">
<span class="keyword1 command">lemma</span> itfib_fib<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">n</span> <span class="main">&gt;</span></span> <span class="main">0</span></span> <span class="main">⟹</span> itfib <span class="free">n</span> <span class="main">(</span>fib <span class="free">k</span><span class="main">)</span> <span class="main">(</span>fib<span class="main">(</span><span class="free">k</span><span class="main">+</span><span class="main">1</span><span class="main">)</span><span class="main">)</span> <span class="main">=</span> fib <span class="main">(</span><span class="free">k</span><span class="main">+</span><span class="free">n</span><span class="main">)</span><span>"</span><span>
</span><span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">induction</span> <span class="quoted free">n</span> <span class="quasi_keyword">arbitrary</span><span class="main main">:</span> <span class="quoted free">k</span><span class="main">)</span><span>
  </span><span class="keyword3 command">case</span> 0<span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="var quoted var">?case</span><span>
    </span><span class="keyword1 command">by</span> <span class="operator">auto</span><span>
</span><span class="keyword1 command">next</span><span>
  </span><span class="keyword3 command">case</span> <span class="main">(</span>Suc <span class="skolem">n</span><span class="main">)</span><span>
  </span><span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">n</span> <span class="main">&gt;</span></span> <span class="main">0</span></span> <span class="main">⟹</span> itfib <span class="skolem">n</span> <span class="main">(</span>fib <span class="main">(</span><span class="skolem">k</span><span class="main">+</span><span class="main">1</span><span class="main">)</span><span class="main">)</span> <span class="main">(</span>fib <span class="skolem">k</span> <span class="main">+</span> fib <span class="main">(</span><span class="skolem">k</span><span class="main">+</span><span class="main">1</span><span class="main">)</span><span class="main">)</span> <span class="main">=</span> fib <span class="main">(</span><span class="skolem">k</span><span class="main">+</span><span class="skolem">n</span><span class="main">+</span><span class="main">1</span><span class="main">)</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> Suc.IH Suc_eq_plus1 add.commute add_Suc_right fib.simps<span class="main main">(</span>3<span class="main main">)</span><span class="main">)</span><span>
  </span><span class="keyword1 command">with</span> Suc <span class="keyword3 command">show</span> <span class="var quoted var">?case</span><span>
    </span><span class="keyword1 command">by</span> <span class="operator">simp</span><span>
</span><span class="keyword1 command">qed</span>
</pre>

(It's on page 224. You should [buy a copy](https://doi.org/10.1017/CBO9780511811326), but you can also find the chapter [online](https://www.cl.cam.ac.uk/~lp15/MLbook/PDF/chapter6.pdf).)

### Computing Fibonacci numbers efficiently

Higher-order logic contains a (rather ad-hoc) executable sublanguage.
In particular, recursive function definitions such as
those shown here are computable.
The Isabelle/HOL [code generator](https://isabelle.in.tum.de/dist/Isabelle/doc/codegen.pdf)
translates it into functional languages such as Standard ML
and OCaml. The translation scheme maps like to like,
so while it is "obviously correct", it is not verified,
and purists prefer to avoid it.

The code generation package provides a top-level command,
<span class="keyword1 command">value</span>, which returns the value 
computed by an executable term; rewriting would return the
same value, but more slowly.
Similarly, `eval` is a proof method that can replace `simp`
when the necessary simplification can be done by computation alone.

Let's try <span class="keyword1 command">value</span> with Fibonacci numbers.
Naive evaluation of $F_{44}$ takes a long time 
despite the use of efficient integers, 
because the recursion is exponential.
(It returns 701408733 in about 10 seconds.)

<pre class="source">
<span class="keyword1 command">value</span> <span class="quoted"><span class="quoted"><span>"</span>fib</span> <span class="numeral">44</span><span>"</span></span>
</pre>

What to do? First, delete the naive recursion rules for `fib` 
from the code generator.

<pre class="source">
<span class="keyword1 command">declare</span> fib.simps <span class="main">[</span><span class="operator">code</span> <span class="quasi_keyword quasi_keyword quasi_keyword">del</span><span class="main">]</span>
</pre>

Second, provide a new way of computing `fib`: a so-called
*code equation* (indicated by the `[code]` attribute). 

<pre class="source">
<span class="keyword1 command">lemma</span> fib_eq_itfib<span class="main">[</span><span class="operator">code</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>fib</span> <span class="free">n</span> <span class="main">=</span></span> <span class="main">(</span><span class="keyword1">if</span> <span class="free">n</span><span class="main">=</span><span class="main">0</span> <span class="keyword1">then</span> <span class="main">0</span> <span class="keyword1">else</span> itfib <span class="main">(</span>int <span class="free">n</span><span class="main">)</span> <span class="main">0</span> <span class="main">1</span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword1 command">using</span> itfib_fib <span class="main">[</span><span class="operator">of</span> <span class="quoted free">n</span> <span class="quoted main">0</span><span class="main">]</span> <span class="keyword1 command">by</span> <span class="operator">simp</span>
</pre>

The new setup is much faster. 
It takes only 0.1 seconds to compute $F_{200} = 280571172992510140037611932413038677189525$.

<pre class="source">
<span class="keyword1 command">value</span> <span class="quoted"><span class="quoted"><span>"</span>fib</span> <span class="numeral">200</span><span>"</span></span>
</pre>

The relevant Isabelle theory file is available
[here](/Isabelle-Examples/Fib_Iter.thy).
