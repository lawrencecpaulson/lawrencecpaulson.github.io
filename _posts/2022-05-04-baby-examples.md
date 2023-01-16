---
layout: post
title:  "Getting started with Isabelle: baby examples, cool proof methods"
usemathjax: true 
tags: examples Isabelle newbies sledgehammer
---

For absolute beginners, proof assistants are daunting. Everything you do seems to go wrong. So let's have some super simple examples that show how to get started while highlighting some pitfalls.

### An algebraic identity

First, a note of caution: Isabelle/HOL is great at inferring types in expressions, but the simplest examples might well be ambiguous, leading to frustration.
For example, it should be trivial to prove $3-2=1$ using `auto`, but it fails. Hovering with your mouse near the blue dot in the left margin, or checking the Output panel, you might see a hint about a missing type constraint:

<img src="/images/3minus2.png" alt="trying and failing to prove 3-2=1" width="500"/>

Isabelle sees that the problem involves numbers, but it can't infer a precise type and therefore it's not clear whether substraction is even meaningful. So it's wise always to include an explicit type constraint in problems involving numeric types.
You can also use CTRL-hover (CMD-hover on Macs) to inspect the type of any variable in Isabelle/jEdit. (More on this next week!)

In the following trivial algebraic identity (due to Kevin Buzzard), we specify the type of `x` using <span class="keyword2 keyword">fixes</span>.
It's trivial to prove, using a single call to the simplifier.

<pre class="source">
<span class="keyword1 command">lemma</span><span>
  </span><span class="keyword2 keyword">fixes</span> <span class="free">x</span><span class="main">::</span><span class="quoted">real</span><span>
  </span><span class="keyword2 keyword">shows</span> <span class="quoted quoted"><span>"</span><span class="main">(</span><span class="free">x</span><span class="main">+</span><span class="free">y</span><span class="main">)</span><span class="main">*</span><span class="main">(</span><span class="free">x</span><span class="main">+</span><span class="numeral">2</span><span class="main">*</span><span class="free">y</span><span class="main">)</span><span class="main">*</span><span class="main">(</span><span class="free">x</span><span class="main">+</span><span class="numeral">3</span><span class="main">*</span><span class="free">y</span><span class="main">)</span> <span class="main">=</span> <span class="free">x</span><span class="main">^</span><span class="numeral">3</span> <span class="main">+</span> <span class="numeral">6</span><span class="main">*</span><span class="free">x</span><span class="main">^</span><span class="numeral">2</span><span class="main">*</span><span class="free">y</span> <span class="main">+</span> <span class="numeral">11</span><span class="main">*</span><span class="free">x</span><span class="main">*</span><span class="free">y</span><span class="main">^</span><span class="numeral">2</span> <span class="main">+</span> <span class="numeral">6</span><span class="main">*</span><span class="free">y</span><span class="main">^</span><span class="numeral">3</span><span>"</span></span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> <span class="dynamic dynamic">algebra_simps</span> eval_nat_numeral<span class="main">)</span>
</pre>

The arguments given to the simplifier are critical:

* `algebra_simps` is a bundle of simplification rules (*simprules*), containing the obvious algebraic laws: associativity and commutativity to arrange terms into a canonical order, and distributive laws to multiply out all the terms.
* `eval_nat_numeral` is a single simprule that expands numerals such as 3 and 47055833459 from their internal symbolic binary notation into unary notation as a series of `Suc` applications to `0`. (Sadly, the second example will not terminate.) 

The `Suc` form is necessary to trigger the simplification $a^{n+1}=a\times a^n$; this identity is called `power_Suc`, but it is a *default simprule*, meaning we don't need to mention it.

With both rules included, `simp` solves the problem. Using only one of them makes the expressions blow up. A skill you need to develop is figuring out what to do when faced with a sea of symbols: did you use too many simplification rules, or too few?
A good strategy is to simplify with the fewest possible rules and gradually add more.
Gigantic formulas are impossible to grasp, but close inspection sometimes reveals subexpressions that could be eliminated through the use of another simprule.

### A numerical inequality

The next example, also due to Kevin, is to show that $\sqrt 2 + \sqrt 3 < \sqrt 10$.
One obvious approach is to get rid of some of the radicals by squaring both sides.
So we state the corresponding formula as a lemma using <span class="keyword2 keyword">have</span>  and open a <span class="keyword2 keyword">proof</span> using the same simplification rules as in the previous example. It leaves us with the task of showing $2(\sqrt 2\sqrt 3) < 5$. Repeating the previous idea,
we use <span class="keyword2 keyword">have</span> to state that formula with both sides squared, then apply those simplification rules again. (It works because $24<25$.)
Curiously, the <span class="keyword2 keyword">show</span> commands, although both inferring $x<y$ from $x^2<y^2$,  require different formal justifications, both found by [sledgehammer]({% post_url 2022-04-13-Sledgehammer %}).
The rest of the proof below was typed in manually.

<pre class="source">
<span class="keyword1 command">lemma</span> <span class="quoted quoted"><span>"</span>sqrt <span class="numeral">2</span> <span class="main">+</span> sqrt <span class="numeral">3</span> <span class="main">&lt;</span> sqrt <span class="numeral">10</span><span>"</span></span><span>
</span><span class="keyword1 command">proof</span> <span class="operator">-</span><span>
  </span><span class="keyword1 command">have</span> <span class="quoted quoted"><span>"</span><span class="main">(</span>sqrt <span class="numeral">2</span> <span class="main">+</span> sqrt <span class="numeral">3</span><span class="main">)</span><span class="main">^</span><span class="numeral">2</span> <span class="main">&lt;</span> <span class="main">(</span>sqrt <span class="numeral">10</span><span class="main">)</span><span class="main">^</span><span class="numeral">2</span><span>"</span></span><span>
  </span><span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> <span class="dynamic dynamic">algebra_simps</span> eval_nat_numeral<span class="main">)</span><span>
    </span><span class="keyword1 command">have</span> <span class="quoted quoted"><span>"</span><span class="main">(</span><span class="numeral">2</span> <span class="main">*</span> <span class="main">(</span>sqrt <span class="numeral">2</span> <span class="main">*</span> sqrt <span class="numeral">3</span><span class="main">)</span><span class="main">)</span><span class="main">^</span><span class="numeral">2</span> <span class="main">&lt;</span> <span class="numeral">5</span> <span class="main">^</span> <span class="numeral">2</span><span>"</span></span><span>
      </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> <span class="dynamic dynamic">algebra_simps</span> eval_nat_numeral<span class="main">)</span><span>
    </span><span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="quoted quoted"><span>"</span><span class="numeral">2</span> <span class="main">*</span> <span class="main">(</span>sqrt <span class="numeral">2</span> <span class="main">*</span> sqrt <span class="numeral">3</span><span class="main">)</span> <span class="main">&lt;</span> <span class="numeral">5</span><span>"</span></span><span>
      </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">smt</span> <span class="main main">(</span>verit<span class="main main">,</span> best<span class="main main">)</span> power_mono<span class="main">)</span><span>
  </span><span class="keyword1 command">qed</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="var quoted var">?thesis</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> real_less_rsqrt<span class="main">)</span><span>
</span><span class="keyword1 command">qed</span>
</pre>

But there's a much simpler way to prove the theorem above: by numerical evaluation using [Johannes Hölzl's](https://home.in.tum.de//~hoelzl/) amazing [approximation tactic](https://www.researchgate.net/publication/238740304_Proving_Inequalities_over_Reals_with_Computation_in_IsabelleHOL).

<pre class="source">
<span class="keyword1 command">lemma</span> <span class="quoted quoted"><span>"</span>sqrt <span class="numeral">2</span> <span class="main">+</span> sqrt <span class="numeral">3</span> <span class="main">&lt;</span> sqrt <span class="numeral">10</span><span>"</span></span>
  <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">approximation 10</span><span class="main">)</span>
</pre>

Is it cheating? No. Working out the inequality by hand calculation is absolutely a proof. The algebraic proof above is less work for somebody who doesn't trust calculators. However, the ability to decide such questions by calculation (interval arithmetic, to be precise) is a huge labour-saver.


<pre class="source">
  <span class="keyword1 command">lemma</span> <span class="quoted quoted"><span>"</span><span class="free">x</span> <span class="main">∈</span> <span class="main">{</span><span class="numeral">0.999</span><span class="main">..</span><span class="numeral">1.001</span><span class="main">}</span> <span class="main">⟹</span> <span class="main">¦</span>pi <span class="main">-</span> <span class="numeral">4</span> <span class="main">*</span> arctan <span class="free">x</span><span class="main">¦</span> <span class="main">&lt;</span> <span class="numeral">0.0021</span><span>"</span></span>
    <span class="keyword1 command">by</span> <span class="main">(</span><a class="entity_ref"><span class="operator">approximation 20<span class="main">)</span></span></a>
</pre>

To use this wonder-working tool, your theory file needs to import the library theory `HOL-Decision_Procs.Approximation`.



While we are talking about automatic tactics, Chaieb's `sos` deserves a mention. It uses [sum of squares](https://mediatum.ub.tum.de/doc/649541/649541.pdf) methods to decide real polynomial inequalities.


<pre class="source">
<span class="keyword1 command">lemma</span><span>
  </span><span class="keyword2 keyword">fixes</span> <span class="free">a</span><span class="main">::</span><span class="quoted">real</span><span>
  </span><span class="keyword2 keyword">shows</span> <span class="quoted quoted"><span>"</span><span class="main">(</span><span class="free">a</span><span class="main">*</span><span class="free">b</span> <span class="main">+</span> <span class="free">b</span> <span class="main">*</span> <span class="free">c</span> <span class="main">+</span> <span class="free">c</span><span class="main">*</span><span class="free">a</span><span class="main">)</span><span class="main">^</span><span class="numeral">3</span> <span class="main">≤</span> <span class="main">(</span><span class="free">a</span><span class="main">^</span><span class="numeral">2</span> <span class="main">+</span> <span class="free">a</span> <span class="main">*</span> <span class="free">b</span> <span class="main">+</span> <span class="free">b</span><span class="main">^</span><span class="numeral">2</span><span class="main">)</span> <span class="main">*</span> <span class="main">(</span><span class="free">b</span><span class="main">^</span><span class="numeral">2</span> <span class="main">+</span> <span class="free">b</span> <span class="main">*</span> <span class="free">c</span> <span class="main">+</span> <span class="free">c</span><span class="main">^</span><span class="numeral">2</span><span class="main">)</span> <span class="main">*</span> <span class="main">(</span><span class="free">c</span><span class="main">^</span><span class="numeral">2</span> <span class="main">+</span> <span class="free">c</span><span class="main">*</span><span class="free">a</span> <span class="main">+</span> <span class="free">a</span><span class="main">^</span><span class="numeral">2</span><span class="main">)</span><span>"</span></span><span>
  </span><span class="keyword1 command">by</span> <span class="operator">sos</span>
</pre>

A decision procedure, it always settles the question, but with too many variables you won't live long enough to see the result. To use it, your theory needs to import `HOL-Library.Sum_of_Squares`.


### The square root of two is irrational

I contrived this example to demonstrate sledgehammer and especially how beautifully it interacts with the development of a structured proof. I knew the mathematical proof already, so the point was to formalise it using sledgehammer alone, without reference to other [formal proofs](http://www.cs.ru.nl/~freek/comparison/comparison.pdf).
It also illustrates some tricky points requiring numeric types.

The irrationality of $\sqrt2$ is stated in terms of $\mathbb Q$, which in Isabelle/HOL is a weird polymorphic set: it is the range of the function `of_rat`, which embeds type `rat` into larger types such as `real` and `complex`.
So the proof begins by assuming that 
sqrt <span class="numeral">2</span> <span class="main">∈</span> <span class="main">ℚ</span>,
thus obtaining `q` of type `rat` such that 
`sqrt` <span class="numeral">2</span> <span class="main">=</span> of_rat <span class="skolem">q</span> and after that, 
<span class="skolem">q</span><span class="main">^</span><span class="numeral">2</span> <span class="main">=</span> <span class="numeral">2</span>.
Sledgehammer was unable to derive this in a single step from the assumption, and this step-by-step approach (thinking of a simple intermediate property) is the simplest way to give sledgehammer a hint.

We next obtain `m` and `n` such that 
<pre class="source">
    <span class="quoted quoted"><span>"</span>coprime <span class="skolem">m</span> <span class="skolem">n</span><span>"</span></span>       <span class="quoted quoted"><span>"</span><span class="skolem">q</span> <span class="main">=</span> of_int <span class="skolem">m</span> <span class="main">/</span> of_int <span class="skolem">n</span><span>"</span></span></pre>

Two tricks here are knowing that `coprime` is available, and using the embedding `of_int` to ensure that `m` and `n` are integers (far better than simply declaring `m` and `n` to have type `int`, when Isabelle may insert embeddings in surprising places).
Next we state the goal

<pre class="source">
    <span class="quoted quoted"><span>"</span>of_int <span class="skolem">m</span> <span class="main">^</span> <span class="numeral">2</span> <span class="main">/</span> of_int <span class="skolem">n</span> <span class="main">^</span> <span class="numeral">2</span> <span class="main">=</span> <span class="main">(</span><span class="numeral">2</span><span class="main">::</span>rat<span class="main">)</span><span>"</span></span>
</pre>

Now a *super-important point*: the embeddings `of_nat`, `of_int`, `of_real` specify their domain type, but their range type **can be anything** belonging to a suitably rich type class. Since 2 can also have many types, the `2::rat` is necessary to ensure that we are talking about the rationals.

The proof continues with the expected argument of showing that 2 is a divisor of both `m` and `n`, contradicting the fact that they are coprime.

<pre class="source">
<span class="keyword1 command">lemma</span> <span class="quoted quoted"><span>"</span>sqrt <span class="numeral">2</span> <span class="main">∉</span> <span class="main">ℚ</span><span>"</span></span><span>
</span><span class="keyword1 command">proof</span><span>
  </span><span class="keyword3 command">assume</span> <span class="quoted quoted"><span>"</span>sqrt <span class="numeral">2</span> <span class="main">∈</span> <span class="main">ℚ</span><span>"</span></span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">obtain</span> <span class="skolem skolem">q</span><span class="main">::</span><span class="quoted">rat</span> <span class="keyword2 keyword">where</span> <span class="quoted quoted"><span>"</span>sqrt <span class="numeral">2</span> <span class="main">=</span> of_rat <span class="skolem">q</span><span>"</span></span><span>
    </span><span class="keyword1 command">using</span> Rats_cases <span class="keyword1 command">by</span> <span class="operator">blast</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword1 command">have</span> <span class="quoted quoted"><span>"</span><span class="skolem">q</span><span class="main">^</span><span class="numeral">2</span> <span class="main">=</span> <span class="numeral">2</span><span>"</span></span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> abs_numeral of_rat_eq_iff of_rat_numeral_eq of_rat_power power2_eq_square
              real_sqrt_mult_self<span class="main">)</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">obtain</span> <span class="skolem skolem">m</span> <span class="skolem skolem">n</span><span>
    </span><span class="keyword2 keyword">where</span> <span class="quoted quoted"><span>"</span>coprime <span class="skolem">m</span> <span class="skolem">n</span><span>"</span></span> <span class="quoted quoted"><span>"</span><span class="skolem">q</span> <span class="main">=</span> of_int <span class="skolem">m</span> <span class="main">/</span> of_int <span class="skolem">n</span><span>"</span></span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> Fract_of_int_quotient Rat_cases<span class="main">)</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword1 command">have</span> <span class="quoted quoted"><span>"</span>of_int <span class="skolem">m</span> <span class="main">^</span> <span class="numeral">2</span> <span class="main">/</span> of_int <span class="skolem">n</span> <span class="main">^</span> <span class="numeral">2</span> <span class="main">=</span> <span class="main">(</span><span class="numeral">2</span><span class="main">::</span>rat<span class="main">)</span><span>"</span></span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> <span class="quoted quoted"><span>‹</span><span class="skolem">q</span><span class="main"><span class="hidden">⇧</span><sup>2</sup></span> <span class="main">=</span> <span class="numeral">2</span><span>›</span></span> power_divide<span class="main">)</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword1 command">have</span> 2<span class="main">:</span> <span class="quoted quoted"><span>"</span>of_int <span class="skolem">m</span> <span class="main">^</span> <span class="numeral">2</span> <span class="main">=</span> <span class="main">(</span><span class="numeral">2</span><span class="main">::</span>rat<span class="main">)</span> <span class="main">*</span> of_int <span class="skolem">n</span> <span class="main">^</span> <span class="numeral">2</span><span>"</span></span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> division_ring_divide_zero double_eq_0_iff mult_2_right mult_zero_right
              nonzero_divide_eq_eq<span class="main">)</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword1 command">have</span> <span class="quoted quoted"><span>"</span><span class="numeral">2</span> <span class="keyword1">dvd</span> <span class="skolem">m</span><span>"</span></span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> <span class="main main">(</span>mono_tags<span class="main main">,</span> lifting<span class="main main">)</span> even_mult_iff even_numeral of_int_eq_iff of_int_mult
              of_int_numeral power2_eq_square<span class="main">)</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">obtain</span> <span class="skolem skolem">r</span> <span class="keyword2 keyword">where</span> <span class="quoted quoted"><span>"</span><span class="skolem">m</span> <span class="main">=</span> <span class="numeral">2</span><span class="main">*</span><span class="skolem">r</span><span>"</span></span><span>
    </span><span class="keyword1 command">by</span> <span class="operator">blast</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword1 command">have</span> <span class="quoted quoted"><span>"</span><span class="numeral">2</span> <span class="keyword1">dvd</span> <span class="skolem">n</span><span>"</span></span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">smt</span> <span class="main main">(</span>verit<span class="main main">)</span> <span class="quoted"><span>"</span>2<span>"</span></span> <span class="quoted quoted"><span>‹</span>even <span class="skolem">m</span><span>›</span></span> dvdE even_mult_iff mult.left_commute mult_cancel_left of_int_1 
            of_int_add of_int_eq_iff of_int_mult one_add_one power2_eq_square<span class="main">)</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="quoted">False</span><span>
    </span><span class="keyword1 command">using</span> <span class="quoted quoted"><span>‹</span>coprime <span class="skolem">m</span> <span class="skolem">n</span><span>›</span></span> <span class="quoted quoted"><span>‹</span><span class="skolem">m</span> <span class="main">=</span> <span class="numeral">2</span> <span class="main">*</span> <span class="skolem">r</span><span>›</span></span> <span class="keyword1 command">by</span> <span class="operator">simp</span><span>
</span><span class="keyword1 command">qed</span>
</pre>


**Every step** in this proof was obtained by sledgehammer. The main skill involves thinking up the right intermediate goals when sledgehammer fails, and typing them in.
Yes, formal proof really is just another sort of coding.

You can download the [theory file `Baby.thy`](/Isabelle-Examples/Baby.thy).
You might want to generalise the example to show that the square root of every prime is irrational. The `prime` predicate and supporting theory can be imported from
`HOL-Computational_Algebra.Primes`.

Give it a try. Isabelle is [easy to install](https://isabelle.in.tum.de/) and comes with [plenty of documentation](https://isabelle.in.tum.de/dist/Isabelle/doc/prog-prove.pdf). 

