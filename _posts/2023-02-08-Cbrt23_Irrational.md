---
layout: post
title:  "An irrationality proof involving cube roots"
usemathjax: true 
tags: [examples, newbies, Isabelle, Isar]
---

According to myth, the discovery that √2 was irrational so horrified the students of Pythagoras
that it was kept secret [upon pain of death](https://nrich.maths.org/2671). Its irrationality was thought to be paradoxical
because √2 could be constructed as the hypotenuse of a right triangle, 
while all numbers were assumed to be rational.
A while back, I [formalised a new proof]({% post_url 2023-01-18-Sqrt2_irrational %})
of the irrationality of √2. Just recently, I stumbled upon an exam question: 
to prove the irrationality of ∛2+∛3.
Its proof uses different techniques, but it's not at all hard.
Why don't you pause for a moment to prove it for yourself 
before looking at the formal treatment below?

### The informal proof

Proofs of rationality always seem to begin with the assumption 
that the given number is rational, leading to a contradiction.
So let's begin by defining $x = \sqrt[3]2+\sqrt[3]3$.
It's natural to see what happens if we cube both sides.
Multiplying out and collecting the terms on the right hand side, we find that
$x^3 = 5 + 3x\sqrt[3]6$.
But this can't be right: if $x$ is rational then so is $x^3$,
which equals the right hand side, which must also be rational.
In that case, $\sqrt[3]6$ is a rational number. It obviously isn't.

Formalising this in Isabelle/HOL, we get a nice Isar proof.

### The calculation

We begin by stating the desired claim. A rather obscure feature of Isar syntax
is the ability to make a definition right in the theorem statement.
Any such definitions will be fully expanded in the final theorem, once we have proved it.

<pre class="source">
<span class="keyword1 command">lemma</span> cuberoot_irrational<span class="main">:</span><span>
  </span><span class="keyword2 keyword">defines</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">≡</span> root</span> <span class="numeral">3</span> <span class="numeral">2</span> <span class="main">+</span></span> root <span class="numeral">3</span> <span class="numeral">3</span><span>"</span><span>
  </span><span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">∉</span></span> <span class="main">ℚ</span></span><span>"</span>
</pre>

Now we commence the proof. Another Isar fine point: omitting the proof method after the
`proof` keyword calls for the default method, which in this case
is to assume the formula, stripped of its initial negation.
In order to obtain the number 5 without complications, we pre-evaluate
the cube roots of 8 and 27.
As in the informal proof, we quickly deduce that the right-hand side is rational.

<pre class="source">
<span class="keyword1 command">proof</span><span>
  </span><span class="keyword3 command">assume</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">∈</span></span> <span class="main">ℚ</span></span><span>"</span><span>
  </span><span class="keyword1 command">moreover</span><span>
  </span><span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span>root</span> <span class="numeral">3</span> <span class="numeral">8</span> <span class="main">=</span></span> <span class="numeral">2</span><span>"</span> <span class="quoted"><span class="quoted"><span>"</span>root</span> <span class="numeral">3</span> <span class="numeral">27</span> <span class="main">=</span></span> <span class="numeral">3</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="operator">auto</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword1 command">have</span> xcubed<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span><span class="main">^</span></span><span class="numeral">3</span> <span class="main">=</span></span> <span class="numeral">5</span> <span class="main">+</span> <span class="numeral">3</span> <span class="main">*</span> <span class="free">x</span> <span class="main">*</span> root <span class="numeral">3</span> <span class="numeral">6</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> x_def <span class="dynamic dynamic">algebra_simps</span> eval_nat_numeral <span class="quasi_keyword">flip</span><span class="main main">:</span> real_root_mult<span class="main">)</span><span>
  </span><span class="keyword1 command">ultimately</span> <span class="keyword1 command">have</span> Q<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="numeral">5</span> <span class="main">+</span></span> <span class="numeral">3</span> <span class="main">*</span></span> <span class="free">x</span> <span class="main">*</span> root <span class="numeral">3</span> <span class="numeral">6</span> <span class="main">∈</span> <span class="main">ℚ</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> Rats_power <span class="quoted"><span class="quoted"><span>‹</span><span class="free">x</span> <span class="main">∈</span></span> <span class="main">ℚ</span></span><span>›</span><span class="main">)</span>
</pre>

### A nested proof

We could have proved that $\sqrt[3]6$ is irrational separately, 
but we can just as easily embed it in the larger proof.
The argument should be familiar: we write $\sqrt[3]6$ as $a/b$,
the ratio of two coprime integers. We then demonstrate that both $a$ and $b$
are divisible by two. See if you can follow the reasoning in the Isar text below.

<pre class="source">
  <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span>root</span> <span class="numeral">3</span> <span class="numeral">6</span> <span class="main">∉</span></span> <span class="main">ℚ</span><span>"</span><span>
  </span><span class="keyword1 command">proof</span><span>
    </span><span class="keyword3 command">assume</span> <span class="quoted"><span class="quoted"><span>"</span>root</span> <span class="numeral">3</span> <span class="numeral">6</span> <span class="main">∈</span></span> <span class="main">ℚ</span><span>"</span><span>
    </span><span class="keyword1 command">then</span> <span class="keyword3 command">obtain</span> <span class="skolem skolem">a</span> <span class="skolem skolem">b</span> <span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">a</span> <span class="main">/</span></span> <span class="skolem">b</span> <span class="main">=</span></span> root <span class="numeral">3</span> <span class="numeral">6</span><span>"</span> <span class="keyword2 keyword">and</span> cop<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>coprime</span> <span class="skolem">a</span> <span class="skolem">b</span><span>"</span></span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">b</span><span class="main">≠</span></span><span class="main">0</span></span><span>"</span><span>
      </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">smt</span> <span class="main main">(</span>verit<span class="main main">,</span> best<span class="main main">)</span> Rats_cases'<span class="main">)</span><span>
    </span><span class="keyword1 command">then</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span><span class="skolem">a</span><span class="main">/</span></span><span class="skolem">b</span><span class="main">)</span><span class="main">^</span></span><span class="numeral">3</span> <span class="main">=</span> <span class="numeral">6</span><span>"</span><span>
      </span><span class="keyword1 command">by</span> <span class="operator">auto</span><span>
    </span><span class="keyword1 command">then</span> <span class="keyword1 command">have</span> eq<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">a</span><span class="main">^</span></span><span class="numeral">3</span> <span class="main">=</span></span> <span class="numeral">2</span><span class="main">*</span><span class="numeral">3</span> <span class="main">*</span> <span class="skolem">b</span><span class="main">^</span><span class="numeral">3</span><span>"</span><span>
      </span><span class="keyword1 command">using</span> of_int_eq_iff <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">fastforce</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> <span class="dynamic dynamic">divide_simps</span> <span class="quoted"><span class="quoted"><span>‹</span><span class="skolem">b</span><span class="main">≠</span></span><span class="main">0</span></span><span>›</span><span class="main">)</span><span>
    </span><span class="keyword1 command">then</span> <span class="keyword1 command">have</span> p<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="numeral">2</span> <span class="keyword1">dvd</span></span> <span class="skolem">a</span><span>"</span></span><span>
      </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> coprime_left_2_iff_odd coprime_power_right_iff dvd_triv_left mult.assoc<span class="main">)</span><span>
    </span><span class="keyword1 command">then</span> <span class="keyword3 command">obtain</span> <span class="skolem skolem">c</span> <span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">a</span> <span class="main">=</span></span> <span class="numeral">2</span><span class="main">*</span></span><span class="skolem">c</span><span>"</span><span>
      </span><span class="keyword1 command">by</span> <span class="operator">blast</span><span>
    </span><span class="keyword1 command">with</span> eq <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="numeral">2</span> <span class="keyword1">dvd</span></span> <span class="skolem">b</span><span>"</span></span><span>
      </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> eval_nat_numeral<span class="main">)</span> <span class="main">(</span><span class="operator">metis</span> even_mult_iff even_numeral odd_numeral<span class="main">)</span><span>
    </span><span class="keyword1 command">with</span> p <span class="keyword2 keyword">and</span> cop <span class="keyword3 command">show</span> <span class="quoted">False</span><span>
      </span><span class="keyword1 command">by</span> <span class="operator">fastforce</span><span>
  </span><span class="keyword1 command">qed</span>
</pre>

### Finishing up

We know that the right side of our calculation above must be rational,
although $\sqrt[3]6$ is irrational.
Just a tiny bit more work remains.
We need to show that $3x$ is nonzero as well as rational.
Given that extra fact, the contradiction is found automatically,
thanks to [Sledgehammer]({% post_url 2022-04-13-Sledgehammer %}).

<pre class="source">
  <span class="keyword1 command">moreover</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="numeral">3</span><span class="main">*</span></span><span class="free">x</span> <span class="main">∈</span></span> <span class="main">ℚ</span> <span class="main">-</span> <span class="main">{</span><span class="main">0</span><span class="main">}</span><span>"</span><span>
    </span><span class="keyword1 command">using</span> xcubed  <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">force</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> <span class="quoted"><span class="quoted"><span>‹</span><span class="free">x</span> <span class="main">∈</span></span> <span class="main">ℚ</span></span><span>›</span><span class="main">)</span><span>
  </span><span class="keyword1 command">ultimately</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="numeral">3</span> <span class="main">*</span></span> <span class="free">x</span> <span class="main">*</span></span> root <span class="numeral">3</span> <span class="numeral">6</span> <span class="main">∉</span> <span class="main">ℚ</span><span>"</span><span>
    </span><span class="keyword1 command">using</span> Rats_divide <span class="keyword1 command">by</span> <span class="operator">force</span><span>
  </span><span class="keyword1 command">with</span> Q <span class="keyword3 command">show</span> <span class="quoted">False</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> Rats_diff Rats_number_of add.commute add_uminus_conv_diff diff_add_cancel<span class="main">)</span><span>
</span><span class="keyword1 command">qed</span>
</pre>

Another Isar fine point: note how `moreover` is used to collect facts.
Each instance of `moreover` records the fact just proved, and this sequence terminates
with `ultimately`, when all the recorded facts are made available to the next proof method.
Above, `ultimately` delivers two facts (that $\sqrt[3]6$ is irrational and that $3x$
is a nonzero rational) to conclude that $3x\sqrt[3]6$ is irrational.
The point of moreover/ultimately is to reduce our reliance on labels.

The Isabelle theory file is [available to download](/Isabelle-Examples/Cbrt23_Irrational.thy).
You can also check out a much more sophisticated proof, 
that [exponentials are irrational]({% post_url 2022-02-16-Irrationals %}).
