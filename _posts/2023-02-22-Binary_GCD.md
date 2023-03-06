---
layout: post
title:  "Verifying the binary algorithm for greatest common divisors"
usemathjax: true 
tags: [examples, Isabelle, Isar]
---
The [Euclidean algorithm](https://en.wikipedia.org/wiki/Euclidean_algorithm) 
for the GCD is generally regarded as
one of the first algorithms worthy of the name ––
its main competitor perhaps the sieve of Eratosthenes, 
for generating prime numbers.
Euclid's algorithm requires repeated calculations
of integer remainders, which was a heavy operation on early computers.
(Some provided no hardware to perform multiplication and division.)
One can replace the remainder operation by subtraction.
That algorithm is far too slow, especially if one of the arguments
is much smaller than the other,
but it can be refined to achieve high performance by noting that 
any binary computer can efficiently divide by two.
Let's verify [this algorithm](https://en.wikipedia.org/wiki/Binary_GCD_algorithm), 
and along the way see how inductive definitions are done in Isabelle/HOL.

### The binary GCD algorithm

The greatest common divisor of two natural numbers satisfies 
the following properties:

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
<span class="keyword1 command">inductive_set</span>  <span class="entity">bgcd</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span>nat</span> <span class="main">×</span></span> nat <span class="main">×</span> nat<span class="main">)</span> set<span>"</span> <span class="keyword2 keyword">where</span><span>
  </span>bgcdZero<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span><span class="free bound entity">u</span><span class="main">,</span> <span class="main">0</span></span><span class="main">,</span> <span class="free bound entity">u</span><span class="main">)</span> <span class="main">∈</span></span> <span class="free">bgcd</span><span>"</span><span>
</span><span class="main">|</span> bgcdEven<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">⟦</span> <span class="main">(</span><span class="free bound entity">u</span><span class="main">,</span> <span class="free bound entity">v</span><span class="main">,</span> <span class="free bound entity">g</span><span class="main">)</span> <span class="main">∈</span></span> <span class="free">bgcd</span> <span class="main">⟧</span> <span class="main">⟹</span> <span class="main">(</span><span class="numeral">2</span><span class="main">*</span></span><span class="free bound entity">u</span><span class="main">,</span> <span class="numeral">2</span><span class="main">*</span><span class="free bound entity">v</span><span class="main">,</span> <span class="numeral">2</span><span class="main">*</span><span class="free bound entity">g</span><span class="main">)</span> <span class="main">∈</span> <span class="free">bgcd</span><span>"</span><span>
</span><span class="main">|</span> bgcdOdd<span class="main">:</span>  <span class="quoted"><span class="quoted"><span>"</span><span class="main">⟦</span> <span class="main">(</span><span class="free bound entity">u</span><span class="main">,</span> <span class="free bound entity">v</span><span class="main">,</span> <span class="free bound entity">g</span><span class="main">)</span> <span class="main">∈</span></span> <span class="free">bgcd</span><span class="main">;</span> <span class="main">¬</span></span> <span class="numeral">2</span> <span class="keyword1">dvd</span> <span class="free bound entity">v</span> <span class="main">⟧</span> <span class="main">⟹</span> <span class="main">(</span><span class="numeral">2</span><span class="main">*</span><span class="free bound entity">u</span><span class="main">,</span> <span class="free bound entity">v</span><span class="main">,</span> <span class="free bound entity">g</span><span class="main">)</span> <span class="main">∈</span> <span class="free">bgcd</span><span>"</span><span>
</span><span class="main">|</span> bgcdStep<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">⟦</span> <span class="main">(</span><span class="free bound entity">u</span> <span class="main">-</span></span> <span class="free bound entity">v</span><span class="main">,</span> <span class="free bound entity">v</span><span class="main">,</span> <span class="free bound entity">g</span><span class="main">)</span> <span class="main">∈</span></span> <span class="free">bgcd</span><span class="main">;</span> <span class="free bound entity">v</span> <span class="main">≤</span> <span class="free bound entity">u</span> <span class="main">⟧</span> <span class="main">⟹</span> <span class="main">(</span><span class="free bound entity">u</span><span class="main">,</span> <span class="free bound entity">v</span><span class="main">,</span> <span class="free bound entity">g</span><span class="main">)</span> <span class="main">∈</span> <span class="free">bgcd</span><span>"</span><span>
</span><span class="main">|</span> bgcdSwap<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">⟦</span> <span class="main">(</span><span class="free bound entity">v</span><span class="main">,</span> <span class="free bound entity">u</span><span class="main">,</span> <span class="free bound entity">g</span><span class="main">)</span> <span class="main">∈</span></span> <span class="free">bgcd</span> <span class="main">⟧</span> <span class="main">⟹</span> <span class="main">(</span><span class="free bound entity">u</span><span class="main">,</span> <span class="free bound entity">v</span><span class="main">,</span> <span class="free bound entity">g</span><span class="main">)</span> <span class="main">∈</span></span> <span class="free">bgcd</span><span>"</span>
</pre>

The inductive definition is abstract, but the corresponding
algorithm isn't hard to see.
If one operand is zero, then return the other;
if both operands are even, then divide by two, obtain the GCD recursively
and then double it; 
if only one of the operands is even then divide it by 2;
if both of the operands are odd, then subtract the smaller from the larger. Testing whether an integer is even or odd, and dividing it by two,
is a trivial binary shift.

### Proving that the algorithm is correct

We must show that the computed "result" 
($g$ in the triple $(x,y,g)$) really is the greatest common divisor.
First we simply prove that it is a common divisor.
The proof is by induction on the relation `bgcd`,
which means reasoning separately on each of the five rules shown above.
Note that four of the five cases are trivial enough to be covered
by a single call to `auto` at the end, with one case (subtraction)
handled specifically.

<pre class="source">
<span class="keyword1 command">lemma</span> bgcd_divides<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span><span class="free">x</span><span class="main">,</span><span class="free">y</span><span class="main">,</span><span class="free">g</span><span class="main">)</span> <span class="main">∈</span></span> bgcd</span> <span class="main">⟹</span> <span class="free">g</span> <span class="keyword1">dvd</span> <span class="free">x</span> <span class="main">∧</span> <span class="free">g</span> <span class="keyword1">dvd</span> <span class="free">y</span><span>"</span><span>
</span><span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">induct</span> <span class="quasi_keyword">rule</span><span class="main main">:</span> bgcd.induct<span class="main">)</span><span>
  </span><span class="keyword3 command">case</span> <span class="main">(</span>bgcdStep <span class="skolem">u</span> <span class="skolem">v</span> <span class="skolem">g</span><span class="main">)</span><span>
  </span><span class="keyword1 command">with</span> dvd_diffD <span class="keyword3 command">show</span> <span class="var quoted var">?case</span><span>
    </span><span class="keyword1 command">by</span> <span class="operator">blast</span><span>
</span><span class="keyword1 command">qed</span> <span class="operator">auto</span>
</pre>

So, it yields a common divisor. Let's show that it is the greatest.
And here it's time to stress that *greatest* refers to **divisibility**,
not magnitude.

<pre class="source">
<span class="keyword1 command">lemma</span> bgcd_greatest<span class="main">:</span><span>
  </span><span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span><span class="free">x</span><span class="main">,</span><span class="free">y</span><span class="main">,</span><span class="free">g</span><span class="main">)</span> <span class="main">∈</span></span> bgcd</span> <span class="main">⟹</span> <span class="free">d</span> <span class="keyword1">dvd</span> <span class="free">x</span> <span class="main">⟹</span> <span class="free">d</span> <span class="keyword1">dvd</span> <span class="free">y</span> <span class="main">⟹</span> <span class="free">d</span> <span class="keyword1">dvd</span> <span class="free">g</span><span>"</span><span>
</span><span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">induct</span> <span class="quasi_keyword">arbitrary</span><span class="main main">:</span> <span class="quoted free">d</span> <span class="quasi_keyword">rule</span><span class="main main">:</span> bgcd.induct<span class="main">)</span><span>
  </span><span class="keyword3 command">case</span> <span class="main">(</span>bgcdEven <span class="skolem">u</span> <span class="skolem">v</span> <span class="skolem">g</span> <span class="skolem">d</span><span class="main">)</span><span> 
  </span><span class="keyword3 command">show</span> <span class="var quoted var">?case</span><span>
    </span><span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">cases</span> <span class="quoted"><span class="quoted"><span>"</span><span class="numeral">2</span> <span class="keyword1">dvd</span></span> <span class="skolem">d</span><span>"</span></span><span class="main">)</span><span> 
      </span><span class="keyword3 command">case</span> True <span class="keyword3 command">thus</span> <span class="var quoted var">?thesis</span> <span class="keyword1 command">using</span> bgcdEven <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">force</span> <span class="quasi_keyword">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> dvd_def<span class="main">)</span><span> 
    </span><span class="keyword1 command">next</span><span>
      </span><span class="keyword3 command">case</span> False<span>
      </span><span class="keyword3 command">thus</span> <span class="var quoted var">?thesis</span> <span class="keyword1 command">using</span> bgcdEven<span>
        </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> coprime_dvd_mult_right_iff<span class="main">)</span><span>
    </span><span class="keyword1 command">qed</span><span>
</span><span class="keyword1 command">next</span><span>
  </span><span class="keyword3 command">case</span> <span class="main">(</span>bgcdOdd <span class="skolem">u</span> <span class="skolem">v</span> <span class="skolem">g</span> <span class="skolem">d</span><span class="main">)</span><span>
  </span><span class="keyword1 command">hence</span> <span class="quoted"><span class="quoted"><span>"</span>coprime</span> <span class="skolem">d</span> <span class="numeral">2</span><span>"</span></span><span>
    </span><span class="keyword1 command">by</span> <span class="operator">fastforce</span><span>
  </span><span class="keyword3 command">thus</span> <span class="var quoted var">?case</span> <span class="keyword1 command">using</span> bgcdOdd<span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> coprime_dvd_mult_right_iff<span class="main">)</span><span>
</span><span class="keyword1 command">qed</span> <span class="operator">auto</span>
</pre>

As with the previous proof, it's by induction on the relation we defined,
and most of the cases are trivially solved by `auto`.
The case where both $u$ and $v$ are even is verified with separate cases
depending on whether $d$ (which is some other common divisor)
is even or not.

#### Proving uniqueness and existence

The two results just proved are enough to show that the relation `bgcd`
is indeed a function, in the sense that it yields at most one result:

<pre class="source">
<span class="keyword1 command">lemma</span> bgcd_unique<span class="main">:</span><span> 
  </span><span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span><span class="free">x</span><span class="main">,</span><span class="free">y</span><span class="main">,</span><span class="free">g</span><span class="main">)</span> <span class="main">∈</span></span> bgcd</span> <span class="main">⟹</span> <span class="main">(</span><span class="free">x</span><span class="main">,</span><span class="free">y</span><span class="main">,</span><span class="free">g'</span><span class="main">)</span> <span class="main">∈</span> bgcd <span class="main">⟹</span> <span class="free">g</span> <span class="main">=</span> <span class="free">g'</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">meson</span> bgcd_divides bgcd_greatest gcd_nat.strict_iff_not<span class="main">)</span>
</pre>

Our final task is to show that this function is total, that some result
is always determined. 
(Strictly speaking, we don't have an operational semantics,
so this is not quite the termination of an actual algorithm.)
The proof is by complete induction, using the observation that
the GCD of any given pair of values is ultimately determined
by that of a smaller pair of values, possibly with the help
of the swap rule. So when considering the GCD of $a$ and $b$,
the induction will be on their sum.

<pre class="source">
<span class="keyword1 command">lemma</span> bgcd_defined_aux<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">a</span><span class="main">+</span></span><span class="free">b</span> <span class="main">≤</span></span> <span class="free">n</span> <span class="main">⟹</span> <span class="main">∃</span> <span class="bound">g</span><span class="main">.</span> <span class="main">(</span><span class="free">a</span><span class="main">,</span> <span class="free">b</span><span class="main">,</span> <span class="bound">g</span><span class="main">)</span> <span class="main">∈</span> bgcd<span>"</span><span>
</span><span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">induction</span> <span class="quoted free">n</span> <span class="quasi_keyword">arbitrary</span><span class="main main">:</span> <span class="quoted free">a</span> <span class="quoted free">b</span> <span class="quasi_keyword">rule</span><span class="main main">:</span> less_induct<span class="main">)</span><span>
  </span><span class="keyword3 command">case</span> <span class="main">(</span>less <span class="skolem">n</span> <span class="skolem">a</span> <span class="skolem">b</span><span class="main">)</span><span>
  </span><span class="keyword3 command">show</span> <span class="var quoted var">?case</span><span>
  </span><span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">cases</span> <span class="quoted skolem">b</span><span class="main">)</span><span>
    </span><span class="keyword3 command">case</span> 0<span>
    </span><span class="keyword3 command">thus</span> <span class="var quoted var">?thesis</span> <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> bgcdZero<span class="main">)</span><span> 
  </span><span class="keyword1 command">next</span><span>
    </span><span class="keyword3 command">case</span> <span class="main">(</span>Suc <span class="skolem">b'</span><span class="main">)</span><span>
    </span><span class="keyword1 command">then</span> <span class="keyword1 command">have</span> *<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">a</span> <span class="main">+</span></span> <span class="skolem">b'</span> <span class="main">&lt;</span></span> <span class="skolem">n</span><span>"</span><span>
      </span><span class="keyword1 command">using</span> Suc_le_eq add_Suc_right less.prems <span class="keyword1 command">by</span> <span class="operator">presburger</span><span>
    </span><span class="keyword3 command">show</span> <span class="var quoted var">?thesis</span><span>
    </span><span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">cases</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">b</span> <span class="main">≤</span></span> <span class="skolem">a</span><span>"</span></span><span class="main">)</span><span>
      </span><span class="keyword3 command">case</span> True<span>
      </span><span class="keyword3 command">thus</span> <span class="var quoted var">?thesis</span><span>
        </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> bgcd.simps le_add1 le_add_diff_inverse less.IH <span class="main main">[</span><span class="operator">OF</span> *<span class="main main">]</span><span class="main">)</span><span>
    </span><span class="keyword1 command">next</span><span>
      </span><span class="keyword3 command">case</span> False<span>
      </span><span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="var quoted var">?thesis</span><span>
        </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> less.IH <span class="main main">[</span><span class="operator">OF</span> *<span class="main main">]</span> Suc Suc_leI bgcd.simps le_add_diff_inverse less_add_same_cancel2<span>
            </span>nle_le zero_less_iff_neq_zero<span class="main">)</span><span>
    </span><span class="keyword1 command">qed</span><span>
  </span><span class="keyword1 command">qed</span><span>
</span><span class="keyword1 command">qed</span>
</pre>

In the proof above, we reason by cases on whether $b=0$
or alternatively $b = b'+1$ for some $b'$ 
(where obviously $b'=b-1$, a fact that doesn't need to be used).
We note that $a+b'<n$, allowing use of the induction hypothesis.
It's reasonable to ask, why not just do mathematical induction on $b$?
And the answer is, I couldn't get a proof that way, but maybe you will.[^1]

[^1]: See the comments below for a simplification suggested by YawarRaza7349.

<pre class="source">
<span class="keyword1 command">lemma</span> bgcd_defined<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">∃!</span><span class="bound">g</span><span class="main">.</span> <span class="main">(</span><span class="free">a</span><span class="main">,</span> <span class="free">b</span><span class="main">,</span> <span class="bound">g</span><span class="main">)</span> <span class="main">∈</span></span> bgcd</span><span>"</span><span>
  </span><span class="keyword1 command">using</span> bgcd_defined_aux bgcd_unique <span class="keyword1 command">by</span> <span class="operator">auto</span>
</pre>

We have finally established that our inductive definition
uniquely identifies a result for every pair of operands.
And as noted above, that result is the GCD.

<pre class="source">
<span class="keyword1 command">theorem</span> bgcd_defined<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">∃!</span><span class="bound">g</span><span class="main">.</span> <span class="main">(</span><span class="free">a</span><span class="main">,</span> <span class="free">b</span><span class="main">,</span> <span class="bound">g</span><span class="main">)</span> <span class="main">∈</span></span> bgcd</span><span>"</span><span>
  </span><span class="keyword1 command">using</span> bgcd_defined_aux bgcd_unique <span class="keyword1 command">by</span> <span class="operator">auto</span>
</pre>

This example is based on an assignment set in 2010 for my late,
lamented MPhil course, [Interactive Formal Verification](https://www.cl.cam.ac.uk/teaching/2122/L21/).
The Isabelle theory file [can be downloaded](/Isabelle-Examples/Binary_Euclidean_Algorithm.thy).


