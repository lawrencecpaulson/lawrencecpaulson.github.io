---
layout: post
title:  "Formalising an easy proof: Dirichlet's approximation theorem"
usemathjax: true 
tags: [examples, Isar, formalised mathematics]
---
For many, the process of transforming a textbook mathematical proof
into a formal document remains mysterious.
Here, we look at a fairly elementary example.
Dirichlet's approximation theorem states that there exists a rational approximation 
to any given real number such that the denominator is relatively small.
The proof combines an application of the pigeonhole principle
with some straightforward calculations.
Formalised, it's only about 50 lines long.
There are still a couple of tricky bits to deal with!

### The textbook proof

Consider the problem of approximating π by a rational number.
Any finite decimal representation of π is rational,
but the denominators are large powers of 10 when we can do much better:
355/113 = 3.1415929 approximates π 
to seven significant figures (the true value is 3.14159265).
Dirichlet's approximation theorem says that given the real number
$\theta$, for every integer $N>0$ 
there exist integers $h$ and $k$ with $0<k \le N$ such that
$\vert k\theta-h\vert < 1/N$.
Thus, $h/k$ is a good approximation to $\theta$.

Here is the proof, which comes from 
*Modular Functions and Dirichlet Series in Number Theory* 
by Tom M. Apostol, page 143.

<img src="/images/Dirichlet-approx-thm.png" width="650"/>

### Starting the formalisation

We begin with a precise formation of the theorem statement.
To avoid possible issues involving [numeric types]({% post_url 2024-07-25-Numeric_types %}),
the types of θ and $N$ are given explicitly.
Some type coercions are also explicit: `int`, which injects from type `nat` to `int`, 
and `of_int`, which injects from type `int` into any numeric type that contains the integers,
in this case `real`.

<pre class="source">
<span class="keyword1 command">theorem</span> Dirichlet_approx<span class="main">:</span><span>
  </span><span class="keyword2 keyword">fixes</span> <span class="free">θ</span><span class="main">::</span><span class="tconst">real</span> <span class="keyword2 keyword">and</span> <span class="free">N</span><span class="main">::</span><span class="tconst">nat</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">N</span> <span class="main">&gt;</span></span> <span class="main">0</span></span><span>"</span><span> 
  </span><span class="keyword2 keyword">obtains</span> <span class="free">h</span> <span class="free">k</span> <span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">0</span></span> <span class="main">&lt;</span></span> <span class="free">k</span><span>"</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">k</span> <span class="main">≤</span></span> </span><span class="const">int</span> <span class="free">N</span><span>"</span> <span class="quoted quoted"><span>"</span><span class="main">¦</span></span><span class="const">of_int</span> <span class="free">k</span><span class="main"> * </span><span class="free">θ</span> <span class="main">-</span> <span class="const">of_int</span> <span class="free">h</span><span class="main">¦</span> <span class="main">&lt;</span> <span class="main">1</span><span class="main">/</span><span class="free">N</span><span>"</span><span>
</span><span class="keyword1 command">proof</span> <span class="operator">-</span>
</pre>

Next, we define $X$ 
to be the set of $N+1$ real numbers mentioned at the start of the proof,
while $Y$
denotes the division of the half-open unit interval into $N$ parts.
Note that the image of a function is written in Isabelle/HOL using
the ` operator, and the formal syntax for integer ranges is also helpful.
Many beginners make the mistake of repeating large expressions 
rather than creating an abbreviation, 
especially when the source proof did not use an abbreviation.
As we reason about $X$ and $Y$ below 
it should become clear that they make the formal text more readable.
They make automation work better too.

<pre class="source">
  <span class="keyword3 command">define</span> <span class="skolem skolem">X</span> <span class="keyword2 keyword">where</span> <span class="quoted quoted"><span>"</span><span class="skolem">X</span> <span class="main">≡</span> <span class="main">(</span><span class="main">λ</span><span class="bound">k</span><span class="main">.</span> </span><span class="const">frac</span> <span class="main">(</span><span class="bound">k</span><span class="main">*</span><span class="free">θ</span><span class="main">)</span><span class="main">)</span> <span class="main">`</span> <span class="main">{..</span><span class="free">N</span><span class="main">}</span><span>"</span><span>
  </span><span class="keyword3 command">define</span> <span class="skolem skolem">Y</span> <span class="keyword2 keyword">where</span> <span class="quoted quoted"><span>"</span><span class="skolem">Y</span> <span class="main">≡</span> <span class="main">(</span><span class="main">λ</span><span class="bound">k</span><span class="main">::</span></span><span class="tconst">nat</span><span class="main">.</span> <span class="main">{</span><span class="bound">k</span><span class="main">/</span><span class="free">N</span><span class="main">..&lt;</span> <span class="const">Suc</span> <span class="bound">k</span><span class="main">/</span><span class="free">N</span><span class="main">}</span><span class="main">)</span> <span class="main">`</span> <span class="main">{..&lt;</span><span class="free">N</span><span class="main">}</span><span>"</span>
</pre>

### Applying the pigeonhole principle

Next we need to prove the claim that "some subinterval must contain 
at least two of these fractional parts".
Proof by contradiction is not mentioned, but struck me as the easiest way to proceed.

<pre class="source">
  <span class="keyword1 command">have</span> <span class="const">False</span><span> 
    </span><span class="keyword2 keyword">if</span> non<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">¬</span></span> <span class="main">(</span><span class="main">∃</span></span><span class="bound bound">b</span><span class="main">≤</span><span class="free">N</span><span class="main">.</span> <span class="main">∃</span><span class="bound bound">a</span><span class="main">&lt;</span><span class="bound">b</span><span class="main">.</span> <span class="main">¦</span><span class="const">frac</span> <span class="main">(</span><span class="const">real</span> <span class="bound">b</span> <span class="main">*</span> <span class="free">θ</span><span class="main">)</span> <span class="main">-</span> <span class="const">frac</span> <span class="main">(</span><span class="const">real</span> <span class="bound">a</span> <span class="main">*</span> <span class="free">θ</span><span class="main">)</span><span class="main">¦</span> <span class="main">&lt;</span> <span class="main">1</span><span class="main">/</span><span class="free">N</span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword1 command">proof</span> <span class="operator">-</span>
</pre>

The point is, it's not immediately obvious that 
"the $N+1$ real numbers $0$, $\\{\theta\\}$, $\\{2\theta\\},\ldots,\\{N\theta\\}$"
really are distinct. But the claim follows immediately from `non`, the negated assumption.
We prove that the map $k\mapsto\\{k\theta\\}$ is injective,
and therefore that $X$ has the desired cardinality.

<pre class="source">
    <span class="keyword1 command">have</span> <span class="quoted quoted">"</span><span class="const">inj_on</span> <span class="main">(</span><span class="main">λ</span><span class="bound">k</span><span class="main">::</span><span class="tconst">nat</span><span class="main">.</span> <span class="const">frac</span> <span class="main">(</span><span class="bound">k</span><span class="main">*</span><span class="free">θ</span><span class="main">)</span><span class="main">)</span> <span class="main">{..</span><span class="free">N</span><span class="main">}</span><span>"</span><span>
      </span><span class="keyword1 command">using</span> non <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">intro</span> linorder_inj_onI<span class="main keyword3">;</span> <span class="operator">force</span><span class="main">)</span><span>
    </span><span class="keyword1 command">then</span> <span class="keyword1 command">have</span> caX<span class="main">:</span> <span class="quoted quoted">"</span><span class="const">card</span> <span class="skolem">X</span> <span class="main">=</span> <span class="const">Suc</span> <span class="free">N</span><span>"</span><span>
      </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> X_def card_image<span class="main">)</span>
</pre>

It shouldn't be difficult to prove that the cardinality of
$Y$ equals $N$,
but for the pigeonhole argument it merely needs to be at most $N$,
which is trivial by definition.

<pre class="source">
    <span class="keyword1 command">have</span> caY<span class="main">:</span> <span class="quoted quoted">"</span><span class="const">card</span> <span class="skolem">Y</span> <span class="main">≤</span> <span class="free">N</span><span>"</span> <span class="quoted quoted">"</span><span class="const">finite</span> <span class="skolem">Y</span><span>"</span><span>
      </span><span class="keyword1 command">unfolding</span> Y_def <span class="keyword1 command">using</span> card_image_le <span class="keyword1 command">by</span> <span class="operator">force</span><span class="main keyword3">+</span>
</pre>

To set up the pigeonhole argument, we define the function $f$.
It is clearly a map from the half-open unit interval
to $Y$, as can be seen from the result we immediately prove.

<pre class="source">
    <span class="keyword3 command">define</span> <span class="skolem skolem">f</span> <span class="keyword2 keyword">where</span> <span class="quoted quoted"><span>"</span><span class="skolem">f</span> <span class="main">≡</span> <span class="main">λ</span><span class="bound">x</span><span class="main">::</span></span><span class="tconst">real</span><span class="main">.</span> <span class="keyword1">let</span> <span class="bound">k</span> <span class="main">=</span> <span class="const">nat</span> <span class="main">⌊</span><span class="bound">x</span> <span class="main">*</span> <span class="free">N</span><span class="main">⌋</span> <span class="keyword1">in</span> <span class="main">{</span><span class="bound">k</span><span class="main">/</span><span class="free">N</span> <span class="main">..&lt;</span> <span class="const">Suc</span> <span class="bound">k</span><span class="main">/</span><span class="free">N</span><span class="main">}</span><span>"</span><span>
    </span><span class="keyword1 command">have</span> <span class="quoted quoted">"</span><span class="const">nat</span> <span class="main">⌊</span><span class="skolem">x</span> <span class="main">*</span> <span class="free">N</span><span class="main">⌋</span> <span class="main">&lt;</span> <span class="free">N</span><span>"</span> <span class="keyword2 keyword">if</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">0</span></span> <span class="main">≤</span></span> <span class="skolem">x</span><span>"</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">x</span> <span class="main">&lt;</span></span> <span class="main">1</span></span><span>"</span> <span class="keyword2 keyword">for</span> <span class="skolem">x</span><span class="main">::</span><span class="tconst">real</span><span>
      </span><span class="keyword1 command">using</span> that assms floor_less_iff nat_less_iff <span class="keyword1 command">by</span> <span class="operator">fastforce</span>
</pre>

We actually show that $f$ maps $X$ to $Y$,
and hence is not injective: that would imply $N+1\le N$.

<pre class="source">
    <span class="keyword1 command">then</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">f</span> <span class="main">∈</span></span> <span class="skolem">X</span> <span class="main">→</span></span> <span class="skolem">Y</span><span>"</span><span>
      </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">force</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> f_def Let_def X_def Y_def frac_lt_1<span class="main">)</span><span>
    </span><span class="keyword1 command">then</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">¬</span></span> </span><span class="const">inj_on</span> <span class="skolem">f</span> <span class="skolem">X</span><span>"</span><span>
      </span><span class="keyword1 command">using</span> <span class="quoted quoted">‹</span><span class="const">finite</span> <span class="skolem">Y</span><span>›</span> caX caY card_inj <span class="keyword1 command">by</span> <span class="operator">fastforce</span>
</pre>

Therefore some pigeonhole holds two elements $x$, $x'$ of $X$, 
which we can write as $\\{c\theta\\}$, $\\{d\theta\\}$, for natural numbers $c$, $d$.

<pre class="source">
    <span class="keyword1 command">then</span> <span class="keyword3 command">obtain</span> <span class="skolem skolem">x</span> <span class="skolem skolem">x'</span> <span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">x</span><span class="main">≠</span></span><span class="skolem">x'</span><span>"</span></span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">x</span> <span class="main">∈</span></span> <span class="skolem">X</span><span>"</span></span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">x'</span> <span class="main">∈</span></span> <span class="skolem">X</span><span>"</span></span> <span class="keyword2 keyword">and</span> eq<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">f</span> <span class="skolem">x</span> <span class="main">=</span></span> <span class="skolem">f</span> <span class="skolem">x'</span><span>"</span></span><span>
      </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> inj_on_def<span class="main">)</span><span>
    </span><span class="keyword1 command">then</span> <span class="keyword3 command">obtain</span> <span class="skolem skolem">c</span> <span class="skolem skolem">d</span><span class="main">::</span><span class="tconst">nat</span> <span class="keyword2 keyword">where</span> c<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">c</span> <span class="main">≠</span></span> <span class="skolem">d</span><span>"</span></span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">c</span> <span class="main">≤</span></span> <span class="free">N</span><span>"</span></span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">d</span> <span class="main">≤</span></span> <span class="free">N</span><span>"</span></span><span> 
            </span><span class="keyword2 keyword">and</span> xeq<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">x</span> <span class="main">=</span></span> </span><span class="const">frac</span> <span class="main">(</span><span class="skolem">c</span><span class="main">*</span><span class="free">θ</span><span class="main">)</span><span>"</span> <span class="keyword2 keyword">and</span> xeq'<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">x'</span> <span class="main">=</span></span> </span><span class="const">frac</span> <span class="main">(</span><span class="skolem">d</span><span class="main">*</span><span class="free">θ</span><span class="main">)</span><span>"</span><span>
      </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> <span class="main main">(</span>no_types<span class="main main">,</span> lifting<span class="main main">)</span> X_def atMost_iff image_iff<span class="main">)</span>
</pre>

To conclude the proof by contradiction, 
we have to exhibit the actual pigeonhole and do a few calculations.
It turns out to be the half open interval $[\frac{i}{N},\frac{i+1}{N})$, 
where $i = \lfloor x N\rfloor$.

<pre class="source">
    <span class="keyword3 command">define</span> <span class="skolem skolem">i</span> <span class="keyword2 keyword">where</span> <span class="quoted quoted"><span>"</span><span class="skolem">i</span> <span class="main">≡</span> </span><span class="const">nat</span> <span class="main">⌊</span><span class="skolem">x</span> <span class="main">*</span> <span class="free">N</span><span class="main">⌋</span><span>"</span><span>
    </span><span class="keyword1 command">then</span> <span class="keyword1 command">have</span> i<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">x</span> <span class="main">∈</span></span> <span class="main">{</span></span><span class="skolem">i</span><span class="main">/</span><span class="free">N</span> <span class="main">..&lt;</span> <span class="const">Suc</span> <span class="skolem">i</span><span class="main">/</span><span class="free">N</span><span class="main">}</span><span>"</span><span> 
      </span><span class="keyword1 command">using</span> assms <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> <span class="dynamic dynamic">divide_simps</span> xeq<span class="main">)</span> <span class="operator">linarith</span><span>
    </span><span class="keyword1 command">have</span> <span>i'</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">x'</span> <span class="main">∈</span></span> <span class="main">{</span></span><span class="skolem">i</span><span class="main">/</span><span class="free">N</span> <span class="main">..&lt;</span> <span class="const">Suc</span> <span class="skolem">i</span><span class="main">/</span><span class="free">N</span><span class="main">}</span><span>"</span><span> 
      </span><span class="keyword1 command">using</span> eq assms <span class="keyword1 command">unfolding</span> f_def Let_def xeq' i_def<span>
      </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> <span class="dynamic dynamic">divide_simps</span><span class="main">)</span> <span class="operator">linarith</span>
</pre>

A further small calculation shows that we have indeed contradicted the assumption
`non` that we made above.

<pre class="source">
    <span class="keyword1 command">with</span> assms i <span class="keyword1 command">have</span> <span class="quoted quoted"><span>"</span><span class="main">¦</span></span><span class="const">frac</span> <span class="main">(</span><span class="skolem">d</span><span class="main">*</span><span class="free">θ</span><span class="main">)</span> <span class="main">-</span> <span class="const">frac</span> <span class="main">(</span><span class="skolem">c</span><span class="main">*</span><span class="free">θ</span><span class="main">)</span><span class="main">¦</span> <span class="main">&lt;</span> <span class="main">1</span> <span class="main">/</span> <span class="free">N</span><span>"</span><span>
      </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> xeq xeq' abs_if add_divide_distrib<span class="main">)</span><span>
    </span><span class="keyword1 command">with</span> c <span class="keyword3 command">show</span> <span class="const">False</span><span>
      </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> abs_minus_commute nat_neq_iff non<span class="main">)</span><span>
  </span><span class="keyword1 command">qed</span>
</pre>

### Finishing up

Thanks to the just-completed pigeonhole argument, 
we obtain natural numbers $a$ and $b$ satisfying claim (2)
of the textbook proof and are ready to define the sought-for $k$ and $h$.
Here <span class="var quoted var">?k</span> is a different sort of abbreviation, 
essentially a macro and appropriate in this simple case.

<pre class="source">
  <span class="keyword1 command">then</span> <span class="keyword3 command">obtain</span> <span class="skolem skolem">a</span> <span class="skolem skolem">b</span><span class="main">::</span><span class="tconst">nat</span> <span class="keyword2 keyword">where</span> *<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">a</span><span class="main">&lt;</span></span><span class="skolem">b</span><span>"</span></span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">b</span><span class="main">≤</span></span><span class="free">N</span><span>"</span></span> <span class="quoted quoted"><span>"</span><span class="main">¦</span></span><span class="const">frac</span> <span class="main">(</span><span class="skolem">b</span><span class="main">*</span><span class="free">θ</span><span class="main">)</span> <span class="main">-</span> <span class="const">frac</span> <span class="main">(</span><span class="skolem">a</span><span class="main">*</span><span class="free">θ</span><span class="main">)</span><span class="main">¦</span> <span class="main">&lt;</span> <span class="main">1</span><span class="main">/</span><span class="free">N</span><span>"</span><span> 
    </span><span class="keyword1 command">by</span> <span class="operator">metis</span>
  <span class="keyword1 command">let</span> <span class="var quoted var">?k</span> <span class="main">=</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">b</span><span class="main">-</span></span><span class="skolem">a</span><span>"</span></span> <span class="keyword2 keyword">and</span> <span class="var quoted var">?h</span> <span class="main">=</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">⌊</span></span><span class="skolem">b</span><span class="main">*</span></span><span class="free">θ</span><span class="main">⌋</span> <span class="main">-</span> <span class="main">⌊</span><span class="skolem">a</span><span class="main">*</span><span class="free">θ</span><span class="main">⌋</span><span>"</span>
</pre>

We are ready for the final calculation.
Because the theorem was stated using <span class="keyword2 keyword">obtains</span>,
the <span class="keyword1 command">proof</span> requires
showing that our <span class="var quoted var">?k</span> and
<span class="var quoted var">?h</span> satisfy 
the three inequalities given in the theorem statement.
We only do the last one explicitly, 
mopping up the other two within the <span class="keyword1 command">qed</span>.

<pre class="source">
  <span class="keyword3 command">show</span> <span class="var quoted var">?thesis</span><span>
  </span><span class="keyword1 command">proof</span><span>
    </span><span class="keyword1 command">have</span> <span class="quoted quoted">"</span><span class="const">frac</span> <span class="main">(</span><span class="skolem">b</span><span class="main">*</span><span class="free">θ</span><span class="main">)</span> <span class="main">-</span> <span class="const">frac</span> <span class="main">(</span><span class="skolem">a</span><span class="main">*</span><span class="free">θ</span><span class="main">)</span> <span class="main">=</span> <span class="var">?k</span><span class="main">*</span><span class="free">θ</span> <span class="main">-</span> <span class="var">?h</span><span>"</span><span>
      </span><span class="keyword1 command">using</span> <span class="quoted"><span class="quoted"><span>‹</span><span class="skolem">a</span> <span class="main">&lt;</span></span> <span class="skolem">b</span><span>›</span></span> <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> frac_def left_diff_distrib of_nat_diff<span class="main">)</span><span>
    </span><span class="keyword1 command">with</span> * <span class="keyword3 command">show</span> <span class="quoted quoted"><span>"</span><span class="main">¦</span></span><span class="const">of_int</span> <span class="var">?k</span><span class="main"> * </span><span class="free">θ</span> <span class="main">-</span> <span class="var">?h</span><span class="main">¦</span> <span class="main">&lt;</span> <span class="main">1</span><span class="main">/</span><span class="free">N</span><span>"</span><span>
      </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> of_int_of_nat_eq<span class="main">)</span><span>
  </span><span class="keyword1 command">qed</span> <span class="main">(</span><span class="operator">use</span> * <span class="keyword2 keyword quasi_keyword">in</span> <span class="operator">auto</span><span class="main">)</span><span>
</span><span class="keyword1 command">qed</span>
</pre>

There is no magic formula for coming up with such proofs.
Do pay attention to the structure given in the text and try to reproduce it.
The proofs themselves are not that complicated 
and in many places were generated by sledgehammer.
Still, you need to master the isabelle/HOL syntax for formulas, 
including some of the more offbeat things shown here.

The relevant Isabelle theory file is available
[here](/Isabelle-Examples/Dirichlet_approx_thm.thy).
A generalisation of the proof to demonstrate the simultaneous approximation 
of finitely many real numbers is 
[proved in the distribution](https://isabelle.in.tum.de/dist/library/HOL/HOL-Analysis/Kronecker_Approximation_Theorem.html).

