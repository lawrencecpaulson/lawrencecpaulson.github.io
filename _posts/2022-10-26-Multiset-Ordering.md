---
layout: post
title:  "Proving Termination with Multiset Orderings"
usemathjax: true
tags: [examples, Isabelle, Ackermann's function]
---

The title of this post is identical to the title of a [seminal paper](https://doi.org/10.1145/359138.359142)
by Nachum Dershowitz and Zohar Manna, both of whom I knew as a graduate student at Stanford.
(I had the privilege of doing directed reading under Zohar's supervision.)
*Multisets* are collections, like sets except that
multiple occurrences of elements are significant.
Computer scientists typically encounter them as a way of specifying
the concept of sorting: to transform an input list into an output
that is correctly ordered but equal to the input when both are regarded as multisets.
Dershowitz and Manna showed that multisets also provided
natural but strong orderings for proving termination.
I had written about the termination of a rewrite system for Ackermann's function
in an [earlier post]({% post_url 2022-02-09-Ackermann-example %})
and was advised to contact "Dershowitz, a leading
expert on termination".
His reply was that the answer I sought was in his 1979 paper!

### Multiset orderings

The idea is to lift an ordering on the elements of multisets to the multisets themselves.
The precise definition of how to compare two multisets is somewhat involved,
but basically involves cancelling everything they have in common and comparing
the largest elements at which they differ.
It may suffice to recount a conversation I had long ago with a dubious
Rod Burstall: "So if apples are greater than oranges then three apples are greater than two oranges? No: then one apple is greater than a million oranges."
Powerful stuff, and yet this ordering is [well-founded](https://en.wikipedia.org/wiki/Well-founded_relation) (therefore terminating)
provided the element ordering is.

A mathematician would probably prefer to replace multisets by non-increasing sequences, compared lexicographically.
Then it's clear that if the base ordering
has order type $\alpha$ then the corresponding multiset ordering
will have order type $\omega^\alpha$.
Dershowitz and Manna also considered the *iterated* nesting of multisets,
which has order type [$\epsilon_0$](https://en.wikipedia.org/wiki/Epsilon_number).
This is easily strong enough for any termination question likely to arise in computer science.

### Ackermann's function (again)

In the interest of saving you from having to keep referring
to the [previous post]({% post_url 2022-02-09-Ackermann-example %})
on Ackermann's function, let's recall its definition:

$$
\begin{align*}
	A(0,n) & = n+1\\
	A(m+1,0) & = A(m,1)\\
	A(m+1,n+1) & = A(m,A(m+1,n)).
\end{align*}
$$

Called the generalised exponential, it is an attempt to extend the sequence
*successor*, *addition*, *multiplication*, *exponentiation* indefinitely according to its first argument.
It grows fast: faster than any primitive recursive function, which is
[easy to prove]({% post_url 2022-09-07-Ackermann-not-PR-II %}).

Ackermann's function can easily be expressed in terms of a stack computation, or equivalently as a term rewriting system:

$$
\DeclareMathOperator{\Suc}{Suc}
\DeclareMathOperator{\ack}{ack}
\newcommand{\cons}{\mathbin{\#}}
\begin{align*}
	\Box \cons n\cons 0\cons L &\longrightarrow \Box \cons \Suc n \cons  L\\
	\Box \cons 0\cons \Suc m\cons L &\longrightarrow \Box \cons 1\cons  m \cons L\\
	\Box \cons \Suc n\cons \Suc m\cons L &\longrightarrow \Box \cons n\cons \Suc m\cons  m \cons L
\end{align*}
$$

(In Isabelle, # separates list elements.)


### Defining the functions in Isabelle/HOL

As before, both definitions of Ackermann's function can be typed straight into Isabelle/HOL.
The termination of the standard version is proved automatically.
It's by the lexicographic combination of the two arguments, which works despite the nested recursion in the third line.

<pre class="source">
<span class="keyword1"><span class="command">fun</span> <span class="entity">ack</span></span><span> </span><span class="main">::</span><span> </span><span class="quoted quoted"><span>"</span><span class="main">[</span>nat<span class="main">,</span>nat<span class="main">]</span><span> </span><span class="main">⇒</span><span> </span>nat<span>"</span></span><span> </span><span class="keyword2 keyword">where</span><span>
  </span><span class="quoted quoted"><span>"</span><span class="free">ack</span><span> </span><span class="main">0</span><span> </span><span class="free bound entity">n</span><span>             </span><span class="main">=</span><span> </span>Suc<span> </span><span class="free bound entity">n</span><span>"</span></span><span>
</span><span class="main">|</span><span> </span><span class="quoted quoted"><span>"</span><span class="free">ack</span><span> </span><span class="main">(</span>Suc<span> </span><span class="free bound entity">m</span><span class="main">)</span><span> </span><span class="main">0</span><span>       </span><span class="main">=</span><span> </span><span class="free">ack</span><span> </span><span class="free bound entity">m</span><span> </span><span class="main">1</span><span>"</span></span><span>
</span><span class="main">|</span><span> </span><span class="quoted quoted"><span>"</span><span class="free">ack</span><span> </span><span class="main">(</span>Suc<span> </span><span class="free bound entity">m</span><span class="main">)</span><span> </span><span class="main">(</span>Suc<span> </span><span class="free bound entity">n</span><span class="main">)</span><span> </span><span class="main">=</span><span> </span><span class="free">ack</span><span> </span><span class="free bound entity">m</span><span> </span><span class="main">(</span><span class="free">ack</span><span> </span><span class="main">(</span>Suc<span> </span><span class="free bound entity">m</span><span class="main">)</span><span> </span><span class="free bound entity">n</span><span class="main">)</span><span>"</span></span>
</pre>

Now we declare the stack version.
[Last time]({% post_url 2022-02-09-Ackermann-example %}),
the termination of the stack computation was shown by explicit reasoning
about its domain. The declaration below still uses the `function` keyword,
which means that the termination proof will come later.

<pre class="source">
<span class="keyword1 command">function</span><span> </span><span class="entity">ackloop</span><span> </span><span class="main">::</span><span> </span><span class="quoted quoted"><span>"</span>nat<span> </span>list<span> </span><span class="main">⇒</span><span> </span>nat<span>"</span></span><span> </span><span class="keyword2 keyword">where</span><span>
  </span><span class="quoted quoted"><span>"</span><span class="free">ackloop</span><span> </span><span class="main">(</span><span class="free bound entity">n</span><span> </span><span class="main">#</span><span> </span><span class="main">0</span><span> </span><span class="main">#</span><span> </span><span class="free bound entity">l</span><span class="main">)</span><span>         </span><span class="main">=</span><span> </span><span class="free">ackloop</span><span> </span><span class="main">(</span>Suc<span> </span><span class="free bound entity">n</span><span> </span><span class="main">#</span><span> </span><span class="free bound entity">l</span><span class="main">)</span><span>"</span></span><span>
</span><span class="main">|</span><span> </span><span class="quoted quoted"><span>"</span><span class="free">ackloop</span><span> </span><span class="main">(</span><span class="main">0</span><span> </span><span class="main">#</span><span> </span>Suc<span> </span><span class="free bound entity">m</span><span> </span><span class="main">#</span><span> </span><span class="free bound entity">l</span><span class="main">)</span><span>     </span><span class="main">=</span><span> </span><span class="free">ackloop</span><span> </span><span class="main">(</span><span class="main">1</span><span> </span><span class="main">#</span><span> </span><span class="free bound entity">m</span><span> </span><span class="main">#</span><span> </span><span class="free bound entity">l</span><span class="main">)</span><span>"</span></span><span>
</span><span class="main">|</span><span> </span><span class="quoted quoted"><span>"</span><span class="free">ackloop</span><span> </span><span class="main">(</span>Suc<span> </span><span class="free bound entity">n</span><span> </span><span class="main">#</span><span> </span>Suc<span> </span><span class="free bound entity">m</span><span> </span><span class="main">#</span><span> </span><span class="free bound entity">l</span><span class="main">)</span><span> </span><span class="main">=</span><span> </span><span class="free">ackloop</span><span> </span><span class="main">(</span><span class="free bound entity">n</span><span> </span><span class="main">#</span><span> </span>Suc<span> </span><span class="free bound entity">m</span><span> </span><span class="main">#</span><span> </span><span class="free bound entity">m</span><span> </span><span class="main">#</span><span> </span><span class="free bound entity">l</span><span class="main">)</span><span>"</span></span><span>
</span><span class="main">|</span><span> </span><span class="quoted quoted"><span>"</span><span class="free">ackloop</span><span> </span><span class="main">[</span><span class="free bound entity">m</span><span class="main">]</span><span> </span><span class="main">=</span><span> </span><span class="free bound entity">m</span><span>"</span></span><span>
</span><span class="main">|</span><span> </span><span class="quoted quoted"><span>"</span><span class="free">ackloop</span><span> </span><span class="main">[]</span><span> </span><span class="main">=</span><span>  </span><span class="main">0</span><span>"</span></span><span>
  </span><span class="keyword1 command">by</span><span> </span><span class="operator">pat_completeness</span><span> </span><span class="operator">auto</span>
</pre>

Only this time, termination will be proved with the help of multisets.

### Proving termination via multisets

Recall that the multiset ordering is based on an ordering of the element type.
The elements of our multisets will be pairs of natural numbers,
ordered lexicographically (the first component dominating).
If the first two elements of the stack are $z$ and $y$, then
the multiset will contain the pair $(y,z)$, and each further stack element $x$
will contribute the pair $(x+1,0)$ to the multiset.
The following function accomplishes this:

<pre class="source">
<span class="keyword1 command">fun</span> <span class="entity">ack_mset</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>nat</span> list</span> <span class="main">⇒</span> <span class="main">(</span>nat<span class="main">×</span>nat<span class="main">)</span> multiset<span>"</span> <span class="keyword2 keyword">where</span><span>
  </span><span class="quoted"><span class="quoted"><span>"</span><span class="free">ack_mset</span> <span class="main">[]</span></span> <span class="main">=</span></span> <span class="main">{#}</span><span>"</span><span>
</span><span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">ack_mset</span> <span class="main">[</span><span class="free bound entity">x</span><span class="main">]</span> <span class="main">=</span></span> <span class="main">{#}</span></span><span>"</span><span>
</span><span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">ack_mset</span> <span class="main">(</span><span class="free bound entity">z</span><span class="main">#</span></span><span class="free bound entity">y</span><span class="main">#</span></span><span class="free bound entity">l</span><span class="main">)</span> <span class="main">=</span> mset <span class="main">(</span><span class="main">(</span><span class="free bound entity">y</span><span class="main">,</span><span class="free bound entity">z</span><span class="main">)</span> <span class="main">#</span> map <span class="main">(</span><span class="main">λ</span><span class="bound">x</span><span class="main">.</span> <span class="main">(</span>Suc <span class="bound">x</span><span class="main">,</span> <span class="main">0</span><span class="main">)</span><span class="main">)</span> <span class="free bound entity">l</span><span class="main">)</span><span>"</span>
</pre>

It's not difficult to check that for each of the recursive calls made by
the stack-based computation, the corresponding multiset decreases
according to the multiset ordering and therefore the recursion terminates.
More details are in [the paper](https://doi.org/10.1145/359138.359142);
it's Example 3, on page 471.
The program in that paper reflects the conventions of 1979:
it is coded in a variant of Algol
with $z$ a global variable rather than a stack element.

The most difficult case of termination I had to formalise explicitly, below.
It's for the first recursive call.
That the multiset $\{(m,n+1)\}$ is less than $\{(m+1,0),(0,n)\}$
requires step-by-step reasoning. The cases for the other two recursive calls
are proved automatically.

<pre class="source">
<span class="keyword1 command">lemma</span> case1<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>ack_mset</span> <span class="main">(</span>Suc</span> <span class="free">n</span> <span class="main">#</span> <span class="free">l</span><span class="main">)</span> <span class="main">&lt;</span> add_mset <span class="main">(</span><span class="main">0</span><span class="main">,</span><span class="free">n</span><span class="main">)</span> <span class="main">{#</span> <span class="main">(</span>Suc <span class="bound">x</span><span class="main">,</span> <span class="main">0</span><span class="main">)</span><span class="main">.</span> <span class="bound">x</span> <span class="main">∈#</span> mset <span class="free">l</span> <span class="main">#}</span><span>"</span><span>
</span><span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">cases</span> <span class="quoted free">l</span><span class="main">)</span><span>
  </span><span class="keyword3 command">case</span> <span class="main">(</span>Cons <span class="skolem">m</span> <span class="skolem">list</span><span class="main">)</span><span>
  </span><span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">{#</span><span class="main">(</span><span class="skolem">m</span><span class="main">,</span> Suc</span> <span class="free">n</span><span class="main">)</span><span class="main">#}</span> <span class="main">&lt;</span></span> <span class="main">{#</span><span class="main">(</span>Suc <span class="skolem">m</span><span class="main">,</span> <span class="main">0</span><span class="main">)</span><span class="main">#}</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="operator">auto</span><span>
  </span><span class="keyword1 command">also</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">…</span> <span class="main">≤</span></span> <span class="main">{#</span><span class="main">(</span>Suc</span> <span class="skolem">m</span><span class="main">,</span> <span class="main">0</span><span class="main">)</span><span class="main">,</span> <span class="main">(</span><span class="main">0</span><span class="main">,</span><span class="free">n</span><span class="main">)</span><span class="main">#}</span><span>"</span><span>
    </span><span class="keyword1 command">by</span> <span class="operator">auto</span><span>
  </span><span class="keyword1 command">finally</span> <span class="keyword3 command">show</span> <span class="var quoted var">?thesis</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> Cons<span class="main">)</span><span>
</span><span class="keyword1 command">qed</span> <span class="operator">auto</span>
</pre>

The following command asks Isabelle—specifically, Alex Krauss's [function package](https://isabelle.in.tum.de/dist/Isabelle/doc/functions.pdf)— to check termination
with reference to the function `ack_mset`,
supplying the result proved above as a lemma.

<pre class="source">
<span class="keyword1 command">termination</span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">relation</span> <span class="quoted"><span class="quoted"><span>"</span>inv_image</span> <span class="main">{</span><span class="main">(</span><span class="bound">x</span><span class="main">,</span><span class="bound">y</span><span class="main">)</span><span class="main">.</span> <span class="bound">x</span><span class="main">&lt;</span></span><span class="bound">y</span><span class="main">}</span> ack_mset<span>"</span><span class="main">)</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> wf case1<span class="main">)</span>
</pre>

Since the supplied tactic proved the termination subgoals, termination is established.
Isabelle will now supply unconditional recursion equations for the function.

### Proving the two definitions equivalent

Last time, I introduced an additional function as part of the proof
that the stack-based computation was equivalent to the traditional version of
Ackermann's function. This had educational value perhaps,
but the equivalence can be proved without it.
The following result is all we need:

<pre class="source">
<span class="keyword1 command">lemma</span> ackloop_ack<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>ackloop</span> <span class="main">(</span><span class="free">n</span> <span class="main">#</span></span> <span class="free">m</span> <span class="main">#</span> <span class="free">l</span><span class="main">)</span> <span class="main">=</span> ackloop <span class="main">(</span>ack <span class="free">m</span> <span class="free">n</span> <span class="main">#</span> <span class="free">l</span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">induction</span> <span class="quoted free">m</span> <span class="quoted free">n</span> <span class="quasi_keyword">arbitrary</span><span class="main main">:</span> <span class="quoted free">l</span> <span class="quasi_keyword">rule</span><span class="main main">:</span> ack.induct<span class="main">)</span> <span class="operator">auto</span>
</pre>

As in the [earlier post]({% post_url 2022-02-09-Ackermann-example %}),
a one line proof is possible thanks to `ack.induct`, the induction rule
specific to Ackermann's function.
And now we are done!

<pre class="source">
<span class="keyword1 command">theorem</span> <span class="quoted"><span class="quoted"><span>"</span>ack</span> <span class="free">m</span> <span class="free">n</span> <span class="main">=</span></span> ackloop <span class="main">[</span><span class="free">n</span><span class="main">,</span><span class="free">m</span><span class="main">]</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> ackloop_ack<span class="main">)</span>
</pre>

You'll find the Isabelle proof development [here](/Isabelle-Examples/AckermannM.thy).
Blanchette et al. [describe](https://drops.dagstuhl.de/opus/volltexte/2017/7715/) much more advanced proofs such as [Goodstein’s theorem](https://en.wikipedia.org/wiki/Goodstein%27s_theorem), 
using their [formalisation](https://www.isa-afp.org/entries/Nested_Multisets_Ordinals.html) of nested multisets.