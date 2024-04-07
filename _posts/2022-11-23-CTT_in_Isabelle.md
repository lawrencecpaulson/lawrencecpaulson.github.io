---
layout: post
title:  "Martin-Löf type theory in Isabelle: formalisation"
usemathjax: true
tags: [Martin-Löf type theory, Isabelle, constructive logic]
---

Last July, [I described]({% post_url 2022-07-13-Isabelle_influences %})
how Isabelle emerged from a jumble of influences: AUTOMATH, LCF and Martin-Löf.
I stated that Isabelle had originated as a proof assistant for
[Martin-Löf type theory](http://www.jstor.org/stable/37448).
Eventually I realised that the type theory community wasn't interested in this work,
just as it wasn't much interested in [Nuprl](https://www.nuprl.org), which was
by far the most developed type theory implementation out there.
Both implementations had been left behind by the sudden change to intensional equality.
As I mentioned in the earlier post, the type theory influence remains strong
in the other formalisms supported by Isabelle, notably higher-order logic
and [ZF set theory](https://rdcu.be/cYn9P).
Few however may be aware that Isabelle's instance for constructive type theory,
Isabelle/CTT, still exists and still runs.


### Syntactic prerequisites

The syntactic framework for type theory is the *system of arities*, which determines
how many arguments an operator must be given before it is *saturated*.
This system is nothing but the typed λ-calculus, so we begin by introducing the types (or rather arities)
of individuals, types and judgments.

<pre class="source">
<span class="keyword1 command">typedecl</span> i<span>
</span><span class="keyword1 command">typedecl</span> t<span>
</span><span class="keyword1 command">typedecl</span> o
</pre>

Now we introduce the four forms of judgment: to be a well-formed type, equality of types,
membership in a type, equality for members of the type:

<pre class="source">
<span class="keyword1 command">consts</span><span>
  </span>Type      <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>t</span> <span class="main">⇒</span> prop<span>"</span></span>          <span class="main">(</span><span class="quoted"><span>"</span><span class="keyword3">(</span>_ <span class="keyword1">type</span><span class="keyword3">)</span><span>"</span></span> <span class="main">[</span>10<span class="main">]</span> 5<span class="main">)</span><span>
  </span>Eqtype    <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">[</span>t</span><span class="main">,</span>t</span><span class="main">]</span><span class="main">⇒</span>prop<span>"</span>        <span class="main">(</span><span class="quoted"><span>"</span><span class="keyword3">(</span>_ <span class="keyword1">=</span><span class="keyword3">/ </span>_<span class="keyword3">)</span><span>"</span></span> <span class="main">[</span>10<span class="main">,</span>10<span class="main">]</span> 5<span class="main">)</span><span>
  </span>Elem      <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">[</span>i</span><span class="main">,</span> t</span><span class="main">]</span><span class="main">⇒</span>prop<span>"</span>       <span class="main">(</span><span class="quoted"><span>"</span><span class="keyword3">(</span>_ <span class="keyword3">/</span><span class="keyword1">:</span> _<span class="keyword3">)</span><span>"</span></span> <span class="main">[</span>10<span class="main">,</span>10<span class="main">]</span> 5<span class="main">)</span><span>
  </span>Eqelem    <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">[</span>i</span><span class="main">,</span>i</span><span class="main">,</span>t<span class="main">]</span><span class="main">⇒</span>prop<span>"</span>      <span class="main">(</span><span class="quoted"><span>"</span><span class="keyword3">(</span>_ <span class="keyword1">=</span><span class="keyword3">/ </span>_ <span class="keyword1">:</span><span class="keyword3">/ </span>_<span class="keyword3">)</span><span>"</span></span> <span class="main">[</span>10<span class="main">,</span>10<span class="main">,</span>10<span class="main">]</span> 5<span class="main">)</span>
</pre>

Each of these includes Isabelle mixfix declarations
to support standard notation such as $x=y:A$. 
(A fifth judgment form, a hack used to implement rewriting, isn't shown.)


### The basic propositional types

The *false* proposition is represented, via the propositions-as-types principle, by
the empty type `F`. It has an eliminator, called `contr`.
*True* is represented by `T`, which has one element: `tt`.
<pre class="source">
  F         <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>t</span><span>"</span></span><span>
  </span>T         <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>t</span><span>"</span></span> <span>
  </span>contr     <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>i</span><span class="main">⇒</span>i</span><span>"</span><span>
  </span>tt        <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>i</span><span>"</span></span>
</pre>

Skipping forward a bit, let's look at some of the inference rules for type `F`.
The first simply says that it is a type.
The second rule concerns  `contr`, the eliminator for `F`; it says that
from any `p` belonging to `F` and any well-formed type, it can return something of that type.
This rule expresses the emptiness of `F` through the principle of
[*ex falso quodlibet*](https://en.wikipedia.org/wiki/Principle_of_explosion).

<pre class="source">
  F<span class="main">:</span>  <span class="quoted"><span class="quoted"><span>"</span>F</span> <span class="keyword1">type</span></span><span>"</span><span>
  </span>FE<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">⟦</span><span class="bound">p</span><span class="main">:</span></span> F</span><span class="main">;</span> <span class="bound">C</span> <span class="keyword1">type</span><span class="main">⟧</span> <span class="main">⟹</span> contr<span class="main">(</span><span class="bound">p</span><span class="main">)</span> <span class="main">:</span> <span class="bound">C</span><span>"</span>
</pre>

The corresponding rules for the equality judgments are what you might expect and are omitted.

### The type of natural numbers

We declare the type `N` of the natural numbers
along with its constructors 0 and successor, and its eliminator, `rec`:

<pre class="source">
<span class="keyword1 command">consts</span>
  N         <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>t</span><span>"</span></span><span>
  </span>Zero      <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>i</span><span>"</span></span>                  <span class="main">(</span><span class="quoted"><span>"</span><span class="keyword1">0</span><span>"</span></span><span class="main">)</span><span>
  </span>succ      <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>i</span><span class="main">⇒</span>i</span><span>"</span><span>
  </span>rec       <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">[</span>i</span><span class="main">,</span> i</span><span class="main">,</span> <span class="main">[</span>i<span class="main">,</span>i<span class="main">]</span><span class="main">⇒</span>i<span class="main">]</span> <span class="main">⇒</span> i<span>"</span>
</pre>

We again skip ahead to see the corresponding rules: `N` is a type containing the element 0
and closed under successors.
These last two facts take the form of introduction rules.

<pre class="source">
  NF<span class="main">:</span>  <span class="quoted"><span class="quoted"><span>"</span>N</span> <span class="keyword1">type</span></span><span>"</span><span>
  </span>NI0<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">0</span></span> <span class="main">:</span></span> N<span>"</span><span>
  </span>NI_succ<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="bound">a</span> <span class="main">:</span></span> N</span> <span class="main">⟹</span> succ<span class="main">(</span><span class="bound">a</span><span class="main">)</span> <span class="main">:</span> N<span>"</span>
</pre>

The elimination rule for `N` takes the following form:

<pre class="source">
  NE<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">⟦</span><span class="bound">p</span><span class="main">:</span></span> N</span><span class="main">;</span> <span class="bound">a</span><span class="main">:</span> <span class="bound">C</span><span class="main">(</span><span class="main">0</span><span class="main">)</span><span class="main">;</span> <span class="main">⋀</span><span class="bound">u</span> <span class="bound">v</span><span class="main">.</span> <span class="main">⟦</span><span class="bound">u</span><span class="main">:</span> N<span class="main">;</span> <span class="bound">v</span><span class="main">:</span> <span class="bound">C</span><span class="main">(</span><span class="bound">u</span><span class="main">)</span><span class="main">⟧</span> <span class="main">⟹</span> <span class="bound">b</span><span class="main">(</span><span class="bound">u</span><span class="main">,</span><span class="bound">v</span><span class="main">)</span><span class="main">:</span> <span class="bound">C</span><span class="main">(</span>succ<span class="main">(</span><span class="bound">u</span><span class="main">)</span><span class="main">)</span><span class="main">⟧</span><span>
       </span><span class="main">⟹</span> rec<span class="main">(</span><span class="bound">p</span><span class="main">,</span> <span class="bound">a</span><span class="main">,</span> <span class="main">λ</span><span class="bound">u</span> <span class="bound">v</span><span class="main">.</span> <span class="bound">b</span><span class="main">(</span><span class="bound">u</span><span class="main">,</span><span class="bound">v</span><span class="main">)</span><span class="main">)</span> <span class="main">:</span> <span class="bound">C</span><span class="main">(</span><span class="bound">p</span><span class="main">)</span><span>"</span>
</pre>

In more conventional notation it should be recognisable as mathematical induction,
as it appears in the propositions-as-types paradigm.

$$\begin{align*}
 \frac{\displaystyle {\; \atop p\in \textrm{N}\quad a \in C(0)}\quad
   {[u\in \textrm{N},\; v\in C(u)] \atop b(u,v)\in C(\textrm{succ}(u))}}
        {\textrm{rec}(p,a,b) \in C(p)}
\end{align*}$$

*Equality* rules describe reductions or computations.
Here, they tell us that `rec` provides primitive recursion. Given 0,
it returns the base value, namely `a`:

<pre class="source">
  NC0<span class="main">:</span><span>
   </span><span class="quoted"><span class="quoted"><span>"</span><span class="main">⟦</span><span class="bound">a</span><span class="main">:</span></span> <span class="bound">C</span><span class="main">(</span><span class="main">0</span></span><span class="main">)</span><span class="main">;</span> <span class="main">⋀</span><span class="bound">u</span> <span class="bound">v</span><span class="main">.</span> <span class="main">⟦</span><span class="bound">u</span><span class="main">:</span> N<span class="main">;</span> <span class="bound">v</span><span class="main">:</span> <span class="bound">C</span><span class="main">(</span><span class="bound">u</span><span class="main">)</span><span class="main">⟧</span> <span class="main">⟹</span> <span class="bound">b</span><span class="main">(</span><span class="bound">u</span><span class="main">,</span><span class="bound">v</span><span class="main">)</span><span class="main">:</span> <span class="bound">C</span><span class="main">(</span>succ<span class="main">(</span><span class="bound">u</span><span class="main">)</span><span class="main">)</span><span class="main">⟧</span><span>
   </span><span class="main">⟹</span> rec<span class="main">(</span><span class="main">0</span><span class="main">,</span> <span class="bound">a</span><span class="main">,</span> <span class="main">λ</span><span class="bound">u</span> <span class="bound">v</span><span class="main">.</span> <span class="bound">b</span><span class="main">(</span><span class="bound">u</span><span class="main">,</span><span class="bound">v</span><span class="main">)</span><span class="main">)</span> <span class="main">=</span> <span class="bound">a</span> <span class="main">:</span> <span class="bound">C</span><span class="main">(</span><span class="main">0</span><span class="main">)</span><span>"</span>
</pre>

Given a successor value, `rec` makes a recursive call:

<pre class="source">
NC_succ<span class="main">:</span><span>
   </span><span class="quoted"><span class="quoted"><span>"</span><span class="main">⟦</span><span class="bound">p</span><span class="main">:</span></span> N</span><span class="main">;</span>  <span class="bound">a</span><span class="main">:</span> <span class="bound">C</span><span class="main">(</span><span class="main">0</span><span class="main">)</span><span class="main">;</span> <span class="main">⋀</span><span class="bound">u</span> <span class="bound">v</span><span class="main">.</span> <span class="main">⟦</span><span class="bound">u</span><span class="main">:</span> N<span class="main">;</span> <span class="bound">v</span><span class="main">:</span> <span class="bound">C</span><span class="main">(</span><span class="bound">u</span><span class="main">)</span><span class="main">⟧</span> <span class="main">⟹</span> <span class="bound">b</span><span class="main">(</span><span class="bound">u</span><span class="main">,</span><span class="bound">v</span><span class="main">)</span><span class="main">:</span> <span class="bound">C</span><span class="main">(</span>succ<span class="main">(</span><span class="bound">u</span><span class="main">)</span><span class="main">)</span><span class="main">⟧</span> <span class="main">⟹</span><span>
   </span>rec<span class="main">(</span>succ<span class="main">(</span><span class="bound">p</span><span class="main">)</span><span class="main">,</span> <span class="bound">a</span><span class="main">,</span> <span class="main">λ</span><span class="bound">u</span> <span class="bound">v</span><span class="main">.</span> <span class="bound">b</span><span class="main">(</span><span class="bound">u</span><span class="main">,</span><span class="bound">v</span><span class="main">)</span><span class="main">)</span> <span class="main">=</span> <span class="bound">b</span><span class="main">(</span><span class="bound">p</span><span class="main">,</span> rec<span class="main">(</span><span class="bound">p</span><span class="main">,</span> <span class="bound">a</span><span class="main">,</span> <span class="main">λ</span><span class="bound">u</span> <span class="bound">v</span><span class="main">.</span> <span class="bound">b</span><span class="main">(</span><span class="bound">u</span><span class="main">,</span><span class="bound">v</span><span class="main">)</span><span class="main">)</span><span class="main">)</span> <span class="main">:</span> <span class="bound">C</span><span class="main">(</span>succ<span class="main">(</span><span class="bound">p</span><span class="main">)</span><span class="main">)</span><span>"</span>
</pre>


### The disjoint union of two types

The disjoint union of two types is well known to many through functional programming
or as the categorical notion of a pushout.
An instance of this type is formed from two other types:

<pre class="source">
  PlusF<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">⟦</span><span class="bound">A</span> <span class="keyword1">type</span></span><span class="main">;</span> <span class="bound">B</span> <span class="keyword1">type</span></span><span class="main">⟧</span> <span class="main">⟹</span> <span class="bound">A</span><span class="main">+</span><span class="bound">B</span> <span class="keyword1">type</span><span>"</span>
</pre>

The introduction rules for this type create values by injecting into the left part
or right part, respectively. The type for the opposite part must be well-formed:


<pre class="source">
  PlusI_inl<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">⟦</span><span class="bound">a</span> <span class="main">:</span></span> <span class="bound">A</span><span class="main">;</span> <span class="bound">B</span> <span class="keyword1">type</span></span><span class="main">⟧</span> <span class="main">⟹</span> inl<span class="main">(</span><span class="bound">a</span><span class="main">)</span> <span class="main">:</span> <span class="bound">A</span><span class="main">+</span><span class="bound">B</span><span>"</span>
  PlusI_inr<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">⟦</span><span class="bound">A</span> <span class="keyword1">type</span></span><span class="main">;</span> <span class="bound">b</span> <span class="main">:</span></span> <span class="bound">B</span><span class="main">⟧</span> <span class="main">⟹</span> inr<span class="main">(</span><span class="bound">b</span><span class="main">)</span> <span class="main">:</span> <span class="bound">A</span><span class="main">+</span><span class="bound">B</span><span>"</span>  
</pre>

The elimination rule expects an instance of the union type and performs case analysis
on whether the left or the right part is present:

<pre class="source">
PlusE<span class="main">:</span><span>
    </span><span class="quoted"><span class="quoted"><span>"</span><span class="main">⟦</span><span class="bound">p</span><span class="main">:</span></span> <span class="bound">A</span><span class="main">+</span></span><span class="bound">B</span><span class="main">;</span><span>
      </span><span class="main">⋀</span><span class="bound">x</span><span class="main">.</span> <span class="bound">x</span><span class="main">:</span><span class="bound">A</span> <span class="main">⟹</span> <span class="bound">c</span><span class="main">(</span><span class="bound">x</span><span class="main">)</span><span class="main">:</span> <span class="bound">C</span><span class="main">(</span>inl<span class="main">(</span><span class="bound">x</span><span class="main">)</span><span class="main">)</span><span class="main">;</span><span>
      </span><span class="main">⋀</span><span class="bound">y</span><span class="main">.</span> <span class="bound">y</span><span class="main">:</span><span class="bound">B</span> <span class="main">⟹</span> <span class="bound">d</span><span class="main">(</span><span class="bound">y</span><span class="main">)</span><span class="main">:</span> <span class="bound">C</span><span class="main">(</span>inr<span class="main">(</span><span class="bound">y</span><span class="main">)</span><span class="main">)</span> <span class="main">⟧</span> <span class="main">⟹</span> when<span class="main">(</span><span class="bound">p</span><span class="main">,</span> <span class="main">λ</span><span class="bound">x</span><span class="main">.</span> <span class="bound">c</span><span class="main">(</span><span class="bound">x</span><span class="main">)</span><span class="main">,</span> <span class="main">λ</span><span class="bound">y</span><span class="main">.</span> <span class="bound">d</span><span class="main">(</span><span class="bound">y</span><span class="main">)</span><span class="main">)</span> <span class="main">:</span> <span class="bound">C</span><span class="main">(</span><span class="bound">p</span><span class="main">)</span><span>"</span>
</pre>

Finally, the equality rules describe how this `when` operator is evaluated:

<pre class="source">
  PlusC_inl<span class="main">:</span><span>
    </span><span class="quoted"><span class="quoted"><span>"</span><span class="main">⟦</span><span class="bound">a</span><span class="main">:</span></span> <span class="bound">A</span><span class="main">;</span><span>
      </span><span class="main">⋀</span><span class="bound">x</span><span class="main">.</span> <span class="bound">x</span><span class="main">:</span></span><span class="bound">A</span> <span class="main">⟹</span> <span class="bound">c</span><span class="main">(</span><span class="bound">x</span><span class="main">)</span><span class="main">:</span> <span class="bound">C</span><span class="main">(</span>inl<span class="main">(</span><span class="bound">x</span><span class="main">)</span><span class="main">)</span><span class="main">;</span><span>
      </span><span class="main">⋀</span><span class="bound">y</span><span class="main">.</span> <span class="bound">y</span><span class="main">:</span><span class="bound">B</span> <span class="main">⟹</span> <span class="bound">d</span><span class="main">(</span><span class="bound">y</span><span class="main">)</span><span class="main">:</span> <span class="bound">C</span><span class="main">(</span>inr<span class="main">(</span><span class="bound">y</span><span class="main">)</span><span class="main">)</span> <span class="main">⟧</span><span>
    </span><span class="main">⟹</span> when<span class="main">(</span>inl<span class="main">(</span><span class="bound">a</span><span class="main">)</span><span class="main">,</span> <span class="main">λ</span><span class="bound">x</span><span class="main">.</span> <span class="bound">c</span><span class="main">(</span><span class="bound">x</span><span class="main">)</span><span class="main">,</span> <span class="main">λ</span><span class="bound">y</span><span class="main">.</span> <span class="bound">d</span><span class="main">(</span><span class="bound">y</span><span class="main">)</span><span class="main">)</span> <span class="main">=</span> <span class="bound">c</span><span class="main">(</span><span class="bound">a</span><span class="main">)</span> <span class="main">:</span> <span class="bound">C</span><span class="main">(</span>inl<span class="main">(</span><span class="bound">a</span><span class="main">)</span><span class="main">)</span><span>"</span>
</pre>

The rule for `Inr` is analogous. By the propositions-as-types principle,
the disjoint union corresponds to disjunction and the elimination rule
performs a logical case analysis.
 
### The disjoint union of a family of types

To form a ∑-type you need to supply both a type $A$ and a family of types $B(x)$
indexed by elements of $A$:

<pre class="source">
  SumF<span class="main">:</span>  <span class="quoted"><span class="quoted"><span>"</span><span class="main">⟦</span><span class="bound">A</span> <span class="keyword1">type</span></span><span class="main">;</span> <span class="main">⋀</span><span class="bound">x</span><span class="main">.</span> <span class="bound">x</span><span class="main">:</span></span><span class="bound">A</span> <span class="main">⟹</span> <span class="bound">B</span><span class="main">(</span><span class="bound">x</span><span class="main">)</span> <span class="keyword1">type</span><span class="main">⟧</span> <span class="main">⟹</span> <span class="main">∑</span><span class="bound">x</span><span class="main">:</span><span class="bound">A</span><span class="main">.</span> <span class="bound">B</span><span class="main">(</span><span class="bound">x</span><span class="main">)</span> <span class="keyword1">type</span><span>"</span>
</pre>

The ∑-type is sometimes called a *dependent product*
because its elements are ordered pairs $\langle a,b \rangle$ where the type of $b$
may depend upon the value of $a$. (But just to be confusing, it is more often called
the "dependent sum" type. This is incredibly annoying. And it's wrong.)
The introduction rule constructs such ordered pairs.

<pre class="source">
  SumI<span class="main">:</span>  <span class="quoted"><span class="quoted"><span>"</span><span class="main">⟦</span><span class="bound">a</span> <span class="main">:</span></span> <span class="bound">A</span><span class="main">;</span> <span class="bound">b</span> <span class="main">:</span></span> <span class="bound">B</span><span class="main">(</span><span class="bound">a</span><span class="main">)</span><span class="main">⟧</span> <span class="main">⟹</span> <span class="main">&lt;</span><span class="bound">a</span><span class="main">,</span><span class="bound">b</span><span class="main">&gt;</span> <span class="main">:</span> <span class="main">∑</span><span class="bound">x</span><span class="main">:</span><span class="bound">A</span><span class="main">.</span> <span class="bound">B</span><span class="main">(</span><span class="bound">x</span><span class="main">)</span><span>"</span> 
</pre>

The elimination rule reasons about an element of the Σ-type, which must be an ordered pair,
in terms of the separate components `x` and `y`.

<pre class="source">
  SumE<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">⟦</span><span class="bound">p</span><span class="main">:</span></span> <span class="main">∑</span><span class="bound">x</span><span class="main">:</span><span class="bound">A</span><span class="main">.</span> <span class="bound">B</span><span class="main">(</span><span class="bound">x</span><span class="main">)</span><span class="main">;</span> <span class="main">⋀</span><span class="bound">x</span> <span class="bound">y</span><span class="main">.</span> <span class="main">⟦</span><span class="bound">x</span><span class="main">:</span></span><span class="bound">A</span><span class="main">;</span> <span class="bound">y</span><span class="main">:</span><span class="bound">B</span><span class="main">(</span><span class="bound">x</span><span class="main">)</span><span class="main">⟧</span> <span class="main">⟹</span> <span class="bound">c</span><span class="main">(</span><span class="bound">x</span><span class="main">,</span><span class="bound">y</span><span class="main">)</span><span class="main">:</span> <span class="bound">C</span><span class="main">(</span><span class="main">&lt;</span><span class="bound">x</span><span class="main">,</span><span class="bound">y</span><span class="main">&gt;</span><span class="main">)</span><span class="main">⟧</span>
         <span class="main">⟹</span> split<span class="main">(</span><span class="bound">p</span><span class="main">,</span> <span class="main">λ</span><span class="bound">x</span> <span class="bound">y</span><span class="main">.</span> <span class="bound">c</span><span class="main">(</span><span class="bound">x</span><span class="main">,</span><span class="bound">y</span><span class="main">)</span><span class="main">)</span> <span class="main">:</span> <span class="bound">C</span><span class="main">(</span><span class="bound">p</span><span class="main">)</span><span>"</span>
</pre>

The equality rule describes the computation of this `split` operator, which takes a given
pair and delivers the separate components to the function `c`:

<pre class="source">
  SumC<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">⟦</span><span class="bound">a</span><span class="main">:</span></span> <span class="bound">A</span><span class="main">;</span>  <span class="bound">b</span><span class="main">:</span></span> <span class="bound">B</span><span class="main">(</span><span class="bound">a</span><span class="main">)</span><span class="main">;</span> <span class="main">⋀</span><span class="bound">x</span> <span class="bound">y</span><span class="main">.</span> <span class="main">⟦</span><span class="bound">x</span><span class="main">:</span><span class="bound">A</span><span class="main">;</span> <span class="bound">y</span><span class="main">:</span><span class="bound">B</span><span class="main">(</span><span class="bound">x</span><span class="main">)</span><span class="main">⟧</span> <span class="main">⟹</span> <span class="bound">c</span><span class="main">(</span><span class="bound">x</span><span class="main">,</span><span class="bound">y</span><span class="main">)</span><span class="main">:</span> <span class="bound">C</span><span class="main">(</span><span class="main">&lt;</span><span class="bound">x</span><span class="main">,</span><span class="bound">y</span><span class="main">&gt;</span><span class="main">)</span><span class="main">⟧</span><span>
    </span><span class="main">⟹</span> split<span class="main">(</span><span class="main">&lt;</span><span class="bound">a</span><span class="main">,</span><span class="bound">b</span><span class="main">&gt;</span><span class="main">,</span> <span class="main">λ</span><span class="bound">x</span> <span class="bound">y</span><span class="main">.</span> <span class="bound">c</span><span class="main">(</span><span class="bound">x</span><span class="main">,</span><span class="bound">y</span><span class="main">)</span><span class="main">)</span> <span class="main">=</span> <span class="bound">c</span><span class="main">(</span><span class="bound">a</span><span class="main">,</span><span class="bound">b</span><span class="main">)</span> <span class="main">:</span> <span class="bound">C</span><span class="main">(</span><span class="main">&lt;</span><span class="bound">a</span><span class="main">,</span><span class="bound">b</span><span class="main">&gt;</span><span class="main">)</span><span>"</span> 
</pre>

According to propositions-as-types, a ∑-type corresponds to existential quantification.
If the family $B(x)$ is just one single type $B$,
the ∑-type degenerates to the Cartesian product $A\times B$, 
which corresponds to logical conjunction.
It's remarkable how one type can do so much!


### The product of a family of types

A ∏-type is formed from an indexed family, similarly to a ∑-type.
However, its elements are functions.

<pre class="source">
  ProdF<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">⟦</span><span class="bound">A</span> <span class="keyword1">type</span></span><span class="main">;</span> <span class="main">⋀</span><span class="bound">x</span><span class="main">.</span> <span class="bound">x</span><span class="main">:</span></span><span class="bound">A</span> <span class="main">⟹</span> <span class="bound">B</span><span class="main">(</span><span class="bound">x</span><span class="main">)</span> <span class="keyword1">type</span><span class="main">⟧</span> <span class="main">⟹</span> <span class="main">∏</span><span class="bound">x</span><span class="main">:</span><span class="bound">A</span><span class="main">.</span> <span class="bound">B</span><span class="main">(</span><span class="bound">x</span><span class="main">)</span> <span class="keyword1">type</span><span>"</span>
</pre>

The introduction rule forms an element of the ∏-type, given a *dependent function*:
the type of the result may depend on the value of the argument.
The sort of people who (incorrectly) refer to a ∑-type as a dependent sum
may refer to a ∏-type as a dependent product (also incorrectly), 
although you can't count on consistency here.
If memory serves, this terminology is due to [Robert Constable](https://www.cs.cornell.edu/home/rc/), 
who led the [Nuprl project](https://www.nuprl.org) and wrote a lot of expository material about type theory. 
If you find yourself getting confused, just refer to "Pi and Sigma types".

<pre class="source">
  ProdI<span class="main">: </span><span class="quoted"><span class="quoted"><span>"</span><span class="main">⟦</span><span class="bound">A</span> <span class="keyword1">type</span></span><span class="main">;</span> <span class="main">⋀</span><span class="bound">x</span><span class="main">.</span> <span class="bound">x</span><span class="main">:</span></span><span class="bound">A</span> <span class="main">⟹</span> <span class="bound">b</span><span class="main">(</span><span class="bound">x</span><span class="main">)</span><span class="main">:</span><span class="bound">B</span><span class="main">(</span><span class="bound">x</span><span class="main">)</span><span class="main">⟧</span> <span class="main">⟹</span> <span class="main"><span class="hidden">❙</span><strong>λ</strong></span><span class="bound">x</span><span class="main">.</span> <span class="bound">b</span><span class="main">(</span><span class="bound">x</span><span class="main">)</span> <span class="main">:</span> <span class="main">∏</span><span class="bound">x</span><span class="main">:</span><span class="bound">A</span><span class="main">.</span> <span class="bound">B</span><span class="main">(</span><span class="bound">x</span><span class="main">)</span><span>"</span> 
</pre>

The elimination rule takes a supplied function, an element of the ∏-type,
and applies it to the given argument `a`. The result of this application has type
`B(a)`.

<pre class="source">
  ProdE<span class="main">:</span>  <span class="quoted"><span class="quoted"><span>"</span><span class="main">⟦</span><span class="bound">p</span> <span class="main">:</span></span> <span class="main">∏</span><span class="bound">x</span><span class="main">:</span><span class="bound">A</span><span class="main">.</span> <span class="bound">B</span><span class="main">(</span><span class="bound">x</span><span class="main">)</span><span class="main">;</span> <span class="bound">a</span> <span class="main">:</span></span> <span class="bound">A</span><span class="main">⟧</span> <span class="main">⟹</span> <span class="bound">p</span><span class="main">`</span><span class="bound">a</span> <span class="main">:</span> <span class="bound">B</span><span class="main">(</span><span class="bound">a</span><span class="main">)</span><span>"</span> 
</pre>

The equality rule, given a well-typed function application, applies the function to its argument.
This corresponds to β-reduction in the λ-calculus.

<pre class="source">
  ProdC<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">⟦</span><span class="bound">a</span> <span class="main">:</span></span> <span class="bound">A</span><span class="main">;</span> <span class="main">⋀</span><span class="bound">x</span><span class="main">.</span> <span class="bound">x</span><span class="main">:</span></span><span class="bound">A</span> <span class="main">⟹</span> <span class="bound">b</span><span class="main">(</span><span class="bound">x</span><span class="main">)</span> <span class="main">:</span> <span class="bound">B</span><span class="main">(</span><span class="bound">x</span><span class="main">)</span><span class="main">⟧</span> <span class="main">⟹</span> <span class="main">(</span><span class="main"><span class="hidden">❙</span><strong>λ</strong></span><span class="bound">x</span><span class="main">.</span> <span class="bound">b</span><span class="main">(</span><span class="bound">x</span><span class="main">)</span><span class="main">)</span> <span class="main">`</span> <span class="bound">a</span> <span class="main">=</span> <span class="bound">b</span><span class="main">(</span><span class="bound">a</span><span class="main">)</span> <span class="main">:</span> <span class="bound">B</span><span class="main">(</span><span class="bound">a</span><span class="main">)</span><span>"</span> 
</pre>

According to propositions as types, a ∏-type corresponds to universal quantification.
In its degenerate form (no dependence in $B$), it is the function type $A\to B$
and the inference rules are precisely those for implication.
In particular, the elimination rule is modus ponens.


### Equality types

The equality (or *identity*) types mediate between equality judgments $a=b:A$ and ordinary membership judgments.
To form an equality type you need only a type $A$ and two expressions $a$ and $b$ belonging to type $A$.
It expresses the proposition that $a$ and $b$ are equal when considered as elements of $A$.
It is a principle of type theory that identity is regarded as being bound up with a type
as opposed to being a property of $a$ and $b$ alone.

<pre class="source">
  EqF<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">⟦</span><span class="bound">A</span> <span class="keyword1">type</span></span><span class="main">;</span> <span class="bound">a</span> <span class="main">:</span></span> <span class="bound">A</span><span class="main">;</span> <span class="bound">b</span> <span class="main">:</span> <span class="bound">A</span><span class="main">⟧</span> <span class="main">⟹</span> Eq<span class="main">(</span><span class="bound">A</span><span class="main">,</span><span class="bound">a</span><span class="main">,</span><span class="bound">b</span><span class="main">)</span> <span class="keyword1">type</span><span>"</span> 
</pre>

Whenever we possess an equality judgment, for example through a computation rule,
the corresponding equality type can be introduced.

<pre class="source">
  EqI<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="bound">a</span> <span class="main">=</span></span> <span class="bound">b</span> <span class="main">:</span></span> <span class="bound">A</span> <span class="main">⟹</span> eq <span class="main">:</span> Eq<span class="main">(</span><span class="bound">A</span><span class="main">,</span><span class="bound">a</span><span class="main">,</span><span class="bound">b</span><span class="main">)</span><span>"</span> 
</pre>

The type theory of 1982 is extensional. In particular, a proof of any
identity however deep was collapsed down to a unique token, `eq`.


<pre class="source">
  EqE<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="bound">p</span> <span class="main">:</span></span> Eq</span><span class="main">(</span><span class="bound">A</span><span class="main">,</span><span class="bound">a</span><span class="main">,</span><span class="bound">b</span><span class="main">)</span> <span class="main">⟹</span> <span class="bound">a</span> <span class="main">=</span> <span class="bound">b</span> <span class="main">:</span> <span class="bound">A</span><span>"</span> 
</pre>

And this `eq` is the only possible element of an equality type.

<pre class="source">
  EqC<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="bound">p</span> <span class="main">:</span></span> Eq</span><span class="main">(</span><span class="bound">A</span><span class="main">,</span><span class="bound">a</span><span class="main">,</span><span class="bound">b</span><span class="main">)</span> <span class="main">⟹</span> <span class="bound">p</span> <span class="main">=</span> eq <span class="main">:</span> Eq<span class="main">(</span><span class="bound">A</span><span class="main">,</span><span class="bound">a</span><span class="main">,</span><span class="bound">b</span><span class="main">)</span><span>"</span> 
</pre>

To the objection that the equality type rules unreasonably destroy information, we have
following response:

> You seem to believe that every constructive mathematician means the same thing by "proof" that you do. In fact the word "proof' as used in Martin-Löf's systems means, the information that a computer would need to verify a statement.[^1]

[^1]: From [*Foundations of Constructive Mathematics*](https://link.springer.com/book/10.1007/978-3-642-68952-9)  by Michael J Beeson (Springer, 1980), page 281. 

This quote is said to be a paraphrase of a letter from [Peter Aczel](http://www.cs.man.ac.uk/~petera/)
to [Michael Beeson](https://www.cs.sjsu.edu/faculty/beeson/).
And the claim is that there is no need for the complicated proof of an identity
to be preserved in the elements of identity types, merely the fact of the identity itself,
which is trivial to check by calculation in any particular instance.

The ability to erase the derivations of identities is powerful.
It was the foundation of my
[early paper](https://doi.org/10.1016/S0747-7171(86)80002-5) on well-founded recursion.
I outlined an approach for constructing well-founded relations in order to prove the termination
of almost any recursive function likely to arise in a computational context.
The complicated proofs of the recursion equations would be erased by the elimination rule
for the equality type. 
Similarly, the rewriting tactics that I devised for Isabelle/CTT relied on our ability
to apply a chain of identities without having to store any details.

### Boom!

Unfortunately, sometime towards the end of the 1980s I learned that the equality types
had been reformulated to destroy this erasing property: and extensionality in general.
Ever since (in most type theories apparently), a fundamental distinction must be made
between $n+0=n$ and $0+n=n$ on natural numbers: one of them will hold by definition
but the other only by induction. 
In the latter case, the equality will forever be second class,
and $T(n+0)$ and $T(0+n)$ will be different types.

I am pretty sure that the rules for the 
[intensional identity type](https://www.pls-lab.org/en/Intensional_Type_Theory)
could be entered in the Isabelle as straightforwardly as the other rules shown above.
But I never saw the point of trying.

Next week, we'll see the formalisation in action.
