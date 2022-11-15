---
layout: post
title:  "Martin-Löf type theory in Isabelle, II"
usemathjax: true
tags: [Martin-Löf type theory, Isabelle, examples]
---

The [previous post]({% post_url 2022-11-23-CTT_in_Isabelle %})
describes the implementation of Martin-Löf type theory in Isabelle.
The ability to type in the rules in a notation as close as possible
to the original papers and use them immediately for proofs was a key design objective
in the early days of Isabelle.
Now, through some tiny examples, let's see how terms can be built incrementally
with the help of schematic variables and high-order unification.
Such terms can be proof objects, but they do not have to be.

###  Incremental term construction

The simplest possible example is to use the type formation rules,
available as `form_rls`, a list of theorems starting with those for $N$ and the $\Pi$-types.

To begin, we enter a **schematic** goal. This allows the use of schematic variables
in the goal, presumably with the expectation that they will be replaced
during the course of the proof.
Isabelle displays these instantiations.

Our initial goal invites Isabelle to generate a well formed type in any possible way:

<img src="/images/CTT/typefm-in1.png" alt="type formation example input" height="44px" />

The cursor is placed after the application of the typing rules, which have instantiated `?A`
with the type `N`:

<img src="/images/CTT/typefm-out1.png" alt="type formation example output" height="66px" />

We have the option of asking Isabelle to backtrack over its most recent choice.
Prolog programmers will notice the similarity to responding to a Prolog output
with a semicolon:

<img src="/images/CTT/typefm-in2.png" alt="type formation example input" height="66px" />

Backtracking has taken us to the next type formation in the list, which is for
$\Pi$-types. But now we are required to synthesise two additional types `?A4` and
the indexed family `?B4(x)`:

<img src="/images/CTT/typefm-out2.png" alt="type formation example output" height="88px"/>

We continue by applying the same list of type formation rules again:

<img src="/images/CTT/typefm-in3.png" alt="type formation example input" height="88px" />

The obvious choice for `?A4` is once again `N`. Note how type `?A` below is now
partially filled in:

<img src="/images/CTT/typefm-out3.png" alt="type formation example output" height="88px" />

We unimaginatively continue with the same set of rules, to instantiate the last remaining type.

<img src="/images/CTT/typefm-in4.png" alt="type formation example input" height="110px" />

The family of types `?B4(x)` has been instantiated (yet again) with `N`.
It is a degenerate family with no dependence on `x`.

<img src="/images/CTT/typefm-out4.png" alt="type formation example output" height="66px" />

So the $\Pi$-type degenerates to a mere function type and is displayed as such,
thanks to some syntactic trickery in the implementation of CTT.
We could have continued to backtrack in order to generate
other well-formed types.

### Watching proof objects emerge


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

### Automation of rewriting and type-checking


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




But I was deeply taken by and devoted perhaps a year of intensive work in order to produce that nobody noticed:


The problem was, for unification to be meaningful for Martin-Löf type theory, it had to take account of variable binding. Luckily, I had spent a couple of weeks with Huet at Inria. One day, he had taken me aside to explain higher-order unification.
I probably understood only 2% of what he said, but something must have stuck in my mind.
It was enough for me to locate and study [his paper on the topic](https://doi.org/10.1016/0304-3975(75)90011-0).
It became clear that higher-order unification would indeed do the trick.


