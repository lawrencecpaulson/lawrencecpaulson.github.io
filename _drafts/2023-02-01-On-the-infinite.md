---
layout: post
title:  "On the Infinite"
usemathjax: true 
tags: [philosophy,general]
---

One can't do mathematics without thinking about 
[infinity](https://plato.stanford.edu/entries/infinity/).
And yet infinity seems to lead to every sort of paradox.
One of these is [Thomson’s Lamp](https://plato.stanford.edu/entries/infinity/#ThomLamp)
,
which is alternately switched on and off
at geometrically decreasing intervals, so that within two minutes
it has been switched on and off infinitely many times: will it then be on or off?
Ninety-nine years ago, [David Hilbert](https://en.wikipedia.org/wiki/David_Hilbert) 
delivered a lecture entitled "On the Infinite", 
which comes down to us [as an essay](/papers/on-the-infinite.pdf).
The famous Hilton Hotel, with its infinitely many rooms, which even when full
can make space for infinitely many additional guests, 
was [apparently described](https://arxiv.org/abs/1403.0059)
in this lecture, although it is not in the essay.
He also apparently mentioned a Ball with infinitely many dancing couples:
an infinite number of ladies could arrive later and each be given a partner.
I hope that the music was audible.
How can we make sense of all this?

### Some remarks on reality

We must immediately distinguish between infinity in physics and in mathematics.
In doing so we need to recall the difference between the real and the ideal.
We can draw a circle but no matter how much care we take it can never be perfect:
the paper can never be perfectly smooth nor the arc perfectly round,
since all matter is composed of atoms.
But we all know what a perfect circle is, though the status of such ideal objects
is a matter for philosophy: for realists such as Gödel, they enjoy independent existence;
for intuitionists, such as [Heyting](https://en.wikipedia.org/wiki/Arend_Heyting),
they existed in our minds alone.
But everyone must surely agree that to whatever extent ideal circles are real,
they do not belong to Ken Kunen's *“real world” of cows and pigs*.[^1]

[^1]: Kenneth Kunen. *Set Theory*. (North-Holland, 1980), 94.

I recently watched a Netflix documentary on Infinity, which prompted this post.
Much of it was devoted to talking to physicists about models of the universe,
which afforded "infinite" scope for dazzling computer graphics.
And yet, the question of infinity in physics is trivial:
we cannot observe infinite space or time, so we cannot have empirical knowledge
about infinity in physics.
Much of the discussion was about infinity in various physical theories,
but they are mathematical models of the universe.
Infinities in those models are infinities in mathematics.
This gives us a clue to the resolution of Thomson's Lamp: 
it is asking about the physical state of a physical lamp in a scenario
that is physically impossible, and once we deal with it in the appropriate way,
namely mathematically, it will become trivial.

### Infinity in mathematics

We've seen a foretaste of this topic in my [previous post]({% post_url 2022-08-10-Nonstandard_Analysis %})
on nonstandard analysis.
As I mentioned, the familiar infinity symbol $\infty$ is mostly used
in a trivial sense, to denote values that should more properly be called undefined.
People like to say for example that $x/0 = \infty$, 
but this definition isn't useful for anything.
(Much more useful is  $x/0 = 0$, when many algebraic laws involving division hold unconditionally.)
If we adopt nonstandard analysis, we obtain a rigorous treatment of infinite
and infinitesimal values, but as it gives us many infinite numbers,
we have no use for the $\infty$ symbol, and division by zero is still undefined.


[Hilbert's essay](/papers/on-the-infinite.pdf)[^2] is rewarding to read. 
But it does reflect the state of thinking
nearly a century ago. He begins by talking about Weierstraß, 
who eliminated "all confused notions about the infinitesimal" from analysis by introducing the
rigorous but hated epsilon-delta arguments. 
We now have a coherent set of rules for reasoning with infinitesimals,
and only a mistaken sense of propriety can account for their continued banishment.
Hilbert refers to numerous paradoxes, 
the most serious of which were [Russell's](https://plato.stanford.edu/entries/russell-paradox/)
and [Burali-Forti's](https://en.wikipedia.org/wiki/Burali-Forti_paradox).
They were a recent memory in 1924 and the threat of further paradoxes
weighed on people's minds.
Hilbert enthusiastically described set theory, which he credited to Cantor.
(Zermelo is mentioned only once.)
He includes a lengthy introduction to the transfinite numbers,
but his description gives the impression that set theory was endangered. 
Many people are aware that he wrote

> No one shall drive us out of the paradise which Cantor has created for us.

but who is aware that this paragraph began with these words?

> Wherever there is any hope of salvage...

Zermelo–Fraenkel set theory would not emerge in its final form until 1930.
Hilbert rather pessimistically concluded,

> Our principal result is that the infinite is nowhere to be found in reality. It neither exists in nature nor provides a legitimate basis for rational thought - a remarkable harmony between being and thought. 

Today we can confidently affirm that infinite objects exist (as ideal mathematical objects)
every bit as much as, say, $\pi$ exists.
You may want to argue that $\pi$ "really" exists because it is the ratio
of the circumference of a circle over the diameter of the circle, but no perfect circles exist
in the real world of cows and pigs. As remarked above, we have a coherent theory
of infinitesimal infinite values for analysis.
Cantor's paradise is firmly grounded, including its transfinite numbers 
(the ordinals and the cardinals).

[^2]: David Hilbert. On the infinite. Paul Benacerraf and Hilary Putnam (eds). [Philosophy of Mathematics: Selected Readings](https://doi.org/10.1017/CBO9781139171519). (Cambridge University press, 1984), 183–201.

### Cardinal numbers and Cantor's theorem

Our understanding of cardinality dates back to 
[Dedekind](https://plato.stanford.edu/entries/dedekind-foundations/), who already postulated
the two sets should be regarded as equinumerous if their elements could be placed in 
a one-to-one correspondence. Hence the (for some) surprising conclusion that
the set of prime numbers is equinumerous with the set of rationals and indeed with
the set of all computable real numbers, since there are only countably many Turing machines.

Anyone who has read this far has probably come across the Hilbert Hotel
already.
There are many impressive videos on YouTube, and I recommend
[this one](https://youtu.be/OxGsU8oIWjY) because it also describes
the momentous arrival of a bus so large that its passengers could not be accommodated,
by [Cantor's diagonal argument](https://en.wikipedia.org/wiki/Cantor's_diagonal_argument).

Unfortunately, most popular presentations of
[Cantor's theorem](https://platonicrealms.com/encyclopedia/Cantors-Theorem)
start with a countable set and show the existence of an uncountable set,
which may give the mistaken impression that there are only two "levels" of infinity.
In actual fact, Cantor's theorem can be applied to any set, 
yielding another set of strictly greater cardinality.
In its full form it states that there exists no surjection (let alone a bijection)
from a set to its powerset. It holds for all sets, finite and infinite.
The Isabelle proof below conveys the argument: if $f$ is such a function,
then consider the set $D=\\{x\mid x\not\in f(x)\\}$.
Then $D$ cannot be in the range of $f$, and we recognise the diagonal argument.
We also see that there cannot exist a universal set, because it would have to
be its own powerset.

<pre class="source">
<span class="keyword1 command">theorem</span> Cantor<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">∄</span><span class="bound">f</span> <span class="main">::</span> <span class="tfree">'a</span> <span class="main">⇒</span> <span class="tfree">'a</span> set</span><span class="main">.</span> <span class="main">∀</span></span><span class="bound">A</span><span class="main">.</span> <span class="main">∃</span><span class="bound">x</span><span class="main">.</span> <span class="bcardinalsspan> <span class="main">=</span> <span class="bound">f</span> <span class="bound">x</span><span>"</span><span>
</span><span class="keyword1 command">proof</span><span>
  </span><span class="keytheir command">assume</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">∃</span></span><span class="bound">f</span> <span class="main">::</span> <span class="tfree">'a</span> <span class="main">⇒</span> <span class="tfree">'a</span> set</span><span class="main">.</span> <span class="main">∀</span><span class="bound">A</span><span class="main">.</span> <span class="main">∃</span><span class="bound">x</span><span class="main">.</span> <span class="bound">A</span> <span class="main">=</span> <span class="bound">f</span> <span class="bound">x</span><span>"</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">obtain</span> <span class="skolem skolem">f</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span><span class="tfree">'a</span> <span class="main">⇒</span> <span class="tfree">'a</span> set</span><span>"</span></span> <span class="keyword2 keyword">where</span> *<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">∀</span></span><span class="bound">A</span><span class="main">.</span></span> <span class="main">∃</span><span class="bound">x</span><span class="main">.</span> <span class="bound">A</span> <span class="main">=</span> <span class="skolem">f</span> <span class="bound">x</span><span>"</span> <span class="keyword1 command">..</span><span>
  </span><span class="keyword1 command">let</span> <span class="var quoted var">?D</span> <span class="main">=</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">{</span><span class="bound">x</span><span class="main">.</span> <span class="bound">x</span> <span class="main">∉</span></span> <span class="skolem">f</span> <span class="bound">x</span><span class="main">}</span><span>"</span></span><span>
  </span><span class="keyword1 command">from</span> * <span class="keyword3 command">obtain</span> <span class="skolem skolem">a</span> <span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span><span class="var">?D</span> <span class="main">=</span></span> <span class="skolem">f</span> <span class="skolem">a</span><span>"</span></span> <span class="keyword1 command">by</span> <span class="operator">blast</span>
  <span class="keyword1 command">moreover</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">a</span> <span class="main">∈</span></span> <span class="var">?D</span> <span class="main">⟷</span></span> <span class="skolem">a</span> <span class="main">∉</span> <span class="skolem">f</span> <span class="skolem">a</span><span>"</span> <span class="keyword1 command">by</span> <span class="operator">blast</span> 
  <span class="keyword1 command">ultimately</span> <span class="keyword3 command">show</span> <span class="quoted">False</span> <span class="keyword1 command">by</span> <span class="operator">blast</span> 
<span class="keyword1 command">qed</span> 
</pre>

Ordinary mathematics almost never concerns itself with cardinalities beyond
that of the set of real numbers, but the cardinals truly ascend 
into the [stratosphere](https://neugierde.github.io/cantors-attic/).
We can construct some that are already beyond human imagination,
but they are nothing by comparison with some that have been postulated.

### The ordinal numbers

Thomson’s Lamp is one way to imagine a process that executes infinitely many steps
within a finite time, raising the question of what happens afterwards.
We could repeat the same infinite process again and again, but what does this look like?
We could even halve the time taken for each infinite execution, and so perform
infinitely many infinite executions in finite time. The transfinite ordinals give us a way of labelling these steps. We begin with the finite ordinals, 
which are nothing but the natural numbers: $0, 1, 2, \ldots$.
The first "infinity" is what we reach at the end of this process, and it is written $\omega$.
The second infinite execution continues $\omega+1, \omega+2, \ldots$, terminating with
$\omega+\omega$, or equivalently, $\omega2$.
This can continue "forever", 
as Hilbert outlines on page 189 of his paper.
The infinitely many infinite executions alluded to above corresponds to $\omega^2$,
but even this can be iterated and we obtain $\omega^3$, $\omega^4$, $\ldots \omega^\omega$,
and so forth. All of these ordinals are countable, and among all countable ordinals, still tiny.

We are now equipped to solve the problem of Thomson’s Lamp.
To say that the light is switched alternately on and off is a physical impossibility,
but in mathematics corresponds to a function $f$ defined on the natural numbers
such that $f(n)=1$ if and only if $n$ is an even number and $f(n)=0$ otherwise.
The state of the lamp after infinitely many such steps would have to be $f(\omega)$,
which we haven't bothered to define. 
[BFD](https://www.urbandictionary.com/define.php?term=BFD).

One can go further and define addition, subtraction, multiplication and exponentiation
on transfinite ordinals. They can be regarded as abstractions of well ordered sets,
which gives them applications to the problem of program termination in computer science.

[^2]: David Hilbert. On the infinite. Paul Benacerraf and Hilary Putnam (eds). [Philosophy of Mathematics: Selected Readings](https://doi.org/10.1017/CBO9781139171519). (Cambridge University press, 1984), 183–201.