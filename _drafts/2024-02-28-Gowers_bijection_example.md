---
layout: post
title:  Two Small Examples by Fields Medallists
usemathjax: true 
tags: [examples,sledgehammer]
---

A couple of weeks ago, Tim Gowers posted on Twitter an unusual characterisation of bijective functions: that they preserve set complements. 
Alex Kontorovich re-tweeted that post accompanied by a Lean proof detailing Gowers' argument. 
I took a look, and lo and behold! Isabelle can prove it with a single sledgehammer call. 
That one line proof isn't necessarily the best proof, however.
Remember, we want proofs that are easy to read and easy to maintain. 
And Terrence Tao published a small example on Mastodon; let's look at that one too.

### Gowers' original tweet

Here is the original tweet, a thread in classical Twitter style: 

> I've just noticed that a function f:X->Y is a bijection if and only if it preserves complements, that is, if and only if f(X\A)=Y\f(A) for every subset A of X. Is this a standard fact that has somehow passed me by for four decades? Simple proof in rest of (short) thread.   1/3

> If f is a bijection and B=X\A, then f preserves unions and intersections and f(X)=Y, so f(A) and f(B) are disjoint and have union equal to Y. Conversely, if f preserves complements, then setting A = emptyset, we see that f(X)=Y, so f is a surjection.  2/3

> And for every x we also have that f(X\{x})=Y\{f(x)}. Therefore, if x and y are distinct, then so are f(x) and f(y). So f is an injection as well. 3/3

In standard mathematical notation, the claim is that if a function $f:X\to Y$ is given,
then $f$ is a bijection from $X$ to $Y$ if and only if it preserves complements, i.e. 
if $f[X\setminus A] = Y \setminus f[A]$ for all $A\subseteq X$.
Incidentally, there are various ways of writing the image under a function of a set; 
Here I use square brackets, while Lean and Isabelle provide their own image operators. 

### The Lean formalisation

Kontorovich posted his version as an image: 

<img src="/images/Gowers-example.jpeg" alt="Formalisation of the bijection proof in Lean by Alex Kontorovich"/>

Note that he has written out the argument in detail, with plenty of comments explaining what is going on. 

### Investigating the problem in Isabelle

This problem looked intriguing, so I typed it into Isabelle.
The brute force way to tackle such a problem is first try the auto proof method
and then to invoke [sledgehammer](https://isabelle.in.tum.de/dist/doc/sledgehammer.pdf) 
on any subgoals that are produced. 
The proof you get this way is likely to be horrible. 
However, once you have a proof it's easy to get a nicer proof. 
For the current problem, if you type auto, you get four ugly subgoals, each of which sledgehammer proves automatically. 
I don't want to show this, but you can try it for yourself. 
The Isabelle theory file is [here](/Isabelle-Examples/Gowers_Bijection.thy).

What I actually tried, first, was to split the logical equivalence into its two directions. 
I was pleased to see that sledgehammer could prove both of them. 
Then I thought, let's see if it can prove both directions at once, and indeed it could!
But please note: if you can, always break up your problem 
into simpler parts before calling sledgehammer; 
the effort needed to prove all the separate parts 
is generally much less than that need to prove the whole all at once. 

XXX

The Isabelle formulation is actually stronger then the other two, 
which are conditional on $f:X\to Y$. It states unconditionally that 
$f$ is a bijection from $X$ to $Y$ if and only if it preserves complements, i.e. 
$f[X\setminus A] = Y \setminus f[A]$ for all $A\subseteq X$.

The file containing this example can be [downloaded](/Isabelle-Examples/Gowers_Bijection.thy).