---
layout: post
title:  A fact about bijections proved by Tim Gowers
usemathjax: true 
tags: []
---

A couple of weeks ago, Tim Gowers posted on Twitter an unusual characterisation of bijective functions: that they preserve set complements. 
Alex Kontorovich re-tweeted his post accompanied by a Lean proof detailing Gowers' argument. 
I took a look, and lo and behold! Isabelle can prove it with a single sledgehammer call. 
The one line proof isn't necessarily the best proof however; there's lots to discuss here.

### Gowers' original tweet

> I've just noticed that a function f:X->Y is a bijection if and only if it preserves complements, that is, if and only if f(X\A)=Y\f(A) for every subset A of X. Is this a standard fact that has somehow passed me by for four decades? Simple proof in rest of (short) thread.   1/3

> If f is a bijection and B=X\A, then f preserves unions and intersections and f(X)=Y, so f(A) and f(B) are disjoint and have union equal to Y. Conversely, if f preserves complements, then setting A = emptyset, we see that f(X)=Y, so f is a surjection.  2/3

> And for every x we also have that f(X\{x})=Y\{f(x)}. Therefore, if x and y are distinct, then so are f(x) and f(y). So f is an injection as well. 3/3
