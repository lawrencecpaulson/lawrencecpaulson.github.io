---
layout: post
title: A trickier lower bound proof
usemathjax: true 
tags: [formalised mathematics, analysis]
---
Last summer, I treated an example of reasoning 
about a function that contained a (removable) singularity.
[That post]({% post_url 2024-08-08-Ln_lower_bound %}) ended with a challenge: to do the same thing for a much trickier function.
Last week, Alexander Pach responded with a solution, which I am delighted to present below.

### A recap

The task last time was to find the minimum of $x\ln x$ for $x\ge0$.
Although strictly speaking it is undefined when $x=0$,
it tends to 0 as $x$ approaches 0 from above, and happily,
0 is the value Isabelle attaches to it anyway.
We had to show the function's continuity with separate proofs for the cases
$x=0$ and $x>0$.
We then obtained its derivative (for $x$ strictly positive)
and by elementary reasoning about its sign
proved that the desired minimum was $-1/e$.

### The challenge

The previous post suggested trying a similar experiment for $x\sin(1/x)$.
This function also has a removable singularity at 0 and its continuity proof (in Isabelle)
is the same as the one for $x\ln x$. However, this function is a horror:

<img src="/images/plot_x_sin_inv_x.png" alt="graph of the function x ln x" width="400"/>

Its derivative, namely $\sin(1/x) - \cos(1/x)/x$, doesn't look nice either.
The lower bound does not appear to be expressible by a simple formula,
so Alexander set up a framework for proving that a given number was a lower bound.
He then calculated it to 81 decimal places!

-0.21723362821122165740827932556247073422304491543558748236544902771450534358906339

You can download his theory [here](/Isabelle-Examples/XsinX_lower_bounds.thy).
