---
layout: post
title:  "Fun with Ackermann's function"
usemathjax: true 
tags: examples, Isabelle, Ackermann's function
---

An undergraduate course on computation theory typically introduces some models of computation: Turing machines, register machines, general recursive functions and possibly the lambda calculus. They learn about the principle of primitive recursion, which is easy to grasp, and the minimisation operator, which isn't. Ackermann's function is invariably mentioned as an example of a function that is obviously computable but not computable by primitive recursion alone. Unfortunately, it is not easily expressible in the familiar models of computation, although its definition is simplicity itself.

### Ackermann's function

In its modern form (having been simplified by Rózsa Péter and Raphael Robinson), Ackermann's function is defined as follows:

$$
\begin{align*}
	A(0,n) & = n+1\\
	A(m+1,0) & = A(m,1)\\
	A(m+1,n+1) & = A(m,A(m+1,n)).
\end{align*}
$$

It resembles the calculation of the Ramsey number as given by the [proof of Ramsey's theorem]({% post_url 2021-12-29-Ramsey-1 %}). Both can easily express unimaginably large numbers.
I was taught this material at Caltech by [Frederick B Thompson](https://www.caltech.edu/about/news/frederick-b-thompson-43160), who as a homework exercise asked his students to write out in full the calculation $A(4,3)$. Nobody did, but one of the students managed to estimate that 

$$ A(4,3)\approx 10^{10^{20000}}. $$

The first argument determines how rapidly it rises: note that $A(3,4)=125$. 
It's funny to think that physicists think that $10^{80}$ is a big number, greater than the number of neutrinos in the universe and vastly greater than the diameter of the universe (in microns). They have no idea what a large number is.

### Expressing Ackermann's function

Ackermann's function is syntactically recursive but that does not help us express it using recursive function theory. Cutland, in [*Computability*](https://doi.org/10.1017/CBO9781139171496) (pages 46–47) devotes an entire page to sketching a laborious construction of a register machine, before remarking that ``a sophisticated proof'' is available as an application of more advanced results. 

One model of computation that can easily express Ackermann's function is the lambda calculus, through the glory of Church numerals (for details, see [my lecture notes](https://www.cl.cam.ac.uk/~lp15/papers/Notes/Founds-FP.pdf), page 17):

 $$
 \begin{align*}
F &\equiv \lambda f n. n f (f \underline{1}) \\
A &\equiv \lambda m. m F \mathbf{suc}
\end{align*}
$$




 [my paper](https://doi.org/10.1017/bsl.2021.47)
 
  [Rosetta code](https://rosettacode.org/wiki/Ackermann_function) for implementations in hundreds of programming languages