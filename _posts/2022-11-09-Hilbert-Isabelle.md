---
layout: post
title:  "(Hilbert, Isabelle) and more universal pairs, by Marco David"
usemathjax: true
tags: [Isabelle, David Hilbert, recruitment]
---

Interest in formalizing the mathematics around [Hilbert's Tenth Problem](https://en.wikipedia.org/wiki/Hilbert%27s_tenth_problem) was sparked almost simultaneously in Coq, Mizar, and Isabelle around five years ago. The problem, which demands an algorithm to decide the solvability of any Diophantine equation, is connected to a myriad problems in all fields of mathematics. For instance, the ABC and Goldbach conjectures as well as Fermat's Last Theorem and the Four Color Theorem can be expressed in terms of Diophantine equations. The question posed by Hilbert is at the heart of the interface between computability theory and number theory.

Given the inherently algebraic objects involved, i.e. Diophantine polynomials as well as models of computation such as register machines, the resulting mathematics and their rigorous formulation are easily accessible, even to undergraduate students. In Isabelle, my collaborators and I have completed the formalization of the [DPRM theorem](https://www.isa-afp.org/entries/DPRM_Theorem.html) (cf. below) this past summer. At the same time, I have launched a new student research group in the *Département des Mathématiques et Applications (DMA)* at École Normale Supérieure de Paris, with the support of Dierk Schleicher and Jonas Bayer, in order to formalize new, yet unpublished research results in the field.

This guest post is a progress report of our project with a small look behind the scenes. It is also an advert, rather a **call for participation** to everyone interested, particularly students! Thank you, Larry, for having my post on your blog.

### Diophantine Equations and Hilbert 10

A Diophantine polynomial is a multivariate polynomial with integer coefficients, where we only look for solutions in the integers. Polynomials can then encode sets as follows.

**Definition:**
> A set $A \subseteq N$ is called a *Diophantine set*[^1] if there is a polynomial $P(a, x_1, \ldots, x_\nu)$ with integer coefficients such that $a \in A \Longleftrightarrow \exists x_1, \ldots, x_\nu \in \mathbb Z. \, P(a, x_1, \ldots, x_\nu) = 0$.

[^1]: This definition can also straightforwardly be extended to tuples of natural numbers.

Examples are the set of squares ($a = x_1^2$), Fermat's last theorem for fixed n ($a^n + b^n = c^n$) and even the primes (but the polynomial requires 26 variables). As conjunctions and disjunctions are also realizable with polynomials, this is a class of relations which is remarkably expressive. To the surprise of many, Yuri Matiyasevich ultimately showed that even exponentiation, $a = b^c$ is a Diophantine relation. This assertion also concluded the negative solution of Hilbert's Tenth Problem and is now seen as the key step in its proof.

One obtains a negative answer to Hilbert's Tenth Problem from the Davis-Putnam-Robinson-Matiyasevich (DRPM) theorem which states that *all recursively enumerable sets are Diophantine* [[1]](#references). From the Halting Problem, we know recursively enumerable sets which are not decidable, hence there are Diophantine sets — equivalently, Diophantine equations — which are not decidable.

### Universal Pairs

As Diophantine equations are themselves recursively enumerable, one may find *universal Diophantine equations* which can encode all others, say, by means of an index variable. As a result, we observe that the solvability of any arbitrary Diophantine equation may be reduced to the solvability of an equivalent equation with a fixed number of variables $\nu$ and a fixed degree $\delta$. 

**Definition:**
> A tuple $(\nu, \delta)_{\mathbb Z}$ is called a *universal pair* if any Diophantine set can be represented by a Diophantine equation with $\nu$ variables (in $\mathbb Z$) and degree $\delta$.

It is noteworthy that the existence of a universal pair yields a stronger negative response to Hilbert 10 than above. Instead of there being some undecidable Diophantine equation, we know that it must be contained in the class of $(\nu, \delta)$ equations. In some cases, one may even obtain an explicit universal Diophantine equation which is undecidable!

The attentive reader will have noticed that we made explicit the set of integers $\mathbb Z$ above. By analogy, one may define universal pairs over other sets, for example the natural numbers $\mathbb N$. As such, Hilbert's Tenth Problem over the integers is equivalent to Hilbert's Tenth Problem over the natural numbers by Legendre's four squares theorem. However, when it comes to universal pairs, there is a big difference in efficiency, i.e. the number of variables required for a universal equation.

It is natural to try to reduce $\nu$ and $\delta$ as far as possible. However, unsurprisingly, there is a trade-off between the two. How far can you get? Universal pairs over the natural numbers have been known by Jones and Matiyasevich: 
They found extrema at $(58, 4)\_{\mathbb N}$
with a lowest known degree of four, and 
$(9, 1.6 \times 10^{45})\_{\mathbb N}$ with a lowest known number of variables of nine [[2]](#references). While these can be translated to the integers by naive substitution, this strategy is far from optimal over $\mathbb Z$.

### New Results

Combining various methods from the literature, my collaborators J. Bayer, S. Dubischar, M. Hassler and D. Schleicher have succeeded in obtaining much better universal pairs over the integers. A cornerstone of their work is the following result.

**Proposition:**
> There is $\delta \in \mathbb N$ such that $(11, \delta)\_{\mathbb Z}$ is a universal pair.

(For the curious, our most recent calculation yields $\delta = 85501605795457180647645145654678344726563009024$ but this was intricate and lengthy. We expect the number to change should mistakes be found during the verification process.)

Using only eleven variables is an impressive improvement compared to the naive substitution requiring 27 variables. While it had been known by Sun [[3]](#references) that eleven variables are universal, it was unknown whether this could be achieved for any arbitrary Diophantine polynomial at fixed degree, to obtain a genuine universal pair. 

### Join us!

Many calculations to obtain universal pairs as the above have been done in a "back-of-the-envelope" style, and rigorous proofs of universal pairs are rarely, if ever, available. This makes these results a prime target for formal verification with proof assistants such as Isabelle. In addition to thoroughly verifying the correctness of all logical arguments, here are huge natural numbers that we'd like to have formally checked in the end.

So what is it that distinguishes this project from other verification efforts you could join instead? We're not just taking a textbook and formalizing some chapters of well-established results. We're doing original mathematical research, based on a draft manuscript that is evolving together with the formalization. There are continuous interactions and a steady back-and-forth between the paper and formal proof from which everyone involved is sure to learn a lot. Moreover, the project is well underway, with almost ten thousand lines of theory already written, which gives you a great base to build on. 

There are no prerequisites to join, except for a curiosity to always learn more. Experience with Isabelle or any other interactive theorem prover is welcome, but not required either. We hold semi-regular workshops to teach Isabelle for mathematicians, and provide lots of guidance and exercises well-adapted to the real work to be done in the project.

We are ready to have you join fully remotely. Formalizing a central three-squares theorem or certain properties of Pell equations are components which are especially well-suited to be formalized remotely! We plan to meet via Zoom once a week. Beyond that, you are flexible to work on your tasks and collaborate with others as much as you please and need. The entire group is helpful, eager to learn, and constantly shares lessons learnt with each other. In Paris, France as well as Bremen, Germany there is also a possibility to meet parts of the group in person.

Please [reach out](gdt-isabelle-up@ens.fr) if any of this sounds exciting and interesting to you! We look forward to hearing from you.

PS. If you are interested in our general philosophy about computer-verified proofs, let me refer you to our recent meta-article on the status of formalization in mathematics, titled [Mathematical Proof Between Generations](https://arxiv.org/pdf/2207.04779.pdf) (arXiv:2207.04779).

### References

[1] Yuri Matiyasevich, [Hilbert’s Tenth Problem](https://mitpress.mit.edu/9780262132954/hilberts-10th-problem). MIT Press, Cambridge (1993).

[2] James P. Jones, [Universal Diophantine equation](https://www.jstor.org/stable/2273588). *Journal of Symbolic Logic* **47**:3 (1982), 549–571.

[3] Zhi-Wei Sun, [Further results on Hilbert's Tenth Problem](https://arxiv.org/abs/1704.03504). *Sci. China Math.* **64**:2 (2021), 281-306. 

*This is a guest post by Marco David. Please let me know if you are interested in contributing a post of your own.*
