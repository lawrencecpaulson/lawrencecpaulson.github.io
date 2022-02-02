---
layout: post
title:  "A classical proof: exponentials are irrational"
usemathjax: true
tags: examples, Isabelle, Proofs from THE BOOK
---

In *[Proofs from THE BOOK](https://link.springer.com/book/10.1007/978-3-662-57265-8)*, Aigner and Ziegler
present hundreds of classic proofs from what we might call the mathematical canon, based in large part on suggestions by [Paul Erdős](https://www.ams.org/notices/199801/comm-erdos.pdf).
The authors confine themselves to proofs requiring "only a modest amount of technique from undergraduate mathematics".
Nothing too advanced or specialised, but nevertheless, a selection of insightful techniques across the mathematical landscape.
Here we look at an Isabelle/HOL proof that the exponential function yields irrational numbers.

### Statement of the problem

Since $\exp(\ln x)=x$, we need to qualify that claim: $\exp r$ is irrational for all rational, nonzero $r$. And this will imply that $\ln r$ is irrational for every positive rational $r≠1$.

The authors present a simple 19th-century proof that uses nothing other than differentiation and integration.
