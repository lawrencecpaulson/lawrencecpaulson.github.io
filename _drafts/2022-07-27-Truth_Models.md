---
layout: post
title:  "Mathematical truth, mathematical modelling and axioms"
usemathjax: true 
tags: general, logic
---

The recent pandemic has given us a striking demonstration of science in action.
Over a period of two years, scientists around the world examined this unknown pathogen.
They analysed its genome and developed vaccines and treatments.
But many people were not impressed, noting that scientific advice changed from month to month, sometimes radically.
To them, that showed that scientific knowledge was unreliable.
Many preferred to rely on treatments advocated by quacks based on no evidence but promoted with absolute and unchanging confidence.
Some fell ill but continued to cling to quack advice and conspiracy theories until literally their dying breath.
On the other hand, mathematical truth is infallible, right?

### Truth in mathematics

Scientific truth, in the beliefs of researchers regarding COVID-19 for example, is regularly challenged by new observations.
Regarding mathematical truth, our starting point must be the classic work
*[Proofs and Refutations: The Logic of Mathematical Discovery](https://doi.org/10.1017/CBO9781139171472)*
by [Imre Lakatos](https://plato.stanford.edu/entries/lakatos/).
Lakatos tells the story of Euler's formula, which relates the vertices, edges and faces of polyhedra.
He considers a sequence of counterexamples, such as cylinders, polyhedra containing holes, and solids consisting of two polyhedra joined at a single vertex or edge.

I can't agree with Lakatos' apparent view that mathematical proof and scientific proof amount to the same thing.
If they were, we'd have to regard the [Riemann Hypothesis](https://www.cantorsparadise.com/the-riemann-hypothesis-explained-fa01c1f75d3f) as true, as it's been [checked by computer](https://arxiv.org/pdf/1607.00709.pdf) for billions of cases over an extremely wide range.
The numerous counterexamples to Euler's formula represent the vagueness of the word "polyhedron", and—though I'm no philosopher, mind—cannot be compared with the discovered of a hitherto unknown organism.
Modern geometry is more precise about the definition of a polyhedron, and the [theorem has even been generalised](https://doi.org/10.4153/CMB-1997-056-4) beyond the three-dimensional case.
Mathematical truth and scientific truth are fundamentally different concepts.

### Mathematical models in science (and formal verification)

Everybody knows that the Earth was believed to be the centre of the Universe until Copernicus proposed his heliocentric model.
Placing the Sun at the centre greatly simplified the orbits of the planets compared with the older, Ptolemaic model.
We now know that the solar system is infinitely more complex than Copernicus imagined.

Simple, abstract models are ubiquitous in science. Every student of Physics has explored a world where blocks slide down slopes without friction and spheres trace perfect parabolas with no air resistance.
Apparently unrealistic models are also common in verification.
[Mike Gordon's hardware models](https://doi.org/10.1007/978-1-4613-2007-4_4) ignore the basic limitations of electronics, such as gate delays and fan-outs.
Cryptographic [protocols are typically verified](https://doi.org/10.3233/JCS-1998-61-205) (or [here](https://www.cl.cam.ac.uk/~lp15/papers/Auth/jcs.pdf)) under the assumption that encryption is unbreakable.
How can we justify such unrealistic assumptions?

* You have to stop somewhere. To capture electronic circuits completely we'd have to descend to the level of electrons and quarks, and even they belong to a model of physics.
* Gordon's models deal with one important aspect of hardware design: the functional correctness of circuits. Other issues (e.g. clock rate) could be dealt with separately.
* Similarly, the correctness of cryptographic protocol can be examined separately from that of the underlying encryption method.
A faulty protocol can be broken without breaking the encryption, e.g. through a man-in-the-middle attack.

Both COVID-19 researchers and climate scientists have been attacked for their use of models, but that's how science is done.
Political demands for scientists to do without models are as senseless as demands for a "chemical-free body" or Nadine Dorries asking Microsoft to get [rid of algorithms](https://www.indy100.com/politics/nadine-dorries-microsoft-algorithms-meme).

The purpose of such models is to capture just enough detail to cover some issue of concern.
A model is useful if it can make predictions, and we simply need to bear its limitations in mind.
For example, if we verify a processor design using Gordon's techniques,
it's essential [not to oversell what has been proved](https://rdcu.be/cRjMz), remaining aware of our model's limitations.

### Axioms in mathematics

To a mathematician, a model is something else entirely: a construction (typically a set) satisfying a given collection of axioms.
In many cases, in apparent inversion of the situation in science, the axioms themselves capture just a few essential aspects of already existing constructions: we had the models *before* we had the axioms.
In a few cases, such as the Zermelo-Fraenkel axioms or the $\lambda$-calculus, the axioms were inspired by other considerations; 
without a model, people feel uncomfortable about using them.

<img src="/images/pure-silver.jpg" alt="I guarantee these bullets are pure silver" width="600"/>


* Axioms are another matter. We don't have to "believe" axioms. 
* The Greeks knew that the world was round, but they assumed the parallel postulate, which is false for around the world.
* Euclidean geometry assumes a flat world. It has proved to be extremely useful even though the world is flat.
* This gives us an angle on other controversial axioms, such as the axiom of choice.
* A colleague once told me "the axiom of choice is a lie". But axioms are not equivalent to a statement such as "I did not sleep with that woman".
* We explore the consequences of axioms. Developing mathematics in that way seems to be useful and interesting.
* Many mathematicians will have worked with an axiom (say the axiom of determinacy) that contradicts another axiom (choice) that they have used on another occasion. That doesn't mean their beliefs are inconsistent.

