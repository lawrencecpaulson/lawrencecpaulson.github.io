---
layout: post
title:  "BDDs in HOL: the coolest thing Mike Gordon ever did"
usemathjax: true 
tags: [HOL system, PVS, BDDs, MJC Gordon, verification]
---

On 22 August, it will be five years since the death of [Mike Gordon](https://www.cl.cam.ac.uk/archive/mjcg/), who • basically invented hardware verification
• contributed to the first version of the [ML programming language](https://doi.org/10.1145/512760.512773)
• made major contributions to proof assistant architecture, and 
• showed that higher-order logic was a powerful formalism for verification.
My [biography](http://doi.org/10.1098/rsbm.2018.0019) (also available [here](https://arxiv.org/abs/1806.04002)) describes his main achievements.
But it is almost silent about the coolest thing he ever did: integrating binary decision diagrams (BDDs) with the HOL system.

### Binary decision diagrams (and model checking)

[*Binary decision diagrams*](https://en.wikipedia.org/wiki/Binary_decision_diagram) are a data structure that can represent Boolean formulas compactly and operate on them efficiently.
Each diagram is a decision tree—a [dag](https://en.wikipedia.org/wiki/Directed_acyclic_graph), to be precise, because of identical subtrees are always shared—embodying
all possible sequences of decisions on the Boolean variables, 
subject to some fixed ordering, ρ.
For a given ρ, the BDD corresponding to a formula is the same for all logically equivalent formulas, regardless of their syntactic form.
A BDD can more properly be regarded as representing a boolean *function* as opposed to a formula.
Converting a formula to a BDD yields a *canonical form* for this function.

Invented in 1986, BDDs were originally used to verify hardware designs, proving agreement between specification and implementation for combinational hardware devices such as adders.
Crucially, in the event of non-agreement, they exhibited counterexamples.
All was fully automatic, and with luck or skill, highly efficient.
Randall Bryant's [original paper](https://doi.org/10.1109/TC.1986.1676819) described experiments involving numerous devices.
He included a proof that binary multiplication could not be treated efficiently.

[Model checking](https://doi.org/10.1145/5397.5399) is a verification technique based on state enumeration, supporting a temporal logic and ideally suited for checking properties of concurrent systems.
Initially, verifying a system required first reducing it (by possibly extreme simplifying assumptions) to a few hundred states.
But in 1990, a breakthrough paper appeared: "[Symbolic model checking: $10^{20}$ states and beyond](https://doi.org/10.1109/LICS.1990.113767)".
Thanks to BDDs, model checkers could be turbocharged.

By the mid-1990s, these two powerful, fully automatic technologies were making interactive theorem provers look distinctly feeble.
What to do?

### BDDs in HOL

One answer came from the [Prototype Verification System](http://pvs.csl.sri.com/) (PVS) community.
They undertook verification projects that attempted combine interactive proof with model checking.
PVS had included "a BDD-based tautology checker" from the very beginning.
Unfortunately, tautology checking isn't particularly useful in interactive theorem proving, and BDDs are capable of much more.

In his (2000) paper "[Reachability Programming in HOL98 Using BDDs](https://rdcu.be/cROox)",
Mike Gordon describes two experiments aimed at achieving a true integration between BDDs and interactive theorem proving.
With both, his aim was to enable "intimate combinations of deduction and algorithmic verification, like model checking."
His first approach involved implementing functions to convert between HOL terms and BDDs, but he found it to be lacking. So what was his second approach? Let's look at Mike's own words:

> In the LCF approach, theorems are represented by an abstract type whose primitive operations are the axioms and inference rules of a logic. Theorem proving tools are implemented by composing together the inference rules using ML programs.
> 
> This idea can be generalised to computing valid judgements that represent other kinds of information. In particular, consider judgements $(\rho,t,b)$, where $\rho$ represents a variable order, $t$ is a boolean term all of whose free variables are boolean and $b$ is a BDD. Such a judgement is valid if $b$ is the BDD representing $t$ with respect to $\rho$, and we will write $\rho\, t \mapsto b$ when this is the case. (p. 188)

The HOL community has always been deeply resistant to putting things into the kernel—unlike, I must add, certain other communities—so this decision was a big deal. But the rewards made it worthwhile.
Gordon was able to introduce primitives to construct Boolean formulas by the standard logical connectives while applying the corresponding BDD operations.
In addition to $\land$, $\lor$, etc., even *quantifiers* were permitted, though only over Boolean variables (there being no others);
thus, the system can represent so-called [quantified Boolean formulas](https://en.wikipedia.org/wiki/True_quantified_Boolean_formula) (QBFs).

Mike went on to show how the set of reachable states of a finite state machine could be computed efficiently as a BDD, using a fixedpoint construction.
He remarked that all 32 steps of the calculation of the BDDs of the sets of reachable states of peg solitaire could be completed in a few hours on his 500MHz Linux box. And that reminds me: all those years ago he asked me to draw a peg solitaire figure for him:

<p style="text-align: center;"><img src="/images/peg-solitaire.png" alt="peg solitaire" width="300"/></p>

He presumably intended to use this (and another I drew) in his [later paper, on Puzzletool](https://rdcu.be/cRQVN), in which he describes "programming computation and deduction".
But for some reason, he opted for ASCII art figures instead!

Mike's student Hasan Amjad went on to [build a model checker](https://doi.org/10.48456/tr-601) for the modal $\mu$-calculus within the HOL system, with acceptable performance through the use of BDDs.
This provided true integration of model checking with theorem proving, a goal that had been sought by many.

If you'd like to look deeper into all this, please consult the
[journal version](https://doi.org/10.1112/S1461157000000693)
of Mike's paper, which omits the first experiment and adds further detail about the second one.
And I need to mention that "the coolest thing that Mike ever did" has [tough competition](https://www.cl.cam.ac.uk/events/cl75/posters/f/acjf3-screen.pdf).

#### *Postscript*

As remarked in the comments below, Mike's implementation of BDD judgements in HOL did not involve extending the proof kernel, but rather, creating a *second kernel* specifically about BDDs. The HOL proof kernel already includes provision for *oracles* (arbitrary code that can generate theorems, labelled as such). Mike provided an oracle to allow some results from the BDD world to be transferred into the world of ordinary theorems.
