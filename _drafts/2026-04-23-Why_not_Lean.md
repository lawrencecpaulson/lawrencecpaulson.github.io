---
layout: post
title:  Why not use Lean?
usemathjax: true 
tags: [AUTOMATH, LCF, HOL system, HOL Light]
---
I have been told that when proposing to formalise mathematics these days, you have to explain why you are not using Lean.
And that reminds me why I left the dependent-typed world 40 years ago:
its cultism, insularity and imposed conformity.
Lean is a great language with good tools,
a large library and a huge, enthusiastic user community that has lately 
accomplished astounding things.
But let's not forget that the 
formalisation of mathematics goes back nearly 60 years.
In all the hype surrounding today's progress we should not lose sight of how we got here. It was not by people following the crowd.

### In the beginning, there was AUTOMATH

Part of the hype mentioned above is the frequent claim "Lean has made the formalisation of mathematics possible".
Sorry, we got there in 1968. 
NG de Bruijn's [AUTOMATH](https://lawrencecpaulson.github.io/tag/AUTOMATH)
already included most of the necessary ingredients.
By 1977, Jutting had used it to formalise Landau's *Foundations of Analysis*, covering mathematical induction and typed set theory.
Jutting worked with equivalence classes and with sets of rational numbers. 
He formally proved the Dedekind completeness of the real number line.
His accomplishment would not be matched for 20 years, despite vast advances in computer power. Finally, in the mid-90s, 
the real numbers were formalised again by John Harrison (using HOL Light) and Jacques Fleuriot (Isabelle/HOL).

I believe that almost anything that has been formalised today in any system could have been formalised in AUTOMATH. 
Its main drawbacks are its notation, which really is horrible, and
its complete lack of automation. Proofs would be too long and completely unreadable. And yet, for reasoning about equivalence classes, 
it is **still** probably better than Rocq.

### And just after, there were Boyer and Moore

From a completely different corner came [the work of Robert Boyer 
and J Moore](https://doi.org/10.1007/s00165-019-00490-3).
First announced in 1973 with the title "[Proving theorems about LISP functions](https://doi.org/10.1145/321864.321875)", 
they set out their objective as the verification of code, not mathematics.
Their "computational logic" has clear limitations for general mathematics, 
but this has not prevented its use in formalising a variety of deep results, ranging from [Gödel's incompleteness theorem](https://www.cambridge.org/core/books/metamathematics-machines-and-godels-proof/B97649A08193300A18EA41D53FC87214) 
to [quadratic reciprocity](https://doi.org/10.1007/BF00263446) to 
the [Banach–Tarski theorem](https://doi.org/10.4230/LIPIcs.ITP.2022.5). 
The current incarnation is called ACL2 and it is chiefly applied to hardware verification.

### After LCF: Coq, HOL and Isabelle 

The groundbreaking [Edinburgh LCF](https://lawrencecpaulson.github.io/2022/09/28/Cambridge_LCF.html) 
focused narrowly on programming language semantics, but its idea of having a functional programming language
as the *metalanguage* (hence ML) of a proof assistant had a broad impact.
Groups at least in Cambridge, INRIA and Cornell built tools using ML, including early versions of HOL, Coq (now Rocq) and Nuprl.
The HOL group was firmly fixated on hardware verification, but the need to verify floating point hardware brought with it a need for real analysis.
Soon, John Harrison had proved some serious mathematics, such as the prime number theorem. He set himself the task of verifying as many of 
the famous *[100 theorems](https://www.cs.ru.nl/~freek/100/)* as possible, 
and HOL Light often tops the table.
If Isabelle has sometimes surpassed HOL Light, 
it is because I stole and ported so many of their formalisations.

By 2014, these systems had been used to formalise a string of advanced results. 
Here is a fairly arbitrary list:

* the [four colour theorem](https://www.ams.org/notices/200811/tx081101382p.pdf)
* the [odd order theorem](https://doi.org/10.1145/2480359.2429071)
* the [relative consistency](https://doi.org/10.1112/S1461157000000449) of the axiom of choice
* Gödel's [second incompleteness theorem](https://rdcu.be/eSZwv)
* Tom Hales' proof of the [Kepler conjecture](https://doi.org/10.1017/fmp.2017.1)

These theorems mostly had long and intricate proofs. 
Their formalisations were major pieces of work and so
me were key to reducing residual doubts about the theorems.
And yet, few mathematicians were impressed.
Notable exceptions were Dana Scott and Ken Kunen, 
both of them set theorists.

### The emergence of the Lean community

I know little about the development of Lean itself, 
but I know a bit about how it swept through the mathematical community.
Mathematicians had been sceptical of the proofs mentioned above because
none of them involved the sort of sophisticated constructions that are necessary 
in mainstream mathematics today: 
things such as Grothendieck schemes and perfectoid spaces.
Tom Hales had the idea of building up a library of such definitions –
just the definitions, never mind the proofs – 
and he chose Lean for that purpose.
He spoke at the Newton Institute programme [Big Proof](https://www.newton.ac.uk/event/bpr/), where many similar ideas were discussed.
Kevin Buzzard heard of this and decided to try out Lean for teaching. 
The rest is history.

A key act of the Lean community was to abandon the curious obsession with
"constructive proofs" that had dominated Rocq for its entire existence.
As I've discussed previously, 
the philosophy of [intuitionism]({% post_url 2021-11-24-Intuitionism %}) 
arose in the aftermath of Russell's paradox.
It had particular implications for the real numbers.
While [Martin-Löf type theory](https://www.jstor.org/stable/37448) 
was recognisably an intuitionistic formalism, Rocq never was and I'm not aware of any Rocq investigations into the key issues of intuitionistic mathematics.
And yet, paper after paper mentioned constructive proof in contexts that were irrelevant and sometimes nonsensical.

### Not everything is "propositions as types"

[*Propositions as types*]({% post_url 2023-08-23-Propositions_as_Types %}) 
is a duality linking the logical signs 
$\forall$, $\exists$, $\to$, $\wedge$, $\vee$ with the type constructors
$\Pi$, $\Sigma$, $\to$, $\times$, $+$.
It is beautiful, fascinating and theoretically fruitful, 
but it is not the only game out there.
I have seen "proof assistant" *defined* as a piece of software that checks proofs according to the principle of propositions as types.
And just like that, most of the research of the past half century is wiped away.
Nothing would be left except Rocq, Lean and [Agda](https://hackage.haskell.org/package/Agda) 
(which implements Martin-Löf type theory).
Even AUTOMATH is not an instance of propositions as types.
Although it has versions of $\Pi$ and $\to$, you set up logic
using axioms resembling those in any logic text. 
De Bruijn understood, 50 years ago, that the categories of 
types and propositions needed to be kept distinct.

I have even heard people say 
"the LCF approach is the same thing as propositions as types".
This is quite untrue, and I have devoted 
[an entire blogpost]({% post_url 2022-01-05-LCF %}) to trying to make this clear.

### LCF (again): we don't need proof objects!

Both Rocq and Lean include the category `Prop` of propositions.
This recognises the necessity of proof irrelevance:
different proofs of a proposition must be regarded as equal.
So proof objects are unnecessary, but are kept anyway. Why?

That proof objects are unnecessary was
[Robin Milner's key discovery](https://lawrencecpaulson.github.io/2022/01/05/LCF.html) for LCF.
All you need is a programming language (ML!) providing abstract data types.
Put your proof kernel inside an abstract data type, 
with the inference rules at the constructors, and bingo! the proofs are checked dynamically. It is impossible to cheat thanks to ML's abstraction barriers.

I once had the surreal experience of trying to explain this 50-year-old idea 
to somebody from the propositions as types world. This was no student
but one of the world's leading experts on functional programming, 
someone who ought to have known the origin story of the ML language.
It took quite a while and I don't think he was convinced.
This is an example of the insularity that I mentioned at the beginning.

It is crazy, in the age of [RAMmageddon](https://www.nature.com/articles/d41586-026-00844-x),
for people to waste megabytes or perhaps gigabytes 
on giant terms that denote nothing and are good for nothing.
There is even research on making these useless things "nice".

### Why should you use Isabelle?

Let's get the obvious out of the way first: if your colleagues are using Lean, 
have expertise in Lean, and if your key prerequisites are in Lean libraries, 
of course you should use Lean.
