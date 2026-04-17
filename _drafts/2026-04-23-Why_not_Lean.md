---
layout: post
title:  Why not use Lean?
usemathjax: true 
tags: [AUTOMATH]
---
I have been told that when proposing to formalise mathematics these days, you have to explain why you are not using Lean.
And that reminds me why I left the dependent-typed world 40 years ago:
the cultism, insularity and imposed conformity.
Lean is a great language with good tools,
a large library and a huge, enthusiastic user community that has lately 
accomplished astounding things.
But let's not forget that the 
formalisation of mathematics goes back nearly 60 years.
In all the hype surrounding today's progress we should not lose sight of how we got here. And it was not by people following the crowd.

### In the beginning, there was AUTOMATH

Part of the hype referred to above is the oft-repeated claim "Lean has made the formalisation of mathematics possible".
Sorry, we got there in 1968. 
NG de Bruijn's [AUTOMATH](https://lawrencecpaulson.github.io/tag/AUTOMATH)
already included most of the necessary ingredients.
By 1977, Jutting had used it to formalise Landau's *Foundations of Analysis*, covering mathematical induction, reasoning with equivalence classes and later with sets of rational numbers. 
Jutting proved the Dedekind completeness of the real number line.
His formalisation was an accomplishment that would not be matched for 20 years, despite vast advances in computer power. Finally, in the mid-90s, 
the real numbers were formalised again by John Harrison (in HOL Light) and Jacques Fleuriot (Isabelle/HOL).

I believe that almost anything that has been formalised today in any system could have been formalised in AUTOMATH. 
Its main drawbacks are its notation, which really is horrible, and
its complete lack of automation. Proofs would be too long and completely unreadable. And yet, for reasoning about equivalence classes, 
it is **still** probably better than Rocq.

### And just after, there were Boyer and Moore

From a completely different corner came [the work of Robert Boyer 
and J Moore](https://doi.org/10.1007/s00165-019-00490-3).
First announced in 1973 with the title "[Proving theorems about LISP functions](https://doi.org/10.1145/321864.321875)", 
they set out their objective as the verification of code, not mathematics.
Their "computational logic" has certain limitations for general mathematics, 
but this has not prevented its use in formalising a variety of deep results, ranging from Gödel's incompleteness theorem to quadratic reciprocity to 
the Banach–Tarski paradox. The current incarnation is called ACL2 and it is chiefly applied to hardware verification.

### After LCF: Coq, HOL and Isabelle 

The groundbreaking Edinburgh LCF focused narrowly on programming language semantics, but its idea of having a functional programming language
as the *metalanguage* (hence ML) of a proof assistant had a broad impact.
Groups at least in Cambridge, INRIA and Cornell built tools using ML, including early versions of HOL, Coq and Nuprl.
The HOL group was firmly fixated on hardware verification, but the need to verify floating point hardware brought with it a need for real analysis.
Soon, John Harrison had proved some serious mathematics, such as the prime number theorem. He set himself the task of verifying as many of 
the famous *100 theorems* as possible, 
and for a long time his HOL Light topped the table.
If Isabelle has caught up and surpassed HOL Light, it is mostly because I stole and ported so many of their formalisations.

By 2014, these systems had been used to formalise a string of advanced results. 
Here is a fairly arbitrary list:

* the four colour theorem
* the odd order theorem
* the relative consistency of the axiom of choice
* Gödel's second incompleteness theorem
* Tom Hales' proof of the Kepler conjecture

These theorems mostly had long and intricate proofs. 
Their formalisations were major pieces of work and so
me were key to reducing residual doubts about the theorems.
And yet, few mathematicians were impressed.
Here is a shout-out to two who were: Dana Scott and Ken Kunen.
It's possibly significant that both of them were set theorists.

### The emergence of the Lean community

I know little about the development of Lean itself, 
but I know a bit about how it swept through the mathematical community.
Mathematicians had been sceptical of the proofs mentioned above because 
none of them involved the sophisticated constructions that are necessary 
in mainstream mathematics today: 
things such as Grothendieck schemes and perfectoid spaces.
Tom Hales had the idea of building up a library of such definitions –
just the definitions, never mind the proofs – 
and he chose Lean for that purpose.
He spoke at the Newton Institute programme [Big Proof](https://www.newton.ac.uk/event/bpr/), where many similar ideas were discussed.
Kevin Buzzard heard of this and decided to try out Lean for teaching. 
The rest is history.

### Not everything is "propositions-as-types"

Above, I accused the dependent-types world of insularity: 
what did I mean by that? The hammer sees everything as a nail.
I have seen "proof assistant" *defined* as a piece of software that checks proofs according to the principle of propositions-as-types.
And just like that, most of the research of the past half century is wiped away.
Nothing would be left except Rocq, Lean and Agda 
(which implements Martin-Löf type theory).
Even AUTOMATH is not an instance of propositions-as-types: you set up logic
using axioms like those in any logic text. And the LCF approach certainly isn't.

### LCF (again): we do not need proof objects

Both Rocq and Lean include the category `Prop` of propositions.
This recognises the necessity of proof irrelevance:
different proofs of a proposition must be regarded as equal.
So proof objects are unnecessary, but are kept anyway.

That we do not need proof objects is Robin Milner's key discovery for LCF.
All you need is a programming language (ML!) providing abstract data types.
Put your proof kernel inside an abstract data type, 
with the inference rules at the constructors, and bingo! the proofs are checked dynamically. It is impossible to cheat thanks to ML's abstraction barriers.

I once had the surreal experience of trying to explain this 50-year-old idea 
to somebody from the propositions-as-types world. This was no student
but one of the world's leaning experts on functional programming, 
someone who ought to have known the origin story of the ML language.
It took quite awhile and I don't think he was convinced.

So go ahead, waste gigabytes if you want to.
If [RAMmageddon](https://www.nature.com/articles/d41586-026-00844-x) gets you,
search for ways to shrink those absolutely useless proof terms.

### Why should you use Isabelle?
