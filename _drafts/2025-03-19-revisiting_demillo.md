---
layout: post
title:  "Revisiting an early critique of formal verification"
usemathjax: true 
tags: [verification,philosophy,formalised_mathematics,Principia_Mathematica]
---
In 1979, a paper appeared that challenged the emerging field of program verification:
"[Social Processes and Proofs of Theorems and Programs](https://doi.org/10.1145/359104.359106)", 
by Richard De Millo, Richard Lipton and Alan Perlis.
They pointed out that proofs in mathematics bore no resemblance
to the formalisms being developed to verify computer programs.
A mathematical proof, they argued, was an argument intended to persuade other mathematicians.
A proof's acceptance by the mathematical community took place through 
a social, consensual process and not through some sort of mechanical checking.
Proofs of programs are too long, tedious and shallow 
to be checked through such a social process.
Some of their points were right, but their main argument was laughably wrong.

### Background

Program verification emerged at the end of the 1960s
with the publication of Robert W Floyd's 
"Assigning Meanings to Programs" 
and Tony Hoare's "[An axiomatic basis for computer programming](https://doi.org/10.1145/363235.363259)".
In his 1971 "[Proof of a Program: FIND](https://doi.org/10.1145/362452.362489)", Hoare worked through the correctness conditions for a subtle algorithm by hand.
Automated program verification tools slowly started to appear,
such as [Gypsy](https://doi.org/10.1145/390019.808306) 
and the [Stanford Pascal Verifier](https://purl.stanford.edu/nh154bt5645)
(which I have experimented with).
These early tools were not very capable and some lacked a sound logical basis.
When I was working at the Stanford AI Lab in 1979,
the main computer (shared by all faculty and students)
had just over one megabyte of memory and we were asked 
not to burden it by using the arrow keys when editing.
So I'm amused to see the authors complain about 
"the lack at this late date of even a single verification of a working system".

### Their argument

The authors' argument rests on two pillars:

* Formal proofs are extremely low-level, "literally unspeakable" and infeasibly long.
* Mathematicians' traditional method of validating a proof through discussion is the right way to establish the truth of any proposition.

The first pillar rests on their claim that Whitehead and Russell's 
*Principia Mathematica* was a "deathblow" for the idea of formalisation, because it 
"failed, in three enormous, taxing volumes, to get beyond the elementary facts of arithmetic."
(Indeed, 362 pages were needed to prove 1+1=2.)
They also mention a logician's claim that the formalisation of a certain result 
by Ramanujan would take 2000 pages "assuming set theory and elementary analysis" and would be of inconceivable length if derived "from first principles". 
Not satisfied with this, they speculate that "ordinary, workaday mathematical proofs"
would require a computer large enough to "fill the entire observable universe"
even assuming "the luxury of a technology that will produce proton-size electronic components connected by infinitely thin wires".

Regarding the second pillar, the authors remark that 
the vast majority of theorems published by mathematicians
are never accepted by the community, being
contradicted, thrown into doubt or simply ignored.
They proceed to quote verbatim a series of footnotes 
they found on a single page of a monograph on the axiom of choice:[^1]

[^1]: T J Jech, *The Axiom of Choice* (North-Holland, 1973), 118.

![Footnotes from Jech](/images/Jech-118-footnotes.png)

The authors seem to revel in the fallibility of mathematicians.
They continue:

> Even simplicity, clarity, and ease provide no guarantee that a proof is correct. The history of attempts to prove the Parallel Postulate is a particularly rich source of lovely, trim proofs that turned out to be false.

They go on to flirt with the idea of abandoning the classical idea of proof altogether in favour of some sort of "probabilistic theorems".

### Their argument, viewed from the 21st century

The pillars of their argument have not stood the test of time.
Within a few years of publication, researchers were proving significant mathematical results
using proof assistants that reduced reasoning to "first principles":
[Wilson's theorem](https://doi.org/10.1007/BF00244993) 
and the [Church-Rosser theorem](https://doi.org/10.1145/44483.44484)
were both proved in 1985;
[Gödel's incompleteness theorem](https://dl.acm.org/doi/10.5555/913294)
followed in 1986
and [Quadratic Reciprocity](https://rdcu.be/edqIJ) in 1990. 
All of this work was done using 
[Nqthm](https://www.cs.utexas.edu/~moore/best-ideas/nqthm/), 
more popularly known as the Boyer–Moore theorem prover.
By 1994, enough mathematics had been formalised for Robert S Boyer
to [propose the QED project](https://rdcu.be/edp1P): 
to build a machine-checked encyclopedia of mathematics.
Today, a vast amount of mathematics has been formalised 
– in Isabelle, Lean, Rocq
and other systems – including
[one of Ramanujan's theorems](https://www.isa-afp.org/entries/Rogers_Ramanujan.html), 
(proved in 20 pages, not 2000).

The situation regarding the second pillar is more interesting.
[A paper](https://www.ias.edu/ideas/2014/voevodsky-origins) published in 2014 
would seem at first sight to buttress the authors' arguments,
in that it provided numerous further examples of errors in mathematics papers
being corrected by the community:

> I was giving a series of lectures, and Pierre Deligne (Professor in the School of Mathematics) was taking notes and checking every step of my arguments. Only then did I discover that the proof of a key lemma in my paper contained a mistake and that the lemma, as stated, could not be salvaged. Fortunately, I was able to prove a weaker and more complicated lemma, which turned out to be sufficient for all applications. A corrected sequence of arguments was published in 2006.

However, Voevodsky's attitude to mathematical mistakes 
turned out to be very different from the authors:

> This story got me scared. Starting from 1993, multiple groups of mathematicians studied my paper at seminars and used it in their work and none of them noticed the mistake. And it clearly was not an accident. A technical argument by a trusted author, which is hard to check and looks similar to arguments known to be correct, is hardly ever checked in detail.

And this is why the Isaac Newton Institute for mathematical sciences
devoted the summer of 2017 to a workshop programme 
entitled [Big Proof](https://www.newton.ac.uk/event/bpr/).
Aimed at "the challenges of bringing [formal] proof technology 
into mainstream mathematical practice", it was attended by a great many mathematicians.
Recently, Fields medallist Peter Scholze asked the verification community to confirm a key lemma of his prior to its publication.
[It was completed](https://leanprover-community.github.io/blog/posts/lte-final/) 
in 18 months.

### But what about the verification of computer systems?

Although the authors' arguments are founded on proofs in mathematics 
and the alleged limitations of formal logic, 
we also need to talk about the point of all this, namely program verification.
The authors are correct that real programs can be millions of lines long,
with messy and complicated specifications. 
We are never going to see a verification of Microsoft Word.
Nevertheless, a number of substantial programs have been formally verified,
such as the [seL4 secure operating system kernel](https://doi.org/10.1145/3230627)
and the [CakeML verifiably bootstrapped compiler](https://cakeml.org).
Hardware verification was not on the authors' radar in 1979,
but it has been even more successful.
Michael Gordon and his team proved the correctness of a 
[simple minicomputer](https://doi.org/10.48456/tr-42) in 1983
of a [network interface chip](https://doi.org/10.48456/tr-66) in 1985
and of a [commercial, military grade microprocessor](https://doi.org/10.48456/tr-134) in 1988.

Today, verification techniques are embedded in the development process of
companies like Nvidia and Intel.
And yes, all of these systems are modified 
from time to time and their formal proofs adjusted as necessary.
The old assumption that verification was only affordable for safety critical applications was exploded 30 years ago, with the 
[Pentium 5 division bug](https://www.righto.com/2024/12/this-die-photo-of-pentium-shows.html). Nobody likes to lose half a billion dollars.
These days, any mission-critical software or hardware is a candidate for verification.

### On the benefit of hindsight

I have struggled to understand what motivated the authors to write this paper in the first place. The 1970s had seen a push to eliminate assembly language programming.
There were two trends in programming language design:

* Pascal and its derivatives such as Modula-2 and Ada.
* Unsafe systems programming languages such as BLISS, BCPL and C.

The UNIX operating system, coded in C, was announced in 1971,
and the Xerox Alto workstation, coded in BCPL, appeared a couple of years later.
Both of these would become hugely influential to the future of computer science.

The authors declare (in the last sentence of the abstract)

> It is felt that ease of formal verification should not dominate program language design.

They got their wish: C took over and the type-safe languages 
(strongly preferred by the program verification community) were abandoned.
The authors conclude by arguing that we all should aim for reliable software.
But we ended up in a world where every non-trivial program performed pointer arithmetic
and where buffer overruns and the link have cost trillions of dollars.

### What they got right

> Since the requirement for a program is informal and the program is formal, there must be a transition, and the transition itself must necessarily be informal.





Cohn, A. The notion of proof in hardware verification. J Autom Reasoning 5, 127–139 (1989). 
https://rdcu.be/edr5n


I quote the exact same footnotes 
in [my grant proposal](https://www.cl.cam.ac.uk/~lp15/Grants/Alexandria/Part-B2.pdf) 
to obtain funding for verification research.
So I owe the authors a debt of gratitude for giving me this example,
for although I had seen it elsewhere they must be the original source.



"So far, there has been little philosophical discussion of making software reliable rather than verifiable."
