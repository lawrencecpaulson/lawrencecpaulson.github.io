---
layout: post
title:  "The philosophical problem of induction, and the problem of Fetzer"
usemathjax: true 
tags: [philosophy,verification]
---
Bertrand Russell has written [an essay](https://www.gutenberg.org/files/5827/5827-h/5827-h.htm#link2HCH0006) that asks,
"We are all convinced that the sun will rise to-morrow. Why?"
This remarkable question takes us to the [*philosophical problem of induction*](https://plato.stanford.edu/entries/induction-problem/)[^1]
and then to another "proof" that formal verification is not merely impossible 
but absurd and pointless.

[^1]: Yes indeed, philosophical induction has nothing to do with mathematical induction.

### On drawing conclusions from observations

Throughout our daily lives we observe our surroundings and subconsciously
make choices on the basis of what has happened before.
We return to a restaurant where we had a good experience and avoid
people who have been unpleasant to us.
Animals too: they return to places where they have found food
and shun places where they have been attacked.
Even plants grow towards sources of water and light.
All of them assume that the future will resemble the past.
In evolutionary terms, this ability to learn from the past
seems to be indispensable for survival.

Scientists working to discover the laws of nature are making a crucial assumption:
that there **are** laws of nature, as opposed to chaos.
We believe the Sun will rise tomorrow not merely because it always has in the past
but because we now possess an elaborate theory of the cosmos
that allows us to predict phenomena such as eclipses with great accuracy.
But we are entirely at the mercy of nature:
the Sun could vanish overnight, not because of some unknown physical law
but because the universe is actually lawless.
And to quote Russell again:[^2]

> The man who has fed the chicken every day throughout its life at last wrings its neck instead.

[^2]: Bertrand Russell, ‘On Induction’, *Problems of Philosophy* (Oxford University Press, 1964)


### ... contrasted with reasoning deductively from axioms

Mathematical reasoning begins with axioms, which are assumed without proof,
and draws conclusions from them rigorously.
The conclusions we draw through mathematics are an entirely different character from the scientific observations mentioned above.
They are not about the real world but about mathematical entities.
There is no past, no future, no observations.
If something is a theorem, it will always be a theorem.

It is also misleading to refer to axioms or theorems as being true.
As I remarked in [an earlier post]({% post_url 2022-07-27-Truth_Models %}),
the Greeks knew that the Earth was round and yet created the field of geometry
on the assumption of infinite flat planes.
Axioms typically create an abstract, simple representation of some more complex phenomenon.
The Pythagorean theorem is a different kind of truth 
from *the Earth is round*:
the former can be shown on paper, while the latter requires observing the world.

In philosophy, knowledge derived 
directly from our brains without observing the world is called
[*a priori knowledge*](https://plato.stanford.edu/entries/apriori/)
and is contrasted with *a posteriori* (empirical) *knowledge*.
And these two realms of knowledge are utterly divorced, or are they?

### How can there be theorems about planets and black holes?

People like to say that Isaac Newton discovered gravity.
Actually, he derived a **mathematical theory** that covered
everything from the motions of the planets 
to Galileo's [Leaning Tower of Pisa experiment](https://en.wikipedia.org/wiki/Galileo%27s_Leaning_Tower_of_Pisa_experiment).
In 1687, Newton published his theory in his book
[Philosophiae Naturalis Principia Mathematica](https://plato.stanford.edu/entries/newton-principia/).
He presented his three laws of motion, followed by a series of propositions proved from them.
He thereby inaugurated the field of theoretical physics, 
which continues to the present day
with (among much else) Einstein's theory of general relativity
and Stephen Hawking's proof that 
[black holes can evaporate](https://www.scientificamerican.com/article/this-is-the-way-the-universe-ends-by-evaporating/).

What does it mean to prove theorems about the real world when, as we have just seen,
mathematics is about objects that do not exist?
It means to prove theorems about **mathematical models** of the real world, which we can use to make predictions and check them.
We do not escape the problem of induction: no matter how accurate our model may be today, things could go rogue tomorrow.

Popular accounts of relativity or quantum mechanics 
often begin by mentioning Newton's laws and adding "but Newton was wrong".
Actually, all models are wrong, or at best, cannot be shown to be right.
Newton's laws are accurate enough to land a man on the moon 
but they cannot explain the behaviour of an electron or a black hole.
Everywhere we look in the natural world, from gas pressure (Boyle's Law)
to the spread of infectious diseases, mathematical models allow us to make
good if not perfect predictions.
No wonder that Eugene Wigner gave his [famous lecture](https://doi.org/10.1002/cpa.3160130102)
(also available [here](/papers/unreasonable.pdf))[^3]
where he says this:

> The first point is that the enormous
> usefulness of mathematics in the natural sciences is something bordering on
> the mysterious and that there is no rational explanation for it.

But he also says this:

> Every empirical law has the disquieting quality that one does not
> know its limitations.

[^3]: Wigner, E.P. (1960), The unreasonable effectiveness of mathematics in the natural sciences. *Comm. Pure Appl. Math.*, 13: 1-14.

The situation in computer science is somewhat different.
We often make simplifying assumptions
that everyone knows to be wrong.
Computer programmers have a mental model of their machine
that covers specific aspects such as word length (32-bit or 64-bit)
and memory capacity, while assuming that it executes C and other languages correctly.
Most of the time they are not planning for failures in the hardware, 
the operating system or the C compiler,
not to mention covert channels, overheating or melted components.
When verifying a security architecture, 
the underlying encryption primitives are typically assumed to be unbreakable.
Every such assumption needs to be addressed somehow, though not necessarily by formal verification.

### Enter a philosopher and his critique

In 1988, a followup to the 
[DeMillo, Lipton and Perlis paper]({% post_url 2025-03-14-revisiting_demillo %}) 
was published by James H Fetzer. (Sorry, no link.)
He largely set aside their arguments to substitute his own,
to say that program verification was impossible in principle due to a "category error":
mixing the two kinds of knowledge outlined above.
It must be pointed out that Fetzer was a trained philosophical logician, 
graduating from Princeton *magna cum lauda* in 1962 and winning a prize for best senior thesis.
So one has to wonder what he was thinking.[^4]

[^4]: Donald MacKenzie has written an account of both papers in his book *Mechanizing Proof* (MIT press, 2001).

His fundamental argument was that a computer program is not a mathematical object
but is stored in the memory of a real, physical computer
and therefore that properties proved of the program in the abstract could not be guaranteed
to hold for the same program executing in the real world.
One doesn't have to be familiar with the
"unreasonable effectiveness of mathematics in the natural sciences"
to find something doubtful about his reasoning.
After all, $E=mc^2$ is also a mathematical theorem 
and it relates to quite dramatic effects in the real world.

Fetzer's argument is only valid against someone who would claim that formal verification
means we can completely abandon testing.
Ironically, a [well argued critique](https://rdcu.be/eeQ4E) of over extravagant claims
about verification was published by one of my colleagues (Avra Cohn)
only a year later. She steers clear of philosophical gobbledygook
and focuses on misleading claims that exaggerate what had been verified.
As noted above, all models incorporate simplifying assumptions; 
moreover, given the cost of verification, 
less critical functions are sometimes simply assumed to be okay.


### The role of testing in a verified system

I asked a colleague, Gerwin Klein, about how they tested the 
[seL4 operating system kernel](https://sel4.systems).
Although it is fully verified in all its functions, there are still things to test:

- code in the verified kernel that is left as an assumption
- code in unverified configurations of the kernel
- tests for verified code to confirm expectations, e.g. that the API is what was intended
- tests for verified code that targets performance and other time-related properties
- integration tests with various user-level libraries and frameworks

For other products, one could imagine testing for overheating, 
vulnerability to [low voltage attacks](https://link.springer.com/chapter/10.1007/BFb0028165)
and other real world risks.
Gerwin mentioned [another paper](https://doi.org/10.1145/1993316.1993532), 
concerning C compilers, where the authors found bugs in
unverified parts of the CompCert compiler.
The evidence suggests that bugs are not discovered in verified code.

Testing may seem to be the perfect response to Fetzer's challenge, 
since it is definitely empirical.
Unfortunately, testing a computer system is not like taking a car for a test drive.
An experienced motorist can drive a car for a short while
and be able to predict how it might perform in conditions not tested,
like a steep climb, a dirt road or foul weather.
The analogous situation with computers would be a car that drove beautifully
but might explode if exactly 26 leaves happened to blow underneath it.

### Epilogue

If you have heard of James H Fetzer before, 
it may be because of his notoriety as a conspiracy theorist.
A co-founder of [Scholars for 9/11 Truth](https://en.wikipedia.org/wiki/9/11_truth_movement#Scholars_for_9/11_Truth),
his claims that no aircraft were involved and 
that the towers were destroyed by nuclear weapons
were so outlandish that most of the group's members left 
to form a new, less crazy truther group.
He also co-authored the book *Nobody Died at Sandy Hook*,
provoking a defamation suit that [awarded $450,000](https://www.bbc.co.uk/news/world-us-canada-50074652) to the father of a child 
killed in the Sandy Hook School shooting.
Fits.
