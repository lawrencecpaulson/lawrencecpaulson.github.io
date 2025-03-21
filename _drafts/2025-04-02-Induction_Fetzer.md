---
layout: post
title:  "The problem of induction, and the problem of James H Fetzer"
usemathjax: true 
tags: [philosophy]
---
Bertrand Russell has written [an essay](https://www.gutenberg.org/files/5827/5827-h/5827-h.htm#link2HCH0006) that asks a remarkable question:
"We are all convinced that the sun will rise to-morrow. Why?"
This takes us to the [philosophical problem of induction](https://plato.stanford.edu/entries/induction-problem/)
(which has nothing to do with "proof by induction")
to another "proof" that formal verification is not merely impossible but pointless.

### On drawing conclusions from observations

Throughout our daily lives we observe our surroundings and subconsciously
make choices on the basis of what has happened before.
We return to a restaurant where we had a good experience and avoid
people who have been unpleasant to us.
Animals do this too: they return to places where they have found food
and shun places where they have been attacked.
Even plants grow towards sources of water and light.
All of them assume that the future will resemble the past.

Scientists working to discover the laws of nature are making a crucial assumption:
that there are laws of nature, that the universe is in some sense lawful.
We believe the Sun will rise tomorrow not merely because it always has in the past
but because we now possess an elaborate theory of the cosmos
that allows us to predict phenomena such as eclipses with great accuracy.
But we are entirely at the mercy of what is and not of what we predict:
for all we know, the Sun could vanish overnight, not because of some unknown physical law
but because our laws were simply an illusion.
And to quote Russell again:[^1]

> The man who has fed the chicken every day throughout its life at last wrings its neck instead.

[^1]: Bertrand Russell, ‘On Induction’, Problems of Philosophy (Oxford University Press, 1964)


### ... contrasted with reasoning deductively from axioms

Mathematics begins with axioms, which are assumed without proof,
and draws conclusions from them by rigorous reasoning.
(The reasoning does not have to be formal, but it must be utterly unambiguous.)
The conclusions we draw through mathematics are an entirely different character from the scientific observations mentioned above.
For one thing, they are not about the real world but about mathematical entities.
For another, there is no past, no future, no observations.
If something is a theorem, it will always be a theorem.

It is also misleading to refer to axioms or theorems as being true:
As I mentioned in [an earlier post]({% post_url 2022-07-27-Truth_Models %}),
the Greeks knew that the Earth was round and yet created the field of geometry
on the assumption of infinite flat planes.
Axioms typically create an abstract, simple representation of some more complex phenomenon.

And none of this is about the real world, … or is it?

### How can there be theorems about black holes?

In 1687, Isaac Newton published his
[Philosophiae Naturalis Principia Mathematica](https://plato.stanford.edu/entries/newton-principia/),
a mathematical treatise outlining his theory of gravity and specifically the motions of the planets.
And in the 1970s, Stephen Hawking proved that 
[black holes can evaporate](https://www.scientificamerican.com/article/this-is-the-way-the-universe-ends-by-evaporating/).
What does it mean to prove theorems about the real world when, as we have just seen,
mathematics is about objects that do not exist?
It means to prove theorems about mathematical models of the real world.
We do not escape the problem of induction, because no matter how accurate our model,
the universe could simply decide tomorrow not to conform.

In other words, we must always rely on our assumption that the universe is lawful.
We don't need to worry about that, because without that assumption it is impossible to make any predictions at all, even if we could somehow remain alive.

More importantly, we must always remain aware of the oversimplifications in our models.
Simplifying assumptions are necessary: for example, if we prove that a
secure digital wallet is correct under the assumption of perfect encryption,
we are separating out the problem of implementing secure encryption
from the implementation of the rest of the digital wallet,
knowing that if the encryption doesn't work, the design of the wallet becomes irrelevant.
It is essential to validate the mathematical model by means of empirical data,
as when it is used to make predictions about the real world which are then confirmed (or not).

And so it happens that a purely theoretical equation such as
$E=mc^2$ can tell us about truly dramatic impacts on the real world.
The real world and the world of mathematics are much more 
tightly coupled than one may have thought at first.