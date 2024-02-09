---
layout: post
title:  Contradictions and the Principle of Explosion
usemathjax: true 
tags: [logic, Bertrand Russell, philosophy]
---

That logic should be [free from contradiction](https://plato.stanford.edu/entries/contradiction/#) probably its most basic principle, 
dating back to Aristotle. As described [last time]({% post_url 2024-01-31-Russells_Paradox %}), 
the emergence of a contradiction in set theory in the form of Russell's paradox was catastrophic. Few question the requirement that we cannot have P and not-P at the same time.
But the law of contradiction is associated with something else, the *principle of explosion*,
or [*ex contradictione quodlibet*](https://plato.stanford.edu/entries/logic-paraconsistent/#BrieHistExContQuod):
that a contradiction implies everything. 
This principle has been disputed. One can formulate predicate logic without it 
(it's called *minimal logic*), and there's an amusing tale regarding Bertrand Russell. 
Allegedly a student challenged him by saying "suppose 1=0 and prove that you are the Pope". 
He is said to have replied that if 1=0 then 2=1 and therefore 
the 2-element set containing himself and the pope actually contains one element. 
Is that argument rigorous? 

### Origins

A 12th century Parisian logician named 
[William of Soissons](https://en.wikipedia.org/wiki/William_of_Soissons)
is said to have been the first to derive the principle of explosion. 
There is a simple logical proof of an arbitrary conclusion $Q$
from the two assumptions $P$ and $\neg P$.
For if we know $P$ then surely $P\lor Q$ follows by the meaning of or.
So either $P$ or $Q$ holds, but the former is impossible by $\neg P$.
Hence, we have derived $Q$.

Unfortunately, this argument cannot be carried out in a typical natural deduction calculus.
The proof turns out to rely on the principle of explosion itself, 
which is built into most systems, so the reasoning would be circular.
I think the informal version of the proof is pretty convincing, 
but we can look for other evidence. 
When we derive a contradiction in a sufficiently concrete situation, an explosion seems to happen naturally. 

### The explosion in arithmetic 

As we saw in the argument attributed to Russell, 1=0 in arithmetic setting 
allows you to derive other identities by adding or multiplying the two sides by a constant.
It's trivial to obtain $m=n$ for all pairs of numbers. 