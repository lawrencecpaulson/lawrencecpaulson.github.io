---
layout: post
title:  Contradictions and the Principle of Explosion
usemathjax: true 
tags: [logic, Bertrand Russell, philosophy]
---

That logic should be [free from contradiction](https://plato.stanford.edu/entries/contradiction/#) probably its most basic principle, 
dating back to Aristotle. As described [last time]({% post_url 2024-01-31-Russells_Paradox %}), 
the emergence of a contradiction in set theory – in the form of Russell's paradox – was catastrophic. Few question the claim that no statement can be both true and false 
at the same time.
But the law of contradiction is widely associated with something else, 
the [*principle of explosion*](https://plato.stanford.edu/entries/logic-paraconsistent/#BrieHistExContQuod):
*ex contradictione quodlibet*, a contradiction implies everything. 
This principle has been disputed. One can formulate predicate logic without it 
(it's called *minimal logic*).  
And allegedly a student challenged Bertrand Russell
by saying "suppose 1=0; prove that you are the Pope". 
Russell is said to have replied that if 1=0 then 2=1 and therefore 
the 2-element set containing himself and the Pope actually contains one element. 
It's an amusing tale, but is the argument rigorous? 

### Origins

A 12th century Parisian logician named 
[William of Soissons](https://en.wikipedia.org/wiki/William_of_Soissons)
is said to have been the first to derive the principle of explosion. 
There is a simple logical proof of an arbitrary conclusion $Q$
from the two assumptions $P$ and $\neg P$.
For if we know $P$ then surely $P\lor Q$ follows by the meaning of logical OR.
So either $P$ or $Q$ holds, but the former is impossible by $\neg P$.
Hence, we have derived $Q$.

Unfortunately, this argument cannot be carried out in a typical natural deduction calculus.
The proof turns out to rely on the principle of explosion itself, 
which is built into most formalisms: the reasoning would be circular.
I think the informal version of the proof is pretty convincing, 
but we can look for other evidence. 
(And yes, evidence is what we should be looking for when trying to justify a principle 
too fundamental to be proved.)
In many specific contexts, a contradicting fact leads to an explosion by calculation. 

### The explosion in arithmetic 

As we saw in the argument attributed to Russell, 1=0 in arithmetic setting 
allows you to derive other identities by adding or multiplying the two sides by a constant.
It's trivial to obtain $m=n$ for all pairs of numbers. 
Conversely, the assumption $m=n$ can be transformed by subtraction and division into 1=0.
On the other hand, it is possible postulate something like 5=0 
if the other axioms are weak enough, and then you have simply specified 
a version of modular arithmetic. 

### The explosion in the λ-calculus 

The λ-calculus is an extremely simple formalism in which a great many 
computational notions can be encoded.
Familiar data types such as the Booleans, natural numbers and integers, lists and trees 
(even infinite data structures) can be represented, as well as algorithms operating on them.
The standard representations of true and false are 
$\lambda x y.x$ and $\lambda x y.y$, respectively. 
So what happens if we are given that true equals false? Then
$M = (\lambda x y.x)MN = (\lambda x y.y)MN = N$. Therefore we can show $M=N$
for any two given λ-terms, $M$ and $N$.

### The explosion in axiomatic set theory 

Here things get a little more technical. And with all due respect to Bertrand Russell,  
he is not a set, and neither is the Pope. 
In set theory, 0 is the empty set and 1 is $\\{0\\}$, which implies $0\in 1$.
So 1=0 then we have big problems: $0\in 1$ is true but also false 
(because nothing can belong to the empty set).
And so, for any given set $A$, the set $\\{x\in A\mid 0\in 1\\}$ equals $A$
if we take $0\in 1$ to be true, but otherwise the resulting set is empty. 
It follows that $A$ equals the empty set for all $A$, so all sets are equal. 

### Final remarks

As promised, in specific formal systems, the principle of explosion arises all by itself. 
It doesn't have to be assumed. Taking it as a general logical principle 
is then simply a form of abstraction.  

[Paraconsistent logics](https://plato.stanford.edu/entries/logic-paraconsistent/) 
are formal systems in which the impact of a contradiction is contained. 
I can't comment on the value of such work to philosophy, 
but they have also been studied in the context of artificial intelligence. 
There, the point is that it's easy for the facts in an inexact real-world situation 
to be inconsistent, and you don't want everything to collapse. 
I would argue however that you should never be using formal logic 
to reason directly about real-world situations. 
And indeed, the symbolic/logical tendency that was so prominent in early AI work
has pretty much vanished in favour of techniques based on neural networks.
There, the problem doesn't arise because nothing is being proved,
but rather calculated statistically. 
