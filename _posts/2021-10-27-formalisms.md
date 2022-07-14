---
layout: post
title:  "On logical formalisms"
usemathjax: true 
tags: [general, logic, Russell, Ernst Zermelo, de Bruijn]
---

Looking at the [previous example]({% post_url 2021-10-13-Fib-example %}), on Fibonacci numbers, you may be wondering, *how we can be sure that a machine proof corresponds to actual mathematics?* This question raises complex issues in the foundations of mathematics and logic.

Logic was already being debated by the ancient Greeks. It was concerned with all matters relating to language, observations and thought. Only in the 19th century did modern deductive logic start to emerge. But the meanings even of the logical signs — negation, conjunction, disjunction, implication, all and exists — turned out to contain hidden subtleties. Early in the 20th century, [Russell's paradox](https://plato.stanford.edu/entries/russell-paradox/) overturned prevailing ideas about the nature of sets. [It was unfortunate.](https://existentialcomics.com/comic/416)

Russell (with Whitehead) went on to formalise a substantial portion of mathematics in a [language](https://plato.stanford.edu/entries/pm-notation/) of their own devising, in their multi-volume [*Principia Mathematica*](https://www.cambridge.org/gb/academic/subjects/mathematics/logic-categories-and-sets/principia-mathematica-56-2nd-edition?format=PB). Although they needed 362 pages to prove 1+1=2, their work heavily influenced later formalisms. [*Higher-order logic*](https://plato.stanford.edu/entries/logic-higher-order/) is a direct descendant, greatly simplified, of their ramified theory of types. First-order logic, thanks to its simpler metatheory, gradually [came to dominance](https://plato.stanford.edu/entries/logic-firstorder-emergence/); combined with [Zermelo's axioms](https://plato.stanford.edu/entries/zermelo-set-theory/), it proved to be an adequate foundation for set theory and therefore for mathematics in general.

But most working mathematicians never imagine their work to have anything to do with set theory. Encoding mathematical objects as sets is no concern of theirs. A few rebelled openly against the doctrines of set theory, notably [N. G. de Bruijn](https://mathshistory.st-andrews.ac.uk/Biographies/De_Bruijn/): 

> I believe that thinking in terms of *types* and *typed sets* is much more natural than appealing to untyped set theory. ... In our mathematical culture we have learned to keep things apart. If we have a rational number and a set of points in the Euclidean plane, we cannot even imagine what it means to form the intersection. The idea that both might have been coded in ZF with a coding so crazy that the intersection is *not empty* seems to be ridiculous. If we think of a set of objects, we usually think of collecting things of a certain type, and set-theoretical operations are to be carried out inside that type. Some types might be considered as subtypes of some other types, but in other cases two different types have nothing to do with each other. That does not mean that their intersection is empty, but that it would be insane to even *talk* about the intersection. 
> [In ["On the roles of types in mathematics"](https://research.tue.nl/en/publications/on-the-roles-of-types-in-mathematics)], 1995.

Formalised mathematics is almost invariably done in the presence of types, but there are huge differences in the nature of those types and even in how logic itself behaves. 
The relationship between any formalism and "actual mathematics" is inherently impossible to prove: the latter is not precisely defined. The introduction of computers and software can only muddy the waters further. Ultimately, confidence in an automated formalism can come only with use, as we observe what it lets us prove and what it forbids.
