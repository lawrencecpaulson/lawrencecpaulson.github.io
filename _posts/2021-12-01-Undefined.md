---
layout: post
title:  "Undefined values, or what do we get when we divide by zero?"
usemathjax: true 
tags: logic descriptions
---

One perplexing issue, especially for newcomers to machine proof, is the question of undefined values: whether from division by zero or from a non-existent limit, integral or other sophisticated concept. This issue produces strong opinions and some proposed solutions are radical. But for many proof assistants the solution is basically "don't worry about it".

### Undefined values? We don't care!

Everybody knows that division by zero is undefined, but what does that mean? I had learnt that $0^0$ was also undefined. So I was shocked, when reading Donald Knuth's *The Art of Computer Programming*, that he was using $0^0=1$. Did that mean that his book was nonsensical? Of course it didn't: it meant that he chose a definition that simplified his work and that could not conflict with other literature because the convention was to give no meaning to $0^0$ at all. (And as we do more advanced mathematics, we frequently discover that authors are unable to agree on the precise definitions of fundamental concepts.) In the world of automated theorem proving, Boyer and Moore were similarly extending the domains of many of the primitive functions in their system to return some neutral value if applied outside their natural domain.

Division is the simplest example of this technique: we go ahead and define $x/0=0$. The point is that many division laws become unconditional, such as $(a/b)(c/d) = (ac)/(bd)$ and $(x+y)/z = x/z+y/z$. But there are notable exceptions: $x/x=1$ holds only if $x\not=0$. This approach has been adopted in numerous proof assistants including Isabelle/HOL and all those of the HOL family.

This definition provokes horrified reactions. You can however unclutch your pearls and consider that at worst, the division operator as defined here is not the usual division but is nevertheless perfectly well defined by case analysis. Any formal theorem whose statement involves the division operator can be interpreted in that light, and any theorem not involving division operator is safe: our weird division operator is no different from any other private definition might be made in order to facilitate the proof. To use logical terminology, this definition is *conservative*.

What do we do when no neutral value is available, as in the case of a [description operator]({% post_url 2021-11-10-Axiom_of_Choice %}) when the described object does not exist? In this case we simply say that the resulting value is unknown: it is literally undefined. Denote by $\alpha$ the natural number answering the description $\alpha<0$. As the natural numbers are nonnegative, the description is vacuous and $\alpha$ can be any natural number (if not for our formalism's type system, it could be anything at all). It still satisfies simple facts such as $\alpha=\alpha$ and $\alpha<\alpha+1$. It may be slightly surprising to discover that we get the same $\alpha$ from other impossible descriptions, because the formal predicate is the same in each case — everywhere false — and the description operator is extensional. So $\alpha$  is also equal to the smallest even prime number greater than 2 and the smallest exponent that is a counterexample to Fermat's Last Theorem.

Analysis introduces a number of operations can be undefined, such as limits, derivatives, integrals and measures. Under the don't care approach, each such operation must be formalised as a relation: for example, "$\sigma$ converges to $a$" as opposed to $\lim_{n\to\infty}\sigma_n = a$.
The more conventional operator form is derived from the relational form using a description, and $\lim_{n\to\infty}\sigma_n$ denotes an arbitrary value (it can be anything) unless the limit converges.

The don't care approach relies on case analysis, i.e. the [law of the excluded middle]({% post_url 2021-11-24-Intuitionism %}), which is not valid in constructive mathematics, and intuitionists will need to try something else.

### Avoiding undefined values through subtyping or dependent types

Another approach to division by zero is to specify its domain within its type, if your type system is rich enough. We could say that real division takes two arguments: a real number and a nonzero real number. A variation often found in formalisms based on the idea of propositions as types is to say that division takes *three* arguments: two reals *along with a proof* that the divisor is nonzero.

This idea was pioneered in de Bruijn's [AUTOMATH]({% post_url 2021-11-03-AUTOMATH %}), although he was not an intuitionist: it simply seemed to him a natural use of the power of his formalism. He quickly discovered the need for *irrelevance of proofs*: the value of $x/y$ should certainly not depend on the supplied proof that $y\not=0$; the fact alone must be enough. This is one reason why systems based on propositions as types generally go on to introduce a separate level where propositions are not types. This happened already with AUTOMATH by around 1970 and is true of present-day Coq and Lean.

A rather offbeat version of the same approach is found in the predicate subtyping of PVS, the [Prototype Verification System](http://pvs.csl.sri.com). PVS adopts neither intuitionistic logic nor propositions as types, but it has a sort of dependent type theory through its system of predicate subtyping. Any type can be constrained by a logical predicate to create a subtype of the element satisfying the given property, so we can have for example the type of nonzero real numbers. PVS remains a niche choice however. One unusual feature is that all specifications, including theorem statements, generate "type checking conditions" derived from predicate subtyping. These need to be proved as part of the overall verification process.

### Free logics (with a "defined" predicate)

A quite different approach is to use a *free logic*: a formalism where you can reason about definedness directly. An early example was published by Dana Scott in 1977 (reviewed [here](https://doi.org/10.2307/2274243)). In the 1990s, a proof assistant called [IMPS](https://github.com/theoremprover-museum/imps) was built, supporting its own free logic. While Scott's work was motivated by intuitionism (since the don't care approach requires the excluded middle), IMPS was motivated by the view that the notion of being defined was fundamental to mathematics.

In a free logic, you typically do not have $x=x$ unless you know that $x$ is defined. But then you do have $x\not=x$ when $x$ is undefined. To me this seems less natural than the don't care approach, where we always have $x=x$.

Free logics haven't caught on. It may simply be that people who really care about such things prefer dependent types, which can accomplish similar aims and more. It may also be that definedness is seldom an issue but a free logic puts it front and centre all the time.
Free logics generally do not introduce a constant `undefined` to designate ill-defined values, but such an approach is similar in spirit. It also has the same drawbacks.

One occasionally sees proposals to use a three valued logic. There you have a constant `undefined` even for truth values. The idea here must be to identify logical formulas with computable Boolean expressions, where $x=x$ is defined only if $x$ is. However, this identification doesn't make sense: mathematics and computation are different things. We would also be forced to give up classical logic without getting in return the cool technical properties of intuitionistic logic.

[*Postscript added 2022-05-14*: See also "[Division by zero in type theory: a FAQ](https://xenaproject.wordpress.com/2020/07/05/division-by-zero-in-type-theory-a-faq/)" on the Xena blog.
And don't overlook the comments!]
