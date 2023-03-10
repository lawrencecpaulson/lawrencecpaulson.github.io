---
layout: post
title:  "The semantics of a simple functional language"
usemathjax: true
tags: [examples, Isabelle, inductive definitions]
---

The simplest way to precisely specify the meanings of programming language expressions
is through an [operational semantics](https://en.wikipedia.org/wiki/Operational_semantics).
Such a definition consists of a set of what look like the inference rules
of a logic, stating the conditions under which a given expression
can be reduced to a value, or at least evaluated one step more.
Formally, this sort of specification is an *inductive definition*,
equipped with an induction principle for proving that a property
holds for all executions.
Such proofs are conceptually trivial—they involve checking
that the property holds
initially and that it is preserved 
by each execution step—but are extremely tedious to write out by hand.
Fortunately, they are often trivial with the help of a little automation.
Let's prove a [Church--Rosser property](https://en.wikipedia.org/wiki/Church–Rosser_theorem):
that expression evaluation always leads to a unique final result.

### A simple functional language

Our language is insufficient to write an airline reservation system—it isn't even
Turing-complete—but it is sufficient to illustrate some of the core themes of operational semantics.

Let's begin with the syntax. An expression can be a Boolean
(true or false), or a natural number given by zero or successor,
or a conditional expression, or an equality test:

<pre class="source">
<span class="keyword1 command">datatype</span> exp <span class="main">=</span> T <span class="main">|</span> F <span class="main">|</span> Zero <span class="main">|</span> Succ <span class="quoted">exp</span> <span class="main">|</span> IF <span class="quoted">exp</span> <span class="quoted">exp</span> <span class="quoted">exp</span> <span class="main">|</span> EQ <span class="quoted">exp</span> <span class="quoted">exp</span>
</pre>

Next we define the operational semantics itself, which takes the form
of a reduction relation (⇛). We use an Isabelle/HOL inductive definition.
The first two rules cover the true and false cases of a conditional expression,
while the third case takes care of a single reduction within the condition.
The fourth rule covers the evaluation of the argument of `Succ`.
So this is a [small-step semantics](https://en.wikipedia.org/wiki/Operational_semantics#Small-step_semantics); 
in a big-step semantics, every rule would be formulated
to deliver the final result.

<pre class="source">
<span class="keyword1 command">inductive</span> <span class="entity">Eval</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>exp</span> <span class="main">⇒</span> exp</span> <span class="main">⇒</span> bool<span>"</span> <span class="main">(</span><span class="keyword2 keyword">infix</span> <span class="quoted"><span>"</span><span class="keyword1">⇛</span><span>"</span></span> 50<span class="main">)</span> <span class="keyword2 keyword">where</span><span>
    </span>IF_T<span class="main">:</span>    <span class="quoted"><span class="quoted"><span>"</span>IF</span> T</span> <span class="free bound entity">x</span> <span class="free bound entity">y</span> <span class="main free">⇛</span> <span class="free bound entity">x</span><span>"</span><span>
  </span><span class="main">|</span> IF_F<span class="main">:</span>    <span class="quoted"><span class="quoted"><span>"</span>IF</span> F</span> <span class="free bound entity">x</span> <span class="free bound entity">y</span> <span class="main free">⇛</span> <span class="free bound entity">y</span><span>"</span><span>
  </span><span class="main">|</span> IF_Eval<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free bound entity">p</span> <span class="main free">⇛</span> <span class="free bound entity">q</span> <span class="main">⟹</span> IF</span> <span class="free bound entity">p</span> <span class="free bound entity">x</span> <span class="free bound entity">y</span> <span class="main free">⇛</span> IF</span> <span class="free bound entity">q</span> <span class="free bound entity">x</span> <span class="free bound entity">y</span><span>"</span><span>
  </span><span class="main">|</span> Succ_Eval<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free bound entity">x</span> <span class="main free">⇛</span> <span class="free bound entity">y</span> <span class="main">⟹</span> Succ</span> <span class="free bound entity">x</span> <span class="main free">⇛</span> Succ</span> <span class="free bound entity">y</span><span>"</span><span>
  </span><span class="main">|</span> EQ_same<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>EQ</span> <span class="free bound entity">x</span> <span class="free bound entity">x</span> <span class="main free">⇛</span> T</span><span>"</span><span>
  </span><span class="main">|</span> EQ_S0<span class="main">:</span>   <span class="quoted"><span class="quoted"><span>"</span>EQ</span> <span class="main">(</span>Succ</span> <span class="free bound entity">x</span><span class="main">)</span> Zero <span class="main free">⇛</span> F<span>"</span><span>
  </span><span class="main">|</span> EQ_0S<span class="main">:</span>   <span class="quoted"><span class="quoted"><span>"</span>EQ</span> Zero</span> <span class="main">(</span>Succ <span class="free bound entity">y</span><span class="main">)</span> <span class="main free">⇛</span> F<span>"</span><span>
  </span><span class="main">|</span> EQ_SS<span class="main">:</span>   <span class="quoted"><span class="quoted"><span>"</span>EQ</span> <span class="main">(</span>Succ</span> <span class="free bound entity">x</span><span class="main">)</span> <span class="main">(</span>Succ <span class="free bound entity">y</span><span class="main">)</span> <span class="main free">⇛</span> EQ <span class="free bound entity">x</span> <span class="free bound entity">y</span><span>"</span><span>
  </span><span class="main">|</span> EQ_Eval1<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free bound entity">x</span> <span class="main free">⇛</span> <span class="free bound entity">z</span> <span class="main">⟹</span> EQ</span> <span class="free bound entity">x</span> <span class="free bound entity">y</span> <span class="main free">⇛</span> EQ</span> <span class="free bound entity">z</span> <span class="free bound entity">y</span><span>"</span><span>
  </span><span class="main">|</span> EQ_Eval2<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free bound entity">y</span> <span class="main free">⇛</span> <span class="free bound entity">z</span> <span class="main">⟹</span> EQ</span> <span class="free bound entity">x</span> <span class="free bound entity">y</span> <span class="main free">⇛</span> EQ</span> <span class="free bound entity">x</span> <span class="free bound entity">z</span><span>"</span>
</pre>

The remaining six rules concern the evaluation of equality tests.
I specifically designed them to be messy.

### Rule inversion

The language admits nonsensical terms such as `Succ T`, which cannot be reduced to anything.
How do we know that? Intuitively, it's because there is only one rule for evaluating`Succ`; 
that rule evaluates the argument, and there is no rule for evaluating `T`.
This straightforward reasoning can fortunately be automated.
The following declarations inform Isabelle's simplifier about the possibilities of
various reductions occurring. In particular, the first three
generate theorems stating that the quoted reductions are impossible.
In other cases, the resulting theorems state conditions under which the reduction can take place,
 e.g.

> `(Succ ?x ⇛ ?z) = (∃y. ?z = Succ y ∧ ?x ⇛ y)`

<pre class="source">
<span class="keyword1 command">inductive_simps</span> T_simp <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>T</span> <span class="main">⇛</span></span> <span class="free">z</span><span>"</span><span>
</span><span class="keyword1 command">inductive_simps</span> F_simp <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>F</span> <span class="main">⇛</span></span> <span class="free">z</span><span>"</span><span>
</span><span class="keyword1 command">inductive_simps</span> Zero_simp <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>Zero</span> <span class="main">⇛</span></span> <span class="free">z</span><span>"</span><span>
</span><span class="keyword1 command">inductive_simps</span> Succ_simp <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>Succ</span> <span class="free">x</span> <span class="main">⇛</span></span> <span class="free">z</span><span>"</span><span>
</span><span class="keyword1 command">inductive_simps</span> IF_simp <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>IF</span> <span class="free">p</span> <span class="free">x</span> <span class="free">y</span> <span class="main">⇛</span></span>  <span class="free">z</span><span>"</span><span>
</span><span class="keyword1 command">inductive_simps</span> EQ_simp <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>EQ</span> <span class="free">x</span> <span class="free">y</span> <span class="main">⇛</span></span> <span class="free">z</span><span>"</span>
</pre>

Such declarations are useful in any inductive definition where the conclusions of the rules
allow most of the cases to be excluded on syntactic grounds.
If your proofs seem to require a lot of explicit case analysis, 
see whether this sort of declaration could help you.

### Types and type preservation

Our language has Booleans and natural numbers, so let's define the corresponding type system.
(It will be simpler than Martin-Löf type theory.)

<pre class="source">
<span class="keyword1 command">datatype</span> tp <span class="main">=</span> bool <span class="main">|</span> num
</pre>

The great thing about operational semantics is its flexibility.
Above, we defined the evaluation of expressions, which is their dynamic behaviour;
now we can define their typing relation, which is static behaviour.
The same techniques work for both.

True and false have the Boolean type, while zero is a number.
`Succ` yields a number if its argument does.
For conditional expressions and equality, the use of types has to be consistent.

<pre class="source">
<span class="keyword1 command">inductive</span> <span class="entity">TP</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>exp</span> <span class="main">⇒</span> tp</span> <span class="main">⇒</span> bool<span>"</span> <span class="keyword2 keyword">where</span><span>
  </span>T<span class="main">:</span>    <span class="quoted"><span class="quoted"><span>"</span><span class="free">TP</span> T</span> bool</span><span>"</span><span>
</span><span class="main">|</span> F<span class="main">:</span>    <span class="quoted"><span class="quoted"><span>"</span><span class="free">TP</span> F</span> bool</span><span>"</span><span>
</span><span class="main">|</span> Zero<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">TP</span> Zero</span> num</span><span>"</span><span>
</span><span class="main">|</span> IF<span class="main">:</span>   <span class="quoted"><span class="quoted"><span>"</span><span class="main">⟦</span><span class="free">TP</span> <span class="free bound entity">p</span> bool</span><span class="main">;</span> <span class="free">TP</span> <span class="free bound entity">x</span> <span class="free bound entity">t</span><span class="main">;</span> <span class="free">TP</span> <span class="free bound entity">y</span> <span class="free bound entity">t</span><span class="main">⟧</span> <span class="main">⟹</span> <span class="free">TP</span> <span class="main">(</span>IF</span> <span class="free bound entity">p</span> <span class="free bound entity">x</span> <span class="free bound entity">y</span><span class="main">)</span> <span class="free bound entity">t</span><span>"</span><span>
</span><span class="main">|</span> Succ<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">TP</span> <span class="free bound entity">x</span> num</span> <span class="main">⟹</span> <span class="free">TP</span> <span class="main">(</span>Succ</span> <span class="free bound entity">x</span><span class="main">)</span> num<span>"</span><span>
</span><span class="main">|</span> EQ<span class="main">:</span>   <span class="quoted"><span class="quoted"><span>"</span><span class="main">⟦</span><span class="free">TP</span> <span class="free bound entity">x</span> <span class="free bound entity">t</span><span class="main">;</span> <span class="free">TP</span> <span class="free bound entity">y</span> <span class="free bound entity">t</span><span class="main">⟧</span> <span class="main">⟹</span> <span class="free">TP</span> <span class="main">(</span>EQ</span> <span class="free bound entity">x</span> <span class="free bound entity">y</span><span class="main">)</span> bool</span><span>"</span>
</pre>

Rule inversion for the above lets us reason easility about
the type-checking possibilities for expressions.

<pre class="source">
<span class="keyword1 command">inductive_simps</span> TP_IF <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>TP</span> <span class="main">(</span>IF</span> <span class="free">p</span> <span class="free">x</span> <span class="free">y</span><span class="main">)</span> <span class="free">t</span><span>"</span><span>
</span><span class="keyword1 command">inductive_simps</span> TP_Succ <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>TP</span> <span class="main">(</span>Succ</span> <span class="free">x</span><span class="main">)</span> <span class="free">t</span><span>"</span><span>
</span><span class="keyword1 command">inductive_simps</span> TP_EQ <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>TP</span> <span class="main">(</span>EQ</span> <span class="free">x</span> <span class="free">y</span><span class="main">)</span> <span class="free">t</span><span>"</span>
</pre>

[*Type preservation*](https://en.wikipedia.org/wiki/Subject_reduction) 
claims that the evaluation of an expression does not change its type.
Formally, we state that if `x ⇛ y` and `x` has some type `T`, then `y` will have the same type.
Induction on the assumption `x ⇛ y` produces 10 gruesome-looking subgoals:

>  `1. ⋀x y t. TP (IF T x y) t ⟹ TP x t`

>  `2. ⋀x y t. TP (IF F x y) t ⟹ TP y t`

>  `3. ⋀p q x y t. ⟦p ⇛ q; ⋀t. TP p t ⟹ TP q t; TP (IF p x y) t⟧ ⟹ TP (IF q x y) t`

>  `4. ⋀x y t. ⟦x ⇛ y; ⋀t. TP x t ⟹ TP y t; TP (Succ x) t⟧ ⟹ TP (Succ y) t`

>  `5. ⋀x t. TP (EQ x x) t ⟹ TP T t`

>  `6. ⋀x t. TP (EQ (Succ x) Zero) t ⟹ TP F t`

>  `7. ⋀y t. TP (EQ Zero (Succ y)) t ⟹ TP F t`

>  `8. ⋀x y t. TP (EQ (Succ x) (Succ y)) t ⟹ TP (EQ x y) t`

>  `9. ⋀x z y t. ⟦x ⇛ z; ⋀t. TP x t ⟹ TP z t; TP (EQ x y) t⟧ ⟹ TP (EQ z y) t`

>  `10. ⋀y z x t. ⟦y ⇛ z; ⋀t. TP y t ⟹ TP z t; TP (EQ x y) t⟧ ⟹ TP (EQ x z) t`

Some courses in operational semantics expect students to be able to carry out 
such proofs by hand. But even writing out the subgoals perfectly by hand is next to impossible.
Fortunately they are trivial to prove, with the help of rule inversion.
The Isabelle/HOL proof takes a single line, which executes instantly:

<pre class="source">
<span class="keyword1 command">proposition</span> type_preservation<span class="main">:</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">⇛</span></span> <span class="free">y</span><span>"</span></span> <span class="quoted"><span class="quoted"><span>"</span>TP</span> <span class="free">x</span> <span class="free">t</span><span>"</span></span> <span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span>TP</span> <span class="free">y</span> <span class="free">t</span><span>"</span></span><span>
  </span><span class="keyword1 command">using</span> assms<span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">induction</span> <span class="quoted free">x</span> <span class="quoted free">y</span> <span class="quasi_keyword">arbitrary</span><span class="main main">:</span> <span class="quoted free">t</span> <span class="quasi_keyword">rule</span><span class="main main">:</span> Eval.induct<span class="main">)</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> TP.intros<span class="main">)</span>
</pre>

A couple of fine points in the proof:

* designating the variable `t` as arbitrary allows for the type of subexpressions to differ from the type of the top expression
* you can give two proof methods to the <span class="keyword1 command">by</span> command

### Values and value preservation

We can interpret the operators of our simple language in terms of the natural numbers.
In particular, true and false denote 1 and zero, respectively. We can also give the semantics
of conditional expressions and equality tests. 
This is a trivial example of a [denotational semantics](https://en.wikipedia.org/wiki/Denotational_semantics).

<pre class="source">
<span class="keyword1 command">fun</span> <span class="entity">evl</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>exp</span> <span class="main">⇒</span> nat</span><span>"</span><span>
  </span><span class="keyword2 keyword">where</span><span>
    </span><span class="quoted"><span class="quoted"><span>"</span><span class="free">evl</span> T</span> <span class="main">=</span></span> <span class="main">1</span><span>"</span><span>
  </span><span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">evl</span> F</span> <span class="main">=</span></span> <span class="main">0</span><span>"</span><span>
  </span><span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">evl</span> Zero</span> <span class="main">=</span></span> <span class="main">0</span><span>"</span><span>
  </span><span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">evl</span> <span class="main">(</span>Succ</span> <span class="free bound entity">x</span><span class="main">)</span> <span class="main">=</span></span> <span class="free">evl</span> <span class="free bound entity">x</span> <span class="main">+</span> <span class="main">1</span><span>"</span><span>
  </span><span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">evl</span> <span class="main">(</span>IF</span> <span class="free bound entity">x</span> <span class="free bound entity">y</span> <span class="free bound entity">z</span><span class="main">)</span> <span class="main">=</span></span> <span class="main">(</span><span class="keyword1">if</span> <span class="free">evl</span> <span class="free bound entity">x</span> <span class="main">=</span> <span class="main">1</span> <span class="keyword1">then</span> <span class="free">evl</span> <span class="free bound entity">y</span> <span class="keyword1">else</span> <span class="free">evl</span> <span class="free bound entity">z</span><span class="main">)</span><span>"</span><span>
  </span><span class="main">|</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">evl</span> <span class="main">(</span>EQ</span> <span class="free bound entity">x</span> <span class="free bound entity">y</span><span class="main">)</span> <span class="main">=</span></span> <span class="main">(</span><span class="keyword1">if</span> <span class="free">evl</span> <span class="free bound entity">x</span> <span class="main">=</span> <span class="free">evl</span> <span class="free bound entity">y</span> <span class="keyword1">then</span> <span class="main">1</span> <span class="keyword1">else</span> <span class="main">0</span><span class="main">)</span><span>"</span>
</pre>

Value preservation is the claim that the evaluation of an expression does not change its value.

<pre class="source">
<span class="keyword1 command">proposition</span> value_preservation<span class="main">:</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">⇛</span></span> <span class="free">y</span><span>"</span></span> <span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span>evl</span> <span class="free">x</span> <span class="main">=</span></span> evl <span class="free">y</span><span>"</span><span>
  </span><span class="keyword1 command">using</span> assms <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">induction</span> <span class="quoted free">x</span> <span class="quoted free">y</span><span class="main keyword3">;</span> <span class="operator">force</span><span class="main">)</span>
</pre>

Here we relate types and values. The value of a Boolean expression is less than 2.

<pre class="source">
<span class="keyword1 command">lemma</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span>TP</span> <span class="free">x</span> <span class="free">t</span><span>"</span></span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">t</span> <span class="main">=</span></span> bool</span><span>"</span> <span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span>evl</span> <span class="free">x</span> <span class="main">&lt;</span></span> <span class="numeral">2</span><span>"</span><span>
  </span><span class="keyword1 command">using</span> assms <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">induction</span> <span class="quoted free">x</span> <span class="quoted free">t</span><span class="main keyword3">;</span> <span class="operator">force</span><span class="main">)</span>
</pre>

### Proving a Church--Rosser property

The Church--Rosser theorem concerns the λ-calculus and in effect states that multiple
evaluation routes cannot yield multiple final values. It's necessary because
in the λ-calculus it's possible to reduce some expressions in more than one way.
Our language has the same problem. For example, four different rules are applicable
to some expressions of the form `EQ (Succ x) (Succ y)`.

Some care is needed when expressing a Church--Rosser property.
The following does not hold:

<pre class="source">
<span class="keyword1 command">lemma</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">⇛</span></span> <span class="free">y</span><span>"</span></span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">⇛</span></span> <span class="free">z</span><span>"</span></span> <span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">∃</span></span><span class="bound">u</span><span class="main">.</span></span> <span class="free">y</span> <span class="main">⇛</span> <span class="bound">u</span> <span class="main">∧</span> <span class="free">z</span> <span class="main">⇛</span> <span class="bound">u</span><span>"</span><span>
  </span><span class="keyword1 command">nitpick</span>
</pre>

The counterexample returned by <span class="keyword1 command">nitpick</span> is `IF F F F`.
The property fails simply because `F` cannot reduce, which is not really what we are worried about here.
To express Church--Rosser properly, we need the transitive closure of the reduction relation.
(We could also have used the built-in transitive closure operator.)

<pre class="source">
<span class="keyword1 command">inductive</span> <span class="entity">EvalStar</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>exp</span> <span class="main">⇒</span> exp</span> <span class="main">⇒</span> bool<span>"</span> <span class="main">(</span><span class="keyword2 keyword">infix</span> <span class="quoted"><span>"</span><span class="keyword1">⇛*</span><span>"</span></span> 50<span class="main">)</span> <span class="keyword2 keyword">where</span><span>
    </span>Id<span class="main">:</span> <span class="quoted quoted"><span>"</span><span class="free bound entity">x</span> <span class="main free">⇛*</span> <span class="free bound entity">x</span><span>"</span></span><span>
  </span><span class="main">|</span> Step<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free bound entity">x</span> <span class="main">⇛</span></span> <span class="free bound entity">y</span> <span class="main">⟹</span> <span class="free bound entity">y</span> <span class="main free">⇛*</span> <span class="free bound entity">z</span> <span class="main">⟹</span> <span class="free bound entity">x</span> <span class="main free">⇛*</span> <span class="free bound entity">z</span><span>"</span></span>
</pre>

The following lemma is just a warmup.
We show that the type is preserved even over a string of evaluation steps.

<pre class="source">
<span class="keyword1 command">proposition</span> type_preservation_Star<span class="main">:</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">⇛*</span></span> <span class="free">y</span><span>"</span></span> <span class="quoted"><span class="quoted"><span>"</span>TP</span> <span class="free">x</span> <span class="free">t</span><span>"</span></span> <span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span>TP</span> <span class="free">y</span> <span class="free">t</span><span>"</span></span><span>
  </span><span class="keyword1 command">using</span> assms<span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">induction</span> <span class="quoted free">x</span> <span class="quoted free">y</span><span class="main">)</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">simp</span><span class="main main">:</span> type_preservation<span class="main">)</span>
</pre>

On the other hand, the following four lemmas are essential.
Each of them transforms a string of evaluation steps into the analogous string of steps
within an argument of some function.
All these proofs are trivial inductions.

<pre class="source">
<span class="keyword1 command">lemma</span> Succ_EvalStar<span class="main">:</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">⇛*</span></span> <span class="free">y</span><span>"</span></span> <span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span>Succ</span> <span class="free">x</span> <span class="main">⇛*</span></span> Succ <span class="free">y</span><span>"</span><span>
  </span><span class="keyword1 command">using</span> assms <span class="keyword1 command">by</span> <span class="operator">induction</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">intro</span><span class="main main">:</span> Succ_Eval EvalStar.intros<span class="main">)</span>
</pre>

<pre class="source">
<span class="keyword1 command">lemma</span> IF_EvalStar<span class="main">:</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">p</span> <span class="main">⇛*</span></span> <span class="free">q</span><span>"</span></span> <span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span>IF</span> <span class="free">p</span> <span class="free">x</span> <span class="free">y</span> <span class="main">⇛*</span></span> IF <span class="free">q</span> <span class="free">x</span> <span class="free">y</span><span>"</span><span>
  </span><span class="keyword1 command">using</span> assms <span class="keyword1 command">by</span> <span class="operator">induction</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">intro</span><span class="main main">:</span> IF_Eval EvalStar.intros<span class="main">)</span>
</pre>

<pre class="source">
<span class="keyword1 command">lemma</span> EQ_EvalStar1<span class="main">:</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">⇛*</span></span> <span class="free">z</span><span>"</span></span> <span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span>EQ</span> <span class="free">x</span> <span class="free">y</span> <span class="main">⇛*</span></span> EQ <span class="free">z</span> <span class="free">y</span><span>"</span><span>
  </span><span class="keyword1 command">using</span> assms <span class="keyword1 command">by</span> <span class="operator">induction</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">intro</span><span class="main main">:</span> EQ_Eval1 EvalStar.intros<span class="main">)</span>
</pre>

<pre class="source">
<span class="keyword1 command">lemma</span> EQ_EvalStar2<span class="main">:</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">y</span> <span class="main">⇛*</span></span> <span class="free">z</span><span>"</span></span> <span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span>EQ</span> <span class="free">x</span> <span class="free">y</span> <span class="main">⇛*</span></span> EQ <span class="free">x</span> <span class="free">z</span> <span>"</span><span>
  </span><span class="keyword1 command">using</span> assms <span class="keyword1 command">by</span> <span class="operator">induction</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">intro</span><span class="main main">:</span> EQ_Eval2 EvalStar.intros<span class="main">)</span>
</pre>

Finally we reach our destination. The diamond property is not the full
Church--Rosser claim, but it captures the main point:
that if some `x` can be reduced either to `y` or `z` in a single step,
then the evaluation strings can be extended to reunite at some common `u`.

<pre class="source">
<span class="keyword1 command">proposition</span> diamond<span class="main">:</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">⇛</span></span> <span class="free">y</span><span>"</span></span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">⇛</span></span> <span class="free">z</span><span>"</span></span> <span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">∃</span></span><span class="bound">u</span><span class="main">.</span></span> <span class="free">y</span> <span class="main">⇛*</span> <span class="bound">u</span> <span class="main">∧</span> <span class="free">z</span> <span class="main">⇛*</span> <span class="bound">u</span><span>"</span><span>
  </span><span class="keyword1 command">using</span> assms<span>
</span><span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">induction</span> <span class="quoted free">x</span> <span class="quoted free">y</span> <span class="quasi_keyword">arbitrary</span><span class="main main">:</span> <span class="quoted free">z</span><span class="main">)</span><span>
  </span><span class="keyword3 command">case</span> <span class="main">(</span>IF_Eval <span class="skolem">p</span> <span class="skolem">q</span> <span class="skolem">x</span> <span class="skolem">y</span><span class="main">)</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="var quoted var">?case</span><span>
    </span><span class="keyword1 command">by</span> <span class="operator">simp</span><span class="main keyword3">;</span> <span class="operator">meson</span> F_simp IF_EvalStar T_simp<span class="main">)</span><span>
</span><span class="keyword1 command">next</span><span>
  </span><span class="keyword3 command">case</span> <span class="main">(</span>EQ_SS <span class="skolem">x</span> <span class="skolem">y</span><span class="main">)</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="var quoted var">?case</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span><span class="main keyword3">;</span> <span class="operator">meson</span> Eval.intros EvalStar.intros<span class="main">)</span><span>
</span><span class="keyword1 command">next</span><span>
  </span><span class="keyword3 command">case</span> <span class="main">(</span>EQ_Eval1 <span class="skolem">x</span> <span class="skolem">u</span> <span class="skolem">y</span><span class="main">)</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="var quoted var">?case</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">auto</span><span class="main keyword3">;</span> <span class="operator">meson</span> EQ_EvalStar1 Eval.intros EvalStar.intros<span class="main">)</span><span class="main keyword3">+</span><span>
</span><span class="keyword1 command">next</span><span>
    </span><span class="keyword3 command">case</span> <span class="main">(</span>EQ_Eval2 <span class="skolem">y</span> <span class="skolem">u</span> <span class="skolem">x</span><span class="main">)</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="var quoted var">?case</span><span>
    </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">auto</span><span class="main keyword3">;</span> <span class="operator">meson</span> EQ_EvalStar2 Eval.intros EvalStar.intros<span class="main">)</span><span class="main keyword3">+</span><span>
</span><span class="keyword1 command">qed</span> <span class="main">(</span><span class="operator">force</span> <span class="quasi_keyword">intro</span><span class="main main">:</span> Succ_EvalStar Eval.intros EvalStar.intros<span class="main">)</span><span class="main keyword3">+</span>
</pre>

Finally, a nontrivial proof! I've tried to make it neat, but it's 
a mess. You could download the
[Isabelle theory file](/Isabelle-Examples/Fun_Semantics.thy)
and see if you can do it better.


### Postscript

There is a myth that you need dependent types to do semantics.
This is ridiculous; the heyday of denotational semantics was the 1970s,
before most people had even heard of dependent types.
Tobias Nipkow and Gerwin Klein have written an entire book,
[*Concrete Semantics*](http://www.concrete-semantics.org),
on how to do semantics in Isabelle/HOL. It has many advanced examples.
You can either [buy a copy](https://link.springer.com/book/10.1007/978-3-319-10542-0) 
or download it for free.

This is another example from my old MPhil course, [Interactive Formal Verification](https://www.cl.cam.ac.uk/teaching/2122/L21/).
