---
layout: post
title:  The mysteries and frustrations of numerical proofs
usemathjax: true 
tags: [general, Isabelle, type classes, newbies]
---

Sometimes the smallest details are the worst. What do we mean by 2+2=4? There are many different kinds of numbers: integers, rationals, reals, etc. It should not affect the answer, and mathematical writing takes advantage of that fact, but formalised mathematics has to be unambiguous. 
A further complication is that the various kinds of numbers are used in distinctive ways, e.g. recursion is only for the natural numbers. 
How do we reconcile the zero-versus-successor conception of the naturals 
with the need to work with decimal constants or large integers? Let's see how it's done in Isabelle/HOL.

### Simple arithmetic with symbolic binary notation

If you ask Isabelle to prove 2+2=4, thankfully it will do it. 

<pre class="source">
<span class="keyword1 command">lemma</span> <span class="quoted"><span class="quoted"><span>"</span><span class="numeral">2</span><span class="main">+</span></span><span class="numeral">2</span><span class="main">=</span></span><span class="numeral">4</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="operator">auto</span>
</pre>

What kind of numbers are we talking about here? [Remember]({% post_url 2022-05-11-jEdit-tricks %}), you can inspect any Isabelle syntactic element using CTRL-hover (CMD-hover on a Mac). 
Hover over any of the numbers and Isabelle will display the type `'a`. Hover over that type variable to inspect its type class, which is `numeral`. 
This is the class of all types for which numerals work, and Isabelle knows how to add numerals. It works just as well for large numerals, say to calculate 123456789 + 987654321 = 1111111110. But such super abstract calculations do not work for 2*3=6: this time, if we inspect the type it is again `'a`, but the type class is `{times,numeral}.` 
That means Isabelle has detected that multiplication is involved but nothing more: it does not assume any ring laws. 
Another example that fails is 0+2=2; here the relevant type class is `{zero,numeral}`, which does not include the identity law for 0. 

<pre class="source">
<span class="keyword1 command">lemma</span> <span class="quoted"><span class="quoted"><span>"</span><span class="numeral">2</span><span class="main">*</span></span><span class="numeral">3</span><span class="main">=</span></span><span class="numeral">6</span><span>"</span><span>
  </span><span class="keyword1 command">oops</span>

<span class="keyword1 command">lemma</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">0</span></span><span class="main">+</span></span><span class="numeral">2</span><span class="main">=</span><span class="numeral">2</span><span>"</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">1</span></span><span class="main">*</span></span><span class="numeral">3</span><span class="main">=</span><span class="numeral">3</span><span>"</span><span>
  </span><span class="keyword1 command">oops</span>
</pre>

The way to avoid all such problems is simply to ensure that the type is constrained somehow. In most cases, the use of a variable declared previously will be enough. Sometimes a variable declaration will need a type constraint: `fix x :: real`. But you can always write an explicit type constraint within an expression, as in 123456789 * (987654321::int). 
Isabelle will happily simplify that to 121932631112635269.
Also, the function `Suc` implies type `nat`.

<pre class="source">
<span class="keyword1 command">lemma</span> <span class="quoted"><span class="quoted"><span>"</span><span class="numeral">123456789</span> <span class="main">*</span></span> <span class="main">(</span><span class="numeral">987654321</span><span class="main">::</span>int</span><span class="main">)</span> <span class="main">=</span> <span class="numeral">121932631112635269</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="operator">simp</span>

<span class="keyword1 command">lemma</span> <span class="quoted"><span class="quoted"><span>"</span>Suc</span> <span class="main">(</span>Suc</span> <span class="main">0</span><span class="main">)</span> <span class="main">*</span> <span class="free">n</span> <span class="main">=</span> <span class="free">n</span><span class="main">*</span><span class="numeral">2</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="operator">simp</span>
</pre>

Isabelle can perform arithmetic on constants efficiently thanks to its internal representation: a form of symbolic binary notation. Positional notation is necessary to handle large integers, binary (as opposed to say decimal) makes the formal theory of arithmetic compact. 
Already in the 1990s I had devised a symbolic representation of numerals that worked well; the one used today is a clever refinement of that, but I have no idea whom to credit. *If anybody is aware of a publication on this topic, I would be happy to cite it here.*
The original version is still used for Isabelle/ZF; it is a two's complement format, eliminating the ugly case-analyses associated with signed arithmetic.

Isabelle/HOL has over the years accumulated some capabilities that are cool although perhaps of little practical value. For example, `root 100 1267650600228229401496703205376` is quickly and automatically simplified to 2.
    
### Unary notation and the horror of 1  

The idea of representing natural numbers using the two symbols `0` and `Suc` (for successor) comes from logic. Unary notation, e.g. `Suc(Suc(Suc 0))` for 3, is convenient for expressing mathematical induction rules symbolically and when defining the concept of a primitive recursive function.
It is not convenient for anything else, taking exponentially more space to represent an integer compared with positional notation.
So it is surprising that one of the most prominent proof assistants uses it even for large integers!

When working with natural numbers (type `nat` in Isabelle/HOL), we sometimes have to translate between unary and binary notation. In particular, we may occasionally need to transform something like 100 into `Suc 99`. If one is prepared to write the transformation as an explicit proof step using the keyword **have**, then Isabelle can prove such identities automatically. Some lower level tricks are available to do the transformation more compactly.
Simplest is to rewrite with `eval_nat_numeral`:

<pre class="source">
<span class="keyword1 command">lemma</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span><span class="main">^</span></span><span class="numeral">5</span> <span class="main">=</span></span> <span class="free">x</span><span class="main">*</span><span class="free">x</span><span class="main">*</span><span class="free">x</span><span class="main">*</span><span class="free">x</span><span class="main">*</span><span class="main">(</span><span class="free">x</span><span class="main">::</span>real<span class="main">)</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> eval_nat_numeral<span class="main">)</span>
</pre>

Please note: 0 and 1 are constants, overloaded on all numeric types. They are separate from the system of symbolic binary notation mentioned above. The constant 1, when it has type `nat`, will automatically be simplified to `Suc 0`. We would much have preferred to treat the two expressions as symbolically identical, but couldn't think of a clean way to do it. If you are working with natural numbers, especially as a beginner, it would be best to avoid the symbol 1 altogether.

### Real constants and interval arithmetic

You can also write real constants such as 3.1416.
This expands to the fraction 31416 / 10^4.
After simplification, this fraction will be simplified and the denominator may get multiplied out; you may not recognise your real constant anymore.

<pre class="source">
<span class="keyword1 command">lemma</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">(</span><span class="main">1</span></span> <span class="main">-</span></span> <span class="numeral">0.3</span><span class="main">*</span><span class="keyword1">𝗂</span><span class="main">)</span> <span class="main">*</span> <span class="main">(</span><span class="numeral">2.7</span> <span class="main">+</span> <span class="numeral">5</span><span class="main">*</span><span class="keyword1">𝗂</span><span class="main">)</span> <span class="main">=</span> <span class="numeral">4.2</span> <span class="main">+</span> <span class="numeral">4.19</span><span class="main">*</span><span class="keyword1">𝗂</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">simp</span> <span class="quasi_keyword">add</span><span class="main main">:</span> <span class="dynamic dynamic">algebra_simps</span><span class="main">)</span>
</pre>
  
For complex numbers, the imaginary constant `𝗂` can be chosen from the Symbols palette under Letters, or typed directly as `\<i>`
Please note that `^` operator requires the exponent to be a natural number; to use integer or real exponents, the corresponding operators are `powi` and `powr`. 

### Large integer computations using code generation 

Evaluating functions like the factorial, that are recursive but generate large integers, require special treatment.
The recursion requires the argument to be given in unary notation, but the results must be given in symbolic binary notation.
The most efficient way to achieve this is to make use of computational reflection, where executable Standard ML code is extracted from function definition and run directly on the computer.
We can compute factorials and test primality with reasonable efficiency.
The proof method `eval` calls for the computational evaluation of expressions in the goal statement. These cannot be done using `auto`!

<pre class="source">
<span class="keyword1 command">lemma</span> <span class="quoted"><span class="quoted"><span>"</span>fact</span> <span class="numeral">20</span> <span class="main">&lt;</span></span> <span class="main">(</span><span class="numeral">2432902008176640001</span><span class="main">::</span>nat<span class="main">)</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="operator">eval</span>

<span class="keyword1 command">lemma</span> <span class="quoted"><span class="quoted"><span>"</span>prime</span> <span class="main">(</span><span class="numeral">179424673</span><span class="main">::</span>nat</span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="operator">eval</span>
</pre>

It must be noted that computational reflection provides a weaker standard of proof, as we are required to trust the translation from higher-order logic into Standard ML and then to machine code for execution.
In mitigation, we can remark that the function being translated into Standard ML is trivial, 
and that we already have to trust the Standard ML system to run Isabelle itself.

### Precise real-number computations using interval arithmetic

The `approximation` proof method, developed by Johannes Hölzl, provides arbitrary-precision real arithmetic via computational reflection.
It can perform calculations that otherwise would be beyond tedious.
Its argument specifies the required precision.

<pre class="source">
<span class="keyword1 command">lemma</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">¦</span></span>pi</span> <span class="main">-</span> <span class="numeral">355</span><span class="main">/</span><span class="numeral">113</span><span class="main">¦</span> <span class="main">&lt;</span> <span class="main">1</span><span class="main">/</span><span class="numeral">10</span><span class="main">^</span><span class="numeral">6</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">approximation</span> 25<span class="main">)</span>

<span class="keyword1 command">lemma</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">¦</span></span>sqrt</span> <span class="numeral">2</span> <span class="main">-</span> <span class="numeral">1.4142135624</span><span class="main">¦</span> <span class="main">&lt;</span> <span class="main">1</span><span class="main">/</span><span class="numeral">10</span><span class="main">^</span><span class="numeral">10</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">approximation</span> 35<span class="main">)</span>
</pre>

Remarkably, `approximation` is not confined to single values but can also prove numerical results on closed intervals, via the `splitting` option.
 
<pre class="source">
<span class="keyword1 command">lemma</span><span>
  </span><span class="keyword2 keyword">fixes</span> <span class="free">x</span><span class="main">::</span><span class="quoted">real</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">∈</span></span> <span class="main">{</span></span><span class="numeral">0.1</span> <span class="main">..</span> <span class="main">1</span><span class="main">}</span><span>"</span><span>
  </span><span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">*</span></span> ln</span><span class="main">(</span><span class="free">x</span><span class="main">)</span> <span class="main">≥</span> <span class="main">-</span><span class="numeral">0.368</span><span>"</span><span>
  </span><span class="keyword1 command">using</span> assms <span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">approximation</span> 17 <span class="quasi_keyword">splitting</span><span class="main main">:</span> <span class="quoted free">x</span><span class="main main">=</span>13<span class="main">)</span>
</pre>

This particular example is problematical because $x\ln x$ is undefined when $x=0$.
The given interval avoids zero, since otherwise `approximation` would simply fail.
The example above takes a couple of seconds even though it is not that close to the exact answer, which is $-1/e \approx 0.36787944$.

If we try to get even a little bit closer, the `approximation` tactic takes much more than a couple of seconds.

<pre class="source">
<span class="keyword1 command">lemma</span><span>
  </span><span class="keyword2 keyword">fixes</span> <span class="free">x</span><span class="main">::</span><span class="quoted">real</span><span>
  </span><span class="keyword2 keyword">assumes</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">∈</span></span> <span class="main">{</span></span><span class="numeral">0.1</span> <span class="main">..</span> <span class="main">1</span><span class="main">}</span><span>"</span><span>
  </span><span class="keyword2 keyword">shows</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free">x</span> <span class="main">*</span></span> ln</span><span class="main">(</span><span class="free">x</span><span class="main">)</span> <span class="main">≥</span> <span class="main">-</span><span class="numeral">0.3679</span><span>"</span><span>
</span><span class="keyword1 command">using</span> assms<span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">approximation</span> 18 <span class="quasi_keyword">splitting</span><span class="main main">:</span> <span class="quoted free">x</span><span class="main main">=</span>16<span class="main">)</span>
</pre>

I hope to treat this example precisely in a future post.
However, sometimes this sort of approximation is exactly what we need.

### A final remark: inclusion chains of different kinds of numbers?

Some proof assistants support the common convention that the different kinds of numbers form an inclusion chain:
the natural numbers are literally a subset of the reals,
as opposed to merely being embeddable into them.
To realise this aim requires ugly technicalities, 
as well as making an arbitrary choice of the largest numeric type, to sit at the top of the inclusion chain.
It could be the real numbers, the complex numbers or even something above that level, such as the quaternions. 
But we can always embed one kind of number into something more complicated.

In Isabelle/HOL, the numeric types are distinct, with embedding functions 
such as `of_nat`, which embeds the natural numbers into any type that defines 0, 1 and +, and the analogous `of_int`.
To prevent formulas from being cluttered with occurrences of such functions, Isabelle by default inserts them where necessary to make an expression type-correct.
It does this its own way, and sometimes you may prefer to take control by inserting them yourself the way you like it.
Remember also that numerals such as 1729 can take on any numeric type.

A file containing the examples above is available to [download](/Isabelle-Examples/Numeric.thy).
