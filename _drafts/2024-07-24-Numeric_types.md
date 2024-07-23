---
layout: post
title:  The mysteries and frustrations of numeric types
usemathjax: true 
tags: [general, Isabelle, type classes, newbies]
---

Sometimes the smallest details are the worst. What do we mean by 2+2=4? The difficulty is that there are many different kinds of numbers. In mathematical writing, it's usually clear what kind of number is intended, but formalised mathematics has to be unambiguous. Making matters worse is the convention that the different kinds of numbers form an inclusion chain, with the natural numbers at the bottom and the reals? the complex numbers? the quaternions??? at the top. 
There is fact no top, because one can always embed one kind of number into something more complicated. A further complication is that the various kinds of numbers are used in distinctive ways. 
ow do we reconcile the zero versus successor conception of natural numbers with the need to work with precise decimals or large integers? Let's see how it's done in Isabelle/HOL.

### Simple arithmetic with internal binary notation

If you ask Isabelle to prove 2+2=4, thankfully it will do it. What kind of numbers are we talking about here? [Remember]({% post_url 2022-05-11-jEdit-tricks %}), you can inspect any Isabelle syntactic element using CTRL-hover (CMD-hover on a Mac). 
Hover over any of the numbers and Isabelle will display the type `'a`. Hover over that type variable to inspect its type class, which is `numeral`. 
This is the class of all types for which numerals work, and Isabelle knows how to add numerals. It works just as well for large numerals, say to calculate 123456789 + 987654321 = 1111111110. But such super abstract calculations do not work for 2*3=6: this time, if we inspect the type it is again `'a`, but the type class is `{times,numeral}.` That means Isabelle has detected that multiplication is involved but nothing more: no ring laws. 
Another example that fails is 0+2=2; here the relevant type class is `{zero,numeral}`, which does not include the identity law for 0. 

The way to avoid all such problems is simply to ensure that the type is constrained somehow. In most cases, the use of a variable declared previously will be enough. Sometimes a variable declaration will need a type constraint: **fix** *x*`::`*real*. But you can always write an explicit type constraint within an expression, as in 123456789 * (987654321::int). 
Isabelle will happily simplify that to 121932631112635269.

Isabelle can perform arithmetic on constants efficiently thanks to its internal representation: a form of symbolic binary notation. Positional notation is necessary to handle large integers, binary (as opposed to say decimal) makes the formal theory of arithmetic compact. 
Already in the 1990s I had devised a symbolic representation of numerals that worked well; the one used today is a clever refinement of that, but I have no idea whom to credit. If anybody is aware of a publication on this topic, I would be happy to cite it here.
The original version is still used for Isabelle/ZF; it is a two's complement format, eliminating the ugly case-analyses associated with signed arithmetic.

Isabelle/HOL has over the years accumulated some capabilities that are cool although perhaps a little practical value. For example, `root 100 1267650600228229401496703205376` is quickly and automatically simplified to 2.
  
### Unary notation and the horror of 1  

The idea of representing natural numbers using the two symbols `0` and `Suc` (for successor) comes from logic. Unary notation, e.g. `Suc(Suc(Suc 0))` for 3, is convenient for expressing mathematical induction rules symbolically and when defining the concept of a primitive recursive function.
It is not convenient for anything else, taking exponentially more space to represent an integer compared with positional notation.
So it is surprising that one of the most prominent proof assistants uses it even for large integers.

When working with natural numbers (type `nat` in Isabelle/HOL), we sometimes have to translate between unary and binary notation. In particular, we may occasionally need to transform something like 100 into `Suc 99`. If one is prepared to write the transformation as an explicit proof step using the keyword **have**, then Isabelle can prove such identities automatically. Some lower level tricks are available to do the transformation more compactly.

Please note: 0 and 1 are constants, overloaded on all numeric types. They are separate from the system of symbolic binary notation mentioned above. The constant 1, when it has type `nat`, will automatically be simplified to `Suc 0`. We would much have preferred to treat the two expressions as symbolically identical, but couldn't think of a clean way to do it. If you are working with natural numbers, especially as a beginner, it would be best to avoid the symbol 1 altogether.

### Real constants and interval arithmetic

You can also write real constants such as 3.1416.
This expands to the fraction 31416 / 10^4.
After simplification, the denominator will probably get multiplied through and you will not recognise your real constant anymore.


[-0.367879441171442334, [x = 0.367879441176403]]

For complex numbers, the imaginary constant `𝗂` can be chosen from the Symbols palette under Letters, or typed directly as `\<i>`
Please note that `^` operator requires the exponent to be a natural number; to use integer or react opponents, the corresponding operators are `powi` and `powr`. 

