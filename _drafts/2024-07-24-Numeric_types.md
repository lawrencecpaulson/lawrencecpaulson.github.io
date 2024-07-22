---
layout: post
title:  The mysteries and frustrations of numeric types
usemathjax: true 
tags: [general, Isabelle, type classes, newbies]
---

Sometimes the smallest details are the worst. What do we mean by 2+2=4? The difficulty is that there are many different kinds of numbers. In mathematical writing, it's usually clear what kind of number is intended, but formalised mathematics has to be unambiguous. Making matters worse is the convention that the different kinds of numbers form an inclusion chain, with the natural numbers at the bottom and the reals? the complex numbers? the quaternions??? at the top. There is fact no top, because one can always embed one kind of number into something more complicated. A further complication is that the various kinds of numbers are used in distinctive ways. How do we reconcile the zero versus successor conception of natural numbers with the need to work with precise decimals or large integers? Let's see how it's done in Isabelle/HOL.

### Simple arithmetic

If you ask Isabelle to prove 2+2=4, thankfully it will do it. And what kind of numbers are we talking about here? [Remember]({% post_url 2022-05-11-jEdit-tricks %}), you can inspect any Isabelle syntactic element using CTRL-hover (CMD-hover on a Mac). Hover over any of the numbers and Isabelle will display the type 'a. You can hover over that to inspect its type class, which is numeral. This is the class of all types for which numerals work, and Isabelle knows how to add numerals. It works just as well for large numerals, say to calculate 123456789 + 987654321 = 1111111110. But search super abstract calculations do not work for 2*3=6: this time, if we inspect the type it is again 'a, but the type class is {times,numeral}. That means Isabelle has detected that multiplication is involved but nothing more. Another example that fails is 0+2=2; here the relevant type class is {zero,numeral}. The way to avoid all such problems is simply to ensure that the type is constrained somehow. In most cases, the use of a variable declared previously will be enough. But you can always write an explicit type constraint, as in 123456789 * (987654321::int). Isabelle will happily, and efficiently, simplify that to 121932631112635269.
