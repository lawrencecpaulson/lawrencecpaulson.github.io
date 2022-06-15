---
layout: post
title:  "On Turing machines"
usemathjax: true 
tags: general, logic, Turing
---

Every now and then, somebody claims that Turing "invented the computer" because he invented Turing machines. However, Turing machines aren't actually machines at all. They aren't even models of machines. It turns out (we have Turing's own word for it), a TM is a model of a man working at a desk. So why *did* Turing invent TMs, and where did this lead?

### "On Computable Numbers"

It's often best to put your textbooks aside and turn to the papers themselves.
These days there is no need to fill out a fetch card for a journal volume dated 1936 and wait an hour or so for the librarian to fetch it.
Just ask Mr Google, while relaxing at home, a glass of single malt at your side.
Turing's paper can be found [online](https://doi.org/10.1112/plms/s2-42.1.230)
(also [here](https://www.cs.virginia.edu/~robins/Turing_Paper_1936.pdf)).
The paper is a wonderful read, even [with its mistakes](http://jdh.hamkins.org/alan-turing-on-computable-numbers/).

Turing states his intentions right in the title: "On Computable Numbers, with an Application to the [Decision Problem]". (The *Entscheidungsproblem* asks whether there exists an effective technique for determining whether a given formula of first-order logic is valid, i.e., true in all interpretations.)
Turing expands on his thinking as follows:

> We may compare a man in the process of computing a real number to a machine which is only capable of a finite number of conditions $q_1$, $q_2$, ... $q_R$ ... . The machine is supplied with a " tape" (the analogue of paper) running through it, and divided into sections (called "squares") each capable of bearing a " symbol". ... Some of the symbols written down
> will form the sequence of figures which is the decimal of the real number which is being computed. The others are just rough notes to "assist the memory". It will only be these rough notes which will be liable to erasure.
> It is my contention that these operations include all those which are used in the computation of a number.

Turing proceeds with definitions and proofs, typical of a mathematics article and not at all typical of an engineering article, where one would expect to see a discussion of how to realise some mechanism that had been described.
Turing's main concern, as we see both from his title and from the passage quoted above, is the computation of a *single* real number to an *unlimited* number of decimal places.

Maurice Wilkes


### Conclusion

This post, like several others, is a response to things I saw on Twitter.