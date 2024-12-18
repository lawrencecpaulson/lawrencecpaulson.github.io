---
layout: post
title:  Isabelle quick start guide
usemathjax: true 
full-width: true 
tags: [newbies, Isabelle]
---
I am often asked, "how do I get started with Isabelle?"
For example, why don't we have an analogue of the excellent 
[Natural Number Game](https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/)?
To that I say, it's impossible to re-create the Isabelle experience in a web browser.
Instead, we make it incredibly easy for you to install Isabelle on your own machine,
be it Windows, Linux or Mac, and provide lots of examples to play with.
For small examples, a 4GB Raspberry Pi might be enough.

### Put it on your computer

It's this easy:

* [download](https://isabelle.in.tum.de/) everything you need with a single click (just choose your platform)
* [install](https://isabelle.in.tum.de/installation.html) in minutes according to the instructions
* launch, on both Windows and macOS after dismissing the built-in protections against Trojans;
you can also launch Isabelle from the UNIX command line

But then what? You need some small examples to get a hang of the syntax and then bigger ones to learn how to scale. On this blog, visit the 
[newbies](https://lawrencecpaulson.github.io/tag/newbies) 
and [Isabelle](https://lawrencecpaulson.github.io/tag/Isabelle) tags.

But now I see that even the simplest example, on Fibonacci numbers, is not really for newbies.
the proofs are simple but polished, hiding the trial and error that a beginner would inevitably go through. They are in the structured 
[Isar](https://lawrencecpaulson.github.io/tag/Isar) style,
where every claim has a single-line proof, although most real proofs (especially big ones)
involve chains of tactic steps such as one finds in other proof assistants 
such as Lean, Coq and HOL4: so-called *apply-style* proofs.

### Prove something trivial

We begin with the same Fibonacci example [as before]({% post_url 2021-10-13-Fib-example %}), 
but this time as a true newbie.
Perhaps you have looked at the "Programming and Proving" tutorial,
which is the first one on the [documentation page](https://isabelle.in.tum.de/documentation.html)
and also on the documentation panel of Isabelle itself, 
or maybe in that panel you clicked on one of the examples.
Or easiest of all, downloaded the [Fibonacci example itself](https://lawrencecpaulson.github.io/Isabelle-Examples/Fibonacci.thy) 
from my blog.

We begin with a **theory** declaration specifying 
the theory name (which needs to match the file name) 
and what it **imports**, here simply `Main`, a bare-bones HOL environment.
We supply the definition of the Fibonacci function,
which maps natural numbers to natural numbers (type `nat => nat`).
Then we state a simple lemma to be proved and type in our very first tactic, 
using **apply** (which is how we can apply a series of tactics one after another).
The side panel displays the two subgoals generated by the tactic.

<img src="/images/Fib-newbie/f1.png" alt="a proof of False?" width="1000"/>

Looking at the subgoals, the second is to prove $F_{n+1} \to F_{n+2}$,
which isn't ideal. (And don't be put off by the 0/`Suc`
notation, which is common in proof assistants and best for this type of work.)
The right form of induction should conform to the definition $F_{n+2} = F_{n+1} + F_n$,
and Isabelle provides it for us. Simply change the theory file and it will be processed anew.

<img src="/images/Fib-newbie/f2.png" alt="a proof of False?" width="1000"/>

These subgoals look promising, and indeed the `auto` tactic can finish the job.
It turns out, the ordinary induction rule leads to an equally simple proof – try it –
but only because, due to the types, we get $F_n\ge0$ for free.

<img src="/images/Fib-newbie/f3.png" alt="a proof of False?" width="1000"/>

Finally, we can polish the proof, replacing the **apply**-lines with 
**by** and a pair of comma-separated tactics. Keep it simple, however:
no one wants to see a long string of these.

<img src="/images/Fib-newbie/f4.png" alt="a proof of False?" width="1000"/>

### Prove something harder

<img src="/images/Fib-newbie/f5.png" alt="a proof of False?" width="1000"/>

<img src="/images/Fib-newbie/f6.png" alt="a proof of False?" width="1000"/>

<img src="/images/Fib-newbie/f7.png" alt="a proof of False?" width="1000"/>

<img src="/images/Fib-newbie/f8.png" alt="a proof of False?" width="1000"/>

### Prove something even harder

<img src="/images/Fib-newbie/f9.png" alt="a proof of False?" width="1000"/>

<img src="/images/Fib-newbie/f10.png" alt="a proof of False?" width="1000"/>

<img src="/images/Fib-newbie/f11.png" alt="a proof of False?" width="1000"/>
