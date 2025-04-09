---
layout: post
title:  "Thoughts on user interfaces for theorem provers"
usemathjax: true 
tags: [general, AUTOMATH, jEdit, LCF]
---

People born after 1980 will struggle to imagine what it was like
to use computers in earlier times.
We would type in a program using 
a [punched-card machine](https://www.ibm.com/history/punched-card), 
drop off a deck of cards to be processed, 
and come back later – only to discover that our job had failed due to a misplaced comma.
Luckier souls could sign into a *time-sharing system* 
where they had immediate interaction through a command-line interface.
To get the computer to do anything, we would type some command
and wait for the computer to type its response.
A text editor from that era would typically display one line at a time,
and to specify which line you had to provide a search string:
even a "full-screen editor" would not offer you the luxury of a mouse.
The era of the modern user interface can be dated from 1973, when the legendary
[Palo Alto Research Center](https://www.parc.com) (PARC) announced the 
[Xerox Alto](https://www.computerhistory.org/revolution/input-output/14/347).
Its unique combination of windows, icons, menus and a pointer (i.e. mouse)
would eventually become ubiquitous. 
Suddenly everybody could master a computer, just as the rapidly shrinking cost of processors
put one on everybody's desk.

When I joined the world of interactive theorem proving in 1982, there was much talk
how verification would be easy if only implementers would adopt WIMP interfaces.
Specific suggestions were made: above all, to let people select a subexpression
and a rewrite rule in order to transform it.
This is actually a dumb idea, since the computer can match rewrite rules to subexpressions 
automatically and apply them a thousand times per second. 
Verification is hard because specifications can be complex,
formal proofs tend to be extremely long
and the formalisation of intuitive mathematical ideas often requires great ingenuity.
It's not obvious what a mouse can do for you here.
Forty years on, we have a clearer idea what a good user interface can do for verification,
but the situation is by no means settled.

### AUTOMATH: the first proof assistant?

Some people say that [AUTOMATH](https://lawrencecpaulson.github.io/tag/AUTOMATH) 
was the first proof assistant.
My impression (from hearing NG de Bruijn lecture at Caltech)
is that punched cards were used, but the early papers refer to an interactive mode.
Either way, the proof text was checked one line at a time, 
each line representing a claim based on previous lines.
Your proof text was everything: 
AUTOMATH did not keep track of what you were trying to prove
and there was no "proof state" to display.
In this it was quite different from the proof assistants it inspired, 
such as Coq and Lean.

### LCF and its metalanguage

Robin Milner's key insight in his design of Edinburgh LCF—as noted [previously]({% post_url 2022-09-28-Cambridge_LCF %})—was that no fixed
set of commands could offer an adequate user experience.
Formal proofs tended to include "common patterns of inferences"
that couldn't easily be captured by any fixed command set.
Hence, interaction with LCF should take place through a fully fledged programming language,
which Robin called ML to abbreviate "metalanguage".
This metalanguage could itself be seen as a kind of user interface.

Actual interaction with LCF and its descendants such as HOL involved the crudest possible
user interface: a split [Emacs](https://en.wikipedia.org/wiki/Emacs) window 
with the top pane containing the proof being developed
and the bottom pane a UNIX shell running the theorem prover.
People wrote Emacs macros to streamline the step of copying material from the proof
into the prover and executing it.
Such habits persisted even after the 
[X Window System](https://en.wikipedia.org/wiki/X_Window_System) became available:
I can still remember Mike Gordon allowing a single Emacs window to take up his entire screen
(and he liked really big screens).
We got a lot of criticism from people who insisted that we should be using WIMP
ideas much more.

I have even heard people claim that doing a machine proof
should resemble playing a computer game. This is absolutely the wrong metaphor.
The killer apps of the modern WIMP interface involve the creation of **documents**:
spreadsheets and word processors are as valuable to Microsoft as Windows is.
User interaction with a proof assistant must likewise yield a document, namely a proof script.
This script needs to be at least maintainable, if not actually legible,
with no requirement to spend countless hours playing through the "game" all over again.

### Proof General

[Proof General](https://proofgeneral.github.io), by [David Aspinall](https://homepages.inf.ed.ac.uk/da/),
is essentially a beefed up version of the Emacs interaction model outlined above.
The top pane holds a proof script while the bottom pane holds a running prover process.
The user can step through the proof script by clicking repeatedly on the "forward" button;
the cursor indicates the current location in the proof, which is actually executed below.
Crucially, there is also a "back" button, through which any step (including declarations)
can be undone. An internal protocol communicates between Proof General and the prover.
Access to other prover features can also be provided through menus.

The name Proof General emphasises that this interface is intended to work
with a variety of proof assistants. For years it was the only way
to use Isabelle, until jEdit came along.
It still supports Coq and has in the past supported a dozen other tools. 

### Isabelle/jEdit

Support for Isabelle within Proof General was possible through the work of Makarius Wenzel,
whose structured proof language (Isar) required considerable sophistication from the interface.
An Isar text is not a list of commands but a structured document,
which for its execution requires the maintenance of certain state variables
that affect the display. These typically include the previous claim or possibly
a series of claims that have just been proved and are being supplied to the next proof.
Makarius eventually decided that Emacs was not the right basis for his vision of interaction.

[Isabelle/jEdit](https://rdcu.be/c1xBk) can be puzzling to a new user because, when you open a document, 
nothing seems to be happening.
In fact, the entire visible proof text will have been given to Isabelle and processed.
As you edit it, it is reprocessed almost instantaneously, and with considerable parallelism.
It's quite possible for an entire theory file to be processed 
with the exception of a few lines need more time; 
it is essential to check that all of them terminate!

An Isabelle/jEdit session offers a number of panes giving access to the prover state,
the theory structure and a variety of search/diagnostic tools.
It's particularly productive in situations where you have a series of similar proofs
and can paste in chunks of copied material,
which is quickly checked and any errors flagged.
It also copes well with maintenance of existing proofs, where making a proposed change
at the top of a file immediately flags up all the places that need to be corrected,
and you can instantly jump from one to the next.

A [more recent article](https://rdcu.be/c1xIv) by Makarius covers later
developments, including [Isabelle/Naproche](https://rdcu.be/c1xRF), where you do mathematics
with an English-like specification language, processed via jEdit.

### The future?

Although early suggestions about pointing at subexpressions to rewrite them
were off target, recent advances in machine learning could lead to a useful version
of this idea. I would like to see a user interface that combined pointing
with a request expressed in natural language:

* "How can I move this variable outside the brackets?"
* "Don't these two occurrences of *x* cancel?"
* "How can I make the indexing of these two summations match up?"
* "How can I show that this function is continuous?"

The reply might itself be in natural language, suggesting a proof strategy,
or perhaps it could be bit of proof script, or a skeleton.
AI-powered proof completion, analogous to 
[GitHub Copilot](https://github.blog/2022-06-21-github-copilot-is-generally-available-to-all-developers/),
would make life much easier for us.
And there would be no need to trust any auto-completed material,
since it would all be checked by Isabelle.

#### *[New material added 2025-04-09]*