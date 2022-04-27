---
layout: post
title:  "Getting started: basic Isabelle/jEdit tricks"
usemathjax: true 
tags: jEdit, Isabelle
---

As mentioned last time, proof assistants can be daunting, and it's not just about how to prove theorems. It's about being aware of all the bells and whistles provided to help you prove theorems. The first modern proof assistant, Edinburgh LCF, provided nothing but a top-level to the language ML, designed specifically to the the Meta Language for proving theorems. It was a bare-bones environment, but at least it was Turing complete! Nowadays, things work differently.

### Isabelle/jEdit fundamentals
 
Nothing says daunting like the Isabelle/jEdit
[reference manual](https://www.cl.cam.ac.uk/research/hvg/Isabelle/dist/Isabelle/doc/jedit.pdf). Everything you want is there, I suppose. More useful to a beginner is the brief [tutorial](https://arxiv.org/abs/1208.1368) by Christian Sternagel.
Let me summarise his main points even more briefly:

* It looks like a text editor, but Isabelle is processing your text the entire time.
* Each and every symbol is digested by the Isabelle process, 
* By hovering/clicking you can interrogate symbols for their types and definitions.
* The document is processed in parallel, so the last proof can be fully processed while some earlier proof is still running.

This last point can be puzzling if you watch the progress bar on the right and follow the processing of your theory: how does it reach the bottom when there are red blobs (inducating errors) and purple blobs (indicating a proof still running)? You need to watch out for this:

<img src="/images/looping-proof.png" alt="a proof of False?" width="500"/>

What's going on? The first lemma, `whoops`, is actually false but the supplied proof fails to terminate. Isabelle assumes that the proof will succeed eventually, allowing `False` to be proved. This strange phenomenon can only happen in interactive mode: the corresponding batch job will run forever. Unfortunately, a student once submitted work containing this error.

More beginner's points:

* When typing text, jEdit will flag errors in your partially-entered text. Ignore and keep going.
* Text containing syntactic or type errors is skipped over. Since it can't be interpreted, "live" highlighting is not avaiable.
* Syntax errors can either be inside formulas ("inner syntax") or in Isar elements themselves ("outer syntax").

### Watch those colours

bound vs free vs "hanging" variables

approved vs legacy Isar commands


auto-indentation; colouring; 


### Dynamic proof development


#### Sketch and explore

#### induction / cases

### General editing features

abbreviations; HyperSearch; CTRL-8