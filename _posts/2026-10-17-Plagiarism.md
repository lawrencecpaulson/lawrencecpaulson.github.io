---
layout: post
title:  Plagiarism in the age of AI
tags: [general]
---
My first ever "[blog post](https://www.cl.cam.ac.uk/~lp15/Pages/Scream.html)" (though not in *this* blog) was about how to write a research paper. 
I wrote it after reviewing a batch of badly-written papers for a conference, probably ITP or CADE. 
Later — a couple of years ago — came the campaign to oust Claudine Gay as President of Harvard on the grounds that she had committed plagiarism.
Allegations of plagiarism were flying about on social media.
Billionaire hedge fund manager Bill Ackman, one of Gay's main opponents, 
discovered that alleging plagiarism was a game that [anyone could play](https://www.theguardian.com/education/2024/jan/06/neri-oxman-bill-ackman-plagiarism-accusations). 
All of this happened shortly before the annual lecture I give at Cambridge
based on that "how to write a paper" post. 
And it dawned on me that many of my complaints about the papers I was reviewing were really about plagiarism. 
It's a tricky concept to pin down, which makes it especially convenient as a tool to ease out people who happen to be the wrong sex or colour. 
And now, with AI, it is automated. 

### Plagiarism 101

Plagiarism is generally defined as using another person's work without acknowledgement, 
passing it off as your own,
for example when a student copies another student's work. 
In my Cambridge department, we have long followed the practice of asking students 
to bring their programming assignment for a brief interview 
where they answer a few questions about their code. 
If they didn't write it, they won't know anything about it. 
Getting answers from [Stack Exchange](https://stackexchange.com) also counts as plagiarism. 
Another case was when a student, 
asked to write a literature review of certain papers, 
simply copied and pasted paragraphs out of each one. 
Asked to explain himself at a disciplinary tribunal, he simply said, 
"I've always done this and no one ever cared before."
We care because he didn't do his assignment, and he didn't learn anything from the papers either. 
But how does this relate to the badly written papers I was grumbling about? 

[Recollections may vary](https://www.theguardian.com/uk-news/2021/mar/10/recollections-may-vary-how-the-papers-covered-queens-response-to-meghan-interview), 
but it seemed to me that many of the papers I read back in 2015 (and before and since),
began by mentioning three things. 

* the Pentium FDIV bug
* the Ariane 5 crash
* "Program testing can be used to show the presence of bugs, but never to show their absence!"

(I saw the last one quoted again in a technical document only a month ago.)

This is a curious list. The Pentium bug and the Ariane 5 crash were both high profile disasters, but they had happened in the mid-'90s, about 20 years earlier. 
(Was there really nothing since?)
Although they triggered a surge in formal verification, their true relevance is unclear.
The first was reported by Intel to be a fabrication error —
[missing entries](https://en.wikipedia.org/wiki/Pentium_FDIV_bug) 
in a lookup table for floating-point division
— although a [recent analysis](https://www.hackster.io/news/ken-shirriff-tracks-down-intel-s-infamous-pentium-fdiv-bug-in-the-silicon-itself-fe6b8be99f30) now disputes this. 
The second was caused by the use of old code from Ariane 4. 
The third, that famous (1972) quote by Edsger Dijkstra, 
is obvious to anyone who ever tried to get a computer to do anything reliably since about 1950. 
It's not insightful, original or even pithy.
It is not "[These are the times that try men's souls](https://en.wikipedia.org/wiki/The_American_Crisis)".
It is not even "[Pigs are much bigger than you expect](https://www.youtube.com/watch?v=zAYR-i4S-ZE)". 

It can't be a coincidence that people keep making the same bad choices, now decades old. 
But is it plagiarism to copy another guy's examples? 
You can't copy him verbatim, nor are you allowed to paraphrase his text without attribution: 
both are straightforward plagiarism. 
But there are grey areas. 
What if you copy the other guy's references, 
as well as the specific claims he made about them, 
but weave them into your own beautiful and original paragraph?
If you have never looked up those sources, 
if you don't know whether they back those claims, 
if you don't even know whether those references exist, 
then (to paraphrase Jesus) you have committed plagiarism in your heart. 
That's because you have no idea whether anything you have written is actually true. 
(This also happens when your text has been written by AI.[^1])
But you will probably get away with it. 

[^1]: As pointed out to me by Claude Opus 5. 

And ironically, for a paper submitted to a conference on formal verification, 
all three points are redundant. You are preaching to the converted. 
That motivational paragraph can be omitted altogether. 

### Quotations

One way to solve the problem of copying the other guy's material 
is to quote him verbatim, *with attribution*. 
It's best to quote material that does not itself cite other works, 
since his sources do not belong in your bibliography. 
And of course it needs to be pithy and quotable. 
The attribution has to be in full, including the page number, and you had better check it. 

In the case of Dijkstra, his famous quote has often been misattributed or mangled.
He is frequently called *Edgar* Dijkstra. 
His quote is rendered in many variant forms, such as "[Testing shows the presence, not the absence, of bugs.](https://quotefancy.com/quote/2268376/Robert-C-Martin-Dijkstra-once-said-Testing-shows-the-presence-not-the-absence-of-bugs-In)"

Dijkstra even misquoted himself in his Turing Award lecture, 
"[The Humble Programmer](https://www.cs.utexas.edu/~EWD/transcriptions/EWD03xx/EWD340.html)", 
but as he omitted the quotation marks, it was okay. He was saying the same thing differently. 
But if *you* get a quote wrong, you are fabricating a quote, 
which is actually worse than plagiarism. 

How many of those who have quoted Dijkstra have checked the original source
or even know where his remark appeared? 
Here is the full citation, and none of it is optional. 

> E. W. Dijkstra. Notes on structured programming. In O.-J. Dahl, E. W. Dijkstra, and C. A. R.
> Hoare, editors, *Structured Programming*. Academic Press, 1972 (page 6).

I have owned this book and read Dijkstra's essay, where he proves, for example, that

> A factor of a thousand is already far beyond our powers of imagination!

And he offers as evidence

> One can close one’s eyes and imagine how it feels to be standing in an open place, a prairie or a sea shore, while far away a big, reinless horse is approaching at a gallop, one can “see” it approaching and passing. To do the same with a phalanx of a thousand of these big beasts is mentally impossible: your heart would miss a number of beats by pure panic, if you could!

Google indicates that I am the first person in the world to quote these passages.
(For completeness, they are found on page 2.)
If you can't be bothered to provide the source for your quotation, 
you should not be quoting it at all. 


### Self-plagiarism

Plagiarism is theft. So what does it mean to steal from yourself? 
It's when you reuse your material inappropriately. 
Another of my hates from that 2015 round of refereeing 
was people who used the same text in their abstract, their introduction, 
and maybe even their conclusions. 
For one thing, the different parts of a paper have different purposes. 
You don't use a toilet plunger as a cookie cutter. 
And once people notice you're in the habit of reusing your own material, 
they are likely to give up altogether. 
I can remember a guy who gave me a bunch of his papers. 
I read one, then I picked up another, and another, 
and there were so many verbatim overlaps — whole paragraphs and worked examples — 
that I threw them all away. 

Self-plagiarism takes another form, which I have been guilty of many times. 
It's when you publish something in a conference, then submit it to a journal. 
The point is that a journal version will give you more views and more prestige, 
but you have to make it significantly longer and better than the conference version. 
These days you are expected to include a footnote to say that the journal version 
is based on your earlier work, which you should cite. 

### Boilerplate

A typical paper starts with an introduction to motivate the work, followed by a section on background material.
This should include the concepts and notation needed to understand the rest of the paper.
Formal definitions, whether mathematical or otherwise, 
may be copied verbatim because they involve no originality. 
There really is only one way to define a prime number. 
On the other hand, explanations and examples still count as original. 

In that bleak time in 2015, I faced again an old enemy:
two incomprehensible pages of definitions involving low‑level syntax: 
*terms* and *formulas*, *occurrences* (positions) in a term, *substitutions*, 
*unifiers*, *literals*, *clauses* and on and on. 
I was never sure, but it seemed to me that they were exactly the same every time, 
as if a file of this crap were being shared to everyone who was worried 
about filling their page limit.[^2]
Occasionally, I felt like checking how many of the definitions were actually used.
The paper might still be good, but often I was tempted to grab my mouse and choose *Strong Reject*. 
Material of that sort belongs in an appendix.

[^2]: which incidentally is an upper bound, not a lower bound

Another source of boilerplate material is your acknowledgements. 
I remember seeing Prof. Gay accused of plagiarising her acknowledgements.
And I am willing to bet a considerable sum that she did not acknowledge 
another person's parents, professor or boyfriend. 
If you write "I am grateful to X for their unstinting love and support, 
to Professor Y for their wise and insightful advice,
and to Z for not letting me give up", 
you will score highly on the plagiarism detector.
Fortunately, it doesn't matter.

### The penalty

Since people have been drummed out of their jobs for plagiarism, 
it's worth thinking about how it should be punished. 
For Cambridge students in straightforward cases, the rule is simple: the copied work receives zero credit. 
So the penalty hinges on how much was copied and how important it was, which is fair. 
Copying a few sentences for your introduction may cost you nothing 
beyond the ordeal of the disciplinary tribunal. 
No one cares about the acknowledgements at all. 
If, on the other hand, you have copied the heart of the work, you are likely to get a zero. 
And that could easily mean failing the course. 

It's remarkable how many media commentators seem to think 
that plagiarism is some sort of ultimate crime,
especially for those of the wrong sex or colour.
But it is not a crime in any legal sense:
it is a form of academic misconduct and more common than many people realise.
The appropriate response depends on what was copied and why.
The same pundits who rage about alleged plagiarism 
seem to fall silent when other academics are implicated in actual and serious crimes. 

### What about AI? 

Today, journals are overwhelmed by papers generated using AI.
Some people say they should all be desk-rejected:
AI sucks at writing, sometimes fabricates references
and is an automated plagiarism machine to boot. 
It has been trained on existing texts 
and has been seen to output known texts verbatim. 

We need to distinguish between papers *generated* using AI
and those *written with the assistance* of AI. 
How can you benefit from AI as an author? 

I find that AI is helpful at reminding me of things I should know but can't easily recall. 
It might be good at suggesting things to cover in your introduction or conclusions. 
Perhaps, with the right prompt, you'll get "the point of this work" (intro)
as separate and distinct from "what has been learned from this work" (conclusions).
And you can limit your abstract to five sentences. 

AI can help analyse, manage, transform and present your experimental data. 
You still need to check that it did the job right.
It is good at suggesting relevant references.
You still have to locate them, 
check their details and actually read them, at least in part. 
(With a well-written paper, the abstract and conclusions should give you the essence.)
One of my pet hates is too-long abstracts, introductions and conclusions, 
so do not allow AI to fill yours with drivel.

For non‑native speakers forced to write in English, 
the temptation to let AI do the job must be overwhelming. 
And yet your own English will likely more focused and coherent 
than anything that AI can write for you.
If pressed for time, it may work to write in your native language 
and then ask a model to perform a literal translation. 
It will at least be your own voice. 

Once you've got a first draft,
a good language model is the best ever proofreader. 
I've been notified of everything from basic typos
to LaTeX errors (the kind where LaTeX silently gives you the wrong output)
to duplicate ORCID numbers and inconsistent punctuation. 
It can even notice mathematical errors and editorial bias. 

Finally, AI is great when you get a pile of reports from not very happy referees. 
It will digest them for you,
returning a well-organised summary of things you need to fix, why and for whom. 
Use AI for what it's good at, not to plagiarise other people's prose for you.



