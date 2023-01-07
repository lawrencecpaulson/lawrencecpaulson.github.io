---
layout: post
title:  "Memories: artificial intelligence at Stamford in the 70s"
usemathjax: true 
tags: [memories]
---

These days, artificial intelligence (AI) is synonymous with machine learning (ML),
but old-timers can remember when symbolic approachs were king,
with the wonderful acronym [GOFAI](https://en.wikipedia.org/wiki/GOFAI).
I was at Stanford University from 1977 until 1982, and can vividly recall
the unique atmosphere of the Stanford AI Lab at that time.

### AI in the 1960s

My own interest in AI (as a high school student in the USA) arose
from references to some of MIT's luminaries in Martin Gardner's
"[Mathematical Games](https://en.wikipedia.org/wiki/List_of_Martin_Gardner_Mathematical_Games_columns)" column 
in *Scientific American*
and to a hagiographic article probably in *National Geographic*, 
also focused on MIT.[^1] (Can't find it, sorry.)
I also saw a [filmed demo](https://youtu.be/bo4RvYJYOzI)
of Terry Winograd's [SHRDLU](https://hci.stanford.edu/~winograd/shrdlu/).
The dialogue that Winograd carried out with his robot 
about blocks in a virtual world  gave a strong impression of sentience.
[Winograd himself later admitted](https://en.wikipedia.org/wiki/SHRDLU)
that it was largely bogus:

> Pressure was for something you could demo. ... I think AI suffered from that a lot, because it led to "Potemkin villages", things which - for the things they actually did in the demo looked good, but when you looked behind that there wasn't enough structure to make it really work more generally.

[^1]: MIT's computing department was at that time called [Project MAC](https://en.wikipedia.org/wiki/MIT_Computer_Science_and_Artificial_Intelligence_Laboratory#Project_MAC): it's a mystery how they never heard from the legal department at McDonald's.

The film *2001: A Space Odyssey* had come out in 1968, envisaging
that within 32 years, computers would be capable of carrying out intelligent dialogue. One of its scientific advisers was MIT's
[Marvin Minsky](https://en.wikipedia.org/wiki/Marvin_Minsky),
the de facto leader of the AI community.

I had the opportunity attend MIT, having been offered an 
undergraduate place in 1973.
Bizarrely, given my enthusiasm for AI at that time, I instead took up
an offer from Caltech, where little AI was done.
The year 1973 also saw the highly critical
[Lighthill Report](http://www.chilton-computing.org.uk/inf/literature/reports/lighthill_report/p001.htm)
in Britain, 
which led to [severe funding cuts](https://en.wikipedia.org/wiki/AI_winter) in both the USA and the UK.

### Stanford AI Lab, 1977

In the 1970s, the [Stanford AI Lab](https://web.stanford.edu/~learnest/sail/)
(SAIL) was located some distance
from the main campus, in the DC Power Building, a wooden semicircular structure that was slowly decaying. I can't recall precisely why I used to
go there, since I wasn't doing AI. 
But it was well worth the half hour bike ride. It had a unique vibe.

It had one of the world's first laser printers, then called the XGP
(Xerox Graphics Printer). It was the size of a refrigerator and printed
on thermal paper that came in rolls. It cut the paper
into pages using an automatic guillotine, and the last page was typically
a little strip (waste not want not). This printer supported Stanford's
[modified version](https://en.wikipedia.org/wiki/Stanford_Extended_ASCII) of the ASCII character set,
extended with logical and mathematical symbols. An ancient line printer
also supported this character set, and somehow the weird green terminals did too.

A PDP-10 ran a bespoke operating system based on an old version of DEC's
[TOPS-10](https://en.wikipedia.org/wiki/TOPS-10). 
Email pioneer [Mark Crispin](https://en.wikipedia.org/wiki/Mark_Crispin)
looked after it.
MIT also used a heavily modified version,
the famous [Incompatible Timesharing System](https://en.wikipedia.org/wiki/Incompatible_Timesharing_System).
DEC's OS presumably had been made available 
in source form, unthinkable now. 
The advantages of rolling your own OS
had to be weighed against the security updates they didn't get,
which already in the 1970s left them vulnerable to hacker 
attacks from across the ARPAnet (that's another story).

[John McCarthy](https://en.wikipedia.org/wiki/John_McCarthy_(computer_scientist)), 
the legendary inventor of Lisp, was the scientific director, 
with [Lester Earnest](https://web.stanford.edu/~learnest/) as lab manager.
Strangely enough, McCarthy was only 50 when I arrived,
but seemed to have left research behind him,[^2]
and I was left with the impression that his main interest was
the promotion of nuclear power.
But exciting things were happening, 
[especially in robotics](https://news.stanford.edu/2019/01/16/stanfords-robotics-legacy/). 
Key researchers including Mike Gordon and Robin Milner
also spent time there.

[^2]: To be fair, his [DBLP page](https://dblp.org/pid/m/JohnMcCarthy.html) shows publications as late as 2009.

### Expert systems

AI has a field seems particularly prone to schisms.
[Expert systems](http://i.stanford.edu/pub/cstr/reports/cs/tr/81/837/CS-TR-81-837.pdf) 
work at Stanford was, as far as I could tell,
entirely separate from McCarthy's world, and not even conducted
at the AI Lab. Expert systems had somehow escaped the gloom
that had fallen over AI as a whole.
[MYCIN](https://en.wikipedia.org/wiki/Mycin), one of the earliest such,
diagnosed bacterial infections and recommended antibiotics
guided by approximately 600 rules that had been obtained by
interviewing doctors. 
Entirely different in architecture from modern ML-based systems,
it was similar in that it used a body of knowledge to deal with 
new situations.
Crucially, it could **explain its answers** in terms of those rules,
which in turn could be traced back to the doctors themselves.
With machine learning we do not need the laborious manual curation
and can work with vastly larger knowledge sources,
but lose this accountability.

### Is theorem proving AI?

[Logic Theorist](https://en.wikipedia.org/wiki/Logic_Theorist), 
regarded by many as the very first AI program, was designed
to prove theorems from Whitehead and Russell's *[Principia Mathematica](https://www.cambridge.org/gb/academic/subjects/mathematics/logic-categories-and-sets/principia-mathematica-56-2nd-edition)*.
LT proved 38 theorems from the first two chapters.
Two years later, [Hao Wang](https://doi.org/10.1147/rd.41.0002)
did rather better:

> the whole list of over 200 theorems of the first five chapters of *Principia Mathematica* were proved ... the actual proving time for over 200 theorems was less than 3 minutes.

It's odd that LT is celebrated while the far superior
work of Wang is generally overlooked.
The reason perhaps is that LT was seen as a cognitive simulation,
while Wang merely used an algorithm. As it happens, algorithms often win.

The AI world at that time struggled over issues such as whether
knowledge was best captured procedurally (in the form of executable code),
or declaratively, and if the latter, in what sort of knowledge 
representation language. John McCarthy was a fan of first-order logic.
For a time, the whole enterprise of automating logic, 
such as the [CADE conference series](https://cadeinc.org), could be regarded as AI.
Allow me to express my view that though is not logical and that
human beings are spectacularly bad at logic.

**LCF done at SAIL**



[survey of early AI](https://projects.csail.mit.edu/films/aifilms/AIFilms.html)


### Postscript

When I arrived at the computer laboratory in 1982, its Head
was Prof Roger Needham. I was amused to stumble upon 
[some comments](http://www.chilton-computing.org.uk/inf/literature/reports/lighthill_report/p003.htm) 
he wrote in response to the Lighthill Report.

> Artificial Intelligence is a rather pernicious label to attach to a very mixed bunch of activities, and one could argue that the sooner we forget it the better. It would be disastrous to conclude that AI was a Bad Thing and should not be supported, and it would be disastrous to conclude that it was a Good Thing and should have privileged access to the money tap. The former would tend to penalise well-based efforts to make computers do complicated things which had not been programmed before, and the latter would be a great waste of resources. AI does not refer to anything definite enough to have a coherent policy about in this way.

The term AI still refers to a very mixed bunch of things.

[Paper by Darwiche](https://doi.org/10.1145/3271625)
also [here](https://arxiv.org/abs/1707.04327)



