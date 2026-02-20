---
layout: post
title:  "Memories: doing my PhD at Stanford, under John L Hennessy"
usemathjax: true 
tags: [memories,general]
---
When young researchers get together, one topic of conversation is "who supervised your PhD?"
Back in the day, Rod Burstall was often named. 
Also mentioned were Robin Milner, Dana Scott and Gordon Plotkin.
Then it would be my turn: "[John Hennessy](https://profiles.stanford.edu/john-hennessy)". Who?
Even today, while everyone has heard of Mark Zuckerberg and Bill Gates, few people can name
the guy who is in charge of Google's sprawling empire.
But even those who got past the "who?" would then be asking "why?"

### Early years at Stanford

I arrived in the autumn of 1977. It was not a good time for me.
After a year of drifting, I found myself in the group of David Luckham 
and his [Stanford Pascal Verifier](http://i.stanford.edu/pub/cstr/reports/cs/tr/79/731/CS-TR-79-731.pdf).
It consisted of a [verification condition generator](https://en.wikipedia.org/wiki/Verification_condition_generator) 
for Pascal coupled with a rewriting engine
for proving the assertions generated. The user had to supply the rewrite rules, 
which had to be trusted: a major weakness.
I worked on verifying list processing programs for a while 
(simple things like *append* and *reverse*), but came a cropper when I noticed that
the rewrite rules for lists that I had been given were inconsistent.

Luckham had a strong group. In particular, [Greg Nelson](https://en.wikipedia.org/wiki/Greg_Nelson_(computer_scientist)) 
and [Derek Oppen]() made contributions 
that are still used today in most SMT solvers:

* [congruence closure](https://dl.acm.org/doi/10.1145/322186.322198), 
whereby all available equalities are propagated throughout a formula
* a cooperation framework for [combining decision procedures](https://doi.org/10.1145/357073.357079)

In addition, Derek Oppen created a framework for 
[pretty printing](https://dl.acm.org/doi/10.1145/357114.357115) 
that I adopted every chance I got, which means it is now in HOL4, Isabelle
and the [Poly/ML](https://polyml.org) implementation of [Standard ML](https://doi.org/10.1145/3386336).
Unfortunately, David Luckham had a reputation for exploiting his PhD students; 
I was even taken aside, probably by the kind and lovely departmental secretary, Carolyn Tajnai, and advised to watch out.
Unfortunately, I was by nature inattentive, so I didn't take heed 
and I didn't even notice when (allegedly) Luckham told me that I should move on.
But I did notice when my financial support disappeared.[^1] Enter John.

[^1]: I was not unhappy to learn, years later, about an unfortunate situation involving airport security that got Luckham an invitation to spend a night in a police cell.

### Working with John Hennessy

My first impression was that John looked incredibly young.
Compared with Luckham and many other Stanford professors, he was practically a baby (he was 27).
It must've been a challenge for him as well as myself.
I was there because I had gotten into trouble and needed funding, 
which is not the most promising start for the professor/student relationship.
I was interested in programming languages and theory, 
while his speciality was computer architecture.
Somehow we arrived at a PhD project involving 
theory ([denotational semantics](https://podcasts.ox.ac.uk/keywords/denotational-semantics)) 
and practice (in the form of compiler generation).
Somehow I started building the thing. At first it wasn't working, then it was.
I had built a [semantics-directed compiler generator](https://doi.org/10.1145/582153.582178) consisting of three components:

* a *Grammar Analyser*, which took a programming language specification 
in the form of an [attribute grammar](https://rdcu.be/e3PLO) 
decorated with formulas of denotational semantics 
* a *Universal Translator*, which functioned as a compiler for the specified language
* a *Stack Sachine*, for executing the generated code

The performance penalty for the generated object code was a factor of 1000, but who's counting?

To support myself, generally I worked as a Teaching Assistant and 
gave the occasional lecture standing in for John, 
but on the whole I was simply able to get on with my research.
And at the end when I had finished too quickly to satisfy Stanford's residence requirement,
John even found the money to pay the difference.
(You can't do that at Cambridge, but the residence requirement is only three years.)

At Stanford, like in many other universities, the PhD defence is a public event.
Moreover, the candidate is supposed to bring refreshments, generally something like donuts. 
I decided to bring milk and cookies. This was a stupid idea. 
I wasn't good at baking cookies (a housemate helped me out when it all went wrong), 
and it isn't wise to pretend that your PhD defence is some sort of kindergarten.

### Watching him rise and rise

After getting my PhD, and with John's advice and help, I found myself at Cambridge.
While mostly preoccupied with my research, I got occasional news from Stanford.
John's career trajectory went like this:

* 1989: Director of the Computer System Laboratory [a research unit within the CS department]
* 1994: Chairman of the Computer Science Department
* 1996: Dean of the School of Engineering
* 1999: Provost of Stanford University
* 2000: President of Stanford University

He remained President of Stanford until 2016. Where does one go up from there?
President of the USA would be a weak and frustrating role, at least back in that quaint time 
when the President's powers were limited by the US Constitution.
If you really want to be master of the universe, take charge of Google.
He did that in 2018.

Up until now I have not mentioned John's research. 
(I was not one to follow developments in computer architecture.)
John, with David Patterson, made fundamental contributions 
to the development of RISC technology and wrote two acclaimed textbooks.
John was also a founder of [MIPS Computer Systems](https://en.wikipedia.org/wiki/MIPS_architecture_processors).
His work has been recognised by the ACM's Turing Award and numerous other honours and prizes.
If your computer is fast, one of the people you should thank is John.[^2]

[^2]: And if it is slow, probably you should be blaming Bill Gates.

### As an influence

If asked whom I see as role models, I typically mention [Richard Feynman](https://feynman.com) and John Hennessy. 
It may be ridiculous to name Nobel and Turing laureates, 
but why not aim high? Seriously, what I tried to emulate is not genius or ambition, 
but their willingness to engage with students. Feynman, despite his celebrity, 
went out of his way to communicate his knowledge to lowly undergraduates, 
never hiding behind mathematical formulas 
but revealing their link to natural phenomena.
John did not understand exactly what I was doing.
But he had already grasped that this was not necessary.
It is enough to guide the student through the labyrinth of the PhD process, 
keeping an eye on their progress and recognising when they needed help.
Think of a General Practitioner who has overall familiarity with their patient's health situation and knows when to refer them to a specialist.

John visited Cambridge during the 1990s, perhaps interested in 
taking up a position here. So in a plausible alternative future, 
he might now be the British Prime Minister.
