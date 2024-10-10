---
layout: post
title:  "Memories: first exposure to computers"
usemathjax: true
tags: [general, memories]
---

In *The Life and Games of Mikhail Tal*, the legendary former World Chess Champion
mentioned his urge—when annotating his earliest games—to stretch out his hand
to attach a question mark (indicating an error) to almost every move.
That's how I feel about my early experiments.
I must have been about 15 when I first touched a computer keyboard, an [ASR-33 teletype](https://en.wikipedia.org/wiki/Teletype_Model_33).
Until then, my main hobby had been electronics: I built radios
and owned a digital breadboard with a few flip-flops that could be
wired together in different ways.
I can't remember which teacher pushed me in the direction of computers.
Two others were involved: Mr Stanfield and Mr Hilbert.
The latter taught Mathematics, but let's be clear: I am not old enough
to have met David Hilbert, and he was never a schoolteacher in the USA.

### Experiments with BASIC

BASIC is a terrible language, but there were few alternatives back then.
I had dial-up access to a 32K Hewlett-Packard minicomputer, and I got so obsessed
I used to slip in for five minute sessions between classes. I learned how
to get something out of the computer quickly.

Perhaps my first program was an attempt to calculate $\pi$, 
suggested by one of my teachers, using the formula

$$ \pi/4 = 1−\frac{1}{3}+\frac{1}{5}−\frac{1}{7}+\cdots $$

I think we used just the four terms above, which we pointlessly stored in an array before adding them, and I was disappointed with the result (about 2.9).
The series converges more slowly than you can imagine.
There are [better methods](https://cloud.google.com/blog/products/compute/calculating-100-trillion-digits-of-pi-on-google-cloud).

As I was an avid fan of [Martin Gardner](https://martin-gardner.org)'s 
[Mathematical Games](https://blogs.scientificamerican.com/guest-blog/the-top-10-martin-gardner-scientific-american-articles/) column
in Scientific American, at some point I turned to 
the [Game of Life](https://conwaylife.com), 
invented by [John Conway](https://royalsocietypublishing.org/doi/10.1098/rsbm.2021.0034).
I decided to do this in BASIC, using a small array and lots of nested loops.
Also through Gardner I came across the [game of Nim](https://en.wikipedia.org/wiki/Nim),
for which perfect play can be had by a simple algorithm. This may be
the first decent program I ever wrote.

I loved writing code. Once I had finished a program and it could no longer be improved, my task was to find some other project. 
Presumably this is how I got into the frame of mind for doing research.

### Experiments with PDP-8 assembly language

The [PDP-8](https://www.pdp8online.com) was a legendary minicomputer built by a legendary company,
the [Digital Equipment Corporation](https://www.computerhistory.org/brochures/d-f/digital-equipment-corporation-dec/) (or DEC).
The University of Pennsylvania's [Moore School of Electrical Engineering](https://www.facilities.upenn.edu/maps/locations/moore-school-building)
had two of them slowly decaying in a basement. My mother got me access
by calling people there and telling them what a genius I was for so long that
they finally gave in just to get her off the line.
I am eternally grateful.
These machines were less capable than the Hewlett-Packard model I could use at school,
but they were right in front of me, panel lights, switches and everything.
There was a [DEC 338](http://www.bitsavers.org/pdf/dec/graphics/338_Display_Brochure_1967.pdf)
vector graphics display with a light pen.
The hard disk could hold an immense 32K of 12-bit words and there was also a
[DECtape drive](https://www.pdp8online.com/tu56/tu56.shtml).
The two machines each had 8K of 12-bit words, which corresponds to 12K bytes of memory.
Its cycle time of 1.5 µs would today be described as a clock rate of 667 kHz.

Software included some sort of rudimentary operating system, 
a BASIC-like programming language called [FOCAL-8](https://homepage.divms.uiowa.edu/~jones/pdp8/focal/)
and minimal versions of Fortran and LISP.
The luxurious [MACRO-8](https://www.grc.com/pdp-8/docs/macro-8_programming_manual.pdf)
assembly language was also available. 
The machine had to be [booted up manually](https://bigdanzblog.wordpress.com/2014/06/17/simh-pdp-8-manually-loading-the-rim-loader-the-binary-loader-and-an-application-from-paper-tape/) by keying instructions through the switches,
then loading software via paper tape.

I wrote a lot of code, most of it of no value,
but I did learn how floating-point arithmetic was implemented, how to program the light pen,
and how code productively in assembler.
I was even hired by a University of Pennsylvania Professor,
[Ruzena Bajcsy](https://www2.eecs.berkeley.edu/Faculty/Homepages/bajcsy.html),
to write a little program to transfer images
from some device of hers to the mainframe upstairs.
This was one of the very few times I was paid to write code.
I believe that I got two dollars an hour. The minimum wage at that time was $1.65 an hour. 
It was a privilege to gain experience with the PDP-8, a machine that [everybody loved](http://homepage.cs.uiowa.edu/~dwjones/pdp8/). 

### My year in the finance industry

During the four years I spent at Caltech, I went home every summer to work at a local company
called ICDC, Inc. They were an insurance premium finance house: 
you could buy insurance on credit, with the policy as collateral.
I learned how small business data processing was done during the 1970s.
Every day, new accounts were opened and payments arrived for existing accounts.
The transactions were keyed onto paper tape, then sorted and merged with the master file.
Every day, letters went out: for the new customers, a welcome letter including
tear-off coupons for each instalment, showing the amount, account number and due date.
Other letters informed customers that they had missed a payment
or were in default with their insurance cancelled.
Those who were still owing despite the refunded premium would receive increasingly threatening
letters from a pretend collection agency called World Wide Searchers.
I was impressed by the office automation: the various letters came off the printer
and were fed into machinery that stuffed envelopes automatically 
and stamped them with the correct postage.

The computing environment was less impressive: a 
[Varian 620/i](http://www.bitsavers.org/pdf/varian/620i/98A9902003C_620iSyRef_Mar69.pdf)
with 16K of memory, several tape drives and several cartridge drives.
You could always count on some of the tape drives being out of action.
There was no disc, and you had to become an expert on splicing paper tapes.
Here too, the ASR-33 was king, and in this era of gigabit Internet in the home,
consider that their transmission rate was only 110 baud, which is 9 million times slower.

Although the business language RPG was available and was probably much more suitable,
the programmers at ICDC had decided to hack the Fortran system so that REAL numbers
were actually 32-bit integers, since you can't use floating-point for accounting purposes.
Without going into details, let's just say the programming environment was delicate.
If [Edsger W Dijkstra](https://www.computer.org/profiles/edsger-dijkstra) were to enter the machine room, he would probably perish within minutes.

During my first summer, a local insurance company called 
[Gateway](https://www.nytimes.com/1974/11/23/archives/insurance-claims-against-gateway-to-be-paid-soon.html) went bankrupt.
This was a crisis: suddenly a big chunk of loans lacked collateral.
I was given the task of determining ICDC's exposure to Gateway and of generating letters
to the affected customers informing them that they would have to pay off the full balance
of their loans even though their insurance was gone
(today it would be a haircut for the lender) and that ICDC, Inc.
would be delighted to refinance their existing balance and new insurance
on generous terms.

To run a program, you had to mount a tape holding its object code along with other tapes
for its inputs and outputs.
(I also recall a small library of paper tapes.)
Just about every program they ran was a simple loop and performed essentially a database query, 
reading successive records from the master file and 
for some of them, doing a basic action such as printing a letter.
A more sophisticated program would involve two nested loops.
Databases that could do these tasks were surely available by the 1970s
and data processing services powered by mainframes probably could have
replaced our entire data processing department. 
As I discovered a few years later, this actually happened:
something broke beyond repair and the company was forced temporarily
to return to manual processing.
But when I was working there, rather than outsourcing their data processing needs,
the company was building a small business software suite with the aim of satisfying
the data processing needs of others. Something tells me they never got a single client.

Academics are often urged to learn about the real world of industrial computing,
but probably the four summers I spent don't count.
Yet I learned a lot. And I earned about $2.50 per hour.

