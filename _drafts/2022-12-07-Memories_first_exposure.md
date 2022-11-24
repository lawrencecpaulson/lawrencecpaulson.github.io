---
layout: post
title:  "Memories: First exposure to computers"
usemathjax: true
tags: [general]
---

I must have been about 15 when I first touched a computer keyboard, an ASR-33.
Until then, my main hobby had been electronics: I built a couple of radios
and owned a digital breadboard with a few flip-flops that could be
wired together in different ways.
I can't remember which teacher pushed me in the direction of computers.
Two others were involved: a Mr Stanfield and a Mr Hilbert.
The latter taught Mathematics, but let's be clear: I am not old enough
to have met David Hilbert, and he was never a schoolteacher in the USA.

### Experiments with BASIC

Mikhail Tal, a legendary chess grandmaster, published a book of his games;
for the earliest games he said that he wished to stretch out his hand
to write the annotation "?", meaning an error, against every single move.
That's how I feel about everything I did in the beginning, but that's how it goes.

BASIC is a terrible language, but there were no good alternatives back then.
I had dial-up access to a 32K Hewlett-Packard minicomputer, and I got so obsessed
I used to slip in for five minute sessions between classes. I learned how
to get something out of the computer quickly.

Perhaps my first program was an attempt to calculate $\pi$, 
suggested by one of my teachers, using the formula

$$ \pi/4 = 1−\frac{1}{3}+\frac{1}{5}−\frac{1}{7}+\cdots $$

I think we used just the four terms above, which we pointlessly stored in an array before adding them, and I was disappointed with the result (about 2.9).
The series converges to $\pi$, but as slowly as possible.
There are [better methods](https://cloud.google.com/blog/products/compute/calculating-100-trillion-digits-of-pi-on-google-cloud).

As I was an avid fan of [Martin Gardner](https://martin-gardner.org)'s 
[Mathematical Games](https://blogs.scientificamerican.com/guest-blog/the-top-10-martin-gardner-scientific-american-articles/) column
in Scientific American, at some point I turned to 
the [Game of Life](https://conwaylife.com), 
invented by [John Conway](https://royalsocietypublishing.org/doi/10.1098/rsbm.2021.0034).
I decided to do this in BASIC, using a small array and lots of nested loops.
Also Gardner I came across the [game of Nim](https://en.wikipedia.org/wiki/Nim),
for which perfect play is obtainable through a simple algorithm. This may be
the first decent program I ever wrote.

### Experiments with PDP-8 assembly language

The [PDP-8](https://www.pdp8online.com) was a legendary minicomputer built by a legendary company,
the [Digital Equipment Corporation](https://digital.com/digital-equipment-corporation/) (or DEC).
The University of Pennsylvania's [Moore School of Electrical Engineering](https://www.facilities.upenn.edu/maps/locations/moore-school-building)
had two of them slowly decaying in a basement. My mother got me access to them
by calling people there and telling them what a genius I was for so long that
they finally gave in just to get her off the line.
I am eternally grateful.

These machines were less capable than the Hewlett-Packard model I could use at school,
but they were right in front of me, panel lights, switches and everything,
and programmable in assembly language.
There was also a DEC338 vector graphics display with a light pen.
It had to be [booted up manually](https://bigdanzblog.wordpress.com/2014/06/17/simh-pdp-8-manually-loading-the-rim-loader-the-binary-loader-and-an-application-from-paper-tape/) by keying instructions through the switches,
then loading software via paper tape.

The two machines each had 8K of 12 bit words, which corresponds to 12K bytes of memory.
Software included some sort of rudimentary operating system, 
a programming language called [FOCAL-8](https://homepage.divms.uiowa.edu/~jones/pdp8/focal/)
and minimal versions of Fortran and LISP.
The luxurious [MACRO-8](https://www.grc.com/pdp-8/docs/macro-8_programming_manual.pdf)
assembly language was also available. 

I wrote a lot of code, most of it of no value,
but I did learn how to program the light pen.
I was even hired by [Ruzena Bajcsy](https://www2.eecs.berkeley.edu/Faculty/Homepages/bajcsy.html) to write a little program to transfer images
from some device of hers to the mainframe upstairs.
This was one of the very few times I was paid to write code.
I believe that I got two dollars an hour. The minimum wage at that time was $1.65 an hour. 

It was a privilege to gain experience with the PDP-8, a machine that [everybody loved](http://homepage.cs.uiowa.edu/~dwjones/pdp8/). 
