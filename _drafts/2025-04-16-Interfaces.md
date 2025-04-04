---
layout: post
title:  "User interface ideas applied to formal verification"
usemathjax: true 
tags: [memories,AUTOMATH,LCF]
---
People born after 1980 will struggle to imagine what it was like
to use computers in earlier times.
We would type in a program using a punch-card machine, 
leave a deck of them to be processed, 
and waited ages only to discover a misplaced comma or whatever.
Luckier souls could sign into a time-sharing system 
where at least they had immediate interaction,
but still with a command line interface.
To get the computer to do anything, we would type some command
and wait for the computer to type its response.
To reach a desired location in a file, we would have to search for a suitable keyword.
The last people to experience such tedium were MS-DOS users or UNIX command line diehards.
The revolutionary [Alto](https://en.wikipedia.org/wiki/Xerox_Alto) 
from Xerox Palo Alto Research Centre (PARC) demonstrated the future:
a graphical display with multiple Windows, desktop Icons, Menus
and Pointing device (WIMP).
WIMP made everything easier, and since interactive theorem proving is hard,
the 1980s saw a clamour for the incorporation of user interface ideas.
But how?

### Early proof assistants

Some people say that [AUTOMATH](https://lawrencecpaulson.github.io/tag/AUTOMATH) 
was the first proof assistant.
My impression from hearing NG de Bruijn lecture at Caltech
is that punch cards were used, but the early papers refer to an interactive mode.
With AUTOMATH your proof text was everything: 
it did not keep track of what you were trying to prove.
It would check your proof lines but there was no "proof state "to display in return.

Edinburgh LCF introduced a new model for proof assistants,
in its own way is revolutionary as the Xerox Alto.
