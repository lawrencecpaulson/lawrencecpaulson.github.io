---
layout: post
title:  "Why are you being constructive?"
usemathjax: true 
tags: logic, intuitionism, constructive logic, law of excluded middle
---

Four decades ago, I was in a hi-fi shop looking at portable cassette players. Metal tapes had just come out, and metal-compatible cassette players were marketed with METAL emblazoned on the packaging. Three boys aged about 12 rushed into the shop. "That one's got metal!", shouted one. "This one's got metal too!" shouted another. The third boy kept asking, "but does that make it sound better?" They ignored him.

### The intuitionist philosophy of mathematics

Let's recall how constructive logic came about. Russell discovered his famous [paradox](https://plato.stanford.edu/entries/russell-paradox/) in 1901. It shocked the mathematical community because it destroyed a widespread idea: that sets and properties were essentially the same. Various other paradoxes emerged around the same time, some based on [self reference](https://www.dpmms.cam.ac.uk/~wtg10/richardsparadox.html) and others connected with size, like [Burali-Forti's paradox](https://www.oxfordreference.com/view/10.1093/oi/authority.20110803095535765).
The various schools of the philosophy of mathematics emerged as responses to these paradoxes. 

[Intuitionism](https://plato.stanford.edu/entries/intuitionism/) longs to return to mathematics as it had been done until the mid-nineteenth century, when constructions were explicit and a function had to be given by an explicit rule.
I'm sympathetic to one of the core ideas of intuitionism — that mathematical objects exist only in our minds — but not to the whole crazy system of ideas.
To [L E J Brouwer](https://plato.stanford.edu/entries/brouwer/), a mathematical fact only became true once it had been proved, so the [largest known prime](https://en.wikipedia.org/wiki/Largest_known_prime_number) could not be said to have been prime at all until recently.
Fermat's last theorem was not true until 1993 (when Wiles first announced it), or maybe October 1994 (when he corrected the error in his proof), or maybe 1995 (after the proof had been accepted by referees and published). Or maybe in 1637, when Fermat first perceived its truth? Only God and Brouwer know for sure.
Brouwer rejected the Law of the Excluded Middle (LEM) because to him, $P\lor \neg P$ was the claim that $P$ or $\neg P$ had already been proved (or could be in principle).

Other ideas connected with intuitionism included [bar induction and the fan theorem](https://plato.stanford.edu/entries/intuitionism/#BarThe), and choice sequences, which were introduced in order to justify the existence of real numbers:

> A *choice sequence* is an infinite sequence of numbers (or finite objects) created by the free will. 

Instead of sets there were [species](https://encyclopediaofmath.org/wiki/Species) and [spreads](https://encyclopediaofmath.org/wiki/Spread_(in_intuitionistic_logic)).
From such a peculiar standpoint, mathematics would have to be developed all over again.
Analysis seemed to pose particular difficulties, and Bishop made a concerted effort to develop [constructive analysis](https://ncatlab.org/nlab/show/Bishop%27s+constructive+mathematics).
Bishop was able to reconstruct a significant fragment of elementary analysis from constructive principles, arriving at a strikingly different mathematics where, for example, all functions turned out to be continuous.
Mainstream mathematicians weren't interested, but it's easy to see why others might want to explore that world further.

The intuitionistic philosophy explicitly rejects any identification of mathematics with language.
Here is [Arend Heyting](https://en.wikipedia.org/wiki/Arend_Heyting), Brouwer's student and disciple:

> Mathematics is a production of the human mind. [The intuitionistic mathematician] uses language, both natural and formalised, only for communicating thoughts, i.e., to get others or himself to follow his own mathematical ideas. Such a linguistic accompaniment is not a representation of mathematics; still less is it mathematics itself.

Thus it is diametrically opposed to the philosophy known as [formalism](https://plato.stanford.edu/entries/formalism-mathematics/), which declares that the objects studied by mathematicians *are nothing but* the symbolic terms of their own language. A chief proponent of that philosophy was [Haskell B Curry](https://plato.stanford.edu/entries/formalism-mathematics/#TerForCur).


### Intuitionistic type theory

The emergence of Martin-Löf's "[Intuitionistic theory of types](https://doi.org/10.1093/oso/9780198501275.003.0010)" (also [here](/papers/Martin-Löf-intuitionistic_theory_of_types)) in 1972 brought constructive mathematics to the attention of a generation of computer scientists.
As the first embodiment of the conception of [propositions as types](https://plato.stanford.edu/entries/type-theory-intuitionistic/#PropType), it appeared to offer everything from the possibility of formalising Bishop-style constructivism to a principled approach to correct-program synthesis.
At the same time, it embodied a glaring contradiction: to support constructive mathematics and in particular the work of Bishop through a formal system combining the ideas of two opposites, Heyting and Curry. 

In his early papers, Martin-Löf continued to refer to Brouwer, Bishop and Heyting,  to affirm the axiom of choice and to adhere to some intuitionistic terminology, such as species. However, as other type theories emerged during the 1980s, the research community left most of that behind as so much baggage, retaining just a couple of core principles:

1. Identifying functions with lambda-terms
2. Rejecting the law of the excluded middle (LEM)



### "Our proofs are constructive"

It's time we saw some pushback against cargo-cult constructivism. 

[Coq](https://coq.inria.fr)

### Why Intuitionism?

$$ (P ∨ ¬P ⟶ ¬Q) ⟶ ¬Q $$

The same in a more general form, no ex falso quodlibet

$$ (P ∨ (P⟶R) ⟶ Q ⟶ R) ⟶ Q ⟶ R $$

[mentioned earlier]({% post_url 2021-11-24-Intuitionism %})



The best introduction to [constructive mathematics](https://plato.stanford.edu/entries/mathematics-constructive/)
 and [intuitionistic logic](https://plato.stanford.edu/entries/logic-intuitionistic/) is through an example.





### Intuitionistic type theory

[Agda](https://wiki.portal.chalmers.se/agda/pmwiki.php),

Carnap, R., Heyting, A., & Neumann, J. (1984). Symposium on the foundations of mathematics. In P. Benacerraf & H. Putnam (Eds.), Philosophy of Mathematics: Selected Readings (pp. 41-65). Cambridge: Cambridge University Press. doi:10.1017/CBO9781139171519.003





