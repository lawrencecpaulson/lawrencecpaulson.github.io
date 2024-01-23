---
layout: post
title:  "Why are you being constructive?"
usemathjax: true 
tags: [logic, Bertrand Russell, intuitionism, constructive logic, Martin-Löf type theory, law of excluded middle, philosophy]
---

Four decades ago, I was in a hi-fi shop looking at portable cassette players. Metal tapes had just come out, and metal-compatible cassette players were marketed with METAL emblazoned on the packaging. Three boys aged about 12 rushed into the shop. "That one's got metal!", shouted one. "This one's got metal too!" shouted another. The third boy kept asking, "But does that make it sound better?" They ignored him.

### The intuitionist philosophy of mathematics

Let's recall how constructive logic came about. Russell discovered his famous [paradox](https://plato.stanford.edu/entries/russell-paradox/) in 1901. It shocked the mathematical community because it destroyed a widespread belief: that sets and properties were essentially the same concept. Various other paradoxes emerged around the same time, some based on [self reference](https://www.dpmms.cam.ac.uk/~wtg10/richardsparadox.html) and others connected with size, like [Burali-Forti's paradox](https://www.oxfordreference.com/view/10.1093/oi/authority.20110803095535765).
The various schools of the philosophy of mathematics emerged as responses to these paradoxes. 

I mentioned [intuitionism](https://plato.stanford.edu/entries/intuitionism/) in a [previous post]({% post_url 2021-11-24-Intuitionism %}).
It longs to return to mathematics as it had been done from Euclid until the mid-nineteenth century, when constructions were explicit. It held that every function should be given by an explicit rule.
I'm sympathetic to one of the core ideas of intuitionism—that mathematical objects exist only in our minds—but not to the whole crazy system of ideas.
To [L E J Brouwer](https://plato.stanford.edu/entries/brouwer/), a mathematical fact only became true once it had been proved, so the [largest known prime](https://en.wikipedia.org/wiki/Largest_known_prime_number) could not be said to have been prime at all until recently.
Fermat's last theorem was not true until 1993 (when Wiles first announced it), or maybe October 1994 (when he corrected the error in his proof), or maybe 1995 (after the proof had been accepted by referees and published). Or maybe in 1637, when Fermat first perceived its truth? (Apparently, once something is proved it [remains true forever](https://plato.stanford.edu/entries/intuitionism/#BHKInt).) 
Only God and Brouwer know for sure.
Brouwer rejected the Law of the Excluded Middle (LEM) because to him, $P\lor \neg P$ was the claim that $P$ or $\neg P$ had already been proved (or could be in principle).

Other ideas connected with intuitionism included [bar induction and the fan theorem](https://plato.stanford.edu/entries/intuitionism/#BarThe), and [choice sequences](https://plato.stanford.edu/entries/intuitionism/#TheCon), which were introduced in order to justify the existence of real numbers:

> A *choice sequence* is an infinite sequence of numbers (or finite objects) created by the free will. 

Instead of sets there were [species](https://encyclopediaofmath.org/wiki/Species) and [spreads](https://encyclopediaofmath.org/wiki/Spread_(in_intuitionistic_logic)).
From such a peculiar standpoint, mathematics would have to be developed all over again.
Analysis seemed to pose particular difficulties, and Bishop made a concerted effort to develop [constructive analysis](https://ncatlab.org/nlab/show/Bishop%27s+constructive+mathematics).
Bishop was able to reconstruct a significant fragment of elementary analysis from constructive principles, arriving at a strikingly different mathematics where, for example, all total functions turned out to be continuous.
Mainstream mathematicians weren't interested, but it's easy to see why others might want to explore that world further.

The intuitionistic philosophy explicitly rejects any identification of mathematics with language.
Here is [Arend Heyting](https://en.wikipedia.org/wiki/Arend_Heyting), Brouwer's student and disciple:

> Mathematics is a production of the human mind. [The intuitionistic mathematician] uses language, both natural and formalised, only for communicating thoughts, i.e., to get others or himself to follow his own mathematical ideas. Such a linguistic accompaniment is not a representation of mathematics; still less is it mathematics itself.[^1]

[^1]: Carnap, R., Heyting, A., & Neumann, J. (1984). Symposium on the foundations of mathematics. In P. Benacerraf & H. Putnam (Eds.), *Philosophy of Mathematics: Selected Readings* (pp. 41-65). Cambridge University Press. doi:10.1017/CBO9781139171519.003


Thus it is diametrically opposed to the philosophy known as [formalism](https://plato.stanford.edu/entries/formalism-mathematics/), which declares that the objects studied by mathematicians *are nothing but* the symbolic terms of their own language. A chief proponent of that philosophy was [Haskell B Curry](https://plato.stanford.edu/entries/formalism-mathematics/#TerForCur). Yes, the same Curry as in Curry–Howard isomorphism.


### Constructive type theories vs intuitionistism

The emergence of Martin-Löf's "[Intuitionistic theory of types](https://doi.org/10.1093/oso/9780198501275.003.0010)" 
(also [here](/papers/ML-Int-TT.pdf)) in 1972 brought constructive mathematics to the attention of a generation of computer scientists.
As the first embodiment of the conception of [propositions as types](https://plato.stanford.edu/entries/type-theory-intuitionistic/#PropType), it appeared to offer everything from the possibility of formalising Bishop-style constructivism to a principled approach to correct-program synthesis.
At the same time, it embodied a glaring contradiction: to support constructive mathematics and in particular the work of Bishop through a formal system combining the ideas of two opposites, Heyting and Curry. 

In his early papers, Martin-Löf continued to refer to Brouwer, Bishop and Heyting,  to affirm the axiom of choice and to adhere to some intuitionistic terminology, such as species. However, as other type theories emerged during the 1980s, [constructive mathematics](https://plato.stanford.edu/entries/mathematics-constructive/) left most of that behind as so much baggage, retaining just two core principles:

1. A proof of $P\lor Q$ or $\exists x.\,P(x)$ should communicate which choice was made.
2. The law of the excluded middle (LEM) must be rejected.

These ideas aren't unreasonable. 
Principle 1 is attractive in itself, and you can't have it if you have LEM. 
Moreover, the constructions of Martin-Löf type theory would not be executable in the presence of LEM. 
A formal system conforming to those principles can be expected to have strong properties not found in other systems. However, *formal systems are not the same thing as mathematics*.

Classical mathematicians already distinguish between proofs that merely guarantee existence—for example, there are only countably many algebraic numbers, so transcendental numbers exist—and those that exhibit a particular object. The constructive objection is that the reasoning must be constructive right the way through, not merely in the construction of the desired object. Such an objection however is seldom supported by reasons.

### The wonderful excluded middle

Now for something odd. The following formula is a tautology even in intuitionistic logic:

$$ 
\begin{align*}
 (P \lor (P\to R) \to Q\to R) \to Q\to R 
\end{align*}
$$

*Proof*. Assume $P \lor (P\to R) \to Q\to R$ and $Q$, hoping to show $R$.
From the two assumptions there follows $P \lor (P\to R) \to R$. Therefore $P\to R$ and $(P\to R) \to R$, from which follows $R$. [BFD](https://www.urbandictionary.com/define.php?term=BFD).

Replacing $R$ by $\bot$ (falsity) above, we obtain

$$ 
\begin{align*}
 (P \lor \neg P \to \neg Q) \to \neg Q.
\end{align*}
$$

Thus, we are free to use the excluded middle as much as we like provided the claim being proved is *negative*. 
Many important results are positive: for example, both the [completensss theorem](https://plato.stanford.edu/entries/goedel/#ComThe)
and [Kőnig's infinity lemma](https://en.wikipedia.org/wiki/Kőnig%27s_lemma)
make non-constructive existential claims.
Are any interesting statements negative? Here are some:

* Fermat's last theorem, $\neg(\exists x y z n\in \mathbb{N^{+}}.\, x^n+y^n = z^n \land n>2)$
* Goldbach's conjecture, $\neg(\exists n\in \mathbb{N}.\, n>2 \land 2\mid n \land \text{ $n$ is not the sum of two primes})$
* Twin prime conjecture: $\neg(\exists p.\, \text{$p$ is the greatest twin prime})$
* The Riemann hypothesis: the nontrivial zeros of the [zeta function](https://en.wikipedia.org/wiki/Riemann_zeta_function) all have real part $1/2$

The most celebrated conjectures in mathematics appear to be universal formulas, which means they are—even to an intuitionist—negated existentials.

One way for an intuitionist to comprehend classical reasoning is to say that it simply identifies the two statements $\neg\neg P$ and $P$, so the language of classical logic is slightly less precise. Then the critical question is how often that precision matters.
And remember what we gain through classical logic:

* powerful automatic proof procedures
* access to the vast world of mathematics as it is done by practically everybody

### "Our proofs are constructive"

The reason for this grumbling post is that I have never encountered the promised formal development of Bishop-style analysis, which would have been fascinating.
Instead, I have been seeing, for decades, excellent papers marred by silly, empty claims about constructive reasoning. They are typically

* Trivial (e.g. the subject matter concerns discrete, finite objects)
* Irrelevant (proving a negative statement about simple, finite objects, completely free of constructive content)
* Nonsensical (e.g. applying constructive methods to classical analysis, a vegan meal with a starter of foie gras)

I've seen related work criticised simply because it is not constructive.
If one asks why, the response is typically that "constructive" is simply better,
in a tone laden with moral condescension. But it isn't actually better without specific reasons, and the original philosophical basis for intuitionism has been jettisoned. The new Intuitionism looks a lot like the old Formalism.

And yet there are plenty of situations where constructive reasoning really does yield concrete dividends.
One example is [synthetic computability theory](https://www.sciencedirect.com/science/article/pii/S1571066106001861) (also available [here](http://math.andrej.com/data/synthetic.pdf)):

> Our goal is to develop a theory of computability synthetically: we work in a mathematical universe in which all sets and functions come equipped with intrinsic computability structure. Precisely because computability is omnipresent, we never have to speak about it—there will be no mention of Turing machines, or any other notion of computation.

Arguably, we should rise to the challenge of dealing with explicit models of computation.
On the other hand, when textbook proofs themselves invoke the Church-Turing thesis, the synthetic approach allows a faithful formalisation.
Caution is necessary, because the Church-Turing thesis is inconsistent with many formal systems; however, the approach [works in Coq.](https://drops.dagstuhl.de/opus/volltexte/2021/13455/)







