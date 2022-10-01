---
layout: post
title:  "Verifying cryptographic protocols"
usemathjax: true
tags: [general]
---

A *cryptographic protocol* is a message sequence, typically of fixed length, with the aim of establishing secure communications between two *principals*.
On-line shopping is the application most people see:
their computer will run a protocol (probably TLS) with the shopping site.
TLS will *authenticate* the on-line shop to you (as assurance that you are not giving your credit card details to some impersonator)
and *encrypt* your communications (keeping them secure from any eavesdropper).
Viewed at a sufficiently high level, a protocol looks like an abstract program
with the great advantage, to people like myself, of not ever having to think about
nasty low-level things like bits.
Although I have never verified code, I (along with many other people) have studied the verification of cryptographic protocols.
There is a lot of confusion about the basic ideas here, which I hope to clarify below.

### Electronic car key fobs

The simplest example of a protocol and what can go wrong is a car key fob.
The first version of these was easy to hack: it simply sent a secret code to the car's locking system, which would check it against its own copy of the code and then unlock.
An attacker could trivially record the signal sent from the key fob
and use it to unlock the car at any time. This is a simple *replay attack*.

One way to defeat this attack would be to for the fob to encrypt the current date and time
using a key shared with the car. The car would decrypt the message,
check the date and time against its own clock, and unlock if they agreed.
A replay of the message recorded earlier would fail this check.
The drawback of this *timestamp* approach is that it requires an accurate clock in the key fob.
Some protocols do use timestamps, notably [Kerberos](https://web.mit.edu/kerberos/), but usually people do not want the bother of maintaining synchronised clocks.

An alternative way to defeat this attack involves a more complicated protocol, involving three messages.
The first message is a request to unlock, including not a code but an 
*identifier* for the car (so that they don't all respond).
In response, the car will generate a random integer $N$ and encrypt it using an 
encryption key $Kc$, which it shares with the fob.
The fob decrypts this response and sends $N$ back to the car's locking system to be checked.
Replay attacks fail because an old value of $N$ will be rejected.

This three message protocol is typically written in the 
following notation:

$$\begin{align*} 
1.\quad F\to C&: C \\
2.\quad C\to F&: \{N\}_{\mathit{Kc}} \\
3.\quad F\to C&: N
\end{align*}$$

The second message is a freshness challenge and illustrates the most common method of defeating
replay attacks: by generating a random number or *nonce* that is impossible to guess
(easily achieved if you make it, say, 40 bytes long).
Timestamps and nonces are the two main techniques for proving freshness.

### Protocol verification: basic principles

Generally we assume the following scenario (the [Dolev-Yao threat model](https://doi.org/10.1109/TIT.1983.1056650)):

* a population of *principals* or *agents* $A$, $B$, $\ldots$
* *nonces*, which we assume to be impossible to guess
* the ability to encrypt, decrypt and hash messages
* an *intruder* who can copy, reroute, delete and even create messages

The intruder is almost omnipotent. 
He is even assumed to have the identity of a normal principal, i.e. he is "inside the castle".
His only limitations are that he cannot simply guess
nonces or cryptographic keys.

Because of the last assumption, we can never prove that a protocol terminates.
Our concern is strictly with the safe execution of protocols.
We assume that encryption and hashing are perfect on the grounds that
if they were not, no protocol could be secure, and we are concerned about
replay attacks that bypass encryption.

*Public-key encryption* is much more expensive than *shared-key encryption* 
and is chiefly used to solve the *key distribution problem* – to convey
a fresh shared key to a distant party – rather than to encrypt long messages.
Other protocols are based entirely on keys shared with a *trusted third party*,
which they use for key distribution.
Returning to the car example, we do not expect a fob
to perform public-key encryption but rather to be manufactured for a particular car
and sharing the required key.



### The Needham-Schroeder protocol and Lowe's attack

In 1978, Roger Needham and Michael Schroeder set forth the principles of crypto protocols in their classic paper,
["Using encryption for authentication in large networks of computers"](https://doi.org/10.1145/359657.359659).
One of their protocols has become particularly well known
in the following form:

$$
\newcommand\Na{\mathit{Na}}
\newcommand\Nb{\mathit{Nb}}
\newcommand\Ka{\mathit{Ka}}
\newcommand\Kb{\mathit{Kb}}
\def\lbb{\mathopen{\{\kern-.30em|}}
\def\rbb{\mathclose{|\kern-.32em\}}}
\def\comp#1{\lbb#1\rbb}
\begin{alignat*}{2}
  &1.&\quad  A\to B  &: \comp{\Na,A}_{\Kb} \\
  &2.&\quad  B\to A  &: \comp{\Na,\Nb}_{\Ka} \\
  &3.&\quad  A\to B  &: \comp{\Nb}_{\Kb}
\end{alignat*}$$

This is the *Needham-Schroeder public-key protocol*.
We have principals $A$ and $B$ ("Alice and Bob").

In the first message, Alice contacts Bob, including nonce $\mathit{Na}$
as a challenge, encrypted with Bob's public key.
By returning $\mathit{Na}$, Bob proves his presence to Alice,
and he includes his own challenge, $\mathit{Nb}$,
both encrypted with Alice's public key.
The third message proves Alice's presence to Bob.
Now each knows that the other is online, and one could imagine a 
"session key" being calculated from $\mathit{Na}$ and $\mathit{Nb}$
for use in private communications.
(Public-key encryption is too expensive to be use with long messages.)

Unfortunately, there is a flaw with this scheme, [pointed out](https://rdcu.be/cWJBL) by
Gavin Lowe back in 1996.
Suppose that Alice runs the protocol with a *dishonest* agent $C$ 
("Charlie"). In that case, Charlie can initiate a new run of the protocol
with some $D$, sending along Alice's first message re-encrypted with $\mathit{Kd}$.
By interleaving the two runs, Charlie can use Alice to decrypt the 
second message, thereby completing the run with $D$ 
while masquerading as $A$: a failure of authentication.
Lowe also showed how to defeat the attack by
a slight chance to the protocol's second message:

$$
\newcommand\Na{\mathit{Na}}
\newcommand\Nb{\mathit{Nb}}
\newcommand\Ka{\mathit{Ka}}
\newcommand\Kb{\mathit{Kb}}
\def\lbb{\mathopen{\{\kern-.30em|}}
\def\rbb{\mathclose{|\kern-.32em\}}}
\def\comp#1{\lbb#1\rbb}
  2'.\quad  B\to A : \comp{\Na,\Nb,B}_{\Ka}
$$


XXXX

One might argue that this is no attack at all.  An agent who is careless
enough to talk to the enemy cannot expect any guarantees.  The mechanised
analysis presented below reveals that the protocol's guarantees for~$A$ are
adequate.  However, those for $B$ are not: they rely upon $A$'s being careful,
which is a stronger assumption than mere honesty.  Moreover, the attack can
also occur if $A$ talks to an honest agent whose private key has been
compromised.  Lowe suggests a simple fix that provides good guarantees for
both $A$ and~$B$.
