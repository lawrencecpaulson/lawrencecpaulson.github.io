---
layout: post
title:  "Verifying cryptographic protocols, I: Fundamentals"
usemathjax: true
tags: [general,verification]
---

A *cryptographic protocol* is a message sequence, typically of fixed length, with the aim of establishing secure communications between two *principals*.
On-line shopping is the application most people see:
their computer will run a protocol (probably TLS) with the shopping site.
TLS will *authenticate* the on-line shop to you (as assurance that you are not giving your credit card details to some impersonator)
and *encrypt* your communications (keeping them secure from any eavesdropper).
Viewed at a sufficiently high level, a protocol looks like an abstract program
with the great advantage, to people like myself, of not ever having to think about
nasty low-level things like bits.
Although I have never verified code, I (among many others) have 
[verified cryptographic protocols](https://doi.org/110.3233/JCS-1998-61-205).
There is a lot of confusion about the basic ideas here, which I hope to clarify below.

### Electronic car key fobs

The simplest example of a protocol and what can go wrong is a car key fob.
The first version of this was easy to hack: it simply sent a secret code to the car's locking system, which would check it against its own copy of the code and then unlock.
An attacker could trivially record the signal sent from the key fob
and use it to unlock the car at any time. This is a simple *replay attack*.

One way to defeat this attack would be to for the fob to encrypt the current date and time
using a key shared with the car. The car would decrypt the message,
check the date and time against its own clock, and unlock if they agreed.
A replay of the message recorded earlier would fail this check.
The drawback of this *timestamp* approach is that it requires an accurate clock in the key fob.
Some protocols do use timestamps, notably [Kerberos](https://web.mit.edu/kerberos/), but usually people do not want the bother of maintaining synchronised clocks.

An alternative way to defeat this attack involves a *challenge-response* protocol, involving three messages.
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

Generally we assume the following scenario:

* a population of *principals* or *agents* $A$, $B$, $\ldots$
* *nonces*, which we assume to be impossible to guess
* *timestamps*, and unstructured data (the message payload)
* the ability to encrypt, decrypt and hash messages
* an *intruder* who can copy, reroute, delete and create messages  

The intruder is almost omnipotent. 
According to the now-prevailing ([Dolev–Yao threat model](https://doi.org/10.1109/TIT.1983.1056650)),
he is even assumed to have the identity of a normal principal, i.e. he has infiltrated the user group.
He can do essentially unlimited amounts of work, but he does not have the power to guess
nonces or to crack encryption.

Because the intruder can delete messages, we can never prove that a protocol terminates.
Our concern is strictly with the **safe** execution of protocols.
We assume that encryption and hashing are perfect on the grounds that
if they were not, no protocol could be secure, and we are concerned about
attacks that bypass encryption.

*Public-key encryption* is expensive, so it is chiefly used to solve the *key distribution problem*—to convey
a fresh shared key to a distant party—rather than to encrypt long messages.
Other protocols are based entirely on keys shared with a *trusted third party*,
which performs key distribution.
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

Unfortunately, there is a flaw with this scheme, which Gavin Lowe discovered in 1996 through his
[pioneering work](https://rdcu.be/cWJBL) on protocol verification using model checking.
Suppose that Alice runs the protocol with a *dishonest* agent $C$ 
("Charlie"). In that case, Charlie can initiate a new run of the protocol
with some $D$, sending along Alice's first message re-encrypted with $\mathit{Kd}$.
By interleaving the two runs, Charlie can use Alice to decrypt the 
second message, thereby completing the run with $D$ 
while masquerading as $A$: a failure of authentication.
(Details of the attack are in Lowe's paper.)
Lowe also showed how to defeat the attack by
a slight change to the protocol's second message:

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

Charlie cannot pass off this message as his own because he cannot replace that $B$ by $C$, 
which is what Alice would expect.

I knew Roger Needham personally and he was jolly annoyed by these observations,
as were other senior security researchers.
This "attack" relies on Alice opening the protocol with a bad guy, Charlie.
While the Dolev–Yao threat model indeed declares that the enemy is one of the agents, 
the Needham–Schroeder paper (written five years earlier), makes weaker assumptions. 
As they clearly state at the start of [their paper](https://doi.org/10.1145/359657.359659), 
the intruder "only" controls the network:

> We assume that an intruder can interpose a computer in all communication paths, and thus can alter or copy parts of messages, replay messages, or emit false material. While this may seem an extreme view, it is the only safe one when designing authentication protocols.

But he does not have the identity of an agent, and in fact

> Our viewpoint throughout is to provide authentication services to principals that choose to communicate securely. 

Lowe's attack is not possible under this weaker threat model.
Roger's point is that his protocol **achieves what it set out to achieve**.
Verification is meaningless unless you are explicit about what you are
trying to prove.
The Needham–Schroeder paper declared its assumptions, 
but almost nobody seems to have noticed. It is enough
to note that while the protocol fails under the now widely accepted Dolev–Yao model, 
it is correct according to its own design criteria.

### Plainly bogus crypto protocol attacks

The security community puts a premium on new protocol attacks, 
which has given the protocol verification community perverse incentives
to find impossible "attacks".
One trend was to ignore message types (agent names, nonces, keys, etc.).
The standard attacking technique is to splice together fragments of
prior messages to create a new message that will appear to an honest agent
as having the correct form. This can be done for real.
But examples I've seen included two nonces $(\mathit{Na}, \mathit{Nb})$
stuffed into a field where a single nonce is expected, 
or a key where a nonce is expected. And yet it's impossible for two nonces to have the same size as a single nonce. (These are fixed-width bit fields.)
It's highly unlikely that a nonce will have the same size as a key.

I once attended a conference where a student presented his work, culminating
in an "attack" involving random junk being shoved into a timestamp field. Not only would the bit lengths differ; 
the timestamp check would undoubtedly fail. 
The student mentioned that his attack had been accepted to a database of
protocol attacks used by researchers to evaluate verifiers.

Questions were invited from the floor, but I elected to keep my
mouth shut. No point embarrassing a student.

### Proofs of broken protocols

The verification community puts a premium on proofs, so it has the opposite perverse incentives.
Early on I [verified a recursive authentication protocol](https://www.cl.cam.ac.uk/~lp15/papers/Auth/jcs.pdf), attracting a lot of attention
because it could mutually authenticate an arbitrarily large group of principals
and could involve arbitrarily many messages.
A quirk of the protocol was that it avoided the use of encryption in order to evade American export controls,
using instead exclusive-or with a random-looking quantity.
Having no means to reason about exclusive-or, I ignored this aspect (which I regarded as rather silly),
verifying instead what I regarded as the *real* protocol.

Unfortunately, the exclusive-or version turned out to be absolutely broken.
If any one of the principals decides to cheat, they can obtain all the session keys that were distributed
in that run. Ryan and Schneider, aware of my proof, [pointed out that](https://doi.org/10.1016/S0020-0190(97)00180-4)
verification of an abstract security protocol does not imply correctness of implementations,
even if the implementation of a particular abstraction (encryption) seems to be correct in isolation.
Correctness properties do not seem to compose when it comes to security.

On the same theme: I [proved the correctness](https://dl.acm.org/doi/10.1145/322510.322530) of a fairly abstract version of
Transport Layer Security. And yet there exist numerous broken implementations of TLS 
and of its predecessor, SSL.

### What about the real world?

Back in 1997, while attending the Computer Security Foundations Workshop, I was buttonholed by [Robert Morris](https://en.wikipedia.org/wiki/Robert_Morris_(cryptographer)), who at the time was Chief Scientist of the [National Security Agency](https://www.nsa.gov). "Tell me something interesting!"

I must have told him about my work.
He then remarked that real-world protocols did not at all resemble the ones discussed at the Workshop, saying that nobody even used nonces. (If that was true back then, it is certainly true no longer: 
protocols such as TLS definitely use nonces.) And he said, "Never forget the three B's: Burglary, Bribery and Blackmail." None of these, however, are relevant to the world of cryptographic protocols.
