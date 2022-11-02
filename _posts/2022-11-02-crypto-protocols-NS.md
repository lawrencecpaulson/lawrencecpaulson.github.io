---
layout: post
title:  "Verifying cryptographic protocols, II: a simple example"
usemathjax: true
tags: [general,verification]
---

[Not long ago]({% post_url 2022-10-19-crypto-protocols %})
I wrote about cryptographic protocols and their verification.
In this post, we shall see a simple example: the famous
[Needham-Schroeder public key protocol](https://en.wikipedia.org/wiki/Needham–Schroeder_protocol) and its verification using Isabelle/HOL.
The protocol will be the version as corrected by Lowe: the original
provides weaker guarantees and is harder to reason about.
Only highlights can be shown here. The proofs rely on a lot of formal machinery,
which is described in the [journal paper](https://doi.org/10.3233/JCS-1998-61-205)
(also available [here](https://www.cl.cam.ac.uk/~lp15/papers/Auth/jcs.pdf)).
For many people, crypto protocol verification rather than Isabelle
seems to be my main research achievement, and yet they can't really be separated:
these techniques don't seem to be reproducible in those proof assistants that have
weaker automation, namely, all of them.
I know that an attempt was made using a Certain Verification System.

### Messages and operations on them

[Lowe's work](https://rdcu.be/cWJBL) was the starting point
for much of the work on protocol verification undertaken during the late
1990s, and sometimes it was even acknowledged.
It completely superseded earlier work on authentication logics [such as BAN](https://doi.org/10.1145/77648.77649),
which although celebrated at first, didn't yield reliable results.
In particular, BAN validates the incorrect version of the protocol discussed here.

First, we set up a common framework for analysing security protocols in general.
The principals or agents consist of a trusted *authentication server* (required by many protocols), infinitely many friendly agents, and the intruder or Spy.

<pre class="source">
<span class="keyword1 command">datatype</span> agent <span class="main">=</span> Server <span class="main">|</span> Friend <span class="quoted">nat</span> <span class="main">|</span> Spy</pre>

Messages are constructed by hashing, concatenation or encryption over
the four primitive message elements: agent names, etc.

<pre class="source">
<span class="keyword1 command">datatype</span><span>
     </span>msg <span class="main">=</span> Agent  <span class="quoted">agent</span>     <span class="comment1"><span>― ‹</span>Agent names<span>›</span></span><span>
         </span><span class="main">|</span> Number <span class="quoted">nat</span>       <span class="comment1"><span>― ‹</span><span>Ordinary integers, timestamps, ...</span><span>›</span></span><span>
         </span><span class="main">|</span> Nonce  <span class="quoted">nat</span>       <span class="comment1"><span>― ‹</span>Unguessable nonces<span>›</span></span><span>
         </span><span class="main">|</span> Key    <span class="quoted">key</span>       <span class="comment1"><span>― ‹</span>Crypto keys<span>›</span></span><span>
         </span><span class="main">|</span> Hash   <span class="quoted">msg</span>       <span class="comment1"><span>― ‹</span>Hashing<span>›</span></span><span>
         </span><span class="main">|</span> MPair  <span class="quoted">msg</span> <span class="quoted">msg</span>   <span class="comment1"><span>― ‹</span>Compound messages<span>›</span></span><span>
         </span><span class="main">|</span> Crypt  <span class="quoted">key</span> <span class="quoted">msg</span>   <span class="comment1"><span>― ‹</span><span>Encryption, public- or shared-key</span><span>›</span></span></pre>

The formalisation of crypto keys is omitted here. Briefly: keys are integers
and every key has an inverse, which in the case of shared-key encryption
is identical to the key itself. No encryption algorithms are formalised.

Several operators are defined inductively to specify what can be derived
from a set of (presumably intercepted) messages.
For reasoning about secrecy, `analz` specifies the set of message components that can be extracted from a given set.
The body of an encrypted message becomes available
if the decryption key is available.

<pre class="source">
<span class="keyword1 command">inductive_set</span><span>
  </span><span class="entity">analz</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>msg</span> set</span> <span class="main">⇒</span> msg set<span>"</span><span>
  </span><span class="keyword2 keyword">for</span> <span class="entity">H</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>msg</span> set</span><span>"</span><span>
  </span><span class="keyword2 keyword">where</span><span>
    </span>Inj <span class="main">[</span><span class="operator">intro</span><span class="main">,</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="free bound entity">X</span> <span class="main">∈</span></span> <span class="free">H</span> <span class="main">⟹</span> <span class="free bound entity">X</span> <span class="main">∈</span></span> <span class="free">analz</span> <span class="free">H</span><span>"</span><span>
  </span><span class="main">|</span> Fst<span class="main">:</span>     <span class="quoted"><span class="quoted"><span>"</span><span class="main">⦃</span><span class="free bound entity">X</span><span class="main">,</span><span class="free bound entity">Y</span><span class="main">⦄</span> <span class="main">∈</span></span> <span class="free">analz</span> <span class="free">H</span> <span class="main">⟹</span> <span class="free bound entity">X</span> <span class="main">∈</span></span> <span class="free">analz</span> <span class="free">H</span><span>"</span><span>
  </span><span class="main">|</span> Snd<span class="main">:</span>     <span class="quoted"><span class="quoted"><span>"</span><span class="main">⦃</span><span class="free bound entity">X</span><span class="main">,</span><span class="free bound entity">Y</span><span class="main">⦄</span> <span class="main">∈</span></span> <span class="free">analz</span> <span class="free">H</span> <span class="main">⟹</span> <span class="free bound entity">Y</span> <span class="main">∈</span></span> <span class="free">analz</span> <span class="free">H</span><span>"</span><span>
  </span><span class="main">|</span> Decrypt<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">⟦</span>Crypt</span> <span class="free bound entity">K</span> <span class="free bound entity">X</span> <span class="main">∈</span></span> <span class="free">analz</span> <span class="free">H</span><span class="main">;</span> Key<span class="main">(</span>invKey <span class="free bound entity">K</span><span class="main">)</span> <span class="main">∈</span> <span class="free">analz</span> <span class="free">H</span><span class="main">⟧</span> <span class="main">⟹</span> <span class="free bound entity">X</span> <span class="main">∈</span> <span class="free">analz</span> <span class="free">H</span><span>"</span>
</pre>

The function `parts` (omitted here) is an over-approximation of `analz`,
defined similarly except that decryption does not require a key.
It is useful for reasoning about *all* secrets that have been communicated,
whereas `analz` is for reasoning about secrets that are no longer secret.

The function `synth` describes the set of messages that could be synthesised
from a given set of message components.
It is here that the "unguessable" property of keys and nonces
is formalised. All numbers are guessable
(this makes sense for small integers, and timestamps).
To create an encrypted message, you need the encryption key.

<pre class="source">
<span class="keyword1 command">inductive_set</span><span>
  </span><span class="entity">synth</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>msg</span> set</span> <span class="main">=&gt;</span> msg set<span>"</span><span>
  </span><span class="keyword2 keyword">for</span> <span class="entity">H</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>msg</span> set</span><span>"</span><span>
  </span><span class="keyword2 keyword">where</span><span>
    </span>Inj    <span class="main">[</span><span class="operator">intro</span><span class="main">]</span><span class="main">:</span>   <span class="quoted"><span class="quoted"><span>"</span><span class="free bound entity">X</span> <span class="main">∈</span></span> <span class="free">H</span> <span class="main">⟹</span> <span class="free bound entity">X</span> <span class="main">∈</span></span> <span class="free">synth</span> <span class="free">H</span><span>"</span><span>
  </span><span class="main">|</span> Agent  <span class="main">[</span><span class="operator">intro</span><span class="main">]</span><span class="main">:</span>   <span class="quoted"><span class="quoted"><span>"</span>Agent</span> <span class="free bound entity">agt</span> <span class="main">∈</span></span> <span class="free">synth</span> <span class="free">H</span><span>"</span><span>
  </span><span class="main">|</span> Number <span class="main">[</span><span class="operator">intro</span><span class="main">]</span><span class="main">:</span>   <span class="quoted"><span class="quoted"><span>"</span>Number</span> <span class="free bound entity">n</span>  <span class="main">∈</span></span> <span class="free">synth</span> <span class="free">H</span><span>"</span><span>
  </span><span class="main">|</span> Hash   <span class="main">[</span><span class="operator">intro</span><span class="main">]</span><span class="main">:</span>   <span class="quoted"><span class="quoted"><span>"</span><span class="free bound entity">X</span> <span class="main">∈</span></span> <span class="free">synth</span> <span class="free">H</span> <span class="main">⟹</span> Hash</span> <span class="free bound entity">X</span> <span class="main">∈</span> <span class="free">synth</span> <span class="free">H</span><span>"</span><span>
  </span><span class="main">|</span> MPair  <span class="main">[</span><span class="operator">intro</span><span class="main">]</span><span class="main">:</span>   <span class="quoted"><span class="quoted"><span>"</span><span class="main">⟦</span><span class="free bound entity">X</span> <span class="main">∈</span></span> <span class="free">synth</span> <span class="free">H</span><span class="main">;</span>  <span class="free bound entity">Y</span> <span class="main">∈</span></span> <span class="free">synth</span> <span class="free">H</span><span class="main">⟧</span> <span class="main">⟹</span> <span class="main">⦃</span><span class="free bound entity">X</span><span class="main">,</span><span class="free bound entity">Y</span><span class="main">⦄</span> <span class="main">∈</span> <span class="free">synth</span> <span class="free">H</span><span>"</span><span>
  </span><span class="main">|</span> Crypt  <span class="main">[</span><span class="operator">intro</span><span class="main">]</span><span class="main">:</span>   <span class="quoted"><span class="quoted"><span>"</span><span class="main">⟦</span><span class="free bound entity">X</span> <span class="main">∈</span></span> <span class="free">synth</span> <span class="free">H</span><span class="main">;</span>  Key</span><span class="main">(</span><span class="free bound entity">K</span><span class="main">)</span> <span class="main">∈</span> <span class="free">H</span><span class="main">⟧</span> <span class="main">⟹</span> Crypt <span class="free bound entity">K</span> <span class="free bound entity">X</span> <span class="main">∈</span> <span class="free">synth</span> <span class="free">H</span><span>"</span>
</pre>

Innumerable properties are for these operators by simple inductions.
They turn out to be idempotent and monotonic.
Identities are proved to simplify the arguments of the operators, for example to
pull out inserted elements. We can pull out an inserted nonce, for example:

<pre class="source">
<span class="keyword1 command">lemma</span> analz_insert_Nonce <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span><span>
  </span><span class="quoted"><span class="quoted"><span>"</span>analz</span> <span class="main">(</span>insert</span> <span class="main">(</span>Nonce <span class="free">N</span><span class="main">)</span> <span class="free">H</span><span class="main">)</span> <span class="main">=</span> insert <span class="main">(</span>Nonce <span class="free">N</span><span class="main">)</span> <span class="main">(</span>analz <span class="free">H</span><span class="main">)</span><span>"</span>
</pre>

There is no analogous law for inserted keys because keys can be used to decrypt.

Among the more interesting laws is the following, which shows that synthesis
can be decoupled from analysis.
Suitable laws are proved for all combinations of the operators in order to
simplify nested expressions.

<pre class="source">
<span class="keyword1 command">lemma</span> analz_synth <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>analz</span> <span class="main">(</span>synth</span> <span class="free">H</span><span class="main">)</span> <span class="main">=</span> analz <span class="free">H</span> <span class="main">∪</span> synth <span class="free">H</span><span>"</span>
</pre>

The most critical combination is synthesis of analysis,
for that is what the Spy does: break down past traffic,
then combine the components into new messages.
The following theorem allows us to eliminate an occurrence
of such a fake message `X` from the argument of `analz`,
which turns out to provide a general method for
solving the subgoal corresponding to a fake message.

<pre class="source">
<span class="keyword1 command">lemma</span> Fake_analz_insert<span class="main">:</span><span>
  </span><span class="quoted"><span class="quoted"><span>"</span><span class="free">X</span> <span class="main">∈</span></span> synth</span> <span class="main">(</span>analz <span class="free">G</span><span class="main">)</span> <span class="main">⟹</span> analz <span class="main">(</span>insert <span class="free">X</span> <span class="free">H</span><span class="main">)</span> <span class="main">⊆</span> synth <span class="main">(</span>analz <span class="free">G</span><span class="main">)</span> <span class="main">∪</span> analz <span class="main">(</span><span class="free">G</span> <span class="main">∪</span> <span class="free">H</span><span class="main">)</span><span>"</span>
</pre>

### Events, traces and other basic notions

Protocols are formalised with respect to a "God's eye" trace model.
The trace holds all message send attempts from the beginning of time, including
multiple protocol runs possibly interleaved with any number of parties.

<pre class="source">
<span class="keyword1 command">datatype</span><span>
  </span>event <span class="main">=</span> Says  <span class="quoted">agent</span> <span class="quoted">agent</span> <span class="quoted">msg</span><span>
        </span><span class="main">|</span> Gets  <span class="quoted">agent</span>       <span class="quoted">msg</span><span>
        </span><span class="main">|</span> Notes <span class="quoted">agent</span>       <span class="quoted">msg</span>
</pre>

The event `Says A B X` represents the attempt by agent `A` to send message `X` to agent `B`.
This was at one point the only event in the model.
Later I introduced `Notes`, to represent the local storage of an agent and also
information leakage outside the protocol.
[Giampaolo Bella](https://www.dmi.unict.it/giamp/), one of my PhD students, introduced `Gets` to signify the reception of a message
by a specific agent, who (because the Spy controls the network)
has no way of knowing who the true sender was.
Giampaolo felt that the explicit `Gets` event made for clearer protocol specifications.
Giampaolo went on to do an enormous amount of work on protocol verification,
including timestamp-based protocols, smartcard protocols and other advanced configurations, and even [wrote a book](https://link.springer.com/book/10.1007/978-3-540-68136-6) on the subject.
(Later still, [Jean Martina](https://jeanmartina.paginas.ufsc.br)
investigated multicast protocols.)
But I never updated the Needham-Schroeder formalisation, so we don't need
`Gets` here.

The basic model includes several other primitives, which can be briefly described as follows:
- `bad`: the set of compromised agents (their keys are known to the Spy)
- `used`: the set of all message components ever sent, whether visible or not
- `spies`: the set of message components visible to the Spy
- `pubEK`: the public encryption key of a given agent


### Formalising the protocol

The [earlier post]({% post_url 2022-10-19-crypto-protocols %})
described the Needham–Schroeder public key protocol and mentioned the flaw
found by Gavin Lowe. The corrected protocol mentions $B$ in message 2:

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
  &2.&\quad  B\to A  &: \comp{\Na,\Nb,B}_{\Ka} \\
  &3.&\quad  A\to B  &: \comp{\Nb}_{\Kb}
\end{alignat*}$$

A reminder of the notation. Some arbitrary principal "Alice" decides for some reason to run the protocol with some other principal, "Bob" and sends the first message (which contains a fresh random number).
Upon the receipt of what appears to be an instance of message 1, Bob can continue
the protocol by sending message 2 (containing another random number) back to Alice.
Alice, upon receiving message 2, checks that it has the correct form,
which for this version of the protocol involves confirming both her nonce and the name $B$.
If everything is okay, she sends message 3, and if Bob actually receives this message,
he will check for his nonce and that will constitute a successful run.
If any of the messages fail to get through or do not have the required form,
the protocol attempt will simply be abandoned.

We reason informally about such a protocol by saying for example "Bob knows Alice is present
by message 3, when his nonce challenge was correctly returned to him.
Only Alice could have done this, because that nonce was encrypted using her public key."
This is inductive reasoning, so it's not surprising that a cryptographic protocol
can naturally be modelled by an inductive definition,
effectively an operational semantics.


<pre class="source">
<span class="keyword1 command">inductive_set</span> <span class="entity">ns_public</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span>event</span> list</span> set<span>"</span><span>
  </span><span class="keyword2 keyword">where</span><span>
   </span>Nil<span class="main">:</span>  <span class="quoted"><span class="quoted"><span>"</span><span class="main">[]</span></span> <span class="main">∈</span></span> <span class="free">ns_public</span><span>"</span><span>
   </span><span class="comment1"><span>― ‹</span>Initial trace is empty<span>›</span></span><span>
 </span><span class="main">|</span> Fake<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">⟦</span><span class="free bound entity">evsf</span> <span class="main">∈</span></span> <span class="free">ns_public</span><span class="main">;</span>  <span class="free bound entity">X</span> <span class="main">∈</span></span> synth <span class="main">(</span>analz <span class="main">(</span>spies <span class="free bound entity">evsf</span><span class="main">)</span><span class="main">)</span><span class="main">⟧</span><span>
          </span><span class="main">⟹</span> Says Spy <span class="free bound entity">B</span> <span class="free bound entity">X</span>  <span class="main">#</span> <span class="free bound entity">evsf</span> <span class="main">∈</span> <span class="free">ns_public</span><span>"</span><span>
   </span><span class="comment1"><span>― ‹</span>The spy can say almost anything.<span>›</span></span><span>
 </span><span class="main">|</span> NS1<span class="main">:</span>  <span class="quoted"><span class="quoted"><span>"</span><span class="main">⟦</span><span class="free bound entity">evs1</span> <span class="main">∈</span></span> <span class="free">ns_public</span><span class="main">;</span>  Nonce</span> <span class="free bound entity">NA</span> <span class="main">∉</span> used <span class="free bound entity">evs1</span><span class="main">⟧</span><span>
          </span><span class="main">⟹</span> Says <span class="free bound entity">A</span> <span class="free bound entity">B</span> <span class="main">(</span>Crypt <span class="main">(</span>pubEK <span class="free bound entity">B</span><span class="main">)</span> <span class="main">⦃</span>Nonce <span class="free bound entity">NA</span><span class="main">,</span> Agent <span class="free bound entity">A</span><span class="main">⦄</span><span class="main">)</span><span>
                </span><span class="main">#</span> <span class="free bound entity">evs1</span>  <span class="main">∈</span>  <span class="free">ns_public</span><span>"</span><span>
   </span><span class="comment1"><span>― ‹</span><span>Alice initiates a protocol run, sending a nonce to Bob</span><span>›</span></span><span>
 </span><span class="main">|</span> NS2<span class="main">:</span>  <span class="quoted"><span class="quoted"><span>"</span><span class="main">⟦</span><span class="free bound entity">evs2</span> <span class="main">∈</span></span> <span class="free">ns_public</span><span class="main">;</span>  Nonce</span> <span class="free bound entity">NB</span> <span class="main">∉</span> used <span class="free bound entity">evs2</span><span class="main">;</span><span>
           </span>Says <span class="free bound entity">A'</span> <span class="free bound entity">B</span> <span class="main">(</span>Crypt <span class="main">(</span>pubEK <span class="free bound entity">B</span><span class="main">)</span> <span class="main">⦃</span>Nonce <span class="free bound entity">NA</span><span class="main">,</span> Agent <span class="free bound entity">A</span><span class="main">⦄</span><span class="main">)</span> <span class="main">∈</span> set <span class="free bound entity">evs2</span><span class="main">⟧</span><span>
          </span><span class="main">⟹</span> Says <span class="free bound entity">B</span> <span class="free bound entity">A</span> <span class="main">(</span>Crypt <span class="main">(</span>pubEK <span class="free bound entity">A</span><span class="main">)</span> <span class="main">⦃</span>Nonce <span class="free bound entity">NA</span><span class="main">,</span> Nonce <span class="free bound entity">NB</span><span class="main">,</span> Agent <span class="free bound entity">B</span><span class="main">⦄</span><span class="main">)</span><span>
                </span><span class="main">#</span> <span class="free bound entity">evs2</span>  <span class="main">∈</span>  <span class="free">ns_public</span><span>"</span><span>
   </span><span class="comment1"><span>― ‹</span><span>Bob responds to Alice's message with a further nonce</span><span>›</span></span><span>
 </span><span class="main">|</span> NS3<span class="main">:</span>  <span class="quoted"><span class="quoted"><span>"</span><span class="main">⟦</span><span class="free bound entity">evs3</span> <span class="main">∈</span></span> <span class="free">ns_public</span><span class="main">;</span><span>
           </span>Says</span> <span class="free bound entity">A</span>  <span class="free bound entity">B</span> <span class="main">(</span>Crypt <span class="main">(</span>pubEK <span class="free bound entity">B</span><span class="main">)</span> <span class="main">⦃</span>Nonce <span class="free bound entity">NA</span><span class="main">,</span> Agent <span class="free bound entity">A</span><span class="main">⦄</span><span class="main">)</span> <span class="main">∈</span> set <span class="free bound entity">evs3</span><span class="main">;</span><span>
           </span>Says <span class="free bound entity">B'</span> <span class="free bound entity">A</span> <span class="main">(</span>Crypt <span class="main">(</span>pubEK <span class="free bound entity">A</span><span class="main">)</span> <span class="main">⦃</span>Nonce <span class="free bound entity">NA</span><span class="main">,</span> Nonce <span class="free bound entity">NB</span><span class="main">,</span> Agent <span class="free bound entity">B</span><span class="main">⦄</span><span class="main">)</span> <span class="main">∈</span> set <span class="free bound entity">evs3</span><span class="main">⟧</span><span>
          </span><span class="main">⟹</span> Says <span class="free bound entity">A</span> <span class="free bound entity">B</span> <span class="main">(</span>Crypt <span class="main">(</span>pubEK <span class="free bound entity">B</span><span class="main">)</span> <span class="main">(</span>Nonce <span class="free bound entity">NB</span><span class="main">)</span><span class="main">)</span> <span class="main">#</span> <span class="free bound entity">evs3</span> <span class="main">∈</span> <span class="free">ns_public</span><span>"</span><span>
   </span><span class="comment1"><span>― ‹</span>Alice proves her existence by sending <span class="antiquoted"><span class="antiquote">@{</span><span class="operator">term</span> <span class="quoted free">NB</span><span class="antiquote">}</span></span> back to Bob.<span>›</span></span>
</pre>

We formalise a protocol by specifying the possible traces of messages that could be sent
over the network. Starting with the empty trace our possibilities are any of the three protocol messages or a Fake message from the Spy, using the `synth` and `analz` operators
to generate arbitrary messages.
Some aspects of the formalisation of the protocol messages deserve comment.

1. Protocol message `NS1`, says that any trace can be extended
by a message containing a nonce `NA` that has never appeared before.
That knowledge is not available, but the constraint can be achieved
with high probability simply by generating a random number.
2. Message `NS2` extends the trace (including another random number)
provided a suitable copy of message 1 has already appeared.
The decryption of that message is implicit in requiring that it be encrypted
with B's public key. The sender of the message 1 is written as A'
because it is not possible to know who the true sender of a message is
(ascertaining this is the very purpose of authentication).
3. Again for message `NS3`, the comparison between the instance message 2
just received and the message 1 originally sent is implicit in the formulation
itself, with no decryption or comparison operations necessary.

It's nice that the formal specification is so close to the conventional notation.
It's not cluttered with any implementation details. That's also a reminder
that the proof offers no guarantees against implementation errors.

### Some properties proved of this protocol

Our protocol model only allows the proof of *safety properties*, i.e.,
that all executions are safe. It cannot prove *liveness properties*,
because the Spy has the power to prevent anything from happening by intercepting
all messages. With this sort of model, if you make a mistake and specify a protocol
that simply cannot run (typically because the message formats aren't consistent),
then all the safety properties will hold vacuously. Therefore the first thing to do
is run a little sanity check. The following result isn't interesting except to show
that traces exist in which the final protocol message is actually sent.
The proof involves simply joining up the protocol rules in the correct order
and checking that the side conditions can be satisfied.

<pre class="source">
<span class="keyword1 command">lemma</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">∃</span></span><span class="bound">NB</span><span class="main">.</span></span> <span class="main">∃</span><span class="bound">evs</span> <span class="main">∈</span> ns_public<span class="main">.</span> Says <span class="free">A</span> <span class="free">B</span> <span class="main">(</span>Crypt <span class="main">(</span>pubEK <span class="free">B</span><span class="main">)</span> <span class="main">(</span>Nonce <span class="bound">NB</span><span class="main">)</span><span class="main">)</span> <span class="main">∈</span> set <span class="bound">evs</span><span>"</span>
</pre>

The objectives of the protocol are sufficiently vague
("Alice and Bob are authenticated to one another") that we need to decide for ourselves what to prove. The following are technical properties that turned out to be necessary
in order to prove more clear-cut properties about secrecy.
As so often happens in machine proofs, they look too easy to bother with.
First we prove that it is impossible for a nonce used in message 1
to be identical to announce used in message 2 (intuitively, because they are chosen randomly).

<pre class="source">
<span class="keyword1 command">lemma</span> no_nonce_NS1_NS2<span class="main">:</span><span>
      </span><span class="quoted quoted"><span>"</span><span class="main">⟦</span><span class="free">evs</span> <span class="main">∈</span></span> ns_public<span class="main">;</span><span>
        </span>Crypt <span class="main">(</span>pubEK <span class="free">C</span><span class="main">)</span> <span class="main">⦃</span><span class="free">NA'</span><span class="main">,</span> Nonce <span class="free">NA</span><span class="main">,</span> Agent <span class="free">D</span><span class="main">⦄</span> <span class="main">∈</span> parts <span class="main">(</span>spies <span class="free">evs</span><span class="main">)</span><span class="main">;</span><span>
        </span>Crypt <span class="main">(</span>pubEK <span class="free">B</span><span class="main">)</span> <span class="main">⦃</span>Nonce <span class="free">NA</span><span class="main">,</span> Agent <span class="free">A</span><span class="main">⦄</span> <span class="main">∈</span> parts <span class="main">(</span>spies <span class="free">evs</span><span class="main">)</span><span class="main">⟧</span><span>
       </span><span class="main">⟹</span> Nonce <span class="free">NA</span> <span class="main">∈</span> analz <span class="main">(</span>spies <span class="free">evs</span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">induct</span> <span class="quasi_keyword">rule</span><span class="main main">:</span> ns_public.induct<span class="main">)</span> <span class="main">(</span><span class="operator">auto</span> <span class="quasi_keyword">intro</span><span class="main main">:</span> analz_insertI<span class="main">)</span>
</pre>

Next comes what I have called a unicity property: that a particular nonce uniquely
identifies all the message components bound up with it. This fact relies on the assumption
that the nonce in question is not known to the Spy, who could otherwise do anything with it.
Honest agents generate a fresh nonce every time, hence this property.

<pre class="source">
<span class="keyword1 command">lemma</span> unique_NA<span class="main">:</span><span>
  </span><span class="keyword2 keyword">assumes</span> NA<span class="main">:</span> <span class="quoted quoted"><span>"</span>Crypt</span><span class="main">(</span>pubEK <span class="free">B</span><span class="main">)</span>  <span class="main">⦃</span>Nonce <span class="free">NA</span><span class="main">,</span> Agent <span class="free">A</span> <span class="main">⦄</span> <span class="main">∈</span> parts<span class="main">(</span>spies <span class="free">evs</span><span class="main">)</span><span>"</span><span>
              </span><span class="quoted quoted"><span>"</span>Crypt</span><span class="main">(</span>pubEK <span class="free">B'</span><span class="main">)</span> <span class="main">⦃</span>Nonce <span class="free">NA</span><span class="main">,</span> Agent <span class="free">A'</span><span class="main">⦄</span> <span class="main">∈</span> parts<span class="main">(</span>spies <span class="free">evs</span><span class="main">)</span><span>"</span><span>
              </span><span class="quoted quoted"><span>"</span>Nonce</span> <span class="free">NA</span> <span class="main">∉</span> analz <span class="main">(</span>spies <span class="free">evs</span><span class="main">)</span><span>"</span><span>
    </span><span class="keyword2 keyword">and</span> evs<span class="main">:</span> <span class="quoted quoted"><span>"</span><span class="free">evs</span> <span class="main">∈</span></span> ns_public<span>"</span><span>
  </span><span class="keyword2 keyword">shows</span> <span class="quoted quoted"><span>"</span><span class="free">A</span><span class="main">=</span></span><span class="free">A'</span> <span class="main">∧</span> <span class="free">B</span><span class="main">=</span><span class="free">B'</span><span>"</span>
</pre>

The proofs start to get messier, so I prefer to omit some of them.
A dogmatic approach to structured proofs doesn't work in verification generally,
where proof steps can easily generate gigantic subgoals.
And by the way: the reason the trace variable has distinctive names `evs1`,
`evs2`, `evs3` is to make it easy to see which protocol rule we are talking about
in a messy, non-structured induction.

The following theorem is a key protocol objective: Alice's nonce from message 1 will remain
forever secret from the Spy, provided both Alice and Bob are trustworthy.

<pre class="source">
<span class="keyword1 command">theorem</span> Spy_not_see_NA<span class="main">:</span><span>
  </span><span class="keyword2 keyword">assumes</span> NA<span class="main">:</span> <span class="quoted quoted"><span>"</span>Says</span> <span class="free">A</span> <span class="free">B</span> <span class="main">(</span>Crypt<span class="main">(</span>pubEK <span class="free">B</span><span class="main">)</span> <span class="main">⦃</span>Nonce <span class="free">NA</span><span class="main">,</span> Agent <span class="free">A</span><span class="main">⦄</span><span class="main">)</span> <span class="main">∈</span> set <span class="free">evs</span><span>"</span><span>
              </span><span class="quoted quoted"><span>"</span><span class="free">A</span> <span class="main">∉</span></span> bad<span>"</span> <span class="quoted quoted"><span>"</span><span class="free">B</span> <span class="main">∉</span></span> bad<span>"</span><span>
    </span><span class="keyword2 keyword">and</span> evs<span class="main">:</span> <span class="quoted quoted"><span>"</span><span class="free">evs</span> <span class="main">∈</span></span> ns_public<span>"</span><span>
  </span><span class="keyword2 keyword">shows</span> <span class="quoted quoted"><span>"</span>Nonce</span> <span class="free">NA</span> <span class="main">∉</span> analz <span class="main">(</span>spies <span class="free">evs</span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword1 command">using</span> evs NA<span>
</span><span class="keyword1 command">proof</span> <span class="main">(</span><span class="operator">induction</span> <span class="quasi_keyword">rule</span><span class="main main">:</span> ns_public.induct<span class="main">)</span><span>
  </span><span class="keyword3 command">case</span> <span class="main">(</span>Fake <span class="skolem">evsf</span> <span class="skolem">X</span> <span class="skolem">B</span><span class="main">)</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="var quoted var">?case</span><span>
    </span><span class="keyword1 command">by</span> <span class="operator">spy_analz</span><span>
</span><span class="keyword1 command">next</span><span>
  </span><span class="keyword3 command">case</span> <span class="main">(</span>NS2 <span class="skolem">evs2</span> <span class="skolem">NB</span> <span class="skolem">A'</span> <span class="skolem">B</span> <span class="skolem">NA</span> <span class="skolem">A</span><span class="main">)</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="var quoted var">?case</span><span>
    </span><span class="keyword1 command">by</span> <span class="operator">simp</span> <span class="main">(</span><span class="operator">metis</span> Says_imp_analz_Spy analz_into_parts parts.simps unique_NA usedI<span class="main">)</span><span>
</span><span class="keyword1 command">next</span><span>
  </span><span class="keyword3 command">case</span> <span class="main">(</span>NS3 <span class="skolem">evs3</span> <span class="skolem">A</span> <span class="skolem">B</span> <span class="skolem">NA</span> <span class="skolem">B'</span> <span class="skolem">NB</span><span class="main">)</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">show</span> <span class="var quoted var">?case</span><span>
    </span><span class="keyword1 command">by</span> <span class="operator">simp</span> <span class="main">(</span><span class="operator">meson</span> Says_imp_analz_Spy analz_into_parts no_nonce_NS1_NS2<span class="main">)</span><span>
</span><span class="keyword1 command">qed</span> <span class="operator">auto</span>
</pre>

An analogous property can be proved for Bob's nonce from message 2.
It doesn't hold for the original, flawed version of Needham–Schroeder.

The following theorem authenticates Bob to Alice.
More formally, if Alice has sent message 1 and receives a copy of message 2
containing a copy of the nonce that she sent, then it was in fact sent by Bob.

<pre class="source">
<span class="keyword1 command">theorem</span> A_trusts_NS2<span class="main">:</span><span>
     </span><span class="quoted quoted"><span>"</span><span class="main">⟦</span>Says</span> <span class="free">A</span>  <span class="free">B</span> <span class="main">(</span>Crypt<span class="main">(</span>pubEK <span class="free">B</span><span class="main">)</span> <span class="main">⦃</span>Nonce <span class="free">NA</span><span class="main">,</span> Agent <span class="free">A</span><span class="main">⦄</span><span class="main">)</span> <span class="main">∈</span> set <span class="free">evs</span><span class="main">;</span><span>
       </span>Says <span class="free">B'</span> <span class="free">A</span> <span class="main">(</span>Crypt<span class="main">(</span>pubEK <span class="free">A</span><span class="main">)</span> <span class="main">⦃</span>Nonce <span class="free">NA</span><span class="main">,</span> Nonce <span class="free">NB</span><span class="main">,</span> Agent <span class="free">B</span><span class="main">⦄</span><span class="main">)</span> <span class="main">∈</span> set <span class="free">evs</span><span class="main">;</span><span>
       </span><span class="free">A</span> <span class="main">∉</span> bad<span class="main">;</span>  <span class="free">B</span> <span class="main">∉</span> bad<span class="main">;</span>  <span class="free">evs</span> <span class="main">∈</span> ns_public<span class="main">⟧</span><span>
      </span><span class="main">⟹</span> Says <span class="free">B</span> <span class="free">A</span> <span class="main">(</span>Crypt<span class="main">(</span>pubEK <span class="free">A</span><span class="main">)</span> <span class="main">⦃</span>Nonce <span class="free">NA</span><span class="main">,</span> Nonce <span class="free">NB</span><span class="main">,</span> Agent <span class="free">B</span><span class="main">⦄</span><span class="main">)</span> <span class="main">∈</span> set <span class="free">evs</span><span>"</span>
</pre>

And this theorem authenticates Alice to Bob.

<pre class="source">
<span class="keyword1 command">theorem</span> B_trusts_NS3<span class="main">:</span><span>
     </span><span class="quoted quoted"><span>"</span><span class="main">⟦</span>Says</span> <span class="free">B</span> <span class="free">A</span>  <span class="main">(</span>Crypt <span class="main">(</span>pubEK <span class="free">A</span><span class="main">)</span> <span class="main">⦃</span>Nonce <span class="free">NA</span><span class="main">,</span> Nonce <span class="free">NB</span><span class="main">,</span> Agent <span class="free">B</span><span class="main">⦄</span><span class="main">)</span> <span class="main">∈</span> set <span class="free">evs</span><span class="main">;</span><span>
       </span>Says <span class="free">A'</span> <span class="free">B</span> <span class="main">(</span>Crypt <span class="main">(</span>pubEK <span class="free">B</span><span class="main">)</span> <span class="main">(</span>Nonce <span class="free">NB</span><span class="main">)</span><span class="main">)</span> <span class="main">∈</span> set <span class="free">evs</span><span class="main">;</span><span>
       </span><span class="free">A</span> <span class="main">∉</span> bad<span class="main">;</span>  <span class="free">B</span> <span class="main">∉</span> bad<span class="main">;</span>  <span class="free">evs</span> <span class="main">∈</span> ns_public<span class="main">⟧</span><span>
      </span><span class="main">⟹</span> Says <span class="free">A</span> <span class="free">B</span> <span class="main">(</span>Crypt <span class="main">(</span>pubEK <span class="free">B</span><span class="main">)</span> <span class="main">(</span>Nonce <span class="free">NB</span><span class="main">)</span><span class="main">)</span> <span class="main">∈</span> set <span class="free">evs</span><span>"</span>
</pre>

The last two properties above guarantee to Alice and Bob that the other person
indeed participated in the protocol. The secrecy properties assure them
that the nonces they exchanged are available to them alone.
A practical application of this protocol might involve calculating a session key
from those nonces in order to transmit a serious amount of data.

### Postscript

It's careless to talk about "verifying" anything
unless it has a definitive formal specification.
A cryptographic protocol — the last time I looked, admittedly quite a while ago —
is typically proposed through an
[RFC](https://en.wikipedia.org/wiki/Request_for_Comments),
a mixture of prose and technical diagrams showing the formats
of messages down to bitfield boundaries.
The aims will be taken for granted ("establish secure communications")
with little discussion of specific protocol objectives
and no abstract protocol design independent of its machine implementation.
As discussed in the [earlier post]({% post_url 2022-10-19-crypto-protocols %}),
ambiguity about the original protocol's
security assumptions resulted in disagreements among experts as to whether it was
correct or not.

If you check the [corresponding formal development](https://isabelle.in.tum.de/dist/library/HOL/HOL-Auth/NS_Public.html)
online, you will find much uglier proofs than those shown here.
I took the opportunity to beautify them,
but the new proofs will not be visible until the release of
Isabelle2023.

My colleagues and I [wrote numerous papers](https://www.cl.cam.ac.uk/~lp15/papers/Auth/index.html) on protocol verification.
But my proofs are too labour intensive.
Others have taken the field forward, and crypto protocol verification
is today done almost exclusively by fully automatic techniques.
