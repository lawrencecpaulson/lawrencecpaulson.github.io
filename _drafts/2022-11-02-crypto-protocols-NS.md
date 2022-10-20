---
layout: post
title:  "Verifying cryptographic protocols, II: A Simple Example"
usemathjax: true
tags: [general,verification]
---

[Not long ago]({% post_url 2022-10-19-crypto-protocols %})
I wrote about cryptographic protocols and their verification.
In this post, we shall see a simple example: the famous
Needham-Schroeder public key protocol and its verification using Isabelle/HOL.
The protocol will be the version as corrected by Lowe, because the original
provide weaker guarantees and is harder to reason about.
Only highlights can be shown here. The proofs rely on a lot of formal machinery,
which is described in the [journal paper](https://doi.org/10.3233/JCS-1998-61-205) 
(also available [here](https://www.cl.cam.ac.uk/~lp15/papers/Auth/jcs.pdf)).
For many people, crypto protocol verification rather than Isabelle
seems to be my main research achievement, and yet they can't really be separated:
these techniques don't seem to be reproducible in proof assistants that have
weaker automation, namely, all of them.
I know that an attempt was made using a Certain Verification System.
But even my proofs are too labour intensive, and crypto protocol verification
is today done almost exclusively by fully automatic techniques.

### Messages and operations on them

[Lowe's work](https://rdcu.be/cWJBL) was the starting point
for much of the work on protocol verification undertaken during the late
1990s, though it was not always credited.
It completely superseded earlier work on [authentication logics](https://doi.org/10.1145/77648.77649),
which although celebrated at first, doesn't seem to yield reliable results.

The principals or agents consist of a trusted *authentication server* (required by many protocols), infinitely many friendly agents, and the intruder or Sanpy.

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
For reasoning about secrecy, `analz` is particularly important.
It specifies the set of message components that can be extracted from a given set,
and in particular, the body of an encrypted message becomes available
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
It is useful for reasoning about secrets that have been communicated,
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

Innumerable properties can be proved for these operators by simple inductions.
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
It is effectively an operational semantics.
The trace holds all message send attempts from the beginning of time, including
multiprotocol runs possibly interleaved with any number of parties.

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
But I never updated the Needham-Schroeder formalisation, so we don't need
`Gets` here.

The basic model includes several other primitives, which can be briefly described as follows:
- `bad`: the set of compromised agents (their keys are known to the Spy)
- `used`: the set of all message components ever sent, whether visible or not
- `knows`: the set of all message components visible to a given agent (we only care about the Spy)
- `pubEK`: the public encryption key of a given agent


### The protocol

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

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>


<pre class="source">
</pre>

<pre class="source">
</pre>


<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>


<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>


<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>


<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>


<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>



<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>


<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

<pre class="source">
</pre>

