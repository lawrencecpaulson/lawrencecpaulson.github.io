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
which is described in the [journal paper](https://content.iospress.com/articles/journal-of-computer-security/jcs102) 
(also available [here](https://www.cl.cam.ac.uk/~lp15/papers/Auth/jcs.pdf)).
For many people, crypto protocol verification rather than Isabelle
seems to be my main research achievement, and yet they can't really be separated:
these techniques don't seem to be reproducible in proof assistants that have
weaker automation, namely, all of them.
I know that an attempt was made using a Certain Verification System.
But all these proofs are too labour intensive, and crypto protocol verification
is today done almost exclusively by fully automatic techniques.

### The basic formal framework

Lowe's work, whether acknowledged or not, was the starting point
for much of the work on protocol verification undertaken during the late
1990s. It completely superseded earlier work on authentication logics,
which although celebrated at first, don't seem to yield reliable results.

<pre class="source">
<span class="keyword1 command">datatype</span>  <span class="comment1"><span>― ‹</span>We allow any number of friendly agents<span>›</span></span><span>
  </span>agent <span class="main">=</span> Server <span class="main">|</span> Friend <span class="quoted">nat</span> <span class="main">|</span> Spy</pre>


<pre class="source">
<span class="keyword1 command">datatype</span><span>
     </span>msg <span class="main">=</span> Agent  <span class="quoted">agent</span>     <span class="comment1"><span>― ‹</span>Agent names<span>›</span></span><span>
         </span><span class="main">|</span> Number <span class="quoted">nat</span>       <span class="comment1"><span>― ‹</span><span>Ordinary integers, timestamps, ...</span><span>›</span></span><span>
         </span><span class="main">|</span> Nonce  <span class="quoted">nat</span>       <span class="comment1"><span>― ‹</span>Unguessable nonces<span>›</span></span><span>
         </span><span class="main">|</span> Key    <span class="quoted">key</span>       <span class="comment1"><span>― ‹</span>Crypto keys<span>›</span></span><span>
         </span><span class="main">|</span> Hash   <span class="quoted">msg</span>       <span class="comment1"><span>― ‹</span>Hashing<span>›</span></span><span>
         </span><span class="main">|</span> MPair  <span class="quoted">msg</span> <span class="quoted">msg</span>   <span class="comment1"><span>― ‹</span>Compound messages<span>›</span></span><span>
         </span><span class="main">|</span> Crypt  <span class="quoted">key</span> <span class="quoted">msg</span>   <span class="comment1"><span>― ‹</span><span>Encryption, public- or shared-key</span><span>›</span></span></pre>

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

<pre class="source">
<span class="keyword1 command">lemma</span> analz_synth <span class="main">[</span><span class="operator">simp</span><span class="main">]</span><span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span>analz</span> <span class="main">(</span>synth</span> <span class="free">H</span><span class="main">)</span> <span class="main">=</span> analz <span class="free">H</span> <span class="main">∪</span> synth <span class="free">H</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> Un_empty_right analz_synth_Un<span class="main">)</span>
</pre>

<pre class="source">
<span class="keyword1 command">lemma</span> Fake_analz_insert<span class="main">:</span><span>
  </span><span class="quoted"><span class="quoted"><span>"</span><span class="free">X</span> <span class="main">∈</span></span> synth</span> <span class="main">(</span>analz <span class="free">G</span><span class="main">)</span> <span class="main">⟹</span><span>
      </span>analz <span class="main">(</span>insert <span class="free">X</span> <span class="free">H</span><span class="main">)</span> <span class="main">⊆</span> synth <span class="main">(</span>analz <span class="free">G</span><span class="main">)</span> <span class="main">∪</span> analz <span class="main">(</span><span class="free">G</span> <span class="main">∪</span> <span class="free">H</span><span class="main">)</span><span>"</span><span>
  </span><span class="keyword1 command">by</span> <span class="main">(</span><span class="operator">metis</span> UnCI Un_commute Un_upper1 analz_analz_Un analz_mono analz_synth_Un insert_subset<span class="main">)</span>
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

