---
layout: post
title:  "On the Infinite"
usemathjax: true 
tags: []
---

[Infinity](https://plato.stanford.edu/entries/infinity/)

Hilbert's [*On the Infinite*](/papers/on-the-infinite.pdf)

[YouTube video](https://youtu.be/OxGsU8oIWjY) 
of the Hotel and uncountable infinity

[story of Hilbert's Hotel](https://arxiv.org/abs/1403.0059)
(and the ball)

[NSA]({% post_url 2022-08-10-Nonstandard_Analysis %})

[Cantor's theorem](https://platonicrealms.com/encyclopedia/Cantors-Theorem)

[Cantor's diagonal argument](https://en.wikipedia.org/wiki/Cantor's_diagonal_argument)

<pre class="source">
<span class="keyword1 command">theorem</span> Cantor<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">∄</span><span class="bound">f</span> <span class="main">::</span> <span class="tfree">'a</span> <span class="main">⇒</span> <span class="tfree">'a</span> set</span><span class="main">.</span> <span class="main">∀</span></span><span class="bound">A</span><span class="main">.</span> <span class="main">∃</span><span class="bound">x</span><span class="main">.</span> <span class="bound">A</span> <span class="main">=</span> <span class="bound">f</span> <span class="bound">x</span><span>"</span><span>
</span><span class="keyword1 command">proof</span><span>
  </span><span class="keyword3 command">assume</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">∃</span></span><span class="bound">f</span> <span class="main">::</span> <span class="tfree">'a</span> <span class="main">⇒</span> <span class="tfree">'a</span> set</span><span class="main">.</span> <span class="main">∀</span><span class="bound">A</span><span class="main">.</span> <span class="main">∃</span><span class="bound">x</span><span class="main">.</span> <span class="bound">A</span> <span class="main">=</span> <span class="bound">f</span> <span class="bound">x</span><span>"</span><span>
  </span><span class="keyword1 command">then</span> <span class="keyword3 command">obtain</span> <span class="skolem skolem">f</span> <span class="main">::</span> <span class="quoted"><span class="quoted"><span>"</span><span class="tfree">'a</span> <span class="main">⇒</span> <span class="tfree">'a</span> set</span><span>"</span></span> <span class="keyword2 keyword">where</span> *<span class="main">:</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">∀</span></span><span class="bound">A</span><span class="main">.</span></span> <span class="main">∃</span><span class="bound">x</span><span class="main">.</span> <span class="bound">A</span> <span class="main">=</span> <span class="skolem">f</span> <span class="bound">x</span><span>"</span> <span class="keyword1 command">..</span><span>
  </span><span class="keyword1 command">let</span> <span class="var quoted var">?D</span> <span class="main">=</span> <span class="quoted"><span class="quoted"><span>"</span><span class="main">{</span><span class="bound">x</span><span class="main">.</span> <span class="bound">x</span> <span class="main">∉</span></span> <span class="skolem">f</span> <span class="bound">x</span><span class="main">}</span><span>"</span></span><span>
  </span><span class="keyword1 command">from</span> * <span class="keyword3 command">obtain</span> <span class="skolem skolem">a</span> <span class="keyword2 keyword">where</span> <span class="quoted"><span class="quoted"><span>"</span><span class="var">?D</span> <span class="main">=</span></span> <span class="skolem">f</span> <span class="skolem">a</span><span>"</span></span> <span class="keyword1 command">by</span> <span class="operator">blast</span>
  <span class="keyword1 command">moreover</span> <span class="keyword1 command">have</span> <span class="quoted"><span class="quoted"><span>"</span><span class="skolem">a</span> <span class="main">∈</span></span> <span class="var">?D</span> <span class="main">⟷</span></span> <span class="skolem">a</span> <span class="main">∉</span> <span class="skolem">f</span> <span class="skolem">a</span><span>"</span> <span class="keyword1 command">by</span> <span class="operator">blast</span> 
  <span class="keyword1 command">ultimately</span> <span class="keyword3 command">show</span> <span class="quoted">False</span> <span class="keyword1 command">by</span> <span class="operator">blast</span> 
<span class="keyword1 command">qed</span> </pre>
</body>
</html>

ordinals

[Thompson's Lamp](https://plato.stanford.edu/entries/infinity/#ThomLamp)
