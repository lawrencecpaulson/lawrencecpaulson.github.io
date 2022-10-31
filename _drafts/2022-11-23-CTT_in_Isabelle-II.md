--
layout: post
title:  "Martin-Löf type theory in Isabelle, II"
usemathjax: true
tags: [Martin-Löf type theory, Isabelle]
-

### Automation of rewriting and type-checking

### Watching proof objects emerge



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




But I was deeply taken by and devoted perhaps a year of intensive work in order to produce that nobody noticed:


The problem was, for unification to be meaningful for Martin-Löf type theory, it had to take account of variable binding. Luckily, I had spent a couple of weeks with Huet at Inria. One day, he had taken me aside to explain higher-order unification.
I probably understood only 2% of what he said, but something must have stuck in my mind.
It was enough for me to locate and study [his paper on the topic](https://doi.org/10.1016/0304-3975(75)90011-0).
It became clear that higher-order unification would indeed do the trick.


