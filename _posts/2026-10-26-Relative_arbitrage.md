---
layout: post
title:  "A Summer with Claude and Relative Arbitrage, by Dmitriy Traytel"
tags: [AI, Isabelle, formalized mathematics]
# The first paragraph as HTML, without its footnote, for the overview page.
# Keep it in step with the first paragraph below.
excerpt: |
  <p>In our Renaissance Philanthropy-funded project
  <a href="https://www.renaissancephilanthropy.org/copilots-for-isabelle-learning-logical-structure-for-a-better-proving-experience">Copilots for Isabelle</a>,
  we develop methods and tools that allow AI agents to conveniently interface with Isabelle.
  One major outcome of the project so far is Kevin Kappelmann's
  <a href="https://github.com/kappelmann/isabelle-pide-mcp">PIDE MCP</a> component,
  which presents AI agents with a live view of Isabelle much like we human users have it
  through Isabelle/jEdit. I am trying to keep Claude entertained through
  ((semi-)auto-)formalization case studies using this tool; this was also the goal for my
  summer vacation (with a week of FLoC in the middle) where I was looking for a larger
  project on which Claude could work rather independently for a longer period of time.
  And one I would be reasonably detached from, so that I would not have the urge to
  check on the agent every hour.</p>
---
In our Renaissance Philanthropy-funded project
[Copilots for Isabelle](https://www.renaissancephilanthropy.org/copilots-for-isabelle-learning-logical-structure-for-a-better-proving-experience),
we develop methods and tools that allow AI agents to conveniently interface with Isabelle.
One major outcome of the project so far is Kevin Kappelmann's
[PIDE MCP](https://github.com/kappelmann/isabelle-pide-mcp) component[^1],
which presents AI agents with a live view of Isabelle much like we human users have it
through Isabelle/jEdit. I am trying to keep Claude entertained through
((semi-)auto-)formalization case studies using this tool; this was also the goal for my
summer vacation (with a week of FLoC in the middle) where I was looking for a larger
project on which Claude could work rather independently for a longer period of time.
And one I would be reasonably detached from, so that I would not have the urge to
check on the agent every hour.

My second cousin [Misha Shkolnikov](https://www.math.cmu.edu/~mshkolni/) recently
gave a talk at the
[Mathematics for the Real World 2026](https://www.sdu.dk/en/forskning/qm/events/icmu-conf-2026)
conference. On his way to Odense, he stopped in Copenhagen so that I could give him a
small tour of the city. Knowing before the summer that Misha was coming to visit, I
decided to prepare a surprise: I asked Claude to autoformalize, in Isabelle using PIDE MCP,
the main result of his joint article with Jou-Hua Lai and H. Mete Soner (not-yet-published,
but in the final stages of the publication process) on the
[Relative arbitrage problem under eigenvalue lower bounds](https://arxiv.org/abs/2512.17702).

Mandatory note here: I am quite clueless about financial mathematics and probability
theory in general, let alone stochastic portfolio theory and relative arbitrage: e.g., I
learned from the article's first sentence that

> Fernholz has introduced the concept of portfolio domination, now more commonly referred
> to as relative arbitrage, to rigorously capture the notion of "beating the market".

I picked this particular result for the aforementioned detachment reasons, but also
because it scored highly along the "recent work"—"short proof"
curve among Misha's recent papers available on arXiv.

Three weeks and over 100&thinsp;000 lines later I had a
[finished Isabelle/HOL proof](https://github.com/dtraytel/relative_arbitrage).

### The Process

Claude was working nearly non-stop during these three weeks. I used a Claude Max 5x
subscription over the summer, which has since been replaced by the Claude Team plan for scientists.
The workflow was: Claude Fable 5 drafted as much as it could within its harsh token limits. 
When those were exhausted, Claude Opus 5 (I may have started with Opus 4.8) took over based on the current proof state,
notes, and plans that Fable developed. Generally, my prompt was more or less
"Formalize https://arxiv.org/abs/2512.17702 in Isabelle using PIDE MCP"
followed by numerous encouragements to keep going and occasional suggestions to look at
the Archive of Formal Proofs before formalizing a new concept. I am in no position to
discuss the mathematical aspects of this autoformalization, but I have something to say
about the outcome and the challenges along the way (which will include some mathematics in
case you are here solely for that purpose).

### The Result

The main result, Theorem 1.1, itself has a rather complex statement.
Here it is, with HTML generated from Isabelle (while hiding comments). Feel free to skip it; there is not enough context given here anyway to understand it fully. I include it here for completeness and to give a flavor of how things look.

<pre class="source">
<span class="keyword1 command">theorem</span> theorem_1_1<span class="main">:</span>
  <span class="keyword2 keyword">fixes</span> <span class="free">K</span> <span class="main">::</span> <span class="quoted quoted">"<span class="main">(</span><span class="tconst">real</span><span class="main">^</span><span class="tfree">'n</span><span class="main">::</span><span class="tclass">finite</span><span class="main">)</span> <span class="tconst">set</span>"</span>
  <span class="keyword2 keyword">assumes</span> kn<span class="main">:</span> <span class="quoted quoted">"<span class="free">k</span> <span class="main">&lt;</span> <span class="keyword1">CARD</span><span class="main">(</span><span class="tfree">'n</span><span class="main">)</span>"</span> <span class="keyword2 keyword">and</span> L1<span class="main">:</span> <span class="quoted quoted">"<span class="main">1</span> <span class="main">≤</span> <span class="free">L</span>"</span> <span class="keyword2 keyword">and</span> k1<span class="main">:</span> <span class="quoted quoted">"<span class="main">1</span> <span class="main">≤</span> <span class="free">k</span>"</span>
    <span class="keyword2 keyword">and</span> cK<span class="main">:</span> <span class="quoted quoted">"<span class="const">compact</span> <span class="free">K</span>"</span>
  <span class="keyword2 keyword">defines</span> <span class="quoted quoted">"<span class="free">v</span> <span class="main">≡</span> <span class="main">(</span><span class="main">λ</span><span class="bound">z</span><span class="main">.</span> <span class="const">enn2real</span> <span class="main">(</span><span class="const">xval</span> <span class="free">k</span> <span class="free">L</span> <span class="free">K</span> <span class="bound">z</span><span class="main">)</span><span class="main">)</span>"</span>
  <span class="keyword2 keyword">shows</span> <span class="quoted quoted">"<span class="main">(</span><span class="main">∃</span><span class="bound">B</span> <span class="main">::</span> <span class="tconst">real</span><span class="main">.</span> <span class="main">∀</span><span class="bound">y</span><span class="main">.</span> <span class="const">xval</span> <span class="free">k</span> <span class="free">L</span> <span class="free">K</span> <span class="bound">y</span> <span class="main">≤</span> <span class="const">ennreal</span> <span class="bound">B</span><span class="main">)</span>
       <span class="main">∧</span> <span class="main">(</span><span class="main">∀</span><span class="bound">c</span> <span class="bound">z</span><span class="main">.</span> <span class="free">v</span> <span class="bound">z</span> <span class="main">&lt;</span> <span class="bound">c</span> <span class="main">⟶</span> <span class="main">(</span><span class="main">∃</span><span class="bound bound">e</span><span class="main">&gt;</span><span class="main">0</span><span class="main">.</span> <span class="main">∀</span><span class="bound">y</span><span class="main">.</span> <span class="const">dist</span> <span class="bound">z</span> <span class="bound">y</span> <span class="main">&lt;</span> <span class="bound">e</span> <span class="main">⟶</span> <span class="free">v</span> <span class="bound">y</span> <span class="main">&lt;</span> <span class="bound">c</span><span class="main">)</span><span class="main">)</span>
       <span class="main">∧</span> <span class="const">visc_subsol_env2</span> <span class="free">k</span> <span class="free">L</span> <span class="free">K</span>
           <span class="main">(</span><span class="const">interior</span> <span class="free">K</span> <span class="main">∪</span> <span class="main">{</span><span class="bound bound">x</span> <span class="main">∈</span> <span class="free">K</span> <span class="main">-</span> <span class="const">interior</span> <span class="free">K</span><span class="main">.</span> <span class="main">0</span> <span class="main">&lt;</span> <span class="free">v</span> <span class="bound">x</span><span class="main">}</span><span class="main">)</span> <span class="free">v</span>
       <span class="main">∧</span> <span class="const">visc_supersol_env2</span> <span class="free">k</span> <span class="free">L</span> <span class="free">K</span>
           <span class="main">(</span><span class="const">interior</span> <span class="free">K</span> <span class="main">∪</span> <span class="main">{</span><span class="bound bound">x</span> <span class="main">∈</span> <span class="free">K</span> <span class="main">-</span> <span class="const">interior</span> <span class="free">K</span><span class="main">.</span> <span class="const">lsc_envK</span> <span class="free">K</span> <span class="free">v</span> <span class="bound">x</span> <span class="main">&lt;</span> <span class="main">0</span><span class="main">}</span><span class="main">)</span>
           <span class="main">(</span><span class="const">lsc_envK</span> <span class="free">K</span> <span class="free">v</span><span class="main">)</span>
       <span class="main">∧</span> <span class="main">(</span><span class="const">expandable</span> <span class="free">K</span> <span class="main">⟶</span>
          <span class="main">(</span><span class="main">∀</span><span class="bound">u</span> <span class="main">::</span> <span class="tconst">real</span><span class="main">^</span><span class="tfree">'n</span> <span class="main">⇒</span> <span class="tconst">real</span><span class="main">.</span> <span class="main">∀</span><span class="bound">Bd</span><span class="main">.</span>
            <span class="main">(</span><span class="main">∀</span><span class="bound">c</span> <span class="bound">z</span><span class="main">.</span> <span class="bound">z</span> <span class="main">∈</span> <span class="free">K</span> <span class="main">⟶</span> <span class="bound">u</span> <span class="bound">z</span> <span class="main">&lt;</span> <span class="bound">c</span> <span class="main">⟶</span>
               <span class="main">(</span><span class="main">∃</span><span class="bound bound">e</span><span class="main">&gt;</span><span class="main">0</span><span class="main">.</span> <span class="main">∀</span><span class="bound">y</span><span class="main">∈</span><span class="free">K</span><span class="main">.</span> <span class="const">dist</span> <span class="bound">z</span> <span class="bound">y</span> <span class="main">&lt;</span> <span class="bound">e</span> <span class="main">⟶</span> <span class="bound">u</span> <span class="bound">y</span> <span class="main">&lt;</span> <span class="bound">c</span><span class="main">)</span><span class="main">)</span>
            <span class="main">⟶</span> <span class="main">(</span><span class="main">∀</span><span class="bound">y</span><span class="main">∈</span><span class="free">K</span><span class="main">.</span> <span class="main">¦</span><span class="bound">u</span> <span class="bound">y</span><span class="main">¦</span> <span class="main">≤</span> <span class="bound">Bd</span><span class="main">)</span>
            <span class="main">⟶</span> <span class="const">visc_subsol_env2</span> <span class="free">k</span> <span class="free">L</span> <span class="free">K</span>
                 <span class="main">(</span><span class="const">interior</span> <span class="free">K</span> <span class="main">∪</span> <span class="main">{</span><span class="bound bound">x</span> <span class="main">∈</span> <span class="free">K</span> <span class="main">-</span> <span class="const">interior</span> <span class="free">K</span><span class="main">.</span> <span class="main">0</span> <span class="main">&lt;</span> <span class="bound">u</span> <span class="bound">x</span><span class="main">}</span><span class="main">)</span> <span class="bound">u</span>
            <span class="main">⟶</span> <span class="const">visc_supersol_env2</span> <span class="free">k</span> <span class="free">L</span> <span class="free">K</span>
                 <span class="main">(</span><span class="const">interior</span> <span class="free">K</span> <span class="main">∪</span> <span class="main">{</span><span class="bound bound">x</span> <span class="main">∈</span> <span class="free">K</span> <span class="main">-</span> <span class="const">interior</span> <span class="free">K</span><span class="main">.</span> <span class="const">lsc_envK</span> <span class="free">K</span> <span class="bound">u</span> <span class="bound">x</span> <span class="main">&lt;</span> <span class="main">0</span><span class="main">}</span><span class="main">)</span>
                 <span class="main">(</span><span class="const">lsc_envK</span> <span class="free">K</span> <span class="bound">u</span><span class="main">)</span>
            <span class="main">⟶</span> <span class="main">(</span><span class="main">∀</span><span class="bound">x</span><span class="main">∈</span><span class="free">K</span><span class="main">.</span> <span class="bound">u</span> <span class="bound">x</span> <span class="main">=</span> <span class="free">v</span> <span class="bound">x</span><span class="main">)</span><span class="main">)</span><span class="main">)</span>"</span>
</pre>

The formalization
pulls in material from HOL-Analysis and HOL-Probability, but also six AFP entries:
Disintegration, Kolmogorov_Chentsov, Levy_Prokhorov_Metric, Lower_Semicontinuous,
Martingales, Standard_Borel_Spaces. I tasked Claude to explain the definitions that were
introduced on top of these dependencies and to compare the statement to the one from the
paper in a visual/interactive way. The output is
[available here](/assets/theorem_1_1_unfolded.html) and I find it surprisingly readable in that it contextualizes things better than Isabelle's unprocessed HTML output.
I am particularly fond of the nested tooltips to explore definitions (something I suggested to
Claude)&mdash;we need deterministic tools that generate such a presentation of formal
material. Fortunately, Isabelle/PIDE has all the markup we need already, so this is really
a question of presentation.

The main question with any autoformalization is whether the theorem states the
right result: I believe that it does after eyeballing the paper and the formal definitions.
And after showing a more static PDF variant of the above document to Misha, the belief has
only grown stronger. Needless to say, Isabelle checked the proofs, so fortunately I did not need to study those carefully.

Claude's original formulation was spread over five lemmas with different
assumptions. Two interesting things happened:

- The first version of boundedness said something like
  `(∃B :: real. ∀y. enn2real (xval k L K y) ≤ B)`, which does not
  achieve the intention to state that `xval` never returns ∞ because the
  conversion `enn2real` from extended non-negative reals to reals assigns
  `0::real` to `∞::ennreal` in Isabelle (a standard
  "totalization" completion
  [as we know it from division](https://lawrencecpaulson.github.io/2021/12/01/Undefined.html)).
  But in fact, Claude had proved along the way that `xval k L K y` is never
  ∞. It just managed to forget this when stating the final lemma. After realizing the
  issue, it was thus immediate to obtain the current formulation with the embedding of reals into extended non-negative reals
  on the right of the inequality.
- The supersolution statement carried the assumption *L* > 1. During self-review
  Claude flagged this deviation from the paper's *L* ≥ 1. I inquired about
  both where this comes from and whether *L* = 1 is an interesting case. The paper
  itself answers the latter: the special case *L* = 1 is sufficiently interesting to
  have a name in the paper: Ambrosio–Soner co-dimension mean curvature flow. On the
  other hand: this case has been studied before (by Ambrosio and Soner—the same Soner), to the extent that,
  according to Misha, in the setting of this paper he mainly considered *L* to be a
  large number. As for the former, Claude pointed to a place in the paper where the existence
  of an element in the open interval (1,&thinsp;*L*) is stated, thus introducing the
  *L* > 1 assumption implicitly in the middle of the proof. I also asked whether it
  is possible to work around this issue, and Claude managed to: I have no understanding of the
  corrected proof, but it yields *L* ≥ 1 as stated and Claude's abridged
  explanation seemed to make sense to Misha (although he said it will take a week to incorporate it into the paper). For Misha, this was the most interesting outcome of the
  formalization.

### The Formalization's Size and Structure

The first complete proof had over 100&thinsp;000 lines, which sounds impressive by human standards.
From the start, I doubted that it had to be that long. Restructuring eventually shrank it by about a third (see below), although I never pushed very hard for really concise proofs.
I did instruct the agents to iteratively remove lemmas that were flagged as unused when looking at
the theorem dependencies (`unused_thms`). There were some in the end but not too many. Granted, the
agents had to develop a lot of infrastructure that the authors assume to be pre-existing. And
this is not counting advanced analysis and probability theory that was already in Isabelle
and the AFP. On several occasions the authors' proofs are of the form: "repeat
the Larsson–Ruf argument word-by-word", which required the agents to read more
than the 17-page paper&mdash;so the de Bruijn factor may be smaller than it sounds.

The proofs the agents write consist of rather small steps. Here are for example the five
most frequently used proof methods along with the number of occurrences in the
current formalization:

```
6736 rule
6469 simp
1621 intro
1318 blast
 917 auto
```

Of course, different authors have different proof styles. My typical proofs consist of
more `auto`s and fewer `rule`s, here e.g., in
[VeriMon](https://bitbucket.org/jshs/monpoly/src/master/thys/)
(68&thinsp;000 lines of Isabelle):

```
6962 auto
2502 simp
1259 cases
 909 blast
 890 rule
```

Apart from the need to deal with huge amounts of formal material, having small-step proofs
is not necessarily a bad thing. In fact, proof processing is very efficient:
`isabelle build` including document preparation finishes in under five minutes on
my machine.

The [first completed proof](https://github.com/dtraytel/relative_arbitrage/tree/af1bae57eacece10892a88759e9a4d2b86fee4e1)
consisted of 64 theories dumped in a single session. I instructed the agents to separate
generally reusable material from things that are specific to the proof and to use these abstractions
and generalization to shrink the material. This exercise was repeated multiple
times as new models would be released (e.g., Claude Opus 5.5). After these improvements, the
formalization currently consists of only 85&thinsp;000 lines structured in 12 sessions, 
of which 9 could become "library-style" AFP entries (roughly 70&thinsp;000 lines together), 
two formalize the main result (13&thinsp;000 lines), and one presents the result in the paper's notation
(1&thinsp;800 lines). I write "could" because it is not clear to me whether this material
belongs to the AFP *in the current form*, and I fear that I might not have enough
understanding of the material to bring it into the desired form. I welcome any contribution
from experts on such material (I'm thinking, e.g., of the authors of the entries the
formalization uses), although I don't want to force a formalization that may contain
AI slop on anyone. I'm also trying to be conservative when it comes to AFP
submissions because, as an AFP editor, I already see how much AI-generated material we are
receiving&mdash;not all bad, but also by far not all good.

Misha tells me that second-order viscosity analysis, in particular the
Crandall–Ishii(–Lions) result, is a standard and widely used tool in stochastic
optimal control. This makes me hopeful that the present autoformalization can
be useful for future formalizations in this area.

### The Agents' Laziness

Perhaps the most human trait of LLM agents is their laziness. When making TODO lists, the
agents will structure them in such a way that low-hanging fruit is handled
first, creating an illusion of fast progress. An example is Crandall–Ishii, which the
agents had enormous respect for and thus kept postponing. Eventually, there was no way
around it, but amusingly the agents went for the bare minimum and formalized only the core
argument needed for Theorem 1.1, not the full Crandall–Ishii theorem. After Misha
told me about Crandall–Ishii's importance, I instructed the agents explicitly to fill this
gap.

In other places, the laziness actually paid off. The agents managed to avoid formalizing
stochastic integrals and Itô's formula, both used in the paper. I cannot really
say what they did instead (and whether it was better, worse, or mathematically interesting).
Claude has mixed feelings about this and justifies it with the claim that developing this
"Itô-calculus" machinery, which Isabelle lacks, would be a substantial project.

### On PIDE MCP

Technologically, PIDE MCP was the perfect interface for the autoformalization part of the
job. The MCP server gave the agents up-to-date access to Isabelle's feedback on their edits.
People using agents with `isabelle build` frequently want to single out
non-terminating commands by introducing timeouts. Every now and then agents would produce
non-terminating proofs (often when using `blast`), but PIDE MCP makes it easy for
them to detect these issues by labeling the offending commands as "potentially
non-terminating" (whereas PIDE's standard terminology is "running",
which has a positive connotation that may confuse agents: when something is running it is often
a good thing). The later refactoring bits proved more challenging: dynamic handling of sessions
was not yet supported by PIDE MCP at the time (it is now), so every structure change required
a restart of the MCP server (and thus a restart of Claude Code).

### Miscellaneous Thoughts

This formalization was an odd experience. I consider myself an experienced formalizer and
for me, completing a formalization is always accompanied by a sense of accomplishment,
ownership, and understanding: now I really know how it works! These aspects were to a large
degree absent here. Sure, in some sense it is satisfying to see the agents tick off boxes
from their own TODO lists. But it is not the same as doing it oneself. Also, at times
boxes get replaced by more boxes—a real Hydra fight typical of a large proof
development—but without the understanding these boxes mean relatively little and one
does not get a good grip on whether we are converging towards the goal or the agents just
engage us in burning more tokens. (The agents have mixed success when estimating difficulty
and their own capabilities.) In terms of learning how things work: I certainly learned some
things while watching the agents work on the formalization: likely enough to understand the
theorem statement, but not enough to distinguish which parts of the proof are reusable and which
ones are specific to the theorem.

Odd things also happen in the brains of these machines. I get particularly annoyed when the
thinking trace is shown and I see "thoughts" like "Writing Lean
proof." or complaints like "nlinarith is not available in this version of
Isabelle". At no point did I catch the agents actually mistaking Lean's syntax
for Isabelle's—these artifacts did not make it out of the
"thoughts"—but they constitute a reminder that these machines may not be
as intelligent as their proof assembly capabilities suggest. A point Larry will
appreciate: even during thinking, none of the agents ever complained about
[Isabelle's lack of dependent types](https://lawrencecpaulson.github.io/2025/11/02/Why-not-dependent.html).

Where does one go from here? It seems feasible to obtain formalizations of recent
mathematical results with bounded resources.[^2] Looking at the cost question in more detail,
the subscription cost of $100 monthly must be contrasted with the (much higher) calculated API cost: Claude estimates
$7&thinsp;500, with roughly 9.7 billion input tokens and 20 million output tokens
distributed over 30% Fable and 70% Opus (the same distribution is observed
when attributing Isabelle lines to models that produced them)—here we are not counting the
cleanup and restructuring that followed the first proved version of Theorem 1.1.

Which results should we focus on for this price? Many formalizers will
care about the structure of the proof. The particular exercise seems to have been useful to
Misha to straighten out the *L* = 1 case, regardless of the formalized proof
structure. From the proof assistant perspective it is also interesting to compare
technologies and libraries. Would it be cheaper, for instance, to autoformalize the same result in
Lean? Also better tool support, especially for refactoring and making sense of definitions
and statements, is dearly needed.

I included some critical thoughts above, but want to end on a positive note: the paradigm
shift that these funny machines bring to proof assistants makes the work of our community
more relevant than ever: formal proofs will be everywhere and easy to generate, also by non-experts.
We just need good tools for inspecting and assessing the quality of the results and
an army of domain experts to sieve through the mud and find the gold nuggets.

[^1]: Another useful MCP for Isabelle is [I/Q](https://github.com/awslabs/AutoCorrode/tree/main/iq). Have a look at the [PIDE MCP preprint](https://zenodo.org/records/21519365) for an architectural comparison of PIDE MCP, I/Q, and other viable approaches connecting agents to Isabelle.
[^2]: Since this summer, big tech companies have showcased that with unreasonable amounts of resources and in part using internal, unpublished models one can jump even higher and run even faster. Here, I report on using the technology they make available to ordinary subscribers.

*Acknowledgements*.
Thanks to Mohammad Abdulaziz, David Basin, Kevin Kappelmann, and Misha Shkolnikov for comments on earlier drafts of this article.
