---
layout: post
title:  "Coinductive puzzle, by Jasmin Blanchette and Dmitriy Traytel"
usemathjax: true 
tags: [examples, Isabelle, recursion]
---

Coinduction has a reputation for being esoteric, but there are some situations where it is close to
indispensable. One such scenario arose during an Isabelle refinement proof for a verified automatic
theorem prover for first-order logic, [a proof that also involved Anders Schlichtkrull](https://doi.org/10.1145/3293880.3294100). In that
prover, execution traces can be finite or infinite, reflecting the undecidability of first-order
logic.
The refinement proof involves a simulation argument between two layers: an abstract specification
and a concrete theorem prover, both given as transition systems (i.e., binary relations over
states). A single "big" step of the concrete prover represents an entire iteration of the prover's
main loop and may therefore correspond to multiple "small" steps of the abstract prover.

The simulation proof requires relating the concrete layer with the abstract layer. The concrete
"big-step" sequence is of the form $St_0 \leadsto^+ St_1 \leadsto^+ St_2 \leadsto^+ \cdots$, where the
$St_i$'s are states and $\leadsto^+$ is the transitive closure of the abstract transition system.
However, to complete the refinement, we must obtain a "small-step" sequence $St_0 \leadsto \cdots
\leadsto St_1 \leadsto \cdots \leadsto St_2 \leadsto \cdots$.

If the big-step sequence is finite, the existence of the small-step sequence can be proved using
induction. But in our semidecidable scenario, sequences may be infinite. One way to cope with this
is to use coinductive methods. This blog entry presents a solution to this coinductive puzzle.


### Preliminaries

To represent possibly infinite sequences of states, we use the coinductive datatype of lazy lists:

```
codatatype 'a llist = LNil | LCons 'a "'a llist"
```

Intuitively, lazy lists are like ordinary finite lists, except that they also allow infinite values
such as `LCons 0 (LCons 1 (LCons 2 ...))`. However, the reasoning principles for
coinductive types and predicates are rather different from their inductive counterparts, as we will
see in a moment.

Let us review some useful vocabulary for lazy lists. First, the selectors `lhd : 'a llist -> 'a` and
`ltl : 'a llist -> 'a llist` return the head and the tail, respectively, of an `LCons` value. For an
`LNil` value, `lhd` returns a [fixed arbitrary value](https://lawrencecpaulson.github.io/2021/12/01/Undefined.html) and `ltl` returns `LNil`. Then
the function `llast : 'a llist -> 'a` returns the last value of a finite lazy list. If there is no
such value, because the lazy list is either empty or infinite, `llast` returns a fixed arbitrary
value. Next, the function `prepend` concatenates a finite list and a lazy list:

```
fun prepend :: "'a list -> 'a llist -> 'a llist" where
  "prepend [] ys = ys"
| "prepend (x # xs) ys = LCons x (prepend xs ys)"
```

In the simulation proof, we do not work with arbitrary lazy lists but with nonempty lazy lists
whose consecutive elements are related by the small-step or big-step transition relation. To
capture this restriction, we use a coinductive predicate that characterizes such chains:

```
coinductive chain :: "('a ⇒ 'a ⇒ bool) ⇒ 'a llist ⇒ bool" for R :: "'a ⇒ 'a ⇒ bool" where
  "chain R (LCons x LNil)"
| "chain R xs ⟹ R x (lhd xs) ⟹ chain R (LCons x xs)"
```

The predicate has two introduction rules, one for singleton chains and one for longer chains. Had
we worked with finite lists instead of lazy lists, we would have written the same definition
replacing the `coinductive` keyword with `inductive`. The magic of coinduction allows us to apply
the second introduction rule infinitely often. This is necessary when proving that an infinite lazy
list forms a chain.

The big-step sequence should be a subsequence of the small-step sequence. We formalize coinductive
subsequences via the predicate `emb`:

```
coinductive emb :: "'a llist ⇒ 'a llist ⇒ bool" where
  "lfinite xs ⟹ emb LNil xs"
| "emb xs ys ⟹ emb (LCons x xs) (prepend zs (LCons x ys))"
```

Our definition requires that finite lazy lists may not be embedded in infinite lazy lists. In our
application, this matters because we want to ensure that only finite small-step sequences can
simulate finite big-step sequences.

In Isabelle, a coinductive predicate `P` is accompanied by corresponding coinduction principles that
allow us to prove positive statements of the form `P ...`. For `chain` and `emb` we obtain the
following principles:

```
X xs ⟹
(⋀xs'. X xs' ⟹
      (∃x. xs' = LCons x LNil) ∨
      (∃xs x. xs' = LCons x xs ∧ (X xs ∨ chain R xs) ∧ R x (lhd xs))) ⟹
chain R xs

X xs ys ⟹
(⋀xs' ys'.
    X xs' ys' ⟹
    (∃ys. xs' = LNil ∧ ys' = ys ∧ lfinite ys) ∨
    (∃xs ys x zs. xs' = LCons x xs ∧ ys' = prepend zs (LCons x ys) ∧ (X xs ys ∨ emb xs ys))) ⟹
emb xs ys
```

These principles embody the fact that `chain` and `emb` are the greatest ("most true") predicates
stable under the application of their respective introduction rules. For example for `emb`, given a
binary relation `X` stable under `emb`'s introduction rules, any arguments satisfying `X` also
satisfy `emb`. Stability under introduction rules means that for any arguments `xs'` and `ys'`
satisfying `X` that correspond to the arguments of `emb` in either one of `emb`'s two introduction
rules, the arguments of the self-calls also satisfy `X`.

### The main theorem

We are now ready to state our desired theorem:

```
lemma "chain R⇧+⇧+ xs ⟹ ∃ys. chain R ys ∧ emb xs ys ∧ lhd ys = lhd xs ∧ llast ys = llast xs"
```

In words, given a big-step sequence `xs` whose consecutive elements are related by the transitive
closure `R⇧+⇧+` of a relation `R`, there exists a small-step sequence `ys` whose consecutive
elements are related by `R`. The small-step sequence must embed, using `emb`, the big-step
sequence. In addition, the sequences' first and last elements must coincide. If both sequences are
infinite, their last elements are equal by definition to the same fixed arbitrary value, as
explained above.

### The proof

To prove the theorem, we instantiate the existential quantifier with a witness, which we define
corecursively:

```
corec wit :: "('a ⇒ 'a ⇒ bool) ⇒ 'a llist ⇒ 'a llist" where
  "wit R xs = (case xs of LCons x (LCons y xs) ⇒
     LCons x (prepend (pick R x y) (wit R (LCons y xs))) | _ ⇒ xs)"
```

The `wit` function fills the gaps between consecutive values of the big-step sequence with
arbitrarily chosen intermediate values that form finite chains. We use Hilbert's choice operator to
construct these chains:

```
definition pick :: "('a ⇒ 'a ⇒ bool) ⇒ 'a ⇒ 'a ⇒ 'a list" where
  "pick R x y = (SOME xs. chain R (llist_of (x # xs @ [y])))"
```

Here, `llist_of` converts finite lists to lazy lists, which allows us to reuse the `chain`
predicate. The `pick` function is characterized by the following property:

lemma "R⇧+⇧+ x y ⟹ chain R (llist_of (x # pick x y @ [y]))"

Going back to `wit`'s definition, we may wonder why Isabelle accepts it in the first place. The
definition is not obviously productive, a requirement that would ensure its totality. Productive
definitions generate at least one constructor after calling themselves. In our case, `LCons` is
that constructor, but `prepend` stands in the way and could potentially destroy constructors
produced by the self-call to `wit`. However, we know that `prepend` is friendly enough to only add
constructors and not to remove them. In Isabelle, we can register it as a ["friend"](https://doi.org/10.1007/978-3-662-54434-1_5), which
convinces our favorite proof assistant to accept the above definition.

It remains to prove the four conjuncts of our main theorem, taking `ys` to be `wit R xs`.

First, we prove `chain R⇧+⇧+ xs ⟹ lhd (wit R xs) = lhd xs` by simple rewriting.

Second, we attempt to show `chain R⇧+⇧+ xs ⟹ emb xs (wit R xs)` using `emb`'s coinduction principle.
To this end, Isabelle's coinduction proof method instantiates `X` with the canonical relation
`λxs ys. ys = wit xs ∧ chain R⇧+⇧+ xs`. After some simplification, we arrive at a goal requiring us to prove
`(∃zs. LCons x (prepend (pick x y) (wit (LCons y xs))) = prepend zs (LCons x (wit (LCons y xs))))`
whose two side have the `prepend` in different positions (on one side before the `x`, on the other side after). We would like to insert a second `prepend zs'` (where `zs'` would be existentially quantified) on the right-hand side, so that we can instantiate `zs` with the empty list and `zs'` with `pick x y`, making both sides equal.
We can achieve this by modifying `X` to be `λxs ys. ∃zs'. ys = prepend zs' (wit xs) ∧ chain R⇧+⇧+ xs`.
A more principled alternative is to manually derive the following generalized coinduction principle, which inserts `prepend zs'` at the right place:
```
X xs ys ⟹
(⋀xs' ys'.
    X xs' ys' ⟹
    (∃ys. xs' = LNil ∧ ys' = ys ∧ lfinite ys) ∨
    (∃xs ys x zs zs'. xs' = LCons x xs ∧ ys' = prepend zs (LCons x (prepend zs' ys)) ∧ (X xs ys ∨ emb xs ys))) ⟹
emb xs ys
```
This approach is an instance of a general technique called [coinduction up to](https://doi.org/10.1017/CBO9780511792588.007).

Third, we need to prove `chain R⇧+⇧+ xs ⟹ llast (wit R xs) = llast xs`. Since we now know that
`emb xs (wit R xs)` holds, by definition of `emb` only two cases are possible. Either both
`wit R xs` and `xs` are finite lazy lists, in which case the property follows by induction, or both 
are infinite, in which case their last elements are equal to the notorious fixed arbitrary value.

Fourth, when attempting to prove `chain R⇧+⇧+ xs ⟹ chain R (wit R xs)`, we run into a similar issue
as in the proof of the second conjunct. The resolution is also similar. We manually derive a
coinduction-up-to principle for `chain` with respect to `prepend`:
```
X xs ⟹
(⋀xs'. X xs' ⟹
      (∃x. xs' = LCons x LNil) ∨
      (∃xs x zs'. xs' = LCons x (prepend zs' xs) ∧ (X xs ∨ chain R xs) ∧ chain R (llist_of (y # zs' @ [lhd xs])))) ⟹
chain R xs
```
This principle additionally involves a generalization of the side condition `R y (lhd xs)` to
`chain R (llist_of (y # zs' @ [lhd xs]))` to incorporate `zs'`.

### Conclusion

We successfully solved the coinductive puzzle that arose during our verification of an automatic
theorem prover. At its core, the puzzle has little to do with theorem proving; instead, it is about
refinement of possibly nonterminating transition systems. Our proof can be found in the [AFP](https://devel.isa-afp.org/sessions/ordered_resolution_prover/#Lazy_List_Chain.html#Lazy_List_Chain.chain_tranclp_imp_exists_chain|fact). On the plus side, Isabelle conveniently
allowed us to define all the functions and predicates we needed to carry out the proof, including
functions whose productivity relied on "friends". On the minus side, the proof of an easy-looking
theorem required some ingenuity. In particular, we found ourselves deriving coinduction-up-to
principles for coinductive predicates manually to use them for definitions involving "friends". An
avenue for future work would be to derive such principles automatically.
