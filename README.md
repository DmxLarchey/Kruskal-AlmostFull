```
(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)
```

# What is this library?

This library formalizes ground results about _Almost Full relations_ (AF) in `Coq 8.14+`,
up to [Dickson's lemma](https://en.wikipedia.org/wiki/Dickson%27s_lemma), 
but excluding [Higman's lemma](https://en.wikipedia.org/wiki/Higman%27s_lemma) 
or the more complex [Kruskal's tree theorem](https://en.wikipedia.org/wiki/Kruskal%27s_tree_theorem) 
which are to be provided in upcoming libraries.
This library is a _major and modular rewrite_ of a somewhat [monolithic development](https://members.loria.fr/DLarchey/files/Kruskal/index.html) 
concluding in a constructive/inductive proof of Kruskal's tree theorem.
This library has some overlap with the [Almost Full `coq-community`](https://github.com/coq-community/almost-full) 
project (see below) but they have different objectives.

We define the notion of AF relation inductively as the constructive counterpart of the classical
notion of [_Well Quasi Order_](https://en.wikipedia.org/wiki/Well-quasi-ordering) (WQO). 
The results contained in here are:
- the [`af R` predicate](#Overview-of-the-definitions) characterizing AF relations;
- the classical characterization with _good pairs_ (see `af_recursion` below);
- the equivalence with _Bar inductive predicates_: `af R ↔ bar (good R) []`;
- critically, [closure properties for `af`/`bar`](#Some-results-contained-in-Kruskal-AlmostFull):
  - under _direct products_ and _direct sums_ via Coquand's version Ramsey's theorem;
  - under [_relational morphism_](#Relational-surjective-morphisms);
  - `af =` for finite types, `af ≤` for `nat`;
  - closure of `af` under `k`-ary products
- as a consequence, we get [_Dickson's lemma_](#Some-results-contained-in-Kruskal-AlmostFull).
 
This library is distributed under the terms of the [MPL-2.0](LICENSE) license.

# Dependencies and install

It can be installed via `opam` 
```console
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam install coq-kruskal-almostfull
```
and requires
- [Kruskal-Trees](https://github.com/DmxLarchey/Kruskal-Trees)
- [Kruskal-Finite](https://github.com/DmxLarchey/Kruskal-Finite)

but see also [Kruskal-Higman](https://github.com/DmxLarchey/Kruskal-Higman)
if you need Higman's lemma (homeomorphic list embedding is AF). Shortly,
Kruskal's tree theorem should also appear as `Kruskal-Theorem`. It just needs
code polishing before release. Ask me directly if you are in a hurry!!

It can then be accessed via `From KruskalAfProp Require ...` or `From KruskalAfType Require ...`,
see section on [the external interface](#The-external-interface) below.

# Comparisons with the [Almost Full `coq-community` project](https://github.com/coq-community/almost-full)
  
That project was initiated as the artifact of the paper of Coquand _et al_ [Stop When You Are Almost-Full](https://link.springer.com/chapter/10.1007/978-3-642-32347-8_17). It has not really evolved beyond that goal. As with the current `Kruskal-Almostfull`, there is a `Type`-bounded and a `Prop`-bounded
version of the `almost-full` library, but they have a disjoint code base. Comparing the contents of the libraries, there is 
some overlap in the results: eg Ramsey's theorem (of which of our own proof is a cleanup/rework a former version of theirs). 
But the two projects head in different directions.

The main differences with the `Kruskal-Almostfull` project are (IMHO):
- the proofs scripts and notations are not really aimed at user readability;
- it is not designed as a toolkit for further developments:
  - it is missing a nice tool like surjective relational morphisms;
  - their `af_finite` is much less versatile than our own version which 
    holds for identity over any listable type;
- it includes, as a sizable code base, examples of termination proofs 
  for recursive programs, which was driving the motivation of their paper;
- the motivation for `Kruskal-Almostfull` is to study and provide basic but versatile
  tools for the closure properties of AF relations. 
  
# Overview of the definitions

Following the work of ,
we characterize AF relations using an inductive predicate:
```coq
Inductive af {X : Type} (R : X → X → Prop) : Prop :=
  | af_full : (∀ x y, R x y) → af R
  | af_lift : (∀ a, af (R↑a)) → af R
where "R↑a" := (λ x y, R x y ∨ R a x).
```

From this definition, we recover the property characterising WQOs _classically_:
```coq
af_recursion : af R → ∀f : nat → X, ∃ i j, i < j ∧ R fᵢ fⱼ
```
where the type `X` is not explicit: this means that any (infinite) sequence `f : nat → X` 
contains a _good pair_ (ie increasing: both `i < j` and `R fᵢ fⱼ` hold). Notice that 
the `af R` predicate is _constructively stronger_ than its classical characterization, mainly
because, as [Coquand frames it](https://www.cairn-int.info/journal-revue-internationale-de-philosophie-2004-4-page-483.htm), 
it works also _for sequences that are not given by a law_ (hence living outside of type `nat → X`).

A variant definition can be implemented at `Type` level (informative)
instead of the `Prop` level (non-informative) with the __nearly__
identical definition (except of the output type):
```coq
Inductive af {X : Type} (R : X → X → Prop) : Type :=
  | af_full : (∀ x y, R x y) → af R
  | af_lift : (∀ a, af (R↑a)) → af R.
```
In that case, the `af_recursion` we derive is more informative:
```coq
af_recursion : af R → ∀f : nat → X, { n | ∃ i j, i < j < n ∧ R fᵢ fⱼ }
```
and read as follows: for any sequence `f : nat → X`, _one can
compute a bound_ (from information contained in both `af R` and `f`)
such that below that bound `n`, we know for sure that there is a good pair 
in the initial segment `f₀`,...,`fₙ₋₁`. Notice that we do not necessarily
have enough information to compute where precisely this good pair resides
inside that initial segment (eg when `R` is not decidable).

In the `Type` case, the `af` predicate is _more informative_ (and
indeed stronger) than in the `Prop` case: it contains a computational
contents. See below for a section discussing this question specifically.

# Dealing with `Prop` vs `Type`

The library deals with both versions `af R : Prop` or `af R : Type` in a _generic way_, using
the _same code base_. Indeed, in `Ltac` language, identical proof scripts
can accommodate with the two variants `Prop` vs `Type` in a uniform way.
The actual Coq lambda-terms produced by these scripts differ however but
these terms are here computer generated exclusively by `Ltac` proof scripts.

To deal with the `Prop` vs `Type` choice, we define a _notation_
`Base` which is either `Base := Prop` or `Base := Type` and, consistently
with this choice, notations for _first order like connectives_ described
below:
```
+------+-----------+---------+----------+--------------+
| Base |   ⊥ₜ      |   ∨ₜ    |   ∧ₜ     |   ∃ₜ         |
+------+-----------+---------+----------+--------------+
| Prop | False     | ∨ / or  | ∧ / and  | ∃ / ex       |
| Type | Empty_set | + / sum | * / prod | { & } / sigT |
+------+-----------+---------+----------+--------------+
```
The _if and only if_ connective is also defined as 
`⇄ₜ` but it is not primitive, ie it is a combination
of `∧ₜ` and the arrow `→`. Notice that universal
quantification `∀` (and its restriction, the arrow `→`)
are naturally parametric in the `Prop` vs `Type` choice
(they are not inductive) whereas the other above (eg. `or` and
`ex`) are not parametric (and they are inductivelly defined).

In that setting grounded on the `Base` choice/notation, the parametric definition of `af` becomes
```coq
Inductive af {X} (R : X → X → Prop) : Base :=
  | af_full : (∀ x y, R x y) → af R
  | af_lift : (∀ a, af (R↑a)) → af R.
```

To be complete, with [`af_recursion`](theories/af/af.v), we get
a refinement of the property classically characterizing WQOs, stated (and proved) as
```coq
Fact af_recursion X (R : X → X → Prop) : af R → ∀f : nat → X, ∃ₜ n, ∃ i j, i < j < n ∧ R fᵢ fⱼ
```
using the generic first order syntax depending on the choice of `Base`:
- when `Base := Prop`, the formula `∃ₜ n, ∃ i j, i < j < n ∧ ...` expands to `∃ n i j, i < j < n ∧ ...` 
which in turn is logically equivalent to `∃ i j, i < j ∧ ...`;
- when `Base := Type`, the `∃ₜ n, ...` quantifier is informative, ie expands to `{ n & ... }`.

The existential quantifiers binding `i` and `j` are non-informative in either case. As hinted above, 
the `af R` predicate itself does not contain enough information to compute the exact position of a good pair.
Only a bound under which one such pair must exist can be extracted. Provided that we are given a _decision procedure_ 
for the relation `R`, this bound can then be used to compute a good pair using _exhaustive finitary search_.

See the discussion below for more details on the proof of `af_recursion` and 
the computational contents of the `af` predicate.

# Some results contained in Kruskal-AlmostFull

We give a non-exhaustive summary of the main results contained in this library:
```coq
Theorem af_le_nat : af ≤. 
Theorem af_eq_fin X : (∃ₜ l : list X, ∀x, x ∊ l) → af (@eq X).
Theorem af_inter X (R T : X → X → Prop) : af R → af T → af (R ∩₂ T).
Theorem af_product X (R T : X → X → Prop) : af R → af T → af (R ⨯ T).
Theorem af_vec_fall2 k X (R : X → X → Prop) : af R → af (vec_fall2 R k).
```
- in [`af_le_nat`](theories/af/af_tools.v), the relation `_ ≤ _ : nat → nat → Prop` is the _less-than_ 
(or natural) ordering on `nat`;
- [`af_eq_fin`](theories/af/af_eq.v) means that if a type `X` is listable (finite), then equality on that type is AF;
- [`af_inter`](theories/af/af_ramsey.v) is _Coquand's et al_ constructive version of [_Ramsey's theorem_](https://en.wikipedia.org/wiki/Ramsey%27s_theorem) 
and [`af_product`](theories/af/af_tools.v) an immediate consequence of it.
- by `af_product` iterating over `k` times, we lift the binary product to `k`-ary products, ie vectors of type `vec X k`
and obtain [`af_vec_fall2`](theories/af/af_tools.v) where `vec_fall2 R k := λ v w : vec X k, ∀p : idx k, R u⦃p⦄ v⦃p⦄`.

Combining `af_le_nat`, `af_vec_fall2` and `af_recursion`, we get [Dickson_lemma](theories/applications/dickson_lemma.v):
```coq
Theorem Dickson_lemma k : ∀f : nat → vec nat k, ∃ₜ n ∃ i j, i < j < n ∧ ∀p, fᵢ⦃p⦄ ≤ fⱼ⦃p⦄.
```
and, because the relation `_ ≤ _` over `nat` is _decidable_, we can derive the stronger form
```coq
Theorem Dickson_lemma_strong k : ∀f : nat → vec nat k, ∃ₜ i j, i < j ∧ ∀p, fᵢ⦃p⦄ ≤ fⱼ⦃p⦄.
```
hence a computation of a good pair (not just a bound) (using the `Base := Type` variant).

# The external interface

The installation procedure _compiles the code base twice_: 
- once under the choice `Base := Prop` and it installs the `KruskalAfProp` library;
- and once under the choice `Base := Type` and it installs the `KruskalAfType` library.

Then both `KruskalAfProp` and `KruskalAfType` can be imported from at the same
time but there name spaces coincide and it is strongly advised not to load both.
The intent is to write code that works with either choice.

From the point of view of the _external interface_ of the library, 
if one wants the `Base := Prop` choice, then the import command would be:
```coq
From KruskalAfProp Require Export base almost_full.
```
and on the other hand, for the `Base := Type` choice, the import
command would be:
```coq
From KruskalAfType Require Export base almost_full.
```

It is recommended to perform this import in a single file using
the `Export` directive so that `Base` would be properly defined
uniformly in every single file importing the library.

# The computational contents of the `af` predicate

We elaborate on the _computational contents_ (CC) of the `af` predicate in case the choice `Base := Type` was made. The CC is also meaningful when `Base := Prop` however, as is conventional in Coq, that CC is sandboxed in the `Prop` realm, and it cannot leak in the `Type` realm. 

A way to look at the CC is to study the proof term for `af_recursion` which would be the following
```coq
Fixpoint af_recursion {R} (a : af R) f {struct a} : { n | ∃ i j, i < j < n ∧ R fᵢ fⱼ } :=
  match a with
  | af_full h => exist _ 2 [PO₁]
  | af_lift h => let (n,hn) := af_recursion (h f₀) (λ x, f (S x)) in
                 exist _ (S n) [PO₂]
  end.
```
in programming style where proofs are just Coq lambda-terms. It is easier to analyse the CC
in this form of proofs rather than `Ltac` style proofs.

We see that it proceeds as a fixpoint by structural recursion on the proof of the `af R` predicate:
- when `R` is full, witnessed by `h : ∀ x y, R x y`, then `n := 2` satisfies both `0 < 1 < n` and `R f₀ f₁`, which is denoted as `[PO₁]` above;
- when all the lifts of `R` are `af` witnessed by `h : ∀ a, af (R↑a)`, then a recursive call on the proof `h f₀ : af (R↑f₀)` computes 
a bound `n` for `R↑f₀` and the tail of the sequence `f` (ie `λ x, f (S x)`), and we state that `S n` is a bound 
for `f` itself, and then prove it as `[PO₂]` above;
- the proof obligations `[PO₁]` and `[PO₂]` are omitted here because do not participate in the CC.

Hence, we can view the computational contents of `a : af R` as containing _well founded tree_ and use `f` to traverse a branch of that tree,
selecting the upper node with `f₀`, `f₁`, `f₂` successively until the relation `R↑f₀...↑fₙ₋₁` becomes full. The number `n` of nodes 
crossed until the `af` tree tells us this relation is full gives the bound `2+n`. The well founded tree contained in `a : af R` collects,
along its branches, _bounds on the position of good pairs_ for every possible sequence of values.

# Relational surjective morphisms

Transporting the AF property from `R : X → X → Prop` to `T : Y → Y → Prop` can be performed using a morphism `f : X → Y` which 
is a _relation preserving_ map, moreover supposed to be _surjective_. Hence, proving a statement like eg
`af R → af T` only involves providing `f : X → Y`, and proving:
- morphism as `∀ u v, R u v → T (f u) (f v)`;
- and surjectivity `∀ y, ∃ₜ x, y = f x`;

which is very convenient indeed: the notion of AF is absent from those two requirements.
Unfortunately this does not work very well with Σ-types. For instance consider the 
natural statement that AF is _closed under restriction_:
```coq
af_af_sub_rel X (P : X → Prop) (R : X → X → Prop): af R → af R⇓P
```
where `R⇓P : {x | P x} → {x | P x} → Prop` is the restriction of `R : X → X → Prop` to the Σ-type `{x | P x}`. 
There is an "obvious" surjective morphism from `X` to `{x | P x}` except that it is not so obvious:
- it cannot be implemented as a Coq function of type `X → {x | P x}` because the morphism is in fact 
  a _partial function_ that is not supposed to map values `x` for which `P x` does not hold;
- it cannot be proved surjective because there is no reason for uniqueness of the proof of `P x` (unless `P` 
  is turned into a Boolean predicate).

To avoid these _strong impairments_, we can instead view the morphism as a _relation_ of type `f : X → Y → Prop`
instead of type `f : X → Y`. Then:
- not only the partiality constraint fades away;
- but also, the morphism can have _several output values_ (possibly even infinitely many).

In the case of the projection on the Σ-type `{x | P x}`, the morphism `f` is simply defined as `f := λ x y, x = π₁ y` and we are (almost) done!!
Using relational morphisms it becomes trivial to establish results like eg:
```coq
Fact af_lift_af_sub_rel X R (x₀ : X) : af R↑x₀ → af R⇓(λ x, ¬ R x₀ x).
Proof.
  af rel morph (λ x y, x = π₁ y).
  + intros []; simpl; eauto.
  + intros ? ? [] [] -> ->; simpl; tauto.
Qed.
```
Beware the converse implication `af R⇓(λ x, ¬ R x₀ x) → af R↑x₀` is an involved question related to the decidability of `R x₀`.

