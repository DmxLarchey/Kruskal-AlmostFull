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
up to Dickson's lemma, but excluding Higman's lemma or Kruskal's tree theorem which are
to be provided in later library.

We define the notion of AF relation inductivelly as the constructive counterpart of the classical
notion of [_Well Quasi Order_](https://en.wikipedia.org/wiki/Well-quasi-ordering) (WQO). 
The results contained in here are:
- the `af R` predicate (see below) characterizing AF relations;
- the classical characterization with _good pairs_ (see `af_recursion` below);
- the equivalence with _Bar inductive predicates_: `af R ↔ bar (good R) []`
  - with a proof of the FAN theorem for inductive bars;
- critically, closure properties for `af`/`bar`:
  - under _direct products_ and _direct sums_ via Coquand's version Ramsey's theorem;
  - under relational morphism;
  - `af =` for finite types, `af ≤` for `nat`;
  - closure of `af` under `k`-ary products
- as a consequence, we get [_Dickson's lemma_](https://en.wikipedia.org/wiki/Dickson%27s_lemma) (see below).
 
This library is distributed under the terms of the [MPL-2.0](LICENSE) license.

# Dependencies

It can be installed via `opam` and requires
- [Kruskal-Trees](https://github.com/DmxLarchey/Kruskal-Trees)
- [Kruskal-Finite](https://github.com/DmxLarchey/Kruskal-Finite)

It can then be accessed via `From KruskalAfProp Require ...` or `From KruskalAfType Require ...`,
see section on the external interface below.
  
# Overview of the definitions

Following the work of Coquand _et al_ in eg [Stop When You Are Almost-Full](https://link.springer.com/chapter/10.1007/978-3-642-32347-8_17),
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
where the type `X` is not explicited: this means that any (infinite) sequence `f : nat → X` 
contains a _good pair_ (ie increasing: both `i < j` and `R fᵢ fⱼ` hold). Notice that 
the `af R` predicate is _constructivelly stronger_ than its classical characterisation, mainly
because, as Coquand frames it, it works also for _sequences that are not given by a law_ (hence
living outside of type `nat → X`).

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
can accomodate with the two variants `Prop` vs `Type` in a uniform way.
The actual Coq lambda-terms produced by these scripts differ however but
these terms are here computer generated exclusivelly by `Ltac` proof scripts.

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
a refinement of the property classically characterising WQOs, stated (and proved) as
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
hence a computation of a good pair (not just a bound) (with the choice `Base := Type`).

# The external interface

The installation procedure _compiles the code base twice_: 
- once under the choice `Base := Prop` and it installs the `KruskalAfProp` library;
- and once under the choice `Base := Type` and it installs the `KruskalAfType` library.

Then both `KruskalAfProp` and `KruskalAfType` can be imported from at the same
time but there namespaces overlap and it is strongly advised not to load both.
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

It is recommanded to perform this import in a single file using
the `Export` directive so that `Base` would be properly defined
uniformyl in every single file importing the library.

# The computational contents of the `af` predicate

We elaborate on the _computational contents_ (CC) of the `af` predicate in case the choice `Base := Type` was made. The CC is also meaningful when `Base := Prop` however, as is conventional in Coq, that CC is sandboxed in the `Prop` realm, and it cannot leak in the `Type` realm. 

A way to look at the CC is to study the proof term for `af_recursion` which would be the following
```coq
Fixpoint af_recursion {R} (a : af R) f {struct a} : { n | ∃ i j, i < j < n ∧ R fᵢ fⱼ } :=
  match a with
  | af_full h => exist _ 2 [PO₁]
  | af_lift h => let (n,hn) := af_recursion (h (f 0)) (λ x, f (S x)) in
                 exist _ (S n) [PO₂]
  end.
```
in programming style where proofs are just Coq lambda-terms. It is easier to analyse the CC
in this form of proofs rather than `Ltac` style proofs.

We see that it proceeds as a fixpoint by structural recursion on the proof of the `af R` predicate:
- when `R` is full, witnessed by `h : ∀ x y, R x y`, then `n := 2` satisfies both `0 < 1 < n` and `R f₀ f₁`, which is denoted as `[PO₁]` above;
- when all the lifts of `R` are `af` witnessed by `h : ∀ a, af (R↑a)`, then a recursive call on the proof `h f₀ : af (R↑f₀)` computes 
a bound `n` for `R↑f₀` and the tail of the sequence `f` (ie `λ x, f (S x)`), and we state that `S n` is a bound 
for `f` itself, and then prove it as `[PO₂]` above.

Hence, we can view the computational contents of `a : af R` as a _well-founded tree_ and use `f` to traverse a branch of that tree,
selecting the upper node with `f₀`, `f₁`, `f₂` successively until the relation `R↑f₀...↑fₙ₋₁` becomes full. The number `n` of nodes 
crossed until the `af` tree tells us this relation is full gives the bound `2+n`.


