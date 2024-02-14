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

This library formalizes in `Coq 8.14+` basic results _Almost Full relations_ in Coq,
a notion defined inductivelly that is the constructive counterpart of the classical
notion of _Well Quasi Order_ (WQO). The results contained in here are:
- the `af R` predicate (see below) characterizing AF relations;
- the equivalence with _Bar inductive predicates_: `af R ↔ bar (good R) []`;
- stability properties for `af`/`bar`:
  - under _direct products_ and _direct sums_ via Coquand's version Ramsey's theorem;
  - under relational morphism;
  - `af =` for finite types;
  - as a consequence, we get eg _Dickson's lemma_.
 
This library is distributed under the terms of the [MPL-2.0](LICENSE) license.

# Dependencies
It can be installed via `opam` and requires
- [Kruskal-Trees](https://github.com/DmxLarchey/Kruskal-Trees)
- [Kruskal-Finite](https://github.com/DmxLarchey/Kruskal-Finite)
  
# Overview of the definitions

Following the work of Coquand _et al_ in eg [Stop When You Are Almost-Full](https://link.springer.com/chapter/10.1007/978-3-642-32347-8_17),
we characterize AF relations using an inductive predicate:
```coq
Inductive af {X : Type} (R : X → X → Prop) : Prop :=
  | af_full : (∀ x y, R x y) → af R
  | af_lift : (∀ a, af (R↑a)) → af R
where "R↑a" := (λ x y, R x y ∨ R a x).
```

From this definition, we can recover the property characterising WQOs classically:
```coq
af_recursion : ∀R, af R → ∀f : nat → X, ∃ i j, i < j ∧ R fᵢ fⱼ
```
where the type `X` is not explicited: this means that any (infinite) sequence `f : nat → X` 
contains a _good pair_ (ie increasing, `i < j` and `R fᵢ fⱼ` at the same time). Notice that 
the `af R` predicate is constructivelly stronger than its classical characterisation.

An alternative characterization can be implemented at `Type` level
instead of the `Prop` level (non-informative) with the __nearly__
identical definition:
```coq
Inductive af {X : Type} (R : X → X → Prop) : Type :=
  | af_full : (∀ x y, R x y) → af R
  | af_lift : (∀ a, af (R↑a)) → af R.
```
In that case, the classical property we derive is more informative:
```coq
af_recursion : ∀R, af R → ∀f : nat → X, { n | ∃ i j, i < j < n ∧ R fᵢ fⱼ }
```
and read as follows: for any sequence `f : nat → X`, _one can
compute a bound_ (from information contained in both `af R` and `f`)
such that below that bound `n`, we know for sure that there is a good pair 
in the initial segment `f₀`,...,`fₙ₋₁`. Notice we do not necessarily
have enough information to compute where this good pair is inside
that initial segment (eg when `R` is not decidable).

In the `Type` case, the `af` predicate is _more informative_ (and
indeed stronger) than in the `Prop` case: it contains a computational
contents.

# Some results contained in this library

We give a non-exhaustive summary of the main results contained in this library:
```coq
Theorem af_le_nat : af ≤. 
Theorem af_finite X : (∃l : list X, ∀x, x ∊ l) → af (@eq X).
Theorem af_inter X (R T : X → X → Prop) : af R → af T → af (R ∩₂ T).
Theorem af_product X (R T : X → X → Prop) : af R → af T → af (R ⨯ T).
```
- in `af_le_nat`, the relation `_ ≤ _ : nat → nat → Prop` is the _less-than_ 
(or natural) ordering on natural numbers;
- `af_finite` means that if a type `X` is listable, then equality on that type of `af`;
- `af_inter` is Coquand's _et al_ constructive version of _Ramsey's theorem_ 
and `af_product` an immediate consequence of it.

By iterating over `n`, we lift the binary product to `n`-ary products, ie vectors:
```coq
Theorem af_vec_product n X (R : X → X → Prop) : af R → af (vec_fall2 R n).
```
where `vec_fall2 R n := λ v w : vec X n, ∀i, R u⦃i⦄ v⦃i⦄`.

Combining `af_le_nat`, `af_vec_product` and `af_recursion`, we get [Dickson's lemma](https://en.wikipedia.org/wiki/Dickson%27s_lemma):
```coq
Theorem Dickson_lemma n : ∀f : nat → vec nat n, ∃ a b, a < b ⋀ ∀i, (f a)⦃i⦄ ≤ (f b)⦃i⦄.
```

# Dealing with `Prop` vs `Type`

The library deals with both versions in a _generic way_, using
the _same code base_. Indeed, in `Ltac` language, identical proof scripts
can accomodate with the two variants `Prop` vs `Type` in a uniform way.
The actual Coq lambda-terms produced by these scripts differ however but
they are computer generated in this library.

To deal with the `Prop` vs `Type` choice, we define a type notation
`Base` which is either `Base := Prop` or `Base := Type` and, consistently
with this choice, notations for first order like connectives described
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

In that setting, the parametric definition of `af` becomes
```coq
Inductive af {X} (R : X → X → Prop) : Base :=
  | af_full : (∀ x y, R x y) → af R
  | af_lift : (∀ a, af (R↑a)) → af R.
```

To be complete, the classical property of WQOs is stated (and proved) as:
```coq
af_recursion : af R → ∀f : nat → X, ∃ₜ n, ∃ i j, i < j < n ∧ R fᵢ fⱼ
```
using the generic first order syntax depending on the choice of `Base`:
- when `Base := Prop` then the formula `∃ₜ n, ∃ i j, i < j < n ∧ ...` means exactly `∃ n i j, i < j < n ∧ ...` which in turn is equivalent to `∃ i j, i < j ∧ ...`;
- when `Base := Type`, the `∃ₜ n, ...` quantifier is informative, ie identical to `{ n | ... }`;

The existential quantifiers binding `i` and `j` which are non-informative in either case. See the discussion below for more details on the proof of `af_recursion` and the computational contents of the `af` predicate.

# The external interface

The installation procedure compiles the code base twice: 
- once under the choice `Base := Prop` and it installs the `KruskalAfProp` library;
- and once under the choice `Base := Type` and it installs the `KruskalAfType` library.

Then both `KruskalAfProp` and `KruskalAfType` can be imported from at the same
time but there namespace overlap and it is advised not to load both. The idea
is to write code that works with either choice.

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

# The computation contents of the `af` predicate

We elaborate on the _computational contents_ (CC) of the `af` predicate in case the choice `Base := Type` was made. The CC is also meaningful when `Base := Prop` however, as is conventional in Coq, that CC is sandboxed in the `Prop` realm, and it cannot leak in the `Type` realm. 

A way to look at the CC is to study the proof term for `af_recursion` which is the following:
```coq
Fixpoint af_recursion {R} (a : af R) f {struct a} : { n | ∃ i j, i < j < n ∧ R fᵢ fⱼ } :=
  match a with
  | af_full h => existT _ 2 [PO₁]
  | af_lift h => let (n,hn) := af_recursion (h (f 0)) (λ x, f (S x)) in
                 existT _ (S n) [PO₂]
  end.
```
We see that it proceeds as a fixpoint by structural recursion on the `af R` predicate:
- when `R` is full, witnessed by `h : ∀ x y, R x y`, then `n := 2` satisfies both `0 < 1 < n` and `R f₀ f₁`, which is denoted as `[PO₁]` above;
- when all the lifts of `R` are `af` witnessed by `h : ∀ a, af (R↑a)`, by a recursive call on the proof `h f₀ : af (R↑f₀)` to get a bound `n` for `(λ x, f (S x))` (the tail of the sequence `f`) and state that `S n` is a bound for `f` itself and then prove it as `[PO₂]` above.

Hence, we can view the computational contents of `a : af R` as a well-founded tree and use `f` to traverse a branch of that tree, selecting the upper node with `f₀`, `f₁`, `f₂` successively until the relation `R↑f₀...↑fₙ₋₁` becomes full. The number of nodes crossed until the `af` tree tells us this relation is full gives the bound `2+n`. 


