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
  | af_lift : (∀ a, af (R↑a)) → af R.
```
where `R↑a := λ x y, R x y ∨ R a x`.

From this definition, we can recover the classical property of WQOs:
```coq
∀R, af R → ∀f : nat → X, ∃ i j, i < j ∧ R (f i) (f j)
```
where the type `X` is not explicited, that is, any (infinite) 
sequence `f : nat → X` contains a _good pair_ (ie increasing).

An alternative characterization can be implemented at `Type` (informative)
level instead of the `Prop` (non-informative) level with the __nearly__
identical definition:
```coq
Inductive af {X} (R : X → X → Prop) : Type :=
  | af_full : (∀ x y, R x y) → af R
  | af_lift : (∀ a, af (R↑a)) → af R.
```
In that case, the classical property we derive is more informative:
```coq
∀R, af R → ∀f : nat → X, { n | ∃ i j, i < j < n ∧ R (f i) (f j) }
```
and read as follows: for any sequence `f : nat → X`, _one can
compute a bound `n`_ (from information in `af R` and `f`) such that 
below that bound, we know for sure that there is a good pair 
in the initial segment `f₀`,...,`fₙ₋₁`.

In the `Type` case, the `af` predicate is _more informative_ (and
indeed stronger) than in the `Prop` case: it contains a computational
contents.

# Dealing with `Prop` vs `Type`

The library deals with both implementations in a _generic way_, using
the same code base. Indeed, in `Ltac` language, identical proof scripts
can accomodate with the two variants in a uniform way. The actual
Coq lambda-terms produced by these scripts differ however.

To deal with the `Prop` vs `Type` choice, we define a type notation
`Base` which is either `Base := Prop` or `Base := Type` and an
dependent on this choice, notation for first order like operators:
```
      +------+-----------+---------+----------+--------------+
      | Base |   ⊥ₜ      |   ∨ₜ    |   ∧ₜ     |   ∃ₜ         |
      +------+-----------+---------+----------+--------------+
      | Prop | False     | ∨ / or  | ∧ / and  | ∃ / ex       |
      | Type | Empty_set | + / sum | * / prod | { & } / sigT |
      +------+-----------+---------+----------+--------------+
```
Hence, the definition of `af` becomes
```coq
Inductive af {X} (R : X → X → Prop) : Base :=
  | af_full : (∀ x y, R x y) → af R
  | af_lift : (∀ a, af (R↑a)) → af R.
```

From the point of view of the external interface, if one wants
the `Base := Prop` choice, then the import command would be:
```coq
Form KruskalAfProp Require Export base almost_full.
```
and on the other hand, for the `Base := Type` choice, the import
command would be:
```coq
Form KruskalAfType Require Export base almost_full.
```

It is recommanded to perform this import in a single file using
the `Export` directive so that `Base` would be properly defined
in every single file importing the library.

To conclude, in this setting, the classical property of WQOs is
stated (and proved) as:
```coq
   af R → ∀f : nat → X, ∃ₜ n, ∃ i j, i < j < n ∧ R (f i) (f j)
```
using the generic first order syntax depending on the choice of `Base`.

