import ChainDescent
import ChainDescent.Saturation
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic

/-!
# Association schemes (Tier 2 infrastructure)

Stage T2.1 of the Tier 2 orbit-recovery program. Defines
`AssociationScheme n`: a partition of `Fin n × Fin n` into
`rank + 1` symmetric relations satisfying the **intersection-number
axiom**.

This is the abstract structure underlying Johnson, Hamming, and
distance-regular graph theory. We develop it directly on `Fin n`
(not via `SimpleGraph`) to stay aligned with the `AdjMatrix n`
representation used by `ChainDescent.lean`.

## Roadmap

1. **§1 (this revision)** — `AssociationScheme n` structure +
   `relOfPair` helper + symmetry/diagonal lemmas.
2. **§2 (T2.1.b)** — `SchurianScheme` extension (relations are
   exactly Aut-orbital classes).
3. **§3 (T2.1.c)** — Concrete smoke test.
4. **T2.2** — `vProfile`, Step 1 (algebraic).
5. **T2.3** — Step 2 (intersection-number induction).
6. **T2.M4** — `SchemeProfile` constructor, discharge
   `schurian_scheme_profile_exists` axiom from
   `ChainDescent.lean §18`.

References:
- `docs/chain-descent-orbit-recovery.md §14.1, §14.3` — paper proofs.
- `docs/chain-descent-tier2-lean-plan.md` — phase plan and parallels
  to Tier 1's OddDegree discharge.
- Bannai-Ito (1984) "Algebraic Combinatorics I" — classical reference.
-/

namespace ChainDescent

/-! ## §1 — `AssociationScheme`: the basic structure -/

/-- A **symmetric association scheme** on `Fin n`: a partition of
`Fin n × Fin n` into `rank + 1` symmetric relations
`R_0, R_1, …, R_rank` (with `R_0` the diagonal), together with
well-defined intersection numbers `p^k_{ij}`.

**Encoding.** `rel i v w = true` iff `(v, w) ∈ R_i`. The
`rel_partition` field forces each ordered pair to inhabit exactly
one relation.

**Intersection-number axiom** (the load-bearing content). For any
`(v, w) ∈ R_k`, the count of intermediate `u` with `(v, u) ∈ R_i`
and `(u, w) ∈ R_j` depends only on `(i, j, k)` — never on the
specific pair `(v, w)`. This is what makes 1-WL refinement capture
the scheme partition (Theorem 2's Step 2).

A *schurian* scheme additionally has relations matching `Aut(G)`'s
orbital classes; that extension lives in `§2` (to come). -/
structure AssociationScheme (n : Nat) where
  /-- Number of non-diagonal relations (so `rank + 1` relations
  total, counting `R_0`). -/
  rank : Nat
  /-- `rel i v w = true` iff the ordered pair `(v, w)` lies in
  relation `R_i`. -/
  rel : Fin (rank + 1) → Fin n → Fin n → Bool
  /-- `R_0` is the diagonal. -/
  rel_zero_iff_eq : ∀ v w : Fin n, rel 0 v w = true ↔ v = w
  /-- Each relation is symmetric. -/
  rel_symm : ∀ (i : Fin (rank + 1)) (v w : Fin n),
    rel i v w = rel i w v
  /-- The relations partition `Fin n × Fin n`: every ordered pair
  is in exactly one. -/
  rel_partition : ∀ v w : Fin n, ∃! i : Fin (rank + 1), rel i v w = true
  /-- The **intersection number** `p^k_{ij}`: the count of
  intermediate `u`'s for a `R_k`-pair. -/
  intersectionNumber : Fin (rank + 1) → Fin (rank + 1) → Fin (rank + 1) → Nat
  /-- **The defining axiom**: for any `(v, w) ∈ R_k`, the number of
  `u` with `(v, u) ∈ R_i` and `(u, w) ∈ R_j` equals
  `intersectionNumber i j k`. Depends only on `(i, j, k)`, never on
  the specific pair. -/
  intersectionNumber_well_defined :
    ∀ (i j k : Fin (rank + 1)) (v w : Fin n),
      rel k v w = true →
      (Finset.univ.filter
        (fun u : Fin n => rel i v u = true ∧ rel j u w = true)).card
        = intersectionNumber i j k

namespace AssociationScheme

variable {n : Nat} (S : AssociationScheme n)

/-! ### §1.1 — `relOfPair`: the unique relation containing a given pair

`relOfPair v w` returns the index `i : Fin (S.rank + 1)` for which
`rel i v w = true` — the relation that contains the ordered pair
`(v, w)`. Existence and uniqueness come from `rel_partition`.

Pure consequences of the partition axiom; no `intersectionNumber`
content yet. The downstream `vProfile` (T2.2.a) will be defined in
terms of `relOfPair` applied to `(individualized vertex, w)`. -/

/-- The unique relation index containing the ordered pair `(v, w)`. -/
noncomputable def relOfPair (v w : Fin n) : Fin (S.rank + 1) :=
  (S.rel_partition v w).exists.choose

/-- `(v, w)` lies in `R_{relOfPair v w}`. -/
theorem rel_relOfPair (v w : Fin n) :
    S.rel (S.relOfPair v w) v w = true :=
  (S.rel_partition v w).exists.choose_spec

/-- Uniqueness: any relation containing `(v, w)` is `relOfPair v w`. -/
theorem relOfPair_unique {v w : Fin n} {i : Fin (S.rank + 1)}
    (h : S.rel i v w = true) : i = S.relOfPair v w :=
  ExistsUnique.unique (S.rel_partition v w) h (S.rel_relOfPair v w)

/-- Characterisation: `rel i v w = true ↔ i = relOfPair v w`. -/
theorem rel_iff_relOfPair {v w : Fin n} {i : Fin (S.rank + 1)} :
    S.rel i v w = true ↔ i = S.relOfPair v w :=
  ⟨S.relOfPair_unique, fun h => h ▸ S.rel_relOfPair v w⟩

/-- `relOfPair` is symmetric (relations are symmetric). -/
theorem relOfPair_symm (v w : Fin n) :
    S.relOfPair v w = S.relOfPair w v := by
  apply S.relOfPair_unique
  rw [S.rel_symm]
  exact S.rel_relOfPair v w

/-- `relOfPair v v = 0`: the diagonal sits in `R_0`. -/
theorem relOfPair_self (v : Fin n) : S.relOfPair v v = 0 := by
  symm
  apply S.relOfPair_unique
  exact (S.rel_zero_iff_eq v v).mpr rfl

/-- `relOfPair v w = 0 ↔ v = w`: the diagonal characterisation. -/
theorem relOfPair_eq_zero_iff (v w : Fin n) :
    S.relOfPair v w = 0 ↔ v = w := by
  constructor
  · intro h
    have hr : S.rel 0 v w = true := h ▸ S.rel_relOfPair v w
    exact (S.rel_zero_iff_eq v w).mp hr
  · rintro rfl
    exact S.relOfPair_self v

/-! ### §1.2 — Closed subsets and primitivity (Exhaustive-Obstruction Lemma, scheme leg)

The association-scheme form of a **block system**. A subset `I` of the relations, containing the
diagonal `R_0` and **closed under the complex product** (if `R_i, R_j ∈ I` and `R_k` can occur as a
composite, `intersectionNumber i j k ≠ 0`, then `R_k ∈ I`), induces an equivalence relation
`schemeEquiv I` whose union `⋃_{i ∈ I} R_i` is exactly the block system. Crucially it is a **union of
scheme relations**, so on a schurian scheme graph — where 1-WL computes the scheme — it is
**refinement-visible**: this is what makes the EOL's primitivity bridge tractable on schemes (block ⟹
closed subset ⟹ refinement-visible split ⟹ cascade), where it is subtle in general graphs. A scheme is
**primitive** when its only closed subsets are the diagonal `{R_0}` and the whole relation set — the
Cameron-free, scheme-theoretic primitivity the EOL's leg C needs on coherent-configuration residuals. -/

/-- A relation subset `I` is **closed** when it contains the diagonal `R_0` and is closed under the
complex (relational) product: `R_i, R_j ∈ I` and `intersectionNumber i j k ≠ 0` force `R_k ∈ I`. The
association-scheme form of a block system / sub-equivalence. -/
def ClosedSubset (I : Finset (Fin (S.rank + 1))) : Prop :=
  (0 : Fin (S.rank + 1)) ∈ I ∧
    ∀ i ∈ I, ∀ j ∈ I, ∀ k, S.intersectionNumber i j k ≠ 0 → k ∈ I

/-- The equivalence candidate induced by a relation subset: `v ~ w` iff `(v, w)`'s relation lies in
`I`. Under `ClosedSubset` this is a genuine equivalence (`schemeEquiv_equivalence`), the block system. -/
def schemeEquiv (I : Finset (Fin (S.rank + 1))) (v w : Fin n) : Prop :=
  S.relOfPair v w ∈ I

theorem schemeEquiv_refl {I : Finset (Fin (S.rank + 1))} (hI : (0 : Fin (S.rank + 1)) ∈ I)
    (v : Fin n) : S.schemeEquiv I v v := by
  unfold schemeEquiv; rw [S.relOfPair_self]; exact hI

theorem schemeEquiv_symm {I : Finset (Fin (S.rank + 1))} {v w : Fin n}
    (h : S.schemeEquiv I v w) : S.schemeEquiv I w v := by
  unfold schemeEquiv at *; rwa [S.relOfPair_symm]

/-- **Transitivity from closure under the complex product.** If `v ~ w` (`(v,w) ∈ R_i`, `i ∈ I`) and
`w ~ x` (`(w,x) ∈ R_j`, `j ∈ I`), then `w` itself witnesses `intersectionNumber i j (relOfPair v x) ≠ 0`,
so the closure clause puts `relOfPair v x ∈ I`, i.e. `v ~ x`. This is where the scheme's intersection
numbers do the work a raw block system could not. -/
theorem schemeEquiv_trans {I : Finset (Fin (S.rank + 1))} (hcl : S.ClosedSubset I)
    {v w x : Fin n} (h1 : S.schemeEquiv I v w) (h2 : S.schemeEquiv I w x) :
    S.schemeEquiv I v x := by
  unfold schemeEquiv at *
  have hk : S.intersectionNumber (S.relOfPair v w) (S.relOfPair w x) (S.relOfPair v x) ≠ 0 := by
    have hcard := S.intersectionNumber_well_defined (S.relOfPair v w) (S.relOfPair w x)
      (S.relOfPair v x) v x (S.rel_relOfPair v x)
    have hw : w ∈ Finset.univ.filter
        (fun u : Fin n => S.rel (S.relOfPair v w) v u = true ∧ S.rel (S.relOfPair w x) u x = true) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨S.rel_relOfPair v w, S.rel_relOfPair w x⟩
    rw [← hcard]
    exact Finset.card_ne_zero.mpr ⟨w, hw⟩
  exact hcl.2 (S.relOfPair v w) h1 (S.relOfPair w x) h2 (S.relOfPair v x) hk

/-- A closed subset's induced relation is a genuine **equivalence relation** — the block system. -/
theorem schemeEquiv_equivalence {I : Finset (Fin (S.rank + 1))} (hcl : S.ClosedSubset I) :
    Equivalence (S.schemeEquiv I) :=
  ⟨S.schemeEquiv_refl hcl.1, S.schemeEquiv_symm, fun h1 h2 => S.schemeEquiv_trans hcl h1 h2⟩

/-- The whole relation set is always a closed subset (the trivial "one block" system). -/
theorem closedSubset_univ : S.ClosedSubset Finset.univ :=
  ⟨Finset.mem_univ _, fun _ _ _ _ k _ => Finset.mem_univ k⟩

/-- A scheme is **primitive** when its only closed subsets are the diagonal `{R_0}` and the whole
relation set — no non-trivial block system. The scheme-theoretic, Cameron-free primitivity for the
Exhaustive-Obstruction Lemma's leg C on coherent-configuration residuals. -/
def IsPrimitive : Prop :=
  ∀ I : Finset (Fin (S.rank + 1)), S.ClosedSubset I →
    I = {0} ∨ I = Finset.univ

end AssociationScheme

/-! ## §2 — Scheme automorphisms and `SchurianScheme`

A **scheme automorphism** is a permutation of `Fin n` preserving
every relation of `S`. The scheme automorphism group of `S` carries
the scheme's symmetry — in a schurian scheme, this group is precisely
the graph automorphism group of any scheme graph built from `S`.

A scheme is **schurian** when its relations are exactly the orbits
of its automorphism group acting diagonally on `Fin n × Fin n`. The
forward direction (orbits ⊆ relations) is automatic from
`IsSchemeAut`'s definition; the **non-trivial direction** — that
*every* pair in `R_i` is `Aut`-related to every other — is what the
schurian field axiomatises.

Schurianness is what makes Theorem 2's Step 1 work: at a fixed
vertex `v`, the `v`-profile classes (level sets of `relOfPair v ·`)
coincide with the `Aut_v`-orbits. -/

/-- **Scheme automorphism.** A permutation of `Fin n` preserving
every relation index. -/
def IsSchemeAut {n : Nat} (S : AssociationScheme n)
    (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ (i : Fin (S.rank + 1)) (v w : Fin n),
    S.rel i (π v) (π w) = S.rel i v w

namespace IsSchemeAut

variable {n : Nat} {S : AssociationScheme n}

/-- The identity permutation is a scheme automorphism. -/
theorem refl : IsSchemeAut S (Equiv.refl (Fin n)) := fun _ _ _ => rfl

/-- Composition of scheme automorphisms is a scheme automorphism. -/
theorem trans {π σ : Equiv.Perm (Fin n)}
    (hπ : IsSchemeAut S π) (hσ : IsSchemeAut S σ) :
    IsSchemeAut S (π.trans σ) := by
  intro i v w
  show S.rel i (σ (π v)) (σ (π w)) = S.rel i v w
  rw [hσ, hπ]

/-- The inverse of a scheme automorphism is a scheme automorphism. -/
theorem symm {π : Equiv.Perm (Fin n)}
    (hπ : IsSchemeAut S π) : IsSchemeAut S π.symm := by
  intro i v w
  have h := hπ i (π.symm v) (π.symm w)
  simp only [Equiv.apply_symm_apply] at h
  exact h.symm

/-- Scheme automorphisms preserve `relOfPair`: if `π` is a scheme
automorphism then `relOfPair (π v) (π w) = relOfPair v w`. -/
theorem relOfPair_eq {π : Equiv.Perm (Fin n)} (hπ : IsSchemeAut S π)
    (v w : Fin n) :
    S.relOfPair (π v) (π w) = S.relOfPair v w := by
  symm
  apply S.relOfPair_unique
  have h := hπ (S.relOfPair v w) v w
  rw [h]
  exact S.rel_relOfPair v w

end IsSchemeAut

/-- A **schurian association scheme**: relations are exactly the
orbits of `IsSchemeAut` acting diagonally on pairs. The non-trivial
content is the `schurian` field — for any two pairs in the same
relation, some scheme automorphism sends one to the other. -/
structure SchurianScheme (n : Nat) extends AssociationScheme n where
  /-- **The schurian axiom.** Any two pairs in the same relation are
  connected by some scheme automorphism. -/
  schurian :
    ∀ (i : Fin (rank + 1)) (v w v' w' : Fin n),
      rel i v w = true → rel i v' w' = true →
      ∃ π : Equiv.Perm (Fin n),
        IsSchemeAut toAssociationScheme π ∧ π v = v' ∧ π w = w'

/-! ## §3 — Smoke test: the trivial scheme on a single vertex

A minimal example confirming `AssociationScheme` and `SchurianScheme`
are inhabited. On `Fin 1` there is only the diagonal pair `(0, 0)`;
the trivial scheme has rank 0, single relation `R_0`, and the
identity is its only (trivially schurian) automorphism.

Heavier examples (Johnson `J(m, k)`, Hamming, K_n) require explicit
intersection-number computations and live downstream of `T2.2-T2.M4`. -/

/-- The trivial scheme on a single vertex. Smoke test confirming
`AssociationScheme` is inhabited. -/
def trivialScheme : AssociationScheme 1 where
  rank := 0
  rel := fun _ _ _ => true
  rel_zero_iff_eq := fun v w =>
    ⟨fun _ => Subsingleton.elim v w, fun _ => rfl⟩
  rel_symm := fun _ _ _ => rfl
  rel_partition := fun _ _ =>
    ⟨0, rfl, fun i _ => Fin.ext (by have := i.isLt; omega)⟩
  intersectionNumber := fun _ _ _ => 1
  intersectionNumber_well_defined := by
    intro i j k v w _
    show (Finset.univ.filter
      (fun u : Fin 1 => (true : Bool) = true ∧ (true : Bool) = true)).card = 1
    rw [Finset.filter_true_of_mem (fun _ _ => ⟨rfl, rfl⟩)]
    rfl

/-- The trivial scheme is schurian: only the identity is needed
(`Fin 1` has only one permutation). -/
def trivialSchurianScheme : SchurianScheme 1 where
  toAssociationScheme := trivialScheme
  schurian := by
    intro _ v w v' w' _ _
    refine ⟨Equiv.refl _, IsSchemeAut.refl, ?_, ?_⟩
    · exact Subsingleton.elim _ _
    · exact Subsingleton.elim _ _

/-! ## §4 — `vProfile` and Step 1 (the algebraic half)

Stage T2.2 of the Tier 2 Lean program: the **v-profile** of a vertex
`w` (relative to a fixed individualized vertex `v`) is the index of
the scheme relation containing `(v, w)`. The level sets of `vProfile
S v ·` partition `Fin n` into the **profile classes** of `v`.

**Step 1 of Theorem 2's paper proof:** for a schurian scheme,
profile classes coincide with v-stabilized scheme-Aut orbits.

The proofs in this section are purely scheme-theoretic — no graph,
no `refineStep`. The bridge from `SchemeOrbitPartition` (defined
here, in terms of `IsSchemeAut`) to `OrbitPartition` (defined in
`ChainDescent.lean §16.3`, in terms of graph `IsAut`) is established
in T2.M4 once a `SchemeGraph` structure ties the scheme to a concrete
graph adjacency. -/

/-- The **v-profile** colouring: `w ↦ (the index of the scheme
relation containing `(v, w)`).val : Nat`.

Note that `vProfile S v v = 0` (since `(v, v) ∈ R_0`); for `w ≠ v`,
`vProfile S v w ≥ 1`. So `v` is automatically a singleton in
`vProfile S v ·`'s partition — no special offset needed.

Noncomputable because `relOfPair` is. -/
noncomputable def vProfile (S : AssociationScheme n) (v : Fin n) : Colouring n :=
  fun w => (S.relOfPair v w).val

namespace AssociationScheme

variable {n : Nat} (S : AssociationScheme n)

/-- `vProfile S v v = 0`. -/
theorem vProfile_self (v : Fin n) : vProfile S v v = 0 := by
  unfold vProfile
  rw [S.relOfPair_self]
  rfl

/-- `vProfile S v w = vProfile S v u ↔ relOfPair v w = relOfPair v u`. -/
theorem vProfile_eq_iff (v w u : Fin n) :
    vProfile S v w = vProfile S v u ↔ S.relOfPair v w = S.relOfPair v u :=
  ⟨Fin.ext, fun h => congrArg Fin.val h⟩

/-- `vProfile S v w = 0 ↔ w = v`: the diagonal-relation form of
`relOfPair_eq_zero_iff`. -/
theorem vProfile_eq_zero_iff (v w : Fin n) :
    vProfile S v w = 0 ↔ w = v := by
  unfold vProfile
  constructor
  · intro h
    have h0 : S.relOfPair v w = 0 := Fin.ext h
    have := (S.relOfPair_eq_zero_iff v w).mp h0
    exact this.symm
  · rintro rfl
    rw [S.relOfPair_self]
    rfl

/-- **v is a singleton in `vProfile S v ·`.** Direct consequence of
`vProfile_eq_zero_iff`: for `w ≠ v`, `vProfile S v w ≠ vProfile S v v
= 0`. Matches the `SchemeProfile.v_singleton` field. -/
theorem vProfile_ne_self_of_ne {v w : Fin n} (h : w ≠ v) :
    vProfile S v w ≠ vProfile S v v := by
  rw [S.vProfile_self]
  intro h_eq
  exact h ((S.vProfile_eq_zero_iff v w).mp h_eq)

end AssociationScheme

/-! ### §4.1 — `SchemeOrbitPartition`: v-stabilized scheme-Aut orbits

The scheme-theoretic analogue of `ChainDescent.OrbitPartition` (which
uses graph-`IsAut`). `SchemeOrbitPartition S v w u` holds when some
scheme automorphism `π` with `π v = v` sends `w` to `u`.

The eventual graph-orbit bridge (T2.M4): every scheme-Aut of a
schurian scheme is a graph-Aut of its scheme graph, and vice versa,
so the two orbit relations coincide. Here we work scheme-internally
so we can complete Step 1 without needing the SchemeGraph type. -/

/-- **v-stabilized scheme-Aut orbit.** -/
def SchemeOrbitPartition {n : Nat} (S : AssociationScheme n)
    (v w u : Fin n) : Prop :=
  ∃ π : Equiv.Perm (Fin n),
    IsSchemeAut S π ∧ π v = v ∧ π w = u

namespace SchemeOrbitPartition

variable {n : Nat} {S : AssociationScheme n} {v : Fin n}

/-- Reflexivity. -/
theorem refl (v w : Fin n) : SchemeOrbitPartition S v w w :=
  ⟨Equiv.refl _, IsSchemeAut.refl, rfl, rfl⟩

/-- Symmetry. -/
theorem symm {w u : Fin n} (h : SchemeOrbitPartition S v w u) :
    SchemeOrbitPartition S v u w := by
  obtain ⟨π, hπ, hπv, hπw⟩ := h
  refine ⟨π.symm, hπ.symm, ?_, ?_⟩
  · have := congrArg π.symm hπv
    simpa using this.symm
  · have := congrArg π.symm hπw
    simpa using this.symm

/-- Transitivity. -/
theorem trans {w u t : Fin n}
    (h₁ : SchemeOrbitPartition S v w u) (h₂ : SchemeOrbitPartition S v u t) :
    SchemeOrbitPartition S v w t := by
  obtain ⟨π₁, hπ₁, hπ₁v, hπ₁w⟩ := h₁
  obtain ⟨π₂, hπ₂, hπ₂v, hπ₂u⟩ := h₂
  refine ⟨π₁.trans π₂, hπ₁.trans hπ₂, ?_, ?_⟩
  · show π₂ (π₁ v) = v
    rw [hπ₁v, hπ₂v]
  · show π₂ (π₁ w) = t
    rw [hπ₁w]; exact hπ₂u

end SchemeOrbitPartition

/-! ### §4.2 — Step 1: vProfile classes = SchemeOrbitPartition classes

The two directions:
- **S1.a** (`vProfile_aut_invariant`): a v-stabilizing scheme-Aut
  preserves `vProfile`. Uses `IsSchemeAut.relOfPair_eq`.
- **S1.b** (`vProfile_eq_imp_schemeOrbit`): if two vertices have
  the same `vProfile`, some v-stabilizing scheme-Aut connects them.
  Uses the schurian axiom directly.

Combined: `vProfile_iff_schemeOrbit` characterises profile equality
exactly as v-stabilized scheme-Aut orbit equivalence — Theorem 2's
Step 1. -/

namespace AssociationScheme

variable {n : Nat} (S : AssociationScheme n)

/-- **S1.a — `vProfile` is invariant under v-stabilizing scheme
automorphisms.** If `π v = v` and `π` is a scheme automorphism,
then `vProfile S v (π w) = vProfile S v w` for every `w`. -/
theorem vProfile_aut_invariant (v : Fin n) {π : Equiv.Perm (Fin n)}
    (hπ : IsSchemeAut S π) (hπv : π v = v) (w : Fin n) :
    vProfile S v (π w) = vProfile S v w := by
  unfold vProfile
  congr 1
  have h := hπ.relOfPair_eq v w
  rw [hπv] at h
  exact h

end AssociationScheme

/-- **Trivial direction (S1.a packaged): `SchemeOrbitPartition`
refines `vProfile`-equality.** -/
theorem vProfile_eq_of_schemeOrbit {n : Nat} {S : AssociationScheme n}
    {v w u : Fin n} (h : SchemeOrbitPartition S v w u) :
    vProfile S v w = vProfile S v u := by
  obtain ⟨π, hπ, hπv, hπw⟩ := h
  have hinv := S.vProfile_aut_invariant v hπ hπv w
  rw [hπw] at hinv
  exact hinv.symm

/-! ### §4.2.1 — The block system is a system of imprimitivity (EOL scheme leg, the bridge)

A `ClosedSubset`'s block system `schemeEquiv I` is preserved by every scheme automorphism, and is
coarser than the v-stabilized scheme-Aut orbits. So scheme-imprimitivity (a non-trivial `ClosedSubset`,
`¬IsPrimitive`) is a genuine **Aut-invariant block structure** — the bridge from the combinatorial
closed subset to the group/orbit action the Exhaustive-Obstruction Lemma's leg C needs. Composed with
orbit recovery (`theorem_2_HOR_of_pPolynomial`: at depth 1 the v-orbits = `warmRefine` cells), the block
of `v` is a union of `warmRefine` cells — **refinement-visible** — so an imprimitive scheme cascades
(the cell splits along the blocks). Contrapositive: a non-cascade scheme is primitive. -/

/-- **The block system is scheme-automorphism-invariant.** For a scheme automorphism `π`,
`schemeEquiv I (π v) (π w) ↔ schemeEquiv I v w` — the closed subset's induced partition is preserved by
the symmetry, i.e. a genuine system of imprimitivity. Immediate from `IsSchemeAut.relOfPair_eq`. -/
theorem schemeEquiv_isSchemeAut {n : Nat} {S : AssociationScheme n}
    {I : Finset (Fin (S.rank + 1))} {π : Equiv.Perm (Fin n)} (hπ : IsSchemeAut S π) (v w : Fin n) :
    S.schemeEquiv I (π v) (π w) ↔ S.schemeEquiv I v w := by
  unfold AssociationScheme.schemeEquiv
  rw [hπ.relOfPair_eq v w]

/-- **The block of `v` is a union of v-stabilized scheme-Aut orbits** (the block system is coarser than
the orbit partition): if `w` and `u` lie in the same `v`-orbit, they share their `schemeEquiv I`
block. With orbit recovery (v-orbits = `warmRefine` cells) this makes the block refinement-visible — the
content that turns scheme-imprimitivity into a cascade. -/
theorem schemeEquiv_schemeOrbit {n : Nat} {S : AssociationScheme n}
    {I : Finset (Fin (S.rank + 1))} {v w u : Fin n} (h : SchemeOrbitPartition S v w u) :
    S.schemeEquiv I v w ↔ S.schemeEquiv I v u := by
  obtain ⟨π, hπ, hπv, hπw⟩ := h
  have key : S.relOfPair v u = S.relOfPair v w := by
    have h := hπ.relOfPair_eq v w
    rw [hπv, hπw] at h
    exact h
  unfold AssociationScheme.schemeEquiv
  rw [key]

namespace SchurianScheme

variable {n : Nat} (S : SchurianScheme n)

/-- **S1.b — vProfile-equality implies v-stabilized scheme-Aut
orbit equivalence.** Under the schurian assumption, two vertices
with the same `vProfile` are connected by some scheme automorphism
fixing `v`. -/
theorem vProfile_eq_imp_schemeOrbit (v w u : Fin n)
    (h : vProfile S.toAssociationScheme v w =
         vProfile S.toAssociationScheme v u) :
    SchemeOrbitPartition S.toAssociationScheme v w u := by
  have hrel : S.relOfPair v w = S.relOfPair v u := Fin.ext h
  -- Apply schurian at i = relOfPair v w with pairs (v, w) and (v, u).
  obtain ⟨π, hπ, hπv, hπw⟩ :=
    S.schurian (S.relOfPair v w) v w v u
      (S.rel_relOfPair v w) (hrel ▸ S.rel_relOfPair v u)
  exact ⟨π, hπ, hπv, hπw⟩

/-- **Step 1 of Theorem 2 (combined).** For a schurian scheme,
profile equality at `v` is exactly v-stabilized scheme-Aut orbit
equivalence. Matches the eventual `SchemeProfile.profile_iff_orbit`
field shape (up to the graph-Aut bridge supplied in T2.M4). -/
theorem vProfile_iff_schemeOrbit (v w u : Fin n) :
    vProfile S.toAssociationScheme v w =
      vProfile S.toAssociationScheme v u ↔
    SchemeOrbitPartition S.toAssociationScheme v w u :=
  ⟨S.vProfile_eq_imp_schemeOrbit v w u,
   fun h => vProfile_eq_of_schemeOrbit h⟩

end SchurianScheme

/-! ## §5 — `SchemeGraph`: a scheme + a designated edge-relation set

A **scheme graph** is an `AssociationScheme` together with a subset
`J ⊆ {1, …, rank}` of non-diagonal relations marked as edges. The
graph's adjacency is then `adj v w = 1 ↔ relOfPair v w ∈ J`.

Johnson `J(m, k)`'s scheme has relations `R_j = {(A, B) : |A ∩ B| = k − j}`
for `j = 0, …, k`; the Johnson **graph** picks `J = {1}` (overlap
`k − 1`). Hamming graphs and distance-regular graphs follow the same
pattern with different relations and `J`.

Stage T2.M4 will build `SchurianSchemeGraph` extending this with
graph-Aut schurian properties, then discharge the
`schurian_scheme_profile_exists` axiom from `ChainDescent.lean §18`. -/

/-- A graph derived from an association scheme by designating a set
of relation indices `J` as edges. `0 ∉ J` ensures the diagonal
isn't an edge (graph is loopless). -/
structure SchemeGraph (n : Nat) where
  /-- The underlying association scheme. -/
  scheme : AssociationScheme n
  /-- The designated edge-relation set. -/
  J : Finset (Fin (scheme.rank + 1))
  /-- `0 ∉ J`: the diagonal `R_0` is not an edge (loopless). -/
  zero_notMem_J : (0 : Fin (scheme.rank + 1)) ∉ J

namespace SchemeGraph

variable {n : Nat} (G : SchemeGraph n)

/-- The derived adjacency matrix: `(v, w)` is an edge iff the
relation containing `(v, w)` is in `J`. -/
noncomputable def adj : AdjMatrix n :=
  ⟨fun v w => if G.scheme.relOfPair v w ∈ G.J then 1 else 0⟩

/-- Adjacency characterisation. -/
theorem adj_eq_one_iff (v w : Fin n) :
    G.adj.adj v w = 1 ↔ G.scheme.relOfPair v w ∈ G.J := by
  show (if G.scheme.relOfPair v w ∈ G.J then 1 else 0) = 1 ↔ _
  by_cases h : G.scheme.relOfPair v w ∈ G.J <;> simp [h]

/-- Non-adjacency characterisation. -/
theorem adj_eq_zero_iff (v w : Fin n) :
    G.adj.adj v w = 0 ↔ G.scheme.relOfPair v w ∉ G.J := by
  show (if G.scheme.relOfPair v w ∈ G.J then 1 else 0) = 0 ↔ _
  by_cases h : G.scheme.relOfPair v w ∈ G.J <;> simp [h]

/-- Loopless: `adj v v = 0`. -/
theorem adj_self (v : Fin n) : G.adj.adj v v = 0 := by
  rw [G.adj_eq_zero_iff, G.scheme.relOfPair_self]
  exact G.zero_notMem_J

/-- Symmetric: `adj v w = adj w v`. -/
theorem adj_symm (v w : Fin n) : G.adj.adj v w = G.adj.adj w v := by
  show (if G.scheme.relOfPair v w ∈ G.J then 1 else 0)
       = (if G.scheme.relOfPair w v ∈ G.J then 1 else 0)
  rw [G.scheme.relOfPair_symm]

/-- Adjacency takes values in `{0, 1}`. -/
theorem adj_eq_zero_or_one (v w : Fin n) :
    G.adj.adj v w = 0 ∨ G.adj.adj v w = 1 := by
  show (if G.scheme.relOfPair v w ∈ G.J then 1 else 0) = 0
       ∨ (if G.scheme.relOfPair v w ∈ G.J then 1 else 0) = 1
  by_cases h : G.scheme.relOfPair v w ∈ G.J <;> simp [h]

end SchemeGraph

/-! ## §6 — `SchurianSchemeGraph`: scheme graph with graph-Aut schurian

A scheme graph is **schurian (w.r.t. graph-Aut)** when its relations
are exactly the orbits of `Aut(adj)` acting diagonally on
`Fin n × Fin n`. This requires two facts:

1. **`schurian_transitive`**: any two pairs in the same relation are
   connected by a graph automorphism. (Orbits ⊇ relations.)
2. **`isAut_imp_isSchemeAut`**: every graph automorphism preserves
   every relation. (Orbits ⊆ relations.)

Both are needed: schurian_transitive on its own doesn't imply
isAut_imp_isSchemeAut (a graph-Aut might cross relation boundaries
without violating intra-relation transitivity). For Johnson, Hamming,
and distance-transitive DRGs both hold; this is the working
hypothesis bundle for Theorem 2's discharge in T2.M4.

A concrete witness for the trivial 1-vertex scheme is given in §7;
heavier examples (`JohnsonSchurianSchemeGraph m k`) are deferred. -/

/-- A scheme graph satisfying the schurian property w.r.t. graph
automorphisms. -/
structure SchurianSchemeGraph (n : Nat) extends SchemeGraph n where
  /-- **Schurian transitive direction.** Any two pairs in the same
  relation `R_i` are connected by some graph automorphism. -/
  schurian_transitive :
    ∀ (i : Fin (scheme.rank + 1)) (v w v' w' : Fin n),
      scheme.rel i v w = true → scheme.rel i v' w' = true →
      ∃ π : Equiv.Perm (Fin n),
        IsAut π toSchemeGraph.adj ∧ π v = v' ∧ π w = w'
  /-- **Schurian invariance direction.** Every graph automorphism
  preserves every relation (i.e., is a scheme automorphism). -/
  isAut_imp_isSchemeAut :
    ∀ {π : Equiv.Perm (Fin n)},
      IsAut π toSchemeGraph.adj → IsSchemeAut scheme π

namespace SchurianSchemeGraph

variable {n : Nat} (G : SchurianSchemeGraph n)

/-- Graph automorphisms preserve `relOfPair`. Direct consequence of
`isAut_imp_isSchemeAut`. -/
theorem relOfPair_aut_eq {π : Equiv.Perm (Fin n)}
    (hπ : IsAut π G.toSchemeGraph.adj) (v w : Fin n) :
    G.scheme.relOfPair (π v) (π w) = G.scheme.relOfPair v w :=
  (G.isAut_imp_isSchemeAut hπ).relOfPair_eq v w

/-- Graph automorphisms preserve `vProfile`: if `π v = v` and
`π` is a graph automorphism, then `vProfile S v (π w) = vProfile S v w`. -/
theorem vProfile_aut_invariant (v : Fin n) {π : Equiv.Perm (Fin n)}
    (hπ : IsAut π G.toSchemeGraph.adj) (hπv : π v = v) (w : Fin n) :
    vProfile G.scheme v (π w) = vProfile G.scheme v w :=
  G.scheme.vProfile_aut_invariant v (G.isAut_imp_isSchemeAut hπ) hπv w

end SchurianSchemeGraph

/-! ## §7 — Step 1 in graph-Aut terms

`vProfile`-equality coincides with the orbit relation "`∃ π ∈ Aut(adj)`
with `π v = v` and `π w = u`". The forward direction uses
`schurian_transitive`; the reverse uses `isAut_imp_isSchemeAut` via
`vProfile_aut_invariant`.

`GraphOrbitFixing adj v w u` is the v-stabilized graph-Aut orbit
predicate; it matches `OrbitPartition adj P {v} w u` (defined in
`ChainDescent.lean §16.3`) for `P` whose entries are all
permutation-invariant (e.g., the trivial all-`unknown` matrix). The
P-aware bridge will be supplied in T2.M4. -/

/-- The v-stabilized graph-Aut orbit relation (without P-preservation
constraints). Equivalent to `OrbitPartition adj P {v} w u` when `P`
is trivially permutation-invariant. -/
def GraphOrbitFixing {n : Nat} (adj : AdjMatrix n) (v w u : Fin n) : Prop :=
  ∃ π : Equiv.Perm (Fin n), IsAut π adj ∧ π v = v ∧ π w = u

namespace GraphOrbitFixing

variable {n : Nat} {adj : AdjMatrix n} {v : Fin n}

theorem refl (v w : Fin n) : GraphOrbitFixing adj v w w :=
  ⟨Equiv.refl _, IsAut.refl, rfl, rfl⟩

theorem symm {w u : Fin n} (h : GraphOrbitFixing adj v w u) :
    GraphOrbitFixing adj v u w := by
  obtain ⟨π, hπ, hπv, hπw⟩ := h
  refine ⟨π.symm, hπ.symm, ?_, ?_⟩
  · have := congrArg π.symm hπv
    simpa using this.symm
  · have := congrArg π.symm hπw
    simpa using this.symm

theorem trans {w u t : Fin n}
    (h₁ : GraphOrbitFixing adj v w u) (h₂ : GraphOrbitFixing adj v u t) :
    GraphOrbitFixing adj v w t := by
  obtain ⟨π₁, hπ₁, hπ₁v, hπ₁w⟩ := h₁
  obtain ⟨π₂, hπ₂, hπ₂v, hπ₂u⟩ := h₂
  refine ⟨π₁.trans π₂, hπ₁.trans hπ₂, ?_, ?_⟩
  · show π₂ (π₁ v) = v; rw [hπ₁v, hπ₂v]
  · show π₂ (π₁ w) = t; rw [hπ₁w]; exact hπ₂u

end GraphOrbitFixing

namespace SchurianSchemeGraph

variable {n : Nat} (G : SchurianSchemeGraph n)

/-- **Step 1 (forward, graph-Aut terms): vProfile-equality implies
graph-orbit equivalence.** Uses `schurian_transitive`. -/
theorem vProfile_eq_imp_graphOrbit (v w u : Fin n)
    (h : vProfile G.scheme v w = vProfile G.scheme v u) :
    GraphOrbitFixing G.toSchemeGraph.adj v w u := by
  have hrel : G.scheme.relOfPair v w = G.scheme.relOfPair v u := Fin.ext h
  obtain ⟨π, hπ, hπv, hπw⟩ :=
    G.schurian_transitive (G.scheme.relOfPair v w) v w v u
      (G.scheme.rel_relOfPair v w) (hrel ▸ G.scheme.rel_relOfPair v u)
  exact ⟨π, hπ, hπv, hπw⟩

/-- **Step 1 (reverse, graph-Aut terms): graph-orbit equivalence
implies vProfile-equality.** Uses `isAut_imp_isSchemeAut`. -/
theorem graphOrbit_imp_vProfile_eq {v w u : Fin n}
    (h : GraphOrbitFixing G.toSchemeGraph.adj v w u) :
    vProfile G.scheme v w = vProfile G.scheme v u := by
  obtain ⟨π, hπ, hπv, hπw⟩ := h
  have hinv := G.vProfile_aut_invariant v hπ hπv w
  rw [hπw] at hinv
  exact hinv.symm

/-- **Step 1 (graph-Aut combined): vProfile equality iff
graph-Aut-orbit equivalence (fixing `v`).** This is the graph-Aut
form of `SchurianScheme.vProfile_iff_schemeOrbit`, and the version
that directly bridges to `OrbitPartition adj P {v}` in T2.M4. -/
theorem vProfile_iff_graphOrbit (v w u : Fin n) :
    vProfile G.scheme v w = vProfile G.scheme v u ↔
    GraphOrbitFixing G.toSchemeGraph.adj v w u :=
  ⟨G.vProfile_eq_imp_graphOrbit v w u,
   fun h => G.graphOrbit_imp_vProfile_eq h⟩

end SchurianSchemeGraph

/-! ## §8 — Step 2 (combinatorial): 1-WL refines vProfile

The substantive technical claim of Theorem 2: under `χ_v =
individualizedColouring n {v}`, the 1-WL fixpoint partition (= the
`warmRefine` colouring) refines the vProfile partition. Together
with Step 1's `vProfile = graph-Aut-orbit-fixing-v` and the trivial
`OrbitPartition.subset_warmRefine`, this gives the equality
`warmRefine partition = vProfile partition = OrbitPartition`.

**Phased proof** (see `docs/chain-descent-tier2-lean-plan.md` for
the full plan):

- **§8.a — S2.a (this revision)**: round-1 lemma. `iter[1] χ_v w
  = iter[1] χ_v u` for `w, u ≠ v` implies `adj w v = adj u v`.
  Generic: holds for any `adj`, `P` (no scheme structure needed).
- **§8.b — S2.b (future)**: inductive refinement at round `k`,
  using intersection-number well-definedness to argue that
  signatures determine `vProfile w` (partially at each round).
- **§8.c — S2.c (future)**: convergence at `k ≤ rank + 1`.
- **§8.d — S2.d (future)**: lift to `warmRefine` via
  `warmRefine_eq_iter_eq` from `ChainDescent.lean §16.4`.
- **§8.e — assembly (future)**: produce the eventual
  `SchemeProfile.warm_refines_profile` field. -/

/-! ### §8.a — S2.a: round-1 distinguishes by adj-to-v

Generic round-1 lemma that holds for ANY `adj`, `P`, and `v` (no
scheme structure required). The intuition: `χ_v` is unique at `v`
(positive colour `v.val + 1`) and zero elsewhere. The
multiset-of-signatures comparison at `iter[1]` forces the tuple from
`u' = v` to match between vertices `w` and `u`, giving `adj w v =
adj u v`.

Useful for both Tier 2's Step 2 (round-1 base case) and any other
depth-1 reasoning. Placed in `Scheme.lean` for now since it's
introduced for Step 2; could move to `ChainDescent.lean §16.4` if
other tiers need it. -/

/-- **Helper: χ_v uniqueness.** `individualizedColouring n {v} u =
individualizedColouring n {v} v` iff `u = v`. Direct consequence of
the definition (positive colour at `v`, zero elsewhere). -/
private theorem individualizedColouring_singleton_eq_v_iff {n : Nat} (v u : Fin n) :
    individualizedColouring n {v} u = individualizedColouring n {v} v ↔
    u = v := by
  constructor
  · intro h
    by_contra hne
    simp only [individualizedColouring, Finset.mem_singleton, hne,
               if_false, if_true] at h
    omega
  · rintro rfl
    rfl

/-- **S2.a: round-1 lemma.** Under `χ_v = individualizedColouring n
{v}`, if two non-`v` vertices `w, u` get the same colour after one
`refineStep`, they have the same adjacency to `v` (and the same
`P · v` value).

The proof packs `(adj w v, P w v) = (adj u v, P u v)` rather than
just `adj w v = adj u v` because the multiset-tuple match gives
both for free; downstream callers typically only need the `adj`
half. -/
theorem refineStep_round1_pair_eq {n : Nat} (adj : AdjMatrix n)
    (P : PMatrix n) {v w u : Fin n} (hwv : w ≠ v) (huv : u ≠ v)
    (h : refineStep adj P (individualizedColouring n {v}) w =
         refineStep adj P (individualizedColouring n {v}) u) :
    adj.adj w v = adj.adj u v ∧ P w v = P u v := by
  set χ := individualizedColouring n {v} with hχ_def
  -- Extract signature equality from refineStep_iff.
  have hsig_eq : signature adj P χ w = signature adj P χ u :=
    ((refineStep_iff adj P χ w u).mp h).2
  -- Witness tuple at u' = v in signature(w): (χ v, adj w v, P w v).
  have htw_in : (χ v, adj.adj w v, P w v) ∈ signature adj P χ w := by
    unfold signature
    refine Multiset.mem_map.mpr ⟨v, ?_, rfl⟩
    rw [Finset.mem_val, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, fun heq => hwv heq.symm⟩
  -- Transport to sig(u) by signature equality.
  have htw_in_sigu : (χ v, adj.adj w v, P w v) ∈ signature adj P χ u :=
    hsig_eq ▸ htw_in
  -- Unfold sig(u) to extract a preimage u' ≠ u.
  unfold signature at htw_in_sigu
  obtain ⟨u', hu'mem, hu'eq⟩ := Multiset.mem_map.mp htw_in_sigu
  rw [Finset.mem_val, Finset.mem_filter] at hu'mem
  -- hu'eq : (χ u', adj u u', P u u') = (χ v, adj w v, P w v)
  -- Project: χ u' = χ v, adj u u' = adj w v, P u u' = P w v.
  have hχ : χ u' = χ v := by
    have := (Prod.mk.injEq _ _ _ _).mp hu'eq
    exact this.1
  have hadj : adj.adj u u' = adj.adj w v := by
    have h1 := (Prod.mk.injEq _ _ _ _).mp hu'eq
    have h2 := (Prod.mk.injEq _ _ _ _).mp h1.2
    exact h2.1
  have hP : P u u' = P w v := by
    have h1 := (Prod.mk.injEq _ _ _ _).mp hu'eq
    have h2 := (Prod.mk.injEq _ _ _ _).mp h1.2
    exact h2.2
  -- χ u' = χ v ⟹ u' = v.
  have hu'v : u' = v := (individualizedColouring_singleton_eq_v_iff v u').mp hχ
  subst hu'v
  -- Now: adj.adj u v = adj.adj w v ∧ P u v = P w v.
  exact ⟨hadj.symm, hP.symm⟩

/-- **S2.a (adj-only form).** Specialisation of
`refineStep_round1_pair_eq` extracting only the `adj`-equality
conjunct — the form typically needed by Step 2's S2.b. -/
theorem refineStep_round1_adj_eq {n : Nat} (adj : AdjMatrix n)
    (P : PMatrix n) {v w u : Fin n} (hwv : w ≠ v) (huv : u ≠ v)
    (h : refineStep adj P (individualizedColouring n {v}) w =
         refineStep adj P (individualizedColouring n {v}) u) :
    adj.adj w v = adj.adj u v :=
  (refineStep_round1_pair_eq adj P hwv huv h).1

/-- **S2.a (specialised to SchemeGraph).** Under `χ_v` for a scheme
graph, round-1 equality implies the two vertices share the J-class
of `relOfPair v ·` (i.e., either both `(v, ·) ∈ ⋃ R_j (j ∈ J)` or
both `(v, ·) ∉ ⋃ R_j (j ∈ J)`). The scheme-internal form of
`refineStep_round1_adj_eq`. -/
theorem SchemeGraph.refineStep_round1_J_eq {n : Nat} (G : SchemeGraph n)
    (P : PMatrix n) {v w u : Fin n} (hwv : w ≠ v) (huv : u ≠ v)
    (h : refineStep G.adj P (individualizedColouring n {v}) w =
         refineStep G.adj P (individualizedColouring n {v}) u) :
    (G.scheme.relOfPair v w ∈ G.J ↔ G.scheme.relOfPair v u ∈ G.J) := by
  -- From S2.a (adj form), adj w v = adj u v.
  have hadj := refineStep_round1_adj_eq G.adj P hwv huv h
  -- adj (v, ·) symmetric, so adj v w = adj v u.
  rw [G.adj_symm w v, G.adj_symm u v] at hadj
  -- adj v · = 1 ↔ relOfPair v · ∈ J.
  rcases G.adj_eq_zero_or_one v w with hw0 | hw1
  · -- adj v w = 0, so relOfPair v w ∉ J.
    have hw_notIn : G.scheme.relOfPair v w ∉ G.J :=
      (G.adj_eq_zero_iff v w).mp hw0
    rw [hw0] at hadj
    have hu0 : G.adj.adj v u = 0 := hadj.symm
    have hu_notIn : G.scheme.relOfPair v u ∉ G.J :=
      (G.adj_eq_zero_iff v u).mp hu0
    exact ⟨fun h => absurd h hw_notIn, fun h => absurd h hu_notIn⟩
  · -- adj v w = 1, so relOfPair v w ∈ J.
    have hw_in : G.scheme.relOfPair v w ∈ G.J :=
      (G.adj_eq_one_iff v w).mp hw1
    rw [hw1] at hadj
    have hu_in : G.scheme.relOfPair v u ∈ G.J :=
      (G.adj_eq_one_iff v u).mp hadj.symm
    exact ⟨fun _ => hu_in, fun _ => hw_in⟩

/-! ### §8.b — S2.b infrastructure: iteration unfolding + intersection counts

Three foundational pieces for the round-by-round induction:
1. `iterSignature`: the signature multiset computed at iter[k] χ_v.
2. `iter_succ_eq_iff`: one-step unfolding via `refineStep_iff`.
3. `intersectionCount_via_w`: scheme-axiom application — counts of
   intermediate vertices by relation-index pairs are determined by
   `relOfPair v w` (hence by `vProfile w`).

These are the building blocks for the eventual S2.b proof. The
inductive step uses `iter_succ_eq_iff` to reduce iter[k+1] equality
to iter[k] equality plus signature equality, then
`intersectionCount_via_w` to interpret the signature counts as
intersection-number sums, then deduce vProfile equality.

The remaining gap is the *convergence* claim: at some bounded k
(≤ rank+1 for schurian schemes via coherent algebra theory),
sufficient signature counts pin down `vProfile`. -/

/-- The signature of `w` computed against the iter[k] refinement of
`χ_v`. Round-(k+1) equality is determined by the round-k colour
plus this signature (per `iter_succ_eq_iff`).

Computable: `signature` and the `refineStep` iterate both reduce (`refineStep`
is concrete since the M0 concretization). -/
def iterSignature {n : Nat} (adj : AdjMatrix n) (P : PMatrix n)
    (v : Fin n) (k : Nat) (w : Fin n) : Multiset (Nat × Nat × POE) :=
  signature adj P (((refineStep adj P)^[k]) (individualizedColouring n {v})) w

/-- **Round-by-round unfolding via `refineStep_iff`.** Equality at
iter[k+1] decomposes into equality at iter[k] plus matching
iter-k signatures. The inductive step's primary tool. -/
theorem iter_succ_eq_iff {n : Nat} (adj : AdjMatrix n) (P : PMatrix n)
    (v : Fin n) (k : Nat) (w u : Fin n) :
    ((refineStep adj P)^[k + 1]) (individualizedColouring n {v}) w =
        ((refineStep adj P)^[k + 1]) (individualizedColouring n {v}) u ↔
      ((refineStep adj P)^[k]) (individualizedColouring n {v}) w =
        ((refineStep adj P)^[k]) (individualizedColouring n {v}) u ∧
      iterSignature adj P v k w = iterSignature adj P v k u := by
  rw [Function.iterate_succ_apply']
  exact refineStep_iff _ _ _ _ _

/-- **Scheme intersection count.** For an association scheme `S` and
any pair `(v, w)`, the count of intermediate vertices `u'` with
`(v, u') ∈ R_i` and `(w, u') ∈ R_l` equals
`intersectionNumber i l (relOfPair v w)`. Direct consequence of
`intersectionNumber_well_defined` plus relation symmetry.

This is the key scheme axiom in usable form: intersection counts
indexed by `(v, w)` depend only on `relOfPair v w` (hence on
`vProfile w`). Step 2's S2.b uses this to argue that iter[k]
signatures aggregate intersection-number values determined by
`vProfile`. -/
theorem AssociationScheme.intersectionCount_via_w {n : Nat}
    (S : AssociationScheme n) (v w : Fin n) (i l : Fin (S.rank + 1)) :
    (Finset.univ.filter
      (fun u' : Fin n => S.rel i v u' = true ∧ S.rel l w u' = true)).card
      = S.intersectionNumber i l (S.relOfPair v w) := by
  -- The axiom statement uses `S.rel l u' w`; we want `S.rel l w u'`.
  -- These coincide by `S.rel_symm`. Rewrite the filter predicate via
  -- `Finset.filter_congr`, then apply the axiom directly.
  have h := S.intersectionNumber_well_defined i l (S.relOfPair v w) v w
              (S.rel_relOfPair v w)
  rw [show (Finset.univ.filter
              (fun u' : Fin n => S.rel i v u' = true ∧ S.rel l w u' = true))
       = (Finset.univ.filter
              (fun u' : Fin n => S.rel i v u' = true ∧ S.rel l u' w = true)) from
    Finset.filter_congr (fun u' _ => by rw [S.rel_symm l w u'])]
  exact h

/-- **Corollary: intersection counts share vProfile dependence.**
If two vertices `w, u` have the same `vProfile` (i.e.,
`relOfPair v w = relOfPair v u`), then for every `(i, l)` their
intersection counts coincide. Trivial corollary of
`intersectionCount_via_w`; included because Step 2's converse
direction (count matches imply vProfile matches) is the actual
content needed. -/
theorem AssociationScheme.intersectionCount_eq_of_vProfile_eq {n : Nat}
    (S : AssociationScheme n) {v w u : Fin n}
    (h : S.relOfPair v w = S.relOfPair v u) (i l : Fin (S.rank + 1)) :
    (Finset.univ.filter
      (fun u' : Fin n => S.rel i v u' = true ∧ S.rel l w u' = true)).card
      = (Finset.univ.filter
          (fun u' : Fin n => S.rel i v u' = true ∧ S.rel l u u' = true)).card := by
  rw [S.intersectionCount_via_w v w i l, S.intersectionCount_via_w v u i l, h]

/-! ### §8.c — Step 2 statement + open gap

The full Step 2 theorem statement, with the convergence step
(S2.b proper + S2.c) marked as an explicit open subgoal. This
keeps the eventual `SchemeProfile` constructor in T2.M4 close at
hand: once the open subgoal is filled, the constructor follows. -/

/-- **Step 2 statement (target).** For a schurian scheme graph and
any compatible `P`, `warmRefine` cells refine `vProfile` classes.
The trivial direction (vProfile ⊆ warmRefine) is `OrbitPartition.subset_warmRefine`
combined with Step 1; this is the substantive opposite direction.

**Status**: not yet proved. S2.a (round-1 lemma) is the base case;
S2.b (inductive intersection-number step) and S2.c (convergence at
depth ≤ rank+1) remain.

When discharged, this directly produces the
`SchemeProfile.warm_refines_profile` field in T2.M4. -/
def Step2_target {n : Nat} (G : SchurianSchemeGraph n) (P : PMatrix n)
    (v : Fin n) : Prop :=
  ∀ w u : Fin n,
    warmRefine G.toSchemeGraph.adj P (individualizedColouring n {v}) w =
      warmRefine G.toSchemeGraph.adj P (individualizedColouring n {v}) u →
    vProfile G.scheme v w = vProfile G.scheme v u

/-! ### §8.b.2 — Count bridge: Multiset.count on signatures → Finset.card

`signature` is a `Multiset.map`; counts via `Multiset.count` correspond
to cardinalities of preimage filters on the underlying Finset. The
bridge lets the inductive step extract concrete vertex counts from
abstract signature equality.

Mathlib's `Multiset.count_map` gives:
> `count b (map f s) = (s.filter (fun a => b = f a)).card`

so combined with `Finset.filter_val` and `Finset.filter_filter` we
collapse the two-level filter (the `(· ≠ w)` filter of `signature`
plus the `count` filter) into a single Finset filter. -/

/-- **Bridge lemma.** Multiset count on a signature equals Finset
cardinality of the matching preimage filter (over `u' ≠ w`). -/
private theorem signature_count_eq_card {n : Nat} (adj : AdjMatrix n) (P : PMatrix n)
    (χ : Colouring n) (w : Fin n) (t : Nat × Nat × POE) :
    Multiset.count t (signature adj P χ w) =
    (Finset.univ.filter (fun u' : Fin n =>
      u' ≠ w ∧ t = (χ u', adj.adj w u', P w u'))).card := by
  unfold signature
  rw [Multiset.count_map, ← Finset.filter_val]
  show (Finset.filter (fun u : Fin n => t = (χ u, adj.adj w u, P w u))
        (Finset.univ.filter (fun u : Fin n => u ≠ w))).card = _
  rw [Finset.filter_filter]

/-- **Count equality from signature equality.** If `signature χ w =
signature χ u`, then for any tuple `t`, the count of `u' ≠ w`
producing `t` from `w` equals the count of `u' ≠ u` producing `t`
from `u`. Direct corollary of `signature_count_eq_card`. -/
private theorem signature_eq_card_eq {n : Nat} (adj : AdjMatrix n) (P : PMatrix n)
    (χ : Colouring n) {w u : Fin n}
    (h : signature adj P χ w = signature adj P χ u)
    (t : Nat × Nat × POE) :
    (Finset.univ.filter (fun u' : Fin n =>
      u' ≠ w ∧ t = (χ u', adj.adj w u', P w u'))).card =
    (Finset.univ.filter (fun u' : Fin n =>
      u' ≠ u ∧ t = (χ u', adj.adj u u', P u u'))).card := by
  rw [← signature_count_eq_card adj P χ w t,
      ← signature_count_eq_card adj P χ u t, h]

/-- **Iter-round count equality.** If two vertices are equal at
iter[k+1] under `χ_v`, then for any (round-k colour, adj-value,
P-value) triple, the counts of intermediate vertices match. -/
private theorem iter_succ_count_eq {n : Nat} (adj : AdjMatrix n) (P : PMatrix n)
    (v : Fin n) (k : Nat) {w u : Fin n}
    (h : ((refineStep adj P)^[k + 1]) (individualizedColouring n {v}) w =
         ((refineStep adj P)^[k + 1]) (individualizedColouring n {v}) u)
    (c : Nat) (a : Nat) (p : POE) :
    (Finset.univ.filter (fun u' : Fin n =>
      u' ≠ w ∧ (c, a, p) = (((refineStep adj P)^[k])
        (individualizedColouring n {v}) u', adj.adj w u', P w u'))).card =
    (Finset.univ.filter (fun u' : Fin n =>
      u' ≠ u ∧ (c, a, p) = (((refineStep adj P)^[k])
        (individualizedColouring n {v}) u', adj.adj u u', P u u'))).card := by
  have hsig := ((iter_succ_eq_iff adj P v k w u).mp h).2
  exact signature_eq_card_eq adj P _ hsig (c, a, p)

/-- **Bridge generalised: `countP` form.** Multiset.countP on a
signature equals Finset.card of the matching preimage filter. -/
private theorem signature_countP_eq_card {n : Nat} (adj : AdjMatrix n) (P : PMatrix n)
    (χ : Colouring n) (w : Fin n) (p : Nat × Nat × POE → Prop) [DecidablePred p] :
    Multiset.countP p (signature adj P χ w) =
    (Finset.univ.filter (fun u' : Fin n =>
      u' ≠ w ∧ p (χ u', adj.adj w u', P w u'))).card := by
  unfold signature
  rw [Multiset.countP_map, ← Finset.filter_val]
  show (Finset.filter (fun u : Fin n => p (χ u, adj.adj w u, P w u))
        (Finset.univ.filter (fun u : Fin n => u ≠ w))).card = _
  rw [Finset.filter_filter]

/-- **Aggregate countP equality from signature equality.** -/
private theorem signature_eq_countP_eq {n : Nat} (adj : AdjMatrix n) (P : PMatrix n)
    (χ : Colouring n) {w u : Fin n}
    (h : signature adj P χ w = signature adj P χ u)
    (p : Nat × Nat × POE → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun u' : Fin n =>
      u' ≠ w ∧ p (χ u', adj.adj w u', P w u'))).card =
    (Finset.univ.filter (fun u' : Fin n =>
      u' ≠ u ∧ p (χ u', adj.adj u u', P u u'))).card := by
  rw [← signature_countP_eq_card adj P χ w p,
      ← signature_countP_eq_card adj P χ u p, h]

/-- **Aggregate iter-round count equality.** Under iter[k+1] equality,
the count of intermediate vertices `u'` whose (iter[k] colour, adj
value, P value) satisfies any decidable predicate `p` matches between
`w` and `u`. The workhorse aggregate version of `iter_succ_count_eq`. -/
private theorem iter_succ_countP_eq {n : Nat} (adj : AdjMatrix n) (P : PMatrix n)
    (v : Fin n) (k : Nat) {w u : Fin n}
    (h : ((refineStep adj P)^[k + 1]) (individualizedColouring n {v}) w =
         ((refineStep adj P)^[k + 1]) (individualizedColouring n {v}) u)
    (p : Nat × Nat × POE → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun u' : Fin n =>
      u' ≠ w ∧ p (((refineStep adj P)^[k])
        (individualizedColouring n {v}) u', adj.adj w u', P w u'))).card =
    (Finset.univ.filter (fun u' : Fin n =>
      u' ≠ u ∧ p (((refineStep adj P)^[k])
        (individualizedColouring n {v}) u', adj.adj u u', P u u'))).card := by
  have hsig := ((iter_succ_eq_iff adj P v k w u).mp h).2
  exact signature_eq_countP_eq adj P _ hsig p

/-- **Aggregate count via colour predicate.** Specialisation of
`iter_succ_countP_eq` for predicates depending only on the round-k
colour (ignoring adj and P values). The Σ-over-all-adj/P collapse:
under iter[k+1] equality, the count of intermediate vertices whose
round-k colour satisfies `q` matches between `w` and `u`. -/
private theorem iter_succ_colour_count_eq {n : Nat} (adj : AdjMatrix n) (P : PMatrix n)
    (v : Fin n) (k : Nat) {w u : Fin n}
    (h : ((refineStep adj P)^[k + 1]) (individualizedColouring n {v}) w =
         ((refineStep adj P)^[k + 1]) (individualizedColouring n {v}) u)
    (q : Nat → Prop) [DecidablePred q] :
    (Finset.univ.filter (fun u' : Fin n =>
      u' ≠ w ∧ q (((refineStep adj P)^[k])
        (individualizedColouring n {v}) u'))).card =
    (Finset.univ.filter (fun u' : Fin n =>
      u' ≠ u ∧ q (((refineStep adj P)^[k])
        (individualizedColouring n {v}) u'))).card := by
  have := iter_succ_countP_eq adj P v k h (fun t => q t.1)
  -- Predicates `(fun u' => q (iter[k] u'))` and `(fun u' => (fun t => q t.1)
  -- (iter[k] u', adj w u', P w u'))` are definitionally equal.
  exact this

/-! ### §8.b.3 — S2.a lifted via iteration helper

The round-1 lemma (S2.a) gives `adj w v = adj u v` from `refineStep
χ_v w = refineStep χ_v u`. By `refineStep_iter_le_eq` (§16.4 of
`ChainDescent.lean`), iter[k+1] equality implies iter[1] equality
(since the partition only refines monotonically). Hence iter[k+1]
equality at any depth `k+1 ≥ 1` already forces `adj w v = adj u v`.

Useful for arguments that hold "after at least one round of
refinement" — including the eventual full Step 2 statement, where
warmRefine equality ≥ iter[1] equality. -/

/-- **S2.a lifted to any depth ≥ 1.** Iter[k+1] equality between two
non-v vertices forces matching adj-to-v. -/
theorem iter_succ_adj_eq {n : Nat} (adj : AdjMatrix n) (P : PMatrix n)
    {v : Fin n} (k : Nat) {w u : Fin n} (hwv : w ≠ v) (huv : u ≠ v)
    (h : ((refineStep adj P)^[k + 1]) (individualizedColouring n {v}) w =
         ((refineStep adj P)^[k + 1]) (individualizedColouring n {v}) u) :
    adj.adj w v = adj.adj u v := by
  -- Convert k+1 to 1+k for `refineStep_iter_le_eq`, then use it with
  -- k_inner = 1, d_inner = k.
  have h' : ((refineStep adj P)^[1 + k]) (individualizedColouring n {v}) w =
            ((refineStep adj P)^[1 + k]) (individualizedColouring n {v}) u := by
    rw [Nat.add_comm]; exact h
  have h1 := refineStep_iter_le_eq adj P (individualizedColouring n {v}) 1 k h'
  rw [Function.iterate_one] at h1
  exact refineStep_round1_adj_eq adj P hwv huv h1

/-- **warmRefine version of S2.a.** Two non-v vertices in the same
warmRefine cell share adjacency to v. -/
theorem warmRefine_adj_eq {n : Nat} (adj : AdjMatrix n) (P : PMatrix n)
    {v : Fin n} {w u : Fin n} (hwv : w ≠ v) (huv : u ≠ v)
    (h : warmRefine adj P (individualizedColouring n {v}) w =
         warmRefine adj P (individualizedColouring n {v}) u) :
    adj.adj w v = adj.adj u v := by
  -- warmRefine = iter[n]; we want iter[1] equality.
  -- Pick k = 0 in iter_succ_adj_eq if n ≥ 1; handle n = 0 vacuously.
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- n = 0: Fin n is empty, no vertices, contradiction.
    exact absurd w.isLt (by omega)
  · -- n ≥ 1: lift via warmRefine_eq_iter_eq at r = 1.
    have h1 := warmRefine_eq_iter_eq adj P (individualizedColouring n {v}) 1 hn h
    rw [Function.iterate_one] at h1
    exact refineStep_round1_adj_eq adj P hwv huv h1

/-- **SchurianSchemeGraph J-class match from warmRefine equality.**
Two non-v vertices in the same warmRefine cell share the J-class
membership of `relOfPair v ·`. Proper Step 2 partial result: this
gives the coarsest non-trivial refinement (J vs not-J), one of the
"layers" that the full Step 2 induction would peel off. -/
theorem SchurianSchemeGraph.warmRefine_J_eq {n : Nat} (G : SchurianSchemeGraph n)
    (P : PMatrix n) {v : Fin n} {w u : Fin n} (hwv : w ≠ v) (huv : u ≠ v)
    (h : warmRefine G.toSchemeGraph.adj P (individualizedColouring n {v}) w =
         warmRefine G.toSchemeGraph.adj P (individualizedColouring n {v}) u) :
    (G.scheme.relOfPair v w ∈ G.J ↔ G.scheme.relOfPair v u ∈ G.J) := by
  have hadj := warmRefine_adj_eq G.toSchemeGraph.adj P hwv huv h
  rw [G.toSchemeGraph.adj_symm w v, G.toSchemeGraph.adj_symm u v] at hadj
  rcases G.toSchemeGraph.adj_eq_zero_or_one v w with hw0 | hw1
  · have hw_notIn : G.scheme.relOfPair v w ∉ G.J :=
      (G.toSchemeGraph.adj_eq_zero_iff v w).mp hw0
    rw [hw0] at hadj
    have hu_notIn : G.scheme.relOfPair v u ∉ G.J :=
      (G.toSchemeGraph.adj_eq_zero_iff v u).mp hadj.symm
    exact ⟨fun h => absurd h hw_notIn, fun h => absurd h hu_notIn⟩
  · have hw_in : G.scheme.relOfPair v w ∈ G.J :=
      (G.toSchemeGraph.adj_eq_one_iff v w).mp hw1
    rw [hw1] at hadj
    have hu_in : G.scheme.relOfPair v u ∈ G.J :=
      (G.toSchemeGraph.adj_eq_one_iff v u).mp hadj.symm
    exact ⟨fun _ => hu_in, fun _ => hw_in⟩

/-! ## §9 — T2.M4 assembly: `SchemeProfile` constructor

Assembles all of T2.1-T2.3's work into the `SchemeProfile`
structure expected by `ChainDescent.lean §18`. Three input
ingredients:

1. A **`SchurianSchemeGraph G`** (scheme + J + adj + schurian
   axioms) — provides Step 1 (algebraic).
2. A **`P`-invariance hypothesis** — every graph-Aut of `G.adj`
   preserves `P`. This bridges `GraphOrbitFixing` (no P) to
   `OrbitPartition adj P {v}` (with P). For "scheme-compatible" P
   (e.g., the trivial all-`unknown` matrix) this holds; for
   arbitrary P it's an additional constraint.
3. A **`Step2_target G P v`** witness — Step 2's substantive
   content. Currently the **only remaining open piece** of
   the Tier 2 program; can be discharged for specific schemes
   (rank ≤ 1) trivially or for general schurian schemes via the
   coherent algebra theorem (S2.b proper, future session).

Output: a `SchemeProfile G.adj P v` that directly populates the
`schurian_scheme_profile_exists` axiom from `ChainDescent.lean §18`. -/

namespace SchurianSchemeGraph

variable {n : Nat} (G : SchurianSchemeGraph n)

/-- **The SchemeProfile constructor.** Given a `SchurianSchemeGraph`,
a P-invariance hypothesis, and a Step 2 witness, produce a concrete
`SchemeProfile` populating the abstract structure from
`ChainDescent.lean §18.1`.

The four fields:
- `profile := vProfile G.scheme v`
- `v_singleton`: from `vProfile_ne_self_of_ne` (T2.2).
- `profile_iff_orbit`: via `vProfile_iff_graphOrbit` (T2.3 Step 1)
  + P-invariance bridge.
- `warm_refines_profile`: from the Step 2 hypothesis. -/
noncomputable def toSchemeProfile (P : PMatrix n) (v : Fin n)
    (hP_invariant : ∀ {π : Equiv.Perm (Fin n)},
      IsAut π G.toSchemeGraph.adj → ∀ x u, P (π x) (π u) = P x u)
    (hStep2 : Step2_target G P v) :
    SchemeProfile G.toSchemeGraph.adj P v where
  profile := vProfile G.scheme v
  v_singleton w hw := G.scheme.vProfile_ne_self_of_ne hw
  profile_iff_orbit w u := by
    -- vProfile equality ↔ GraphOrbitFixing (Step 1) ↔ OrbitPartition (with P-invariance)
    rw [G.vProfile_iff_graphOrbit v w u]
    constructor
    · -- GraphOrbitFixing → OrbitPartition
      rintro ⟨π, hπ, hπv, hπw⟩
      refine ⟨π, hπ, hP_invariant hπ, ?_, hπw⟩
      intro x hx
      rw [Finset.mem_singleton] at hx
      subst hx
      exact hπv
    · -- OrbitPartition → GraphOrbitFixing (drop the P-preservation)
      rintro ⟨π, hπ, _hP, hfix, hπw⟩
      have hπv : π v = v := hfix v (Finset.mem_singleton.mpr rfl)
      exact ⟨π, hπ, hπv, hπw⟩
  warm_refines_profile := hStep2

/-- **Existence: SchemeProfile from SchurianSchemeGraph + P-invariance
+ Step 2.** Packaging `toSchemeProfile` as a `Nonempty` existence
result matches the shape of the `schurian_scheme_profile_exists`
axiom from `ChainDescent.lean §18`. -/
theorem schurian_scheme_profile_exists_of_step2 (P : PMatrix n) (v : Fin n)
    (hP_invariant : ∀ {π : Equiv.Perm (Fin n)},
      IsAut π G.toSchemeGraph.adj → ∀ x u, P (π x) (π u) = P x u)
    (hStep2 : Step2_target G P v) :
    Nonempty (SchemeProfile G.toSchemeGraph.adj P v) :=
  ⟨G.toSchemeProfile P v hP_invariant hStep2⟩

end SchurianSchemeGraph

/-! ### §9.1 — P-invariance discharged for trivial P

When `P` is constant (e.g., the all-`unknown` matrix), every
permutation trivially preserves it, so `hP_invariant` is automatic.
This is the simplest case where the SchemeProfile constructor is
fully unconditional (modulo `Step2_target`). -/

/-- The trivial `PMatrix`: every entry is `POE.unknown`. -/
def trivialPMatrix (n : Nat) : PMatrix n := fun _ _ => POE.unknown

/-- Every permutation preserves the trivial `PMatrix`. -/
theorem trivialPMatrix_invariant {n : Nat} {adj : AdjMatrix n}
    {π : Equiv.Perm (Fin n)} (_ : IsAut π adj) :
    ∀ x u, trivialPMatrix n (π x) (π u) = trivialPMatrix n x u :=
  fun _ _ => rfl

/-- **SchemeProfile for trivial P.** Specialisation of
`toSchemeProfile` requiring only `Step2_target`; the P-invariance
hypothesis is discharged automatically. -/
noncomputable def SchurianSchemeGraph.toSchemeProfile_trivialP {n : Nat}
    (G : SchurianSchemeGraph n) (v : Fin n)
    (hStep2 : Step2_target G (trivialPMatrix n) v) :
    SchemeProfile G.toSchemeGraph.adj (trivialPMatrix n) v :=
  G.toSchemeProfile (trivialPMatrix n) v trivialPMatrix_invariant hStep2

/-! ### §9.2 — Concrete predicate + bridge to `theorem_2_HOR`

`IsSchurianSchemeGraph'` is the concrete analogue of the abstract
axiom `IsSchurianSchemeGraph` from `ChainDescent.lean §18`. A graph
satisfies it iff it arises as the adjacency of some
`SchurianSchemeGraph`.

`theorem_2_HOR_concrete` is the bridge: it produces the
`theorem_2_HOR`-shaped statement (OrbitPartition ↔ warmRefine
equality) from the concrete predicate + P-invariance + Step 2
hypothesis. Once `Step2_target` is discharged unconditionally (the
remaining open Step 2 work), `theorem_2_HOR_concrete` becomes
unconditional for concrete schurian schemes, and the abstract
`schurian_scheme_profile_exists` axiom can be retired (mirroring
the Tier 1 IsCFI → IsCFI' refactor). -/

/-- **Concrete schurian scheme graph predicate.** `adj` is the
adjacency matrix of some `SchurianSchemeGraph`. -/
structure IsSchurianSchemeGraph' {n : Nat} (adj : AdjMatrix n) where
  /-- The underlying schurian scheme graph. -/
  G : SchurianSchemeGraph n
  /-- Its derived adjacency equals `adj`. -/
  matching : G.toSchemeGraph.adj = adj

/-- **Theorem 2 (HOR for schurian scheme graphs), concrete form.**
The `theorem_2_HOR`-shaped statement, derived from the concrete
predicate `IsSchurianSchemeGraph'` plus a P-invariance hypothesis
plus the Step 2 witness.

Becomes unconditional once `Step2_target` is fully discharged. -/
theorem theorem_2_HOR_concrete {n : Nat} {adj : AdjMatrix n}
    (h : IsSchurianSchemeGraph' adj) (P : PMatrix n) (v : Fin n)
    (hP_invariant : ∀ {π : Equiv.Perm (Fin n)}, IsAut π adj →
      ∀ x u, P (π x) (π u) = P x u)
    (hStep2 : Step2_target h.G P v) :
    ∀ w u : Fin n,
      OrbitPartition adj P {v} w u ↔
        warmRefine adj P (individualizedColouring n {v}) w =
          warmRefine adj P (individualizedColouring n {v}) u := by
  -- Convert hP_invariant from `adj` to `h.G.toSchemeGraph.adj` via h.matching.
  have hP' : ∀ {π : Equiv.Perm (Fin n)}, IsAut π h.G.toSchemeGraph.adj →
      ∀ x u, P (π x) (π u) = P x u := by
    intro π hπ
    apply hP_invariant
    rw [← h.matching]
    exact hπ
  -- Build the SchemeProfile.
  have sp := h.G.toSchemeProfile P v hP' hStep2
  -- Apply theorem_2_HOR_of_profile + transport via h.matching.
  intro w u
  rw [← h.matching]
  exact theorem_2_HOR_of_profile sp w u

/-- **Theorem 2 specialised to trivial P (most readable form).**
With the trivial all-`unknown` P matrix, the P-invariance hypothesis
is automatic; the only remaining open piece is `Step2_target`. -/
theorem theorem_2_HOR_concrete_trivialP {n : Nat} {adj : AdjMatrix n}
    (h : IsSchurianSchemeGraph' adj) (v : Fin n)
    (hStep2 : Step2_target h.G (trivialPMatrix n) v) :
    ∀ w u : Fin n,
      OrbitPartition adj (trivialPMatrix n) {v} w u ↔
        warmRefine adj (trivialPMatrix n)
          (individualizedColouring n {v}) w =
          warmRefine adj (trivialPMatrix n)
            (individualizedColouring n {v}) u :=
  theorem_2_HOR_concrete h (trivialPMatrix n) v
    trivialPMatrix_invariant hStep2

/-! ### §9.3 — End-to-end smoke test: trivial 1-vertex scheme

A complete instantiation showing the full theorem_2_HOR_concrete
pipeline works for at least one case. The trivial 1-vertex scheme
has `Fin 1`-many vertices, all in the diagonal relation `R_0`. The
`Step2_target` discharges trivially since `w = u` always (Fin 1
subsingleton); the rest of the pipeline goes through unconditionally.

Validates: `SchurianSchemeGraph` structure → `Step2_target`
discharge → `theorem_2_HOR_concrete` produces an axiom-clean
Theorem 2 instance. -/

/-- The trivial 1-vertex schurian scheme graph. -/
def trivialSchurianSchemeGraph : SchurianSchemeGraph 1 where
  scheme := trivialScheme
  J := ∅
  zero_notMem_J := by simp
  schurian_transitive := by
    intro _ v w v' w' _ _
    refine ⟨Equiv.refl _, IsAut.refl, ?_, ?_⟩
    · exact Fin.ext (by have := v.isLt; have := v'.isLt; omega)
    · exact Fin.ext (by have := w.isLt; have := w'.isLt; omega)
  isAut_imp_isSchemeAut := by
    intro _ _ _ _ _
    rfl

/-- Step 2 holds trivially on the 1-vertex scheme: any two vertices
in `Fin 1` are equal, so `vProfile` equality is automatic. -/
theorem trivialSchurianSchemeGraph_step2 (P : PMatrix 1) (v : Fin 1) :
    Step2_target trivialSchurianSchemeGraph P v := by
  intro w u _
  have hwu : w = u := Fin.ext (by have := w.isLt; have := u.isLt; omega)
  rw [hwu]

/-- **End-to-end unconditional Theorem 2 instance.** For the trivial
1-vertex scheme with trivial P, the `OrbitPartition ↔ warmRefine`
equivalence holds unconditionally (no axioms beyond
`refineStep`/`refineStep_iff` and the standard basis).

This is the **first fully discharged Theorem 2 instance** — no
remaining "open piece" for the trivial case. Validates the
architecture; serves as a template for richer instances (Johnson,
Hamming, etc.) once their `Step2_target` is discharged. -/
theorem theorem_2_HOR_trivial : ∀ w u : Fin 1,
    OrbitPartition trivialSchurianSchemeGraph.toSchemeGraph.adj
        (trivialPMatrix 1) {(0 : Fin 1)} w u ↔
    warmRefine trivialSchurianSchemeGraph.toSchemeGraph.adj
        (trivialPMatrix 1) (individualizedColouring 1 {0}) w =
    warmRefine trivialSchurianSchemeGraph.toSchemeGraph.adj
        (trivialPMatrix 1) (individualizedColouring 1 {0}) u :=
  theorem_2_HOR_concrete_trivialP
    ⟨trivialSchurianSchemeGraph, rfl⟩ 0
    (trivialSchurianSchemeGraph_step2 _ _)

/-! ### §9.4 — Step 2 discharged for `rank ≤ 1` schemes (covers K_n)

A more substantive Step 2 discharge: for schemes with at most 2
relations (R_0 diagonal + R_1 complement), `vProfile` takes only 2
values (0 at v, 1 elsewhere). Step 2 reduces to "warmRefine
separates v from non-v," which holds trivially since χ_v already
does so and warmRefine refines χ_v (split-only).

The K_n schurian scheme graph is exactly this case (with J = {1}).
This gives an unconditional Theorem 2 instance for any concrete
rank-1 schurian scheme graph, modulo construction (not done here). -/

/-- **Step 2 for rank ≤ 1 schurian scheme graphs.** Direct case
analysis: vertices are either `v` (vProfile 0) or not (vProfile 1
when rank = 1; rank = 0 forces n ≤ 1 with only one vertex). -/
theorem step2_of_rank_le_one {n : Nat} (G : SchurianSchemeGraph n)
    (hrank : G.scheme.rank ≤ 1)
    (P : PMatrix n) (v : Fin n) :
    Step2_target G P v := by
  intro w u hwu
  by_cases hwv : w = v
  · by_cases huv : u = v
    · -- both = v: rewrite both to v.
      rw [hwv, huv]
    · -- w = v, u ≠ v: contradiction via iter[0] = χ_v.
      exfalso
      have h0 := warmRefine_eq_iter_eq G.toSchemeGraph.adj P
                    (individualizedColouring n {v}) 0 (Nat.zero_le _) hwu
      rw [hwv] at h0
      exact huv ((individualizedColouring_singleton_eq_v_iff v u).mp h0.symm)
  · by_cases huv : u = v
    · -- w ≠ v, u = v: symmetric contradiction.
      exfalso
      have h0 := warmRefine_eq_iter_eq G.toSchemeGraph.adj P
                    (individualizedColouring n {v}) 0 (Nat.zero_le _) hwu
      rw [huv] at h0
      exact hwv ((individualizedColouring_singleton_eq_v_iff v w).mp h0)
    · -- Both ≠ v: vProfile values both in {1, …, rank} ⊆ {1} (for rank ≤ 1).
      unfold vProfile
      have hw_ne_0 : G.scheme.relOfPair v w ≠ 0 := by
        intro heq
        exact hwv ((G.scheme.relOfPair_eq_zero_iff v w).mp heq).symm
      have hu_ne_0 : G.scheme.relOfPair v u ≠ 0 := by
        intro heq
        exact huv ((G.scheme.relOfPair_eq_zero_iff v u).mp heq).symm
      have hw_lt := (G.scheme.relOfPair v w).isLt
      have hu_lt := (G.scheme.relOfPair v u).isLt
      have hw_pos : (G.scheme.relOfPair v w).val ≠ 0 :=
        fun h => hw_ne_0 (Fin.ext h)
      have hu_pos : (G.scheme.relOfPair v u).val ≠ 0 :=
        fun h => hu_ne_0 (Fin.ext h)
      omega

/-- **Theorem 2 unconditional for rank ≤ 1 schurian scheme graphs.**
Combining `step2_of_rank_le_one` with `theorem_2_HOR_concrete`. -/
theorem theorem_2_HOR_concrete_rank_le_one {n : Nat} {adj : AdjMatrix n}
    (h : IsSchurianSchemeGraph' adj) (hrank : h.G.scheme.rank ≤ 1)
    (P : PMatrix n) (v : Fin n)
    (hP_invariant : ∀ {π : Equiv.Perm (Fin n)}, IsAut π adj →
      ∀ x u, P (π x) (π u) = P x u) :
    ∀ w u : Fin n,
      OrbitPartition adj P {v} w u ↔
        warmRefine adj P (individualizedColouring n {v}) w =
          warmRefine adj P (individualizedColouring n {v}) u :=
  theorem_2_HOR_concrete h P v hP_invariant
    (step2_of_rank_le_one h.G hrank P v)

/-! ## §10 — Depth-parametrised Step 2 framework

`Step2_at_depth G P v k` says iter[k] equality between any two
vertices implies their vProfile equality. This is a depth-explicit
version of `Step2_target` (which uses warmRefine, i.e., iter[n]).

For concrete schemes, the convergence depth is bounded by something
like `rank + 1`. Discharging `Step2_at_depth` at a specific small
depth for a specific scheme then lifts to `Step2_target` via the
`warmRefine_eq_iter_eq` helper.

This framework lets specific schemes (Petersen, Johnson J(m,k), …)
discharge Step 2 at their own characteristic depth without needing
the general convergence-at-rank+1 argument. -/

/-- **Step 2 at fixed depth k.** Iter[k] equality implies vProfile
equality. -/
def Step2_at_depth {n : Nat} (G : SchurianSchemeGraph n) (P : PMatrix n)
    (v : Fin n) (k : Nat) : Prop :=
  ∀ w u : Fin n,
    ((refineStep G.toSchemeGraph.adj P)^[k])
        (individualizedColouring n {v}) w =
      ((refineStep G.toSchemeGraph.adj P)^[k])
        (individualizedColouring n {v}) u →
    vProfile G.scheme v w = vProfile G.scheme v u

/-- **Step2_at_depth lifts to Step2_target.** For any `k ≤ n`,
discharge at depth `k` implies the warmRefine-form. -/
theorem step2_of_step2_at_depth {n : Nat} (G : SchurianSchemeGraph n)
    (P : PMatrix n) (v : Fin n) (k : Nat) (hk : k ≤ n)
    (h : Step2_at_depth G P v k) : Step2_target G P v := by
  intro w u hwu
  apply h
  exact warmRefine_eq_iter_eq G.toSchemeGraph.adj P
          (individualizedColouring n {v}) k hk hwu

/-- **Step2_at_depth at k = 0 for rank ≤ 1 schurian scheme graphs.**
Specialisation of `step2_of_rank_le_one` to the cleaner
`Step2_at_depth` form. -/
private theorem step2_at_depth_zero_of_rank_le_one {n : Nat} (G : SchurianSchemeGraph n)
    (hrank : G.scheme.rank ≤ 1) (P : PMatrix n) (v : Fin n) :
    Step2_at_depth G P v 0 := by
  intro w u h0
  -- h0 : iter[0] χ_v w = iter[0] χ_v u, already unfolded to χ_v w = χ_v u.
  -- Decide whether w = v / u = v via χ_v uniqueness, then conclude vProfile equality.
  by_cases hwv : w = v
  · by_cases huv : u = v
    · rw [hwv, huv]
    · exfalso
      rw [hwv] at h0
      exact huv ((individualizedColouring_singleton_eq_v_iff v u).mp h0.symm)
  · by_cases huv : u = v
    · exfalso
      rw [huv] at h0
      exact hwv ((individualizedColouring_singleton_eq_v_iff v w).mp h0)
    · -- Both ≠ v: rank ≤ 1 forces vProfile = 1 for both.
      unfold vProfile
      have hw_ne_0 : G.scheme.relOfPair v w ≠ 0 := by
        intro heq
        exact hwv ((G.scheme.relOfPair_eq_zero_iff v w).mp heq).symm
      have hu_ne_0 : G.scheme.relOfPair v u ≠ 0 := by
        intro heq
        exact huv ((G.scheme.relOfPair_eq_zero_iff v u).mp heq).symm
      have hw_lt := (G.scheme.relOfPair v w).isLt
      have hu_lt := (G.scheme.relOfPair v u).isLt
      have hw_pos : (G.scheme.relOfPair v w).val ≠ 0 :=
        fun h => hw_ne_0 (Fin.ext h)
      have hu_pos : (G.scheme.relOfPair v u).val ≠ 0 :=
        fun h => hu_ne_0 (Fin.ext h)
      omega

/-! ### §10.1 — Inductive partition Π_k

For schurian scheme graphs of `rank ≥ 2`, Step 2 needs the
inductive intersection-number argument. We define a **recursive
partition predicate** `schemePart_at` capturing what's
distinguishable at depth `k`, and aim to prove
`iter[k] χ_v` refines it.

The partition at depth 0 separates `v` from everyone else (just
the χ_v partition). At each successive depth, we refine by the
multiset of (partition-class, adj, P) triples over neighbours —
mimicking what `refineStep` computes.

**Open inductive step:** prove
`iter[k+1] χ_v w = iter[k+1] χ_v u → schemePart_at (k+1) w u`,
using `iter_succ_eq_iff` + `signature_eq_countP_eq` +
`intersectionCount_via_w`.

**Open convergence claim:** for schurian schemes, at some
`k ≤ rank + 1`, `schemePart_at k` coincides with the vProfile
partition. This is the "coherent algebra rank = scheme rank"
content; classical but non-trivial. -/

/-- **Bridge lemma.** For a `Fintype` and any decidable predicate `p`,
`Set.ncard {x | p x} = (Finset.univ.filter p).card`. The classical
choice in `Set.ncard` is invisible because we have a `DecidablePred`,
and the set-builder collapses to `Finset.univ.filter`. -/
theorem ncard_setOf_eq_filter_card {n : Nat} (p : Fin n → Prop)
    [DecidablePred p] :
    {x : Fin n | p x}.ncard = (Finset.univ.filter p).card := by
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_setOf]

/-- Recursive partition predicate at depth `k`. Two vertices are
indistinguishable up to depth `k` iff:
- k = 0: they share their χ_v colour (i.e., either both = v or
  both ≠ v).
- k = k'+1: indistinguishable at depth `k'`, AND for every adj
  value `a`, every P value `p`, and every depth-`k'` class
  representative `w'`, the count of `u'` in the same `Π_k'`-class
  as `w'` with `adj w u' = a` and `P w u' = p` matches between
  `w` and `u`.

Uses `Set.ncard` rather than `(Finset.univ.filter ...).card` to
sidestep `Decidable` instance bridging issues — `Set.ncard` is
`Nat.card`-backed (classical), so set-builder equalities are
propositional and congruence-friendly. -/
def schemePart_at {n : Nat} (G : SchurianSchemeGraph n) (P : PMatrix n)
    (v : Fin n) : Nat → Fin n → Fin n → Prop
  | 0, w, u => individualizedColouring n {v} w = individualizedColouring n {v} u
  | k + 1, w, u =>
    schemePart_at G P v k w u ∧
    -- For each (a, p, w'), counts match between the w-perspective and the u-perspective.
    ∀ (a : Nat) (p : POE) (w' : Fin n),
      {u' : Fin n | u' ≠ w ∧ schemePart_at G P v k u' w' ∧
                    G.toSchemeGraph.adj.adj w u' = a ∧ P w u' = p}.ncard =
      {u' : Fin n | u' ≠ u ∧ schemePart_at G P v k u' w' ∧
                    G.toSchemeGraph.adj.adj u u' = a ∧ P u u' = p}.ncard

/-! ### §10.2 — `schemePart_at` is an equivalence relation

Reflexivity, symmetry, transitivity by straightforward induction
on `k`. Needed to argue that `iter[k] χ_v` (also an equivalence)
refines `schemePart_at k`. -/

/-- `schemePart_at` is reflexive. -/
private theorem schemePart_at_refl {n : Nat} (G : SchurianSchemeGraph n) (P : PMatrix n)
    (v : Fin n) (k : Nat) (w : Fin n) : schemePart_at G P v k w w := by
  induction k with
  | zero => exact rfl
  | succ k ih =>
    refine ⟨ih, ?_⟩
    intro _ _ _
    rfl

/-- `schemePart_at` is symmetric. -/
private theorem schemePart_at_symm {n : Nat} (G : SchurianSchemeGraph n) (P : PMatrix n)
    (v : Fin n) (k : Nat) {w u : Fin n}
    (h : schemePart_at G P v k w u) : schemePart_at G P v k u w := by
  induction k generalizing w u with
  | zero => exact h.symm
  | succ k ih =>
    obtain ⟨hk, hc⟩ := h
    refine ⟨ih hk, ?_⟩
    intro a p w'
    exact (hc a p w').symm

/-- `schemePart_at` is transitive. -/
private theorem schemePart_at_trans {n : Nat} (G : SchurianSchemeGraph n) (P : PMatrix n)
    (v : Fin n) (k : Nat) {w u t : Fin n}
    (h1 : schemePart_at G P v k w u) (h2 : schemePart_at G P v k u t) :
    schemePart_at G P v k w t := by
  induction k generalizing w u t with
  | zero => exact h1.trans h2
  | succ k ih =>
    obtain ⟨hk1, hc1⟩ := h1
    obtain ⟨hk2, hc2⟩ := h2
    refine ⟨ih hk1 hk2, ?_⟩
    intro a p w'
    exact (hc1 a p w').trans (hc2 a p w')

/-! ### §10.3 — `iter[k] χ_v` refines `schemePart_at G P v k`

The substantive inductive step. Combines:
- Base case: iter[0] = χ_v, matches `schemePart_at 0` by definition.
- Inductive step: from iter[k+1] equality, get (a) iter[k] equality
  (gives `schemePart_at k` by ih), (b) signature equality at iter[k]
  (gives the count condition via `signature_eq_countP_eq` plus the
  ih-derived equivalence "schemePart_at k u' w' ↔ ∃ x with iter[k]
  x = iter[k] u' and schemePart_at k x w'").

After this lemma, the only remaining piece for full Step 2 is the
**convergence claim**: for schurian schemes, at some bounded `k ≤
rank + 1`, `schemePart_at G P v k w u ↔ vProfile w = vProfile u`.
That last piece is the coherent-algebra-style argument; classical
but still open in this development. -/

/-- **Inductive refinement.** `iter[k] χ_v` partition refines
`schemePart_at G P v k`. -/
theorem iter_refines_schemePart_at {n : Nat} (G : SchurianSchemeGraph n)
    (P : PMatrix n) (v : Fin n) :
    ∀ (k : Nat) (w u : Fin n),
      ((refineStep G.toSchemeGraph.adj P)^[k])
          (individualizedColouring n {v}) w =
        ((refineStep G.toSchemeGraph.adj P)^[k])
          (individualizedColouring n {v}) u →
      schemePart_at G P v k w u := by
  intro k
  induction k with
  | zero =>
    intro w u h
    -- iter[0] = χ_v; schemePart_at 0 w u is just χ_v w = χ_v u (already).
    exact h
  | succ k ih =>
    intro w u h
    obtain ⟨hk, hsig⟩ :=
      (iter_succ_eq_iff G.toSchemeGraph.adj P v k w u).mp h
    refine ⟨ih w u hk, ?_⟩
    intro a p w'
    -- The key equivalence: schemePart_at k u' w' ↔ ∃ x, iter[k] x = iter[k] u' ∧ schemePart_at k x w'.
    set χk := ((refineStep G.toSchemeGraph.adj P)^[k])
                (individualizedColouring n {v}) with hχk_def
    have hequiv : ∀ u', schemePart_at G P v k u' w' ↔
                  ∃ x : Fin n, χk x = χk u' ∧ schemePart_at G P v k x w' := by
      intro u'
      refine ⟨fun h_sp => ⟨u', rfl, h_sp⟩, ?_⟩
      rintro ⟨x, hx_eq, hx_sp⟩
      have hux : schemePart_at G P v k u' x := ih u' x hx_eq.symm
      exact schemePart_at_trans G P v k hux hx_sp
    -- The iter-k-encoded predicate.
    let p_pred : Nat × Nat × POE → Prop := fun t =>
      (∃ x : Fin n, χk x = t.1 ∧ schemePart_at G P v k x w') ∧
      t.2.1 = a ∧ t.2.2 = p
    haveI : DecidablePred p_pred := Classical.decPred _
    -- Apply signature_eq_countP_eq with p_pred.
    have hcount := signature_eq_countP_eq G.toSchemeGraph.adj P χk hsig p_pred
    -- Rewrite both filters to expose the schemePart_at form.
    haveI : DecidablePred (fun u' : Fin n =>
        u' ≠ w ∧ schemePart_at G P v k u' w' ∧
        G.toSchemeGraph.adj.adj w u' = a ∧ P w u' = p) := Classical.decPred _
    haveI : DecidablePred (fun u' : Fin n =>
        u' ≠ u ∧ schemePart_at G P v k u' w' ∧
        G.toSchemeGraph.adj.adj u u' = a ∧ P u u' = p) := Classical.decPred _
    -- Filter equalities: p_pred-form ↔ schemePart_at-form (via hequiv).
    have h_w_filter : (Finset.univ.filter (fun u' : Fin n =>
              u' ≠ w ∧ p_pred (χk u', G.toSchemeGraph.adj.adj w u', P w u'))) =
          (Finset.univ.filter (fun u' : Fin n =>
              u' ≠ w ∧ schemePart_at G P v k u' w' ∧
              G.toSchemeGraph.adj.adj w u' = a ∧ P w u' = p)) := by
      apply Finset.filter_congr
      intro u' _
      constructor
      · rintro ⟨hne, ⟨hex, ha, hp⟩⟩
        exact ⟨hne, (hequiv u').mpr hex, ha, hp⟩
      · rintro ⟨hne, hsp, ha, hp⟩
        exact ⟨hne, (hequiv u').mp hsp, ha, hp⟩
    have h_u_filter : (Finset.univ.filter (fun u' : Fin n =>
              u' ≠ u ∧ p_pred (χk u', G.toSchemeGraph.adj.adj u u', P u u'))) =
          (Finset.univ.filter (fun u' : Fin n =>
              u' ≠ u ∧ schemePart_at G P v k u' w' ∧
              G.toSchemeGraph.adj.adj u u' = a ∧ P u u' = p)) := by
      apply Finset.filter_congr
      intro u' _
      constructor
      · rintro ⟨hne, ⟨hex, ha, hp⟩⟩
        exact ⟨hne, (hequiv u').mpr hex, ha, hp⟩
      · rintro ⟨hne, hsp, ha, hp⟩
        exact ⟨hne, (hequiv u').mp hsp, ha, hp⟩
    -- Chain: schemePart-w-ncard = schemePart-w-card = p_pred-w-card = p_pred-u-card
    --        = schemePart-u-card = schemePart-u-ncard. The Set.ncard ↔ Finset.card
    -- bridge uses `ncard_setOf_eq_filter_card` (below) under the local DecidablePred.
    have h_w_ncard : {u' : Fin n | u' ≠ w ∧ schemePart_at G P v k u' w' ∧
                      G.toSchemeGraph.adj.adj w u' = a ∧ P w u' = p}.ncard =
                    (Finset.univ.filter (fun u' : Fin n =>
                      u' ≠ w ∧ schemePart_at G P v k u' w' ∧
                      G.toSchemeGraph.adj.adj w u' = a ∧ P w u' = p)).card :=
      ncard_setOf_eq_filter_card _
    have h_u_ncard : {u' : Fin n | u' ≠ u ∧ schemePart_at G P v k u' w' ∧
                      G.toSchemeGraph.adj.adj u u' = a ∧ P u u' = p}.ncard =
                    (Finset.univ.filter (fun u' : Fin n =>
                      u' ≠ u ∧ schemePart_at G P v k u' w' ∧
                      G.toSchemeGraph.adj.adj u u' = a ∧ P u u' = p)).card :=
      ncard_setOf_eq_filter_card _
    rw [h_w_ncard, h_u_ncard, ← h_w_filter, ← h_u_filter]
    exact hcount

/-! ### §10.4 — Convergence assembly

With `iter_refines_schemePart_at` (the substantive inductive step
done) and `warmRefine_eq_iter_eq` (the iter-to-warmRefine lift), the
full Step 2 reduces to **one remaining content piece**: showing that
at some bounded depth `k ≤ n`, `schemePart_at` coincides with
`vProfile`.

For schurian schemes, classical coherent algebra theory gives this
at `k = rank + 1` — the intersection-number matrix has full column
rank for the relation indices, so the "schemePart_at" partition
uniquely identifies each `vProfile` class.

We package this remaining piece as `Step2_converges_at` and the
assembly `step2_of_converges_at` that lifts it to `Step2_target`. -/

/-- **Step 2 convergence at depth `k`.** schemePart_at-k equivalence
implies vProfile equality. This is the **single remaining open
content piece** for full Step 2 (modulo the inductive step
`iter_refines_schemePart_at` which is already proved). -/
def Step2_converges_at {n : Nat} (G : SchurianSchemeGraph n) (P : PMatrix n)
    (v : Fin n) (k : Nat) : Prop :=
  ∀ w u : Fin n, schemePart_at G P v k w u →
    vProfile G.scheme v w = vProfile G.scheme v u

/-- **Step 2 from convergence + the inductive step.** Given
`Step2_converges_at G P v k` for some `k ≤ n`, the full
`Step2_target` holds. -/
theorem step2_of_converges_at {n : Nat} (G : SchurianSchemeGraph n)
    (P : PMatrix n) (v : Fin n) (k : Nat) (hk : k ≤ n)
    (hconv : Step2_converges_at G P v k) :
    Step2_target G P v := by
  intro w u hwu
  apply hconv
  apply iter_refines_schemePart_at
  exact warmRefine_eq_iter_eq G.toSchemeGraph.adj P
    (individualizedColouring n {v}) k hk hwu

/-- **Step2_converges_at at depth 0 for rank ≤ 1 schemes.** A
sanity check: the convergence framework recovers the rank-≤-1 case
already proved directly. At depth 0, schemePart_at reduces to
χ_v-equality. -/
private theorem step2_converges_at_zero_of_rank_le_one {n : Nat}
    (G : SchurianSchemeGraph n) (hrank : G.scheme.rank ≤ 1)
    (P : PMatrix n) (v : Fin n) :
    Step2_converges_at G P v 0 := by
  intro w u h
  -- schemePart_at G P v 0 w u is, by def, χ_v w = χ_v u.
  -- This matches step2_at_depth_zero_of_rank_le_one's body.
  exact step2_at_depth_zero_of_rank_le_one G hrank P v w u h

/-! ### §10.5 — Depth-1 extraction: `adj` and `P` to `v`

The previously-blocked lemma: extract `adj w v = adj u v` and
`P w v = P u v` from `schemePart_at G P v 1 w u` via the depth-1
count condition at `w' = v`. Argument:
- LHS-set = `{v}` (the only `u' ≠ w` with `χ_v u' = χ_v v` is `v`,
  via `individualizedColouring_singleton_eq_v_iff`).
- |LHS-set| = 1; by the count condition, |RHS-set| = 1.
- RHS-set ⊆ {v} by the same `χ_v` uniqueness; so RHS-set = {v}.
- `v ∈ RHS-set` yields `adj u v = adj w v ∧ P u v = P w v`.

This was blocked under the old `Finset.filter`-based `schemePart_at`
by a `Decidable` instance unification issue; the `Set.ncard`
restructure (§10.1) makes the argument go through cleanly because
`Set.ncard` doesn't carry a Decidable instance to align. -/

/-- **Depth-1 extraction.** For `w, u ≠ v`, `schemePart_at G P v 1 w u`
forces `adj w v = adj u v` and `P w v = P u v`. -/
theorem schemePart_at_one_to_v {n : Nat} (G : SchurianSchemeGraph n) (P : PMatrix n)
    (v w u : Fin n) (hwv : w ≠ v) (huv : u ≠ v)
    (h : schemePart_at G P v 1 w u) :
    G.toSchemeGraph.adj.adj w v = G.toSchemeGraph.adj.adj u v ∧
    P w v = P u v := by
  obtain ⟨_, hcount⟩ := h
  -- Specialize: (a, p, w') = (adj w v, P w v, v).
  have hkey := hcount (G.toSchemeGraph.adj.adj w v) (P w v) v
  -- Both sets collapse to a singleton-or-empty form via χ_v uniqueness.
  have hLHS : {u' : Fin n |
                u' ≠ w ∧ schemePart_at G P v 0 u' v ∧
                G.toSchemeGraph.adj.adj w u' = G.toSchemeGraph.adj.adj w v ∧
                P w u' = P w v} = {v} := by
    ext u'
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    refine ⟨?_, ?_⟩
    · rintro ⟨_, h_sp0, _, _⟩
      exact (individualizedColouring_singleton_eq_v_iff v u').mp h_sp0
    · rintro rfl
      exact ⟨hwv.symm, rfl, rfl, rfl⟩
  -- RHS-set: same shape, with u in place of w.
  -- First: every member equals v (χ_v uniqueness).
  have hRHS_sub : {u' : Fin n |
                u' ≠ u ∧ schemePart_at G P v 0 u' v ∧
                G.toSchemeGraph.adj.adj u u' = G.toSchemeGraph.adj.adj w v ∧
                P u u' = P w v} ⊆ {v} := by
    intro u' h_mem
    obtain ⟨_, h_sp0, _, _⟩ := h_mem
    exact (individualizedColouring_singleton_eq_v_iff v u').mp h_sp0
  -- The count condition: lhs.ncard = rhs.ncard, both equal 1 (lhs = {v}).
  rw [hLHS] at hkey
  have hcard_v : ({v} : Set (Fin n)).ncard = 1 := Set.ncard_singleton v
  rw [hcard_v] at hkey
  -- So |RHS| = 1 and RHS ⊆ {v}; hence RHS = {v}.
  have hRHS_eq : {u' : Fin n |
                u' ≠ u ∧ schemePart_at G P v 0 u' v ∧
                G.toSchemeGraph.adj.adj u u' = G.toSchemeGraph.adj.adj w v ∧
                P u u' = P w v} = {v} :=
    Set.eq_of_subset_of_ncard_le hRHS_sub
      (by rw [hcard_v]; exact hkey.le) (Set.finite_singleton v)
  -- v belongs to the RHS-set, so adj u v = adj w v and P u v = P w v.
  have hv_mem : v ∈ {u' : Fin n |
                u' ≠ u ∧ schemePart_at G P v 0 u' v ∧
                G.toSchemeGraph.adj.adj u u' = G.toSchemeGraph.adj.adj w v ∧
                P u u' = P w v} := by
    rw [hRHS_eq]
    rfl
  obtain ⟨_, _, hadj, hP⟩ := hv_mem
  exact ⟨hadj.symm, hP.symm⟩

/-- **Depth-1 extraction, adj-only specialization.** -/
private theorem schemePart_at_one_adj_to_v {n : Nat} (G : SchurianSchemeGraph n) (P : PMatrix n)
    (v w u : Fin n) (hwv : w ≠ v) (huv : u ≠ v)
    (h : schemePart_at G P v 1 w u) :
    G.toSchemeGraph.adj.adj w v = G.toSchemeGraph.adj.adj u v :=
  (schemePart_at_one_to_v G P v w u hwv huv h).1

/-! ### §10.6 — Convergence at depth 1

With the depth-1 extraction in hand, convergence reduces to a
scheme-side **depth-1 separation hypothesis**: that `(adj v ·, P v ·)`
determines `relOfPair v ·` on non-`v` vertices.

This hypothesis is **automatic** for two important classes:
- `rank ≤ 1` schemes (only one non-diagonal relation, so adj-to-v
  classifies completely); subsumes the existing
  `step2_converges_at_zero_of_rank_le_one`.
- Rank-2 schemes with `J = {1}` (e.g., Johnson `J(5,2)` = Petersen,
  Kneser graphs): adj-to-v separates the two non-diagonal relations.

The hypothesis is **not** automatic for higher-rank schemes (e.g.,
Hamming `H(2, 3)`, Johnson `J(m, k)` for `k ≥ 3`), where multiple
non-diagonal relations share J-class membership and adj-to-v alone
cannot distinguish them. Those require deeper convergence (depth 2+
via intersection-number reasoning), which is left to future work as
a per-scheme strengthening. -/

/-- **Depth-1 separation hypothesis.** `(adj v ·, P v ·)` determines
`relOfPair v ·` on non-`v` vertices: any two non-`v` vertices with
matching adj/P to `v` lie in the same scheme relation with `v`. -/
def RelOfPairDetByAdjP {n : Nat} (G : SchurianSchemeGraph n) (P : PMatrix n)
    (v : Fin n) : Prop :=
  ∀ w u : Fin n, w ≠ v → u ≠ v →
    G.toSchemeGraph.adj.adj w v = G.toSchemeGraph.adj.adj u v →
    P w v = P u v →
    G.scheme.relOfPair v w = G.scheme.relOfPair v u

/-- **Step 2 convergence at depth 1 under depth-1 separation.** When
`RelOfPairDetByAdjP G P v` holds, the depth-1 extraction
(`schemePart_at_one_to_v`) immediately yields vProfile equality. -/
theorem step2_converges_at_one_of_det {n : Nat}
    (G : SchurianSchemeGraph n) (P : PMatrix n) (v : Fin n)
    (hdet : RelOfPairDetByAdjP G P v) :
    Step2_converges_at G P v 1 := by
  intro w u h
  -- Reduce to relOfPair equality (vProfile is its .val).
  suffices h_rel : G.scheme.relOfPair v w = G.scheme.relOfPair v u by
    unfold vProfile; rw [h_rel]
  by_cases hwv : w = v
  · -- w = v: by schemePart_at-0, also u = v.
    obtain ⟨h0, _⟩ := h
    rw [hwv] at h0
    have hu : u = v :=
      (individualizedColouring_singleton_eq_v_iff v u).mp h0.symm
    rw [hwv, hu]
  · by_cases huv : u = v
    · -- u = v: symmetric.
      obtain ⟨h0, _⟩ := h
      rw [huv] at h0
      have hw : w = v :=
        (individualizedColouring_singleton_eq_v_iff v w).mp h0
      rw [huv, hw]
    · -- Both ≠ v: depth-1 extraction + hdet.
      obtain ⟨hadj, hP⟩ := schemePart_at_one_to_v G P v w u hwv huv h
      exact hdet w u hwv huv hadj hP

/-- **`rank ≤ 1` implies depth-1 separation.** When the scheme has
only one non-diagonal relation, adj-to-v trivially determines
relOfPair v · (both non-v vertices land in the same unique
non-diagonal relation). -/
private theorem relOfPairDetByAdjP_of_rank_le_one {n : Nat}
    (G : SchurianSchemeGraph n) (hrank : G.scheme.rank ≤ 1)
    (P : PMatrix n) (v : Fin n) :
    RelOfPairDetByAdjP G P v := by
  intro w u hwv huv _ _
  -- Both relOfPair v · values are non-zero (since w, u ≠ v) and < rank + 1 ≤ 2.
  -- Hence both = 1, forcing equality.
  have hw_ne_0 : G.scheme.relOfPair v w ≠ 0 := by
    intro heq
    exact hwv ((G.scheme.relOfPair_eq_zero_iff v w).mp heq).symm
  have hu_ne_0 : G.scheme.relOfPair v u ≠ 0 := by
    intro heq
    exact huv ((G.scheme.relOfPair_eq_zero_iff v u).mp heq).symm
  have hw_lt := (G.scheme.relOfPair v w).isLt
  have hu_lt := (G.scheme.relOfPair v u).isLt
  apply Fin.ext
  have hw_pos : (G.scheme.relOfPair v w).val ≠ 0 :=
    fun h => hw_ne_0 (Fin.ext h)
  have hu_pos : (G.scheme.relOfPair v u).val ≠ 0 :=
    fun h => hu_ne_0 (Fin.ext h)
  omega

/-! ### §10.7 — End-to-end Theorem 2 via depth-1 convergence

Compose `step2_converges_at_one_of_det` with `step2_of_converges_at`
to get `Step2_target`, then plug into `theorem_2_HOR_concrete`. -/

/-- **Step 2 from depth-1 separation.** For any schurian scheme graph
on `n ≥ 1` vertices satisfying `RelOfPairDetByAdjP`,
`Step2_target G P v` holds — unconditionally. -/
theorem step2_of_det {n : Nat} (G : SchurianSchemeGraph n)
    (P : PMatrix n) (v : Fin n)
    (hdet : RelOfPairDetByAdjP G P v) :
    Step2_target G P v :=
  step2_of_converges_at G P v 1 (Nat.one_le_iff_ne_zero.mpr (by
    intro h
    rw [h] at v
    exact (Fin.elim0 v))) (step2_converges_at_one_of_det G P v hdet)

/-- **Theorem 2 unconditional under depth-1 separation.** -/
theorem theorem_2_HOR_concrete_of_det {n : Nat} {adj : AdjMatrix n}
    (h : IsSchurianSchemeGraph' adj) (P : PMatrix n) (v : Fin n)
    (hP_invariant : ∀ {π : Equiv.Perm (Fin n)}, IsAut π adj →
      ∀ x u, P (π x) (π u) = P x u)
    (hdet : RelOfPairDetByAdjP h.G P v) :
    ∀ w u : Fin n,
      OrbitPartition adj P {v} w u ↔
        warmRefine adj P (individualizedColouring n {v}) w =
          warmRefine adj P (individualizedColouring n {v}) u :=
  theorem_2_HOR_concrete h P v hP_invariant (step2_of_det h.G P v hdet)

/-! ### §10.8 — Adj-separation predicate and the rank-≤-2 case

A cleaner reformulation: depth-1 separation follows from
`(· ∈ J)` being injective on non-diagonal relations. This holds
**iff** `rank ≤ 2` (the function has codomain `Bool`, so injectivity
on a domain of size `> 2` is impossible). For `rank ≤ 2` we get:

- `rank ≤ 1`: automatic (≤ 1 non-diagonal relation; trivially
  injective). Already proved as
  `relOfPairDetByAdjP_of_rank_le_one`.
- `rank = 2` with `|J| = 1`: J splits the two non-diagonal
  relations cleanly; injective. **Proved here.**
- `rank = 2` with `|J| = 0` or `|J| = 2`: both non-diagonal
  relations have the same J-membership; **not** injective —
  depth-1 separation fails and a deeper convergence argument is
  needed.

For Petersen (= Kneser `K(5,2)` = `J(5,2)`), `rank = 2` and `|J| = 1`
(`J = {1}` for the "share 1 element" relation), so the rank-2 case
applies. -/

/-- **Adj-separation:** `(· ∈ J)` restricted to non-diagonal
relations is injective. Equivalent to depth-1 separation. -/
def AdjSeparatesRelations {n : Nat} (G : SchemeGraph n) : Prop :=
  ∀ i j : Fin (G.scheme.rank + 1), i ≠ 0 → j ≠ 0 →
    ((i ∈ G.J) ↔ (j ∈ G.J)) → i = j

/-- **`AdjSeparatesRelations` implies depth-1 separation.** -/
theorem relOfPairDetByAdjP_of_adjSeparates {n : Nat}
    (G : SchurianSchemeGraph n) (hsep : AdjSeparatesRelations G.toSchemeGraph)
    (P : PMatrix n) (v : Fin n) :
    RelOfPairDetByAdjP G P v := by
  intro w u hwv huv hadj _hP
  -- Both relOfPair v · are non-zero (since w, u ≠ v).
  have hw_ne : G.scheme.relOfPair v w ≠ 0 :=
    fun heq => hwv ((G.scheme.relOfPair_eq_zero_iff v w).mp heq).symm
  have hu_ne : G.scheme.relOfPair v u ≠ 0 :=
    fun heq => huv ((G.scheme.relOfPair_eq_zero_iff v u).mp heq).symm
  -- (relOfPair v w ∈ J) ↔ (relOfPair v u ∈ J), from adj equality + symmetry.
  have hiff : (G.scheme.relOfPair v w ∈ G.toSchemeGraph.J) ↔
              (G.scheme.relOfPair v u ∈ G.toSchemeGraph.J) := by
    rw [← G.toSchemeGraph.adj_eq_one_iff, ← G.toSchemeGraph.adj_eq_one_iff,
        G.toSchemeGraph.adj_symm v w, G.toSchemeGraph.adj_symm v u, hadj]
  exact hsep _ _ hw_ne hu_ne hiff

/-- **`rank ≤ 1` implies adj-separation.** Automatic since
the non-diagonal index set has size ≤ 1. -/
private theorem adjSeparates_of_rank_le_one {n : Nat}
    (G : SchemeGraph n) (hrank : G.scheme.rank ≤ 1) :
    AdjSeparatesRelations G := by
  intro i j hi_ne hj_ne _
  apply Fin.ext
  have hi_lt := i.isLt
  have hj_lt := j.isLt
  have hi_pos : i.val ≠ 0 := fun h => hi_ne (Fin.ext h)
  have hj_pos : j.val ≠ 0 := fun h => hj_ne (Fin.ext h)
  omega

/-- **`rank = 2` + `|J| = 1` implies adj-separation.** The unique
element of J distinguishes the two non-diagonal relations. -/
theorem adjSeparates_of_rank_two_J_singleton {n : Nat}
    (G : SchemeGraph n) (hrank : G.scheme.rank = 2)
    (hJ : G.J.card = 1) :
    AdjSeparatesRelations G := by
  intro i j hi_ne hj_ne hiff
  obtain ⟨j_0, hJ_eq⟩ := Finset.card_eq_one.mp hJ
  -- Both i, j ∈ {1, 2}; the J-membership iff says (i = j_0) ↔ (j = j_0).
  have hi_lt := i.isLt
  have hj_lt := j.isLt
  have hi_pos : i.val ≠ 0 := fun h => hi_ne (Fin.ext h)
  have hj_pos : j.val ≠ 0 := fun h => hj_ne (Fin.ext h)
  -- i and j are each either j_0 or the other rank-2 element.
  -- (i ∈ J) ↔ i = j_0; same for j. So hiff is (i = j_0) ↔ (j = j_0).
  have hi_iff : (i ∈ G.J) ↔ i = j_0 := by
    rw [hJ_eq]; exact Finset.mem_singleton
  have hj_iff : (j ∈ G.J) ↔ j = j_0 := by
    rw [hJ_eq]; exact Finset.mem_singleton
  by_cases hi_j0 : i = j_0
  · -- i = j_0; by hiff, j = j_0; so i = j.
    have : j = j_0 := hj_iff.mp ((hiff.mp (hi_iff.mpr hi_j0)))
    rw [hi_j0, this]
  · -- i ≠ j_0; by hiff contrapositive, j ≠ j_0; both are the "other" element.
    have hj_nj0 : j ≠ j_0 :=
      fun heq => hi_j0 (hi_iff.mp (hiff.mpr (hj_iff.mpr heq)))
    -- For rank = 2 with i, j ∈ {1, 2} and both ≠ j_0:
    -- they must be the unique element of {1, 2} \ {j_0}, hence equal.
    apply Fin.ext
    -- j_0 ∈ {1, 2}; let j_0.val ∈ {1, 2}.
    have hj0_lt := j_0.isLt
    have hj0_mem : j_0 ∈ G.J := by
      rw [hJ_eq]; exact Finset.mem_singleton_self _
    have hj0_ne_zero : j_0.val ≠ 0 := by
      intro h
      have : j_0 = 0 := Fin.ext h
      rw [this] at hj0_mem
      exact G.zero_notMem_J hj0_mem
    have hi_ne_j0_val : i.val ≠ j_0.val :=
      fun heq => hi_j0 (Fin.ext heq)
    have hj_ne_j0_val : j.val ≠ j_0.val :=
      fun heq => hj_nj0 (Fin.ext heq)
    -- All of i.val, j.val, j_0.val ∈ {1, 2}. j_0.val ∈ {1, 2} and i.val ≠ j_0.val,
    -- and i.val ∈ {1, 2}, so i.val is the other element. Same for j.val. omega.
    omega

/-- **Combined: `rank = 2` + `|J| = 1` ⇒ depth-1 separation.** -/
theorem relOfPairDetByAdjP_of_rank_two_J_singleton {n : Nat}
    (G : SchurianSchemeGraph n) (hrank : G.scheme.rank = 2)
    (hJ : G.toSchemeGraph.J.card = 1)
    (P : PMatrix n) (v : Fin n) :
    RelOfPairDetByAdjP G P v :=
  relOfPairDetByAdjP_of_adjSeparates G
    (adjSeparates_of_rank_two_J_singleton G.toSchemeGraph hrank hJ) P v

/-- **Theorem 2 unconditional for `rank = 2` + `|J| = 1` schurian
scheme graphs.** Covers Petersen (= Kneser `K(5,2)` = `J(5,2)`) and
other "single-edge-relation" rank-2 schemes. -/
theorem theorem_2_HOR_concrete_rank_two_J_singleton {n : Nat} {adj : AdjMatrix n}
    (h : IsSchurianSchemeGraph' adj) (hrank : h.G.scheme.rank = 2)
    (hJ : h.G.toSchemeGraph.J.card = 1)
    (P : PMatrix n) (v : Fin n)
    (hP_invariant : ∀ {π : Equiv.Perm (Fin n)}, IsAut π adj →
      ∀ x u, P (π x) (π u) = P x u) :
    ∀ w u : Fin n,
      OrbitPartition adj P {v} w u ↔
        warmRefine adj P (individualizedColouring n {v}) w =
          warmRefine adj P (individualizedColouring n {v}) u :=
  theorem_2_HOR_concrete_of_det h P v hP_invariant
    (relOfPairDetByAdjP_of_rank_two_J_singleton h.G hrank hJ P v)

/-! ### §10.9 — Depth-2 convergence layer

The depth-1 path (§10.5–§10.8) converges only when `(adj v ·, P v ·)`
already determines `relOfPair v ·` — i.e. `rank ≤ 2` with a single
edge-relation. For higher-rank schurian schemes (Johnson `J(m, k)`,
`k ≥ 3`; Hamming `H(d, q)`, `d ≥ 3`; rank-≥-3 distance-regular graphs)
the single 0/1 adjacency-to-`v` value cannot separate the ≥ 3
non-diagonal relations, and `schemePart_at 1` is strictly coarser than
`vProfile` — it merges relations that share an adjacency-to-`v` value.

One further refinement round separates them: counting, for each
depth-1 block and each adjacency value, how many block-members each
vertex is adjacent to (the **block-degree vector**). This is the
intersection-number refinement of coherent-algebra theory, realised
here as `schemePart_at 2`.

This section builds the **abstract depth-2 layer**, mirroring §10.5–§10.8
one level up. The separation predicate `Depth2Det` is phrased over the
depth-2 extractables (adj/P-to-`v`, proved by `schemePart_at_one_to_v`,
plus the depth-1 block-degree counts, which are *definitionally* the
second component of `schemePart_at 2`). Discharging `Depth2Det` for a
concrete higher-rank scheme — the intersection-number argument — is the
remaining open content (the analogue of `adjSeparates_of_rank_two_J_singleton`
one level up). Full generality (convergence at `k = rank + 1`, the
coherent-algebra matrix-rank theorem) stays open. -/

/-- **Depth-2 separation hypothesis.** The depth-2 invariant of a non-`v`
vertex — its adjacency/`P` value to `v`, together with its block-degree
vector (for each depth-1 class `w'` and each `(a, p)`, the number of
depth-1-`w'`-class members it is `(a, p)`-adjacent to) — determines
`relOfPair v ·`. Weaker (easier to satisfy) than `RelOfPairDetByAdjP`:
it may use the block-degree counts, not just adj/`P`-to-`v`. -/
def Depth2Det {n : Nat} (G : SchurianSchemeGraph n) (P : PMatrix n)
    (v : Fin n) : Prop :=
  ∀ w u : Fin n, w ≠ v → u ≠ v →
    G.toSchemeGraph.adj.adj w v = G.toSchemeGraph.adj.adj u v →
    P w v = P u v →
    (∀ (a : Nat) (p : POE) (w' : Fin n),
      {u' : Fin n | u' ≠ w ∧ schemePart_at G P v 1 u' w' ∧
                    G.toSchemeGraph.adj.adj w u' = a ∧ P w u' = p}.ncard =
      {u' : Fin n | u' ≠ u ∧ schemePart_at G P v 1 u' w' ∧
                    G.toSchemeGraph.adj.adj u u' = a ∧ P u u' = p}.ncard) →
    G.scheme.relOfPair v w = G.scheme.relOfPair v u

/-- **Depth-1 separation is a special case of depth-2 separation.**
`RelOfPairDetByAdjP` ignores the block-degree counts, so it trivially
implies `Depth2Det`. Confirms depth-2 subsumes the depth-1 coverage. -/
theorem det2_of_det {n : Nat} (G : SchurianSchemeGraph n) (P : PMatrix n)
    (v : Fin n) (hdet : RelOfPairDetByAdjP G P v) :
    Depth2Det G P v := by
  intro w u hwv huv hadj hP _hcount
  exact hdet w u hwv huv hadj hP

/-- **Step 2 convergence at depth 2 under depth-2 separation.** The
second component of `schemePart_at 2` is definitionally the
block-degree count condition; the first component yields adj/`P`-to-`v`
equality via `schemePart_at_one_to_v`. Feeding both to `Depth2Det`
gives `relOfPair`-equality, hence `vProfile`-equality. -/
theorem step2_converges_at_two_of_det2 {n : Nat}
    (G : SchurianSchemeGraph n) (P : PMatrix n) (v : Fin n)
    (hdet2 : Depth2Det G P v) :
    Step2_converges_at G P v 2 := by
  intro w u h
  suffices h_rel : G.scheme.relOfPair v w = G.scheme.relOfPair v u by
    unfold vProfile; rw [h_rel]
  obtain ⟨h1, hcount⟩ := h
  by_cases hwv : w = v
  · -- w = v: schemePart_at 0 forces u = v.
    obtain ⟨h0, _⟩ := h1
    rw [hwv] at h0
    have hu : u = v :=
      (individualizedColouring_singleton_eq_v_iff v u).mp h0.symm
    rw [hwv, hu]
  · by_cases huv : u = v
    · -- u = v: symmetric.
      obtain ⟨h0, _⟩ := h1
      rw [huv] at h0
      have hw : w = v :=
        (individualizedColouring_singleton_eq_v_iff v w).mp h0
      rw [huv, hw]
    · -- Both ≠ v: depth-1 extraction + the block-degree counts + hdet2.
      obtain ⟨hadj, hP⟩ := schemePart_at_one_to_v G P v w u hwv huv h1
      exact hdet2 w u hwv huv hadj hP hcount

/-- **Step 2 from depth-2 separation.** Lifts `Step2_converges_at … 2`
to `Step2_target` via `step2_of_converges_at` (depth `2 ≤ n`). The
`n < 2` case is vacuous: `v : Fin n` forces `n = 1`, where `Fin n` is a
subsingleton and `vProfile` is constant. -/
theorem step2_of_det2 {n : Nat} (G : SchurianSchemeGraph n)
    (P : PMatrix n) (v : Fin n) (hdet2 : Depth2Det G P v) :
    Step2_target G P v := by
  by_cases hn : 2 ≤ n
  · exact step2_of_converges_at G P v 2 hn
      (step2_converges_at_two_of_det2 G P v hdet2)
  · -- n < 2 and v : Fin n ⟹ n = 1; all vertices coincide.
    intro w u _
    have hne : n ≠ 0 := by intro h; rw [h] at v; exact Fin.elim0 v
    have hn1 : n = 1 := by omega
    subst hn1
    rw [Subsingleton.elim w u]

/-- **Theorem 2 unconditional under depth-2 separation.** The depth-2
analogue of `theorem_2_HOR_concrete_of_det`; covers any schurian scheme
graph whose `Depth2Det` is discharged. -/
theorem theorem_2_HOR_concrete_of_det2 {n : Nat} {adj : AdjMatrix n}
    (h : IsSchurianSchemeGraph' adj) (P : PMatrix n) (v : Fin n)
    (hP_invariant : ∀ {π : Equiv.Perm (Fin n)}, IsAut π adj →
      ∀ x u, P (π x) (π u) = P x u)
    (hdet2 : Depth2Det h.G P v) :
    ∀ w u : Fin n,
      OrbitPartition adj P {v} w u ↔
        warmRefine adj P (individualizedColouring n {v}) w =
          warmRefine adj P (individualizedColouring n {v}) u :=
  theorem_2_HOR_concrete h P v hP_invariant (step2_of_det2 h.G P v hdet2)

/-! ### §10.10 — Discharging Depth2Det via intersection-number separation

The depth-2 layer (§10.9) reduces Theorem 2 for a scheme graph to
`Depth2Det`. This section discharges `Depth2Det` for the first
genuinely-rank-≥-3 class, via an abstract scheme-side condition —
mirroring how §10.8 discharged the depth-1 `RelOfPairDetByAdjP` for
`rank = 2 ∧ |J| = 1` without ever constructing a concrete scheme.

**The mechanism.** For a single-edge scheme (`J = {j0}`), the
`schemePart_at 1` class of an edge-neighbour `w₀` of `v` is *exactly*
the edge-relation block `R_{j0}` from `v`:
- `⊆`: `schemePart_at_one_to_v` forces adj-to-`v` equality, and for
  `|J| = 1` adj-to-`v` pins membership in `R_{j0}`.
- `⊇`: same relation with `v` ⟹ a v-fixing automorphism (schurian
  Step 1) ⟹ (with `P`-invariance) an `OrbitPartition` ⟹ equal
  `warmRefine` ⟹ equal `schemePart_at 1`.

So the depth-2 block-degree of `w` into that class, summed over the
`P`-value, counts `{x : relOfPair v x = j0 ∧ relOfPair w x = j0}` =
the intersection number `p^{relOfPair v w}_{j0,j0}`. The depth-2 count
condition then equates these intersection numbers for `w` and `u`,
and the separating hypothesis — `intersectionNumber j0 j0 ·` injective
on the non-edge relations — forces `relOfPair v w = relOfPair v u`.

This covers any single-edge schurian scheme graph whose common-edge-
neighbour-with-`v` count distinguishes the relations that adjacency
alone cannot (rank-≥-3 distance-regular graphs, e.g. the 7-cycle;
Johnson `J(m, k)` and Hamming `H(d, q)` once the count separates their
relations). It strictly subsumes the `rank = 2 ∧ |J| = 1` case, where
there is at most one non-edge relation and the hypothesis is vacuous. -/

/-- **`schemePart_at`-from-orbit chain.** A v-fixing `P`-preserving
automorphism mapping `w` to `u` puts them in the same `schemePart_at k`
class (`k ≤ n`): orbit ⟹ equal `warmRefine` (`subset_warmRefine`) ⟹
equal iter[k] ⟹ `schemePart_at k`. -/
theorem schemePart_at_of_orbit {n : Nat} (G : SchurianSchemeGraph n)
    (P : PMatrix n) (v : Fin n) {k : Nat} (hk : k ≤ n) {w u : Fin n}
    (h : OrbitPartition G.toSchemeGraph.adj P {v} w u) :
    schemePart_at G P v k w u :=
  iter_refines_schemePart_at G P v k w u
    (warmRefine_eq_iter_eq G.toSchemeGraph.adj P (individualizedColouring n {v}) k hk
      (OrbitPartition.subset_warmRefine h))

/-- **vProfile equality ⟹ OrbitPartition** (given `P`-invariance).
Schurian Step 1 supplies a v-fixing graph automorphism; `P`-invariance
upgrades it to a `P`-preserving one. -/
theorem orbit_of_vProfile_eq {n : Nat} (G : SchurianSchemeGraph n)
    (P : PMatrix n) (v : Fin n)
    (hP_invariant : ∀ {π : Equiv.Perm (Fin n)},
      IsAut π G.toSchemeGraph.adj → ∀ x u, P (π x) (π u) = P x u)
    {w u : Fin n} (h : vProfile G.scheme v w = vProfile G.scheme v u) :
    OrbitPartition G.toSchemeGraph.adj P {v} w u := by
  obtain ⟨π, hπ, hπv, hπw⟩ := G.vProfile_eq_imp_graphOrbit v w u h
  refine ⟨π, hπ, hP_invariant hπ, ?_, hπw⟩
  intro x hx
  rw [Finset.mem_singleton] at hx
  subst hx
  exact hπv

/-- **P-value fibering of an `ncard`.** Counting splits over the
finitely-many `POE` values of `P x ·`. Used to drop the `P`-component
from a depth-2 block-degree count, recovering a pure intersection
number. -/
theorem ncard_eq_sum_POE {n : Nat} (P : PMatrix n) (x : Fin n)
    (q : Fin n → Prop) [DecidablePred q] :
    {u' : Fin n | q u'}.ncard
      = ∑ p : POE, {u' : Fin n | q u' ∧ P x u' = p}.ncard := by
  classical
  rw [ncard_setOf_eq_filter_card,
    Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ.filter q) (t := (Finset.univ : Finset POE))
      (f := fun u' => P x u') (fun u' _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro p _
  rw [ncard_setOf_eq_filter_card, ← Finset.filter_filter]

/-- **Intersection-number separation hypothesis.** The common-edge-
neighbour count `intersectionNumber j0 j0 ·` distinguishes the
non-edge, non-diagonal relations from each other. (For `|J| = 1`,
adjacency already separates the edge relation `j0`; this handles the
relations adjacency cannot.) -/
def IntersectionSeparates {n : Nat} (G : SchurianSchemeGraph n)
    (j0 : Fin (G.scheme.rank + 1)) : Prop :=
  ∀ i i' : Fin (G.scheme.rank + 1), i ≠ 0 → i' ≠ 0 → i ≠ j0 → i' ≠ j0 →
    G.scheme.intersectionNumber j0 j0 i = G.scheme.intersectionNumber j0 j0 i' →
    i = i'

/-- **Depth-2 separation from intersection-number separation.** For a
single-edge schurian scheme graph (`J = {j0}`) with an edge-neighbour
of `v`, whose `intersectionNumber j0 j0 ·` separates the non-edge
relations, `Depth2Det` holds — so `schemePart_at 2` converges to
`vProfile`. -/
theorem depth2Det_of_intersectionSeparates {n : Nat} (G : SchurianSchemeGraph n)
    (P : PMatrix n) (v : Fin n) (j0 : Fin (G.scheme.rank + 1))
    (hJ : G.toSchemeGraph.J = {j0})
    (hP_invariant : ∀ {π : Equiv.Perm (Fin n)},
      IsAut π G.toSchemeGraph.adj → ∀ x u, P (π x) (π u) = P x u)
    (hv_nbr : ∃ w₀ : Fin n, G.scheme.relOfPair v w₀ = j0)
    (hsep : IntersectionSeparates G j0) :
    Depth2Det G P v := by
  classical
  have hn : 1 ≤ n :=
    Nat.one_le_iff_ne_zero.mpr (by intro h; rw [h] at v; exact Fin.elim0 v)
  have hj0_ne : j0 ≠ 0 := by
    intro h; subst h
    exact G.toSchemeGraph.zero_notMem_J (by rw [hJ]; exact Finset.mem_singleton_self _)
  -- |J| = 1 turns adjacency into edge-relation membership.
  have hadj_iff : ∀ x y : Fin n,
      G.toSchemeGraph.adj.adj x y = 1 ↔ G.scheme.relOfPair x y = j0 := by
    intro x y
    rw [G.toSchemeGraph.adj_eq_one_iff, hJ, Finset.mem_singleton]
  obtain ⟨w₀, hw₀⟩ := hv_nbr
  have hw₀v : w₀ ≠ v := by
    intro h; subst h
    rw [G.scheme.relOfPair_self] at hw₀; exact hj0_ne hw₀.symm
  -- L1: schemePart_at 1 · w₀  ↔  relOfPair v · = j0.
  have hL1 : ∀ u' : Fin n,
      schemePart_at G P v 1 u' w₀ ↔ G.scheme.relOfPair v u' = j0 := by
    intro u'
    constructor
    · intro hsp
      by_cases hu'v : u' = v
      · exfalso
        obtain ⟨h0, _⟩ := hsp
        rw [hu'v] at h0
        exact hw₀v ((individualizedColouring_singleton_eq_v_iff v w₀).mp h0.symm)
      · have hext := schemePart_at_one_to_v G P v u' w₀ hu'v hw₀v hsp
        have hw₀adj : G.toSchemeGraph.adj.adj v w₀ = 1 := (hadj_iff v w₀).mpr hw₀
        have hvu' : G.toSchemeGraph.adj.adj v u' = 1 := by
          rw [G.toSchemeGraph.adj_symm v u', hext.1, ← G.toSchemeGraph.adj_symm v w₀]
          exact hw₀adj
        exact (hadj_iff v u').mp hvu'
    · intro hrel
      have hvp : vProfile G.scheme v u' = vProfile G.scheme v w₀ := by
        unfold vProfile; rw [hrel, hw₀]
      exact schemePart_at_of_orbit G P v hn (orbit_of_vProfile_eq G P v hP_invariant hvp)
  -- Common-edge-neighbour count = intersection number p^{relOfPair v z}_{j0 j0}.
  have hcommon : ∀ z : Fin n,
      {u' : Fin n | G.scheme.relOfPair v u' = j0 ∧ G.scheme.relOfPair z u' = j0}.ncard
        = G.scheme.intersectionNumber j0 j0 (G.scheme.relOfPair v z) := by
    intro z
    rw [ncard_setOf_eq_filter_card,
      ← G.scheme.intersectionNumber_well_defined j0 j0 (G.scheme.relOfPair v z) v z
        (G.scheme.rel_relOfPair v z)]
    congr 1
    ext u'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [G.scheme.rel_iff_relOfPair, G.scheme.rel_iff_relOfPair,
      G.scheme.relOfPair_symm u' z]
    exact ⟨fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩, fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩⟩
  -- The main statement.
  intro w u hwv huv hadjwv _hPwv hcount
  by_cases hwadj : G.toSchemeGraph.adj.adj w v = 1
  · -- Both adjacent to v ⟹ both in the edge relation j0.
    have hrw : G.scheme.relOfPair v w = j0 := by
      rw [← hadj_iff v w, G.toSchemeGraph.adj_symm v w]; exact hwadj
    have hru : G.scheme.relOfPair v u = j0 := by
      rw [← hadj_iff v u, G.toSchemeGraph.adj_symm v u]; exact hadjwv ▸ hwadj
    rw [hrw, hru]
  · -- Both non-adjacent to v ⟹ both in non-edge relations; use the counts.
    have hwadj0 : G.toSchemeGraph.adj.adj w v = 0 := by
      rcases G.toSchemeGraph.adj_eq_zero_or_one w v with h | h
      · exact h
      · exact absurd h hwadj
    have huadj0 : G.toSchemeGraph.adj.adj u v = 0 := hadjwv ▸ hwadj0
    have hrw_ne_0 : G.scheme.relOfPair v w ≠ 0 :=
      fun heq => hwv ((G.scheme.relOfPair_eq_zero_iff v w).mp heq).symm
    have hru_ne_0 : G.scheme.relOfPair v u ≠ 0 :=
      fun heq => huv ((G.scheme.relOfPair_eq_zero_iff v u).mp heq).symm
    have hrw_ne_j0 : G.scheme.relOfPair v w ≠ j0 := by
      intro hc
      have h1 : G.toSchemeGraph.adj.adj v w = 1 := (hadj_iff v w).mpr hc
      rw [G.toSchemeGraph.adj_symm v w, hwadj0] at h1
      exact one_ne_zero h1.symm
    have hru_ne_j0 : G.scheme.relOfPair v u ≠ j0 := by
      intro hc
      have h1 : G.toSchemeGraph.adj.adj v u = 1 := (hadj_iff v u).mpr hc
      rw [G.toSchemeGraph.adj_symm v u, huadj0] at h1
      exact one_ne_zero h1.symm
    -- Intersection numbers for w and u match, via the depth-2 count condition.
    have hkey : G.scheme.intersectionNumber j0 j0 (G.scheme.relOfPair v w)
              = G.scheme.intersectionNumber j0 j0 (G.scheme.relOfPair v u) := by
      rw [← hcommon w, ← hcommon u, ncard_eq_sum_POE P w, ncard_eq_sum_POE P u]
      apply Finset.sum_congr rfl
      intro p _
      have hAw : {u' : Fin n | (G.scheme.relOfPair v u' = j0 ∧
                    G.scheme.relOfPair w u' = j0) ∧ P w u' = p}
               = {u' : Fin n | u' ≠ w ∧ schemePart_at G P v 1 u' w₀ ∧
                    G.toSchemeGraph.adj.adj w u' = 1 ∧ P w u' = p} := by
        ext u'
        simp only [Set.mem_setOf_eq]
        constructor
        · rintro ⟨⟨hv', hw'⟩, hp⟩
          refine ⟨?_, (hL1 u').mpr hv', (hadj_iff w u').mpr hw', hp⟩
          intro he; rw [he, G.scheme.relOfPair_self] at hw'; exact hj0_ne hw'.symm
        · rintro ⟨_, hsp, hadj1, hp⟩
          exact ⟨⟨(hL1 u').mp hsp, (hadj_iff w u').mp hadj1⟩, hp⟩
      have hAu : {u' : Fin n | (G.scheme.relOfPair v u' = j0 ∧
                    G.scheme.relOfPair u u' = j0) ∧ P u u' = p}
               = {u' : Fin n | u' ≠ u ∧ schemePart_at G P v 1 u' w₀ ∧
                    G.toSchemeGraph.adj.adj u u' = 1 ∧ P u u' = p} := by
        ext u'
        simp only [Set.mem_setOf_eq]
        constructor
        · rintro ⟨⟨hv', hu'⟩, hp⟩
          refine ⟨?_, (hL1 u').mpr hv', (hadj_iff u u').mpr hu', hp⟩
          intro he; rw [he, G.scheme.relOfPair_self] at hu'; exact hj0_ne hu'.symm
        · rintro ⟨_, hsp, hadj1, hp⟩
          exact ⟨⟨(hL1 u').mp hsp, (hadj_iff u u').mp hadj1⟩, hp⟩
      rw [hAw, hAu]
      exact hcount 1 p w₀
    exact hsep _ _ hrw_ne_0 hru_ne_0 hrw_ne_j0 hru_ne_j0 hkey

/-- **Theorem 2 unconditional for single-edge schurian scheme graphs
with intersection-number separation.** Strictly subsumes the
`rank = 2 ∧ |J| = 1` case and covers the first genuinely-rank-≥-3
schemes (depth-1 insufficient, depth-2 sufficient — e.g. the 7-cycle
scheme). Axiom-clean. -/
theorem theorem_2_HOR_concrete_intersectionSeparates {n : Nat} {adj : AdjMatrix n}
    (h : IsSchurianSchemeGraph' adj) (P : PMatrix n) (v : Fin n)
    (j0 : Fin (h.G.scheme.rank + 1)) (hJ : h.G.toSchemeGraph.J = {j0})
    (hP_invariant : ∀ {π : Equiv.Perm (Fin n)}, IsAut π adj →
      ∀ x u, P (π x) (π u) = P x u)
    (hv_nbr : ∃ w₀ : Fin n, h.G.scheme.relOfPair v w₀ = j0)
    (hsep : IntersectionSeparates h.G j0) :
    ∀ w u : Fin n,
      OrbitPartition adj P {v} w u ↔
        warmRefine adj P (individualizedColouring n {v}) w =
          warmRefine adj P (individualizedColouring n {v}) u := by
  have hP' : ∀ {π : Equiv.Perm (Fin n)}, IsAut π h.G.toSchemeGraph.adj →
      ∀ x u, P (π x) (π u) = P x u := by
    intro π hπ; apply hP_invariant; rw [← h.matching]; exact hπ
  exact theorem_2_HOR_concrete_of_det2 h P v hP_invariant
    (depth2Det_of_intersectionSeparates h.G P v j0 hJ hP' hv_nbr hsep)

/-! ### §10.11 — Relation-isolation bootstrap (general depth-k convergence)

The depth-1 (`relOfPairDetByAdjP`) and depth-2 (`IntersectionSeparates`)
results are two instances of one pattern: **a relation whose
`schemePart_at k` class is exactly its relation block can serve as a
counting anchor at depth `k+1`.** The edge relation is isolated at depth
1 by adjacency; each further round bootstraps more relations using the
intersection counts into the already-isolated ones.

This section builds that bootstrap as reusable infrastructure:
- `RelIsolatedAt G P v k l` — relation `l`'s `schemePart_at k` class is
  exactly `R_l` (from `v`).
- `isolatedCount_eq` — the reusable heart: a depth-`k`-isolated `l` lets
  `schemePart_at (k+1)` pin the intersection number `p^{·}_{l, j0}`.
- `relIsolatedAt_one_j0` (base, edge at depth 1), `relIsolatedAt_succ`
  (bootstrap), `convergence_of_all_isolated` (all relations isolated at
  depth `k` ⟹ Step 2 converges at `k`).

An instantiator proves Theorem 2 for any single-edge schurian scheme
graph by exhibiting an **isolation chain** (edge at depth 1, then deeper
relations round by round). This re-derives the depth-2 case and newly
reaches depth-≥-3 schemes (e.g. the 9-cycle, where the distance-2
relation isolates at depth 2 and distance-3/4 separate at depth 3).
General convergence is then exactly "an isolation chain always exists"
— the coherent-algebra content, cleanly isolated. -/

/-- **Relation `l` is isolated at depth `k`.** Its `schemePart_at k`
class is exactly the relation block `R_l` from `v`: any two vertices,
one of which is at relation `l` with `v`, are `schemePart_at k`-related
iff the other is also at relation `l` with `v`. -/
def RelIsolatedAt {n : Nat} (G : SchurianSchemeGraph n) (P : PMatrix n)
    (v : Fin n) (k : Nat) (l : Fin (G.scheme.rank + 1)) : Prop :=
  ∀ w u : Fin n, G.scheme.relOfPair v w = l →
    (schemePart_at G P v k w u ↔ G.scheme.relOfPair v u = l)

/-- **The ⊇ direction, general and free.** Same relation with `v` ⟹
same `schemePart_at k` class (via the orbit chain). -/
theorem vProfile_imp_schemePart_at {n : Nat} (G : SchurianSchemeGraph n)
    (P : PMatrix n) (v : Fin n)
    (hP_invariant : ∀ {π : Equiv.Perm (Fin n)},
      IsAut π G.toSchemeGraph.adj → ∀ x u, P (π x) (π u) = P x u)
    {k : Nat} (hk : k ≤ n) {w u : Fin n}
    (h : vProfile G.scheme v w = vProfile G.scheme v u) :
    schemePart_at G P v k w u :=
  schemePart_at_of_orbit G P v hk (orbit_of_vProfile_eq G P v hP_invariant h)

/-- `schemePart_at` is downward-monotone in the depth. -/
theorem schemePart_at_le {n : Nat} (G : SchurianSchemeGraph n) (P : PMatrix n)
    (v : Fin n) {j k : Nat} (hjk : j ≤ k) {w u : Fin n}
    (h : schemePart_at G P v k w u) : schemePart_at G P v j w u := by
  induction k with
  | zero =>
    have : j = 0 := Nat.le_zero.mp hjk
    subst this; exact h
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hjk with h' | h'
    · subst h'; exact h
    · exact ih (Nat.le_of_lt_succ h') h.1

/-- **Common-neighbour count = intersection number** (general `l, m`):
`#{u' : (v,u') ∈ R_l ∧ (z,u') ∈ R_m}` is the structure constant
`p^{relOfPair v z}_{l,m}`. Generalises the `hcommon` step of
`depth2Det_of_intersectionSeparates`. -/
theorem AssociationScheme.relCommon_eq_intersectionNumber {n : Nat}
    (S : AssociationScheme n) (v z : Fin n) (l m : Fin (S.rank + 1)) :
    {u' : Fin n | S.relOfPair v u' = l ∧ S.relOfPair z u' = m}.ncard
      = S.intersectionNumber l m (S.relOfPair v z) := by
  rw [ncard_setOf_eq_filter_card,
    ← S.intersectionNumber_well_defined l m (S.relOfPair v z) v z
      (S.rel_relOfPair v z)]
  congr 1
  ext u'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [S.rel_iff_relOfPair, S.rel_iff_relOfPair, S.relOfPair_symm u' z]
  exact ⟨fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩, fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩⟩

/-- **The bootstrap counting lemma.** A relation `l` isolated at depth
`k` (with a nonempty block from `v`) lets `schemePart_at (k+1)` pin the
intersection number `p^{relOfPair v ·}_{l, j0}` — the count of common
edge-neighbours via `R_l`. The depth-`(k+1)` block-degree into `R_l`
(summed over `P`) equals this intersection number. -/
theorem isolatedCount_eq {n : Nat} (G : SchurianSchemeGraph n) (P : PMatrix n)
    (v : Fin n) (j0 : Fin (G.scheme.rank + 1)) (hJ : G.toSchemeGraph.J = {j0})
    {k : Nat} {l : Fin (G.scheme.rank + 1)}
    (hiso : RelIsolatedAt G P v k l)
    (hl_nbr : ∃ w₀ : Fin n, G.scheme.relOfPair v w₀ = l)
    {w u : Fin n} (h : schemePart_at G P v (k + 1) w u) :
    G.scheme.intersectionNumber l j0 (G.scheme.relOfPair v w)
      = G.scheme.intersectionNumber l j0 (G.scheme.relOfPair v u) := by
  classical
  have hj0_ne : j0 ≠ 0 := by
    intro hz; subst hz
    exact G.toSchemeGraph.zero_notMem_J (by rw [hJ]; exact Finset.mem_singleton_self _)
  have hadj_iff : ∀ x y : Fin n,
      G.toSchemeGraph.adj.adj x y = 1 ↔ G.scheme.relOfPair x y = j0 := by
    intro x y; rw [G.toSchemeGraph.adj_eq_one_iff, hJ, Finset.mem_singleton]
  obtain ⟨w₀, hw₀⟩ := hl_nbr
  obtain ⟨_, hcount⟩ := h
  have hiso' : ∀ u' : Fin n,
      schemePart_at G P v k u' w₀ ↔ G.scheme.relOfPair v u' = l := by
    intro u'
    rw [show schemePart_at G P v k u' w₀ ↔ schemePart_at G P v k w₀ u' from
      ⟨schemePart_at_symm G P v k, schemePart_at_symm G P v k⟩]
    exact hiso w₀ u' hw₀
  rw [← G.scheme.relCommon_eq_intersectionNumber v w l j0,
    ← G.scheme.relCommon_eq_intersectionNumber v u l j0,
    ncard_eq_sum_POE P w, ncard_eq_sum_POE P u]
  apply Finset.sum_congr rfl
  intro p _
  have hAw : {u' : Fin n | (G.scheme.relOfPair v u' = l ∧
                G.scheme.relOfPair w u' = j0) ∧ P w u' = p}
           = {u' : Fin n | u' ≠ w ∧ schemePart_at G P v k u' w₀ ∧
                G.toSchemeGraph.adj.adj w u' = 1 ∧ P w u' = p} := by
    ext u'; simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨hv', hw'⟩, hp⟩
      refine ⟨?_, (hiso' u').mpr hv', (hadj_iff w u').mpr hw', hp⟩
      intro he; rw [he, G.scheme.relOfPair_self] at hw'; exact hj0_ne hw'.symm
    · rintro ⟨_, hsp, hadj1, hp⟩
      exact ⟨⟨(hiso' u').mp hsp, (hadj_iff w u').mp hadj1⟩, hp⟩
  have hAu : {u' : Fin n | (G.scheme.relOfPair v u' = l ∧
                G.scheme.relOfPair u u' = j0) ∧ P u u' = p}
           = {u' : Fin n | u' ≠ u ∧ schemePart_at G P v k u' w₀ ∧
                G.toSchemeGraph.adj.adj u u' = 1 ∧ P u u' = p} := by
    ext u'; simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨hv', hu'⟩, hp⟩
      refine ⟨?_, (hiso' u').mpr hv', (hadj_iff u u').mpr hu', hp⟩
      intro he; rw [he, G.scheme.relOfPair_self] at hu'; exact hj0_ne hu'.symm
    · rintro ⟨_, hsp, hadj1, hp⟩
      exact ⟨⟨(hiso' u').mp hsp, (hadj_iff u u').mp hadj1⟩, hp⟩
  rw [hAw, hAu]
  exact hcount 1 p w₀

/-- **Base case: the edge relation is isolated at depth 1.** `R_{j0}` is
exactly the depth-1 (`schemePart_at 1`) class of any edge-neighbour of
`v` — ⊆ from `schemePart_at_one_to_v` + `|J|=1`, ⊇ from the orbit chain. -/
theorem relIsolatedAt_one_j0 {n : Nat} (G : SchurianSchemeGraph n) (P : PMatrix n)
    (v : Fin n) (j0 : Fin (G.scheme.rank + 1)) (hJ : G.toSchemeGraph.J = {j0})
    (hP_invariant : ∀ {π : Equiv.Perm (Fin n)},
      IsAut π G.toSchemeGraph.adj → ∀ x u, P (π x) (π u) = P x u) :
    RelIsolatedAt G P v 1 j0 := by
  classical
  have hn : 1 ≤ n :=
    Nat.one_le_iff_ne_zero.mpr (by intro hz; rw [hz] at v; exact Fin.elim0 v)
  have hj0_ne : j0 ≠ 0 := by
    intro hz; subst hz
    exact G.toSchemeGraph.zero_notMem_J (by rw [hJ]; exact Finset.mem_singleton_self _)
  have hadj_iff : ∀ x y : Fin n,
      G.toSchemeGraph.adj.adj x y = 1 ↔ G.scheme.relOfPair x y = j0 := by
    intro x y; rw [G.toSchemeGraph.adj_eq_one_iff, hJ, Finset.mem_singleton]
  intro w u hwj0
  have hwv : w ≠ v := by
    intro he; rw [he, G.scheme.relOfPair_self] at hwj0; exact hj0_ne hwj0.symm
  constructor
  · intro hsp
    by_cases huv : u = v
    · exfalso
      obtain ⟨h0, _⟩ := hsp
      rw [huv] at h0
      exact hwv ((individualizedColouring_singleton_eq_v_iff v w).mp h0)
    · have hext := schemePart_at_one_to_v G P v w u hwv huv hsp
      have hwadj : G.toSchemeGraph.adj.adj v w = 1 := (hadj_iff v w).mpr hwj0
      have hvu : G.toSchemeGraph.adj.adj v u = 1 := by
        rw [G.toSchemeGraph.adj_symm v u, ← hext.1, G.toSchemeGraph.adj_symm w v]
        exact hwadj
      exact (hadj_iff v u).mp hvu
  · intro hru
    have hvp : vProfile G.scheme v w = vProfile G.scheme v u := by
      unfold vProfile; rw [hwj0, hru]
    exact vProfile_imp_schemePart_at G P v hP_invariant hn hvp

/-- **The diagonal relation is isolated at every depth.** `R_0` is the
singleton `{v}`, which is always its own `schemePart_at k` class. -/
theorem relIsolatedAt_zero {n : Nat} (G : SchurianSchemeGraph n) (P : PMatrix n)
    (v : Fin n) (k : Nat) : RelIsolatedAt G P v k 0 := by
  intro w u hw0
  have hwv : w = v := ((G.scheme.relOfPair_eq_zero_iff v w).mp hw0).symm
  rw [hwv]
  constructor
  · intro hsp
    have h1 := schemePart_at_le G P v (Nat.zero_le k) hsp
    have : u = v := (individualizedColouring_singleton_eq_v_iff v u).mp h1.symm
    rw [this]; exact G.scheme.relOfPair_self v
  · intro hu0
    have : u = v := ((G.scheme.relOfPair_eq_zero_iff v u).mp hu0).symm
    rw [this]; exact schemePart_at_refl G P v k v

/-- **Isolation is upward-closed in depth.** A relation isolated at
depth `k` stays isolated at every depth `k ≤ j ≤ n`. -/
theorem relIsolatedAt_mono {n : Nat} (G : SchurianSchemeGraph n) (P : PMatrix n)
    (v : Fin n)
    (hP_invariant : ∀ {π : Equiv.Perm (Fin n)},
      IsAut π G.toSchemeGraph.adj → ∀ x u, P (π x) (π u) = P x u)
    {k j : Nat} {l : Fin (G.scheme.rank + 1)} (hkj : k ≤ j) (hjn : j ≤ n)
    (h : RelIsolatedAt G P v k l) : RelIsolatedAt G P v j l := by
  intro w u hwl
  constructor
  · intro hsp
    exact (h w u hwl).mp (schemePart_at_le G P v hkj hsp)
  · intro hul
    have hvp : vProfile G.scheme v w = vProfile G.scheme v u := by
      unfold vProfile; rw [hwl, hul]
    exact vProfile_imp_schemePart_at G P v hP_invariant hjn hvp

/-- **The bootstrap step.** If a finset `Iso` of relations is isolated
at depth `k` (each with a nonempty block from `v`), and relation `i` is
uniquely pinned among non-diagonal relations by its adjacency-to-`v`
class together with the intersection counts `p^{·}_{l, j0}` into the
`Iso` relations, then `i` is isolated at depth `k+1`. -/
theorem relIsolatedAt_succ {n : Nat} (G : SchurianSchemeGraph n) (P : PMatrix n)
    (v : Fin n) (j0 : Fin (G.scheme.rank + 1)) (hJ : G.toSchemeGraph.J = {j0})
    (hP_invariant : ∀ {π : Equiv.Perm (Fin n)},
      IsAut π G.toSchemeGraph.adj → ∀ x u, P (π x) (π u) = P x u)
    {k : Nat} (hkn : k + 1 ≤ n) (Iso : Finset (Fin (G.scheme.rank + 1)))
    (hIso : ∀ l ∈ Iso, RelIsolatedAt G P v k l)
    (hIso_nbr : ∀ l ∈ Iso, ∃ w₀ : Fin n, G.scheme.relOfPair v w₀ = l)
    (i : Fin (G.scheme.rank + 1)) (hi_ne : i ≠ 0)
    (hsep : ∀ i' : Fin (G.scheme.rank + 1), i' ≠ 0 →
        ((i' = j0) ↔ (i = j0)) →
        (∀ l ∈ Iso, G.scheme.intersectionNumber l j0 i'
          = G.scheme.intersectionNumber l j0 i) →
        i' = i) :
    RelIsolatedAt G P v (k + 1) i := by
  classical
  have hadj_iff : ∀ x y : Fin n,
      G.toSchemeGraph.adj.adj x y = 1 ↔ G.scheme.relOfPair x y = j0 := by
    intro x y; rw [G.toSchemeGraph.adj_eq_one_iff, hJ, Finset.mem_singleton]
  intro w u hwi
  have hwv : w ≠ v := by
    intro he; rw [he, G.scheme.relOfPair_self] at hwi; exact hi_ne hwi.symm
  constructor
  · intro hsp
    have hsp1 : schemePart_at G P v 1 w u :=
      schemePart_at_le G P v (by omega) hsp
    have huv : u ≠ v := by
      intro he
      obtain ⟨h0, _⟩ := hsp1
      rw [he] at h0
      exact hwv ((individualizedColouring_singleton_eq_v_iff v w).mp h0)
    have hext := schemePart_at_one_to_v G P v w u hwv huv hsp1
    have hadj_match : (G.scheme.relOfPair v u = j0) ↔ (i = j0) := by
      rw [← hwi, ← hadj_iff v u, ← hadj_iff v w,
        G.toSchemeGraph.adj_symm v u, G.toSchemeGraph.adj_symm v w, hext.1]
    apply hsep (G.scheme.relOfPair v u)
    · intro hz; exact huv ((G.scheme.relOfPair_eq_zero_iff v u).mp hz).symm
    · exact hadj_match
    · intro l hl
      have hc := isolatedCount_eq G P v j0 hJ (hIso l hl) (hIso_nbr l hl) hsp
      rw [← hwi]; exact hc.symm
  · intro hui
    have hvp : vProfile G.scheme v w = vProfile G.scheme v u := by
      unfold vProfile; rw [hwi, hui]
    exact vProfile_imp_schemePart_at G P v hP_invariant hkn hvp

/-- **Convergence from full isolation.** If every relation is isolated
at depth `k`, then `schemePart_at k` equals the `vProfile` partition —
`Step2_converges_at G P v k`. -/
theorem convergence_of_all_isolated {n : Nat} (G : SchurianSchemeGraph n)
    (P : PMatrix n) (v : Fin n) {k : Nat}
    (hall : ∀ l : Fin (G.scheme.rank + 1), RelIsolatedAt G P v k l) :
    Step2_converges_at G P v k := by
  intro w u hsp
  have h := (hall (G.scheme.relOfPair v w) w u rfl).mp hsp
  unfold vProfile; rw [h]

/-- **Theorem 2 from an isolation chain.** If an instantiator exhibits
that every relation is isolated by depth `k ≤ n` (edge at depth 1 via
`relIsolatedAt_one_j0`, deeper relations via `relIsolatedAt_succ`,
lifting earlier ones with `relIsolatedAt_mono`), Theorem 2 holds
unconditionally. This is the general engine; the depth-2
`IntersectionSeparates` result is its `Iso = {j0}`, `k = 2` instance,
and depth-≥-3 schemes (e.g. the 9-cycle) chain `relIsolatedAt_succ`
further. -/
theorem theorem_2_HOR_concrete_of_isolation {n : Nat} {adj : AdjMatrix n}
    (h : IsSchurianSchemeGraph' adj) (P : PMatrix n) (v : Fin n) {k : Nat}
    (hk : k ≤ n)
    (hP_invariant : ∀ {π : Equiv.Perm (Fin n)}, IsAut π adj →
      ∀ x u, P (π x) (π u) = P x u)
    (hall : ∀ l : Fin (h.G.scheme.rank + 1), RelIsolatedAt h.G P v k l) :
    ∀ w u : Fin n,
      OrbitPartition adj P {v} w u ↔
        warmRefine adj P (individualizedColouring n {v}) w =
          warmRefine adj P (individualizedColouring n {v}) u :=
  theorem_2_HOR_concrete h P v hP_invariant
    (step2_of_converges_at h.G P v k hk (convergence_of_all_isolated h.G P v hall))

/-- **Theorem 2 for depth-3 single-anchor schemes** (e.g. the 9-cycle).
A worked instance of the isolation bootstrap reaching depth 3: the edge
relation `j0` isolates at depth 1; a single anchor relation `l0` —
pinned among the non-edge relations by its common-edge-neighbour count
`p^{·}_{j0,j0}` — isolates at depth 2; then the full profile
`(adjacency, p^{·}_{j0,j0}, p^{·}_{l0,j0})` separates every relation, so
all isolate by depth 3 and Theorem 2 holds. Covers rank-≥-3 schemes the
single-count depth-2 result cannot (the 9-cycle: distance-2 isolates at
depth 2, distance-3/4 separate at depth 3 via counts into distance-2). -/
theorem theorem_2_HOR_concrete_intersectionSeparates3 {n : Nat} {adj : AdjMatrix n}
    (h : IsSchurianSchemeGraph' adj) (P : PMatrix n) (v : Fin n)
    (j0 l0 : Fin (h.G.scheme.rank + 1)) (hJ : h.G.toSchemeGraph.J = {j0})
    (h3n : 3 ≤ n)
    (hP_invariant : ∀ {π : Equiv.Perm (Fin n)}, IsAut π adj →
      ∀ x u, P (π x) (π u) = P x u)
    (hj0_nbr : ∃ w₀ : Fin n, h.G.scheme.relOfPair v w₀ = j0)
    (hl0_nbr : ∃ w₀ : Fin n, h.G.scheme.relOfPair v w₀ = l0)
    (hl0_ne0 : l0 ≠ 0) (hl0_nej0 : l0 ≠ j0)
    (hl0_iso : ∀ i : Fin (h.G.scheme.rank + 1), i ≠ 0 → i ≠ j0 →
        h.G.scheme.intersectionNumber j0 j0 i
          = h.G.scheme.intersectionNumber j0 j0 l0 → i = l0)
    (hsep3 : ∀ i i' : Fin (h.G.scheme.rank + 1), i ≠ 0 → i' ≠ 0 →
        ((i = j0) ↔ (i' = j0)) →
        h.G.scheme.intersectionNumber j0 j0 i
          = h.G.scheme.intersectionNumber j0 j0 i' →
        h.G.scheme.intersectionNumber l0 j0 i
          = h.G.scheme.intersectionNumber l0 j0 i' →
        i = i') :
    ∀ w u : Fin n,
      OrbitPartition adj P {v} w u ↔
        warmRefine adj P (individualizedColouring n {v}) w =
          warmRefine adj P (individualizedColouring n {v}) u := by
  have hP' : ∀ {π : Equiv.Perm (Fin n)}, IsAut π h.G.toSchemeGraph.adj →
      ∀ x u, P (π x) (π u) = P x u := by
    intro π hπ; apply hP_invariant; rw [← h.matching]; exact hπ
  have hj0_1 : RelIsolatedAt h.G P v 1 j0 := relIsolatedAt_one_j0 h.G P v j0 hJ hP'
  have hj0_2 : RelIsolatedAt h.G P v 2 j0 :=
    relIsolatedAt_mono h.G P v hP' (by omega) (by omega) hj0_1
  have hl0_2 : RelIsolatedAt h.G P v 2 l0 := by
    refine relIsolatedAt_succ h.G P v j0 hJ hP' (by omega) {j0} ?_ ?_ l0 hl0_ne0 ?_
    · intro m hm; rw [Finset.mem_singleton] at hm; subst hm; exact hj0_1
    · intro m hm; rw [Finset.mem_singleton] at hm; subst hm; exact hj0_nbr
    · intro i' hi'0 hadjmatch hcounts
      have hi'j : i' ≠ j0 := fun hc => hl0_nej0 (hadjmatch.mp hc)
      exact hl0_iso i' hi'0 hi'j (hcounts j0 (Finset.mem_singleton_self _))
  have hall : ∀ l : Fin (h.G.scheme.rank + 1), RelIsolatedAt h.G P v 3 l := by
    intro l
    by_cases hl0eq : l = 0
    · subst hl0eq; exact relIsolatedAt_zero h.G P v 3
    · by_cases hlj : l = j0
      · subst hlj; exact relIsolatedAt_mono h.G P v hP' (by omega) h3n hj0_2
      · by_cases hll0 : l = l0
        · subst hll0; exact relIsolatedAt_mono h.G P v hP' (by omega) h3n hl0_2
        · refine relIsolatedAt_succ h.G P v j0 hJ hP' h3n {j0, l0} ?_ ?_ l hl0eq ?_
          · intro m hm
            rw [Finset.mem_insert, Finset.mem_singleton] at hm
            rcases hm with rfl | rfl
            · exact hj0_2
            · exact hl0_2
          · intro m hm
            rw [Finset.mem_insert, Finset.mem_singleton] at hm
            rcases hm with rfl | rfl
            · exact hj0_nbr
            · exact hl0_nbr
          · intro i' hi'0 hadjmatch hcounts
            exact hsep3 i' l hi'0 hl0eq hadjmatch
              (hcounts j0 (by simp)) (hcounts l0 (by simp))
  exact theorem_2_HOR_concrete_of_isolation h P v h3n hP_invariant hall

/-! ### §10.12 — General convergence: the isolation closure

`theorem_2_HOR_concrete_intersectionSeparates3` reached depth-3 schemes but took
the per-scheme separation data (`hl0_iso`, `hsep3`) as hypotheses — the
rank-by-rank ladder. This subsection replaces the ladder with **one** structural
hypothesis, `EdgeGenerates`: the *isolation closure* of `{R₀, R_{j0}}` — the
diagonal and edge relation, then everything iteratively pinned by
intersection-counts into the already-isolated relations — reaches every relation
occurring from `v`.

The closure round `isolationStep` is an **extensive operator** on
`Finset (Fin (rank+1))`, so the generic `ChainDescent.Saturation` engine bounds
its saturation depth; running it inside `B = occursFromV` keeps that depth `≤ n`
even when empty relations inflate the nominal carrier `Fin (rank+1)` beyond `n`.
`EdgeGenerates` is the concrete, decidable realisation of the oracle-capability
seal's **D1** ("a poly-length symmetry-only process exposes the symmetry") for
scheme graphs. -/

/-- The relations that actually **occur from `v`** (non-empty blocks `R_l` from
`v`). The honest carrier for the isolation closure: `relIsolatedAt_succ`'s
counting needs non-empty blocks, and relations that never occur from `v` are
vacuously isolated. -/
noncomputable def occursFromV {n : Nat} (G : SchurianSchemeGraph n) (v : Fin n) :
    Finset (Fin (G.scheme.rank + 1)) :=
  Finset.univ.image (fun w => G.scheme.relOfPair v w)

theorem mem_occursFromV {n : Nat} (G : SchurianSchemeGraph n) (v : Fin n)
    {l : Fin (G.scheme.rank + 1)} :
    l ∈ occursFromV G v ↔ ∃ w, G.scheme.relOfPair v w = l := by
  simp only [occursFromV, Finset.mem_image, Finset.mem_univ, true_and]

theorem zero_mem_occursFromV {n : Nat} (G : SchurianSchemeGraph n) (v : Fin n) :
    (0 : Fin (G.scheme.rank + 1)) ∈ occursFromV G v :=
  (mem_occursFromV G v).mpr ⟨v, G.scheme.relOfPair_self v⟩

theorem occursFromV_card_le {n : Nat} (G : SchurianSchemeGraph n) (v : Fin n) :
    (occursFromV G v).card ≤ n := by
  refine le_trans Finset.card_image_le ?_
  rw [Finset.card_univ, Fintype.card_fin]

/-- **`i` is pinned by `Iso`**: `i` is the unique non-diagonal relation with its
`(edge-membership, intersection-counts into Iso)` signature — exactly the `hsep`
hypothesis of `relIsolatedAt_succ`. -/
def IsoPinned {n : Nat} (G : SchurianSchemeGraph n)
    (j0 Iso_i : Fin (G.scheme.rank + 1)) (Iso : Finset (Fin (G.scheme.rank + 1)))
    : Prop :=
  Iso_i ≠ 0 ∧ ∀ i' : Fin (G.scheme.rank + 1), i' ≠ 0 → ((i' = j0) ↔ (Iso_i = j0)) →
    (∀ l ∈ Iso, G.scheme.intersectionNumber l j0 i'
      = G.scheme.intersectionNumber l j0 Iso_i) → i' = Iso_i

/-- One round of the **isolation closure**: keep `Iso`, and add every relation
occurring from `v` that is pinned by `Iso`. -/
noncomputable def isolationStep {n : Nat} (G : SchurianSchemeGraph n) (v : Fin n)
    (j0 : Fin (G.scheme.rank + 1)) (Iso : Finset (Fin (G.scheme.rank + 1))) :
    Finset (Fin (G.scheme.rank + 1)) :=
  Iso ∪ @Finset.filter _ (fun i => IsoPinned G j0 i Iso)
    (Classical.decPred _) (occursFromV G v)

/-- Membership in one closure round: already isolated, or newly pinned. -/
theorem mem_isolationStep {n : Nat} (G : SchurianSchemeGraph n) (v : Fin n)
    (j0 : Fin (G.scheme.rank + 1)) {Iso : Finset (Fin (G.scheme.rank + 1))}
    {i : Fin (G.scheme.rank + 1)} :
    i ∈ isolationStep G v j0 Iso ↔
      i ∈ Iso ∨ (i ∈ occursFromV G v ∧ IsoPinned G j0 i Iso) := by
  classical
  rw [isolationStep, Finset.mem_union, Finset.mem_filter]

/-- The closure round is **extensive** — the input drives the engine. -/
theorem subset_isolationStep {n : Nat} (G : SchurianSchemeGraph n) (v : Fin n)
    (j0 : Fin (G.scheme.rank + 1)) (Iso : Finset (Fin (G.scheme.rank + 1))) :
    Iso ⊆ isolationStep G v j0 Iso :=
  Finset.subset_union_left

/-- The closure round **preserves the `occursFromV` bound** — so the generic
engine saturates within `occursFromV.card ≤ n` steps. -/
theorem isolationStep_subset_occursFromV {n : Nat} (G : SchurianSchemeGraph n)
    (v : Fin n) (j0 : Fin (G.scheme.rank + 1))
    {Iso : Finset (Fin (G.scheme.rank + 1))} (h : Iso ⊆ occursFromV G v) :
    isolationStep G v j0 Iso ⊆ occursFromV G v := by
  classical
  rw [isolationStep]
  exact Finset.union_subset h (Finset.filter_subset _ _)

/-- Relations that never occur from `v` are **vacuously isolated** at any depth
(the `relOfPair v w = l` premise is never met). -/
theorem relIsolatedAt_of_not_occurs {n : Nat} (G : SchurianSchemeGraph n)
    (P : PMatrix n) (v : Fin n) (k : Nat) {l : Fin (G.scheme.rank + 1)}
    (hl : l ∉ occursFromV G v) : RelIsolatedAt G P v k l := by
  intro w u hwl
  exact absurd ((mem_occursFromV G v).mpr ⟨w, hwl⟩) hl

/-- **Stage lemma (the closure ⇒ isolation engine).** Every relation present in
the `m`-th closure round `isolationStep^[m] {0, j0}` is isolated at depth
`m + 1`. Proved by induction: the seed `{R₀, R_{j0}}` is isolated at depth 1
(`relIsolatedAt_zero` / `relIsolatedAt_one_j0`); a relation carried from the
previous round lifts via `relIsolatedAt_mono`; a newly-pinned relation isolates
at the next depth via `relIsolatedAt_succ` (its `hsep` is exactly the
`IsoPinned` witness the closure round filtered on, `hIso_nbr` from the
`occursFromV` bound). -/
theorem stage_relIsolatedAt {n : Nat} (G : SchurianSchemeGraph n) (P : PMatrix n)
    (v : Fin n) (j0 : Fin (G.scheme.rank + 1)) (hJ : G.toSchemeGraph.J = {j0})
    (hP' : ∀ {π : Equiv.Perm (Fin n)}, IsAut π G.toSchemeGraph.adj →
      ∀ x u, P (π x) (π u) = P x u)
    (hseed : ({0, j0} : Finset (Fin (G.scheme.rank + 1))) ⊆ occursFromV G v) :
    ∀ m : ℕ, m + 1 ≤ n →
      ∀ l ∈ (isolationStep G v j0)^[m] {0, j0}, RelIsolatedAt G P v (m + 1) l := by
  intro m
  induction m with
  | zero =>
    intro _ l hl
    rw [Function.iterate_zero_apply, Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | hlj
    · exact relIsolatedAt_zero G P v 1
    · rw [hlj]; exact relIsolatedAt_one_j0 G P v j0 hJ hP'
  | succ m ih =>
    intro hm l hl
    rw [Function.iterate_succ_apply', mem_isolationStep] at hl
    have hsub : (isolationStep G v j0)^[m] {0, j0} ⊆ occursFromV G v :=
      Saturation.iterate_subset_of_invariant (isolationStep G v j0)
        (occursFromV G v) {0, j0} hseed
        (fun s hs => isolationStep_subset_occursFromV G v j0 hs) m
    rcases hl with hlold | ⟨_, hpin⟩
    · exact relIsolatedAt_mono G P v hP' (by omega) hm (ih (by omega) l hlold)
    · obtain ⟨hi_ne, hsep⟩ := hpin
      exact relIsolatedAt_succ G P v j0 hJ hP' (k := m + 1) hm
        ((isolationStep G v j0)^[m] {0, j0})
        (fun l' hl' => ih (by omega) l' hl')
        (fun l' hl' => (mem_occursFromV G v).mp (hsub hl'))
        l hi_ne hsep

/-- **EdgeGenerates** — the one structural hypothesis replacing the rank ladder.
The isolation closure of `{R₀, R_{j0}}`, iterated `|occursFromV|` times (≥ the
saturation bound), reaches every relation occurring from `v`. Equivalently: the
edge relation, by iterated common-neighbour counting, *exposes* every relation —
the scheme-graph realisation of the seal's **D1**. -/
def EdgeGenerates {n : Nat} (G : SchurianSchemeGraph n) (v : Fin n)
    (j0 : Fin (G.scheme.rank + 1)) : Prop :=
  occursFromV G v ⊆ (isolationStep G v j0)^[(occursFromV G v).card] {0, j0}

/-- **General convergence — Theorem 2 from `EdgeGenerates`.** A single theorem
covering *every* single-edge schurian scheme graph whose edge relation
generates the scheme, with **no per-rank separation data**: the saturation
engine bounds the closure depth at `≤ n`, the stage lemma turns the closure into
full isolation, and `theorem_2_HOR_concrete_of_isolation` finishes. The
per-instance `…rank_two_J_singleton` / `…intersectionSeparates` /
`…intersectionSeparates3` theorems are now special cases (each proves
`EdgeGenerates` in `1`/`2`/`3` rounds). -/
theorem theorem_2_HOR_of_edgeGenerates {n : Nat} {adj : AdjMatrix n}
    (h : IsSchurianSchemeGraph' adj) (P : PMatrix n) (v : Fin n)
    (j0 : Fin (h.G.scheme.rank + 1)) (hJ : h.G.toSchemeGraph.J = {j0})
    (hP_invariant : ∀ {π : Equiv.Perm (Fin n)}, IsAut π adj →
      ∀ x u, P (π x) (π u) = P x u)
    (hj0_nbr : ∃ w₀ : Fin n, h.G.scheme.relOfPair v w₀ = j0)
    (hEG : EdgeGenerates h.G v j0) :
    ∀ w u : Fin n,
      OrbitPartition adj P {v} w u ↔
        warmRefine adj P (individualizedColouring n {v}) w =
          warmRefine adj P (individualizedColouring n {v}) u := by
  classical
  have hP' : ∀ {π : Equiv.Perm (Fin n)}, IsAut π h.G.toSchemeGraph.adj →
      ∀ x u, P (π x) (π u) = P x u := by
    intro π hπ; apply hP_invariant; rw [← h.matching]; exact hπ
  have hseed : ({0, j0} : Finset (Fin (h.G.scheme.rank + 1))) ⊆ occursFromV h.G v := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | hxj
    · exact zero_mem_occursFromV h.G v
    · rw [hxj]; exact (mem_occursFromV h.G v).mpr hj0_nbr
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le v.val) v.isLt
  obtain ⟨k₀, hk₀le, hfix⟩ :=
    Saturation.exists_iterate_isFixed_within (isolationStep h.G v j0)
      (subset_isolationStep h.G v j0) (occursFromV h.G v) {0, j0} hseed
      (fun s hs => isolationStep_subset_occursFromV h.G v j0 hs)
  have hcardle : (occursFromV h.G v).card ≤ n := occursFromV_card_le h.G v
  have hseedpos : 0 < ({0, j0} : Finset (Fin (h.G.scheme.rank + 1))).card :=
    Finset.card_pos.mpr ⟨0, Finset.mem_insert_self _ _⟩
  have hKn : k₀ + 1 ≤ n := by omega
  have hreach : occursFromV h.G v ⊆ (isolationStep h.G v j0)^[k₀] {0, j0} := by
    have hCk : (isolationStep h.G v j0)^[(occursFromV h.G v).card] {0, j0}
        = (isolationStep h.G v j0)^[k₀] {0, j0} := by
      conv_lhs => rw [show (occursFromV h.G v).card
        = ((occursFromV h.G v).card - k₀) + k₀ from by omega]
      rw [Function.iterate_add_apply]
      exact Saturation.iterate_eq_of_isFixed (isolationStep h.G v j0) hfix _
    rw [← hCk]; exact hEG
  have hall : ∀ l : Fin (h.G.scheme.rank + 1), RelIsolatedAt h.G P v (k₀ + 1) l := by
    intro l
    by_cases hlo : l ∈ occursFromV h.G v
    · exact stage_relIsolatedAt h.G P v j0 hJ hP' hseed k₀ hKn l (hreach hlo)
    · exact relIsolatedAt_of_not_occurs h.G P v (k₀ + 1) hlo
  exact theorem_2_HOR_concrete_of_isolation h P v hKn hP_invariant hall

/-! ### §10.13 — The structural class: P-polynomial (metric / distance-regular) schemes

`theorem_2_HOR_of_edgeGenerates` is the uniform engine, but `EdgeGenerates` is
still proved per scheme. This subsection discharges it **for an entire
structural family at once**: every *P-polynomial* (metric, i.e.
distance-regular) schurian scheme — Johnson, Hamming, cycles, all DRGs.

A scheme is P-polynomial when its relations are *distance* relations
`R 0, R 1, …, R d` (`R 1 = j0` the edge) with a **tridiagonal** intersection
array: `intersectionNumber (R a) j0 (R k) = 0` for `|a − k| ≥ 2`, and the
subdiagonal `c_k = intersectionNumber (R (k−1)) j0 (R k)` is nonzero. Then the
edge relation generates: distance `R k` is the *unique* relation whose
intersection counts into the closer distances match (the `m </=/> k` case
split below), so the isolation closure walks out the distance ladder and
reaches every relation — `EdgeGenerates`.

**Leg-A pattern.** The leveling `R : ℕ → relation` with "each level pinned by
strictly-lower levels" is the scheme instance of D1's *graded* exposure: a
poly-length symmetry-only process (here: BFS by distance) that exposes the whole
structure. The `IsoPinned.mono` + closure-fixpoint induction is the reusable
"a graded pinning saturates the closure" skeleton — directly transplantable to
Leg A's support induction. -/

/-- **Pinning is monotone in the isolated set.** A larger `Iso` only adds
matching constraints, so it can only *shrink* the set of rival relations — if
`i` was uniquely pinned by `Iso1`, it stays uniquely pinned by any `Iso2 ⊇
Iso1`. The lemma that lets a graded chain feed the closure's growing fixpoint. -/
theorem IsoPinned.mono {n : Nat} {G : SchurianSchemeGraph n}
    {j0 i : Fin (G.scheme.rank + 1)} {Iso1 Iso2 : Finset (Fin (G.scheme.rank + 1))}
    (h : IsoPinned G j0 i Iso1) (hsub : Iso1 ⊆ Iso2) : IsoPinned G j0 i Iso2 := by
  obtain ⟨hne, hsep⟩ := h
  refine ⟨hne, fun i' hi'_ne hadj hcounts =>
    hsep i' hi'_ne hadj (fun l hl => hcounts l (hsub hl))⟩

/-- **P-polynomial (metric) schurian scheme** w.r.t. edge relation `j0`. The
relations are a distance ladder `R 0 = R₀, R 1 = j0, …, R rank` (bijective onto
all relations, each occurring from `v`) with a tridiagonal intersection array
and nonzero subdiagonal. This is the abstract form of "distance-regular". -/
structure PPolynomial {n : Nat} (G : SchurianSchemeGraph n) (v : Fin n)
    (j0 : Fin (G.scheme.rank + 1)) where
  /-- Distance-`k` relation. -/
  R : ℕ → Fin (G.scheme.rank + 1)
  /-- The diameter is at least 1 (there is an edge relation). -/
  one_le_rank : 1 ≤ G.scheme.rank
  /-- `R 0` is the diagonal. -/
  R_zero : R 0 = 0
  /-- `R 1` is the edge relation. -/
  R_one : R 1 = j0
  /-- The distance ladder is injective on `[0, rank]`. -/
  R_inj : ∀ a b, a ≤ G.scheme.rank → b ≤ G.scheme.rank → R a = R b → a = b
  /-- …and surjective onto all relations (so there are no extra relations). -/
  R_surj : ∀ i : Fin (G.scheme.rank + 1), ∃ k, k ≤ G.scheme.rank ∧ R k = i
  /-- Every distance relation occurs from `v`. -/
  R_occurs : ∀ k, k ≤ G.scheme.rank → R k ∈ occursFromV G v
  /-- **Tridiagonal**: counts vanish off the distance band `|a − k| ≤ 1`. -/
  tridiagonal : ∀ a k, a ≤ G.scheme.rank → k ≤ G.scheme.rank →
    (a + 1 < k ∨ k + 1 < a) → G.scheme.intersectionNumber (R a) j0 (R k) = 0
  /-- **Nonzero subdiagonal** `c_k`: each distance is reachable from the prior. -/
  subdiagonal : ∀ k, 1 ≤ k → k ≤ G.scheme.rank →
    G.scheme.intersectionNumber (R (k - 1)) j0 (R k) ≠ 0

/-- **The metric pinning lemma.** In a P-polynomial scheme, distance relation
`R k` (`k ≥ 2`) is uniquely pinned among non-diagonal relations by its
intersection counts into the strictly-closer distances `{R 0, …, R (k−1)}`. A
rival `R m` is excluded by a single off-band zero: if `m > k`, its count into
`R (k−1)` vanishes while `c_k ≠ 0`; if `m < k`, its own subdiagonal `c_m ≠ 0`
clashes with the off-band zero into `R (m−1)`. -/
theorem pPolynomial_pinned {n : Nat} (G : SchurianSchemeGraph n) (v : Fin n)
    (j0 : Fin (G.scheme.rank + 1)) (hpp : PPolynomial G v j0)
    {k : ℕ} (hk2 : 2 ≤ k) (hkd : k ≤ G.scheme.rank) :
    IsoPinned G j0 (hpp.R k) ((Finset.range k).image hpp.R) := by
  refine ⟨?_, ?_⟩
  · intro hRk0
    have : k = 0 := hpp.R_inj k 0 hkd (Nat.zero_le _) (by rw [hRk0, hpp.R_zero])
    omega
  · intro i' hi'_ne _hadj hcounts
    obtain ⟨m, hmd, hRm⟩ := hpp.R_surj i'
    rcases lt_trichotomy m k with hmk | hmk | hmk
    · exfalso
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · subst hm0
        exact hi'_ne (by rw [← hRm, hpp.R_zero])
      · have hc := hcounts (hpp.R (m - 1))
          (Finset.mem_image_of_mem hpp.R (Finset.mem_range.mpr (by omega)))
        rw [← hRm,
          hpp.tridiagonal (m - 1) k (by omega) hkd (Or.inl (by omega))] at hc
        exact hpp.subdiagonal m (by omega) (by omega) hc
    · rw [← hRm, hmk]
    · exfalso
      have hc := hcounts (hpp.R (k - 1))
        (Finset.mem_image_of_mem hpp.R (Finset.mem_range.mpr (by omega)))
      rw [← hRm,
        hpp.tridiagonal (k - 1) m (by omega) hmd (Or.inl (by omega))] at hc
      exact hpp.subdiagonal k (by omega) hkd hc.symm

/-- **EdgeGenerates for every P-polynomial scheme.** The distance ladder walks
out the isolation closure: by fixpoint induction, distance `R k` lands in the
closure once all closer distances do (its prefix pinning lifts to the fixpoint
via `IsoPinned.mono`), so the closure contains every relation. -/
theorem edgeGenerates_of_pPolynomial {n : Nat} (G : SchurianSchemeGraph n)
    (v : Fin n) (j0 : Fin (G.scheme.rank + 1)) (hpp : PPolynomial G v j0) :
    EdgeGenerates G v j0 := by
  classical
  have hseed : ({0, j0} : Finset (Fin (G.scheme.rank + 1))) ⊆ occursFromV G v := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | hxj
    · exact zero_mem_occursFromV G v
    · rw [hxj, ← hpp.R_one]; exact hpp.R_occurs 1 hpp.one_le_rank
  obtain ⟨k₀, hk₀le, hfix⟩ :=
    Saturation.exists_iterate_isFixed_within (isolationStep G v j0)
      (subset_isolationStep G v j0) (occursFromV G v) {0, j0} hseed
      (fun s hs => isolationStep_subset_occursFromV G v j0 hs)
  set F := (isolationStep G v j0)^[k₀] {0, j0} with hF
  have hseedF : ({0, j0} : Finset (Fin (G.scheme.rank + 1))) ⊆ F := by
    have hm := Saturation.iterate_mono (isolationStep G v j0)
      (subset_isolationStep G v j0) {0, j0} (Nat.zero_le k₀)
    rwa [Function.iterate_zero_apply] at hm
  have hmem : ∀ k, k ≤ G.scheme.rank → hpp.R k ∈ F := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hkd
      by_cases hk0 : k = 0
      · subst hk0; rw [hpp.R_zero]; exact hseedF (Finset.mem_insert_self _ _)
      · by_cases hk1 : k = 1
        · subst hk1; rw [hpp.R_one]
          exact hseedF (Finset.mem_insert_of_mem (Finset.mem_singleton_self j0))
        · have hpre : ((Finset.range k).image hpp.R) ⊆ F := by
            intro x hx
            rw [Finset.mem_image] at hx
            obtain ⟨a, ha, rfl⟩ := hx
            rw [Finset.mem_range] at ha
            exact ih a ha (by omega)
          have hpin : IsoPinned G j0 (hpp.R k) F :=
            (pPolynomial_pinned G v j0 hpp (by omega) hkd).mono hpre
          have hmemF : hpp.R k ∈ isolationStep G v j0 F :=
            (mem_isolationStep G v j0).mpr (Or.inr ⟨hpp.R_occurs k hkd, hpin⟩)
          rwa [hfix] at hmemF
  have hoccF : occursFromV G v ⊆ F := by
    intro l hl
    obtain ⟨m, hmd, hRm⟩ := hpp.R_surj l
    rw [← hRm]; exact hmem m hmd
  intro l hl
  have hlF : l ∈ F := hoccF hl
  rw [hF] at hlF
  exact Saturation.iterate_mono (isolationStep G v j0)
    (subset_isolationStep G v j0) {0, j0} (by omega) hlF

/-- **General convergence for the metric class — Theorem 2 for every
P-polynomial schurian scheme graph.** One theorem covering the entire
distance-regular family (cycles, Johnson, Hamming, all DRGs), with **no
per-scheme separation data**: the P-polynomial structure discharges
`EdgeGenerates`, which the convergence engine turns into orbit recovery. The
rank ladder is closed for the metric class. -/
theorem theorem_2_HOR_of_pPolynomial {n : Nat} {adj : AdjMatrix n}
    (h : IsSchurianSchemeGraph' adj) (P : PMatrix n) (v : Fin n)
    (j0 : Fin (h.G.scheme.rank + 1)) (hJ : h.G.toSchemeGraph.J = {j0})
    (hP_invariant : ∀ {π : Equiv.Perm (Fin n)}, IsAut π adj →
      ∀ x u, P (π x) (π u) = P x u)
    (hpp : PPolynomial h.G v j0) :
    ∀ w u : Fin n,
      OrbitPartition adj P {v} w u ↔
        warmRefine adj P (individualizedColouring n {v}) w =
          warmRefine adj P (individualizedColouring n {v}) u := by
  have hj0_nbr : ∃ w₀ : Fin n, h.G.scheme.relOfPair v w₀ = j0 := by
    have hocc := hpp.R_occurs 1 hpp.one_le_rank
    rw [hpp.R_one] at hocc
    exact (mem_occursFromV h.G v).mp hocc
  exact theorem_2_HOR_of_edgeGenerates h P v j0 hJ hP_invariant hj0_nbr
    (edgeGenerates_of_pPolynomial h.G v j0 hpp)

end ChainDescent
