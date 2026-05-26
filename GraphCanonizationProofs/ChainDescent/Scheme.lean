import ChainDescent
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card

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

end ChainDescent
