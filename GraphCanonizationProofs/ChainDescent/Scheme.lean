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

end ChainDescent
