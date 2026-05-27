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
theorem individualizedColouring_singleton_eq_v_iff {n : Nat} (v u : Fin n) :
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

Noncomputable because `refineStep` is axiomatised. -/
noncomputable def iterSignature {n : Nat} (adj : AdjMatrix n) (P : PMatrix n)
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
theorem signature_count_eq_card {n : Nat} (adj : AdjMatrix n) (P : PMatrix n)
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
theorem signature_eq_card_eq {n : Nat} (adj : AdjMatrix n) (P : PMatrix n)
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
theorem iter_succ_count_eq {n : Nat} (adj : AdjMatrix n) (P : PMatrix n)
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
theorem signature_countP_eq_card {n : Nat} (adj : AdjMatrix n) (P : PMatrix n)
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
theorem signature_eq_countP_eq {n : Nat} (adj : AdjMatrix n) (P : PMatrix n)
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
theorem iter_succ_countP_eq {n : Nat} (adj : AdjMatrix n) (P : PMatrix n)
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
theorem iter_succ_colour_count_eq {n : Nat} (adj : AdjMatrix n) (P : PMatrix n)
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

end ChainDescent
