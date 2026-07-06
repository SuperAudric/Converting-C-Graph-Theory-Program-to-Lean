/-
# ChainDescent/OrbitRecovery.lean — §16–18 orbit recovery (split from `ChainDescent.lean`).
Tier-agnostic orbit-recovery infrastructure (`OrbitPartition`, `FixesPointwise`), Tier-1 CFI recovery
(`theorem_1_HOR`), Tier-2 schurian-scheme recovery (`theorem_2_HOR` / `SchemeProfile`). Imports `Spine`
(uses `IsAut`).
-/
import ChainDescent.Spine

namespace ChainDescent

/-! ## §16 — Orbit recovery: shared infrastructure

The orbit-recovery program ([`docs/chain-descent-orbit-recovery.md`](../docs/chain-descent-orbit-recovery.md))
states that for "nice enough" graphs, 1-WL refinement after sufficient
fresh-colour individualization recovers `Aut_S`-orbits. This section
develops the **tier-agnostic** machinery the program rests on:

- Fresh-colour individualization and the pointwise stabilizer predicate
  (§16.1).
- Automorphisms preserve refinement (§16.2). The key lifting lemma.
- The orbit partition predicate `OrbitPartition` and the **trivial
  direction** `orbits ⊆ 1-WL cells` (§16.3). Always true; the
  load-bearing half of the squeeze used by both tiers.

Tier-specific assemblies live downstream:
- §17 — Tier 1 (CFI graphs): squeeze via "warmRefine is discrete at the
  cascade depth" + Fact B (`aut_trivial_of_discrete_warmRefine`).
- §18 — Tier 2 (schurian scheme graphs): squeeze via "warmRefine equals
  the scheme profile partition at depth 1" + "profile partition equals
  Aut_v orbits".

The squeeze framing common to both tiers:
```
OrbitPartition ⊆ samePartition (warmRefine adj P χ_S) ⊆ TargetPartition
```
- §16.3 gives the left inclusion (always true).
- The right inclusion is tier-specific: discrete (Tier 1), or scheme
  profile partition (Tier 2). Combined with `OrbitPartition ⊇
  TargetPartition` (Fact B / Step 1 in the paper proofs), the squeeze
  yields equality.
-/

/-! ### §16.1 — Fresh-colour individualization and pointwise stabilizer -/

/-- **Fresh-colour individualization** of a vertex set `S`. Each `v ∈ S`
gets a unique colour `v.val + 1`; vertices outside `S` share colour `0`.
The `+1` keeps `0` reserved for the non-individualized cell. -/
def individualizedColouring (n : Nat) (S : Finset (Fin n)) : Colouring n :=
  fun v => if v ∈ S then v.val + 1 else 0

/-- A permutation `π` *fixes `S` pointwise* iff `π v = v` for every `v ∈ S`. -/
def FixesPointwise {n : Nat} (π : Equiv.Perm (Fin n)) (S : Finset (Fin n)) :
    Prop :=
  ∀ v ∈ S, π v = v

namespace FixesPointwise

variable {n : Nat} {π : Equiv.Perm (Fin n)} {S : Finset (Fin n)}

/-- A permutation fixing `S` pointwise also stabilizes the complement setwise.
For `v ∉ S`, we have `π v ∉ S` — otherwise `π (π v) = π v` (by pointwise
fix) forces `π v = v` by injectivity, contradicting `v ∉ S`. -/
theorem complement (hπ : FixesPointwise π S) {v : Fin n} (hv : v ∉ S) :
    π v ∉ S := by
  intro hπv
  have hfix : π (π v) = π v := hπ (π v) hπv
  have heq : π v = v := π.injective hfix
  exact hv (heq ▸ hπv)

end FixesPointwise

/-- An automorphism fixing `S` pointwise preserves the individualized
colouring `χ_S`: `χ_S (π v) = χ_S v` for every `v`. -/
theorem individualizedColouring_invariant {n : Nat} {S : Finset (Fin n)}
    {π : Equiv.Perm (Fin n)} (hπS : FixesPointwise π S) (v : Fin n) :
    individualizedColouring n S (π v) = individualizedColouring n S v := by
  unfold individualizedColouring
  by_cases hv : v ∈ S
  · rw [hπS v hv]
  · have hπv : π v ∉ S := hπS.complement hv
    simp [hv, hπv]

/-! ### §16.2 — Automorphisms preserve refinement -/

/-- An automorphism that preserves `(adj, P, χ)` pointwise preserves the
signature multiset for every vertex.

The proof reindexes the signature's underlying multiset along `π`: the
multiset over `u ≠ π v` of `(χ u, adj (π v) u, P (π v) u)` equals the
multiset over `u' ≠ v` of `(χ (π u'), adj (π v) (π u'), P (π v) (π u'))`,
which by the three invariance hypotheses equals the multiset over
`u' ≠ v` of `(χ u', adj v u', P v u')` = `signature adj P χ v`. -/
private theorem signature_invariant_of_isAut {n : Nat} {adj : AdjMatrix n}
    {P : PMatrix n} {χ : Colouring n} {π : Equiv.Perm (Fin n)}
    (hπ : IsAut π adj) (hP : ∀ v u, P (π v) (π u) = P v u)
    (hχ : ∀ v, χ (π v) = χ v) (v : Fin n) :
    signature adj P χ (π v) = signature adj P χ v := by
  unfold signature
  -- Reindex the filtered multiset along π: u ranges over `univ.filter (· ≠ π v)`
  -- iff `u = π u'` for u' ranging over `univ.filter (· ≠ v)`.
  have key : (Finset.univ : Finset (Fin n)).filter (· ≠ π v) =
      ((Finset.univ : Finset (Fin n)).filter (· ≠ v)).map π.toEmbedding := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
               Equiv.coe_toEmbedding]
    constructor
    · intro hu
      refine ⟨π.symm u, ?_, π.apply_symm_apply u⟩
      intro h
      apply hu
      rw [← h, π.apply_symm_apply]
    · rintro ⟨u', hu', rfl⟩
      intro h
      exact hu' (π.injective h)
  rw [key, Finset.map_val, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro u' _
  simp only [Function.comp_apply, Equiv.coe_toEmbedding]
  -- Show pointwise equality of the tuple `(χ (π u'), adj (π v) (π u'), P (π v) (π u'))`
  -- with `(χ u', adj v u', P v u')` via the three invariance hypotheses.
  refine Prod.mk.injEq .. |>.mpr ⟨hχ u', ?_⟩
  refine Prod.mk.injEq .. |>.mpr ⟨hπ v u', hP v u'⟩

/-- An automorphism that preserves `(adj, P, χ)` pointwise preserves
`refineStep`. Follows from signature invariance via `refineStep_iff`. -/
private theorem refineStep_invariant_of_isAut {n : Nat} {adj : AdjMatrix n}
    {P : PMatrix n} {χ : Colouring n} {π : Equiv.Perm (Fin n)}
    (hπ : IsAut π adj) (hP : ∀ v u, P (π v) (π u) = P v u)
    (hχ : ∀ v, χ (π v) = χ v) (v : Fin n) :
    refineStep adj P χ (π v) = refineStep adj P χ v := by
  -- Two vertices have the same refined colour iff (same old colour, same
  -- signature). For π v and v: old colours equal by hχ; signatures equal
  -- by signature_invariant_of_isAut. Hence refined colours equal.
  have hχπ : χ (π v) = χ v := hχ v
  have hσ : signature adj P χ (π v) = signature adj P χ v :=
    signature_invariant_of_isAut hπ hP hχ v
  exact ((refineStep_iff adj P χ (π v) v).mpr ⟨hχπ, hσ⟩)

/-- Iterating refinement preserves the invariance: `(refineStep)^[k] χ` is
also `π`-invariant when the inputs are. -/
private theorem iterate_refineStep_invariant_of_isAut {n : Nat} {adj : AdjMatrix n}
    {P : PMatrix n} {π : Equiv.Perm (Fin n)}
    (hπ : IsAut π adj) (hP : ∀ v u, P (π v) (π u) = P v u) :
    ∀ (k : Nat) {χ : Colouring n}, (∀ v, χ (π v) = χ v) →
      ∀ v, ((refineStep adj P)^[k]) χ (π v) = ((refineStep adj P)^[k]) χ v := by
  intro k
  induction k with
  | zero => intro χ hχ v; exact hχ v
  | succ k ih =>
    intro χ hχ v
    simp only [Function.iterate_succ, Function.comp_apply]
    -- Need to show invariance after one refineStep, then iterate ih on it.
    have hχ' : ∀ v, refineStep adj P χ (π v) = refineStep adj P χ v :=
      refineStep_invariant_of_isAut hπ hP hχ
    exact ih hχ' v

/-- Warm refinement preserves the invariance: if `(adj, P, χ_init)` are all
`π`-invariant (with `π` an automorphism), then `warmRefine adj P χ_init` is
also `π`-invariant. -/
theorem warmRefine_invariant_of_isAut {n : Nat} {adj : AdjMatrix n}
    {P : PMatrix n} {χ : Colouring n} {π : Equiv.Perm (Fin n)}
    (hπ : IsAut π adj) (hP : ∀ v u, P (π v) (π u) = P v u)
    (hχ : ∀ v, χ (π v) = χ v) (v : Fin n) :
    warmRefine adj P χ (π v) = warmRefine adj P χ v := by
  unfold warmRefine
  exact iterate_refineStep_invariant_of_isAut hπ hP n hχ v

/-! ### §16.2b — Cross-config transport under an automorphism

Now that `refineStep` is concrete, we can relate refinements of *two different*
`(P, χ)` configurations that an automorphism `g` carries onto one another — not
just the invariance of a single configuration (§16.2). If `g ∈ Aut(adj)` maps
config `(P₁, χ₁)` to `(P₂, χ₂)` — `P₂ (g·)(g·) = P₁` and `χ₂ ∘ g = χ₁` — then warm
refinement transports: `warmRefine adj P₂ χ₂ (g v) = warmRefine adj P₁ χ₁ v`. This
is the engine for `realizableFlip_of_cfi` (M1): the orbit automorphism that swaps a
decided pair carries the `σ`-branch refinement onto the flip-branch refinement, so
the two leaves coincide up to `g`. (Impossible against the old abstract `refineStep`
axiom, which fixed only the partition, not the colour values.) -/

/-- **Signature transport.** An automorphism `g` carrying `(P₁, χ₁)` to `(P₂, χ₂)`
maps the `(P₂, χ₂)`-signature at `g v` to the `(P₁, χ₁)`-signature at `v`.
Cross-config generalisation of `signature_invariant_of_isAut`. -/
theorem signature_transport {n : Nat} {adj : AdjMatrix n}
    {P₁ P₂ : PMatrix n} {χ₁ χ₂ : Colouring n} {g : Equiv.Perm (Fin n)}
    (hg : IsAut g adj) (hP : ∀ v u, P₂ (g v) (g u) = P₁ v u)
    (hχ : ∀ v, χ₂ (g v) = χ₁ v) (v : Fin n) :
    signature adj P₂ χ₂ (g v) = signature adj P₁ χ₁ v := by
  unfold signature
  have key : (Finset.univ : Finset (Fin n)).filter (· ≠ g v) =
      ((Finset.univ : Finset (Fin n)).filter (· ≠ v)).map g.toEmbedding := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
               Equiv.coe_toEmbedding]
    constructor
    · intro hu
      refine ⟨g.symm u, ?_, g.apply_symm_apply u⟩
      intro h; apply hu; rw [← h, g.apply_symm_apply]
    · rintro ⟨u', hu', rfl⟩
      intro h; exact hu' (g.injective h)
  rw [key, Finset.map_val, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro u' _
  simp only [Function.comp_apply, Equiv.coe_toEmbedding]
  refine Prod.mk.injEq .. |>.mpr ⟨hχ u', ?_⟩
  exact Prod.mk.injEq .. |>.mpr ⟨hg v u', hP v u'⟩

/-- **`sigKey` transport** — immediate from `signature_transport` and `χ₂ ∘ g = χ₁`. -/
theorem sigKey_transport {n : Nat} {adj : AdjMatrix n}
    {P₁ P₂ : PMatrix n} {χ₁ χ₂ : Colouring n} {g : Equiv.Perm (Fin n)}
    (hg : IsAut g adj) (hP : ∀ v u, P₂ (g v) (g u) = P₁ v u)
    (hχ : ∀ v, χ₂ (g v) = χ₁ v) (v : Fin n) :
    sigKey adj P₂ χ₂ (g v) = sigKey adj P₁ χ₁ v := by
  unfold sigKey
  rw [hχ v, signature_transport hg hP hχ v]

/-- **`refineStep` transport** — one round, cross-config. -/
theorem refineStep_transport {n : Nat} {adj : AdjMatrix n}
    {P₁ P₂ : PMatrix n} {χ₁ χ₂ : Colouring n} {g : Equiv.Perm (Fin n)}
    (hg : IsAut g adj) (hP : ∀ v u, P₂ (g v) (g u) = P₁ v u)
    (hχ : ∀ v, χ₂ (g v) = χ₁ v) (v : Fin n) :
    refineStep adj P₂ χ₂ (g v) = refineStep adj P₁ χ₁ v := by
  show Encodable.encode (sigKey adj P₂ χ₂ (g v))
     = Encodable.encode (sigKey adj P₁ χ₁ v)
  rw [sigKey_transport hg hP hχ v]

/-- **Iterated `refineStep` transport.** The `P`-hypothesis is fixed across rounds;
the `χ`-hypothesis re-establishes itself each round (`refineStep_transport` on the
once-refined colourings), so the induction carries it. -/
theorem iterate_refineStep_transport {n : Nat} {adj : AdjMatrix n}
    {P₁ P₂ : PMatrix n} {g : Equiv.Perm (Fin n)}
    (hg : IsAut g adj) (hP : ∀ v u, P₂ (g v) (g u) = P₁ v u) :
    ∀ (k : Nat) {χ₁ χ₂ : Colouring n}, (∀ v, χ₂ (g v) = χ₁ v) →
      ∀ v, ((refineStep adj P₂)^[k]) χ₂ (g v) = ((refineStep adj P₁)^[k]) χ₁ v := by
  intro k
  induction k with
  | zero => intro χ₁ χ₂ hχ v; exact hχ v
  | succ k ih =>
    intro χ₁ χ₂ hχ v
    simp only [Function.iterate_succ, Function.comp_apply]
    exact ih (fun v' => refineStep_transport hg hP hχ v') v

/-- **Warm-refinement transport.** An automorphism carrying `(P₁, χ₁)` to `(P₂, χ₂)`
carries the warm refinement of the first onto that of the second. The cross-config
form of `warmRefine_invariant_of_isAut`. -/
theorem warmRefine_transport {n : Nat} {adj : AdjMatrix n}
    {P₁ P₂ : PMatrix n} {χ₁ χ₂ : Colouring n} {g : Equiv.Perm (Fin n)}
    (hg : IsAut g adj) (hP : ∀ v u, P₂ (g v) (g u) = P₁ v u)
    (hχ : ∀ v, χ₂ (g v) = χ₁ v) (v : Fin n) :
    warmRefine adj P₂ χ₂ (g v) = warmRefine adj P₁ χ₁ v := by
  unfold warmRefine
  exact iterate_refineStep_transport hg hP n hχ v

/-! ### §16.3 — Orbit partition and the trivial direction

`OrbitPartition adj P S` is the equivalence relation on `Fin n` defined
by "some automorphism of `adj` preserving `P` and fixing `S` pointwise
maps `v` to `w`." It is the partition-level expression of "1-WL cells
contain Aut_S orbits."

The **trivial direction** (`OrbitPartition.subset_warmRefine`) says
this relation refines the 1-WL fixpoint partition: every Aut_S-orbit
lies inside a single 1-WL cell. This is always true and follows
directly from `warmRefine_invariant_of_isAut`. It is the load-bearing
half of the squeeze that both Tier 1 and Tier 2 use to conclude
"cells = orbits." -/

/-- **Aut_S orbit relation.** `v ~ w` iff some automorphism of `adj`
preserving `P` and fixing `S` pointwise maps `v` to `w`. -/
def OrbitPartition {n : Nat} (adj : AdjMatrix n) (P : PMatrix n)
    (S : Finset (Fin n)) (v w : Fin n) : Prop :=
  ∃ π : Equiv.Perm (Fin n),
    IsAut π adj ∧ (∀ x u, P (π x) (π u) = P x u) ∧
    FixesPointwise π S ∧ π v = w

namespace OrbitPartition

variable {n : Nat} {adj : AdjMatrix n} {P : PMatrix n} {S : Finset (Fin n)}

/-- Reflexivity: every vertex is in its own orbit (via the identity
permutation). -/
theorem refl (v : Fin n) : OrbitPartition adj P S v v :=
  ⟨Equiv.refl _, IsAut.refl, fun _ _ => rfl, fun _ _ => rfl, rfl⟩

/-- Symmetry: orbit equivalence is symmetric (via permutation inverse). -/
theorem symm {v w : Fin n} (h : OrbitPartition adj P S v w) :
    OrbitPartition adj P S w v := by
  obtain ⟨π, hπ, hP, hπS, hvw⟩ := h
  refine ⟨π.symm, hπ.symm, ?_, ?_, ?_⟩
  · intro x u
    have h := hP (π.symm x) (π.symm u)
    simp only [Equiv.apply_symm_apply] at h
    exact h.symm
  · intro v' hv'
    have hfix := hπS v' hv'
    -- π v' = v', so π.symm v' = v'.
    have := congrArg π.symm hfix
    simpa using this.symm
  · have := congrArg π.symm hvw
    simpa using this.symm

/-- Transitivity: orbit equivalence composes (via permutation composition). -/
theorem trans {v w u : Fin n}
    (h₁ : OrbitPartition adj P S v w) (h₂ : OrbitPartition adj P S w u) :
    OrbitPartition adj P S v u := by
  obtain ⟨π₁, hπ₁, hP₁, hπS₁, hvw⟩ := h₁
  obtain ⟨π₂, hπ₂, hP₂, hπS₂, hwu⟩ := h₂
  refine ⟨π₁.trans π₂, hπ₁.trans hπ₂, ?_, ?_, ?_⟩
  · intro x u'
    -- (π₁.trans π₂) x = π₂ (π₁ x)
    show P (π₂ (π₁ x)) (π₂ (π₁ u')) = P x u'
    rw [hP₂, hP₁]
  · intro v' hv'
    show π₂ (π₁ v') = v'
    rw [hπS₁ v' hv', hπS₂ v' hv']
  · show π₂ (π₁ v) = u
    rw [hvw]; exact hwu

/-- **The trivial direction: orbits refine 1-WL cells.** If `v` and `w` are
in the same Aut_S orbit, they share a cell in `warmRefine adj P χ_S`.

This is the always-true half of the squeeze. Both Tier 1 (CFI) and
Tier 2 (scheme graphs) combine this with a tier-specific bound on the
1-WL cells to conclude `OrbitPartition = warmRefine partition`. -/
theorem subset_warmRefine {v w : Fin n} (h : OrbitPartition adj P S v w) :
    warmRefine adj P (individualizedColouring n S) v =
      warmRefine adj P (individualizedColouring n S) w := by
  obtain ⟨π, hπ, hP, hπS, hvw⟩ := h
  have hχ : ∀ x, individualizedColouring n S (π x) = individualizedColouring n S x :=
    individualizedColouring_invariant hπS
  have hwarm := warmRefine_invariant_of_isAut hπ hP hχ v
  -- warmRefine ... (π v) = warmRefine ... v, and π v = w.
  rw [hvw] at hwarm
  exact hwarm.symm

end OrbitPartition

/-! ### §16.4 — Iteration helpers (tier-agnostic)

Two helpers for lifting per-round refineStep distinctions to
`warmRefine`. Pure properties of `refineStep_iff`; no CFI-specific
content. Used by both Tier 1's M4 cascade (`ChainDescent/CFI.lean`
§13.24) and the planned Tier 2 Step 2 induction. Originally introduced
inside `CFI.lean` for the OddDegree discharge; relocated here so both
tiers can use them without an explicit CFI import. -/

/-- **Refinement is split-only across iterations.** Equal at iterate
`k + d` implies equal at iterate `k`. Inductive engine: each
`refineStep` round can only split cells, never merge — so if two
vertices agree at a later iterate, they agreed at every earlier
iterate. -/
theorem refineStep_iter_le_eq {n : Nat} (adj : AdjMatrix n) (P : PMatrix n)
    (χ : Colouring n) (k d : Nat) {v w : Fin n}
    (h : ((refineStep adj P)^[k + d]) χ v =
         ((refineStep adj P)^[k + d]) χ w) :
    ((refineStep adj P)^[k]) χ v = ((refineStep adj P)^[k]) χ w := by
  induction d with
  | zero => exact h
  | succ d' ih =>
    apply ih
    have h' : ((refineStep adj P)^[k + d' + 1]) χ v =
              ((refineStep adj P)^[k + d' + 1]) χ w := by
      rw [show k + d' + 1 = k + (d' + 1) from by omega]; exact h
    rw [Function.iterate_succ_apply'] at h'
    exact ((refineStep_iff adj P _ _ _).mp h').1

/-- `warmRefine` equality implies iterate-r equality for any `r ≤ n`.
Combines the definition `warmRefine = iter[n]` with
`refineStep_iter_le_eq`; the bridge from "fixpoint partition" to
"any earlier-round partition." -/
theorem warmRefine_eq_iter_eq {n : Nat} (adj : AdjMatrix n) (P : PMatrix n)
    (χ : Colouring n) (r : Nat) (hr : r ≤ n) {v w : Fin n}
    (h : warmRefine adj P χ v = warmRefine adj P χ w) :
    ((refineStep adj P)^[r]) χ v = ((refineStep adj P)^[r]) χ w := by
  unfold warmRefine at h
  have h' : ((refineStep adj P)^[r + (n - r)]) χ v =
            ((refineStep adj P)^[r + (n - r)]) χ w := by
    have hcount : r + (n - r) = n := by omega
    rw [hcount]
    exact h
  exact refineStep_iter_le_eq adj P χ r (n - r) h'

/-! ## §17 — Tier 1: orbit recovery for CFI graphs

Formalisation of Theorem 1 of [`docs/chain-descent-orbit-recovery.md`](../docs/chain-descent-orbit-recovery.md):
for connected `CFI(H)`, 1-WL refinement after `≤ tw(H)` fresh-colour
individualizations recovers the `Aut(CFI(H))_S`-orbit partition.

**Proof structure** (orbit-recovery doc §5):
- **Fact A** — CFI cascade depth ≤ tw(H). Classical Cai-Fürer-Immerman
  1992. Requires CFI construction in Lean (a multi-week infrastructure
  project); stated here as an `axiom` placeholder so the assembly can
  proceed.
- **Fact B** — discrete partition ⟹ `Aut_S` is trivial ⟹ cells = orbits.
  Provable from §16's shared infrastructure.
- **Assembly** — at the cascade depth, partition is discrete (Fact A),
  so cells = orbits (Fact B + §16.3 trivial direction).

Sub-sections:
- §17.1 — Fact B (discrete ⟹ trivial Aut_S; cells = orbits)
- §17.2 — Fact A placeholder + Theorem 1 assembly
-/

/-! ### §17.1 — Fact B: discrete partition ⟹ trivial Aut_S -/

/-- **Fact B (pointwise version).** If a `π`-invariant colouring `χ` is
discrete (every cell singleton), then `π` is the identity. -/
theorem id_of_discrete_invariant {n : Nat} {χ : Colouring n}
    {π : Equiv.Perm (Fin n)} (hd : Discrete χ)
    (hχ : ∀ v, χ (π v) = χ v) :
    π = Equiv.refl (Fin n) := by
  apply Equiv.ext
  intro v
  -- χ (π v) = χ v, so by discreteness π v = v.
  exact hd (π v) v (hχ v)

/-- **Fact B (CFI version).** Let `adj`, `P` be a graph state and `S` an
individualized vertex set. If `warmRefine adj P χ_S` is discrete, then every
automorphism of `adj` that preserves `P` and fixes `S` pointwise is the
identity. -/
theorem aut_trivial_of_discrete_warmRefine {n : Nat} {adj : AdjMatrix n}
    {P : PMatrix n} {S : Finset (Fin n)}
    (hd : Discrete (warmRefine adj P (individualizedColouring n S)))
    {π : Equiv.Perm (Fin n)}
    (hπ : IsAut π adj) (hP : ∀ v u, P (π v) (π u) = P v u)
    (hπS : FixesPointwise π S) :
    π = Equiv.refl (Fin n) := by
  have hχ : ∀ v, individualizedColouring n S (π v) = individualizedColouring n S v :=
    individualizedColouring_invariant hπS
  have hwarm : ∀ v, warmRefine adj P (individualizedColouring n S) (π v) =
      warmRefine adj P (individualizedColouring n S) v :=
    warmRefine_invariant_of_isAut hπ hP hχ
  exact id_of_discrete_invariant hd hwarm

/-- **Fact B (partition version).** At discrete depth, the orbit partition
collapses to equality of vertices — the reverse direction of the squeeze.

If `warmRefine adj P χ_S` is discrete, then `OrbitPartition v w ↔ v = w`.
Combined with §16.3's trivial direction, this gives `OrbitPartition v w ↔
warmRefine ... v = warmRefine ... w` for the Tier 1 cascade-discrete case. -/
theorem orbit_iff_eq_of_discrete_warmRefine {n : Nat} {adj : AdjMatrix n}
    {P : PMatrix n} {S : Finset (Fin n)}
    (hd : Discrete (warmRefine adj P (individualizedColouring n S)))
    (v w : Fin n) :
    OrbitPartition adj P S v w ↔ v = w := by
  constructor
  · intro h
    obtain ⟨π, hπ, hP, hπS, hvw⟩ := h
    have hπ_id := aut_trivial_of_discrete_warmRefine hd hπ hP hπS
    rw [← hvw, hπ_id]
    rfl
  · rintro rfl
    exact OrbitPartition.refl v

/-! ### §17.2 — The `CascadesAt` predicate

The orbit-recovery program's Tier-1 hypothesis "warmRefine becomes
discrete after some `S`" is, on its own, **trivially true for every
graph** — take `S = univ`, every vertex gets a unique fresh colour, and
warm refinement preserves discreteness. So the existential statement
carries no CFI-specific content.

The interesting content is the **depth at which discreteness is
reached**. We make depth explicit as a parameter `k`:

> `CascadesAt adj P k` iff some `S` with `|S| ≤ k` yields a discrete
> warmRefine.

The orbit-recovery doc notes that **any polynomial bound on `|S|`
preserves polynomial runtime** for chain descent (Corollary 1) — so
the chain-descent polynomial argument only needs `CascadesAt adj P (p
n)` for some polynomial `p`. The classical CFI cascade content is
`|S| ≤ tw(H)`; we capture that abstractly in §17.4 below. -/

/-- **Cascade at depth `k`**: some `S` with `|S| ≤ k` makes `warmRefine`
discrete. Every graph satisfies `CascadesAt adj P n` trivially
(`cascadesAt_univ`); the interesting case is `k` polynomial in `n` and
strictly less than `n` for special families (CFI: `k ≤ tw(H)`). -/
def CascadesAt {n : Nat} (adj : AdjMatrix n) (P : PMatrix n) (k : Nat) : Prop :=
  ∃ S : Finset (Fin n),
    S.card ≤ k ∧
    Discrete (warmRefine adj P (individualizedColouring n S))

/-- **Trivial cascade at depth `n`.** Take `S = univ`: each vertex gets
a unique fresh colour `v.val + 1`, the initial colouring is discrete,
and warm refinement preserves discreteness. This is the "every-graph
fallback" — non-content in itself; the polynomial-depth claim is
non-trivial only when `k < n`. -/
theorem cascadesAt_univ {n : Nat} (adj : AdjMatrix n) (P : PMatrix n) :
    CascadesAt adj P n := by
  refine ⟨Finset.univ, ?_, ?_⟩
  · rw [Finset.card_univ, Fintype.card_fin]
  · apply Discrete.warmRefine_preserves
    intro i j hij
    -- individualizedColouring n univ assigns each v the colour v.val + 1.
    have hi : (i : Fin n) ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
    have hj : (j : Fin n) ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ j
    have hci : individualizedColouring n Finset.univ i = i.val + 1 := by
      simp [individualizedColouring, hi]
    have hcj : individualizedColouring n Finset.univ j = j.val + 1 := by
      simp [individualizedColouring, hj]
    rw [hci, hcj] at hij
    exact Fin.ext (Nat.succ_injective hij)

/-- Monotonicity: a cascade at depth `k` is a cascade at every depth `≥ k`. -/
private theorem CascadesAt.mono {n : Nat} {adj : AdjMatrix n} {P : PMatrix n}
    {k₁ k₂ : Nat} (hle : k₁ ≤ k₂) (h : CascadesAt adj P k₁) :
    CascadesAt adj P k₂ := by
  obtain ⟨S, hcard, hd⟩ := h
  exact ⟨S, Nat.le_trans hcard hle, hd⟩

/-! ### §17.3 — Theorem 1 (depth-parameterised, unconditional)

Given a cascade hypothesis at depth `k`, the squeeze argument
(§16.3 trivial direction + §17.1 Fact B) gives orbit recovery at
`|S| ≤ k`. No axioms beyond the standard `refineStep` basis — all
CFI specificity has been pushed into the `CascadesAt` hypothesis.

This is the structural Theorem 1. Tier-1 specialisations
(`theorem_1_HOR_at_n`, `theorem_1_HOR_cfi`) instantiate the cascade
hypothesis from different sources (trivial bound vs. CFI axiom). -/

/-- **Theorem 1 (depth-parametrised, unconditional).** If `adj`
cascades at depth `k`, the 1-WL fixpoint partition equals the Aut_S
orbit partition at some `S` with `|S| ≤ k`.

This is the load-bearing theorem of Tier 1. The CFI-specific
content lives in the cascade hypothesis. -/
theorem theorem_1_HOR_at_depth {n : Nat} {adj : AdjMatrix n}
    {P : PMatrix n} {k : Nat} (h : CascadesAt adj P k) :
    ∃ S : Finset (Fin n),
      S.card ≤ k ∧
      Discrete (warmRefine adj P (individualizedColouring n S)) ∧
      ∀ v w,
        OrbitPartition adj P S v w ↔
        warmRefine adj P (individualizedColouring n S) v =
          warmRefine adj P (individualizedColouring n S) w := by
  obtain ⟨S, hcard, hd⟩ := h
  refine ⟨S, hcard, hd, ?_⟩
  intro v w
  constructor
  · exact OrbitPartition.subset_warmRefine
  · intro hχ
    have hvw : v = w := hd v w hχ
    rw [hvw]
    exact OrbitPartition.refl w

/-! ### §17.4 — Specialisations of `theorem_1_HOR_at_depth`

The Tier-1 theorem in three structural forms, all axiom-free:
- **Trivial-bound form** (`theorem_1_HOR_at_n`): every graph admits
  orbit recovery at depth `n`. Useful as a smoke-test.
- **Legacy form** (`theorem_1_HOR`): existential, no depth bound.
  Corollary of `theorem_1_HOR_at_n`.
- **Pointwise form** (`theorem_1_HOR_pointwise`): Aut_S is trivial
  at the cascade depth.

The CFI-specific polynomial-depth form (`theorem_1_HOR_cfi`) and its
placeholder axioms (`IsCFI`, `cfi_depth_bound`,
`cfi_cascades_polynomially`) live in
[`ChainDescent/CFI.lean`](./ChainDescent/CFI.lean), where the
concrete `IsCFI'` predicate (built on `CFIBase` / `CFIVertex` /
`cfiAdj`) is used directly instead of an abstract Prop axiom.
Mirroring this for Tier 2 (`IsSchurianSchemeGraph` →
concrete-scheme-based predicate) is a follow-on once Tier 2's
analogue of `CFI.lean` lands. -/

/-- **Theorem 1, trivial-bound corollary.** Every graph admits orbit
recovery at depth `n`. Axiom-free; specialises
`theorem_1_HOR_at_depth` to the universal `cascadesAt_univ`. -/
theorem theorem_1_HOR_at_n {n : Nat} (adj : AdjMatrix n) (P : PMatrix n) :
    ∃ S : Finset (Fin n),
      S.card ≤ n ∧
      Discrete (warmRefine adj P (individualizedColouring n S)) ∧
      ∀ v w,
        OrbitPartition adj P S v w ↔
        warmRefine adj P (individualizedColouring n S) v =
          warmRefine adj P (individualizedColouring n S) w :=
  theorem_1_HOR_at_depth (cascadesAt_univ adj P)

/-- **Theorem 1 (legacy existential form).** No depth bound; some `S`
makes `warmRefine` discrete and orbits = cells. Axiom-free corollary
of `theorem_1_HOR_at_n`; kept for downstream use. -/
theorem theorem_1_HOR {n : Nat} (adj : AdjMatrix n) (P : PMatrix n) :
    ∃ S : Finset (Fin n),
      Discrete (warmRefine adj P (individualizedColouring n S)) ∧
      ∀ v w,
        OrbitPartition adj P S v w ↔
        warmRefine adj P (individualizedColouring n S) v =
          warmRefine adj P (individualizedColouring n S) w := by
  obtain ⟨S, _, hd, hpart⟩ := theorem_1_HOR_at_n adj P
  exact ⟨S, hd, hpart⟩

/-- **Theorem 1, pointwise corollary.** Aut_S is trivial at the cascade
depth. Axiom-free corollary of `theorem_1_HOR_at_n` +
`aut_trivial_of_discrete_warmRefine`. -/
theorem theorem_1_HOR_pointwise {n : Nat} (adj : AdjMatrix n) (P : PMatrix n) :
    ∃ S : Finset (Fin n),
      Discrete (warmRefine adj P (individualizedColouring n S)) ∧
      ∀ (π : Equiv.Perm (Fin n)),
        IsAut π adj → (∀ v u, P (π v) (π u) = P v u) →
        FixesPointwise π S → π = Equiv.refl (Fin n) := by
  obtain ⟨S, _, hd, _⟩ := theorem_1_HOR_at_n adj P
  refine ⟨S, hd, ?_⟩
  intro π hπ hP hπS
  exact aut_trivial_of_discrete_warmRefine hd hπ hP hπS

/-! ## §18 — Tier 2: orbit recovery for schurian scheme graphs

Formalisation of Theorem 2 of [`docs/chain-descent-orbit-recovery.md`](../docs/chain-descent-orbit-recovery.md):
for a graph admitting a vertex-transitive schurian association scheme,
1-WL refinement after a **single** fresh-colour individualization
recovers the `Aut_v`-orbit partition.

The paper proof (orbit-recovery doc §14.3) routes through:
- **Step 1** — schurian assumption ⟹ `Aut(G)_v` orbits = v-profile
  classes (scheme-relation classes relative to `v`).
- **Step 2** — 1-WL on `(G, v)` distinguishes v-profile classes (the
  intersection-number argument).
- **Step 3** — combine.

Lean structure mirrors Tier 1 (§17):
- §18.1 — `SchemeProfile` structure bundling Steps 1 and 2 as fields.
- §18.2 — Theorem 2 assembly (`theorem_2_HOR_of_profile`).

The full association-scheme machinery (relations `R_0,…,R_d`,
intersection numbers, the schurian property, and the `SchemeProfile`
existence) is now formalised concretely in `ChainDescent/Scheme.lean`
(the `AssociationScheme` / `SchurianSchemeGraph` structures,
`toSchemeProfile`, and the de-classed `theorem_2_HOR_of_pPolynomial`
covering the whole metric / distance-regular family). The earlier
placeholder axioms `IsSchurianSchemeGraph` /
`schurian_scheme_profile_exists` and the axiom-conditional unconditional
form `theorem_2_HOR` have therefore been **retired**; only the
axiom-free `SchemeProfile` bundle and the `theorem_2_HOR_of_profile`
assembly remain here, consumed by `Scheme.lean`'s
`theorem_2_HOR_concrete`.
-/

/-! ### §18.1 — `SchemeProfile`: the v-profile partition

A `SchemeProfile adj P v` is a colouring `profile : Colouring n`
that represents the **v-profile** (which scheme relation each w ≠ v
shares with v, relative to a fixed association scheme on `adj`),
together with two structural facts:

- **Step 1 field (`profile_iff_orbit`)**: profile classes coincide
  with Aut_v orbits. This is the schurian assumption's content —
  scheme-relation classes are exactly Aut-orbital classes.
- **Step 2 field (`warm_refines_profile`)**: 1-WL refinement on
  `(adj, P, χ_{v})` is at least as fine as the profile partition
  (i.e., cells ⊆ profile classes). This is the intersection-number
  argument.

The reverse inclusion (`profile classes ⊆ 1-WL cells`) follows
from §16.3's trivial direction plus the Step 1 field, so the
structure does not need to bundle it explicitly. Derived in
`SchemeProfile.warm_iff_profile`. -/
structure SchemeProfile {n : Nat} (adj : AdjMatrix n) (P : PMatrix n)
    (v : Fin n) where
  /-- The v-profile colouring: encodes which scheme relation each w
  shares with v. -/
  profile : Colouring n
  /-- `v` is a singleton in the profile partition. -/
  v_singleton : ∀ w, w ≠ v → profile w ≠ profile v
  /-- **Step 1 (schurian).** Profile classes equal Aut_v orbits. -/
  profile_iff_orbit :
    ∀ w u, profile w = profile u ↔ OrbitPartition adj P {v} w u
  /-- **Step 2 (intersection numbers).** 1-WL on (adj, P, χ_{v}) refines
  the profile partition. -/
  warm_refines_profile :
    ∀ w u,
      warmRefine adj P (individualizedColouring n {v}) w =
        warmRefine adj P (individualizedColouring n {v}) u →
      profile w = profile u

namespace SchemeProfile

variable {n : Nat} {adj : AdjMatrix n} {P : PMatrix n} {v : Fin n}

/-- **Squeeze: 1-WL fixpoint partition equals profile partition.**

The "←" direction comes from §16.3's trivial direction (orbits refine
1-WL cells) composed with Step 1 (orbits = profile classes). The "→"
direction is the Step 2 field directly. -/
theorem warm_iff_profile (sp : SchemeProfile adj P v) (w u : Fin n) :
    warmRefine adj P (individualizedColouring n {v}) w =
      warmRefine adj P (individualizedColouring n {v}) u ↔
    sp.profile w = sp.profile u := by
  constructor
  · exact sp.warm_refines_profile w u
  · intro h
    have horb := (sp.profile_iff_orbit w u).mp h
    exact OrbitPartition.subset_warmRefine horb

end SchemeProfile

/-! ### §18.2 — Theorem 2 assembly

`theorem_2_HOR_of_profile` turns a `SchemeProfile` witness into the
depth-1 orbit-recovery equality. The witness itself is produced
concretely in `ChainDescent/Scheme.lean` (`toSchemeProfile`, built
from a `SchurianSchemeGraph` plus a Step-2 discharge), so the former
placeholder axioms (`IsSchurianSchemeGraph`,
`schurian_scheme_profile_exists`) and the axiom-conditional
unconditional form (`theorem_2_HOR`) have been retired. This assembly
lemma is axiom-clean and is the bridge `Scheme.lean`'s
`theorem_2_HOR_concrete` calls. -/

/-- **Theorem 2 (HOR for schurian scheme graphs), assembly form.**

Given a SchemeProfile witness at vertex `v`, the 1-WL fixpoint
partition (at depth 1) equals the Aut_v orbit partition.

This is the assembly version — the actual content is the existence
of a SchemeProfile (`schurian_scheme_profile_exists`). Once we have a
witness, the equality follows from chaining the two iff-fields. -/
theorem theorem_2_HOR_of_profile {n : Nat} {adj : AdjMatrix n}
    {P : PMatrix n} {v : Fin n} (sp : SchemeProfile adj P v)
    (w u : Fin n) :
    OrbitPartition adj P {v} w u ↔
      warmRefine adj P (individualizedColouring n {v}) w =
        warmRefine adj P (individualizedColouring n {v}) u :=
  -- OrbitPartition ↔ profile (Step 1 backwards), then profile ↔ warmRefine
  -- (sp.warm_iff_profile backwards).
  (sp.profile_iff_orbit w u).symm.trans (sp.warm_iff_profile w u).symm

end ChainDescent
