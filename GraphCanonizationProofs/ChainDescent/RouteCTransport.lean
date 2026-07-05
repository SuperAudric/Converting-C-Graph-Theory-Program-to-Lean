/-
# Route C — the cross-graph (scheme-iso) WL-transport toolkit.

This is the reusable substrate under Route C's seam (`RouteCSeam`). It packages the **cross-graph**
generalization of the landed single-graph refinement-transport tower (`ChainDescent.lean`:
`signature_transport` → … → `warmRefine_transport`, stated for an automorphism `IsAut g adj`).

The seam needs the two-adjacency case: `adj₁`, `adj₂` related by a graph iso `g` (`adj₂.adj (g v) (g w) =
adj₁.adj v w`) — exactly what `SchemeRealizes f S X` supplies (`adj₁ = schemeAdj S`, `adj₂ = schemeAdj X`,
`g = f`). `IsAut g adj` is the `adj₁ = adj₂ = adj` special case, so the `…_iso` siblings below are the landed
proofs verbatim with the single adjacency split into `adj₁`/`adj₂` and the one adjacency-reading hypothesis
`hg v u'` replaced by `hf v u'`; everything else (universe-filter reindexing, encode/sort, round induction) is
adjacency-independent and copies unchanged.

Contents:
* `SchemeRealizes` — a permutation realizes a scheme iso `S ≅ X` (preserves `schemeAdj`).
* three `samePartition` helpers (`warmRefine_congr_samePartition`, `mem_image_transport`,
  `indiv_samePartition_image`) — the partition-congruence machinery the base-pullback rides on.
* the five `…_transport_iso` lemmas (the cross-graph refinement tower).
* `separatesAtBoundedBase_transport` — the payoff: `SeparatesAtBoundedBase` is invariant along a scheme iso.
-/
import ChainDescent.Cascade

namespace ChainDescent

open scoped Classical

variable {n : Nat}

/-- A permutation `f` **realizes** the scheme iso `S ≅ X` if it preserves the labelled adjacency (`schemeAdj`).
By `isAut_schemeAdj_iff` this is exactly a relation-preserving bijection — the combinatorial scheme iso the
cited rank-3 classification supplies (the `AlgIso.InducedBy f` data). -/
def SchemeRealizes (f : Equiv.Perm (Fin n)) (S X : SchurianScheme n) : Prop :=
  ∀ v w, (schemeAdj S.toAssociationScheme).adj v w = (schemeAdj X.toAssociationScheme).adj (f v) (f w)

/-! ## `samePartition` helpers (distilled from the transport seam) -/

/-- **`warmRefine` is a `samePartition` congruence in its seed** (the `D = ∅` case of `warmRefine_agree_off'`):
refining two same-partition seed colourings yields same-partition results. The engine that lets the
base-transport pass through warm refinement. -/
theorem warmRefine_congr_samePartition {adj : AdjMatrix n} {P : PMatrix n} {χ χ' : Colouring n}
    (h : samePartition χ χ') :
    samePartition (warmRefine adj P χ) (warmRefine adj P χ') :=
  warmRefine_agree_off' adj P P χ χ' ∅ h (fun _ _ _ => rfl)
    (fun x hx => absurd hx (by simp))

/-- **Membership transport, general base.** `g i ∈ T.image g ↔ i ∈ T` (just injectivity of `g`). -/
theorem mem_image_transport {T : Finset (Fin n)} {g : Equiv.Perm (Fin n)} (i : Fin n) :
    g i ∈ T.image g ↔ i ∈ T := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨a, ha, hga⟩; rwa [g.injective hga] at ha
  · intro hi; exact ⟨i, hi, rfl⟩

/-- **Seed transport, general base.** The `T`-individualized seed and the `g`-pullback of the `g(T)`-individualized
seed induce the same partition: both are "singletons on the pinned set, one class elsewhere", and `g` matches the
pinned sets (`mem_image_transport`). The literal (index-based) labels differ, but the partition does not. -/
theorem indiv_samePartition_image {T : Finset (Fin n)} {g : Equiv.Perm (Fin n)} :
    samePartition (individualizedColouring n T)
      (fun v => individualizedColouring n (T.image g) (g v)) := by
  intro i j
  have hi := mem_image_transport (T := T) (g := g) i
  have hj := mem_image_transport (T := T) (g := g) j
  simp only [individualizedColouring]
  by_cases hI : i ∈ T <;> by_cases hJ : j ∈ T
  · rw [if_pos hI, if_pos hJ, if_pos (hi.mpr hI), if_pos (hj.mpr hJ)]
    simp only [add_left_inj, Fin.val_inj, EmbeddingLike.apply_eq_iff_eq]
  · rw [if_pos hI, if_neg hJ, if_pos (hi.mpr hI), if_neg (fun h => hJ (hj.mp h))]; simp
  · rw [if_neg hI, if_pos hJ, if_neg (fun h => hI (hi.mp h)), if_pos (hj.mpr hJ)]; simp
  · rw [if_neg hI, if_neg hJ, if_neg (fun h => hI (hi.mp h)), if_neg (fun h => hJ (hj.mp h))]

/-! ## The cross-graph refinement transport tower -/

section Iso
variable {adj₁ adj₂ : AdjMatrix n} {P₁ P₂ : PMatrix n} {χ₁ χ₂ : Colouring n} {g : Equiv.Perm (Fin n)}

/-- **`signature` cross-graph transport.** The root lemma: `g` carries `adj₁`'s neighbour signature at `v`
onto `adj₂`'s at `g v`. Mirrors `signature_transport`, replacing `IsAut g adj` by the iso condition `hf`. -/
theorem signature_transport_iso
    (hf : ∀ v w, adj₂.adj (g v) (g w) = adj₁.adj v w) (hP : ∀ v u, P₂ (g v) (g u) = P₁ v u)
    (hχ : ∀ v, χ₂ (g v) = χ₁ v) (v : Fin n) :
    signature adj₂ P₂ χ₂ (g v) = signature adj₁ P₁ χ₁ v := by
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
  exact Prod.mk.injEq .. |>.mpr ⟨hf v u', hP v u'⟩

/-- **`sigKey` cross-graph transport** — from `signature_transport_iso` and `χ₂ ∘ g = χ₁`. -/
theorem sigKey_transport_iso
    (hf : ∀ v w, adj₂.adj (g v) (g w) = adj₁.adj v w) (hP : ∀ v u, P₂ (g v) (g u) = P₁ v u)
    (hχ : ∀ v, χ₂ (g v) = χ₁ v) (v : Fin n) :
    sigKey adj₂ P₂ χ₂ (g v) = sigKey adj₁ P₁ χ₁ v := by
  unfold sigKey
  rw [hχ v, signature_transport_iso hf hP hχ v]

/-- **`refineStep` cross-graph transport** — one round. -/
theorem refineStep_transport_iso
    (hf : ∀ v w, adj₂.adj (g v) (g w) = adj₁.adj v w) (hP : ∀ v u, P₂ (g v) (g u) = P₁ v u)
    (hχ : ∀ v, χ₂ (g v) = χ₁ v) (v : Fin n) :
    refineStep adj₂ P₂ χ₂ (g v) = refineStep adj₁ P₁ χ₁ v := by
  show Encodable.encode (sigKey adj₂ P₂ χ₂ (g v))
     = Encodable.encode (sigKey adj₁ P₁ χ₁ v)
  rw [sigKey_transport_iso hf hP hχ v]

/-- **Iterated `refineStep` cross-graph transport.** As in the single-graph case, the `χ`-hypothesis
re-establishes itself each round (`refineStep_transport_iso`), so the induction carries it. -/
theorem iterate_refineStep_transport_iso
    (hf : ∀ v w, adj₂.adj (g v) (g w) = adj₁.adj v w) (hP : ∀ v u, P₂ (g v) (g u) = P₁ v u) :
    ∀ (k : Nat) {χ₁ χ₂ : Colouring n}, (∀ v, χ₂ (g v) = χ₁ v) →
      ∀ v, ((refineStep adj₂ P₂)^[k]) χ₂ (g v) = ((refineStep adj₁ P₁)^[k]) χ₁ v := by
  intro k
  induction k with
  | zero => intro χ₁ χ₂ hχ v; exact hχ v
  | succ k ih =>
    intro χ₁ χ₂ hχ v
    simp only [Function.iterate_succ, Function.comp_apply]
    exact ih (fun v' => refineStep_transport_iso hf hP hχ v') v

/-- **`warmRefine` cross-graph transport (the tower's deliverable).** For a graph iso `g` from `adj₁` to
`adj₂` (`hf`) with corresponding `P` (`hP`) and initial colouring (`hχ`), the whole `warmRefine` fixpoint
transports along `g`: `warmRefine adj₂ P₂ χ₂ (g v) = warmRefine adj₁ P₁ χ₁ v`. This is the single medium
lemma the `SeparatesAtBoundedBase` transport rides on. -/
theorem warmRefine_transport_iso
    (hf : ∀ v w, adj₂.adj (g v) (g w) = adj₁.adj v w) (hP : ∀ v u, P₂ (g v) (g u) = P₁ v u)
    (hχ : ∀ v, χ₂ (g v) = χ₁ v) (v : Fin n) :
    warmRefine adj₂ P₂ χ₂ (g v) = warmRefine adj₁ P₁ χ₁ v := by
  unfold warmRefine
  exact iterate_refineStep_transport_iso hf hP n hχ v

end Iso

/-! ## The payoff — `SeparatesAtBoundedBase` transports along a scheme iso -/

/-- **`SeparatesAtBoundedBase` is invariant under a scheme iso `S ≅ X` (`SchemeRealizes f`).** Given a bounded
base `S₀` discretising `X`, the pulled-back base `f⁻¹(S₀)` discretises `S`. Mechanism: with the colourings
`χ₂ = indiv S₀` (on `X`) and `χ₁ = indiv S₀ ∘ f` (on `S`), `warmRefine_transport_iso` gives
`warmRefine (schemeAdj X) χ₂ (f v) = warmRefine (schemeAdj S) χ₁ v`, so `Discrete` transfers through `f`
(injective); then `indiv_samePartition_image` + `warmRefine_congr_samePartition` bridge `χ₁` to the honest base
`indiv (f⁻¹ S₀)`. No `schemeEquiv`, no `StabilizerAt`/`ResidualAut`, no `IsCameronScheme` — the whole point of
transporting the light predicate. -/
theorem separatesAtBoundedBase_transport {S X : SchurianScheme n} {f : Equiv.Perm (Fin n)} {bound : Nat}
    (hreal : SchemeRealizes f S X) (hX : SeparatesAtBoundedBase X bound) :
    SeparatesAtBoundedBase S bound := by
  obtain ⟨S₀, hcard, hDisc⟩ := hX
  refine ⟨S₀.image f.symm, ?_, ?_⟩
  · rw [Finset.card_image_of_injective S₀ f.symm.injective]; exact hcard
  · have hf : ∀ v w, (schemeAdj X.toAssociationScheme).adj (f v) (f w)
        = (schemeAdj S.toAssociationScheme).adj v w := fun v w => (hreal v w).symm
    -- transport at the two individualized colourings (χ₂ = indiv S₀, χ₁ = indiv S₀ ∘ f; hP, hχ are rfl)
    have htrans : ∀ v, warmRefine (schemeAdj X.toAssociationScheme) (fun _ _ => POE.unknown)
            (individualizedColouring n S₀) (f v)
          = warmRefine (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown)
            (fun w => individualizedColouring n S₀ (f w)) v :=
      fun v => warmRefine_transport_iso hf (fun _ _ => rfl) (fun _ => rfl) v
    -- Discrete of the S-side pulled-back colouring, from hDisc + f injective
    have hDisc₁ : Discrete (warmRefine (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown)
        (fun w => individualizedColouring n S₀ (f w))) := by
      intro i j hij
      have hEq : warmRefine (schemeAdj X.toAssociationScheme) (fun _ _ => POE.unknown)
              (individualizedColouring n S₀) (f i)
            = warmRefine (schemeAdj X.toAssociationScheme) (fun _ _ => POE.unknown)
              (individualizedColouring n S₀) (f j) := by
        rw [htrans i, htrans j]; exact hij
      exact f.injective (hDisc _ _ hEq)
    -- bridge `indiv S₀ ∘ f` to the honest base `indiv (f⁻¹ S₀)` via samePartition
    have hset : (S₀.image (⇑f.symm)).image (⇑f) = S₀ := by
      rw [Finset.image_image, Equiv.self_comp_symm, Finset.image_id]
    have hsp : samePartition (individualizedColouring n (S₀.image (⇑f.symm)))
        (fun w => individualizedColouring n S₀ (f w)) := by
      have h := indiv_samePartition_image (T := S₀.image (⇑f.symm)) (g := f)
      simp only [hset] at h
      exact h
    exact Discrete.of_samePartition
      (warmRefine_congr_samePartition (adj := schemeAdj S.toAssociationScheme)
        (P := fun _ _ => POE.unknown) hsp).symm hDisc₁

end ChainDescent
