/-
# L1 STEP 1 — cross-graph (iso) transport of the WL refinement tower.

The landed transport tower (`ChainDescent.lean`: `signature_transport` → `sigKey_transport` →
`refineStep_transport` → `iterate_refineStep_transport` → `warmRefine_transport`) is stated for `g` an
**automorphism of a single `adj`** (`IsAut g adj`, i.e. `adj.adj (g v) (g w) = adj.adj v w`). The seam's
`htransport` needs the **cross-graph** case: two adjacencies `adj₁`, `adj₂` related by a graph iso `g`
(`adj₂.adj (g v) (g w) = adj₁.adj v w`) — exactly what `SchemeRealizes f S X` supplies (`adj₁ = schemeAdj S`,
`adj₂ = schemeAdj X`, `g = f`). `IsAut g adj` is the `adj₁ = adj₂ = adj` special case.

These `…_iso` siblings are the landed proofs verbatim, with the single adjacency `adj` split into
`adj₁`/`adj₂` and the one adjacency-reading hypothesis `hg v u'` (`adj.adj (g v) (g u') = adj.adj v u'`)
replaced by `hf v u'` (`adj₂.adj (g v) (g u') = adj₁.adj v u'`). Everything else (the universe-filter
reindexing, the encode/sort, the round induction) is adjacency-independent, so it copies unchanged.

NOT in build (scratch; `lake env lean ChainDescent/ScratchSeamTransport.lean`).
-/
import ChainDescent.ScratchSeam            -- SchemeRealizes / SealDisj (+ CascadeAffine transitively)
import ChainDescent.ScratchNodeCountBridge  -- indiv_samePartition_image / warmRefine_congr_samePartition

namespace ChainDescent

open NodeCountBridge   -- indiv_samePartition_image / warmRefine_congr_samePartition

variable {n : Nat} {adj₁ adj₂ : AdjMatrix n}
  {P₁ P₂ : PMatrix n} {χ₁ χ₂ : Colouring n} {g : Equiv.Perm (Fin n)}

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

/-- **`warmRefine` cross-graph transport (the step-1 deliverable).** For a graph iso `g` from `adj₁` to
`adj₂` (`hf`) with corresponding `P` (`hP`) and initial colouring (`hχ`), the whole `warmRefine` fixpoint
transports along `g`: `warmRefine adj₂ P₂ χ₂ (g v) = warmRefine adj₁ P₁ χ₁ v`. This is the single
medium lemma the `SeparatesAtBoundedBase` transport (step 2) rides on. -/
theorem warmRefine_transport_iso
    (hf : ∀ v w, adj₂.adj (g v) (g w) = adj₁.adj v w) (hP : ∀ v u, P₂ (g v) (g u) = P₁ v u)
    (hχ : ∀ v, χ₂ (g v) = χ₁ v) (v : Fin n) :
    warmRefine adj₂ P₂ χ₂ (g v) = warmRefine adj₁ P₁ χ₁ v := by
  unfold warmRefine
  exact iterate_refineStep_transport_iso hf hP n hχ v

/-! ## Step 2 — `SeparatesAtBoundedBase` transports along a scheme iso -/

/-- **Step 2 (the L1 payoff).** `SeparatesAtBoundedBase` is invariant under a scheme iso `S ≅ X` (`SchemeRealizes
f`). Given a bounded base `S₀` discretising `X`, the pulled-back base `f⁻¹(S₀)` discretises `S`. Mechanism: with the
colourings `χ₂ = indiv S₀` (on `X`) and `χ₁ = indiv S₀ ∘ f` (on `S`), `warmRefine_transport_iso` (step 1) gives
`warmRefine (schemeAdj X) χ₂ (f v) = warmRefine (schemeAdj S) χ₁ v`, so `Discrete` transfers through `f` (injective);
then `indiv_samePartition_image` + `warmRefine_congr_samePartition` bridge `χ₁` to the honest base `indiv (f⁻¹ S₀)`.
No `schemeEquiv`, no `StabilizerAt`/`ResidualAut`, no `IsCameronScheme` — the whole point of transporting the light
predicate. -/
theorem separatesAtBoundedBase_transport {S X : SchurianScheme n} {f : Equiv.Perm (Fin n)} {bound : Nat}
    (hreal : SchemeRealizes f S X) (hX : SeparatesAtBoundedBase X bound) :
    SeparatesAtBoundedBase S bound := by
  obtain ⟨S₀, hcard, hDisc⟩ := hX
  refine ⟨S₀.image f.symm, ?_, ?_⟩
  · rw [Finset.card_image_of_injective S₀ f.symm.injective]; exact hcard
  · have hf : ∀ v w, (schemeAdj X.toAssociationScheme).adj (f v) (f w)
        = (schemeAdj S.toAssociationScheme).adj v w := fun v w => (hreal v w).symm
    -- step 1 at the two individualized colourings (χ₂ = indiv S₀, χ₁ = indiv S₀ ∘ f; hP, hχ are rfl)
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

/-! ## Steps 3 + 4 — the Cameron-free producer, and the seam with `htransport` proved -/

section Rank3Affine
variable {p d : ℕ} [Fact p.Prime]

/-- **Step 3 — the Cameron-free `SeparatesAtBoundedBase` producer (extracted).** The forms-graph chain's own
Cameron-free content, lifted out of `reachesRigidOrCameron_viaSymmetryBrokenBase`'s body *before* the
`Or.inl (Or.inr …)` disjunction padding: `IsotropySeparatesAtBase Q T` (+ bounded `T`) gives a bounded base
that discretises the affine-polar similitude scheme. Verbatim the witness that body feeds to `viaSpielman`. -/
theorem separatesAtBoundedBase_affinePolar
    (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    (T : Finset (Fin (p ^ d))) {bound : Nat} (hcard : T.card ≤ bound)
    (hIso : IsotropySeparatesAtBase Q T) :
    SeparatesAtBoundedBase (affineScheme (similitudeGroup Q) (neg_mem_similitudeGroup Q)) bound :=
  ⟨T, hcard,
    discrete_affineScheme_of_twoRoundDiffSeparates (similitudeGroup Q) (neg_mem_similitudeGroup Q) (T := T)
      (separatesAtBase_of_isotropySeparates_weak Q (relationRefinesIsotropy_similitude Q) hIso)⟩

/-- **Step 4 — the seam, `htransport` PROVED (not carried).** Replaces `ScratchSeam`'s
`reachesRigidOrCameron_viaSchurianRank3Affine`, whose `htransport` hypothesis and `IsCameronScheme`-invariance
premise are both eliminated. Forms-graph branch: extract the Cameron-free `SeparatesAtBoundedBase` on the concrete
`affineScheme(Q)` (step 3), transport it to `S` (step 2), then `viaSpielman` on `S` gives `SealDisj S` directly —
so only the single `SchemeRecoveredByDepth` disjunct is ever transported (via the light `SeparatesAtBoundedBase`),
never `SchemeBlockRecovered`/`schemeEquiv` or `IsCameronScheme`. Cameron branch: `Or.inr` directly on `S`. -/
theorem reachesRigidOrCameron_viaSchurianRank3Affine_proved
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop} {bound : Nat}
    (S : SchurianScheme (p ^ d))
    (hclass : IsCameronScheme (p ^ d) S ∨
        ∃ (Q : QuadraticForm (ZMod p) (Fin d → ZMod p)) (T : Finset (Fin (p ^ d)))
          (f : Equiv.Perm (Fin (p ^ d))),
          T.card ≤ bound ∧ IsotropySeparatesAtBase Q T ∧
          SchemeRealizes f S (affineScheme (similitudeGroup Q) (neg_mem_similitudeGroup Q))) :
    SealDisj IsCameronScheme bound S := by
  rcases hclass with hcam | ⟨Q, T, f, hT, hIso, hreal⟩
  · exact Or.inr hcam
  · exact reachesRigidOrCameron_viaSpielman S
      (separatesAtBoundedBase_transport hreal (separatesAtBoundedBase_affinePolar Q T hT hIso))

end Rank3Affine

-- Axiom check (expect `[propext, Classical.choice, Quot.sound]`).
#print axioms warmRefine_transport_iso
#print axioms separatesAtBoundedBase_transport
#print axioms reachesRigidOrCameron_viaSchurianRank3Affine_proved

end ChainDescent
