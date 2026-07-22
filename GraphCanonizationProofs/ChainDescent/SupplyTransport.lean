import ChainDescent.Residue
import ChainDescent.MatchSupply
import Mathlib.Tactic.Group

/-!
# `P1` — the supply's transport obligation, and the FLAG's iso-invariance

## The hole this closes

`Residue.guarded_mixed_canonizer` — the `①` capstone for the **mixed** object — carries a hypothesis
`hse : Stall.StallEquivariant (forceThenConsume key S)`, and **until this file, nothing discharged it for any
supply.** The docs asserted it was "free for a structural supply"; that was prose, not a theorem, so the mixed
canonizer had *no instance at all*. Meanwhile `Regression.lean` §6 `#guard`s a genuine **counterexample** (the
fixed-generator `dihSupply` makes `C₅` answer and `σ·C₅` flag), so the hypothesis is emphatically not free.

## Why the flag needs it and soundness does not

`consume`'s headline is that the supply is **untrusted** — `consume_canonizer` holds for *every* supply — because
a covering resolver is **value**-invisible (`canonForm?_eq_deferAll_of_covering`). **A flag is not
value-invisible.** `Stall.stalled` reads the narrowing's *length*, which depends on how many orbits the supply's
generators actually **prove**. A supply that is good on `G` and junk on `σ·G` makes `G` answer and `σ·G` flag —
and then `①c` is **false**.

## The shape of the proof

The narrowing is `((forcedSet key adj χ).map (rep (verified S adj χ))).dedup`, and `rep` is a **least-index**
choice — emphatically *not* equivariant, and deliberately so (orbit members are indistinguishable to refinement,
so no canonical choice exists). So the length cannot be shown invariant by transporting `rep`.

It is invariant because the length **counts orbits**. That is exactly `Consume.rep_eq_iff_wordReach` (§9 of
`Consume.lean`): two branches share a representative **iff** the verified generators connect them. The `←` half
was already there (`rep_eq_of_wordReach`); the `→` half — *consume merges nothing more than the orbit* — is what
this argument needs, and it is what a merely-*sound* `rep` could never give.

So: orbits transport (`wordReach_conj_iff`, given `SupplyEquivariant`), the forced set transports
(`Composite.narrowFnEquivariant_forcedSet`, given `KeyEquivariant`), hence the orbit **count** transports, hence
the length does — with the non-equivariant `rep` never needing to transport at all.

## What a supply must now discharge

`GensEquivariant` — *the supply hands back the `σ`-conjugates on the relabelled graph*. This is **free for any
supply that is a structural function of `(adj, χ)`** and is exactly what an accumulating, history-dependent supply
(the C# harness's global `PermutationGroup`) **cannot** satisfy. It is therefore a real design constraint on the
cascade/stabilizer-chain supply to come, not a formality: **the Lean supply must be stateless.**
-/

namespace ChainDescent
namespace SupplyTransport

open ChainDescent.CostModel (CostM)
open ChainDescent.Descend
open ChainDescent.Force (Key KeyEquivariant)
open ChainDescent.Consume (Supply gens verified rep WordReach IsColAut)
open ChainDescent.Composite (forceThenConsume forcedSet)
open ChainDescent.Stall (StallEquivariant)

variable {n : Nat}

/-! ## 1. Counting distinct values of a map over a list -/

/-- The deduplicated image of a list is its `Finset` image. (Both count *distinct values*.) -/
theorem dedup_map_length_eq_card_image (L : List (Fin n)) (f : Fin n → Fin n) :
    ((L.map f).dedup).length = (L.toFinset.image f).card := by
  rw [← List.toFinset_card_of_nodup (List.nodup_dedup (L.map f))]
  congr 1
  ext x
  simp [List.mem_toFinset, List.mem_dedup]

/-- **★ THE COUNTING LEMMA.** Two maps that induce the **same fibres** on `s` have images of the same size — even
when neither map is expressible in terms of the other. This is what lets a *non-equivariant* representative
choice still produce an *invariant* count. -/
theorem card_image_congr_of_iff {s : Finset (Fin n)} {f g : Fin n → Fin n}
    (h : ∀ a ∈ s, ∀ b ∈ s, (f a = f b ↔ g a = g b)) :
    (s.image f).card = (s.image g).card := by
  classical
  refine Finset.card_bij (fun x hx => g (Finset.mem_image.mp hx).choose) ?_ ?_ ?_
  · intro a ha
    obtain ⟨hmem, _⟩ := (Finset.mem_image.mp ha).choose_spec
    exact Finset.mem_image.mpr ⟨_, hmem, rfl⟩
  · intro a ha b hb hab
    obtain ⟨hma, hfa⟩ := (Finset.mem_image.mp ha).choose_spec
    obtain ⟨hmb, hfb⟩ := (Finset.mem_image.mp hb).choose_spec
    rw [← hfa, ← hfb]
    exact (h _ hma _ hmb).mpr hab
  · intro y hy
    obtain ⟨b, hb, hgb⟩ := Finset.mem_image.mp hy
    have hfb : f b ∈ s.image f := Finset.mem_image.mpr ⟨b, hb, rfl⟩
    refine ⟨f b, hfb, ?_⟩
    obtain ⟨hma, hfa⟩ := (Finset.mem_image.mp hfb).choose_spec
    rw [← hgb]
    exact (h _ hma _ hb).mp hfa

/-! ## 2. The supply's transport obligation -/

/-- **The supply's raw generators transport.** On the relabelled graph the supply hands back exactly the
`σ`-conjugates of what it hands back here. Free for any supply that is a **structural function of `(adj, χ)`**;
provably false for a supply carrying a fixed generator list (the demo `dihSupply` — see `Regression.lean` §6). -/
def GensEquivariant (S : Supply n) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n) (g : Equiv.Perm (Fin n)),
    g ∈ gens S (relabelAdj σ adj) (transportColouring σ χ) ↔
      ∃ h ∈ gens S adj χ, g = σ * h * σ⁻¹

/-- The same condition on the **verified** list — the only thing the resolver ever reads. -/
def SupplyEquivariant (S : Supply n) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n) (g : Equiv.Perm (Fin n)),
    g ∈ verified S (relabelAdj σ adj) (transportColouring σ χ) ↔
      ∃ h ∈ verified S adj χ, g = σ * h * σ⁻¹

/-- Verification commutes with conjugation (`Consume.isColAut_conj_iff`), so an equivariant *supply* yields an
equivariant *verified* list. This is the form an instance should discharge. -/
theorem supplyEquivariant_of_gensEquivariant {S : Supply n} (h : GensEquivariant S) :
    SupplyEquivariant S := by
  intro σ adj χ g
  constructor
  · intro hg
    obtain ⟨hgen, hchk⟩ := List.mem_filter.mp hg
    obtain ⟨k, hk, rfl⟩ := (h σ adj χ g).mp hgen
    refine ⟨k, List.mem_filter.mpr ⟨hk, ?_⟩, rfl⟩
    exact decide_eq_true ((Consume.isColAut_conj_iff σ).mp (of_decide_eq_true hchk))
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨hgen, hchk⟩ := List.mem_filter.mp hk
    refine List.mem_filter.mpr ⟨(h σ adj χ _).mpr ⟨k, hgen, rfl⟩, ?_⟩
    exact decide_eq_true ((Consume.isColAut_conj_iff σ).mpr (of_decide_eq_true hchk))

/-! ## 3. Orbits transport -/

/-- The conjugation relation, read backwards. -/
theorem conj_symm {G G' : List (Equiv.Perm (Fin n))} {σ : Equiv.Perm (Fin n)}
    (hG : ∀ g, g ∈ G' ↔ ∃ h ∈ G, g = σ * h * σ⁻¹) :
    ∀ g, g ∈ G ↔ ∃ h ∈ G', g = σ⁻¹ * h * σ := by
  intro g
  constructor
  · exact fun hg => ⟨σ * g * σ⁻¹, (hG _).mpr ⟨g, hg, rfl⟩, by group⟩
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨k, hk, hkh⟩ := (hG h).mp hh
    have hek : σ⁻¹ * h * σ = k := by rw [hkh]; group
    rw [hek]; exact hk

/-- A word in `G` becomes the conjugate word in `G'`. -/
theorem wordReach_conj {G G' : List (Equiv.Perm (Fin n))} {σ : Equiv.Perm (Fin n)}
    (hG : ∀ g, g ∈ G' ↔ ∃ h ∈ G, g = σ * h * σ⁻¹) {u w : Fin n}
    (h : WordReach G u w) : WordReach G' (σ u) (σ w) := by
  induction h with
  | refl => exact Consume.WordReach.refl (σ u)
  | @step m _ g hg ih =>
      have hmem : σ * g * σ⁻¹ ∈ G' := (hG _).mpr ⟨g, hg, rfl⟩
      have hstep := ih.step hmem
      have happ : (σ * g * σ⁻¹) (σ m) = σ (g m) := by
        show σ (g (σ.symm (σ m))) = σ (g m)
        rw [Equiv.symm_apply_apply]
      rwa [happ] at hstep

/-- **★ ORBITS TRANSPORT.** The verified generators on `σ·G` connect `σ u` to `σ w` **iff** the originals connect
`u` to `w`. The orbit *partition* of the branch cell is therefore a genuine isomorphism invariant, even though the
representative chosen from each orbit is not. -/
theorem wordReach_conj_iff {G G' : List (Equiv.Perm (Fin n))} {σ : Equiv.Perm (Fin n)}
    (hG : ∀ g, g ∈ G' ↔ ∃ h ∈ G, g = σ * h * σ⁻¹) {u w : Fin n} :
    WordReach G' (σ u) (σ w) ↔ WordReach G u w := by
  refine ⟨fun h => ?_, wordReach_conj hG⟩
  have hsym : ∀ g, g ∈ G ↔ ∃ k ∈ G', g = σ⁻¹ * k * (σ⁻¹)⁻¹ := by
    simpa using conj_symm hG
  simpa using wordReach_conj hsym h

/-! ## 4. ★★★ THE PAYOFF — `StallEquivariant`, discharged -/

/-- **★★★ AN EQUIVARIANT SUPPLY MAKES THE FLAG ISO-INVARIANT.**

The `hse` hypothesis of `Residue.guarded_mixed_canonizer` — carried since `Stall.lean` was written and never
instantiated — is discharged from `KeyEquivariant` + `SupplyEquivariant`.

The proof never transports `rep`. It transports the **orbit partition** (`wordReach_conj_iff`) and the **forced
set** (`narrowFnEquivariant_forcedSet`), and then observes that the narrowing's length is the number of *distinct
representatives*, which by `Consume.rep_eq_iff_wordReach` is the number of **orbits meeting the forced set** — a
count both transports carry. -/
theorem stallEquivariant_forceThenConsume {key : Key n} (hk : KeyEquivariant key)
    {S : Supply n} (hS : SupplyEquivariant S) :
    StallEquivariant (forceThenConsume key S) := by
  intro σ adj χ
  rw [Composite.narrow_forceThenConsume, Composite.narrow_forceThenConsume]
  have hmemG' : ∀ g, g ∈ verified S (relabelAdj σ adj) (transportColouring σ χ) ↔
      ∃ h ∈ verified S adj χ, g = σ * h * σ⁻¹ := fun g => hS σ adj χ g
  have hperm : (forcedSet key (relabelAdj σ adj) (transportColouring σ χ)).Perm
      ((forcedSet key adj χ).map σ) := Composite.narrowFnEquivariant_forcedSet hk σ adj χ
  have hFin : (forcedSet key (relabelAdj σ adj) (transportColouring σ χ)).toFinset
      = (forcedSet key adj χ).toFinset.image σ := by
    ext x
    simp only [List.mem_toFinset, Finset.mem_image]
    rw [hperm.mem_iff]
    simp [List.mem_map]
  rw [dedup_map_length_eq_card_image, dedup_map_length_eq_card_image, hFin, Finset.image_image]
  refine card_image_congr_of_iff ?_
  intro a _ b _
  show rep (verified S (relabelAdj σ adj) (transportColouring σ χ)) (σ a)
      = rep (verified S (relabelAdj σ adj) (transportColouring σ χ)) (σ b)
    ↔ rep (verified S adj χ) a = rep (verified S adj χ) b
  rw [Consume.rep_eq_iff_wordReach, Consume.rep_eq_iff_wordReach]
  exact wordReach_conj_iff hmemG'

/-- **★★ `StallEquivariant` FROM BRANCH-ORBIT TRANSPORT — no `SupplyEquivariant` needed.** The narrowing reads the
supply only through `rep` on `forcedSet ⊆ branches`, and `rep` there depends only on the branch-orbit relation. So a
supply whose **branch-orbit relation transports** (even one whose generator *list* does NOT σ-conjugate — e.g. a
greedy-pick supply) still has an equivariant flag. This is the reference-free route to `①c`: prove the branch orbits
equal the (equivariant) `IsColAut`-orbits and feed the transport `↔` here directly. -/
theorem stallEquivariant_forceThenConsume_of_branchOrbitTransport {key : Key n} (hk : KeyEquivariant key)
    {S : Supply n}
    (horb : ∀ (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n) (a b : Fin n),
      a ∈ Descend.branches χ → b ∈ Descend.branches χ →
      (Consume.WordReach (verified S (relabelAdj σ adj) (transportColouring σ χ)) (σ a) (σ b)
        ↔ Consume.WordReach (verified S adj χ) a b)) :
    StallEquivariant (forceThenConsume key S) := by
  intro σ adj χ
  rw [Composite.narrow_forceThenConsume, Composite.narrow_forceThenConsume]
  have hperm : (forcedSet key (relabelAdj σ adj) (transportColouring σ χ)).Perm
      ((forcedSet key adj χ).map σ) := Composite.narrowFnEquivariant_forcedSet hk σ adj χ
  have hFin : (forcedSet key (relabelAdj σ adj) (transportColouring σ χ)).toFinset
      = (forcedSet key adj χ).toFinset.image σ := by
    ext x
    simp only [List.mem_toFinset, Finset.mem_image]
    rw [hperm.mem_iff]
    simp [List.mem_map]
  rw [dedup_map_length_eq_card_image, dedup_map_length_eq_card_image, hFin, Finset.image_image]
  refine card_image_congr_of_iff ?_
  intro a ha b hb
  simp only [Function.comp_apply]
  rw [Consume.rep_eq_iff_wordReach, Consume.rep_eq_iff_wordReach]
  exact horb σ adj χ a b
    (Composite.forcedSet_subset key adj χ (List.mem_toFinset.mp ha))
    (Composite.forcedSet_subset key adj χ (List.mem_toFinset.mp hb))

/-- **★★★ THE GUARDED MIXED CANONIZER, WITH NO CARRIED FLAG HYPOTHESIS.** Sound, iso-invariant, complete, and
unconditionally polynomial — for **any** equivariant key and **any** equivariant supply. This is the first form
of the mixed capstone whose hypotheses a concrete resolver stack can actually discharge. -/
theorem guarded_mixed_canonizer {key : Key n} (hk : KeyEquivariant key)
    {S : Supply n} (hS : SupplyEquivariant S) :
    CanonSpec.IsCanonicalFormOpt
      (Descend.canonForm? (Refine.encodeFreeFast (n := n))
        (Stall.guard (forceThenConsume key S))) :=
  Residue.guarded_mixed_canonizer hk (stallEquivariant_forceThenConsume hk hS)

/-! ## 5. ★★★ THE INSTANCE — `matchSupply` discharges it

A conditional theorem whose hypothesis nothing satisfies is the project's recurring failure mode, and until this
section `StallEquivariant` was exactly that. `matchSupply` is a **structural function of `(adj, χ)`** — it refines
each branch, colour-matches the discrete pairs, and hands the results back — so its generators **conjugate**
(`Consume.matchCandidate_conj`), which is precisely `GensEquivariant`. -/

/-- **★★ `matchSupply` IS EQUIVARIANT.** The construction conjugates, *including its failure mode*: it declines on
`σ·G` exactly where it declines on `G`. -/
theorem gensEquivariant_matchSupply : GensEquivariant (Consume.matchSupply (n := n)) := by
  intro σ adj χ g
  have hbr : ∀ x : Fin n, x ∈ branches (transportColouring σ χ) ↔ ∃ y ∈ branches χ, σ y = x := by
    intro x
    rw [(branches_transport_perm σ χ).mem_iff, List.mem_map]
  simp only [Consume.mem_gens_matchSupply_iff]
  constructor
  · rintro ⟨v, hv, w, hw, hmc⟩
    obtain ⟨v₀, hv₀, rfl⟩ := (hbr v).mp hv
    obtain ⟨w₀, hw₀, rfl⟩ := (hbr w).mp hw
    rw [Consume.matchCandidate_conj] at hmc
    rcases hcase : Consume.matchCandidate adj χ v₀ w₀ with _ | t
    · rw [hcase] at hmc; simp at hmc
    · rw [hcase] at hmc
      simp only [Option.map_some, Option.some.injEq] at hmc
      exact ⟨t, ⟨v₀, hv₀, w₀, hw₀, hcase⟩, hmc.symm⟩
  · rintro ⟨h, ⟨v, hv, w, hw, hmc⟩, rfl⟩
    refine ⟨σ v, (hbr _).mpr ⟨v, hv, rfl⟩, σ w, (hbr _).mpr ⟨w, hw, rfl⟩, ?_⟩
    rw [Consume.matchCandidate_conj, hmc]
    rfl

theorem supplyEquivariant_matchSupply : SupplyEquivariant (Consume.matchSupply (n := n)) :=
  supplyEquivariant_of_gensEquivariant gensEquivariant_matchSupply

/-- **★★★ THE FIRST CONCRETE MIXED CANONIZER.** Every parameter is a *named, built* object — the encode-free
refiner, the look-ahead key, the colour-match oracle — and **no hypothesis is carried**. `①a` (sound), `①b`
(complete), `①c` (iso-invariant answer *and* iso-invariant flag), and — via `Stall.descentCost_guard_le` —
**unconditionally polynomial**.

Everything still open is a **firing** question: how large `Residue.Handled` is, i.e. how much the key and the
oracle can actually see. Nothing open is a correctness question. -/
theorem matchSupply_guarded_canonizer :
    CanonSpec.IsCanonicalFormOpt
      (Descend.canonForm? (Refine.encodeFreeFast (n := n))
        (Stall.guard (forceThenConsume (Force.lookaheadKey (n := n))
          (Consume.matchSupply (n := n))))) :=
  guarded_mixed_canonizer Force.keyEquivariant_lookahead supplyEquivariant_matchSupply

end SupplyTransport
end ChainDescent
