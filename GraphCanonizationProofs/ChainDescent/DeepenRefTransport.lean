import ChainDescent.DeepenRef
/-! ⚠⚠ SUPERSEDED & PARKED (2026-07-23, TRACK A) — NOT in `build.sh`, DOES NOT COMPILE against the current
`deepen`. This is the DISCARDED reference route (`deepenRefSupply`/`DeepenRefInExec`/R1/R2) for `deepenSupply`
's `①c`. It was made MOOT by the whole-graph-discretize redesign: `①c` now closes modulo `{Tinhofer}` alone
(`DeepenTinhofer.deepenSupply_guarded_canonizer_direct`), with `[DISC]`/gate/termination structural and
`AnchorFires` eliminated. Retained for provenance only — see `docs/chain-descent-deepen-supply.md` STATUS +
§8/§9 (provenance) and `docs/00-START-HERE.md` §2 C3b. Do NOT build on this. -/


/-!
# `C3b` tranche 2, part IV — the reference's transport (R2), algebraic core

`DeepenRef.lean` §6 (R2): `deepenRefSupply` must be `SupplyEquivariant` for the `OrbitPrune.SameOrbits`
reduction to hand ①c to `deepenSupply`. This file builds toward `GensEquivariant deepenRefSupply` (⟹
`SupplyEquivariant` by `supplyEquivariant_of_gensEquivariant`).

The algebraic core, landed here: **`twistOf` transports to its σ-conjugate**. Everything else in R2 is
the set-level bookkeeping (`deepenAll`/`replayAll` leaf-set correspondence via the part-I stage
lemmas + `branches_transport_perm`), assembled on top of this.

The heart is `Deck2.permOf_conj` (`permOf (σ ∘ f ∘ σ⁻¹) = (permOf f).map (σ · σ⁻¹)`) and
`Consume.isColAut_conj_iff` (the verification gate is conjugation-invariant): the twist's colour-match
function is σ-conjugate under relabelling, so the whole `permOf`-then-verify pipeline conjugates.

## ⚠ Note for the assembly (a subtlety found while scoping it)

`twistOf_transport` takes `K.map σ` on the nose, but the *transported* `deepenRefGens` calls `twistOf`
with `K' = coupled (transp σ χ) (transp σ χ1)`, which is only a **`List.Perm` of `(coupled χ χ1).map σ`**
— `coupled` filters `finRange` in index order, which `σ` need not respect (the same up-to-`Perm` wall as
part I). `twistOf`'s `K.find?` is order-dependent in general, so this gap is real — EXCEPT under the
gate: `deepenRefGens` only calls `twistOf` when `allSingletonsK K χ1`, and then each `χ1`-colour has a
UNIQUE `K`-match, so `find?` returns the same vertex regardless of `K`'s order. So the assembly needs a
lemma **`twistOf` is invariant under a `Perm` of `K` when `allSingletonsK K χ1`**, then `twistOf_transport`
composes with `coupled`'s up-to-`Perm` transport. Recorded so it is not rediscovered.
-/

namespace ChainDescent
namespace Deepen

open ChainDescent.Consume (IsColAut isColAut_conj_iff)
open ChainDescent.Deck2 (permOf permOf_conj)
open ChainDescent.Descend (transportColouring)

variable {n : Nat}

/-! ## 1. The colour-match image function -/

/-- The colour-match function inside `twistOf`, named so it can be reasoned about. On the coupled
component `K`, `v` maps to the first `K`-member whose replayed colour matches `v`'s anchor colour;
off `K`, identity. -/
def imgFun (χ1 : Colouring n) (K : List (Fin n)) (χj : Colouring n) : Fin n → Fin n :=
  fun v => if K.contains v then (K.find? (fun w => χj w == χ1 v)).getD v else v

/-- `Vector.ofFn` read back pointwise is the function. -/
theorem vget_ofFn (g : Fin n → Fin n) (v : Fin n) : (Vector.ofFn g).get v = g v := by
  rw [Vector.get]; simp

/-- `twistOf` is `permOf` of `imgFun`, gated by `IsColAut` — the `Vector.ofFn` is just materialisation
(trap #1) and `permOf` reads it back pointwise. -/
theorem twistOf_eq_imgFun (adj : AdjMatrix n) (χ χ1 : Colouring n) (K : List (Fin n))
    (χj : Colouring n) :
    twistOf adj χ χ1 K χj =
      match permOf (imgFun χ1 K χj) with
      | none => none
      | some ρ => if decide (IsColAut adj χ ρ) then some ρ else none := by
  unfold twistOf imgFun
  simp only [vget_ofFn]
  rfl

/-! ## 2. `imgFun` transports as a σ-conjugate -/

/-- Membership in `K.map σ` at `σ v` reduces to membership in `K` at `v`. -/
theorem contains_map_apply (σ : Equiv.Perm (Fin n)) (K : List (Fin n)) (v : Fin n) :
    (K.map σ).contains (σ v) = K.contains v := by
  simp only [List.contains_eq_mem, List.mem_map, decide_eq_decide]
  constructor
  · rintro ⟨u, hu, heq⟩; rwa [σ.injective heq] at hu
  · intro hv; exact ⟨v, hv, rfl⟩

/-- **`imgFun` conjugates under `σ`.** The transported image function equals `σ ∘ imgFun ∘ σ⁻¹`. -/
theorem imgFun_transport (σ : Equiv.Perm (Fin n)) (χ1 : Colouring n) (K : List (Fin n))
    (χj : Colouring n) :
    imgFun (transportColouring σ χ1) (K.map σ) (transportColouring σ χj)
      = (fun x => σ (imgFun χ1 K χj (σ.symm x))) := by
  funext x
  obtain ⟨v, rfl⟩ : ∃ v, x = σ v := ⟨σ.symm x, (Equiv.apply_symm_apply σ x).symm⟩
  simp only [Equiv.symm_apply_apply]
  unfold imgFun
  rw [contains_map_apply σ K v]
  by_cases hc : K.contains v
  · rw [if_pos hc, if_pos hc]
    have h1 : transportColouring σ χ1 (σ v) = χ1 v := by
      show χ1 (σ.symm (σ v)) = χ1 v; rw [Equiv.symm_apply_apply]
    rw [h1]
    -- transported find? predicate at `w` is the original predicate at `σ⁻¹ w`
    have hpe : ((fun w => transportColouring σ χj w == χ1 v) ∘ (σ : Fin n → Fin n))
        = (fun u => χj u == χ1 v) := by
      funext u
      show (transportColouring σ χj (σ u) == χ1 v) = (χj u == χ1 v)
      rw [show transportColouring σ χj (σ u) = χj u from by
        show χj (σ.symm (σ u)) = χj u; rw [Equiv.symm_apply_apply]]
    rw [List.find?_map, hpe]
    cases hf : K.find? (fun u => χj u == χ1 v) with
    | none => simp
    | some u => simp
  · rw [if_neg hc, if_neg hc]

/-! ## 3. `twistOf` transports as a σ-conjugate -/

/-- **★ THE ALGEBRAIC CORE OF R2.** The twist on the relabelled graph is the σ-conjugate of the twist
here — verification included, via `isColAut_conj_iff`. -/
theorem twistOf_transport (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ χ1 : Colouring n)
    (K : List (Fin n)) (χj : Colouring n) :
    twistOf (relabelAdj σ adj) (transportColouring σ χ) (transportColouring σ χ1) (K.map σ)
        (transportColouring σ χj)
      = (twistOf adj χ χ1 K χj).map (fun ρ => σ * ρ * σ⁻¹) := by
  rw [twistOf_eq_imgFun, twistOf_eq_imgFun, imgFun_transport, permOf_conj]
  cases hp : permOf (imgFun χ1 K χj) with
  | none => simp
  | some ρ =>
      simp only [Option.map_some, isColAut_conj_iff]
      cases decide (IsColAut adj χ ρ) <;> simp

end Deepen
end ChainDescent
