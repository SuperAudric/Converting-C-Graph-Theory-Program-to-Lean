/-
# Bridge capstone — a `Z`-separating base discharges `ZProfileSeparates` (B1-deg dissolved).

The observable↔count bridge closes in two clean steps:
* **per-pair (B1a + B1b):** a *config-nondegenerate* pair `{t,t₀}` on which the pair invariant `χ(det G₂)` separates
  `(u,v)` is a pair on which the **joint isotropic counts differ**, `Z_u({t,t₀}) ≠ Z_v({t,t₀})`
  (`ScratchBridgeA.levelset_count_collapse` gives the closed form `Z_w·q³ = qᵈ + χ(det G₂_w)·K·(q[c=0]−1)`;
  `ScratchBridge.pairCount_ne_of_chiSep` is the distinctness);
* **this module:** a base `T` on which **some** sub-frame `S ⊆ T` separates the joint counts of every `u ≠ v`
  discharges `ZProfileSeparates Q T` outright.

**Why this dissolves B1-deg.** The earlier worry — a separating pair with one point's config degenerate (`χ = 0`,
where `levelset_count_collapse` does not apply) — never arises if the increment-4 matching targets *config-nondegenerate*
separating pairs. The config-degenerate locus `{(t,t₀) : det G₂ = 0}` is a proper subvariety of density `O(1/√q)`
(an affine-quadric zero set, `≈ q^{d-1/2}` of `q^d` per anchor — the same `zeroCount_sq_le` bound increment 3 already
uses), so folding it into the matching's "bad" set (alongside bad anchors) costs only an `O(1/√q)` shrink of the gap:
increment 3 gives `#{strict-separating t} ≥ ¼·|V| − (z_u+z_v) ≥ (¼ − O(1/√q))·|V| > 0` for `q ≳ const`. So a
config-nondeg `Z`-separating base exists by the same first-moment/matching argument, and the **degenerate-config `Z`
value is never needed** — B1-deg is dissolved into the increment-4 density rather than proved. (Computing it directly,
the `D3b` rank-deficient Lemma-A count, remains an option but is off the critical path.)

So the bridge reduces to: increment 4/5 must produce the hypothesis `hsep` below (a config-nondeg χ-separating base,
turned into a `Z`-separating base by the per-pair step) — and `ZProfileSeparates` follows. NOT in build (scratch;
`lake env lean ChainDescent/ScratchBridgeZ.lean`, after `lake build ChainDescent.ScratchCrux`).
-/
import ChainDescent.ScratchCrux

namespace ChainDescent

variable {p d : ℕ} [Fact p.Prime]

/-- **The bridge reduction.** If every pair of distinct points is separated by *some* sub-frame `S ⊆ T` in the joint
isotropic counts, then `ZProfileSeparates Q T` holds. (The contrapositive of `ZProfileSeparates`'s antecedent: agreeing
`Z`-profiles over all `S ⊆ T` force `u = u'`, hence the `Q`-profiles agree by reflexivity.) This is what the per-pair
bridge step (`ScratchBridge.pairCount_ne_of_chiSep`, fed by `levelset_count_collapse`) delivers from a config-nondeg
χ-separating base — see the module header. -/
theorem zProfileSeparates_of_zSep (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    (T : Finset (Fin (p ^ d)))
    (hsep : ∀ u u' : Fin (p ^ d), u ≠ u' →
      ∃ S, S ⊆ T ∧ jointIsoCount Q u S ≠ jointIsoCount Q u' S) :
    ZProfileSeparates Q T := by
  intro u u' hall
  by_cases h : u = u'
  · subst h; exact ⟨rfl, fun _ => rfl⟩
  · obtain ⟨S, hS, hne⟩ := hsep u u' h
    exact absurd (hall S hS) hne

end ChainDescent

#print axioms ChainDescent.zProfileSeparates_of_zSep
