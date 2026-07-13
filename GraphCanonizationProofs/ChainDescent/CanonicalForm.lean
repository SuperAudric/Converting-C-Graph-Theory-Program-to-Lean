import ChainDescent.Cascade

/-!
# Stage 0 of the mixed-composition track — the canonical-form correctness framework

(`docs/chain-descent-mixed-composition.md` Stage 0.)

The mixed canonizer does **not** compute the global lex-min over all labellings — the deferral schedule
produces a *different* canonical form (the individualization order fixes each leaf's numbering), which is
nonetheless **iso-invariant**, and that is all correctness needs. So the spec here is deliberately NOT "= the
global lex-min". It is the universal correctness predicate:

  a **canonical form** is any `C : AdjMatrix n → (Fin n → Fin n → Nat)` that is
  · **sound** — `C G` is a genuine relabelling of `G`, and
  · **iso-invariant** — relabelling the input leaves `C G` unchanged.

The load-bearing lemma (`complete_of_isCanonicalForm`) is that these two give **completeness for free**:
`C G = C H ↔ G ≅ H`. So `①b` (completeness) and `①c` (flag/output iso-invariance) are not separate work — the
ONLY real obligation is iso-invariance of the *construction*, exactly where the "X3" difficulty lives.

`lexMin` is the generic iso-invariant **selection** technique — a lex-min over a finite candidate set of
labellings. It is sound when every candidate is a relabelling, and iso-invariant when the candidate SET is the
same finset for `G` and `relabelAdj σ G` (`cand (relabelAdj σ G) = cand G`). That set-equality — NOT "the set
is all of `Perm`" — is the honest obligation the later stages discharge (for deferral it holds because a
reached leaf's matrix is a function of the abstract refinement, which is σ-invariant).
-/

namespace ChainDescent
namespace CanonSpec

open scoped Classical

variable {n : Nat}

/-- A candidate canonical output: a labelled adjacency matrix. -/
abbrev Labelled (n : Nat) := Fin n → Fin n → Nat

/-! ## Graph isomorphism (matching `GraphIso` / `Publication.Iso`) -/

/-- **Graph isomorphism:** some relabelling of `G` is `H`. -/
def GraphIso (G H : AdjMatrix n) : Prop :=
  ∃ π : Equiv.Perm (Fin n), labelledAdj π G = H.adj

theorem GraphIso.refl (G : AdjMatrix n) : GraphIso G G :=
  ⟨1, by funext i j; simp [labelledAdj]⟩

/-- **A common labelled image ⟹ isomorphic.** If `labelledAdj πG G = labelledAdj πH H` the inputs are
relabellings of one another. Pure `Equiv.Perm` bookkeeping on `labelledAdj π adj i j = adj (π.symm i) (π.symm j)`. -/
theorem iso_of_labelledAdj_eq {G H : AdjMatrix n} {πG πH : Equiv.Perm (Fin n)}
    (h : labelledAdj πG G = labelledAdj πH H) : GraphIso G H := by
  refine ⟨(πH.trans πG.symm).symm, funext fun i => funext fun j => ?_⟩
  simp only [labelledAdj, Equiv.symm_symm, Equiv.trans_apply]
  have hEq := congrFun (congrFun h (πH i)) (πH j)
  simp only [labelledAdj, Equiv.symm_apply_apply] at hEq
  exact hEq

/-- **`H` is `relabelAdj π G` when `labelledAdj π G = H.adj`.** The structure-level restatement of `GraphIso`:
`relabelAdj π G` is *definitionally* `⟨labelledAdj π G⟩`, so a witnessing `π` exhibits `H` as a relabel of `G`. -/
theorem relabelAdj_eq_of_labelledAdj {G H : AdjMatrix n} {π : Equiv.Perm (Fin n)}
    (h : labelledAdj π G = H.adj) : relabelAdj π G = H := by
  obtain ⟨aH⟩ := H
  show (⟨fun i j => G.adj (π.symm i) (π.symm j)⟩ : AdjMatrix n) = ⟨aH⟩
  have h' : (fun i j => G.adj (π.symm i) (π.symm j)) = aH := h
  rw [h']

/-! ## The correctness predicate — sound + iso-invariant -/

/-- **Soundness:** the output on `G` is a genuine relabelling of `G`. -/
def Sound (C : AdjMatrix n → Labelled n) : Prop :=
  ∀ G : AdjMatrix n, ∃ π : Equiv.Perm (Fin n), C G = labelledAdj π G

/-- **Iso-invariance:** relabelling the input leaves the output unchanged. -/
def IsoInvariant (C : AdjMatrix n → Labelled n) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (G : AdjMatrix n), C (relabelAdj σ G) = C G

/-- **A canonical form** = sound ∧ iso-invariant. Completeness is then free (`complete_of_isCanonicalForm`). -/
def IsCanonicalForm (C : AdjMatrix n → Labelled n) : Prop :=
  Sound C ∧ IsoInvariant C

/-- **THE Stage-0 payoff — completeness is FREE.** A sound, iso-invariant `C` is a *complete* isomorphism
invariant: `C G = C H ↔ G ≅ H`. So once the construction is proven iso-invariant, `①b` costs nothing; all the
weight is the iso-invariance itself. -/
theorem complete_of_isCanonicalForm {C : AdjMatrix n → Labelled n} (h : IsCanonicalForm C)
    (G H : AdjMatrix n) : C G = C H ↔ GraphIso G H := by
  obtain ⟨hsound, hinv⟩ := h
  constructor
  · intro hEq
    obtain ⟨πG, hπG⟩ := hsound G
    obtain ⟨πH, hπH⟩ := hsound H
    exact iso_of_labelledAdj_eq (hπG.symm.trans (hEq.trans hπH))
  · rintro ⟨π, hπ⟩
    have hHrel : relabelAdj π G = H := relabelAdj_eq_of_labelledAdj hπ
    rw [← hHrel, hinv]

/-! ## The generic iso-invariant selection combinator — lex-min over a candidate set

`lexMin S hS` is the row-major lex-least matrix in a nonempty finite candidate set `S`, via the reusable
`MatrixLex` linear order (`Spine.lean`). Its two properties feed `IsCanonicalForm` directly. -/

/-- The lex-least labelling in a nonempty finite candidate set. -/
noncomputable def lexMin (S : Finset (Labelled n)) (hS : S.Nonempty) : Labelled n :=
  ofMatrixLex ((S.image toMatrixLex).min' (hS.image _))

/-- `lexMin` returns a genuine member of the candidate set. -/
theorem lexMin_mem (S : Finset (Labelled n)) (hS : S.Nonempty) : lexMin S hS ∈ S := by
  obtain ⟨M, hM, hEq⟩ :=
    Finset.mem_image.mp (Finset.min'_mem (S.image toMatrixLex) (hS.image _))
  have : lexMin S hS = M := by
    unfold lexMin; rw [← hEq, ofMatrixLex_toMatrixLex]
  rw [this]; exact hM

/-- `lexMin` depends only on the candidate SET (the nonemptiness proof is irrelevant). -/
theorem lexMin_congr {S T : Finset (Labelled n)} (h : S = T)
    (hS : S.Nonempty) (hT : T.Nonempty) : lexMin S hS = lexMin T hT := by
  subst h; rfl

/-- **Soundness of a lex-min canonizer.** If every candidate of `cand G` is a relabelling of `G`, then
`fun G => lexMin (cand G) …` is sound. -/
theorem sound_lexMin {cand : AdjMatrix n → Finset (Labelled n)}
    (hne : ∀ G, (cand G).Nonempty)
    (hrel : ∀ (G : AdjMatrix n), ∀ M ∈ cand G, ∃ π : Equiv.Perm (Fin n), M = labelledAdj π G) :
    Sound (fun G => lexMin (cand G) (hne G)) :=
  fun G => hrel G _ (lexMin_mem (cand G) (hne G))

/-- **Iso-invariance of a lex-min canonizer — reduced to candidate-set equality.** If the candidate set is the
SAME finset for `G` and `relabelAdj σ G`, then the lex-min canonizer is iso-invariant. This is the honest
obligation (NOT "cand is all of Perm"): for the deferral descent it holds because a reached leaf's matrix is a
function of the abstract, σ-invariant refinement. -/
theorem isoInvariant_lexMin {cand : AdjMatrix n → Finset (Labelled n)}
    (hne : ∀ G, (cand G).Nonempty)
    (htr : ∀ (σ : Equiv.Perm (Fin n)) (G : AdjMatrix n), cand (relabelAdj σ G) = cand G) :
    IsoInvariant (fun G => lexMin (cand G) (hne G)) :=
  fun σ G => lexMin_congr (htr σ G) (hne (relabelAdj σ G)) (hne G)

/-- **The Stage-0 assembly — a lex-min over a sound, set-iso-invariant candidate family is a canonical form**
(hence a complete invariant, `complete_of_isCanonicalForm`). The two hypotheses are exactly what the
consume/branch descent must deliver: (i) every reached leaf is a relabelling; (ii) the reached-leaf matrix set
transports trivially under relabelling. -/
theorem isCanonicalForm_lexMin {cand : AdjMatrix n → Finset (Labelled n)}
    (hne : ∀ G, (cand G).Nonempty)
    (hrel : ∀ (G : AdjMatrix n), ∀ M ∈ cand G, ∃ π : Equiv.Perm (Fin n), M = labelledAdj π G)
    (htr : ∀ (σ : Equiv.Perm (Fin n)) (G : AdjMatrix n), cand (relabelAdj σ G) = cand G) :
    IsCanonicalForm (fun G => lexMin (cand G) (hne G)) :=
  ⟨sound_lexMin hne hrel, isoInvariant_lexMin hne htr⟩

/-! ## Stage 0a (lift) — the FLAGGING (`Option`) canonizer: the shape `Publication.canonForm?` really has

The real canonizer **flags**: it returns `none` at mutual stall (`docs/chain-descent-mixed-composition.md` §1).
So the object every later stage is proved about is `AdjMatrix n → Option (Labelled n)`, not the total
`AdjMatrix n → Labelled n` above. This section lifts the framework onto that type, and the payoff survives
verbatim: **`Sound ∧ IsoInvariant ⟹ complete`, with the flag's iso-invariance thrown in for free.**

Note the economy: `IsoInvariantOpt` is a *single* equation `C (relabelAdj σ G) = C G` on `Option`s, so it says
"relabelling changes nothing" — the answer *and* whether it flagged. That is `Publication.canon_complete`'s
hypothesis and `Publication.flag_iso_invariant` in one. There is no separate flag obligation. -/

/-- **Soundness, flagging form.** Whenever the canonizer answers, the output is a genuine relabelling of the
input. This is *exactly* the statement of `Publication.canon_sound`. -/
def SoundOpt (C : AdjMatrix n → Option (Labelled n)) : Prop :=
  ∀ (G : AdjMatrix n) (c : Labelled n), C G = some c → ∃ π : Equiv.Perm (Fin n), c = labelledAdj π G

/-- **Iso-invariance, flagging form.** Relabelling the input changes nothing — *including whether it flagged*.
Carries both the output invariance and `①c` (flag invariance). -/
def IsoInvariantOpt (C : AdjMatrix n → Option (Labelled n)) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (G : AdjMatrix n), C (relabelAdj σ G) = C G

/-- **A flagging canonical form** = sound ∧ iso-invariant. The complete spec of the mixed canonizer: nothing
else is required of it, and in particular it is NOT required to compute any global lex-min. -/
def IsCanonicalFormOpt (C : AdjMatrix n → Option (Labelled n)) : Prop :=
  SoundOpt C ∧ IsoInvariantOpt C

/-- Isomorphic inputs receive the **same answer** (same value, or both flagged). The engine behind both payoffs
below: it is `IsoInvariantOpt` re-expressed against `GraphIso` instead of a literal `relabelAdj`. -/
theorem eq_of_graphIso {C : AdjMatrix n → Option (Labelled n)} (hinv : IsoInvariantOpt C)
    {G H : AdjMatrix n} (h : GraphIso G H) : C G = C H := by
  obtain ⟨π, hπ⟩ := h
  have hHrel : relabelAdj π G = H := relabelAdj_eq_of_labelledAdj hπ
  rw [← hHrel, hinv]

/-- **`①b` (`Publication.canon_complete`) — FREE.** Whenever the canonizer answers on both inputs, the outputs
coincide iff the graphs are isomorphic. The `→` direction is iso-invariance; the `←` direction is soundness. -/
theorem complete_of_isCanonicalFormOpt {C : AdjMatrix n → Option (Labelled n)}
    (h : IsCanonicalFormOpt C) (G H : AdjMatrix n) (cG cH : Labelled n)
    (hG : C G = some cG) (hH : C H = some cH) : GraphIso G H ↔ cG = cH := by
  obtain ⟨hsound, hinv⟩ := h
  constructor
  · intro hiso
    have hEq : C G = C H := eq_of_graphIso hinv hiso
    rw [hG, hH] at hEq
    exact Option.some.inj hEq
  · intro hEq
    obtain ⟨πG, hπG⟩ := hsound G cG hG
    obtain ⟨πH, hπH⟩ := hsound H cH hH
    exact iso_of_labelledAdj_eq (hπG.symm.trans (hEq.trans hπH))

/-- **`①c` (`Publication.flag_iso_invariant`) — FREE.** Flagging is a property of the isomorphism class. -/
theorem flag_iso_invariant_of_isoInvariantOpt {C : AdjMatrix n → Option (Labelled n)}
    (hinv : IsoInvariantOpt C) {G H : AdjMatrix n} (h : GraphIso G H) :
    C G = none ↔ C H = none := by
  rw [eq_of_graphIso hinv h]

/-! ### The flag mechanism — `none ⟺ stalled`, and stalled is equivariant

The descent flags exactly when every resolver stalls. `guardBy` is that shape at the spec level: a total
construction gated by a "handled" predicate. The lemma below is the doc's claim, proved: **if the construction
is a canonical form and the handled-predicate is iso-invariant, the guarded (flagging) canonizer is a flagging
canonical form** — so the flag contributes no new obligation beyond the equivariance of "stalled".

(The real `descend` returns `Option` natively rather than being built by `guardBy`; this is the spec-level
statement of why its flag is free. It is `noncomputable` only because of the `Classical` decidability of an
arbitrary `P` — the real object's stall test is decidable and computable.) -/

/-- An iso-invariant predicate on graphs (the "handled" / `¬stalled` side of the flag). -/
def IsoInvariantPred (P : AdjMatrix n → Prop) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (G : AdjMatrix n), P (relabelAdj σ G) ↔ P G

/-- Gate a total construction by a handled-predicate: answer when handled, flag otherwise. -/
noncomputable def guardBy (P : AdjMatrix n → Prop) (C : AdjMatrix n → Labelled n) :
    AdjMatrix n → Option (Labelled n) :=
  fun G => if P G then some (C G) else none

/-- **The flag is free.** A canonical form gated by an iso-invariant handled-predicate is a *flagging*
canonical form. So `①a`+`①b`+`①c` all reduce to: the construction is sound + iso-invariant, and "stalled" is
iso-invariant. -/
theorem isCanonicalFormOpt_guardBy {P : AdjMatrix n → Prop} {C : AdjMatrix n → Labelled n}
    (hC : IsCanonicalForm C) (hP : IsoInvariantPred P) :
    IsCanonicalFormOpt (guardBy P C) := by
  obtain ⟨hsound, hinv⟩ := hC
  constructor
  · intro G c hc
    unfold guardBy at hc
    by_cases hPG : P G
    · rw [if_pos hPG] at hc
      obtain ⟨π, hπ⟩ := hsound G
      exact ⟨π, (Option.some.inj hc).symm.trans hπ⟩
    · rw [if_neg hPG] at hc
      simp at hc
  · intro σ G
    unfold guardBy
    by_cases hPG : P G
    · rw [if_pos ((hP σ G).mpr hPG), if_pos hPG, hinv]
    · rw [if_neg (fun h => hPG ((hP σ G).mp h)), if_neg hPG]

/-- The total theory embeds: a (never-flagging) canonical form is a flagging canonical form. Keeps the
single-path / total objects usable against the `Option` spec. -/
theorem isCanonicalFormOpt_some {C : AdjMatrix n → Labelled n} (h : IsCanonicalForm C) :
    IsCanonicalFormOpt (fun G => some (C G)) := by
  obtain ⟨hsound, hinv⟩ := h
  constructor
  · intro G c hc
    obtain ⟨π, hπ⟩ := hsound G
    exact ⟨π, (Option.some.inj hc).symm.trans hπ⟩
  · intro σ G
    show some (C (relabelAdj σ G)) = some (C G)
    rw [hinv]

end CanonSpec
end ChainDescent
