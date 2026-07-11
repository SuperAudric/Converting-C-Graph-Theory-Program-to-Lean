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

end CanonSpec
end ChainDescent
