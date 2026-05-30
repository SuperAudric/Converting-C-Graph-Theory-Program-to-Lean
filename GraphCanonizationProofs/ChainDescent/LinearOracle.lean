import ChainDescent
import Mathlib.GroupTheory.Perm.Basic

/-!
# §L — Linear oracle: abelian-stripping (B2)

The Lean formalisation of the **linear oracle / abelian-stripping** deliverable
(`docs/chain-descent-linear-oracle.md`; tractable-buildout B2), built on the §15.8
scaffolding of `ChainDescent.lean` (`DirAssignment`, `flipPair`, `LinearOracleSpec`,
`LeafTwistSpec`, `canonAdj`, `relabelMatrix`).

The linear oracle resolves an **abelian genuine decision** — a size-2 target cell
whose two branches `σ` and `flipPair σ a b` differ only in the one order label on the
decided pair `(a, b)`. It discovers a **twist** `t`: a vertex permutation, *verified*
to be a graph automorphism (the mandatory §4.5 edge-check), whose relabelling carries
`σ`'s leaf adjacency matrix to the flipped branch's. A verified twist certifies the two
branches isomorphic, so one is pruned — turning a `2`-way fork into a single descent.

## Scope of this file (B2.1 — the soundness anchor)

* `RealizesFlip` — the precise relation "`t` relabels `σ`'s leaf to `flipPair σ`'s leaf".
* `TwistWitness` — the verified data the (C#-side) discovery produces: the flipped pair,
  the permutation, its `IsAut` proof, and the `RealizesFlip` proof.
* `twistOracle` — a concrete `LinearOracleSpec` instance, parameterised by an abstracted
  discovery function (the canonical-id sub-cell matching lives in C#). Verification is
  *inside* `TwistWitness`, so every returned permutation is a genuine automorphism.
* `twistOracle_leafTwist` — the discharge: `twistOracle` satisfies `LeafTwistSpec`, with
  the flipped branch as the **explicit** witness `σ' = flipPair σ` (sharper than the
  existential the bare spec asks for). This is `docs/chain-descent-linear-oracle.md` §8.2
  step 1 + the §2.3 "missing deliverable", modulo the discovery construction.

The **abelian structure** is already proved upstream: the per-pair flips are commuting
involutions (`DirAssignment.flipPair_comm`, `flipPair_idempotent`) — the `Z₂^d` action.

## Out of scope here (later milestones)

* B2.2 — the construction's *determinacy* (`UniqueCandidateTwist`: an all-singleton
  refinement footprint forces a unique candidate; §4.2–4.3).
* B2.3 — the `warm_6_2 → canonAdj` bridge that *constructs* a realizing twist from the
  partition mirror (`flipPair_partition_invariant`) + verification, rather than taking it
  as given (§8.2 step 2).
-/

namespace ChainDescent

variable {n : Nat} {adj : AdjMatrix n} {P₀ : PMatrix n}
  {χι₀ : Colouring n} {sel : Colouring n → Finset (Fin n)}

/-! ## §L.1 — Soundness anchor (B2.1) -/

/-- **A twist realises the flip of decision `(a, b)` on branch `σ`.** The permutation
`t`, acting on the leaf adjacency matrix by relabelling, carries `σ`'s canonical leaf to
that of the flipped branch `σ.flipPair a b`. This is the exact shape of the
`LeafTwistSpec` conclusion, with the partner branch pinned to the flip — the
pruning-justification: the two directions of the decision give the same leaf modulo `t`. -/
def RealizesFlip {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) (isLeaf : chain.IsLeaf)
    (σ : DirAssignment P₀ chain.D) (t : Equiv.Perm (Fin n))
    (a b : Fin n) (ha : a ∈ chain.D) (hb : b ∈ chain.D) : Prop :=
  relabelMatrix t (chain.canonAdj isLeaf σ)
    = chain.canonAdj isLeaf (σ.flipPair a b ha hb)

/-- **A verified twist witness for branch `σ`.** Bundles the decided pair `(a, b)`, the
candidate permutation `t`, the **verification** that `t` is an automorphism (the
mandatory §4.5 edge-check — the sole soundness anchor), and the proof that `t` realises
the flip. This is precisely what the C# discovery (`HarvestTwists`) constructs and
checks before returning. -/
structure TwistWitness {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k)
    (isLeaf : chain.IsLeaf) (σ : DirAssignment P₀ chain.D) where
  /-- The first vertex of the decided pair. -/
  a : Fin n
  /-- The second vertex of the decided pair. -/
  b : Fin n
  /-- `a` lies in the committed decision set. -/
  ha : a ∈ chain.D
  /-- `b` lies in the committed decision set. -/
  hb : b ∈ chain.D
  /-- The candidate twist permutation. -/
  t : Equiv.Perm (Fin n)
  /-- Verification: `t` is a graph automorphism (edge-by-edge, §4.5). -/
  isAut : IsAut t adj
  /-- `t` relabels `σ`'s leaf to the flipped branch's leaf. -/
  realizes : RealizesFlip chain isLeaf σ t a b ha hb

/-- **The twist oracle.** A concrete `LinearOracleSpec` instance, parameterised by an
abstracted `discover` function (the canonical-id sub-cell matching — C#-side, out of
scope for Lean, exactly as `LinearOracleSpec` abstracts discovery). It returns the
verified automorphism when discovery yields a `TwistWitness`, `none` otherwise. Because
the `IsAut` verification is carried *inside* `TwistWitness`, every returned permutation
is a genuine automorphism by construction. -/
def twistOracle
    (discover : ∀ {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) (hL : chain.IsLeaf)
      (σ : DirAssignment P₀ chain.D), Option (TwistWitness chain hL σ)) :
    LinearOracleSpec adj P₀ χι₀ sel :=
  fun {_} chain isLeaf σ => (discover chain isLeaf σ).map (fun tw => ⟨tw.t, tw.isAut⟩)

/-- **Soundness discharge (B2.1).** `twistOracle` satisfies `LeafTwistSpec`: whenever it
returns a twist, that twist relabels the branch `σ`'s leaf to *another* branch's leaf —
and we identify that branch **explicitly** as `σ' = flipPair σ`, sharper than the bare
existential. The proof is immediate from the `TwistWitness.realizes` field: verification
established `t ∈ Aut(adj)`, and `realizes` *is* the required leaf equality, so the flipped
branch witnesses the existential. This closes the pruning-justification contract
(`docs/chain-descent-linear-oracle.md` §2.3) for any sound discovery function. -/
theorem twistOracle_leafTwist
    (discover : ∀ {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) (hL : chain.IsLeaf)
      (σ : DirAssignment P₀ chain.D), Option (TwistWitness chain hL σ)) :
    LinearOracleSpec.LeafTwistSpec (twistOracle discover) := by
  intro k chain isLeaf σ result hsome
  -- Invert the `Option.map`: discovery produced a `TwistWitness`.
  simp only [twistOracle, Option.map_eq_some_iff] at hsome
  obtain ⟨tw, _, hmk⟩ := hsome
  -- The partner branch is the flipped one.
  refine ⟨σ.flipPair tw.a tw.b tw.ha tw.hb, ?_⟩
  -- `result.val = tw.t`, and `tw.realizes` is exactly the required equality.
  rw [← hmk]
  exact tw.realizes

/-! ## §L.2 — The candidate twist is forced (B2.2)

At a leaf, both branches `σ` and `flipPair σ a b` have **discrete** warm-refined
colourings (`samePartition_chain` + `isLeaf`), so each canonically labels the graph by
colour-rank: `canonAdj σ = labelledAdj (rankPerm π_σ) adj`. The two labellings therefore
differ by exactly one permutation — the **rank rebasing**
`rankPerm π_flip * (rankPerm π_σ)⁻¹` — and *that* permutation always realises the flip
(`candidateTwist_realizesFlip`). So the twist is not *discovered* among many candidates;
it is **forced**, the unique rank-aligning map (`candidateTwist_unique`). The linear
oracle's entire content collapses to one question — **is the forced candidate a graph
automorphism?** — the mandatory §4.5 edge-check, and nothing more
(`twistWitness_of_isAut`, `canonicalTwistOracle`).

This **discharges the iso-invariance obligation** (strategy §15 gap 2) for the linear
oracle at the leaf level: the candidate is a function of iso-invariant rank data, so the
discovery is deterministic. (The §4.3 all-singleton-vs-non-singleton ambiguity is a
*decision-node* concern in the C# online behaviour — subsumed here because the descent
reaches a discrete leaf before the oracle fires.) The candidate is precisely the
canonical **transversal element** for the decision (cf. the support / stabilizer-chain
relocation discussion): verifying it asks whether that coset representative is a real
symmetry. The abelian `Z₂` structure is `flipPair_idempotent` (the candidate for the
flip-back is the inverse) + `flipPair_comm` (disjoint decisions commute). -/

/-- **Relabelling composes.** Relabelling a labelled adjacency by `t` is labelling by the
product `t * s` — the `Equiv.Perm` group action on labelled matrices. -/
theorem relabelMatrix_labelledAdj (t s : Equiv.Perm (Fin n)) :
    relabelMatrix t (labelledAdj s adj) = labelledAdj (t * s) adj := by
  funext i j
  simp only [relabelMatrix, labelledAdj]
  rw [show (t * s).symm i = s.symm (t.symm i) by
        rw [Equiv.Perm.mul_def, Equiv.symm_trans_apply],
      show (t * s).symm j = s.symm (t.symm j) by
        rw [Equiv.Perm.mul_def, Equiv.symm_trans_apply]]

/-- `canonAdj` is `labelledAdj` of the rank permutation. Holds for *any* discreteness
proof (the rank permutation is proof-irrelevant), so `rfl`. -/
theorem canonAdj_eq_labelledAdj {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k)
    (isLeaf : chain.IsLeaf) (σ : DirAssignment P₀ chain.D)
    (hd : Discrete (warmRefine adj σ.σ chain.χι)) :
    chain.canonAdj isLeaf σ = labelledAdj (Colouring.rankPerm _ hd) adj := rfl

/-- **Rank rebasing relates any two branches' leaves.** For branches `σ, σ'`, relabelling
`σ`'s canonical leaf by the rank rebasing `rankPerm π_{σ'} * (rankPerm π_σ)⁻¹` gives
`σ'`'s canonical leaf. General over the two branches; the flip is the instance
`σ' = flipPair σ`. -/
theorem canonAdj_rebase {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k)
    (isLeaf : chain.IsLeaf) (σ σ' : DirAssignment P₀ chain.D)
    (hσ : Discrete (warmRefine adj σ.σ chain.χι))
    (hσ' : Discrete (warmRefine adj σ'.σ chain.χι)) :
    relabelMatrix (Colouring.rankPerm _ hσ' * (Colouring.rankPerm _ hσ)⁻¹)
      (chain.canonAdj isLeaf σ) = chain.canonAdj isLeaf σ' := by
  rw [canonAdj_eq_labelledAdj chain isLeaf σ hσ,
      canonAdj_eq_labelledAdj chain isLeaf σ' hσ', relabelMatrix_labelledAdj]
  have hmul : Colouring.rankPerm _ hσ' * (Colouring.rankPerm _ hσ)⁻¹
        * Colouring.rankPerm _ hσ = Colouring.rankPerm _ hσ' := by
    rw [mul_assoc, inv_mul_cancel, mul_one]
  rw [hmul]

/-- The discreteness proof for a branch's warm-refined colouring at a leaf, derived
exactly as `canonAdj` derives it (so the rank permutations match definitionally). -/
theorem branch_discrete {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k)
    (isLeaf : chain.IsLeaf) (σ : DirAssignment P₀ chain.D) :
    Discrete (warmRefine adj σ.σ chain.χι) :=
  Discrete.of_samePartition
    (samePartition.symm (DirAssignment.samePartition_chain chain σ)) isLeaf

/-- **The forced candidate twist** for decision `(a, b)` on branch `σ` at a leaf: the rank
rebasing carrying `σ`'s canonical leaf labels to the flipped branch's. Always realises the
flip (`candidateTwist_realizesFlip`); the only open question is whether it is an
automorphism (`twistWitness_of_isAut`). -/
noncomputable def candidateTwist {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k)
    (isLeaf : chain.IsLeaf) (σ : DirAssignment P₀ chain.D)
    (a b : Fin n) (ha : a ∈ chain.D) (hb : b ∈ chain.D) : Equiv.Perm (Fin n) :=
  Colouring.rankPerm _ (branch_discrete chain isLeaf (σ.flipPair a b ha hb))
    * (Colouring.rankPerm _ (branch_discrete chain isLeaf σ))⁻¹

/-- **The candidate always realises the flip.** Instance of `canonAdj_rebase` at
`σ' = flipPair σ`. The construction is forced — no choice, no ambiguity. -/
theorem candidateTwist_realizesFlip {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k)
    (isLeaf : chain.IsLeaf) (σ : DirAssignment P₀ chain.D)
    (a b : Fin n) (ha : a ∈ chain.D) (hb : b ∈ chain.D) :
    RealizesFlip chain isLeaf σ (candidateTwist chain isLeaf σ a b ha hb) a b ha hb :=
  canonAdj_rebase chain isLeaf σ (σ.flipPair a b ha hb)
    (branch_discrete chain isLeaf σ) (branch_discrete chain isLeaf (σ.flipPair a b ha hb))

/-- **Determinacy.** The candidate is the *unique* permutation aligning `σ`'s rank labels
to the flipped branch's (`t * rankPerm π_σ = rankPerm π_flip`). So twist discovery is a
deterministic function of iso-invariant rank data — the iso-invariance gate (§15 gap 2)
at the leaf level. (Other permutations may *also* realise the flip — they differ from the
candidate by an automorphism of `adj` — but the construction canonically picks this one.) -/
theorem candidateTwist_unique {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k)
    (isLeaf : chain.IsLeaf) (σ : DirAssignment P₀ chain.D)
    (a b : Fin n) (ha : a ∈ chain.D) (hb : b ∈ chain.D)
    (t : Equiv.Perm (Fin n))
    (h : t * Colouring.rankPerm _ (branch_discrete chain isLeaf σ)
       = Colouring.rankPerm _ (branch_discrete chain isLeaf (σ.flipPair a b ha hb))) :
    t = candidateTwist chain isLeaf σ a b ha hb := by
  rw [candidateTwist, ← h, mul_assoc, mul_inv_cancel, mul_one]

/-- **The oracle reduces to verification.** When the forced candidate verifies as an
automorphism (the §4.5 edge-check), it yields a complete `TwistWitness` — the decided
pair, the candidate, its `IsAut` proof, and the (always-true) `RealizesFlip`. Twist
*discovery* is thus a single decidable check on the canonical candidate. -/
noncomputable def twistWitness_of_isAut {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k)
    (isLeaf : chain.IsLeaf) (σ : DirAssignment P₀ chain.D)
    (a b : Fin n) (ha : a ∈ chain.D) (hb : b ∈ chain.D)
    (hAut : IsAut (candidateTwist chain isLeaf σ a b ha hb) adj) :
    TwistWitness chain isLeaf σ where
  a := a
  b := b
  ha := ha
  hb := hb
  t := candidateTwist chain isLeaf σ a b ha hb
  isAut := hAut
  realizes := candidateTwist_realizesFlip chain isLeaf σ a b ha hb

open Classical in
/-- **The canonical twist oracle.** Parameterised only by an abstracted *pair selector*
(which decision to resolve — C#-side, soundness-irrelevant). For the selected pair it
computes the forced candidate and returns it **iff** it verifies as an automorphism. A
fully concrete `LinearOracleSpec`: the construction is determined, the only runtime choice
is the edge-check. -/
noncomputable def canonicalTwistOracle
    (selectPair : ∀ {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) (_ : chain.IsLeaf)
      (_σ : DirAssignment P₀ chain.D),
      Option (Σ' (a : Fin n) (b : Fin n), a ∈ chain.D ∧ b ∈ chain.D)) :
    LinearOracleSpec adj P₀ χι₀ sel :=
  twistOracle (fun {_} chain isLeaf σ =>
    (selectPair chain isLeaf σ).bind (fun s =>
      if h : IsAut (candidateTwist chain isLeaf σ s.1 s.2.1 s.2.2.1 s.2.2.2) adj then
        some (twistWitness_of_isAut chain isLeaf σ s.1 s.2.1 s.2.2.1 s.2.2.2 h)
      else none))

/-- `canonicalTwistOracle` satisfies `LeafTwistSpec` — it is a `twistOracle`, so the
soundness discharge of B2.1 applies directly. Every twist it returns is a verified
automorphism relating `σ`'s leaf to the flipped branch `σ' = flipPair σ`. -/
theorem canonicalTwistOracle_leafTwist
    (selectPair : ∀ {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) (_ : chain.IsLeaf)
      (_σ : DirAssignment P₀ chain.D),
      Option (Σ' (a : Fin n) (b : Fin n), a ∈ chain.D ∧ b ∈ chain.D)) :
    LinearOracleSpec.LeafTwistSpec (canonicalTwistOracle selectPair) :=
  twistOracle_leafTwist _

/-! ## §L.3 — Abelian structure (B2.4, partial)

The "abelian" in *abelian-stripping*: the per-decision twists form an
**elementary-abelian `Z₂^d`** action. Two facts:

* **Involution** (`candidateTwist_flip_inv`): the twist resolving the *flip-back*
  (`flipPair σ → σ`) is the inverse of the twist resolving the flip (`σ → flipPair σ`).
  Since `flipPair` is an involution (`flipPair_idempotent`), each decision contributes a
  `Z₂`. If the twist verifies as an automorphism, its inverse does too — the decision is
  a genuine `Z₂` symmetry, consistently in both directions.
* **Commuting** — already proved at the `DirAssignment` level: `flipPair_comm` shows
  flips on disjoint decided pairs commute. So the residual generated by the twists is
  `Z₂^d` (one generator per coupled component), the abelian regime of
  `chain-descent-calculator.md` §6.

Lifting these to "`{twists}` generate an elementary-abelian *subgroup* `N ≤ Aut(G)`",
hence the `N ⋊ Q` decomposition (tractable-buildout §0), needs the group object —
Part A. The `canonForm` lex-min tie (§8.2 step 3 — a descent guided by the oracle reaches
the brute-force lex-min) needs the descent-with-pruning model and is the remaining larger
piece of B2. -/

/-- **The twist is a `Z₂` involution at the twist level.** The forced candidate for the
flip-back equals the inverse of the forced candidate for the flip. Together with
`DirAssignment.flipPair_comm` (commuting flips) this is the elementary-abelian `Z₂^d`
structure of the residual. -/
theorem candidateTwist_flip_inv {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k)
    (isLeaf : chain.IsLeaf) (σ : DirAssignment P₀ chain.D)
    (a b : Fin n) (ha : a ∈ chain.D) (hb : b ∈ chain.D) :
    candidateTwist chain isLeaf (σ.flipPair a b ha hb) a b ha hb
      = (candidateTwist chain isLeaf σ a b ha hb)⁻¹ := by
  simp only [candidateTwist, mul_inv_rev, inv_inv, DirAssignment.flipPair_idempotent]

end ChainDescent
