import ChainDescent
import ChainDescent.CascadeOracle
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
private theorem relabelMatrix_labelledAdj (t s : Equiv.Perm (Fin n)) :
    relabelMatrix t (labelledAdj s adj) = labelledAdj (t * s) adj := by
  funext i j
  simp only [relabelMatrix, labelledAdj]
  rw [show (t * s).symm i = s.symm (t.symm i) by
        rw [Equiv.Perm.mul_def, Equiv.symm_trans_apply],
      show (t * s).symm j = s.symm (t.symm j) by
        rw [Equiv.Perm.mul_def, Equiv.symm_trans_apply]]

/-- `canonAdj` is `labelledAdj` of the rank permutation. Holds for *any* discreteness
proof (the rank permutation is proof-irrelevant), so `rfl`. -/
private theorem canonAdj_eq_labelledAdj {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k)
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
private theorem branch_discrete {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k)
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

/-! ## §L.4 — Completeness (effectiveness): when does the oracle fire?

Soundness (§L.1–L.2) says: *if* the forced candidate verifies, pruning is sound.
Completeness is the converse-flavoured question — does the oracle fire **whenever it
should**, i.e. whenever the decision is a genuine symmetry? The answer is sharp and
matches the design boundary (`chain-descent-calculator.md` §6):

* The oracle fires **iff the forced candidate is an automorphism**
  (`canonicalTwistOracle_isSome_iff`), equivalently iff a *rank-aligned* automorphism
  exists (`isAut_candidateTwist_iff_aligned`).
* When it fires, the two branches are **genuinely `Aut(adj)`-equivalent** — pruning is
  justified by a real automorphism, not bookkeeping (`realizableFlip_of_isAut_candidateTwist`).
* Firing is **`Z₂`-direction-consistent**: pruning `σ → flip` forces pruning
  `flip → σ` (`candidateTwist_flipBack_isAut`).

**The completeness boundary (why this is not unconditional).** A genuine automorphism `g`
realising the flip need only agree with the *rank-aligned* candidate up to
`Aut(canonAdj σ)` — a conjugate of `Aut(adj)`. So "the branches are `Aut`-equivalent"
does **not** in general imply "the *forced* candidate is an automorphism": that holds
exactly when the decision is **abelian** (the unique-candidate / `Z₂` regime). For a
non-abelian residual the forced candidate fails the edge-check and the oracle does not
fire — the budget then flags. This is precisely Babai's split-or-Johnson boundary
(calculator §6). The remaining content — *forced candidate ∈ Aut(adj)* for genuine
abelian decisions, via the `warm_6_2` rank machinery — is the abelian-sufficiency lemma
(the §8.2 step-3 / orbit-recovery connection), the open core of B2's completeness. -/

/-- The forced candidate satisfies the rank-alignment equation `candidate · π_σ = π_flip`
(definitional; the inverse cancels). The algebraic heart of the determinacy. -/
private theorem candidateTwist_mul_rankPerm {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k)
    (isLeaf : chain.IsLeaf) (σ : DirAssignment P₀ chain.D)
    (a b : Fin n) (ha : a ∈ chain.D) (hb : b ∈ chain.D) :
    candidateTwist chain isLeaf σ a b ha hb
        * Colouring.rankPerm _ (branch_discrete chain isLeaf σ)
      = Colouring.rankPerm _ (branch_discrete chain isLeaf (σ.flipPair a b ha hb)) := by
  rw [candidateTwist, inv_mul_cancel_right]

/-- **Firing characterisation (algebraic).** The forced candidate is an automorphism
**iff** some automorphism is rank-aligned (`g · π_σ = π_flip`). Forward: the candidate
itself. Backward: determinacy (`candidateTwist_unique`) forces `g = candidate`. So the
whole completeness question is "does a rank-aligned automorphism exist?" -/
theorem isAut_candidateTwist_iff_aligned {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k)
    (isLeaf : chain.IsLeaf) (σ : DirAssignment P₀ chain.D)
    (a b : Fin n) (ha : a ∈ chain.D) (hb : b ∈ chain.D) :
    IsAut (candidateTwist chain isLeaf σ a b ha hb) adj
      ↔ ∃ g : Equiv.Perm (Fin n), IsAut g adj
          ∧ g * Colouring.rankPerm _ (branch_discrete chain isLeaf σ)
            = Colouring.rankPerm _ (branch_discrete chain isLeaf (σ.flipPair a b ha hb)) := by
  constructor
  · intro h
    exact ⟨_, h, candidateTwist_mul_rankPerm chain isLeaf σ a b ha hb⟩
  · rintro ⟨g, hg, heq⟩
    rwa [candidateTwist_unique chain isLeaf σ a b ha hb g heq] at hg

/-- **The decision is a genuine `Aut(adj)` symmetry**: some automorphism realises the
flip (carries `σ`'s leaf to the flipped branch's). The graph-intrinsic statement that
the two branches are isomorphic — what pruning *should* require. -/
def RealizableFlip {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) (isLeaf : chain.IsLeaf)
    (σ : DirAssignment P₀ chain.D) (a b : Fin n) (ha : a ∈ chain.D) (hb : b ∈ chain.D) :
    Prop :=
  ∃ g : Equiv.Perm (Fin n), IsAut g adj ∧ RealizesFlip chain isLeaf σ g a b ha hb

/-- **Firing is semantically justified.** When the forced candidate verifies, the two
branches are genuinely `Aut(adj)`-equivalent (the candidate itself is the witnessing
automorphism). So a pruning the oracle performs reflects a real graph symmetry — not a
labelling artefact. (The converse — every real symmetry is *caught* — fails outside the
abelian regime; see the boundary discussion above.) -/
theorem realizableFlip_of_isAut_candidateTwist {k : Nat}
    (chain : SpineChain adj P₀ χι₀ sel k) (isLeaf : chain.IsLeaf)
    (σ : DirAssignment P₀ chain.D) (a b : Fin n) (ha : a ∈ chain.D) (hb : b ∈ chain.D)
    (h : IsAut (candidateTwist chain isLeaf σ a b ha hb) adj) :
    RealizableFlip chain isLeaf σ a b ha hb :=
  ⟨candidateTwist chain isLeaf σ a b ha hb, h,
    candidateTwist_realizesFlip chain isLeaf σ a b ha hb⟩

/-- **The oracle fires iff the forced candidate is an automorphism.** Given the pair
selector returns `(a, b)`, `canonicalTwistOracle` returns `some` exactly when the forced
candidate passes the §4.5 edge-check. The entire completeness question is this one
decidable predicate. -/
theorem canonicalTwistOracle_isSome_iff {k : Nat}
    (selectPair : ∀ {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) (_ : chain.IsLeaf)
      (_σ : DirAssignment P₀ chain.D),
      Option (Σ' (a : Fin n) (b : Fin n), a ∈ chain.D ∧ b ∈ chain.D))
    (chain : SpineChain adj P₀ χι₀ sel k) (isLeaf : chain.IsLeaf)
    (σ : DirAssignment P₀ chain.D) (a b : Fin n) (ha : a ∈ chain.D) (hb : b ∈ chain.D)
    (hsel : selectPair chain isLeaf σ = some ⟨a, b, ha, hb⟩) :
    (canonicalTwistOracle selectPair chain isLeaf σ).isSome
      ↔ IsAut (candidateTwist chain isLeaf σ a b ha hb) adj := by
  simp only [canonicalTwistOracle, twistOracle, Option.isSome_map, hsel, Option.bind_some]
  by_cases h : IsAut (candidateTwist chain isLeaf σ a b ha hb) adj
  · simp [h]
  · simp [h]

/-- **Firing is `Z₂`-direction-consistent.** If the forced candidate for `σ → flip`
verifies, then the forced candidate for the flip-back `flip → σ` (its inverse,
`candidateTwist_flip_inv`) also verifies. So the oracle prunes both directions of a
genuine `Z₂` decision consistently — a completeness/coherence property of the abelian
regime. -/
theorem candidateTwist_flipBack_isAut {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k)
    (isLeaf : chain.IsLeaf) (σ : DirAssignment P₀ chain.D)
    (a b : Fin n) (ha : a ∈ chain.D) (hb : b ∈ chain.D)
    (h : IsAut (candidateTwist chain isLeaf σ a b ha hb) adj) :
    IsAut (candidateTwist chain isLeaf (σ.flipPair a b ha hb) a b ha hb) adj := by
  rw [candidateTwist_flip_inv]
  exact IsAut.symm h

/-! ## §L.5 — Toward abelian sufficiency (partial)

The open core of completeness (§L.4): *the forced candidate is an automorphism for a
genuine abelian decision*. This section makes provable progress.

**Why the leaf hides the structure.** At a leaf both branches are **discrete**, so
`warm_6_2`'s *partition* equality (`flipPair_partition_invariant`) is **vacuous** there
— both partitions are all-singletons. The content lives entirely in the *rank order*.
The reindexing lemma `rankPerm_comp` makes the consequence precise: relabelling a
colouring **conjugates** its rank permutation. So if the flip-colouring were merely
`σ`-colouring relabelled by an automorphism `g` (the colouring-level symmetry), the
candidate would be a *conjugate* of `g` by `rankPerm π_σ` — **not** `g`, and a conjugate
by a non-automorphism need not be an automorphism. This is the exact reason
colouring-alignment is insufficient and the forced candidate needs *rank*-alignment
(C2) — which the gadget twist supplies. That gadget-level rank-alignment is the
remaining research content.

**What is provable now:** (1) `rankPerm_comp`, the reindexing infrastructure; (2) the
**absorbed-decision** instance — when the flip leaves the leaf rank permutation
unchanged, the candidate is the *identity* automorphism, so the oracle fires (the most
degenerate genuine abelian symmetry: the two branches give the identical canonical
leaf). -/

-- `rankPerm_comp` relocated to `ChainDescent.lean` (after `end Colouring`) so the
-- cascade oracle's `colourMatchPerm` (M-B) can consume it; still in scope via import.

/-- **Absorbed-decision sufficiency.** When the two branches induce the **same leaf rank
permutation**, the forced candidate is the identity — a trivially genuine automorphism —
so the oracle fires. This is the degenerate end of the abelian regime: the decision is
absorbed by refinement (the branches produce the identical canonical leaf, `canonAdj σ =
canonAdj flip`), and the realizing symmetry is the identity. -/
theorem candidateTwist_eq_one_of_rankPerm_eq {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k)
    (isLeaf : chain.IsLeaf) (σ : DirAssignment P₀ chain.D)
    (a b : Fin n) (ha : a ∈ chain.D) (hb : b ∈ chain.D)
    (h : Colouring.rankPerm _ (branch_discrete chain isLeaf (σ.flipPair a b ha hb))
       = Colouring.rankPerm _ (branch_discrete chain isLeaf σ)) :
    candidateTwist chain isLeaf σ a b ha hb = 1 := by
  rw [candidateTwist, h, mul_inv_cancel]

/-- The absorbed decision fires: the forced candidate (the identity) is an automorphism. -/
private theorem isAut_candidateTwist_of_rankPerm_eq {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k)
    (isLeaf : chain.IsLeaf) (σ : DirAssignment P₀ chain.D)
    (a b : Fin n) (ha : a ∈ chain.D) (hb : b ∈ chain.D)
    (h : Colouring.rankPerm _ (branch_discrete chain isLeaf (σ.flipPair a b ha hb))
       = Colouring.rankPerm _ (branch_discrete chain isLeaf σ)) :
    IsAut (candidateTwist chain isLeaf σ a b ha hb) adj := by
  rw [candidateTwist_eq_one_of_rankPerm_eq chain isLeaf σ a b ha hb h]
  exact IsAut.refl

/-! ## §L.6 — Relativized completeness (the retargeting)

§L.4 showed the oracle fires ⟺ the forced candidate is an automorphism, and that the
*general* completeness statement ("fires whenever the two branches are isomorphic")
cannot hold: a realizing automorphism agrees with the forced candidate only up to
`Aut(canonAdj σ)` — a *conjugate* of `Aut(adj)`, pinned by `rankPerm_comp` — so for a
**non-abelian** residual the candidate genuinely misses, which is the
`chain-descent-calculator.md` §6 split-or-Johnson wall *by design*.

The fix mirrors the a-priori cascade oracle's **Phase B** (`CascadeOracle.lean`): do not
target the general statement; **relativize** completeness to the recoverable/abelian class
and reduce it to orbit recovery. This is the *same* gap the cascade oracle carries
(`construct → verify → harvest`, the "[FIRM behavior, CONJECTURAL characterization]"
boundary, `chain-descent-cascade-oracle.md` §4.3) and the *same* resolution.

The scaffold:

* `RankAligned` — the algebraic firing condition (a rank-aligned automorphism exists);
  `isAut_candidateTwist_iff_rankAligned` is the interface (= `isAut_candidateTwist_iff_aligned`).
* `AbelianSufficiency` — the **per-decision relativized target**: *if* the flip is a real
  symmetry (`RealizableFlip`) *then* the forced candidate verifies. FALSE in the non-abelian
  regime (the wall), the claim to discharge on the abelian/cascade class.
* `oracleFires_of_abelianSufficiency` — the capstone ("what suffices"): given
  `AbelianSufficiency` and a real symmetry, the oracle fires. Linear-oracle analog of
  cascade's `cascadeComplete_of_localization`.
* `abelianSufficiency_of_rankPerm_eq` — a **non-vacuous closed instance** (the absorbed
  decision), validating the scaffold.
* `AbelianSufficiencyHolds` — the graph-level predicate (every leaf decision is
  abelian-sufficient), the discharge target. The remaining open obligation is
  `abelianSufficiencyHolds_of_cfi : IsCFI adj → AbelianSufficiencyHolds adj`, provable
  downstream (`CFI.lean`) by wiring to the axiom-free `theorem_1_HOR_cfi_oddDeg` — the
  gadget rank-alignment, **the same nut as Tier-3a B1's path-fixing witness** (`hwit`).
  Not proven here (and not a `sorry`: it is the conjecturally-true content of the abelian
  regime, isolated as a single named statement). -/

/-- **The algebraic firing condition: a rank-aligned automorphism exists.** Names the
right-hand side of `isAut_candidateTwist_iff_aligned`. The oracle fires exactly when this
holds (`isAut_candidateTwist_iff_rankAligned`). -/
def RankAligned {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) (isLeaf : chain.IsLeaf)
    (σ : DirAssignment P₀ chain.D) (a b : Fin n) (ha : a ∈ chain.D) (hb : b ∈ chain.D) :
    Prop :=
  ∃ g : Equiv.Perm (Fin n), IsAut g adj
    ∧ g * Colouring.rankPerm _ (branch_discrete chain isLeaf σ)
      = Colouring.rankPerm _ (branch_discrete chain isLeaf (σ.flipPair a b ha hb))

/-- **Interface.** The forced candidate is an automorphism ⟺ `RankAligned`. So the entire
completeness question is "does a rank-aligned automorphism exist?" (= `isAut_candidateTwist_iff_aligned`,
restated against the named predicate). -/
theorem isAut_candidateTwist_iff_rankAligned {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k)
    (isLeaf : chain.IsLeaf) (σ : DirAssignment P₀ chain.D)
    (a b : Fin n) (ha : a ∈ chain.D) (hb : b ∈ chain.D) :
    IsAut (candidateTwist chain isLeaf σ a b ha hb) adj
      ↔ RankAligned chain isLeaf σ a b ha hb :=
  isAut_candidateTwist_iff_aligned chain isLeaf σ a b ha hb

/-- **The per-decision relativized completeness target (abelian-sufficiency).** *If* the
decision `(a, b)` is a real symmetry — some automorphism realises the flip — *then* the
forced candidate verifies as an automorphism, so the oracle fires. This is the abelian
direction of completeness. It is **false in general** (the non-abelian wall: a realizing
automorphism need not be rank-aligned), and it is precisely the claim to discharge on the
abelian / cascade class. -/
def AbelianSufficiency {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) (isLeaf : chain.IsLeaf)
    (σ : DirAssignment P₀ chain.D) (a b : Fin n) (ha : a ∈ chain.D) (hb : b ∈ chain.D) :
    Prop :=
  RealizableFlip chain isLeaf σ a b ha hb
    → IsAut (candidateTwist chain isLeaf σ a b ha hb) adj

/-- **Capstone — what suffices.** Given abelian-sufficiency for the selected decision and a
genuine realizing symmetry, the oracle fires. The linear-oracle analog of cascade's
`cascadeComplete_of_localization`: it reduces the oracle's effectiveness to the single
relativized obligation `AbelianSufficiency`. -/
theorem oracleFires_of_abelianSufficiency {k : Nat}
    (selectPair : ∀ {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) (_ : chain.IsLeaf)
      (_σ : DirAssignment P₀ chain.D),
      Option (Σ' (a : Fin n) (b : Fin n), a ∈ chain.D ∧ b ∈ chain.D))
    (chain : SpineChain adj P₀ χι₀ sel k) (isLeaf : chain.IsLeaf)
    (σ : DirAssignment P₀ chain.D) (a b : Fin n) (ha : a ∈ chain.D) (hb : b ∈ chain.D)
    (hsel : selectPair chain isLeaf σ = some ⟨a, b, ha, hb⟩)
    (habs : AbelianSufficiency chain isLeaf σ a b ha hb)
    (hreal : RealizableFlip chain isLeaf σ a b ha hb) :
    (canonicalTwistOracle selectPair chain isLeaf σ).isSome := by
  rw [canonicalTwistOracle_isSome_iff selectPair chain isLeaf σ a b ha hb hsel]
  exact habs hreal

/-- **Non-vacuous closed instance: the absorbed decision is abelian-sufficient.** When the
two branches induce the same leaf rank permutation, the forced candidate is the identity —
an automorphism regardless — so `AbelianSufficiency` holds (its conclusion is true outright,
independent of the `RealizableFlip` hypothesis). The degenerate end of the abelian regime;
it validates the scaffold against a real instance. -/
theorem abelianSufficiency_of_rankPerm_eq {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k)
    (isLeaf : chain.IsLeaf) (σ : DirAssignment P₀ chain.D)
    (a b : Fin n) (ha : a ∈ chain.D) (hb : b ∈ chain.D)
    (h : Colouring.rankPerm _ (branch_discrete chain isLeaf (σ.flipPair a b ha hb))
       = Colouring.rankPerm _ (branch_discrete chain isLeaf σ)) :
    AbelianSufficiency chain isLeaf σ a b ha hb :=
  fun _ => isAut_candidateTwist_of_rankPerm_eq chain isLeaf σ a b ha hb h

/-- **The graph-level discharge target.** Every leaf decision of `adj` is abelian-sufficient.
True for graphs with abelian residual symmetry (CFI); the open obligation
`abelianSufficiencyHolds_of_cfi : IsCFI adj → AbelianSufficiencyHolds adj` is provable
downstream (`CFI.lean`) via `theorem_1_HOR_cfi_oddDeg` — the gadget rank-alignment, the same
content as Tier-3a B1's path-fixing witness. -/
def AbelianSufficiencyHolds : Prop :=
  ∀ {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) (isLeaf : chain.IsLeaf)
    (σ : DirAssignment P₀ chain.D) (a b : Fin n) (ha : a ∈ chain.D) (hb : b ∈ chain.D),
    AbelianSufficiency chain isLeaf σ a b ha hb

/-- **Graph-level capstone.** If `adj` satisfies abelian-sufficiency everywhere, then the
oracle fires at every leaf decision that is a real symmetry. This is the relativized
completeness statement: on the abelian class, the oracle is complete. -/
theorem oracleFires_of_abelianSufficiencyHolds {k : Nat}
    (selectPair : ∀ {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) (_ : chain.IsLeaf)
      (_σ : DirAssignment P₀ chain.D),
      Option (Σ' (a : Fin n) (b : Fin n), a ∈ chain.D ∧ b ∈ chain.D))
    (hholds : AbelianSufficiencyHolds (adj := adj) (P₀ := P₀) (χι₀ := χι₀) (sel := sel))
    (chain : SpineChain adj P₀ χι₀ sel k) (isLeaf : chain.IsLeaf)
    (σ : DirAssignment P₀ chain.D) (a b : Fin n) (ha : a ∈ chain.D) (hb : b ∈ chain.D)
    (hsel : selectPair chain isLeaf σ = some ⟨a, b, ha, hb⟩)
    (hreal : RealizableFlip chain isLeaf σ a b ha hb) :
    (canonicalTwistOracle selectPair chain isLeaf σ).isSome :=
  oracleFires_of_abelianSufficiency selectPair chain isLeaf σ a b ha hb hsel
    (hholds chain isLeaf σ a b ha hb) hreal

/-! ## §L.7 — The CFI bridge (M1b): the forced candidate is a conjugate of a graph automorphism

A **config-swap** for decision `(a, b)` is an automorphism `g` of `adj` that carries
the σ-branch configuration onto the flip-branch configuration — it fixes the initial
colouring `χι` and transforms `σ.σ` into `(flipPair σ).σ`. For CFI this is the gadget
twist swapping the decided pair (its existence is gadget-level content, the M1b
obligation). Given a config-swap, the cross-config transport (`warmRefine_transport`,
§16.2b) forces the two leaf rank permutations to differ by exactly `g`:
`π_σ = π_flip · g`. Hence the forced candidate is the **`π_σ`-conjugate of `g⁻¹`**
(`candidateTwist_eq_conjugate`). This turns the opaque obligation
`IsAut candidateTwist adj` into the concrete, structural
`IsAut (π_σ · g⁻¹ · π_σ⁻¹) adj` — the gadget rank-alignment, the genuine open nut,
now stated via a *real* automorphism rather than a rank-rebasing. -/

-- `vertexRank_comp` relocated to `ChainDescent.lean` (after `end Colouring`);
-- still in scope via import.

/-- A **config-swap** for decision `(a, b)`: a graph automorphism carrying the σ-branch
configuration onto the flip-branch configuration (fixes `χι`, sends `σ.σ` to
`(flipPair σ).σ`). For CFI, the gadget twist swapping the decided pair. -/
structure ConfigSwap {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k)
    (σ : DirAssignment P₀ chain.D) (a b : Fin n) (ha : a ∈ chain.D) (hb : b ∈ chain.D) where
  /-- The swapping automorphism. -/
  g : Equiv.Perm (Fin n)
  /-- It is a graph automorphism. -/
  isAut : IsAut g adj
  /-- It fixes the initial colouring. -/
  fixesχι : ∀ v, chain.χι (g v) = chain.χι v
  /-- It carries `σ.σ` onto `(flipPair σ).σ`. -/
  swapsConfig : ∀ v u, (σ.flipPair a b ha hb).σ (g v) (g u) = σ.σ v u

/-- **The leaf rank permutations differ by exactly `g`.** Cross-config transport
(`warmRefine_transport`) forces `χ_σ = χ_flip ∘ g`, so by the rank reindex
(`vertexRank_comp`), `π_σ = π_flip · g`. The algebraic heart of both the M1b reduction
and the soundness `canonAdj σ = canonAdj flip`. -/
theorem configSwap_rankPerm {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k)
    (isLeaf : chain.IsLeaf) (σ : DirAssignment P₀ chain.D)
    (a b : Fin n) (ha : a ∈ chain.D) (hb : b ∈ chain.D)
    (cs : ConfigSwap chain σ a b ha hb) :
    Colouring.rankPerm _ (branch_discrete chain isLeaf σ)
      = Colouring.rankPerm _ (branch_discrete chain isLeaf (σ.flipPair a b ha hb)) * cs.g := by
  apply Equiv.ext; intro v
  have hfun : (warmRefine adj σ.σ chain.χι)
      = fun u => warmRefine adj (σ.flipPair a b ha hb).σ chain.χι (cs.g u) :=
    funext fun u => (warmRefine_transport cs.isAut cs.swapsConfig cs.fixesχι u).symm
  rw [Equiv.Perm.mul_apply, Colouring.rankPerm_apply, Colouring.rankPerm_apply, hfun]
  exact vertexRank_comp _ cs.g v

/-- `π_flip = π_σ · g⁻¹` — the rearrangement of `configSwap_rankPerm`. -/
private theorem configSwap_rankPerm_flip {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k)
    (isLeaf : chain.IsLeaf) (σ : DirAssignment P₀ chain.D)
    (a b : Fin n) (ha : a ∈ chain.D) (hb : b ∈ chain.D)
    (cs : ConfigSwap chain σ a b ha hb) :
    Colouring.rankPerm _ (branch_discrete chain isLeaf (σ.flipPair a b ha hb))
      = Colouring.rankPerm _ (branch_discrete chain isLeaf σ) * cs.g⁻¹ := by
  rw [configSwap_rankPerm chain isLeaf σ a b ha hb cs, mul_assoc, mul_inv_cancel, mul_one]

/-- **The forced candidate is the `π_σ`-conjugate of `g⁻¹`.** Given a config-swap `g`,
`candidateTwist = π_flip · π_σ⁻¹ = π_σ · g⁻¹ · π_σ⁻¹`. The opaque rank-rebasing is exposed
as the conjugate of a genuine graph automorphism — the M1b reduction. -/
theorem candidateTwist_eq_conjugate {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k)
    (isLeaf : chain.IsLeaf) (σ : DirAssignment P₀ chain.D)
    (a b : Fin n) (ha : a ∈ chain.D) (hb : b ∈ chain.D)
    (cs : ConfigSwap chain σ a b ha hb) :
    candidateTwist chain isLeaf σ a b ha hb
      = Colouring.rankPerm _ (branch_discrete chain isLeaf σ) * cs.g⁻¹
        * (Colouring.rankPerm _ (branch_discrete chain isLeaf σ))⁻¹ := by
  rw [candidateTwist, configSwap_rankPerm_flip chain isLeaf σ a b ha hb cs]

/-- **The reduction.** `IsAut candidateTwist adj` ⟺ `IsAut (π_σ · g⁻¹ · π_σ⁻¹) adj`:
the firing obligation is exactly the gadget rank-alignment (the `π_σ`-conjugate of the
config-swap is a graph automorphism). This is the concrete remaining nut, shared with
Tier-3a B1. -/
theorem isAut_candidateTwist_iff_conjugate {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k)
    (isLeaf : chain.IsLeaf) (σ : DirAssignment P₀ chain.D)
    (a b : Fin n) (ha : a ∈ chain.D) (hb : b ∈ chain.D)
    (cs : ConfigSwap chain σ a b ha hb) :
    IsAut (candidateTwist chain isLeaf σ a b ha hb) adj
      ↔ IsAut (Colouring.rankPerm _ (branch_discrete chain isLeaf σ) * cs.g⁻¹
          * (Colouring.rankPerm _ (branch_discrete chain isLeaf σ))⁻¹) adj := by
  rw [candidateTwist_eq_conjugate chain isLeaf σ a b ha hb cs]

/-! ### §L.7b — Vertex-model soundness: equal canonical leaves

The vertex-space view (matching the C# `TwistConstruction`): a config-swap is an
*actual graph automorphism* carrying one branch's configuration onto the other, so the
two branches produce the **same canonical leaf** — `canonAdj σ = canonAdj flip`. This is
the clean soundness statement (pruning the flip branch loses nothing) and it does **not**
go through the rank-space candidate: it needs only that the config-swap is an
automorphism (`g⁻¹ ∈ Aut(adj)`) and the rank relation `π_flip = π_σ · g⁻¹`. -/

/-- **Equal canonical leaves.** Given a config-swap, both branches of the decision produce
the identical canonical leaf adjacency matrix. (`canonAdj flip = labelledAdj (π_σ · g⁻¹) adj
= labelledAdj π_σ adj` because `g⁻¹` is an automorphism, so relabelling by it is invisible.) -/
theorem canonAdj_eq_of_configSwap {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k)
    (isLeaf : chain.IsLeaf) (σ : DirAssignment P₀ chain.D)
    (a b : Fin n) (ha : a ∈ chain.D) (hb : b ∈ chain.D)
    (cs : ConfigSwap chain σ a b ha hb) :
    chain.canonAdj isLeaf σ = chain.canonAdj isLeaf (σ.flipPair a b ha hb) := by
  have hinv : IsAut cs.g⁻¹ adj := IsAut.symm cs.isAut
  rw [canonAdj_eq_labelledAdj chain isLeaf σ (branch_discrete chain isLeaf σ),
      canonAdj_eq_labelledAdj chain isLeaf (σ.flipPair a b ha hb)
        (branch_discrete chain isLeaf (σ.flipPair a b ha hb)),
      configSwap_rankPerm_flip chain isLeaf σ a b ha hb cs,
      ← relabelMatrix_labelledAdj (Colouring.rankPerm _ (branch_discrete chain isLeaf σ)) cs.g⁻¹,
      labelledAdj_eq_of_isAut hinv]
  rfl

/-- **`RealizableFlip` from a config-swap.** Since the two branches give the identical
canonical leaf, the identity automorphism realises the flip — so the decision is a genuine
`Aut(adj)`-symmetry. This is the vertex-model completeness witness: pruning is justified by
a real automorphism (`cs.g`), with no rank-alignment obligation. -/
theorem realizableFlip_of_configSwap {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k)
    (isLeaf : chain.IsLeaf) (σ : DirAssignment P₀ chain.D)
    (a b : Fin n) (ha : a ∈ chain.D) (hb : b ∈ chain.D)
    (cs : ConfigSwap chain σ a b ha hb) :
    RealizableFlip chain isLeaf σ a b ha hb := by
  refine ⟨1, IsAut.refl, ?_⟩
  show relabelMatrix 1 (chain.canonAdj isLeaf σ) = chain.canonAdj isLeaf (σ.flipPair a b ha hb)
  have h1 : relabelMatrix (1 : Equiv.Perm (Fin n)) (chain.canonAdj isLeaf σ)
      = chain.canonAdj isLeaf σ := by
    funext i j; rfl
  rw [h1, canonAdj_eq_of_configSwap chain isLeaf σ a b ha hb cs]

/-! ## §L.8 — CFI completeness: config-swap from a swapping automorphism (the cascade-1b bridge)

§L.7b gave the vertex-model **soundness**: a `ConfigSwap` ⟹ the two branches give the
identical canonical leaf (`canonAdj_eq_of_configSwap`) ⟹ `RealizableFlip`. This section is the
**completeness** direction — *where a config-swap comes from* — and it reduces that to the
cascade oracle's currency, a **swapping automorphism**: a graph automorphism `g` with
`g a = b`, `g b = a`. That is exactly an `OrbitPartition adj P S a b` witness (an `IsAut`
automorphism mapping `a ↦ b`, `ChainDescent.lean` §16.3) specialised to the size-2 decision
cell `{a, b}`. So this is the linear oracle's half of the **shared cascade-1b** obligation
(`chain-descent-cascade-oracle.md` §2): its bounded-depth recoverability is proved
(`recoverableByDepth_cfi`); obtaining the witness *at the decision-node depth* is the open,
**not-`GI∈P`** bridge.

**What is proved here (closed, axiom-clean):** `configSwap_of_aut` — the *general*
constructor: **any** swapping automorphism `g` (`g a = b`, `g b = a`) that fixes `χι` and
preserves `σ.σ` *off the flip pair* `{(a,b),(b,a)}` *is* a `ConfigSwap`. `g` need **not** be a
transposition: it may move the whole coupled component (the CFI gadget twist). The flip-pair
cells are exactly where `flipPair` negates and `g` co-swaps, so the two compensate via
antisymmetry. `configSwap_of_swap` is the transposition specialisation (the simplest genuine
abelian `Z₂` twin-swap decision: `{a, b}` a true 2-element orbit), and `configSwap_of_twin`
the (adj, σ)-twin instance. With §L.7b these fire the oracle on those classes.

**What stays open (the named nut, not a `sorry`):** *producing* the general CFI gadget twist
`g` and knowing its off-pair `σ`-action. `configSwap_of_aut` removes the config-swap
*packaging* from the open content — once `g` and its `σ`-action are in hand, the `ConfigSwap`
is built with no rank-alignment. What remains is the CFI gadget structure itself: the deferred
Stage-3 `Aut(CFI) ≅ Z₂^β ⋊ Aut(H)` machinery (the same `hwit` as Tier-3a B1), plus producing
`g` at decision-node depth (cascade-1b). Both are isolated as the graph-level hypothesis
`ConfigSwapRecoverable`, which the capstones reduce oracle effectiveness to. -/

/-- **A swapping automorphism that preserves `σ.σ` off the flip pair is a config-swap.**
The *general* config-swap constructor: `g` need only be a graph automorphism that swaps the
pair `a, b` (`g a = b`, `g b = a`), fix the initial colouring (`∀ v, χι (g v) = χι v`), and
preserve the direction assignment *everywhere except the flip-pair cells*
(`σ.σ (g v) (g u) = σ.σ v u` whenever `(v, u) ∉ {(a, b), (b, a)}`). It need **not** be a
transposition — `g` may move the whole coupled component (the CFI gadget twist). The
flip-pair cells are exactly where `flipPair` negates, and `g` co-swaps them via `g a = b`,
`g b = a` + antisymmetry, so the two compensate. This is the entry point the deferred CFI
gadget twist (`hwit`, Stage-3 `Aut(CFI)`) plugs into: once `g` and its off-pair `σ`-action
are known, packaging it as a `ConfigSwap` is *done* — no further rank-alignment. -/
def configSwap_of_aut {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k)
    (σ : DirAssignment P₀ chain.D) (a b : Fin n) (ha : a ∈ chain.D) (hb : b ∈ chain.D)
    (g : Equiv.Perm (Fin n)) (hg : IsAut g adj)
    (hga : g a = b) (hgb : g b = a)
    (hgχ : ∀ v, chain.χι (g v) = chain.χι v)
    (hgpres : ∀ v u, ¬((v = a ∧ u = b) ∨ (v = b ∧ u = a)) → σ.σ (g v) (g u) = σ.σ v u) :
    ConfigSwap chain σ a b ha hb where
  g := g
  isAut := hg
  fixesχι := hgχ
  swapsConfig := by
    have happ : ∀ i j : Fin n, (σ.flipPair a b ha hb).σ i j
        = if (i = a ∧ j = b) ∨ (i = b ∧ j = a) then POE.neg (σ.σ i j) else σ.σ i j :=
      fun _ _ => rfl
    intro v u
    rw [happ]
    by_cases hg2 : (g v = a ∧ g u = b) ∨ (g v = b ∧ g u = a)
    · rw [if_pos hg2]
      rcases hg2 with ⟨hv, hu⟩ | ⟨hv, hu⟩
      · have hvb : v = b := g.injective (hv.trans hgb.symm)
        have hua : u = a := g.injective (hu.trans hga.symm)
        rw [hv, hu, hvb, hua]
        exact (σ.antisym b a).symm
      · have hva : v = a := g.injective (hv.trans hga.symm)
        have hub : u = b := g.injective (hu.trans hgb.symm)
        rw [hv, hu, hva, hub]
        exact (σ.antisym a b).symm
    · rw [if_neg hg2]
      apply hgpres v u
      intro hcontra
      apply hg2
      rcases hcontra with ⟨hv, hu⟩ | ⟨hv, hu⟩
      · rw [hv, hu]; exact Or.inr ⟨hga, hgb⟩
      · rw [hv, hu]; exact Or.inl ⟨hgb, hga⟩

/-- **A σ-cell-coherent transposition automorphism is a config-swap.** The closed `Z₂`
twin-swap instance: if `g` is a graph automorphism that swaps the distinct pair `a, b`,
fixes every other vertex and the initial colouring (`χι a = χι b`), and the pair is
σ-cell-coherent (`σ.σ a w = σ.σ b w` for `w ≠ a, b`), then `g` is a `ConfigSwap`. A thin
specialisation of `configSwap_of_aut`: a transposition fixing `χι a = χι b` automatically
fixes `χι`, and σ-cell-coherence is exactly off-pair `σ`-preservation for a transposition
(the only moved vertices are `a, b`). -/
def configSwap_of_swap {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k)
    (σ : DirAssignment P₀ chain.D) (a b : Fin n) (ha : a ∈ chain.D) (hb : b ∈ chain.D)
    (hab : a ≠ b)
    (g : Equiv.Perm (Fin n)) (hg : IsAut g adj)
    (hga : g a = b) (hgb : g b = a) (hgfix : ∀ v, v ≠ a → v ≠ b → g v = v)
    (hχab : chain.χι a = chain.χι b)
    (hcoh : ∀ w, w ≠ a → w ≠ b → σ.σ a w = σ.σ b w) :
    ConfigSwap chain σ a b ha hb := by
  have hgχ : ∀ v, chain.χι (g v) = chain.χι v := by
    intro v
    by_cases hva : v = a
    · subst hva; rw [hga]; exact hχab.symm
    by_cases hvb : v = b
    · subst hvb; rw [hgb]; exact hχab
    rw [hgfix v hva hvb]
  have hdiag : ∀ x : Fin n, σ.σ x x = POE.unknown := by
    intro x
    have h := σ.antisym x x
    cases hc : σ.σ x x with
    | less => simp only [hc, POE.neg] at h; exact absurd h (by decide)
    | unknown => rfl
    | greater => simp only [hc, POE.neg] at h; exact absurd h (by decide)
  have hcoh' : ∀ w : Fin n, w ≠ a → w ≠ b → σ.σ w a = σ.σ w b := by
    intro w hwa hwb
    rw [σ.antisym w a, σ.antisym w b, hcoh w hwa hwb]
  have hgpres : ∀ v u, ¬((v = a ∧ u = b) ∨ (v = b ∧ u = a)) → σ.σ (g v) (g u) = σ.σ v u := by
    intro v u hne
    by_cases hva : v = a
    · by_cases hub : u = b
      · exact absurd (Or.inl ⟨hva, hub⟩) hne
      · by_cases hua : u = a
        · rw [hva, hua, hga, hdiag b, hdiag a]
        · rw [hva, hga, hgfix u hua hub]; exact (hcoh u hua hub).symm
    · by_cases hvb : v = b
      · by_cases hua : u = a
        · exact absurd (Or.inr ⟨hvb, hua⟩) hne
        · by_cases hub : u = b
          · rw [hvb, hub, hgb, hdiag a, hdiag b]
          · rw [hvb, hgb, hgfix u hua hub]; exact hcoh u hua hub
      · by_cases hua : u = a
        · rw [hgfix v hva hvb, hua, hga]; exact (hcoh' v hva hvb).symm
        · by_cases hub : u = b
          · rw [hgfix v hva hvb, hub, hgb]; exact hcoh' v hva hvb
          · rw [hgfix v hva hvb, hgfix u hua hub]
  exact configSwap_of_aut chain σ a b ha hb g hg hga hgb hgχ hgpres

/-- **A twin decision pair admits a config-swap** — the linear-oracle analogue of the
cascade oracle's `cellsAreOrbits_of_twin_cells`, sharing the *same* twin hypothesis and
the *same* transposition witness (`CascadeOracle.isAut_swap_of_twin`). When the decision
pair `(a, b)` is an **(adj, σ)-twin**: an adjacency-twin (`adj a s = adj b s` for every
other `s`, on a simple graph) *and* a σ-cell-coherent pair (`σ.σ a w = σ.σ b w`), with
`χι a = χι b`, then the transposition `(a b)` is a `ConfigSwap`. The genuine-twin `Z₂`
swap decision resolved without any rank-alignment, at **decision-node depth** (no descent
to discreteness, no `|Sᶜ|` bound), exactly as `cellsAreOrbits_of_twin_cells` is on the
orbit side — the two oracles fire on the same twin class via one shared lemma.

**Scope (corrected 2026-05-31).** This is the **genuine-twin / module** class, **not**
CFI: `CFI(H)` has no twins (`CFI.cfi_triangle_no_twins`), so its `Z₂` is a global
gadget-flip involution and a CFI decision pair is *not* an `(adj, σ)-twin`. CFI fires the
oracle through `configSwap_of_swap` with the *general* (non-transposition, non-`hgfix`)
gadget twist `g`, which is the deferred `configSwapRecoverable_of_cfi` content — not this
lemma. `configSwap_of_twin` is the closed abelian instance for the twin/module class. -/
def configSwap_of_twin {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k)
    (σ : DirAssignment P₀ chain.D) (a b : Fin n) (ha : a ∈ chain.D) (hb : b ∈ chain.D)
    (hab : a ≠ b)
    (hsymm : ∀ x y, adj.adj x y = adj.adj y x) (hloop : ∀ x, adj.adj x x = 0)
    (htwinAdj : ∀ s, s ≠ a → s ≠ b → adj.adj a s = adj.adj b s)
    (hχab : chain.χι a = chain.χι b)
    (hcoh : ∀ w, w ≠ a → w ≠ b → σ.σ a w = σ.σ b w) :
    ConfigSwap chain σ a b ha hb :=
  configSwap_of_swap chain σ a b ha hb hab (Equiv.swap a b)
    (isAut_swap_of_twin hsymm hloop htwinAdj)
    (Equiv.swap_apply_left a b) (Equiv.swap_apply_right a b)
    (fun _ hva hvb => Equiv.swap_apply_of_ne_of_ne hva hvb)
    hχab hcoh

/-- **Decision-node recoverability (the named cascade-1b obligation for the linear oracle).**
Every leaf decision `(a, b)` (distinct pair in the decision set) admits a config-swap. Holds
for the recoverable / abelian class (CFI: every undecided pair is a real symmetry); the open
discharge `configSwapRecoverable_of_cfi : IsCFI adj → ConfigSwapRecoverable` is downstream
content (`CFI.lean`), provable via the gadget twists + `theorem_1_HOR_cfi_oddDeg` — the same
`hwit` as Tier-3a B1, and the decision-node-depth half of cascade-1b. The graph-level analog
of `AbelianSufficiencyHolds`. -/
def ConfigSwapRecoverable : Prop :=
  ∀ {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) (_isLeaf : chain.IsLeaf)
    (σ : DirAssignment P₀ chain.D) (a b : Fin n) (ha : a ∈ chain.D) (hb : b ∈ chain.D),
    a ≠ b → Nonempty (ConfigSwap chain σ a b ha hb)

/-- **Capstone (soundness of pruning).** If `adj` is config-swap-recoverable, then at every
leaf decision the two branches produce the identical canonical leaf — so pruning the flipped
branch loses nothing. Reduces the linear oracle's effectiveness on CFI to the single
`ConfigSwapRecoverable` hypothesis. -/
theorem canonAdj_eq_of_configSwapRecoverable {k : Nat}
    (h : ConfigSwapRecoverable (adj := adj) (P₀ := P₀) (χι₀ := χι₀) (sel := sel))
    (chain : SpineChain adj P₀ χι₀ sel k) (isLeaf : chain.IsLeaf)
    (σ : DirAssignment P₀ chain.D) (a b : Fin n) (ha : a ∈ chain.D) (hb : b ∈ chain.D)
    (hab : a ≠ b) :
    chain.canonAdj isLeaf σ = chain.canonAdj isLeaf (σ.flipPair a b ha hb) := by
  obtain ⟨cs⟩ := h chain isLeaf σ a b ha hb hab
  exact canonAdj_eq_of_configSwap chain isLeaf σ a b ha hb cs

/-- **Capstone (the decision is a real symmetry).** Config-swap-recoverability gives a genuine
realizing automorphism for every leaf decision — the vertex-model completeness statement: on
the recoverable class the oracle's pruning is always justified by a real `Aut(adj)` symmetry,
no rank-alignment needed. -/
theorem realizableFlip_of_configSwapRecoverable {k : Nat}
    (h : ConfigSwapRecoverable (adj := adj) (P₀ := P₀) (χι₀ := χι₀) (sel := sel))
    (chain : SpineChain adj P₀ χι₀ sel k) (isLeaf : chain.IsLeaf)
    (σ : DirAssignment P₀ chain.D) (a b : Fin n) (ha : a ∈ chain.D) (hb : b ∈ chain.D)
    (hab : a ≠ b) :
    RealizableFlip chain isLeaf σ a b ha hb := by
  obtain ⟨cs⟩ := h chain isLeaf σ a b ha hb hab
  exact realizableFlip_of_configSwap chain isLeaf σ a b ha hb cs

/-! ## §L.9 — CFI gadget twist fires the oracle (Phase 6a: wiring the cycle-space flip)

The Stage-3 gadget flip (`CFI.lean §15`, `IsCFI'.cfiFlipAut`) is the **vertex-space twist** the C#
constructs and §2 of the handoff identified as the right completeness witness. Phases 3–5 built it as
a controlled `Aut(adj)` involution with localised support. This section wires it into
`configSwap_of_aut`, giving the concrete statement that **the CFI gadget twist is a valid config-swap**
(no rank-alignment), and reduces `ConfigSwapRecoverable` for CFI to the existence of the right cycle
`F` per decision — the shared, non-`GI∈P` cascade-1b nut.

**What is unconditional here:** that a gadget flip *suffices* — `configSwap_of_cfiFlipAut` proves an
`IsCFI'` gadget twist satisfying the (swap, `χι`-fix, `σ`-off-pair) conditions IS a `ConfigSwap`. This
is the soundness Approach C set out to establish: the genuine `Aut(adj)` symmetry prunes the branch.

**What stays open (the residual = cascade-1b):** that such a flip *exists* for every decision —
isolated as `CFIGadgetFlippable`. Its three per-decision obligations (the flip swaps `(a,b)`, fixes the
leaf colouring `χι`, and carries `σ` off the pair) are exactly the descent-coherence content of
cascade-1b: an even-symmetric cycle through the decision edge, local to the decided gadget. Discharging
them (via partition-invariance for `χι` and locality + σ-cell-coherence for `σ`) is follow-on
groundwork; here they are bundled so the gadget-flip mechanism is committed and the remainder is purely
the cycle's existence. -/

/-- **The CFI gadget twist is a config-swap.** Instantiating `configSwap_of_aut` with the Stage-3
gadget flip `cfiFlipAut F` (an `Aut(adj)` involution by `isAut_cfiFlipAut`): if the flip swaps the
decision pair, fixes the leaf colouring, and carries `σ` off the pair, it is a `ConfigSwap`. The
concrete realisation that the vertex-space gadget twist (the C#'s witness) fires the linear oracle —
no rank-alignment. -/
def configSwap_of_cfiFlipAut (h : IsCFI' adj) {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k)
    (σ : DirAssignment P₀ chain.D) (a b : Fin n) (ha : a ∈ chain.D) (hb : b ∈ chain.D)
    (F : Fin h.m → Fin h.m → Bool) (hEven : ∀ v, (h.H.flipSet F v).card % 2 = 0)
    (hFsymm : ∀ v w, F v w = F w v)
    (hga : h.cfiFlipAut F hEven a = b) (hgb : h.cfiFlipAut F hEven b = a)
    (hgχ : ∀ v, chain.χι (h.cfiFlipAut F hEven v) = chain.χι v)
    (hgpres : ∀ v u, ¬((v = a ∧ u = b) ∨ (v = b ∧ u = a)) →
      σ.σ (h.cfiFlipAut F hEven v) (h.cfiFlipAut F hEven u) = σ.σ v u) :
    ConfigSwap chain σ a b ha hb :=
  configSwap_of_aut chain σ a b ha hb (h.cfiFlipAut F hEven)
    (h.isAut_cfiFlipAut F hEven hFsymm) hga hgb hgχ hgpres

/-- **The CFI gadget-flip recoverability hypothesis (the named cascade-1b residual).** Every leaf
decision `(a, b)` admits an even-symmetric cycle `F` whose Stage-3 gadget flip swaps `(a, b)`, fixes
the leaf colouring, and carries `σ` off the pair. This commits the linear oracle's CFI witness to the
**gadget-flip mechanism** (matching the C#) — the open content is purely the existence of such an `F`
per decision (the cycle through the decision edge, local to the decided gadget), which is cascade-1b. -/
def CFIGadgetFlippable (h : IsCFI' adj) : Prop :=
  ∀ {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) (_isLeaf : chain.IsLeaf)
    (σ : DirAssignment P₀ chain.D) (a b : Fin n) (_ha : a ∈ chain.D) (_hb : b ∈ chain.D),
    a ≠ b →
    ∃ (F : Fin h.m → Fin h.m → Bool) (hEven : ∀ v, (h.H.flipSet F v).card % 2 = 0),
      (∀ v w, F v w = F w v) ∧
      h.cfiFlipAut F hEven a = b ∧ h.cfiFlipAut F hEven b = a ∧
      (∀ v, chain.χι (h.cfiFlipAut F hEven v) = chain.χι v) ∧
      (∀ v u, ¬((v = a ∧ u = b) ∨ (v = b ∧ u = a)) →
        σ.σ (h.cfiFlipAut F hEven v) (h.cfiFlipAut F hEven u) = σ.σ v u)

/-- **`ConfigSwapRecoverable` for CFI, via the gadget flip.** If every CFI leaf decision admits the
right gadget-flip cycle (`CFIGadgetFlippable`), then `adj` is config-swap-recoverable — so the linear
oracle fires on every CFI decision (capstones `canonAdj_eq_of_configSwapRecoverable` /
`realizableFlip_of_configSwapRecoverable`). This is the discharge `configSwapRecoverable_of_cfi`
reduced to its irreducible combinatorial core: the existence of the decision-local even cycle. -/
theorem configSwapRecoverable_of_cfi (h : IsCFI' adj)
    (hflip : CFIGadgetFlippable (P₀ := P₀) (χι₀ := χι₀) (sel := sel) h) :
    ConfigSwapRecoverable (adj := adj) (P₀ := P₀) (χι₀ := χι₀) (sel := sel) := by
  intro k chain isLeaf σ a b ha hb hab
  obtain ⟨F, hEven, hFsymm, hga, hgb, hgχ, hgpres⟩ := hflip chain isLeaf σ a b ha hb hab
  exact ⟨configSwap_of_cfiFlipAut h chain σ a b ha hb F hEven hFsymm hga hgb hgχ hgpres⟩

/-! ### §L.9 follow-on — reducing the config-swap conditions to locality + cell-coherence

`configSwap_of_aut`'s three conditions (swap, `χι`-fix, `σ`-off-pair) entangle the gadget-flip
mechanics with the descent's cell structure. The lemmas below **decouple** them: the σ-off-pair
condition reduces to *σ-cell-coherence* (`a, b` relate identically under `σ` to every other decided
vertex) plus *F-locality* (the flip fixes the decided vertices off `{a,b}`); the `χι`-fix reduces to
*χι-coherence on the F-touched support*. Coherence is the "`{a,b}` is a genuine cell" content the
descent provides (shared with cascade-1b); F-locality is a property of the chosen cycle. The σ
reduction is general (any `g`), reusable beyond CFI. -/

/-- **σ-off-pair preservation from locality (the `hgpres` reduction, general `g`).** Any `g` that
swaps `(a, b)`, fixes every *other* decided vertex (`hgfixD`), preserves the decided set
(`hgD`), and preserves `P₀` (`hP0`) satisfies `configSwap_of_aut`'s off-pair condition — given only
**σ-cell-coherence** at `(a, b)` (`hcoh`). Off the decided set, `agrees_off` + `P₀`-invariance close
it; on it, the coherence case-analysis (as in `configSwap_of_swap`). Decouples the twist mechanics
from the descent-coherence fact `hcoh`. -/
theorem swapsConfig_off_pair_of_local {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k)
    (σ : DirAssignment P₀ chain.D) (a b : Fin n)
    (g : Equiv.Perm (Fin n)) (hga : g a = b) (hgb : g b = a)
    (hgfixD : ∀ x, x ∈ chain.D → x ≠ a → x ≠ b → g x = x)
    (hgD : ∀ x, g x ∈ chain.D ↔ x ∈ chain.D)
    (hcoh : ∀ w, w ≠ a → w ≠ b → σ.σ a w = σ.σ b w)
    (hP0 : ∀ x y, P₀ (g x) (g y) = P₀ x y) :
    ∀ v u, ¬((v = a ∧ u = b) ∨ (v = b ∧ u = a)) → σ.σ (g v) (g u) = σ.σ v u := by
  have hdiag : ∀ x : Fin n, σ.σ x x = POE.unknown := by
    intro x
    have h := σ.antisym x x
    cases hc : σ.σ x x with
    | less => simp only [hc, POE.neg] at h; exact absurd h (by decide)
    | unknown => rfl
    | greater => simp only [hc, POE.neg] at h; exact absurd h (by decide)
  have hcoh' : ∀ w : Fin n, w ≠ a → w ≠ b → σ.σ w a = σ.σ w b := by
    intro w hwa hwb
    rw [σ.antisym w a, σ.antisym w b, hcoh w hwa hwb]
  intro v u hne
  by_cases hvD : v ∈ chain.D
  · by_cases huD : u ∈ chain.D
    · by_cases hva : v = a
      · by_cases hub : u = b
        · exact absurd (Or.inl ⟨hva, hub⟩) hne
        · by_cases hua : u = a
          · rw [hva, hua, hga, hdiag b, hdiag a]
          · rw [hva, hga, hgfixD u huD hua hub]; exact (hcoh u hua hub).symm
      · by_cases hvb : v = b
        · by_cases hua : u = a
          · exact absurd (Or.inr ⟨hvb, hua⟩) hne
          · by_cases hub : u = b
            · rw [hvb, hub, hgb, hdiag a, hdiag b]
            · rw [hvb, hgb, hgfixD u huD hua hub]; exact hcoh u hua hub
        · by_cases hua : u = a
          · rw [hgfixD v hvD hva hvb, hua, hga]; exact (hcoh' v hva hvb).symm
          · by_cases hub : u = b
            · rw [hgfixD v hvD hva hvb, hub, hgb]; exact hcoh' v hva hvb
            · rw [hgfixD v hvD hva hvb, hgfixD u huD hua hub]
    · rw [σ.agrees_off (g v) (g u) (Or.inr (mt (hgD u).mp huD)),
          σ.agrees_off v u (Or.inr huD), hP0]
  · rw [σ.agrees_off (g v) (g u) (Or.inl (mt (hgD v).mp hvD)),
        σ.agrees_off v u (Or.inl hvD), hP0]

/-- **Decided-set preservation for an involutive local swap.** An involution that swaps `(a, b)`
and fixes every other decided vertex maps the decided set to itself, hence preserves membership
(`g x ∈ D ↔ x ∈ D`). The `hgD` input to `swapsConfig_off_pair_of_local`, discharged for the
gadget flip (an involution by `cfiFlipAut_involutive`). -/
theorem preserves_D_of_involutive_local {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k)
    (a b : Fin n) (ha : a ∈ chain.D) (hb : b ∈ chain.D)
    (g : Equiv.Perm (Fin n)) (hinv : Function.Involutive g)
    (hga : g a = b) (hgb : g b = a)
    (hgfixD : ∀ x, x ∈ chain.D → x ≠ a → x ≠ b → g x = x) :
    ∀ x, g x ∈ chain.D ↔ x ∈ chain.D := by
  have hinto : ∀ x, x ∈ chain.D → g x ∈ chain.D := by
    intro x hx
    by_cases hxa : x = a
    · rw [hxa, hga]; exact hb
    · by_cases hxb : x = b
      · rw [hxb, hgb]; exact ha
      · rw [hgfixD x hx hxa hxb]; exact hx
  intro x
  refine ⟨fun hgx => ?_, hinto x⟩
  have := hinto (g x) hgx
  rwa [hinv x] at this

/-- **`χι`-fix from χι-coherence on the F-support (the `hgχ` reduction).** The gadget flip fixes
the leaf colouring `χι` once it does so on the gadgets `F` actually touches — Phase-4 locality
(`cfiFlipAut_eq_self_of_flipSet_empty`) fixes everything in an `F`-free gadget outright. Reduces the
global `hgχ` to χι-coherence on the (small) F-support. -/
theorem cfiFlipAut_fixesχι_of_support (h : IsCFI' adj) {k : Nat}
    (chain : SpineChain adj P₀ χι₀ sel k) (F : Fin h.m → Fin h.m → Bool)
    (hEven : ∀ v, (h.H.flipSet F v).card % 2 = 0)
    (hχsupp : ∀ v, h.H.flipSet F (h.H.gadget (h.e v)) ≠ ∅ →
      chain.χι (h.cfiFlipAut F hEven v) = chain.χι v) :
    ∀ v, chain.χι (h.cfiFlipAut F hEven v) = chain.χι v := by
  intro v
  by_cases hv : h.H.flipSet F (h.H.gadget (h.e v)) = ∅
  · rw [h.cfiFlipAut_eq_self_of_flipSet_empty F hEven hv]
  · exact hχsupp v hv

/-- **The CFI gadget twist is a config-swap, from locality + cell-coherence (the reduced bridge).**
The three `configSwap_of_aut` conditions are replaced by: the flip swaps `(a, b)`; `F` is **D-local**
(its edges avoid the gadgets of decided vertices other than `a, b`); `σ` is **cell-coherent** at
`(a, b)`; `P₀` is automorphism-invariant; and `χι` is coherent on the F-support. The σ-off-pair and
`χι`-fix conditions are then discharged by `swapsConfig_off_pair_of_local` (+ `preserves_D_…`,
Phase-5 `P₀`-preservation) and `cfiFlipAut_fixesχι_of_support`. -/
def configSwap_of_cfiFlipAut_local (h : IsCFI' adj) {k : Nat}
    (chain : SpineChain adj P₀ χι₀ sel k) (σ : DirAssignment P₀ chain.D)
    (a b : Fin n) (ha : a ∈ chain.D) (hb : b ∈ chain.D)
    (F : Fin h.m → Fin h.m → Bool) (hEven : ∀ v, (h.H.flipSet F v).card % 2 = 0)
    (hFsymm : ∀ v w, F v w = F w v)
    (hga : h.cfiFlipAut F hEven a = b) (hgb : h.cfiFlipAut F hEven b = a)
    (hFlocalD : ∀ x, x ∈ chain.D → x ≠ a → x ≠ b →
      h.H.flipSet F (h.H.gadget (h.e x)) = ∅)
    (hcoh : ∀ w, w ≠ a → w ≠ b → σ.σ a w = σ.σ b w)
    (hP0inv : ∀ (π : Equiv.Perm (Fin n)), IsAut π adj → ∀ x y, P₀ (π x) (π y) = P₀ x y)
    (hχsupp : ∀ v, h.H.flipSet F (h.H.gadget (h.e v)) ≠ ∅ →
      chain.χι (h.cfiFlipAut F hEven v) = chain.χι v) :
    ConfigSwap chain σ a b ha hb :=
  let g := h.cfiFlipAut F hEven
  have hgfixD : ∀ x, x ∈ chain.D → x ≠ a → x ≠ b → g x = x :=
    fun x hx hxa hxb => h.cfiFlipAut_eq_self_of_flipSet_empty F hEven (hFlocalD x hx hxa hxb)
  have hgD := preserves_D_of_involutive_local chain a b ha hb g
    (h.cfiFlipAut_involutive F hEven) hga hgb hgfixD
  configSwap_of_cfiFlipAut h chain σ a b ha hb F hEven hFsymm hga hgb
    (cfiFlipAut_fixesχι_of_support h chain F hEven hχsupp)
    (swapsConfig_off_pair_of_local chain σ a b g hga hgb hgfixD hgD hcoh
      (h.cfiFlipAut_preserves_P F hEven hFsymm hP0inv))

/-- **The reduced CFI gadget-flip recoverability hypothesis.** Per decision: an even-symmetric `F`
that is **D-local** (avoids decided gadgets off `{a,b}`), whose flip swaps `(a, b)`, with `σ`
cell-coherent and `χι` coherent on the F-support — plus the global `P₀`-invariance. The conditions
are now the descent-coherence / cycle-locality facts (the cascade-1b content), not the opaque
`configSwap_of_aut` package. -/
def CFIGadgetFlippableLocal (h : IsCFI' adj) : Prop :=
  ∀ {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) (_isLeaf : chain.IsLeaf)
    (σ : DirAssignment P₀ chain.D) (a b : Fin n) (_ha : a ∈ chain.D) (_hb : b ∈ chain.D),
    a ≠ b →
    ∃ (F : Fin h.m → Fin h.m → Bool) (hEven : ∀ v, (h.H.flipSet F v).card % 2 = 0),
      (∀ v w, F v w = F w v) ∧
      h.cfiFlipAut F hEven a = b ∧ h.cfiFlipAut F hEven b = a ∧
      (∀ x, x ∈ chain.D → x ≠ a → x ≠ b → h.H.flipSet F (h.H.gadget (h.e x)) = ∅) ∧
      (∀ w, w ≠ a → w ≠ b → σ.σ a w = σ.σ b w) ∧
      (∀ v, h.H.flipSet F (h.H.gadget (h.e v)) ≠ ∅ →
        chain.χι (h.cfiFlipAut F hEven v) = chain.χι v)

/-- **`ConfigSwapRecoverable` for CFI via the reduced (locality + coherence) hypothesis.** Same
discharge as `configSwapRecoverable_of_cfi`, but consuming the decoupled `CFIGadgetFlippableLocal`
— the open content is now F-locality + descent cell-coherence, the cascade-1b shape. -/
theorem configSwapRecoverable_of_cfi_local (h : IsCFI' adj)
    (hP0inv : ∀ (π : Equiv.Perm (Fin n)), IsAut π adj → ∀ x y, P₀ (π x) (π y) = P₀ x y)
    (hflip : CFIGadgetFlippableLocal (P₀ := P₀) (χι₀ := χι₀) (sel := sel) h) :
    ConfigSwapRecoverable (adj := adj) (P₀ := P₀) (χι₀ := χι₀) (sel := sel) := by
  intro k chain isLeaf σ a b ha hb hab
  obtain ⟨F, hEven, hFsymm, hga, hgb, hFlocalD, hcoh, hχsupp⟩ :=
    hflip chain isLeaf σ a b ha hb hab
  exact ⟨configSwap_of_cfiFlipAut_local h chain σ a b ha hb F hEven hFsymm hga hgb
    hFlocalD hcoh hP0inv hχsupp⟩

/-! ### §L.9 (C1b.1) — the CFI glue: parity-pair decisions

C1b.0 settled that the gadget flip swaps a parity-pair `e^0_{v→w}/e^1_{v→w}` exactly when `{v,w} ∈ F`
(`cfiFlipAut_swaps_endpointVertex`). C1b.1 uses this to reduce `CFIGadgetFlippableLocal` to the
**parity-pair** form: the open content becomes "every decision is a parity-pair edge admitting a
D-local even cycle through it, with cell-coherence" — the swap obligation is now discharged in advance.
The remaining pieces are C1b.2 (the cycle exists in `H`) and C1b.3 (decisions *are* parity-pairs + the
descent provides coherence). The complementary **subset-pair** decision class (`cfiFlip_subset`) is the
parallel case, deferred. -/

/-- **Parity-pair decision recoverability** (the reduced cascade-1b hypothesis). Every leaf decision
`(a, b)` is the parity-pair of some base edge `{v, w}` (`a = e^{b₀}_{v→w}`, `b = e^{¬b₀}_{v→w}`) and
admits an even-symmetric cycle `F` with `{v,w} ∈ F` (so the flip swaps the pair), confined to `F`-free
gadgets off `{a,b}`, with `σ` cell-coherent and `χι` coherent on the F-support. The explicit-edge form
of `CFIGadgetFlippableLocal` — the swap is no longer an obligation (it is `cfiFlipAut_swaps_endpointVertex`),
only the cycle's existence and the coherence remain. -/
def CFIParityDecisionFlippable (h : IsCFI' adj) : Prop :=
  ∀ {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) (_isLeaf : chain.IsLeaf)
    (σ : DirAssignment P₀ chain.D) (a b : Fin n) (_ha : a ∈ chain.D) (_hb : b ∈ chain.D),
    a ≠ b →
    ∃ (v w : Fin h.m) (hw : w ∈ h.H.neighbors v) (b₀ : Bool)
      (F : Fin h.m → Fin h.m → Bool) (hEven : ∀ x, (h.H.flipSet F x).card % 2 = 0),
      a = h.endpointVertex hw b₀ ∧ b = h.endpointVertex hw (!b₀) ∧
      (∀ p q, F p q = F q p) ∧ F v w = true ∧
      (∀ x, x ∈ chain.D → x ≠ a → x ≠ b → h.H.flipSet F (h.H.gadget (h.e x)) = ∅) ∧
      (∀ u, u ≠ a → u ≠ b → σ.σ a u = σ.σ b u) ∧
      (∀ x, h.H.flipSet F (h.H.gadget (h.e x)) ≠ ∅ → chain.χι (h.cfiFlipAut F hEven x) = chain.χι x)

/-- **The CFI glue (C1b.1).** A parity-pair decision recoverable graph is gadget-flip recoverable:
`CFIParityDecisionFlippable → CFIGadgetFlippableLocal`. The two swap conjuncts of the latter's body are
discharged by `cfiFlipAut_endpointVertex` + `F v w = true` (C1b.0); the rest passes through. Composing
with `configSwapRecoverable_of_cfi_local` gives the linear oracle's CFI completeness from the
parity-pair form. -/
theorem cfiGadgetFlippableLocal_of_parity (h : IsCFI' adj)
    (hpar : CFIParityDecisionFlippable (P₀ := P₀) (χι₀ := χι₀) (sel := sel) h) :
    CFIGadgetFlippableLocal (P₀ := P₀) (χι₀ := χι₀) (sel := sel) h := by
  intro k chain isLeaf σ a b ha hb hab
  obtain ⟨v, w, hw, b₀, F, hEven, hEqa, hEqb, hFsymm, hFvw, hFlocalD, hcoh, hχsupp⟩ :=
    hpar chain isLeaf σ a b ha hb hab
  refine ⟨F, hEven, hFsymm, ?_, ?_, hFlocalD, hcoh, hχsupp⟩
  · rw [hEqa, hEqb, h.cfiFlipAut_endpointVertex, hFvw]; cases b₀ <;> rfl
  · rw [hEqb, hEqa, h.cfiFlipAut_endpointVertex, hFvw]; cases b₀ <;> rfl

end ChainDescent
