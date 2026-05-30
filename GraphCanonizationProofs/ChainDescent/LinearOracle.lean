import ChainDescent

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

end ChainDescent
