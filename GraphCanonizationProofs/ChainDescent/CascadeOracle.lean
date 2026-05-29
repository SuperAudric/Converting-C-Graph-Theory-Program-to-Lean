import ChainDescent

/-!
# §C — A-priori cascade oracle: interface and soundness

The Lean contract for the **a-priori cascade oracle**
(`docs/chain-descent-cascade-oracle.md`), paralleling the linear-oracle interface
of §15.8 (`LinearOracleSpec` / `LeafTwistSpec`). As there, the *discovery*
algorithm — the lockstep single-path recursion — lives on the C# side (built +
measured 2026-05-28); the Lean side supplies the interface and the spec it must
meet. The plan is `docs/chain-descent-cascade-oracle-lean-brief.md`.

This file is **Phase A** (soundness / validity), depending only on the core
`ChainDescent` development:

* `CascadeOracleSpec` — the interface type. Unlike `LinearOracleSpec` it is **not**
  leaf-gated: the cascade oracle harvests at *internal* target cells, so it takes a
  `SpineChain` at any level `k` (the committed path `D = chain.D`) and two candidate
  representatives `v w`, returning an optional verified automorphism.
* `CascadeOracleSpec.some_isAut` — subtype-level soundness (automatic).
* `CascadeOracleSpec.OrbitMapSpec` — the validity predicate (the `LeafTwistSpec`
  analogue): a returned merge witnesses an `Aut_D` orbit relation `OrbitPartition`.
  This is the soundness anchor that justifies pruning.
* `CascadeOracleSpec.merged_sameCell` — a certified merge never crosses 1-WL cells.

Completeness on the cascade class (CFI / schemes) is **Phase B** — wiring
`OrbitMapSpec` to `theorem_1_HOR_at_depth` and its axiom-free specialisations
(`theorem_1_HOR_cfi_oddDeg`, `theorem_2_HOR_concrete_rank_two_J_singleton`),
appended later. General-class completeness and verdict iso-invariance are the
explicitly open obligations (Phase C).

**P-invariance seam.** `OrbitPartition` requires the witness to preserve `P`
(not just `adj`); `OrbitMapSpec` therefore requires it too. This mirrors the
`hP_invariant` hypothesis of `theorem_2_HOR_concrete_rank_two_J_singleton` — a
known seam, discharged operationally (the descent builds `P` only from path
individualisations, which a path-fixing automorphism preserves).
-/

namespace ChainDescent

/-- **Cascade-oracle interface type.** Given a node — a `SpineChain` at level `k`,
whose accumulated `chain.D` is the committed individualisation path — and two
candidate representatives `v w`, return either `none` (no orbit map certified) or a
verified automorphism `π` of `adj` (bundled with its `IsAut` proof).

Parallel to `LinearOracleSpec` (§15.8) but **internal-node**, not leaf-gated: the
cascade oracle harvests *before* branching at a target cell, so there is no
`chain.IsLeaf` argument. The implementation is the C# lockstep single-path
recursion; the Lean side is the interface + spec. -/
def CascadeOracleSpec {n : Nat} (adj : AdjMatrix n) (P₀ : PMatrix n)
    (χι₀ : Colouring n) (sel : Colouring n → Finset (Fin n)) : Type :=
  ∀ {k : Nat}, SpineChain adj P₀ χι₀ sel k → (v w : Fin n) →
    Option { π : Equiv.Perm (Fin n) // IsAut π adj }

namespace CascadeOracleSpec

variable {n : Nat} {adj : AdjMatrix n} {P₀ : PMatrix n}
  {χι₀ : Colouring n} {sel : Colouring n → Finset (Fin n)}

/-- **Soundness (subtype-level).** When the oracle returns `some result`, the
returned permutation is an automorphism — automatic from the bundled subtype
(mirrors `LinearOracleSpec.some_isAut`). -/
theorem some_isAut (oracle : CascadeOracleSpec adj P₀ χι₀ sel)
    {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) (v w : Fin n)
    {result : { π : Equiv.Perm (Fin n) // IsAut π adj }}
    (_ : oracle chain v w = some result) :
    IsAut result.val adj :=
  result.property

/-- **Cascade-orbit validity** (the `LeafTwistSpec` analogue). When the oracle
merges `v` and `w` (returns `some`), they lie in the same `Aut_D` orbit: there is
an automorphism of `adj` preserving `chain.P`, fixing `chain.D` pointwise, and
sending `v` to `w` (`OrbitPartition`). This is the soundness anchor that justifies
pruning `w`'s branch as isomorphic to `v`'s.

Like `LeafTwistSpec`, this *constrains* the oracle (it is the spec the discharge
must meet); the C# verification gate establishes it operationally. -/
def OrbitMapSpec (oracle : CascadeOracleSpec adj P₀ χι₀ sel) : Prop :=
  ∀ {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) (v w : Fin n)
    (result : { π : Equiv.Perm (Fin n) // IsAut π adj }),
    oracle chain v w = some result →
    OrbitPartition adj chain.P chain.D v w

/-- A valid cascade oracle never merges across 1-WL cells: a certified merge of
`v, w` forces them into the same `warmRefine` cell (under the individualisation of
the committed path `chain.D`). Immediate from `OrbitPartition.subset_warmRefine` —
the merge is consistent with the partition the descent branches on. -/
theorem merged_sameCell {oracle : CascadeOracleSpec adj P₀ χι₀ sel}
    (hvalid : OrbitMapSpec oracle)
    {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) (v w : Fin n)
    (result : { π : Equiv.Perm (Fin n) // IsAut π adj })
    (h : oracle chain v w = some result) :
    warmRefine adj chain.P (individualizedColouring n chain.D) v =
      warmRefine adj chain.P (individualizedColouring n chain.D) w :=
  OrbitPartition.subset_warmRefine (hvalid chain v w result h)

end CascadeOracleSpec

end ChainDescent
