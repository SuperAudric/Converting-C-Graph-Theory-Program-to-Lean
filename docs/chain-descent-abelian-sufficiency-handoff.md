# Handoff — abelian-sufficiency / linear-oracle completeness on CFI

**Status (2026-05-31): active Lean work.** This doc lets a cold reader pick up the
in-flight proof that the **linear oracle is complete on CFI** (it fires whenever it
should). It records the approach, the alternates, and what is built vs. open.

Authoritative companions: [`chain-descent-linear-oracle.md`](./chain-descent-linear-oracle.md)
§8.2 (the retargeting), [`chain-descent-cascade-oracle.md`](./chain-descent-cascade-oracle.md)
§2/§4.3 (the shared completeness gap). Lean lives in
[`GraphCanonizationProofs/ChainDescent/LinearOracle.lean`](../GraphCanonizationProofs/ChainDescent/LinearOracle.lean)
(`§L.1–L.7b`) on top of [`ChainDescent.lean`](../GraphCanonizationProofs/ChainDescent.lean).

---

## 1. The problem, in one paragraph

The linear oracle resolves an **abelian genuine decision**: a size-2 target cell `{a,b}`
1-WL can't separate, whose two branches are `σ` (= "`a<b`") and `flipPair σ a b` (= "`b<a`").
At a leaf both branches refine to **discrete** colourings; relabelling `adj` by colour-rank
gives each branch's canonical leaf matrix `canonAdj σ` / `canonAdj flip`. **Soundness** of
the oracle is fully proved (`§L.1–L.2`). The open question is **completeness on CFI**: does
the oracle *fire* (prune the redundant branch) on every CFI decision? Firing requires a
*verified twist*. This doc is the discharge of that for the CFI class.

Why it matters: firing on every CFI decision ⟹ the descent collapses CFI to a single path
⟹ polynomial CFI (the C# already shows this empirically; this is the Lean proof).

---

## 2. The key conceptual finding (read this before touching the code)

There are **two inequivalent twists**, and the choice decides everything:

- **Rank-space** `candidateTwist = π_flip · π_σ⁻¹` (where `π_σ`, `π_flip` are the leaves'
  rank permutations). This is what `§L.2` models. It *always* realizes the flip
  (`candidateTwist_realizesFlip`), but `IsAut candidateTwist adj` is the **rank-alignment
  nut** — see below.
- **Vertex-space** `g = π_flip⁻¹ · π_σ` (the path-fixing automorphism; for CFI it is the
  gadget parity-flip twist). This is what the **C# actually verifies** (confirmed in
  [`TwistConstruction.cs`](../GraphCanonizationProject/TwistConstruction.cs): it builds a
  vertex permutation by colour-matching and checks `IsAutomorphism` on `adj`). `IsAut g adj`
  is **trivially true when the decision is a real symmetry** — `g` *is* the gadget automorphism.

They are conjugate: `candidateTwist = π_σ · g⁻¹ · π_σ⁻¹` (proved: `candidateTwist_eq_conjugate`).
So `IsAut candidateTwist adj` asks whether the **`π_σ`-conjugate** of a genuine automorphism is
again an automorphism — the conjugation gap. It always lands in `Aut(canonAdj σ) = π_σ·Aut(adj)·π_σ⁻¹`
but escaping to `Aut(adj)` is not automatic; abstractly it is **provably not closable** (it has
counter-models) and is the formal shadow of Babai's split-or-Johnson wall.

**Conclusion that drives the plan:** model completeness via the **vertex** twist `g`
(= the cascade oracle's `OrbitPartition` automorphism), not the rank-space candidate. This
*sidesteps the rank-alignment nut* and reduces CFI firing to **orbit recovery** — which is
already proved for odd-degree CFI.

---

## 3. The plan (Approach C) and the alternates

**Chosen: Approach C — completeness via the vertex path-fixing automorphism.**
A pruning certificate is a `ConfigSwap`: an automorphism `g` of `adj` that fixes the initial
colouring `χι` and carries `σ.σ` onto `(flipPair σ).σ`. Then:
- **Soundness:** `ConfigSwap ⟹ canonAdj σ = canonAdj flip` (the branches give the identical
  canonical leaf), so pruning the flip branch loses nothing. **(BUILT — see §4.)**
- **Completeness on CFI:** "a `ConfigSwap` exists" = `OrbitPartition adj P S a b` at the
  decision node = **cells-are-orbits at the node** = the cascade oracle's localization
  obligation. Its bounded-depth half (`recoverableByDepth_cfi`) is **proved**; the
  intermediate-node bridging (**cascade-1b**) is open-but-not-GI∈P and **shared with the
  cascade oracle**. **(NEXT — see §5.)**

Alternates considered and rejected:
- **A — push the rank-space rank-alignment** (`IsAut (π_σ·g⁻¹·π_σ⁻¹) adj` for CFI). The
  irreducible conjugation nut; also needs a Stage-3 explicit-twist slice. High risk.
- **B — extract a swap from orbit recovery + the abelian Z₂ structure.** Gets `g a = b`;
  still rank-space for firing; subsumed by C.
- **D — `decide` on a concrete tiny CFI.** Off-style (the project is abstract-structural;
  `warmRefine`-to-discreteness isn't `decide`-friendly).

---

## 4. What is BUILT (all axiom-clean: `[propext, Classical.choice, Quot.sound]`; full build 1132 jobs)

Milestones, in dependency order:

- **M0 — `refineStep` concretized** (`ChainDescent.lean`, ~the old `axiom refineStep` site).
  Was an axiom specifying only the *partition* (`refineStep_iff`); the colour *order* was
  unspecified, which made `candidateTwist`'s value — hence abelian-sufficiency — *independent
  of the axioms* (counter-models). Now a concrete `def`:
  `refineStep adj P χ v := Encodable.encode (sigKey adj P χ v)`, with
  `sigKey = χ v :: Multiset.sort ((signature adj P χ v).map encTuple) (·≤·)` (the C#'s
  `WarmPartition.RefineRound`: own colour, then sorted encoded signature; `POE.toNat`:
  less<unknown<greater). `refineStep_iff` is now a **theorem**. Helpers: `POE.toNat`(`_injective`),
  `encTuple`(`_injective`), `sigKey`, `sigKey_eq_iff`. **Payoff: `refineStep`/`refineStep_iff`
  left the axiom basis project-wide** (`warm_6_2` is now `[propext, Classical.choice, Quot.sound]`).
  Design note: *encode-as-colour*, not rank-by-List-lex — `<` on `List ℕ` has an instance
  diamond (core `List.lt` vs Mathlib's lex). Partition is byte-identical to the C#; the cell-id
  *order* is a fixed canonical encoding (no theorem depends on it).
  New imports: `Mathlib.Data.Multiset.Sort`, `Mathlib.Data.Nat.Pairing`, `Mathlib.Logic.Equiv.List`.

- **M1a — cross-config transport** (`ChainDescent.lean` `§16.2b`, right after
  `warmRefine_invariant_of_isAut`). `signature_transport`, `sigKey_transport`,
  `refineStep_transport`, `iterate_refineStep_transport`, **`warmRefine_transport`**: if `g ∈
  Aut(adj)` carries `(P₁,χ₁)` to `(P₂,χ₂)` (`P₂ (g·)(g·) = P₁`, `χ₂∘g = χ₁`) then
  `warmRefine adj P₂ χ₂ (g v) = warmRefine adj P₁ χ₁ v`. The value-level generalisation of the
  `*_invariant_of_isAut` chain — newly provable *because* `refineStep` is concrete (unfold to
  `encode (sigKey …)`, reindex the signature multiset by `g`).

- **M1b — the reduction** (`LinearOracle.lean` `§L.7`). `ConfigSwap` (structure: `g`, `isAut`,
  `fixesχι`, `swapsConfig`), `vertexRank_comp` (`vertexRank (χ∘g) v = vertexRank χ (g v)`),
  `configSwap_rankPerm` (`π_σ = π_flip·g`) / `_flip` (`π_flip = π_σ·g⁻¹`),
  **`candidateTwist_eq_conjugate`** (`candidateTwist = π_σ·g⁻¹·π_σ⁻¹`),
  `isAut_candidateTwist_iff_conjugate` (the rank-space firing obligation = the conjugation nut).

- **M1c Approach C, steps 1–2 — vertex-model soundness** (`LinearOracle.lean` `§L.7b`).
  **`canonAdj_eq_of_configSwap`** (a `ConfigSwap` ⟹ `canonAdj σ = canonAdj flip`) and
  **`realizableFlip_of_configSwap`** (⟹ `RealizableFlip`, identity witness). The faithful
  C# soundness: pruning rests on a *real* automorphism, no rank-alignment.

Earlier scaffolding still standing (`LinearOracle.lean` `§L.1–L.6`): `RealizesFlip`,
`TwistWitness`, `twistOracle`/`canonicalTwistOracle` + `LeafTwistSpec` discharge (soundness),
`candidateTwist`(`_realizesFlip`/`_unique`), `isAut_candidateTwist_iff_aligned`,
`canonicalTwistOracle_isSome_iff`, the §L.6 relativized-completeness scaffold
(`AbelianSufficiency`, `AbelianSufficiencyHolds`, `oracleFires_of_abelianSufficiency`).

---

## 5. What still needs to be BUILT — step 3 (the open frontier)

**Wire "a `ConfigSwap` exists for a CFI decision" to orbit recovery.** Concretely:

1. **Define the existence target** and connect it to the cascade machinery:
   `ConfigSwap`-exists ⟸ `OrbitPartition adj P S a b` ⟸ `CascadeOracle.CellsAreOrbits adj P S`
   (in [`CascadeOracle.lean`](../GraphCanonizationProofs/ChainDescent/CascadeOracle.lean);
   see `OrbitRecoverableAt`, `orbitRecoverableAt_iff_cellsAreOrbits`, `recoverableByDepth_cfi`).

2. **Reconcile two mismatches** (both flagged; neither is the deep nut):
   - `ConfigSwap.swapsConfig` is the *full* config relation `(flipPair σ).σ (g·)(g·) = σ.σ`,
     which (as worked out) needs `g` to **swap** `a,b` — whereas `OrbitPartition` gives only
     `g a = b`. Either weaken `ConfigSwap` to a path-fixing-`g a=b` form (re-checking that
     `canonAdj_eq_of_configSwap` still goes through — it used `swapsConfig` via
     `warmRefine_transport`), or obtain the swap from the abelian Z₂ structure (the cell is
     size 2). **Decide this first** — it shapes the `ConfigSwap` interface.
   - The automorphism is needed at the **decision-node depth** (where `a,b` still share a
     cell), not at `theorem_1_HOR_cfi`'s **discretizing depth** (where they're separated). The
     gap between them is exactly **cascade-1b** (intermediate-node → discretizing-depth
     reconstruction) — **open but not GI∈P**, and **shared with the cascade oracle**
     (`cascade-oracle.md` §2: its 1a half is proved, 1b open). This is where the genuine
     remaining content sits; it is NOT a `sorry` to insert — name it and reduce to it.

3. **Discharge for odd-degree CFI** via `theorem_1_HOR_cfi_oddDeg`
   ([`CFI.lean`](../GraphCanonizationProofs/ChainDescent/CFI.lean), axiom-free) once the
   node-depth/1b reconciliation is in place.

Net: step 3 **unifies the linear oracle's completeness with the cascade oracle's localization**.
The genuine open nut is cascade-1b (shared, not GI∈P), *not* the rank-alignment.

---

## 6. Lean gotchas already hit (save time)

- `refineStep` is now a `def` — use the `refineStep_iff` **theorem**; downstream partition
  proofs are unchanged.
- `<` on `List ℕ` is an instance diamond — don't rank by List-lex; encode to `ℕ`.
- `IsAut.symm h : IsAut g.symm adj`; `g⁻¹` is defeq `g.symm` but not syntactic — bind
  `have hinv : IsAut cs.g⁻¹ adj := IsAut.symm cs.isAut` so `rw` matches.
- `ext v` on an `Equiv.Perm` equality **over-applies** into `Fin.val` (coerces to `ℕ`); use
  `apply Equiv.ext; intro v` to stop at the `Fin n` level.
- `labelledAdj π adj` is defeq `relabelMatrix π adj.adj` but `rw` won't auto-close it — finish
  with an explicit `rfl`.

---

## 7. Pointers

- **Lean:** `LinearOracle.lean` (`§L.1–L.7b`); `ChainDescent.lean` (refineStep concretization;
  `§16.2b` transport; `OrbitPartition` ~L3473; `theorem_1_HOR_at_depth` ~L3732);
  `CascadeOracle.lean` (`CellsAreOrbits`, `recoverableByDepth_cfi`); `CFI.lean`
  (`IsCFI'`, `OddDegree`, `theorem_1_HOR_cfi_oddDeg`).
- **Index:** [`PublicTheoremIndex.md`](../GraphCanonizationProofs/PublicTheoremIndex.md)
  `§L.7`/`§L.7b` (this work), `§L.6` (relativized completeness scaffold).
- **Memory:** `project_refinestep_concretized_2026-05-30.md` (M0 + M1a/b/c progress, full detail),
  `project_linear_oracle_spec_2026-05-28.md` (§L.6 retargeting + the B2/M1–M4 plan),
  `project_cascade_oracle_spec_2026-05-28.md` (the shared cascade-1b frontier).
- **Build:** `cd GraphCanonizationProofs && lake build`. Check axioms with
  `#print axioms <name>` (target: `[propext, Classical.choice, Quot.sound]`).
