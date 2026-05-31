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

The linear oracle exposes a **hidden abelian symmetry** at an *apparent decision*: a
size-2 target cell `{a,b}` 1-WL can't separate, whose two branches are `σ` (= "`a<b`")
and `flipPair σ a b` (= "`b<a`"). When the twist verifies, the two branches are
equivalent — `{a,b}` was a true symmetry 1-WL couldn't see, not a genuine decision.
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
- **Completeness on CFI:** "a `ConfigSwap` exists" = a swapping automorphism (`g a = b`,
  `g b = a`) = `OrbitPartition adj P S a b` at the decision node = **cells-are-orbits at the
  node** = the cascade oracle's localization obligation. The **reduction is landed** (`§L.8`):
  the closed `Z₂`-twin-swap instance (`configSwap_of_swap`) + the capstones reducing oracle
  effectiveness to `ConfigSwapRecoverable`. Its bounded-depth half (`recoverableByDepth_cfi`)
  is **proved**; the residual is (a) the **general gadget twist** (non-transposition `g`,
  needs Stage-3 `Aut(CFI)` = `hwit`) and (b) the **decision-node-depth** bridging
  (**cascade-1b**) — open-but-not-GI∈P and **shared with the cascade oracle**. **(BUILT the
  reduction — see §4/§5.)**

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

- **M1c Approach C, step 3 — the cascade-1b bridge** (`LinearOracle.lean` `§L.8`).
  **`configSwap_of_aut`** (the *general* constructor, added 2026-05-31): **any** swapping
  automorphism `g` (`g a = b`, `g b = a`) that fixes `χι` and preserves `σ.σ` *off the flip
  pair* (`σ.σ (g v)(g u) = σ.σ v u` for `(v,u) ∉ {(a,b),(b,a)}`) *is* a `ConfigSwap` — `g` need
  **not** be a transposition; it may move the whole coupled component (the CFI gadget twist).
  The flip-pair cells are exactly where `flipPair` negates and `g` co-swaps, compensating via
  antisymmetry. This **removes the config-swap packaging from the open content**: once the
  gadget twist `g` + its off-pair `σ`-action are in hand, the `ConfigSwap` is built with no
  rank-alignment — `hwit` plugs straight in. **`configSwap_of_swap`** is now a thin
  transposition specialisation (σ-cell-coherence = off-pair preservation for a transposition);
  the `Z₂` twin-swap, simplest genuine abelian decision (real proof content: swap case-analysis
  + antisymmetry). **`ConfigSwapRecoverable`** (every leaf decision admits a config-swap = the
  linear oracle's decision-node recoverability) + capstones
  **`canonAdj_eq_of_configSwapRecoverable`** / **`realizableFlip_of_configSwapRecoverable`**
  reduce oracle effectiveness to that one hypothesis. The reduction is *landed*: a swapping
  automorphism (`g a = b`, `g b = a`) is an `OrbitPartition` witness specialised to the size-2
  cell, so this unifies linear-oracle completeness with the cascade oracle's localization.

Earlier scaffolding still standing (`LinearOracle.lean` `§L.1–L.6`): `RealizesFlip`,
`TwistWitness`, `twistOracle`/`canonicalTwistOracle` + `LeafTwistSpec` discharge (soundness),
`candidateTwist`(`_realizesFlip`/`_unique`), `isAut_candidateTwist_iff_aligned`,
`canonicalTwistOracle_isSome_iff`, the §L.6 relativized-completeness scaffold
(`AbelianSufficiency`, `AbelianSufficiencyHolds`, `oracleFires_of_abelianSufficiency`).

---

## 5. Step 3 — BUILT (the reduction) + what remains (the named nut)

Step 3 wired "a `ConfigSwap` exists for a CFI decision" to the swapping-automorphism /
orbit-recovery picture. **The reduction landed** (`§L.8`, axiom-clean):

- **The swap-vs-map mismatch is resolved** the way §5 anticipated: `configSwap_of_swap`
  builds the full `swapsConfig` config relation from a *swapping* automorphism (`g a = b`,
  `g b = a`) plus σ-cell-coherence (`σ.σ a w = σ.σ b w` off the pair), proven by a direct
  case-analysis using `flipPair`'s definition + `σ.antisym` (no need to weaken `ConfigSwap`).
  The closed instance is the **transposition** (`g` fixes everything off `{a,b}`) — the `Z₂`
  twin-swap, simplest genuine abelian decision.
- **The existence target is named** as `ConfigSwapRecoverable` (every leaf decision admits a
  config-swap) and the **capstones** (`canonAdj_eq_of_configSwapRecoverable`,
  `realizableFlip_of_configSwapRecoverable`) reduce oracle effectiveness to it. This is the
  linear-oracle analog of `AbelianSufficiencyHolds`, and — since a swapping automorphism *is*
  an `OrbitPartition adj P S a b` witness specialised to the size-2 cell — it **unifies
  linear-oracle completeness with the cascade oracle's localization** (the doc's goal).
- **Twin bridge landed (2026-05-31).** `configSwap_of_twin` (`§L.8`) closes the genuine-twin
  `Z₂` decision class via the *same* twin hypothesis and the *same* transposition witness as the
  cascade oracle: an **(adj, σ)-twin** decision pair (adjacency-twin on a simple graph +
  σ-cell-coherent, `χι a = χι b`) ⟹ `ConfigSwap`, by feeding `configSwap_of_swap` the shared lemma
  `CascadeOracle.isAut_swap_of_twin`. LinearOracle now `import`s `ChainDescent.CascadeOracle`.
  Linear-oracle analogue of `cellsAreOrbits_of_twin_cells` — **both oracles fire on the same twin
  class through one shared lemma**, at decision-node depth, no `|Sᶜ|` bound, no rank-alignment.
  - **IMPORTANT scope correction (2026-05-31): this twin class is NOT CFI.** `CFI(H)` has no twins
    (`CFI.cfi_triangle_no_twins`, `native_decide`; general: unique bridge partner per endpoint,
    subset neighbourhoods encode the subset) — CFI's `Z₂` is a global gadget-flip involution, not a
    transposition. So the twin bridge does **not** discharge CFI; it covers the complementary
    genuine-twin / module class. CFI still needs remaining-point-1 below (the general
    non-transposition gadget twist via `configSwap_of_swap`). Remaining-point-2 (decision-node
    depth) is reduced only for the twin/module class, not for CFI.

**What remains (the named nut, NOT a `sorry`):** `configSwapRecoverable_of_cfi : IsCFI adj →
ConfigSwapRecoverable`, which has two open pieces, both shared:

1. **The general gadget twist.** Real CFI's resolving `g` moves the *whole* coupled component
   — it is **not** a transposition, so `configSwap_of_swap`'s `hgfix` (fix off `{a,b}`) does
   not apply. **The config-swap packaging is now done in general** (`configSwap_of_aut`,
   2026-05-31): drop `hgfix`, replace `hcoh` by "`g` preserves `σ.σ` off the flip pair" — so
   the *only* remaining content is **constructing** `g` and knowing its off-pair `σ`-action,
   which needs the deferred Stage-3 `Aut(CFI) ≅ Z₂^β ⋊ Aut(H)` machinery (`CFI.lean`) = the
   **same `hwit` as Tier-3a B1**. Once `hwit` yields `g`, `configSwap_of_aut` closes the bridge
   with no further rank-alignment.
2. **Decision-node depth (cascade-1b).** The witness is needed where `a,b` still share a cell,
   not at `theorem_1_HOR_cfi`'s discretizing depth — the intermediate-node → discretizing-depth
   bridge, **open but not GI∈P**, **shared with the cascade oracle** (`cascade-oracle.md` §2:
   1a proved, 1b open).

Net: the genuine open content is now exactly `hwit` (gadget twist) + cascade-1b — both shared,
neither GI∈P, neither the rank-alignment. Discharge for odd-degree CFI routes through
`theorem_1_HOR_cfi_oddDeg` ([`CFI.lean`](../GraphCanonizationProofs/ChainDescent/CFI.lean),
axiom-free) once those are in place.

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
