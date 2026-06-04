# HANDOFF — Part A / cross-branch harvest / CFI coverage (temporary, archive when consumed)

> **STATUS: TEMPORARY HANDOFF (2026-06-04).** Brings a fresh agent up to speed to continue the
> **Part A → A2-complete → CFI-coverage** work thread immediately. **Archive/delete this file once the next
> worker has internalized it** — the authoritative, durable record is
> [`chain-descent-schreier-sims.md`](./chain-descent-schreier-sims.md) (Part A doc) +
> [`PublicTheoremIndex.md`](../GraphCanonizationProofs/PublicTheoremIndex.md) (theorem list with line
> numbers) + [`chain-descent-declassing.md`](./chain-descent-declassing.md) (current architecture). This
> doc is a *pointer + working-notes* layer, not a source of truth; where it disagrees with the Lean source,
> the source wins.

---

## 0. One-paragraph orientation

Graph-canonization research project (C# + Lean). The Lean side proves the *chain-descent canonizer* correct.
The current thread builds **Part A** — the cross-branch automorphism-harvest / stabilizer-chain object — which
the *conservation finding* (`lockstep_disc_imp_stab_trivial`, `CascadeOracle.lean`) established as **required**
for multi-step hidden symmetry (CFI gauge twists, `tw ≥ 2`): the within-cell discretizing oracle provably
*cannot* harvest a multi-step moved orbit, so it must be harvested **cross-branch**, folding verified
automorphisms into a residual group object. We have built that object and its soundness+completeness seams
abstractly, and are now instancing it for **CFI** graphs. Read [`chain-descent-schreier-sims.md`](./chain-descent-schreier-sims.md)
in full first — it is the authoritative Part A doc and this handoff mirrors its staging.

**If you read nothing else:** the immediate next target is **CFI-cov.3 core** (§4 below) — the
`Aut(CFI(H)) ≅ Z₂^β ⋊ Aut(H)` *structure theorem* plus per-level orbit-coverage, yielding `cfi_coversOrbits`.
Everything before it is landed and axiom-clean.

---

## 1. Build / verify / doc-sync conventions (read before touching anything)

- **Full build:** `cd /workspace && bash scripts/build.sh` (serial, 8 modules, ~15–30 s; avoids RAM thrash).
- **One module:** `cd /workspace/GraphCanonizationProofs && lake build ChainDescent.CFI` (or `.Cascade`,
  `.CascadeOracle`, …).
- **⚠️ cwd GOTCHA:** the shell cwd resets to `/workspace` between `Bash` calls. `lake` must run from
  `/workspace/GraphCanonizationProofs`; `scripts/build.sh` must run from `/workspace`. A bare `lake build`
  from `/workspace` fails with "no configuration file".
- **Axiom-clean check** (the project's quality bar — every theorem must be axiom-clean):
  ```
  cat > /tmp/ax.lean <<'EOF'
  import ChainDescent.Cascade   -- or ChainDescent.CFI
  open ChainDescent
  #print axioms <theorem_name>
  EOF
  cd /workspace/GraphCanonizationProofs && lake env lean /tmp/ax.lean
  ```
  **Clean = `[propext, Classical.choice, Quot.sound]`** (the standard basis). Anything else (a stray
  `sorry`/axiom) is a regression.
- **Theorem index regen** (after adding/renaming declarations):
  `cd /workspace/GraphCanonizationProofs && python3 ../scripts/GenerateTheoremIndexes.py rewrite --with-line-numbers`.
  It prints "newly added" rows (Description cell `—`) to hand-fill, and is idempotent. **Renamed theorems
  leave a stale row** ("no matching source decl") that you must delete by hand. The 6 pre-existing
  `Decidable …`/`Fintype …` stale rows are expected — ignore them.
- **Doc sync after each landed increment** (the established rhythm): regenerate + fill `PublicTheoremIndex.md`;
  update `docs/chain-descent-schreier-sims.md` (its STATUS block + §7 stage entry); update the Part A pointer
  in `MEMORY.md` (`/home/node/.claude/projects/-workspace/memory/MEMORY.md`).
- **Module dependency order:** `ChainDescent` (root) → `Saturation`/`CFI`/`Scheme` → `CascadeOracle` (imports
  CFI) → `LinearOracle`/`Group` → **`Cascade` (last; imports CascadeOracle+Group+Saturation, so transitively
  sees CFI)**. ⇒ CFI-level facts go in `CFI.lean`; anything needing `StabilizerAt`/`CoversOrbits` (defined in
  `Cascade.lean`) goes in `Cascade.lean`.

---

## 2. Lean proof gotchas hit this session (save yourself the time)

- **`rw` "motive is not type correct"** when the goal carries proof-bearing dependent terms (a `Sigma`/`Subtype`
  whose proof depends on the thing you're rewriting — e.g. CFI vertices `⟨v, ⟨S, hS⟩⟩` where `hS : S ∈ …`).
  **Fix:** prove the underlying *data* equality (the `Finset`/`Bool`) as a standalone `have` in a clean
  context, then feed it to `Subtype.ext`/`congrArg`. Do **not** `rw` inside the dependent goal.
- **CFI-vertex equality** (the reusable pattern, from `cfiFlip_eq_self_of_flipSet_empty`):
  - subset: `congrArg Sum.inl (Sigma.ext rfl (heq_of_eq (Subtype.ext hset)))` where `hset : <set> = <set>`.
  - endpoint: `congrArg Sum.inr (Sigma.ext rfl (heq_of_eq (congrArg (Prod.mk (⟨w,hw⟩ : {x // x ∈ H.neighbors v})) hbool)))`
    where `hbool : <Bool> = <Bool>` (close by `cases b <;> cases (F v w) <;> … <;> rfl`).
- **Permutation (`Equiv.Perm`) equality via the CFI bijection:** use
  `refine Equiv.ext fun v => h.e.injective ?_` — **not** `ext v; apply h.e.injective` (the latter leaves a
  coercion-wrapped goal `apply` cannot unify). Then `simp only [e_cfiFlipAut, Equiv.Perm.mul_apply, …]`.
- **`xorF` is `CFIBase.xorF` with no `H` argument** (so it is *not* dot-accessible as `h.H.xorF`). Inside the
  `IsCFI'` namespace it does not resolve unqualified — write **`CFIBase.xorF F F'`**. (By contrast `flipSet`,
  `even_xorF`, `CycleSpace`, `cfiFlip` take `H` and are reached via `h.H.…` / `H.…`.)
- `Finset.not_mem_empty` is not a usable name here — discharge vacuous `∀ i ∈ (∅ : Finset _), …` with `by simp`.
- Proof-irrelevant data equalities: `subst h; rfl` (or `Subtype.ext`/proof irrelevance) rather than fighting `rw`.
- `symmDiff` (Finset is a `GeneralizedBooleanAlgebra`): `symmDiff_assoc`, `symmDiff_comm` apply. A private
  `card_symmDiff_mod_two` already exists in `CFI.lean` (used by `symmDiff_flipSet_mem_even`); reuse it in-file.

---

## 3. What is LANDED (all axiom-clean, full build green as of 2026-06-04)

The arc, in dependency order. Names below are exact; **line numbers are in `PublicTheoremIndex.md`** (don't
hardcode them — they drift). All in `ChainDescent/Cascade.lean` unless marked `[CFI.lean]`.

### Part A abstract layer (the residual group object)
- **A1 — `StabilizerAt adj P S : Subgroup (Equiv.Perm (Fin n))`** (carrier = `ResidualAut adj P S` = a
  `P`-preserving automorphism fixing `S` pointwise). `mem_stabilizerAt` (Iff.rfl), `mem_stabilizerAt_empty`
  (root = all `P`-preserving auts), `stabilizerAt_mono` (`S ⊆ S' → Stab S' ≤ Stab S`),
  `stabilizerAt_eq_bot_iff_isBase`, `mem_orbit_stabilizerAt_iff` (`MulAction.orbit (Stab S) v ↔ OrbitPartition adj P S v`).
- **A2 — soundness seam:** `closure_le_stabilizerAt` (harvested gens that are `ResidualAut` ⟹ `closure ⊆ Stab`),
  `orbit_pathFixing_sound`, `covered_sound` (the prune is sound).
- **A3 — order:** `card_stabilizerAt_eq_one_iff_isBase` (rigid verdict), `card_stabilizerAt_eq_orbit_mul`
  (`|Stab S| = |orbit b| · |Stab (insert b S)|`).
- **A3.5 — full order product:** `orbitSizeProd`, `card_stabilizerAt_eq_prod` (telescoping identity),
  `card_stabilizerAt_eq_prod_of_base`, `card_autP_eq_prod_of_base` (`|Aut(G)^P| = ∏ basic-orbit sizes`).

### A2-complete — the harvest COMPLETENESS seam (the dual of A2 soundness)
> ⚠️ **CRITICAL DESIGN NOTE — do not reintroduce the circular version.** A first cut defined `CoversOrbits`
> with realizers in the *full* `closure gens`. That is **circular**: since the residual shrinks down the base
> (`Stab S ≤ Stab ∅`), `closure gens = Stab ∅` already realizes every deeper orbit, so the "witness" was
> equivalent to the conclusion. The **genuine** version (now in place) requires realizers from the
> **path-fixing** generators `gensAt adj P gens S := {g ∈ gens | g ∈ StabilizerAt adj P S}` — the classical
> *strong generating set* condition, genuinely stronger than top-level generation. **Keep it path-fixing.**
- `gensAt adj P gens S` + `gensAt_anti`, `closure_gensAt_le_stabilizerAt`, `closure_gensAt_anti`, `gensAt_empty_eq`.
- `stabilizerAt_le_closure_gensAt_step` — the one-level strong-generation core (dual of `closure_le_stabilizerAt`).
- `CoversOrbits adj P gens bs S` — the coverage witness along a base sequence (recursive: at each head the
  *path-fixing* closure realizes the current residual orbit of the base point; tail = `IsBase`).
- `coversOrbits_realize_of_mem` — **the harvest interface**: if the path-fixing *generators* themselves realize
  `b`'s orbit, the coverage clause holds (via `Subgroup.subset_closure`). **This is what CFI-cov.3 plugs into.**
- `stabilizerAt_le_closure_gensAt_of_coversOrbits` (≤), `stabilizerAt_eq_closure_gensAt_of_coversOrbits` (=),
  `closure_eq_stabilizerAt_empty_of_coversOrbits` (`closure gens = Stab ∅` at the root),
  `card_closure_gensAt_eq_prod_of_coversOrbits` (the chain reproduces the residual *order*).

### CFI-cov.1 — bridge gauge flips → the residual vocabulary
- `cfiFlipAut_residualAut` (a symmetric/even gauge flip `F`-free on `S`'s gadgets is a `ResidualAut adj P S`),
  `cfiFlipAut_mem_stabilizerAt`, `cfiFlipAut_orbitPartition` (**forward** coverage: a path-fixing flip moves `v`
  within its orbit), `cfiGaugeGens` (the gauge generating set), `cfiGaugeGens_residualAut_empty` (root soundness),
  `cfiFlipAut_mem_gensAt` (a path-fixing flip ∈ `gensAt (cfiGaugeGens h) S`).

### CFI-cov.2 — cycle-space `Z₂^β` + base sequence
- `[CFI.lean, CFIBase ns]` `xorF`, `flipSet_xorF` (`flipSet (xorF F F') = flipSet F ∆ flipSet F'`), `even_xorF`,
  `CycleSpace` (symmetric + even = the `Z₂^β` index set), `cycleSpace_xorF`, `cycleSpace_const_false`.
- `isBase_of_discrete_warmRefine` (general `Discrete ⟹ IsBase` bridge), `foldl_insert_eq_union` /
  `foldl_insert_empty_eq_toFinset`, `cfi_exists_base_seq` (**odd-degree CFI has an ordered base sequence**, from
  the axiom-free cascade discreteness `theorem_1_HOR_cfi_oddDeg`).

### CFI-cov.3 stage 1 — the gauge-flip group homomorphism `Z₂^β → Aut`
- `[CFI.lean]` `cfiFlip_xorF` (`cfiFlip (xorF F F') = cfiFlip F ∘ cfiFlip F'`), `cfiFlip_const_false`,
  `cfiFlipAut_xorF` (`cfiFlipAut (xorF F F') = cfiFlipAut F * cfiFlipAut F'`), `cfiFlipAut_one`.
  ⇒ `F ↦ cfiFlipAut F` is a group homomorphism `(CycleSpace, xorF) → Equiv.Perm (Fin n)`, image = the gauge group.

---

## 4. THE IMMEDIATE NEXT TARGET — CFI-cov.3 core

**Goal:** prove `cfi_coversOrbits : CoversOrbits adj P (cfiGaugeGens h) bs ∅` for the odd-degree-CFI base
sequence `bs` from `cfi_exists_base_seq`. Combined with the already-landed pieces this gives, end-to-end:
`Subgroup.closure (cfiGaugeGens h) = StabilizerAt adj P ∅` (via `closure_eq_stabilizerAt_empty_of_coversOrbits`,
soundness from `cfiGaugeGens_residualAut_empty`) and `|Aut(CFI)^P| = ∏ basic-orbit sizes`
(`card_closure_gensAt_eq_prod_of_coversOrbits`). That is the headline: **the cross-branch harvest reproduces
`Aut(CFI(H))^P` exactly, for the odd-degree class.**

**What `CoversOrbits adj P (cfiGaugeGens h) bs ∅` unfolds to** (see `CoversOrbits` def): at each level `Sᵢ`
along `bs` (`S₀ = ∅`, `Sᵢ₊₁ = insert bᵢ Sᵢ`), the clause
`∀ w, OrbitPartition adj P Sᵢ bᵢ w → ∃ g ∈ Subgroup.closure (gensAt adj P (cfiGaugeGens h) Sᵢ), g bᵢ = w`,
terminating in `IsBase adj P (bs.foldl insert ∅)` (you have this from `cfi_exists_base_seq` — but note `bs`
there is `S.toList` for the cascade's discrete `S`; you'll likely need to thread that specific `bs`).

**The crux (the structure theorem, reverse of `cfiFlipAut_orbitPartition`):** given
`OrbitPartition adj P Sᵢ bᵢ w` (a path-fixing residual aut `g` with `g bᵢ = w`), produce a **single
path-fixing gauge flip** — `F ∈ CycleSpace`, `F`-free on `Sᵢ`'s gadgets — with `cfiFlipAut F … bᵢ = w`. Then
`cfiFlipAut_mem_gensAt` puts it in `gensAt (cfiGaugeGens h) Sᵢ`, and `coversOrbits_realize_of_mem` discharges
the clause (single generator suffices — no products/closure needed if every residual move is one flip).

So the real content is: **every path-fixing residual automorphism of `CFI(H)` is a path-fixing gauge flip.**
This is the `Aut(CFI(H)) ≅ Z₂^β ⋊ Aut(H)` structure theorem, specialized: at a path containing the seeds, the
`Aut(H)` (base-graph) factor is killed (the residual fixes the seeds, pinning base vertices), leaving the pure
gauge `Z₂^β` factor = single flips.

### Decomposition of the crux into sub-steps (suggested order)
1. **`flipSet`-free ⟸ path-fixing (the easy converse of locality).** If a gauge flip `cfiFlipAut F` fixes
   `Sᵢ` pointwise and `Sᵢ` contains a seed of gadget `v`, then `flipSet F v = ∅` (the flip can't move the seed's
   gadget). Mirror of `cfiFlipAut_eq_self_of_flipSet_empty` / `disjoint_support_cfiFlipAut`. Tractable.
2. **Aut(CFI) decomposition / Φ(σ) base-aut lift — THE BIG MISSING INFRA.** There is currently **no** Lean
   representation of `Aut(CFI(H)) ≅ Z₂^β ⋊ Aut(H)`, no base-automorphism lift `Φ : Aut(H) → Aut(CFI(H))`, and
   no decomposition theorem. This must be built. Likely shape: define `Φ(σ)` (relabel CFI vertices by `σ` on
   the base index), prove `IsAut (Φ σ)`, then the decomposition "every `IsAut π (cfiAdjMatrix H)` is
   `Φ σ ∘ cfiFlipAut F` for some `σ ∈ Aut(H)`, `F ∈ CycleSpace`." This is the multi-week piece and the honest
   bottleneck.
3. **Seeds kill the base factor.** A residual aut fixing all seeds in `Sᵢ`'s gadgets has `σ = id` in its
   decomposition (the seed `a_∅^v` is the canonical gadget marker; fixing it pins `v`). ⇒ the residual is a
   pure gauge flip `cfiFlipAut F`, and by (1) `F` is path-fixing.
4. **Assemble** `cfi_coversOrbits` by induction over `bs`, using (1)–(3) at each level + `coversOrbits_realize_of_mem`.

### Honest difficulty
Step 2 (the decomposition / `Φ(σ)` infra) is the genuine multi-week nut — it is exactly the long-pending
"CFI Aut structure lemma" noted in `chain-descent-orbit-recovery.md §9`. Steps 1, 3, 4 are tractable *given* 2.
The C# canonizer already computes `Aut(CFI(K₄–K₇))` correctly, so this is *firing content, not GI-hard* — but
it is a substantial Lean build. Consider whether a **narrower first win** is wanted: e.g. prove
`cfi_coversOrbits` for a *fully-individualized tail* (where `Sᵢ = allSeeds`, the base, so the clause is vacuous
/ `IsBase`), or for the **endpoint parity-pair** sub-case where `cfiFlipAut_swaps_endpointVertex` already gives
the realizing flip once a cycle through the decision edge avoiding `Sᵢ`'s gadgets is exhibited (that cycle's
existence is base-graph cycle-space content — see the existing `triEdge`/`evenPermEdge` witnesses in `CFI.lean`,
which already construct concrete even subgraphs through an edge).

### What already exists to build on (from the CFI gauge-flip survey)
`CFI.lean` has a complete gauge-flip layer: `cfiFlip`/`cfiFlipAut` (the `Z₂^β` flip), `isAut_cfiFlipAut`,
`cfiFlipAut_preserves_P`, `cfiFlipAut_eq_self_of_flipSet_empty` (locality), `disjoint_support_cfiFlipAut`,
`cfiFlipAut_endpointVertex` / `cfiFlipAut_swaps_endpointVertex` (parity-pair swap), `e_cfiFlipAut` (the
conjugation identity `e (cfiFlipAut F v) = cfiFlip F (e v)`). CFI vertex API: `seedVertex`, `endpointVertex`,
`subsetVertex`, `aEmpty`, `endpoint`, `subset`, and `adj_…_eq_one_iff` characterization lemmas. `IsCFI'` fields:
`m`, `H : CFIBase m`, `e : Fin n ≃ H.CFIVertex`, `matching`. Concrete even-subgraph constructors through an edge
already exist: `triEdge` (triangle, for triangle-containing bases) and `evenPermEdge` (permutation cycle, for
triangle-free bases) with their locality lemmas `flipSet_triEdge_other` / `flipSet_evenPermEdge_of_fixed`.
**There is NO** `Aut(CFI)` group object, `Z₂^β ⋊ Aut(H)`, `Φ(σ)` lift, or decomposition theorem yet (step 2).

---

## 5. Key conceptual findings this session (so they aren't relearned)

1. **The conservation finding is the *why* of this whole thread.** `lockstep_disc_imp_stab_trivial` proves the
   within-cell discretizing colour-match oracle cannot harvest a multi-step moved orbit — so multi-step hidden
   symmetry *must* go cross-branch (Part A). Do not re-attempt the within-cell route (the A2b lockstep
   discharge) — provably futile. (Memory: `project_discretizing_oracle_limit_2026-06-03.md`.)
2. **A2-complete circularity.** (See the CRITICAL note in §3.) The coverage witness must use *path-fixing*
   generators (`gensAt`), or it degenerates to the conclusion. This was caught and fixed; keep it fixed.
3. **A2-complete reduces CFI completeness to a single-flip realization**, via `coversOrbits_realize_of_mem` —
   you do **not** need products/closure if every residual orbit move is a single gauge flip (which the
   structure theorem gives). This simplifies CFI-cov.3.
4. **The gauge flips already form a group** (CFI-cov.3 stage 1, `cfiFlipAut_xorF`) — so if you *do* end up
   needing closure, the closure of `cfiGaugeGens` is the homomorphic image of the cycle space.

---

## 6. Pointers (authoritative, durable)

- **Part A doc (authoritative for this thread):** [`chain-descent-schreier-sims.md`](./chain-descent-schreier-sims.md)
  — STATUS block + §7 staging (A1–A4, A2-complete, CFI-cov.1/2/3) carry the live state.
- **Current architecture:** [`chain-descent-declassing.md`](./chain-descent-declassing.md) (the de-classing
  turn; §9 frontier). Its STATUS notes the Part A progress.
- **Theorem index (line numbers):** [`PublicTheoremIndex.md`](../GraphCanonizationProofs/PublicTheoremIndex.md)
  — every landed declaration with a one-line description; regenerated from source.
- **Reading order for full context:** `chain-descent-simplified-overview.md` → `chain-descent-strategy.md` →
  `chain-descent-calculator.md` → `chain-descent-declassing.md` → (`chain-descent-orbit-recovery.md` as the
  *witness layer*, see its §0 reading map) → the index. Also `MEMORY.md` (the project's auto-memory index).
- **C# reference** (the object the Lean mirrors / validates against): `GraphCanonizationProject/PermutationGroup.cs`
  (BSGS, `Order = ∏ OrbitSize`), `ChainDescent.cs` (`HandleLeaf` a-posteriori harvest, `CoveredByPathFixingAut`
  consumption), `CfiGraphGenerator.cs`.

---

## 7. Suggested first action for the next worker

1. Run `cd /workspace && bash scripts/build.sh` — confirm green (sanity).
2. Read `chain-descent-schreier-sims.md` §7 (the staging) and skim the A2-complete + CFI-cov declarations in
   `Cascade.lean` / `CFI.lean` (use the index for line numbers).
3. Start CFI-cov.3 sub-step (1) (the easy `path-fixing ⟹ flipSet-free` converse) to warm up, then scope
   sub-step (2) (the `Φ(σ)` lift + decomposition) — that is the real work. Decide with the user whether to
   attempt the full structure theorem or a narrower first win (endpoint parity-pair coverage on a
   triangle-containing base, using the existing `triEdge` witness).
4. After any landed increment: axiom-check, full build, regen+fill the index, update schreier-sims §7/STATUS
   and the `MEMORY.md` Part A pointer.
