# WL-visibility of group structure — a Lean formalization plan

> **What this is.** The build plan for formalizing, in Lean, the **WL-visibility dichotomy** for group structure that
> `NonAbelianCfiProbe` established empirically: the standard CFI/multipede gadget is **1-WL-blind** to a group's
> structure (S₃ behaves exactly like Z₆), while a **commutator / commuting-pairs gadget is 1-WL-visible**. The
> mathematical hearts of both halves are already built (axiom-clean); this doc records the targets, the proven cores,
> the reusable tools (with exact lemma names), the remaining gaps, and the phased plan. Written for a developer new to
> this thread. Provenance: memory `project_wl_visibility_lean_2026-06-28`, `project_nonabelian_cfi_witness_2026-06-28`,
> the duality doc [`chain-descent-cameron-entanglement.md`](./chain-descent-cameron-entanglement.md) §4 Route B.

---

## STATUS (read first)

**Phase 0 DONE (2026-06-28, axiom-clean `[propext, Classical.choice, Quot.sound]`).** The two algebraic hearts of the
dichotomy are proved in `GraphCanonizationProofs/ChainDescent/ScratchWLVisibility.lean` (`lake env lean` scratch, NOT in
`build.sh`):
- **blindness heart** `product_coord_regular` — coordinate-regularity of the product relation;
- **visibility heart** `commDeg_const_iff_comm` (+ `_const_of_comm`, `_nonconst_of_noncomm`) — the commuting-degree is
  constant iff the group is abelian.

**Two design decisions are settled** (do not re-litigate):
1. **Generalize 1-WL to an arbitrary `[Fintype V] [DecidableEq V]` vertex type** (not `Fin n`). Removes all index
   encoding; reused by every theorem. (User-approved 2026-06-28.)
2. **State the dichotomy on MINIMAL graphs**, not the full multipede: the **commuting graph** for visibility (T2) and a
   **single product-gadget** for blindness (T1). The full-multipede generalization is deferred (Phase 4).

**Next = Phase 1** (generalize the 1-WL primitives to `Fintype V`), then Phase 2 (T2 visibility — the smaller half,
consumes `commDeg_nonconst_of_noncomm`), Phase 3 (T1 blindness — consumes `product_coord_regular`), Phase 4 (T3
characterization + multipede generalization). Quality bar: axiom-clean, no `sorry` / no fresh `axiom` /
`native_decide` banned, full build green when ported.

---

## 1. The question and why it matters

The canonizer's open frontier is the **structural wall** (rigid graphs that resist Weisfeiler–Leman). Every known
WL-hard rigid graph (CFI / multipede / Lichter) is **linear over an abelian gauge**; whether a *non-abelian* gauge can
produce WL-hardness is the open "structure / non-linear" corner (cameron-entanglement §4 Route B; the rigid seal's flag
floor, `chain-descent-ir-blindspot-solver.md` §11.14).

`NonAbelianCfiProbe` (C#) answered the empirical version: generalizing the CFI gadget from F₂ to an arbitrary finite
group Γ (gadget = the relation `g₁·g₂·…·g_d = 1`), the resulting graph's **WL-hardness depends only on `|Γ|`, never on
whether Γ is abelian** — S₃ ≡ Z₆ and D₄ ≡ Z₈ behave *byte-for-byte identically* in every WL measure, even though the
graphs are non-isomorphic. WL is **blind** to the non-abelian structure. By contrast, a gadget that exposes
*commutativity* (connect `a`–`b` iff `ab = ba`) is 1-WL-**visible** (centralizer sizes vary). This doc formalizes that
dichotomy and isolates its cause.

**The cause (the theorem to prove):** a single-constraint gadget is **1-WL-blind to Γ iff its relation is
coordinate-regular** (a perfect quasigroup — any one coordinate's value leaves a completion count independent of the
value and the group). The product relation `g₁…g_d = 1` is coordinate-regular (cancellation); the commutator relation
is not. 1-WL only counts, and the counts of a coordinate-regular relation see only `|Γ|`.

---

## 2. The target theorems

Let `Γ` be a finite group (`[Group G] [Fintype G] [DecidableEq G]`).

- **T1 (blindness).** Color refinement on the **product-gadget graph** `B_d(Γ)` does not refine the fine colouring
  {one colour per segment, one per gadget} — i.e. `warmRefine` is stuck at it, for every Γ. Corollary: `B_d(Γ)` and
  `B_d(Γ′)` are **1-WL-equivalent** whenever `|Γ| = |Γ′|` (e.g. S₃ ≡ Z₆). Engine: each segment value-vertex has a
  Γ-independent signature (coordinate-regularity), so `refineStep` produces no split.
- **T2 (visibility).** Color refinement on the **commuting graph** `Comm(Γ)` (vertices = Γ, `a ~ b ⟺ ab = ba`, `a≠b`)
  **does** refine the trivial colouring **iff** Γ is non-abelian, because vertices split by `commDeg` (= centralizer
  size). Corollary: `Comm(S₃) ≢ Comm(Z₆)` (different degree sequences) — non-abelian structure is 1-WL-visible.
- **T3 (characterization, the capstone).** A single-constraint gadget on a finite relation `R ⊆ Γ^d` is 1-WL-blind to
  Γ **iff** `R` is coordinate-regular. T1 (product, blind) and T2 (commutator, visible) are the ± instances.

> **Scope note.** "1-WL-blind / -visible" is the right altitude: it already separates the cases, it is what the probe
> measured (WL-*depth* `b_WL`, of which 1-WL-stability is the base case), and it keeps the graphs out of the
> association-scheme machinery (which does not apply — see §4). A k-WL version is a possible later strengthening but is
> **not** needed for the dichotomy.

---

## 3. What is already built (Phase 0) — exact decls + insights

File: `GraphCanonizationProofs/ChainDescent/ScratchWLVisibility.lean`, namespace `WLVis`, all axiom-clean
`[propext, Classical.choice, Quot.sound]`. Imports are trimmed to the minimum (≈3× faster than `import Mathlib`):
`Mathlib.Algebra.Group.Basic`, `Mathlib.Data.Fintype.EquivFin`, `Mathlib.Data.Fintype.Prod`,
`Mathlib.Logic.Equiv.Basic`, `Mathlib.Tactic.Push`.

**Blindness heart:**
- `product_coord_regular (a : G) : Fintype.card {p : G × G // a * p.1 * p.2 = 1} = Fintype.card G` — degree-3
  coordinate-regularity. **Proof:** the explicit `Equiv` `(y,z) ↦ y`, inverse `y ↦ (y, (a*y)⁻¹)`; the inverse's
  membership proof is `mul_inv_cancel`, and `left_inv` recovers `z = (a*y)⁻¹` via **`eq_inv_of_mul_eq_one_right`**.
- `product_coord_regular_indep (a a' : G) : … card … = … card …'` — the same count is independent of the fixed value
  (`rw [product_coord_regular, product_coord_regular]`). This is the form blindness literally needs.

**Visibility heart:**
- `commDeg (g : G) : ℕ := Fintype.card {h : G // g * h = h * g}` — the commuting-degree = the 1-WL degree in a
  commuting-pairs gadget. **Use the explicit subtype `{h // g*h=h*g}`, not the opaque `Commute g h` def** (see gotcha).
- `commDeg_const_of_comm (hab : ∀ a b, a*b=b*a) (g) : commDeg g = Fintype.card G` — proof
  `Fintype.card_congr (Equiv.subtypeUnivEquiv (fun h => hab g h))`.
- `commDeg_nonconst_of_noncomm (h : ∃ a b, a*b≠b*a) : ∃ g, commDeg g < commDeg (1 : G)` — pick the non-commuting `a`;
  `commDeg 1 = |G|` via `Equiv.subtypeUnivEquiv`; `commDeg a < |G|` via **`Fintype.card_subtype_lt (x := b)`** (the
  non-partner `b` witnesses a missing element).
- `commDeg_const_iff_comm : (∀ g, commDeg g = Fintype.card G) ↔ (∀ a b, a*b=b*a)` — the dichotomy in one line
  (`push Not` + `omega`).

**Insights from the build (save the next developer time):**
1. **Subtypes of a group need `[DecidableEq G]`** to get a `Fintype` instance (`DecidablePred` of the defining
   equation). Every decl carries it.
2. **Do not use `Commute g h`** as the subtype predicate — `Commute` is an opaque `def`, so `Fintype {h // Commute g h}`
   fails to synthesize. Spell out `{h // g * h = h * g}`.
3. **Annotate `(1 : G)`** in statements/terms — a bare `1` defaults to `ℕ`, producing a spurious `Group ℕ` /
   `Fintype ℕ` synthesis failure and a downstream `rw` mismatch (`commDeg 1` (ℕ) ≠ `commDeg (1:G)`).
4. `push Not at h` is the current spelling (`push_neg` is deprecated; `Mathlib.Tactic.Push`).
5. The **degree-d generalization** of `product_coord_regular` (`#{t : Fin d → G // ∏ t = 1 ∧ t i = a} = |G|^{d-2}`,
   independent of `a`) is the natural next lemma if T1 is stated for general degree; the d=3 case suffices for the
   minimal product-gadget. Tools: the bijection that adjusts one free coordinate (group cancellation, `Equiv.mulLeft`).

---

## 4. Tools that already exist (reuse — exact names)

**Graph-level 1-WL — top-level `GraphCanonizationProofs/ChainDescent.lean`** (this is the engine T1/T2 run on):
- `Colouring n := Fin n → Nat`; `AdjMatrix n`; `PMatrix n` (the partial-order matrix; pass the trivial all-`unknown`
  for a plain graph).
- `signature adj P χ v : Multiset (Nat × Nat × POE)` — the neighbour `(colour, adj-value, P-relation)` multiset over
  `u ≠ v`. **This is the object whose Γ-(in)dependence is the whole proof.**
- `refineStep adj P χ` and **`refineStep_iff`** : `refineStep … v = refineStep … w ↔ χ v = χ w ∧ signature … v =
  signature … w`. **The lever:** equal signatures ⟹ no split (T1); unequal signatures ⟹ split (T2).
- `warmRefine adj P initial := (refineStep adj P)^[n] initial`; `warmRefine_refines`.
- `samePartition χ₁ χ₂ := ∀ i j, χ₁ i = χ₁ j ↔ χ₂ i = χ₂ j` (+ `refl`/`symm`/`trans`). The "stuck" target of T1 is
  `samePartition (warmRefine …) initial`.

> **These are defined on `Fin n`.** Phase 1 generalizes them to an arbitrary `[Fintype V] [DecidableEq V]` (decision §0).
> The generalization is mechanical (`signature` sums over `Finset.univ.filter (· ≠ v)`, already `Fintype`-shaped); the
> only `Fin n`-specific use is the iteration count `n` in `warmRefine` — replace by `Fintype.card V`.

**Mathlib (all confirmed used in Phase 0):** `Group`, `Fintype`, `DecidableEq`, `Fintype.card_eq`,
`Fintype.card_congr`, `Equiv.subtypeUnivEquiv`, `Fintype.card_subtype_lt`, `eq_inv_of_mul_eq_one_right`,
`mul_inv_cancel`, `Equiv.mulLeft` (for the degree-d generalization), `Fintype.equivFin` (only if any `Fin n` transport
is still needed). For T2's degree-sequence corollary: centralizer cardinalities live in
`Mathlib/GroupTheory/Subgroup/Centralizer.lean` if a `Subgroup.centralizer` framing is preferred over the bare subtype.

**NOT applicable — do not reach for it.** The scheme-level discreteness engine (`AssociationScheme`,
`kRoundProfileCount`, `discrete_of_kRoundRelationSeparates` in `CascadeAffine.lean`) is for association schemes /
orbital schemes. The commuting graph and the product-gadget are **not** schemes (not vertex-transitive / not regular),
so the graph-level `warmRefine` is the correct and only tool here.

---

## 5. The gaps, and how to close each

1. **Generalize 1-WL to `[Fintype V] [DecidableEq V]` (Phase 1, the one infra change).** Re-state `signature`,
   `refineStep`, `refineStep_iff`, `warmRefine`, `samePartition` over a vertex type `V` (graph = `V → V → …`). Mechanical
   (the defs already quantify over `Finset.univ`); iteration count `n ↦ Fintype.card V`. *Decision:* do this as a small
   new module (e.g. `ChainDescent/WLGeneric.lean`) rather than editing the top-level file, to keep the canonizer's
   `Fin n` invariants untouched; re-derive `refineStep_iff` (the only lemma the proofs need) generically.
2. **Build the minimal graphs (Phase 2/3).**
   - **Commuting graph `Comm(Γ)`** (T2): vertices `= Γ`, `adj a b := decide (a*b = b*a ∧ a ≠ b)`. Trivial — no
     encoding. `warmRefine` round-1 colour of `a` is its degree `= commDeg a − 1`; `commDeg_nonconst_of_noncomm` ⟹ ≥2
     colours ⟺ non-abelian ⟹ refines. The S₃≢Z₆ corollary = different degree multisets (a `Multiset`-of-degrees
     invariant; cheap).
   - **Product-gadget `B_d(Γ)`** (T1): vertices `= (Σ _ : Fin d, Γ) ⊕ {t : Fin d → Γ // ∏ t = 1}` (segments ⊕ tuples),
     `adj` = incidence (`tuple t — (i, t i)`). Fine colouring = segment-index for the left part, a single colour for the
     right. The signature of `(i, a)` is, per the incidence, a multiset whose multiplicity of the gadget-colour is the
     coordinate-regular count `product_coord_regular` ⟹ independent of `a` ⟹ `refineStep_iff` ⟹ no split.
3. **Signature ↔ count bridge (Phase 2/3, the load-bearing lemma).** Relate `signature (i,a)` to
   `Fintype.card {tuples adjacent to (i,a)}`. The signature is a `Multiset.map` over neighbours; its relevant content is
   the multiplicity of each neighbour-colour = a `Finset.card` = the coordinate-regular count. Tool: `Multiset.count` /
   `Finset.card` rewriting; this is the main proof obligation and where `product_coord_regular` / `commDeg` plug in.
4. **Cross-graph 1-WL-equivalence (Phase 2/3, small new def).** `warmRefine`/`samePartition` are within one graph. Define
   `WLEquiv` of two coloured graphs as equality of the **multiset of stable-colour class sizes** (the standard 1-WL
   invariant). T1's corollary (`B_d(Γ) ≡ B_d(Γ′)`) and T2's separation (`Comm(S₃) ≢ Comm(Z₆)`) are then statements
   about these multisets. Keep it minimal (don't formalize full 1-WL game equivalence).
5. **T3 characterization (Phase 4).** Abstract over a relation `R ⊆ Γ^d` with a `CoordRegular R` predicate (any
   `d−1` coords + a value of the last has a count independent of choices); prove blind ⟺ `CoordRegular`. The product and
   commutator gadgets instantiate it. Optional but it is the clean general statement.
6. **Full-multipede generalization (Phase 4, optional).** Lift T1 from a single gadget to the multipede over a base
   graph (segments shared across gadgets). Only needed if the doc wants the literal CFI object; the dichotomy does not
   require it.

---

## 6. Sequencing

| Phase | Deliverable | Consumes | Risk |
|---|---|---|---|
| **0 ✓** | algebraic cores (`ScratchWLVisibility.lean`) | — | done |
| **1** | `Fintype V`-generic 1-WL (`WLGeneric.lean`): `signature`/`refineStep_iff`/`warmRefine`/`samePartition` | top-level `ChainDescent.lean` defs | low (mechanical) |
| **2** | **T2 visibility** on `Comm(Γ)` + `Comm(S₃)≢Comm(Z₆)` | `commDeg_nonconst_of_noncomm`, P1, gap 4 | low–med |
| **3** | **T1 blindness** on `B_d(Γ)` + `B_d(Γ)≡B_d(Γ′)` | `product_coord_regular`, P1, gaps 3–4 | med (signature↔count) |
| **4** | T3 characterization; (optional) multipede lift | P2, P3 | med |

Do **T2 before T1** — it is smaller (trivial graph, no incidence bookkeeping) and exercises the P1 generic 1-WL +
gap-4 cross-graph notion end-to-end, de-risking T1.

---

## 7. Pointers

- **Built cores:** `GraphCanonizationProofs/ChainDescent/ScratchWLVisibility.lean` (Phase 0, axiom-clean, not in build).
- **1-WL engine to generalize:** top-level `GraphCanonizationProofs/ChainDescent.lean` (`signature`, `refineStep_iff`,
  `warmRefine`, `samePartition`).
- **Empirical source:** `GraphCanonizationProject.Tests/NonAbelianCfiProbe.cs` (5 probes: WL-hardness, rigidified,
  S3-vs-Z6 distinct, extraction discriminator, group-varying) — memory `project_nonabelian_cfi_witness_2026-06-28`.
- **The duality this serves:** `chain-descent-cameron-entanglement.md` §4 Route B (no non-abelian gauge);
  `chain-descent-ir-blindspot-solver.md` §11.14 (the 2×2; rigid-seal flag floor).
- **Memory:** `project_wl_visibility_lean_2026-06-28` (this plan, condensed), `project_nonabelian_cfi_witness_2026-06-28`
  (the probe arc + the fixed/varying × abelian/non-abelian map; the wall narrows to growing non-solvable groups).

---

## 8. Honest scope

- This formalizes **why WL is blind to non-abelian structure in the standard gadget** (coordinate-regularity) and
  **that a commutator gadget breaks the blindness** — it does **not** resolve whether any rigid graph is a genuine
  non-poly wall. The probe arc already showed the fixed/varying-solvable group-CFI families are *tame* (extractable,
  WL-depth-tame, poly); the remaining wall candidate is **growing non-solvable groups**, which is a theory question
  (Babai–Luks string-canonization), not reachable by this construction (gadget size `|Γ|^{d−1}` explodes) and **out of
  scope here**.
- T1/T2 are about **1-WL**. The probe's `b_WL` (individualization-refinement depth) blindness is a stronger statement;
  1-WL-stability is its base case and the right first target. A `b_WL` / k-WL version would be a separate, harder build.
