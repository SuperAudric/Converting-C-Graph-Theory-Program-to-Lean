# A1 — the CC sparse substrate (build history + the route not taken)

> **What this is.** The build record for **A1** — "sparse ⟹ the δ′ forced-triangle closure exhausts `X_T`" on the
> general (multi-fiber) coherent configuration. **A1 is DONE** (`CoherentConfig.lean §CC.11`–`§CC.19`, all axiom-clean,
> 2026-06-14). This doc is *history*: the increment log, the abundance insight that closed it, and the abandoned
> PV-port roadmap (kept as the route-not-taken). **It is not the live frontier** — the live frontier (A2: bounding
> `c(X_{T₀}), k(X_{T₀})`) is `chain-descent-cxt-scoping.md`; the build map + STATUS is `chain-descent-general-cc-separability.md`.
> Split out of cxt-scoping 2026-06-14 to keep that doc A2-focused. Not yet archived — `§S-playbook` and the
> cross-fiber finding remain reusable reference.

---

## 0. What A1 delivers (the one-paragraph summary)

A1's deliverable is `allSingletonFiber_of_card_gt_subset` (`§CC.19`): **`T₀ ⊆ T ∧ (k(X_{T₀})−1)·c(X_{T₀}) < |T| ⟹
pointExtension X T` is complete (`T` a base of `X`).** It reduces the seal's open input `hclo` to a single `O(1)`
threshold on the extension's own parameters — the crisp interface A2 meets. The whole thing is **one counting lemma**
(`basePinsAll_of_card_gt`) + a padding/monotonicity bridge; it skips the entire PV `§S.10`–`§S.16` connectivity port
(the route not taken, §3 below). Decl index: `chain-descent-general-cc-separability.md §9`.

---

## 1. The increment log (§CC.11–§CC.19, all axiom-clean `[propext, Classical.choice, Quot.sound]`)

- **incr 1–2 (`§CC.11`):** the CC indistinguishing number `c(X)` (`indistinguishingNumberOf` /
  `indistinguishingNumberOf_eq_card` (PV eq. (7) geometric form `c(r)=|{γ:relOf γ α=relOf γ β}|`) / `IsReflexive` /
  `indistinguishingNumber` / `_le`), the max valency `k(X)` (`sourceFiber` / `valency` / `valency_eq_card` /
  `maxValency` / `valency_le_maxValency`), and `SparseSeparable` (`2c(k−1)<n`).
- **incr 3 (`§CC.12`, the (19) estimate):** `pu` / `pu_eq`, the **transpose bridge** `relOf_right_eq_iff_left` (the
  non-symmetric CC's substitute for `relOfPair_symm`), `not_isReflexive_relOf_of_ne`, `card_relNeighbors_le_maxValency`
  (`A.card ≤ k(X)` for non-reflexive `u` — the CC replacement for homogeneity's exact `= k`), and `sum_pu_le`
  (`Σ_δ pᵤ(δ) ≤ k(k−1)·c`). First place M2-Q1's non-symmetry bit; it was clean.
- **incr 4 (`§CC.13`, identity (20)):** `pu_eq_sum` (`pᵤ(δ) = Σ_w c^v_{uw}(c^v_{uw}−1)`, `v = relOf α δ`). *Cleaner*
  than homogeneous — the colour-function `interNum_eq` matches the fiber filter directly (no `rel`↔`relOfPair`).
- **incr 5 (`§CC.14`, triangle identity — TRANSPOSE-AWARE):** `outDeg_mul_interNum` (`(deg_k x)·c^k_{i,j} =
  (deg_i x)·c^i_{k,j*}`) + `valency_mul_interNum` (`n_k·c^k_{i,j} = n_i·c^i_{k,j*}`, apex realizing both source fibers).
  **The first place M2-Q1 changes the *theorem*, not just the proof:** homogeneous `valency_mul_intersectionNumber` is
  `c^i_{kj}`; the non-symmetric `y`-leg flip introduces `j* = transposeRel j`.
- **incr 6 (`§CC.15`, §S.4 graph layer + `saAdj_symm`):** `InSmax`/`smaxAdj`/`SmaxConnected`/`saAdj`/`SaConnected` +
  `saAdj_symm` (forced-triangle relation symmetric, via §CC.14 — `j*` lands on `relOf γ β`; needs no symmetric `smaxAdj`).
- **incr 7 (`§CC.16`, §S.5 + §S.9):** `sum_interNum_eq_outDeg` (§S.5, out-degree form, hypothesis-free) +
  `valency_le_pu_of_forall_ne_one` / `interNum_ne_one_of_valency_lt` / `valency_le_pu_of_valency_lt` (§S.9, Lemma-3.5(1)
  `n_u>n_v` half), carrying the explicit **source witness** `relOf α β₀ = u`.
- **incr 8 (`§CC.17`, the fiber-size identity):** `fiberSet` / `outDeg_eq_interNum` (`#{w:relOf u w=r} =
  c^{relOf u u}_{r,r*}`, generalises `valency_eq_card`) / `fiberSize_mul_valency` (`|F_src(r)|·n_r = |F_tgt(r)|·n_{r*}`,
  class double-count) / `smaxAdj_symm_of_sameFiber`. **The decisive cross-fiber finding (§3):** `smaxAdj` is symmetric
  ONLY intra-fiber ⟹ **global `SmaxConnected` is FALSE** on the multi-fiber CC. Landed infra; off the critical path
  after §CC.18.
- **★ incr 9 (`§CC.18`, the abundance discharge — A1 closed):** `dominatorReachable_of_basePinsAll` (CC mirror) /
  `basePinsAll_of_card_gt` (`(k−1)·c < |T| ⟹` every `γ∉T` pinned by two base points) / `dominatorReachable_of_card_gt`
  (`⟹ ∀v DominatorReachable T v`) / `allSingletonFiber_of_card_gt` (`(k(X_T)−1)·c(X_T) < |T| ⟹ X_T` complete). See §2.
- **A2-interface (`§CC.19`, the monotonicity/padding bridge):** `indistinguishingNumber_mono` / `maxValency_mono`
  (`Refines Y Z ⟹ c(Y)≤c(Z), k(Y)≤k(Z)`) / `refines_pointExtension_of_subset` (`T₀⊆T ⟹ X_T` refines `X_{T₀}`) /
  `allSingletonFiber_of_card_gt_subset` (the padding capstone) / `dominatorReachable_of_card_gt_subset` (the seal-`hclo`
  feeder). The threshold can't be checked at a non-discrete `X_T` (contrapositive forces `(k−1)c ≥ |T|`) — it is used
  via padding from a small base, hence monotonicity. Belongs to A2's interface but built as part of the A1 substrate.

---

## 2. The abundance insight (why A1 is one lemma, not a 600-line port)

**The δ′ engine `dominatorReachable_of_rank` accepts *any* bounded base.** So PV Theorem 3.1's sharp `b(X) ≤ 2` is
overkill — a crude `b(X) ≤ (k−1)c + 1` suffices. And that falls out of one counting lemma `basePinsAll_of_card_gt`:
for `γ ∉ T` and any `α ∈ T`, a base point `β` *fails* to pin `γ` (against `α`) only if it confuses `γ` with one of the
`≤ k−1` other `α`-out-neighbours in `γ`'s class — and each confusion set has size `≤ c` (an indistinguishing-number
count, `indistinguishingNumberOf_eq_card` + the transpose bridge `relOf_right_eq_iff_left`). Union bound: `≤ (k−1)c`
bad base points; `|T| > (k−1)c` leaves a good `β`. **Cross-fiber is automatic** (`α, β` range over all of `T`, the
forced triangle is `interNum`-level — no smax). So the entire PV `§S.10`–`§S.16` connectivity apparatus is unnecessary.

**The padding subtlety (why §CC.19 is needed).** The contrapositive of the abundance lemma is now a theorem:
`X_T` non-discrete ⟹ `(k(X_T)−1)·c(X_T) ≥ |T|`. So the threshold is *never* satisfiable at a still-non-discrete `X_T`
— it is consumed by **padding**: A2 bounds `c, k` at a *small* base `T₀`, monotonicity transports the bound to any
superset `T ⊇ T₀`, and once `|T|` overtakes `(k(X_{T₀})−1)·c(X_{T₀})` the lemma fires (at the padded `T`, `X_T` genuinely
is discrete). Hence A2's deliverable is "bound `c(X_{T₀}), k(X_{T₀}) = O(1)` at one `O(1)` base," not "meet the threshold."

---

## 3. The route NOT taken — the PV §S.10→§S.16 connectivity port (ABANDONED)

> **Historical.** This was the planned A1 route (M2-Q1 confirmed the PV sparse theorem is homogeneous-only, so a port
> was the citation-free path). The §CC.17 cross-fiber finding then made the *global* version impossible, and §CC.18's
> abundance route made the *whole* port unnecessary. Kept as the route-not-taken. **Do not port §S.10–§S.16.**

**The §CC.17 finding that killed it.** `smaxAdj_symm_of_sameFiber` proves `smaxAdj` is symmetric only intra-fiber (the
fiber-size identity cancels `|F|` only when `relOf a a = relOf b b`). So **global `SmaxConnected` is not merely hard to
port — it is not a theorem** on the multi-fiber `X_T`: a max-valency class in one fiber has no smax-edge to another.
The connectivity infra `exists_small_closed_of_not_connected` needs a globally symmetric relation, which does not exist
here. Cross-fiber spread *must* come from the δ′ dominator step against determined points — which is exactly what §CC.18
does directly, bypassing smax entirely.

**The roadmap (for the record only).** Each row was a homogeneous `Separability.lean` lemma to port to `CoherentConfig`:

| Homogeneous source | CC subtlety (why it was hard / impossible) |
|---|---|
| §S.10 `exists_small_closed_of_not_connected` + `exists_inSmax` | needs a **symmetric** relation; `smaxAdj` symmetric only intra-fiber ⟹ only a *single-fiber* `SmaxConnected` is even true. |
| §S.10 `smaxConnected_of_sparseSeparable` | smax-half; uses `valency_le_pu_of_valency_lt` (§CC.16, source witness `relOf α β₀ = u`). |
| §S.11 `exists_saAdj_of_intersectionNumber_eq_one`, `valency_le_pu_of_no_saAdj` | sα↔counting bridge + Lemma 3.5(1) `n_u=n_v` half. |
| §S.12–§S.15 `saComp`/`compsOf`/`transport`/`lemma35_2`/`card_compsOf_eq_one` | the sα-component analysis (~400 lines) ⟹ `\|C(u)\|=1`. The bulk; the most homogeneity-dependent part. |
| §S.16 `saConnected_of_sparseSeparable` | sα-half; with §S.10 gives `SmaxConnected ∧ ∀α SaConnected α` on a single fiber. |
| the δ′ bridge | convert connectivity into a pinning rank for §CC.10 `dominatorReachable_of_rank`. |

The sα-component analysis (§S.11–§S.15) exists in PV solely to handle the equal-valency `n_u = n_v` case under the
smax-restricted pinning; the δ′ abundance route never needs it (it pins by any two reached points, and uses the strong
`c = O(1)` directly). The homogeneous source `Separability.lean §S.1–§S.16` remains intact and is unaffected.

---

## 4. The porting playbook (reusable patterns confirmed during A1)

- **Transpose-aware statements (M2-Q1).** When the homogeneous proof uses `rel_symm` to flip a leg, the CC analogue
  gains a `transposeRel` on that leg. Confirmed: §S.8 triangle identity is `c^i_{k,j*}` (not `c^i_{kj}`) — a genuine
  *statement* change. Where the flipped quantity is only tested for `=1`/`0`/`≥1` (e.g. §S.9), the transpose is
  *harmless*. Where two relations must literally match (e.g. the inner bound of §S.6), insert the transpose bridge
  `relOf_right_eq_iff_left` (§CC.12).
- **Out-degree form over valency.** State counting lemmas with `#{w : relOf α w = u}` (hypothesis-free), not
  `valency u`; the `= valency u` step needs `α` a source of `u`. Avoids threading fiber hypotheses (§S.5/§CC.16).
- **Source witnesses.** Where valency *must* appear (triangle identity, Lemma 3.5), carry an explicit witness
  `relOf α β₀ = u` (= "`α` is in `u`'s source fiber") — the apex-in-fiber requirement made into a hypothesis (§CC.16).
- **Lean gotchas.** (1) `Finset.card_bij` surjectivity: a simp-collapsed `z = z` membership conjunct becomes `True`,
  so close it with `trivial`, **not** `rfl` (bit twice in §CC.14). (2) `interNum_eq` is in colour-function form
  (`relOf u w = a ∧ relOf w v = b`), so CC fiber-card steps are often *more direct* than homogeneous (no `rel`↔`relOfPair`
  conversion). (3) `Finset.card_sdiff` resolved to the *unconditional* `(s\t).card = s.card − (s∩t).card` variant —
  for `(T\Bad).Nonempty` use `Finset.sdiff_nonempty` + `Finset.card_le_card`, not `card_sdiff` (§CC.18). (4) defeq folds
  (`valency`/`fiberSet` against their definitions) need an explicit trailing `rfl` after the rewrite chain (§CC.17).
- **`§CC` namespace gotchas.** The `CoherentConfig` namespace is reopened mid-file with only `variable {n}` — re-add
  `variable (X : CoherentConfig n)` before new decls; `open scoped Classical` is active from §CC.11 for the
  non-reflexive `Finset.filter`; the section variable `X` is auto-bound, so cross-CC lemmas (e.g. the §CC.19 mono
  lemmas) must use fresh binders `{Y Z : CoherentConfig n}` to avoid shadowing.

---

## 5. The M3 lemma-draft history (the A1/A2/A3 decomposition + the route decision)

> Drafted 2026-06-13, when M1 (probe) showed `c, k = O(1)` on the extension and M2 (research) confirmed the sparse
> theorem is homogeneous-only. This is the reasoning that chose the citation-free route; retained for provenance.

The reduction split the citation-free path into three pieces:
- **A1 `SparseClosesCC`** — "sparse ⟹ a pinning rank exists" on the CC `X_T`, feeding §CC.10 `dominatorReachable_of_rank`.
  Originally planned as the PV-port (§3); *actually closed* by the §CC.18 abundance route.
- **A2 `ParamBoundOnExtension`** — the shared open core: `c(X_{T'}), k(X_{T'}) = O(1)` after `O(1)` individualizations.
  The genuine `s(X)` math; the live frontier (`cxt-scoping.md`).
- **A3 `hcatch`** — the 1-WL↔2-WL bridge (`WarmTwinsAreFiberTwins`); coupled to the seal, free where the scheme-level δ′
  closes, otherwise part of the `c(X_T)` content (the 2026-06-13 `hcatch` finding).

**The route decision:** Option A (citation-free, the landed sparse machinery applied to the extension) over Option B
(cite Ponomarenko Thm 4.1 via `Theorem41Statement` + the pointed transport §CC.9). Both reduce to `ParamBoundOnExtension`
= A2 (§1B of the build doc), so the choice was *clothing*, not difficulty; A1 turned out to reuse landed machinery, so
the citation-free route won. The Thm-4.1 path (`reachesRigidOrCameron_viaExtensionSeparability`) remains landed as a
fallback checkpoint.
