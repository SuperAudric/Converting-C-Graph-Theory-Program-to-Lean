# Scoping — the general `c(X_T)` work (the seal's last open quantity)

> **What this is.** A scoping/planning artifact for the ONE open input to the unconditional seal: proving that the
> residue family recovers at a bounded base. It does **not** execute the work — it pins the precise target, shows why
> the two routes converge on one quantity, isolates the irreducible crux, and lays out a probe-first attack with honest
> milestones and endpoints. Read the main build doc (`chain-descent-general-cc-separability.md`) STATUS + §5 first; this
> is the deep-dive on its §5.2 open link. Per the 2026-06-13 decision this is **ONE general theorem, not a family ladder**.

---

## 0. The target, precisely

For the residue family — a **primitive, small, non-abelian, non-Cameron** schurian scheme `S = orbitalScheme H` — prove
there is a **bounded base `T`** with

> `hclo : ∀ v, (pointExtension (S.toCoherentConfig hne) T).DominatorReachable T v`

(the δ′ form), equivalently the **post-base indistinguishing number** `c(X_T) = O(1)` (the parameter form), equivalently
**Thm 4.1's domination condition** holds on `X_T` (the separability form). All three are the *same* quantity (§1; §1B of
the main doc). The Lean objects are already defined: `Separability.indistinguishingNumber` (`c`), `maxValency` (`k`),
`SeparableParam` (`3·c·(k−1)·k < n`); `CoherentConfig.DominationCondition` (Thm 4.1 (i)), `Theorem41Hypotheses`; and the
δ′ engine `CoherentConfig.DominatorReachable` / `dominatorReachable_of_rank` / `allSingletonFiber_of_dominatorClosure_pointExtension`.

**Calibration (the bar is `O(log n)` base, which IS polynomial).** The IR cost is exponential in the base size `b`
(`≈ 2^{O(b)}`), so `b = O(log n)` gives `2^{O(log n)} = n^{O(1)}` — **polynomial**. `exists_greedy_base_le_log` gives
`b ≤ log₂|Aut|`, so a *poly-bounded* `|Aut|` (`n^{O(1)}`) already yields an `O(log n)` base = poly canonization. Hence the
target is not strictly `c(X_T)=O(1)` — it is `c(X_T)` small enough to keep the base `O(log n)` (i.e. `c(X_T)=O(polylog)`
suffices); and the only genuine *non*-poly risk is if "small"/`IsLarge` is pinned at the sub-exponential Babai/Sun–Wilmes
threshold (`|Aut|≈exp(n^{1/3})` ⟹ base `n^{1/3}`) rather than poly. Pin the poly `IsLarge` instantiation; do **not**
treat an `O(log n)` base as a problem.

Feeding either landed checkpoint then closes the seal `modulo {G3 (+ Thm 4.1 if cited)}`:
`reachesRigidOrCameron_viaExtensionDominatorClosure` (δ′, citation-free) or `…viaExtensionSeparability` (cites Thm 4.1).

---

## 1. Why both routes converge on `c(X_T)` (recap of §1B — no escape)

| Route | Owed | Reduces to |
|---|---|---|
| **δ′** (citation-free) | a pinning rank on `X_T` (every positive level forced-triangle-pinned) | forced-triangle abundance on `X_T` = `c(X_T)=O(1)` |
| **(A)+(B)** (cite Thm 4.1) | `DominationCondition` + `CoupleExtensionCondition` on `X_T` | (i) domination ⟸ parameter bound `n > 3·c(X_T)·k(X_T)²` ⟸ `c(X_T)=O(1)` |

The **`k`-half is free**: `maxValency(X_T) ≤ |Aut_T|` (orbit–stabiliser) and the greedy base shrinks `|Aut_T|`
geometrically (landed `exists_greedy_base_le_log`). The **`c`-half — `c(X_T)=O(1)` — is the irreducible crux** for *both*
routes. Citing Thm 4.1 does **not** make it vanish: it repackages "separable" as "conditions (i)/(ii)", and (i) is the
`c(X_T)` content. So the choice of route is a choice of *clothing*, not of difficulty (§1B punchline).

---

## 2. The irreducible crux is NOT free-citable — it is the `s(X)` content

`c(X_T)=O(1)` is essentially the **separability/schurity number** `s(X)` of the residue being bounded. Two tempting
citations do **not** discharge it:

- **Group base-size theory** (Babai; Cameron–Liebeck–Saxl; Liebeck–Shalev; Burness): small/non-standard primitive groups
  have base size `b(G) = O(1)`/`O(log n)`. But **`b(G) ≤ b(X)`** (Cartan ineq. (2)) bounds the *group* base, and the gap
  `b(X) − b(G)` is *exactly* the recovery/`s(X)` content the seal is fighting. Small `b(G)` does **not** bound `b(X)`.
- **Ponomarenko Thm 4.1** reduces `Separable` to conditions (i)/(ii), but (i) = domination = the `c(X_T)` bound. Citing it
  moves the crux, doesn't remove it.

**Honest verdict:** there is (to current knowledge) **no single citable theorem** giving `c(X_T)=O(1)` for *all*
primitive-small-non-Cameron CCs — that statement is itself a substantial piece of open separability theory (proving it
in full generality would resolve a chunk of GI for the class). The cyclotomic instance (Thm 1.1) is the only large
family with a citable `s(X)≤2`, and that is the already-closed affine slice. So the general `c(X_T)` work is genuine
research, and the realistic endpoints are structured (§5).

---

## 3. THE central scoping question (resolve FIRST, by probe)

> **Is there a UNIFORM `X_T`-level forced-triangle mechanism across the residue family** — the parametric analogue of the
> `n=16` rainbow-rigidity, which died by `n=25` at *scheme* level but, per `b(X)=2` for `Z5²`, **must reappear in `X_T`'s
> finer colours**?

Everything downstream branches on the answer:
- **If YES (a uniform structural rule on `X_T`):** prove it directly — **Route δ′, citation-free**: define the rank from
  the rule, discharge per-level pinning via `dominatorReachable_of_rank` on `X_T`. This is the §1A "tame remainder ⟹
  uniform mechanism" belief made operational, now on the *right object* (the extension, where the `n≥25` triangles live).
- **If NO (the mechanism is family-dependent):** fall back to **Route (A)+(B), cite Thm 4.1** + discharge conditions
  (i)/(ii) for structured sub-families + finite `decide` exceptions (mirroring the affine slice). The uniform coverage
  then comes from the *cited* theorem, not from a uniform δ′ rule.

The §1A carve-out predicts **YES** (the residue is tame, 0 witnesses, the n=16 bullseye had a clean uniform rainbow rule).
But that rule was **scheme-level and order-16-only** (probe-refuted as parametric). Whether its `X_T`-level successor is
uniform across `q` and across construction types is **unverified** — and is the single most decision-relevant unknown.

---

## 4. The attack — milestones (probe-first)

### M1 — RAN (2026-06-13, `Theorem41ConditionsProbe.Probe_CXT_ScopingM1`, green) — `c(X_T)=O(1)` is UNIFORM; no falsifier

Measured `c` (the indistinguishing number) collapsing under individualization across a **diverse** family — rank-3 and
rank-4, cyclotomic and not, char 2 and odd, `n = 10..41`:

| scheme | n | rk | `c(X)` | `c(X₁)` | `c(X₂)` | `b(X)` | dom@`X_α` |
|---|---|---|---|---|---|---|---|
| amorph-Z4² | 16 | 4 | 4 | 4 | 0 | 2 | PASS |
| amorph-Z2⁴ | 16 | 4 | 4 | 4 | 4 | 3 | fail@1pt |
| amorph-Z5² | 25 | 4 | 7 | 1 | 0 | 2 | PASS |
| Paley-13/17/29/37/41 | 13–41 | 3 | 5/7/13/17/19 | **1** | 0 | 2 | PASS |
| Petersen | 10 | 3 | 4 | 4 | 4 | 3 | fail@1pt |

**Findings:** (1) bare `c(X)` grows `~(n−1)/2` (dense, unbounded — confirms the bare scheme fails domination), but
**collapses to a small constant after O(1) individualizations, uniformly** — `c(X₁) ≤ 4` across *all* of `n=10..41`
(Paley/`Z5²` → 1; the char-2 schemes `Z4²`/`Z2⁴`/Petersen → 4, a slower collapse). **No scheme shows `c` growing after
individualization — no seal-falsifier.** So **`c(X_T)=O(1)` holds uniformly** — the central belief, now evidence-backed
across a diverse set, not just `n=16`. (2) `dom@X_α` PASS ⟺ `b(X)=2`; the `b(X)=3` schemes fail at *one* point but
collapse at two — i.e. Thm 4.1's domination holds at the `(b−1)`-point extension, consistent, not a falsifier. (3) The
collapse *rate/constant* varies by family (char-2 slower, `b=3`), so a uniform **proof** must handle the char-2 case —
boundedness is uniform, the constant is not.
**Honest caveat (recorded so it is not re-walked):** testing the δ′ forced-triangle *closure on `X_T`* at a base is
**vacuous** — `X_T` at a base is already discrete, so the closure trivially completes. The meaningful signal is the
**`c`-collapse** above (which *is* the forced-triangle abundance: `c=1` triangles abundant ⟺ `c` small) plus the
scheme-level δ′ failing for `n≥25` (forced triangles vanish in `X`'s *own* colours — the order-16 artifact motivating `X_T`).
**§3 verdict:** `c(X_T)=O(1)` is uniform ⟹ a general theorem is plausible; **both routes (δ′ and cite-Thm-4.1) need
exactly this bound** (M1 shows domination holds, so cite-Thm-4.1 is viable; δ′ is its citation-free twin). The route
choice is therefore *citation* (prove `c(X_T)` vs cite Thm 4.1), not *mechanism* — and the proof's hard case is char-2.

### M1 (original plan) — PROBE: measure `c(X_T)` and extract the `X_T` mechanism across a DIVERSE family
Extend `Theorem41ConditionsProbe.cs` (it already builds `X_T` via `CoherentClosure` and checks `DominationCondition`):
- **Measure** `c(X_T)` = `indistinguishingNumber` of the one-point / minimal-base extension, across a *diverse* set:
  amorphic-NLS at several `q` (16, 25, 49, 64), **rank-3 primitive SRGs** (Paley, and other small-aut primitive
  constructions), varying the group — *not just amorphic-NLS*, to test uniformity across construction type, not just `q`.
- **Report:** is `c(X_T)` uniformly small? the constant vs `rank`/`q`/construction? AND **extract the `X_T`-level
  forced-triangle / pinning structure** (the analogue of `Probe_ExtractPinningRank`, but on `X_T`'s colours) — is the
  pinning rule **one structural statement** (e.g. "any `X_T`-rainbow triangle is rigid", or a stabiliser-orbit condition)
  or family-specific? This **answers §3** and chooses the route.
- **De-risk bonus:** any scheme with `c(X_T)` growing with `n` is a *candidate seal-falsifier* (a G2-B witness with
  unbounded base) — flag loudly; that would be a statement change (§5 risk a).

### M2 — the research pass: EXACTLY what to find (the cite-vs-prove boundary for Option A)

> **Purpose.** M3 reduced the citation-free path to three pieces — A1 (port the sparse theorem to the CC), A2
> (`ParamBoundOnExtension`: `c,k = O(1)` on the `O(1)`-extension), A3 (`hcatch`). A1 reuses landed machinery and A3 is
> project-internal; **A2 is the research core.** M2 decides how much of A1/A2 can be *cited* rather than *proved*. Each
> question below is binary-actionable: a YES changes a "prove" into a "cite (hypothesis, G3-pattern)".

**Q1 — Is the sparse/Cartan theorem stated at COHERENT-CONFIGURATION generality? (governs A1)**
The project formalized Cartan **Thm 3.1** (`2c(k−1)<n ⟹ b(X)≤2 ∧ 2-separable`) only for homogeneous `AssociationScheme`.
*Find:* does Ponomarenko–Vasil'ev *Cartan coherent configurations* (arXiv:1602.07132) — or Chen–Ponomarenko's monograph —
state Thm 3.1 (or its `1`-regularity / base-≤2 consequence) for a **general CC / a CC after individualizing points**? If
yes, A1 is a *citation* (carry the statement, G3-pattern) instead of a port. If no (homogeneous only), A1 is the port
(feasible — reuses `saAdj`/`transport`/`saComp` + the §CC.10 δ′ rank engine).

**Q2 — Is there a citable bound on the INDISTINGUISHING NUMBER `c(X_µ)` of the extension of a primitive small CC? (governs A2, the `c`-half)**
*Find:* Evdokimov–Ponomarenko *Separability number and Schurity number of coherent configurations* (EJC 2000, ref [4]) and
Ponomarenko's later separability papers — any theorem of the form *"a primitive (small / non-Cameron) CC has `c(X) = O(1)`
after `O(1)` individualizations"*, or any `s(X)`/`t(X)` bound that implies it. This is the genuine open core; a citable
form would collapse A2 to a citation. **Most likely NOT citable in full** (it is essentially the open content, §2) — but a
*structured* version (e.g. for rank-3, or for cyclotomic/affine which is already the cited slice) may exist and would cover
sub-families.

**Q3 — Is there a citable bound on the MAX VALENCY `k(X_µ)` / point-stabiliser orbit sizes of a primitive small group after `O(1)` points? (governs A2, the `k`-half)**
M1 shows `k(X₂)=O(1)`; `k(X_T) ≤ |Aut_T|` is orbit–stabiliser (free). *Find:* base-size / minimal-degree / distinguishing-
number results for primitive groups — Babai (*order of uniprimitive groups*), Cameron–Liebeck–Saxl, Liebeck–Shalev
(base size ≤ 7 for non-standard almost simple), Burness et al. (explicit small bases) — giving *"a primitive small group's
largest point-stabiliser orbit drops to `O(1)` after `O(1)` individualizations"* (i.e. the **distinguishing/base profile**,
not just `b(G)`). NB `b(G) ≤ b(X)` does **not** suffice (§2); we need the *valency* (orbit-size) decay, a finer statement.

**Q4 — the calibration cross-check (governs poly vs sub-exp, scoping §0).**
Confirm which `IsLarge` threshold the seal's `PrimitiveCCClassification` (G3) instantiates — poly (`|Aut| ≤ n^{O(1)}`) vs
sub-exponential (Babai/Sun–Wilmes `exp(n^{1/3})`). Poly ⟹ `O(log n)` base ⟹ polynomial canonisation (the reminder: that
IS poly); sub-exp ⟹ pin it before claiming *polynomial*. Source: Sun–Wilmes / Babai's quasipoly-GI line + the project's
`IsLargeSchemeViaAut` definition.

**Form.** A single `/deep-research` run keyed on Q1–Q3 ("coherent-configuration base number / separability number bounds;
Cartan coherent configurations; primitive small CC indistinguishing number; primitive group base-size / valency decay").
**Outcome that matters:** for each of Q1/Q2/Q3, *cite (carry as hypothesis)* or *prove* — and a YES on Q1 alone already
makes A1 free, leaving only A2 (the genuine core) and A3.

### M3 — the lemma statements (DRAFTED 2026-06-13) — and a CITATION-FREE candidate

M1 (extended to measure `k` and the parameter bound) sharpened the target: **both `c(X_T)` and `k(X_T)` collapse to
`O(1)` after `O(1)` individualizations**, so the landed sparse bound `2c(k−1)<n` holds *on the extension* for the whole
diverse family. That reorganises M3 into one shared open core + two downstream routes, one **citation-free**.

**The shared open core (both routes — the genuine `s(X)` math):**
> **`ParamBoundOnExtension`.** For the residue family `S`, there is a bounded `m` such that the `m`-point extension
> `E = X_{T'}` satisfies `2·c(E)·(k(E)−1) < n` — i.e. `c(E)=O(1)` **and** `k(E)=O(1)` after `O(1)` individualizations.
> *M1 evidence:* holds with `m=2` across `n=10–41`, rank 3/4, cyclotomic/amorphic, char 2/odd — including the char-2
> `b=3` schemes where `X₂` is genuinely non-discrete (`c=4,k=2`, `2·4·1<n`). A *parameter* statement (two small numbers),
> sharper than "domination" and now carrying the `k`-bound M1 added. **This is the one piece neither route avoids (§2).**

**Option A — CITATION-FREE (the discovery): apply the LANDED sparse theorem to the extension.**
The project already has, citation-free + axiom-clean, `separatesAtBoundedBase_of_sparseSeparable`:
`2c(X)(k(X)−1)<n ⟹ b(X)≤2` (the saAdj forced-triangle connectivity closure completes). "Ruled out" only because the
*bare* residue is dense — but M1 shows the *extension* meets its hypothesis. So:
> - **A1 `SparseClosesCC`** — port `separatesAtBoundedBase_of_sparseSeparable` from homogeneous `AssociationScheme` to the
>   extension `E` (general CC / the warmRefine-refined structure post-`T'`): `2c(E)(k(E)−1)<n ⟹ E discretizes in ≤2 more`.
>   Reuses the landed `saAdj`/`transport`/`saComp` connectivity argument + the **CC δ′ engine `dominatorReachable_of_rank`
>   (§CC.10)** which already consumes a pinning rank — A1 is exactly *"sparse ⟹ a pinning rank exists"*.
> - **A2 = `ParamBoundOnExtension`** (the shared open core above).
> - **A3 the `hcatch` 1-WL↔2-WL bridge** — coupled as always (the homogeneous sparse theorem lands in 1-WL/warmRefine
>   directly; on the CC `E` the conclusion is 2-WL, so the warmRefine descent is still owed — main doc §5.1 + `hcatch` finding).
>
> **A1 + A2 ⟹ `b(X) ≤ m+2` ⟹ `SeparatesAtBoundedBase`, with NO Thm 4.1 citation** (seal `modulo {G3}` only); finite
> small-`n` exceptions (where `2c(k−1)<n` fails for tiny `n` — e.g. `Z2⁴` at one point) by `decide` / one extra base point.

**Option B — cite Thm 4.1 (the fallback).** `ParamBoundOnExtension` (the `3c·k(k−1)<n` form) ⟹ `DominationCondition`
(Lemma 5.2 — a provable double-counting of non-dominators, itself citation-free) ⟹ **[cite `Theorem41Statement`]**
`Separable E` ⟹ [landed pointed transport §CC.9] recovery ⟹ `…viaExtensionSeparability`. Strictly heavier than A (adds
the Thm 4.1 citation *and* still needs `ParamBoundOnExtension`), so **B is the fallback** only if A1 (the CC sparse port)
or A3 turns out harder than the citation.

**Verdict (the user's question — what's possible):**
- **A citation-free path is PLAUSIBLE** (Option A): the M1-confirmed parameter bound on the extension + the *landed*
  sparse theorem ported to the CC. No external citation — `modulo {G3}` only.
- **The irreducible shared open core is `ParamBoundOnExtension`** (`c,k=O(1)` on the `O(1)`-extension) — the `s(X)`
  content of §2, now sharpened to a 2-parameter bound (both M1-evidenced) feeding a *landed* consumer.
- **Char-2 is the load-bearing sub-case** (`k(X₁)` doesn't shrink, `k(X₂)` does ⟹ needs `m=2`).
- **M2 is now targeted:** (1) is `ParamBoundOnExtension` (a `c(X_µ)`/`k(X_µ)` bound for primitive small CCs) citable?
  (2) is the CC sparse theorem (A1) in the literature (Cartan Thm 3.1 at CC generality)? — these decide whether A1/A2 can
  be *cited* vs *proved*; a citation-free *proof* of both looks within reach (A1 reuses landed machinery; A2 is the research core).

### M4 — Lean decomposition (once M3 is pinned)
- **`k`-half** (infrastructure): `maxValency(X_T) ≤ |Aut_T|` and its geometric decay along the greedy base — mostly
  landed-adjacent (`exists_greedy_base_le_log` + orbit–stabiliser).
- **`c`-half** (the M3 crux lemma) — the new mathematics.
- **Assembly:** feed `reachesRigidOrCameron_viaExtensionDominatorClosure` (δ′; `hcatch` rides along with the closure, per
  the 2026-06-13 `hcatch` finding) or `…viaExtensionSeparability` (cite Thm 4.1). Both landed and waiting.

---

## 5. Honest endpoints + risks

**Legitimate endpoints** (mirroring how the affine slice landed via cited `TwinsAreSemilinear` + finite exceptions):
1. a **uniform** `X_T`-rigidity theorem (best — closes the family, Route δ′, citation-free);
2. **cite Thm 4.1** + a structured-sub-family discharge of (i)/(ii) + finite `decide` exceptions (seal `modulo {G3 + Thm 4.1}`);
3. a **clean sufficient condition** / **carried predicate** `DominatorClosesFrom S T` fed to a per-family capstone, with the
   genuine instances (Clebsch n=16 landed; more by probe) — an honest partial result, not a full closure.

**Risks (state plainly):**
- **(a) `c(X_T)` is NOT uniformly `O(1)`** — M1 finds a residue with unbounded post-base indistinguishing number. That is a
  **G2-B witness ⟹ the seal is false** (a statement change — itself a real result). This is the falsifier §1A names.
- **(b) uniform mechanism exists but the proof is genuinely hard** — the realistic case; fall to endpoint 2 or 3.
- **(c) no uniform mechanism AND no citation** — the route choice (§3) returns NO and Thm 4.1's conditions also resist
  uniformly; then endpoint 3 (carried predicate + decidable instances) is the honest floor, and the "general theorem, not
  a ladder" decision is genuinely blocked (re-open the decision with the user).

---

## 6. Decision points for the user
- **After M1:** Route δ′ (if the mechanism is uniform) vs Route (A)+(B)/cite-Thm-4.1 (if family-dependent).
- **M2 timing:** run the literature/deep-research check before committing to a from-scratch `c(X_T)` proof?
- **Endpoint tolerance:** is a family-restricted / carried-predicate result (endpoint 3) acceptable as a milestone, or only
  a full uniform closure?

**M1 + M3 are DONE** (above): `c(X_T)` **and** `k(X_T)` collapse to `O(1)`, the landed sparse bound `2c(k−1)<n` holds on
the 2-point extension uniformly, and M3 drafted a **citation-free candidate (Option A)** — port the landed sparse theorem
to the CC + the shared open core `ParamBoundOnExtension`, no Thm 4.1.
**Immediate next action — pick one:**
- **(A1) STARTED in Lean (`CoherentConfig.lean §CC.11`, axiom-clean, build green 94s):** the first increment ports the
  **indistinguishing number `c(X)`** to the general CC + its geometric counting form (`indistinguishingNumberOf` /
  **`indistinguishingNumberOf_eq_card`**: `c(r) = |{γ : relOf γ α = relOf γ β}|` — the shape §S.16's connectivity argument
  consumes) / `IsReflexive` / `indistinguishingNumber` / `indistinguishingNumberOf_le`, with the non-symmetric transpose
  bookkeeping (`b* = transposeRel b`). **Increment 2 LANDED (`§CC.11`, axiom-clean): the max-valency `k(X)` + sparse
  predicate** — `sourceFiber` / `valency` (via `interNum r r* (sourceFiber r)`, the multi-fiber non-symmetric form) /
  **`valency_eq_card`** (valency = out-degree `|{w:relOf u w=r}|`) / `maxValency` / `valency_le_maxValency` /
  **`SparseSeparable`** (`2c(k−1)<n` on the CC). So `c(X)`, `k(X)`, and the sparse hypothesis are all now defined on the
  general CC. **NEXT A1 increment:** the §S.6 (19)-estimate `Σ_δ pᵤ(δ) ≤ k(k−1)c` (the workhorse counting, via
  `indistinguishingNumberOf_eq_card`) ⟹ the §S.16 connectivity (`saConnected`-analogue) ⟹ *"sparse ⟹ a pinning rank
  exists"* feeding the §CC.10 `dominatorReachable_of_rank`. That counting+connectivity body is the bulk of the remaining port.
- **(M2) targeted literature/`deep-research`:** is `ParamBoundOnExtension` (a `c`/`k` bound for primitive small CC
  extensions) or the CC sparse theorem citable? — fixes how much of A1/A2 must be proved vs cited.
- **(A2) the research core:** prove `ParamBoundOnExtension` (`c,k=O(1)` on the `O(1)`-extension) for the residue family —
  the genuine `s(X)` math, char-2 load-bearing. Hardest; do after A1 makes the consumer concrete.
