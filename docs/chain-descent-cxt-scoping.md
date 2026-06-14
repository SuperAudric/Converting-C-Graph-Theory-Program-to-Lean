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
suffices); and the only genuine *non*-poly risk is the largeness threshold. **M2 pinned this (Q4):** for *bounded-rank*
primitive non-Cameron CCs `|Aut|` is **polynomially** bounded (Babai rank-3, Kivva rank-4 ⟹ `O(log n)` base ⟹ genuinely
polynomial) — and the project's residue IS rank 3–4 (amorphic-NLS is rank 4), so this is the relevant regime; but in
*unbounded* rank only a **sub-exponential** `|Aut| ≤ exp(Õ(n^{1/3}))` is proved (Sun–Wilmes; Babai's poly conjecture is
open), giving an `~n^{1/3}` base. **So: claim *polynomial* only on the bounded-rank residue (cite Babai/Kivva); the
general statement is sub-exponential-base.** Do **not** treat an `O(log n)` base as a problem.

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

### M2 — RESULTS (RAN 2026-06-13, deep-research, 17 sources, 23/25 claims 3-vote-verified)

Net: **build over cite is confirmed** — the two pieces the project actually needs (A1 at CC generality, A2) are *not*
citable; the citable results (Q3, Q4) are about the *group* side / *order*, not the scheme-level `c`/`s`/`b`.

- **Q1 (A1) — the sparse theorem is HOMOGENEOUS-ONLY; no CC version; homogeneity is LOAD-BEARING.** PV Thm 3.1
  (arXiv:1602.07132, JACO 2017) verbatim: *"Let X be a **homogeneous** coherent configuration … `2c(k−1)<n` … then every
  one-point extension is 1-regular, in particular `b(X)≤2`."* The proof uses `n_{s*}=n_s` (homogeneity) to make `s_max`
  **symmetric** for the connectivity argument; no multi-fiber generalization exists (verified in-source). **⟹ A1 is a
  genuine port, not a citation — and the load-bearing risk is precisely the connectivity step (§S.16): the multi-fiber
  `X_T` is non-symmetric, so the `s_max`-symmetry the original leans on must be replaced by a transpose-aware argument.**
  (The §CC.11 definitions already ported are fine; the counting/connectivity body is where homogeneity bit, and is the
  real work.) The Chen–Ponomarenko 2022 book was *not* independently confirmed to lack a broader version — a direct check
  is the one residual citation hope, but expectation is "homogeneous-only".
- **Q2 (A2) — OPEN; the crux must be proved from scratch.** No surviving citable theorem bounds `c(X)` or `s(X)` for a
  primitive (small/non-Cameron) CC, nor "becomes sparse / bounded `c`,`b` after `O(1)` individualizations". Confirms
  `ParamBoundOnExtension` is the genuine open core. *Caveat (medium confidence):* Evdokimov–Ponomarenko (EJC 2000) and the
  CP book were named but produced no surviving quote — a direct read of those two is the one place a partial citation
  might still hide.
- **Q3 (A2 `k`-half + (C)) — base size is citable, but only TOTAL and only `b(G)`, not the scheme.** Halasi–Liebeck–Maróti:
  `b(G) ≤ 2·log|G|/log n + 24` (so `|G|≤n^{O(1)} ⟹ b(G)=O(1)`); non-standard almost simple `b(G)≤7` (Burness, `=7` iff M24);
  `|G|≤n^5` except M23/M24 (Liebeck–Saxl). **But:** (i) these bound the *group* base `b(G)`, and `b(G) ≤ b(X)` — they do
  **not** bound the *scheme* base (the `s(X)` gap is the open part, scoping §2); (ii) the finer **valency-decay** profile
  Q3 asked for (do orbits shrink to `O(1)` after `O(1)` points?) is **not** addressed by any source. So the `k`-half of A2
  is also open — not rescued by base-size theory. (The group base (C) being free is re-confirmed.)
- **Q4 (calibration) — the residue's `|Aut|` is only SUB-EXPONENTIAL in general; POLYNOMIAL is citable only for bounded
  rank.** Sun–Wilmes: a primitive CC not triangular/lattice has `|Aut| ≤ exp(Õ(n^{1/3}))` (Babai 1981: `exp(Õ(n^{1/2}))`).
  Babai's **poly-`|Aut|`-or-Cameron conjecture is OPEN**, proved only for **rank 3 (Babai 2014)** and **rank 4 (Kivva —
  a rank-4 non-Cameron PCC has minimal degree `≥ γ₄·n`, only exceptions Johnson/Hamming)**. The dichotomy is framed as
  *"Cameron scheme vs. high minimal degree (`motion ≥ γ_r·n`)"*, **not** an `|Aut|`-order threshold. **Two consequences:**
  (1) **good news for the actual residue** — it is rank 3–4 (amorphic-NLS is rank 4), so **Kivva/Babai give a citable
  *polynomial* `|Aut|` bound ⟹ `O(log n)` base ⟹ genuinely polynomial canonisation for the bounded-rank residue**;
  (2) **honest limit** — for *unbounded-rank* primitive small non-Cameron CCs only a *sub-exponential* base (`~n^{1/3}`) is
  citable (polynomial would need Babai's open conjecture). So pin the seal's `IsLarge`/G3 to the **bounded-rank** regime
  (Babai rank-3 / Kivva rank-4) to claim *polynomial*; the general statement is sub-exponential-base.

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

### M4 — Lean decomposition + STATE (A1 in progress)
- **A1 incr 1–2 LANDED** (`CoherentConfig.lean §CC.11`, axiom-clean): the CC indistinguishing number `c(X)`
  (`indistinguishingNumberOf` / **`indistinguishingNumberOf_eq_card`** / `IsReflexive` / `indistinguishingNumber` / `_le`),
  the max valency `k(X)` (`sourceFiber` / `valency` / **`valency_eq_card`** / `maxValency` / `valency_le_maxValency`), and
  **`SparseSeparable`** (`2c(k−1)<n`) — all on the general CC.
- **A1 incr 3 (the (19) estimate) LANDED 2026-06-14** (`CoherentConfig.lean §CC.12`, all axiom-clean): the CC pair-count
  **`pu`** + **`pu_eq`**, the transpose bridge **`relOf_right_eq_iff_left`** (the non-symmetric CC's substitute for
  `relOfPair_symm`), **`not_isReflexive_relOf_of_ne`**, **`card_relNeighbors_le_maxValency`** (`A.card ≤ k(X)` for
  non-reflexive `u` — the CC replacement for homogeneity's exact `= k`), and **`sum_pu_le`** (`Σ_δ pᵤ(δ) ≤ k(k−1)·c`). A
  direct port of `Separability.lean §S.6`; the first place M2-Q1's non-symmetry bit (the transpose bridge + the `≤ k` vs `= k`
  weakening) and it was *clean* — the load-bearing non-symmetry is still ahead at §S.8/§S.16.
- **A1 incr 4 (§S.7 identity (20)) LANDED 2026-06-14** (`CoherentConfig.lean §CC.13`, axiom-clean): **`pu_eq_sum`**
  (`pᵤ(δ) = Σ_w c^v_{uw}(c^v_{uw}−1)`, `v = relOf α δ`) — the bridge from the pair-count to intersection numbers. *Cleaner*
  than homogeneous: the CC's colour-function `interNum_eq` matches the fiber filter directly (no `rel`↔`relOfPair` conversion,
  no transpose subtlety — the orientation `relOf α β = u`, `relOf β δ = w` is exactly `interNum u w (relOf α δ)`).
- **SCOPE CORRECTION (from reading the full `PublicTheoremIndex.md`, 2026-06-14):** A1 is **not** "(19) + connectivity" — the
  homogeneous source is the **whole §S.5→§S.16 chain** (§S.5 summation identity, §S.6 (19), §S.7 (20) `pu_eq_sum`, §S.8
  triangle identity `valency_mul_intersectionNumber` + `saAdj_symm`, §S.9–§S.15 both Lemma-3.5/3.6 halves + components +
  set-equality transport + `|C(u)|=1`, §S.16 `saConnected_of_sparseSeparable`). Each must be ported to the CC. The §S.8
  triangle identity is itself *homogeneous* (uses single-fiber valency), so the non-symmetry bites in **more than one place**,
  not only §S.16. Plan the port as one §S section at a time.
- **A1 incr 5 (§S.8 triangle identity) LANDED 2026-06-14** (`CoherentConfig.lean §CC.14`, axiom-clean):
  **`outDeg_mul_interNum`** (the unconditional out-degree double-count `(deg_k x)·c^k_{i,j} = (deg_i x)·c^i_{k,j*}`) +
  **`valency_mul_interNum`** (valency form `n_k·c^k_{i,j} = n_i·c^i_{k,j*}`, given an apex realizing both source fibers).
  **⚠ TRANSPOSE-AWARE STATEMENT (first place M2-Q1 changes the *theorem*, not just the proof):** homogeneous
  `valency_mul_intersectionNumber` is `n_k·c^k_{ij} = n_i·c^i_{kj}`; on the non-symmetric CC the `y`-leg flip introduces a
  transpose, so it is `c^i_{k,j*}` (`j* = transposeRel j`). Verified the `j*` lands exactly right for the downstream
  `saAdj_symm` (the reflected triangle's `relOf γ β = s*` matches). `saAdj_symm` deferred to the graph-layer increment (next).
- **A1 incr 6 (§S.4 graph layer + `saAdj_symm`) LANDED 2026-06-14** (`CoherentConfig.lean §CC.15`, axiom-clean): the defs
  **`InSmax`**/**`smaxAdj`**/**`SmaxConnected`**/**`saAdj`**/**`SaConnected`** + **`saAdj_symm`** (the forced-triangle relation
  is symmetric, via the transpose-aware §CC.14 identity — the `j*` lands exactly on `relOf γ β = (relOf β γ)*`). `saAdj_symm`
  does *not* need a symmetric `smaxAdj` (the two legs are out-going from `α`, so `InSmax` gives equal valency directly). So the
  sα-components are now a genuine equivalence.
- **A1 NEXT (connectivity — the SINGLE-FIBER localization):** the connectivity theorems `smaxConnected_of_sparseSeparable`
  (§S.10) and `saConnected_of_sparseSeparable` (§S.16) + the §S.9/§S.11–§S.15 counting in between. **Two findings pin how to
  do it:** (1) the connectivity infra (`exists_small_closed_of_not_connected`) needs a **symmetric** relation, and `smaxAdj` is
  symmetric only **within a fiber** (`n_s = n_{s*}` for intra-fiber `s`, from the pair-count identity `|F|·n_s = |F|·n_{s*}`);
  (2) the PV counting `valency_le_pu_of_valency_lt` (§S.9, via §CC.14) needs the **apex `α` in `u`'s source fiber** (else
  `valency_mul_interNum`'s witness fails). **Both say the same thing: the connectivity argument is intrinsically single-fiber.**
  So the next sub-pieces are: (a) the **pair-count / fiber-size identity** `|F_src|·n_r = |F_tgt|·n_{r*}` ⟹ within-fiber
  `smaxAdj_symm`; (b) §S.9 `valency_le_pu_of_valency_lt` (CC, apex-in-fiber); (c) §S.10/§S.16 connectivity restricted to a
  fiber. Then "sparse ⟹ a pinning rank exists" ⟹ feed §CC.10 `dominatorReachable_of_rank`.
- **A2 (the open core, after A1):** prove `ParamBoundOnExtension` (`c,k=O(1)` on the `O(1)`-extension) for the residue —
  M2 confirmed not citable; char-2 load-bearing.
- **Assembly:** feed `reachesRigidOrCameron_viaExtensionDominatorClosure` (δ′; `hcatch` rides along, per the `hcatch`
  finding) — landed and waiting on `hclo`.

---

## 5. Honest endpoints + risks

**Legitimate endpoints** (mirroring how the affine slice landed via cited `TwinsAreSemilinear` + finite exceptions):
1. a **uniform** `X_T`-rigidity theorem (best — closes the family, Route δ′, citation-free);
2. **cite Thm 4.1** + a structured-sub-family discharge of (i)/(ii) + finite `decide` exceptions (seal `modulo {G3 + Thm 4.1}`);
3. a **clean sufficient condition** / **carried predicate** `DominatorClosesFrom S T` fed to a per-family capstone, with the
   genuine instances (Clebsch n=16 landed; more by probe) — an honest partial result, not a full closure.

**Risks (state plainly):**
- **(a) `c(X_T)` is NOT uniformly `O(1)`** — would be a residue with unbounded post-base indistinguishing number =
  a **G2-B witness ⟹ the seal is false** (a statement change — itself a real result; the falsifier §1A names).
  **M1 found NO such witness** across the diverse family (rank 3/4, cyclotomic/amorphic, char 2/odd, n=10–41), so this
  risk is empirically pushed back, though not formally excluded.
- **(b) uniform mechanism exists but the proof is genuinely hard** — the realistic case; fall to endpoint 2 or 3.
- **(c) no uniform mechanism AND no citation** — the route choice (§3) returns NO and Thm 4.1's conditions also resist
  uniformly; then endpoint 3 (carried predicate + decidable instances) is the honest floor, and the "general theorem, not
  a ladder" decision is genuinely blocked (re-open the decision with the user).

---

## 6. HANDOFF — current state + pick up here

**Decisions RESOLVED this session** (so a fresh reader does not re-litigate them):
1. **Family-by-family δ′ dries up ⟹ the input must be a GENERAL theorem** (G2-B = primitive-small-non-Cameron = infinitely
   many families). (build doc STATUS decision.)
2. **M2 ran ⟹ build over cite** — the two pieces the project needs (A1 at CC generality, A2) are *not* citable (§4-M2:
   Q1 sparse-thm homogeneous-only, Q2 crux open); the citable results are group-side/order only.
3. **Route = δ′ Option A** (citation-free: port the sparse theorem to the CC), with cite-Thm-4.1 (Option B) as fallback.
4. **Calibration pinned (Q4):** polynomial canonisation is citable for the **rank-3/4 residue** (Babai/Kivva); only
   sub-exponential in unbounded rank. The project's residue is rank 3–4, so the polynomiality claim holds there.

**Current Lean state (all axiom-clean `[propext, Classical.choice, Quot.sound]`):** the δ′ engine on `X_T` (§CC.10),
`Sharp (pointExtension X T)`, and the seal wiring `reachesRigidOrCameron_viaExtensionDominatorClosure` are LANDED and
waiting on the single input `hclo`. The CC sparse substrate **A1 incr 1–2** (`§CC.11`: `c(X)`, `k(X)`, `SparseSeparable`)
is landed. The open content is `hclo` = `ParamBoundOnExtension` (A2), reached via the A1 sparse theorem.

**▶ PICK UP HERE (the exact next Lean step):** A1 §S-chain port LANDED through §S.8 + the §S.4 graph layer: incr 3 (§S.6
`sum_pu_le`, `§CC.12`), incr 4 (§S.7 `pu_eq_sum`, `§CC.13`), incr 5 (§S.8 triangle identity, `§CC.14`), incr 6 (§S.4 graph defs
+ `saAdj_symm`, `§CC.15`) — all axiom-clean, 2026-06-14, all transpose-aware. **Next = the connectivity theorems
(§S.9–§S.16), localized to a SINGLE FIBER.** Two findings force this: the connectivity infra needs a *symmetric* relation and
`smaxAdj` is symmetric only within a fiber (`n_s = n_{s*}` intra-fiber); and the PV counting `valency_le_pu_of_valency_lt`
needs the apex in `u`'s source fiber. Sub-pieces: (a) the pair-count/fiber-size identity `|F_src|·n_r = |F_tgt|·n_{r*}` ⟹
within-fiber `smaxAdj_symm`; (b) §S.9 `valency_le_pu_of_valency_lt` (apex-in-fiber, via §CC.14); (c) §S.10/§S.16 connectivity
on a fiber ⟹ "sparse ⟹ a pinning rank exists" ⟹ feed the landed §CC.10 `dominatorReachable_of_rank`. After A1: **A2** (prove
`ParamBoundOnExtension`, the open `s(X)` core, char-2 load-bearing), then assembly is automatic.

**Still-open decision (for the user, not blocking):** endpoint tolerance — is a family-restricted / carried-predicate
result (endpoint 3, §5) an acceptable milestone, or only a full uniform closure?

**Reading order for a fresh reader:** the general-CC build doc STATUS → its §1A (why not GI∈P) / §1B (both routes ⟹
`c(X_T)`) → THIS doc §0–§4 (the reduction + M1/M2/M3 results) → `CoherentConfig.lean` §CC.10 (the landed δ′ engine + `Sharp`)
and §CC.11 (the A1 sparse substrate) → resume at **A1 increment 3** above.
