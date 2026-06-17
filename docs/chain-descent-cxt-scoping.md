# Scoping — A2: bounded WL-dimension of the residue (the seal's last open quantity)

> **What this is.** The live planning doc for the **one open input to the unconditional seal**: A2 — proving the
> residue family recovers at a bounded base, i.e. `c(X_{T₀}), k(X_{T₀}) = O(1)` at an `O(1)` base. It pins the precise
> target, records the evidence (probe) and the cite-vs-prove research (A2 is OPEN / not citable), and lays out the
> attack toward the *unconditional* seal with an honest tractability verdict. **A1 is DONE** — its build history + the
> abandoned PV-port live in `chain-descent-a1-cc-substrate.md` (split out 2026-06-14 to keep this doc A2-focused). Read
> the build doc `chain-descent-general-cc-separability.md` STATUS first; this is the deep-dive on its open link.
>
> **★ CURRENT FRONTIER POINTER (2026-06-17): this doc is the A2 *scoping*; the live attack + current state is
> [`chain-descent-a2-potential-route.md`](./chain-descent-a2-potential-route.md) §9.9 (esp. §9.9.6 + §9.9.7).** Since this
> doc was written, the entire thin-side cascade is PROVED end-to-end (`BoundedMinMult` → cleanup → cascade → poly seal,
> `§CC.22b–d`, axiom-clean), D1 cover-rigidity is landed (`§CC.22c`: `confusionMultiplicity_perm` — load is `Aut`-invariant),
> and the D3 dichotomy capstone `reachesRigidOrCameron_viaBoundedMinMult` reduces the seal to **one computable predicate
> `hSmallAutThin` = "small-Aut residue ⟹ bounded `minMult`"** = thick⟹large-Aut = node 4 = the wall (route-doc §9.9.7).
> The "route 3 = carry the predicate" floor below now means carrying `hSmallAutThin`; the route-2 (poly) target = discharging
> it for the non-geometric core. Next builds: node-2 rung (affine via `dominatorReachable_of_rainbowRank`) / Spielman floor.

---

## 0. The target, precisely (what A2 must deliver)

A1 reduced the seal's open input to a single threshold. A2's deliverable (the crisp interface, `§CC.19`):

> **Bound `c(X_{T₀}), k(X_{T₀}) = O(1)` at one `O(1)` base `T₀`** — then `allSingletonFiber_of_card_gt_subset` makes
> every `T ⊇ T₀` with `|T| > (k(X_{T₀})−1)·c(X_{T₀})` a base of `X`, and the seal closes.

Here `X_T = pointExtension (S.toCoherentConfig hne) T` for the residue `S = orbitalScheme H` (**primitive, small-`|Aut|`,
non-abelian, non-Cameron** schurian; bullseye rank 3–4), `c = indistinguishingNumber`, `k = maxValency`. This is the
**bounded WL-dimension / bounded base number `b(X)`** of the residue — the genuine `s(X)` content. The Lean objects are
all landed (`§CC.11`–`§CC.19` + the seal wiring `reachesRigidOrCameron_viaBoundedExtensionParams`, `§S-gate2`); only the
bound itself is open.

**Calibration (the bar is `O(log n)` base, which IS polynomial).** IR cost `≈ 2^{O(b)}`, so `b = O(log n)` ⟹
`2^{O(log n)} = n^{O(1)}` — polynomial. So the target is not strictly `c, k = O(1)` — it is small enough to keep the base
`O(log n)` (e.g. `c = O(1), k = O(log n)` gives `(k−1)c = O(log n)` ⟹ `O(log n)` base ⟹ poly). The only genuine *non*-poly
risk is the largeness threshold: **M2-Q4** — for *bounded-rank* primitive non-Cameron CCs `|Aut|` is polynomially bounded
(Babai rank-3 / Kivva rank-4) ⟹ `O(log n)` base ⟹ genuinely polynomial; in *unbounded* rank only sub-exponential
`|Aut| ≤ exp(Õ(n^{1/3}))` is proved. **The residue is rank 3–4, so claim *polynomial* there; the general statement is
sub-exponential-base.** Do **not** treat an `O(log n)` base as a problem.

---

## 1. Why everything reduces to `c(X_T)` (no escape)

| Route | Owed | Reduces to |
|---|---|---|
| **δ′** (citation-free, the landed route) | a pinning rank on `X_T` | forced-triangle abundance = `c(X_T)=O(1)` (A1 §CC.18 made this `(k−1)c<\|T\|`) |
| **(A)+(B)** (cite Thm 4.1) | `DominationCondition` on `X_T` | (i) domination ⟸ `n > 3·c(X_T)·k(X_T)²` ⟸ `c(X_T)=O(1)` |

The **`k`-half is "free-ish"**: `maxValency(X_T) ≤ |Aut_T|` (orbit–stabiliser) and the greedy base shrinks `|Aut_T|`
geometrically (`exists_greedy_base_le_log`) — **but** this bounds the *group* side; the WL-valency `k(X_T)` can exceed
the orbit valency (the WL-dim gap), so `k(X_T)=O(1)` is itself WL content, not free. The **`c`-half is the irreducible
crux** for both routes. Citing Thm 4.1 only repackages `c(X_T)` as condition (i); it doesn't remove it. **All uniform
statements of A2 are inter-derivable and equal:** `c(X_T)=O(1)` ⟺ bounded `b(X)` ⟺ bounded WL-dim ⟺ schurian
self-detection (`RelCountsDetermineOrbit` at base+O(1)) ⟺ `s(X)=O(1)`. There is no reformulation that cheaply collapses
the family-ladder — a "pattern" that resolves it *is* this theorem (§5).

---

## 2. The crux is NOT free-citable — confirmed twice (M2 + A2-research)

`c(X_T)=O(1)` is the separability/schurity number `s(X)` of the residue being bounded. **Two deep-research passes confirm
it is OPEN / not citable:**

- **M2 (2026-06-13, 17 sources):** no citable theorem bounds `c(X)` / `s(X)` for a primitive small/non-Cameron CC. Group
  base-size theory (Halasi–Liebeck–Maróti `b(G) ≤ 2log|G|/log n + 24`; Burness `b(G)≤7`) bounds the *group* base, and
  `b(G) ≤ b(X)` — the gap `b(X) − b(G)` is exactly the `s(X)` content. Evdokimov–Ponomarenko give constant `s(C)/t(C)`
  only for *named* families and only in the *imprimitive* 3/2-homogeneous case.
- **A2-research (2026-06-14, 19 sources, 20/25 verified):** confirms it from the *distinct* SRG-WL-dimension literature.
  Babai rank-3 (I/II) and Kivva rank-4 (JCTB'23) bound **|Aut| / minimal-degree / thickness / fixity** under a Cameron
  dichotomy, **not** WL-dim / `b(X)` / `c(X)`. Only general WL-dim ceiling is **linear** (0.15n, Schneider–Schweitzer
  ICALP'25; 0.05n even for fiber ≤ 7). See §4 for the strategically important *positive* findings.

**Verdict:** there is no single citable theorem giving `c(X_T)=O(1)` for the residue. A2 is genuine open research
(proving it in full would resolve a chunk of GI for the class). The only citable slice is cyclotomic `s(X)≤2` = the
already-closed affine slice. So the realistic endpoints are structured (§5–§6).

---

## 3. The central strategy question: uniform proof, or infinite ladder?

> **Can A2 be closed by a *uniform* argument (the unconditional seal), or only family-by-family (an infinite ladder)?**

The residue contains infinitely many families, so family-by-family never closes. Closure ⟺ a uniform statement — and
every uniform statement is the same open theorem (§1). So a "collapse the ladder" route must find a *proven* uniform
implication, not an empirical pattern; the families' common cause is exactly `c=O(1)` (circular) unless a *deeper* cause
is found. **The bounded rank (3–4) bounds the collapse target:** the ladder collapses to the **rank-3 base case**
("primitive, large-motion, non-conference SRG ⟹ `b(X)=O(log n)`"), with rank-4 amorphic morally easier (finer scheme).
That base case is "morally known" (Babai's quasipoly-GI algorithm individualizes few vertices for exactly these SRGs;
CGGP proves a family) but has **no portable proof**. §5 is the attack on it; §4 is why it's believable.

---

## 4. The evidence — probe (true) + research (carve validated, no falsifier)

### 4.1 — M1 probe (2026-06-13, `Theorem41ConditionsProbe.Probe_CXT_ScopingM1`, green): `c(X_T)=O(1)` is uniform

| scheme | n | rk | `c(X)` | `c(X₁)` | `c(X₂)` | `b(X)` |
|---|---|---|---|---|---|---|
| amorph-Z4² | 16 | 4 | 4 | 4 | 0 | 2 |
| amorph-Z2⁴ | 16 | 4 | 4 | 4 | 4 | 3 |
| amorph-Z5² | 25 | 4 | 7 | 1 | 0 | 2 |
| Paley-13/17/29/37/41 | 13–41 | 3 | 5/7/13/17/19 | **1** | 0 | 2 |
| Petersen | 10 | 3 | 4 | 4 | 4 | 3 |

Bare `c(X)` grows `~(n−1)/2` (dense) but **collapses to a small constant after O(1) individualizations, uniformly**
(`c(X₁) ≤ 4` across `n=10–41`, rank 3/4, cyclotomic/amorphic, char 2/odd). **No falsifier** (no scheme shows `c` growing).
`k(X₂)=O(1)` likewise. **Char-2 is the hard case** (slower collapse, `b=3`, needs `m=2`). So the target is *true*; the
constant varies by family but boundedness is uniform. (Caveat: testing the δ′ *closure* on `X_T` at a base is vacuous —
`X_T` is discrete there; the signal is the `c`-collapse.)

### 4.2 — A2-research (2026-06-14): the strategically decisive findings

- **The carve-out is VALIDATED.** Babai's SRG structure theorem (n≥29): a primitive SRG is either large-motion (≥ n/8 —
  the residue) OR triangular/Johnson `T(m)` / lattice/Hamming `L₂(m)` / disjoint-cliques — and those hard families all
  have **thickness ≥ √n = LARGE |Aut|** (→ Cameron) or are imprimitive. The one primitive base-size obstruction,
  **conference/Paley** (`O(log n)` base, unimproved 40 yrs), is **cyclotomic = abelian → leg B / the cited affine slice.**
  So every known unbounded/large-WL SRG is *already carved out* of the residue.
- **POSITIVE (decoupling).** The Fon-Der-Flaass / CGGP family (Combinatorica'25, arXiv:2312.00460) — `n^Ω(n^{2/3})`
  same-parameter primitive SRGs with **trivial automorphism groups** (small-`|Aut|`, non-Cameron = the residue) — ALL
  have **WL-dim ≤ 4**, via `base ≤ 2 ⟹ WL-dim ≤ 4` (affine-plane geometry, BCN Thm 3.3.8). So bounded WL-dim is
  **decoupled from `|Aut|`-largeness** — the residue *can* be tame, and this is the closest published positive mechanism.
- **NO falsifier found** — no primitive small-`|Aut|` SRG with provably unbounded WL-dim was located (nor formally excluded).

Net: the conjecture (residue has bounded WL-dim) is well-supported, and the hard cases are carved out — but no uniform
theorem covers the residue.

### 4.3 — The recovery-witness roster: seven empirical falsifiers, 0 G2-B witnesses

The "no falsifier" claim above (and the build/route docs' "seven empirical falsifiers returned 0 witnesses") is this
roster — every targeted hunt for a primitive-small-non-Cameron scheme that *fails* to recover at a bounded base. All
recovered; a witness would be a statement-change (the seal false). This is the standing evidence the carve is right;
the **row-4 probe (route 3 / route-doc §5) extends exactly this roster** toward the one gap with no scalable data.

1. **Hanaki–Miyamoto catalogue** — 2363 schemes, all 481 primitive recover.
2. **affine `ΓL(1,2^d)` sweep** + **3. non-solvable `A_n` sweep**.
4. **non-affine `PGL(2,p)`-on-2-subsets** (`NonAffinePrimitiveProbe.cs`, 2026-06-10): 6 almost-simple poly-order
   schemes, orders 28–276, depth 2.
5. **Theorem-3.1 density** (`CatalogueSchemeProbe.Probe_Theorem31_DensityBoundary`, 2026-06-11).
6. **non-affine Latin-square** (`CatalogueSchemeProbe.Probe_AmorphicResidue_LatinSquare`, 2026-06-11): non-group
   LS-graphs n≤100, flat depth 2–3.
7. **PSL(2,q) exceptional-coset** (`CosetSchemeProbe.Probe_PSL2_ExceptionalCosets`, 2026-06-11): 7 primitive non-affine
   `orbitalScheme(PSL(2,q)/{A₅,S₄})`, rank 4–9, index 57–620, all recover WL-depth 2–3.

Plus **the amorphic-NLS bullseye** (`PdsAmorphicSchemeProbe.Probe_AmorphicNLS_Order16`, 2026-06-11): the on-target
primitive G2-B data point — `ℤ₄²` carries the rank-4 equal-valency amorphic-NLS Clebsch SRG(16,5,0,2) and **recovers at
WL-depth 2** (fails depth-1 `EdgeGenerates` = the amorphic-`S₃` gap, separates at base+O(1)); `ℤ₂⁴` depth 3. Probe
methodology gotchas (use Aut's OWN orbital scheme; prune+node-cap brute force) + the full record:
[`Archive/ChainDescent/chain-descent-steers-archive.md`](./Archive/ChainDescent/chain-descent-steers-archive.md) §6.

---

## 5. The attack on the unconditional seal (routes, ranked)

The unconditional goal needs A2 uniformly. The honest verdict (from §2–§4): **fully unconditional is not tractably
reachable by known means — it requires resolving the rank-3 base case, which is open.** The ladder collapses to *one*
hard theorem, not a cheap pattern. The routes, ranked by tractability-toward-unconditional:

1. **Probe-mine the collapse invariant (the prerequisite; cheap, concrete, DO FIRST).** Sweep the *primitive
   non-conference* residue broadly (rank-3 non-geometric SRGs, rank-4 amorphic, varied constructions, larger `n`) and
   correlate `b(X)`/`c`/`k` against structural invariants — spectral gap, eigenvalue multiplicity, p-rank / Smith form,
   "geometricity." Goal: does a *single* invariant provably control the base **and** is it provably bounded on the
   residue? YES → a real collapse mechanism to attempt (route 2). NO → confirms the conditional (route 3) is the floor.
   This is the "notice the pattern" step; it can't waste effort (sharpens both 2 and 3). Extend `Theorem41ConditionsProbe`.

2. **Attack the rank-3 base case (the path to unconditional; research-hard).** Re-derive Babai's non-conference-SRG
   splitting as a **base / WL-dim bound** (not an `|Aut|` bound), using the abelian/conference carve-out to dodge his
   published bottleneck. The genuine open math; no guarantee, but it's *one* problem, not infinitely many, and the probe
   (route 1) feeds it the candidate invariant. Rank-4 amorphic is morally easier (finer) — though not a clean reduction
   (constituents may be large).

3. **Collapse to one named conjecture (the honest floor; near-done).** Sharpen the carried `viaBoundedExtensionParams`
   predicate into a single named hypothesis — *"every primitive non-Cameron rank-≤4 CC has `b(X) = O(log n)"`* — and
   carry it. Collapses the infinite *family*-ladder to **one predicate**; the seal stands `modulo {G3 + one conjecture}`.
   Not unconditional, but the sharpest honest end-state — and essentially the wiring already landed (§S-gate2).

**Recommendation (toward the stated unconditional goal):** route 1 → route 2, with route 3 as the guaranteed floor.
Unconditional closes *iff* route 2 yields; that's the single point of risk. **Update (2026-06-15): the probe (route 1)
ran** (`A2MonovariantProbe`, incl. `Probe_SmallestEigenvalueAxis`) and reframed the obstruction as the *partial-geometry
line system* (not the eigenvalue magnitude); the attack is now the **potential-drop / G-mech build-order** — see §6
PICK-UP and `chain-descent-a2-potential-route.md` §4c.

---

## 6. Honest endpoints, risks, and handoff

**Legitimate endpoints** (mirroring the affine slice's cited-`TwinsAreSemilinear` + finite-exceptions closure):
1. a **uniform** rank-3 (then rank-4) base-size theorem — the unconditional goal (route 2; research-hard);
2. a **structured-sub-family** discharge (CGGP `base≤2⟹WL≤4`, the affine slice) — partial, real, but a ladder;
3. a **carried predicate** (route 3) fed to the landed capstone — the honest floor, `modulo {G3 + one conjecture}`.

**Risks (plain):**
- **(a) `c(X_T)` NOT uniformly bounded** — a primitive small non-Cameron scheme with unbounded base = a **G2-B witness ⟹
  the seal is false** (a statement change; the §1A off-track falsifier). M1 + A2-research found **no witness** (and the
  carve-out removes every known unbounded-WL family), so empirically pushed back — not formally excluded. The probe
  (route 1) is also the falsifier hunt.
- **(b) uniform mechanism exists but the proof is genuinely hard** — the realistic case (the rank-3 base case); fall to
  endpoint 3.
- **(c) no clean invariant emerges** — route 1 returns nothing portable; endpoint 3 (carried predicate) is the floor.

**▶ PICK UP HERE (Stage 1b discharge — the G-mech build-order, route-doc §4c):** **A1 + the A2 interface + the
potential-drop engine + the Stage-1b `c`-halving reduction + the discharge framework are all LANDED** (`§CC.11`–`§CC.22`
+ `§S-gate2`, axiom-clean, build green). The seal is sharpened to **`modulo {G3 + IndistinguishingHalves + hcatch +
hImprim}`** (`IndistinguishingHalves` = some individualization halves `c(X_T)` alone; `k` rides free —
`potentialDrops_of_indistinguishingHalves`). The discharge of `IndistinguishingHalves` is the open heart, and its plan is
the route-doc **§4c build-order**:
- **Step 1 ✅ LANDED** — the **G-mech kill lemma** (`§CC.22`: `relOf_v_eq_of_confused` + `confusionSet_eq_empty_of_relOf_v_ne`):
  a `v` that *distinguishes* `α,β` annihilates `C(α,β)` in `X_{T∪v}`. ⟹ `c(X_{T∪v}) ≤ max{|C_{X_T}(α,β)| : v∈C(α,β)}`,
  so a `v` outside all over-half confusion sets halves `c`.
- **Step 2 ✅ LANDED** (2026-06-15, `§CC.22`) — the bound `indistinguishingNumber_pointExtension_insert_le`: `c(W) ≤ M`
  if every `v`-undistinguished `X_T`-pair has confusion `≤ M` (via `Finset.sup_le` over non-reflexive `W`-classes + the
  kill lemma + `Refines`-monotonicity). **Dissolved the G-sim gap** (one covering hypothesis on `v` replaces the per-class splitter).
- **Step 3 ✅ LANDED** (2026-06-15, `§CC.22`) — halving wiring `indistinguishingHalves_of_exists_avoiding_v`
  (`∃v` avoiding all big confusion sets per over-`B` base `⟹ IndistinguishingHalves`, pure arithmetic at `M=c/2`).
  **The entire open content is now exactly the existence of an avoiding `v`.**
- **Step 4 ✅ LANDED** (2026-06-15, `§CC.22`) — the `BigConfusionCover` obstruction predicate (`>c/2` confusion sets
  cover `Fin n`) + `exists_avoiding_of_not_cover` (`¬cover ⟹ ∃ v avoiding`) + the capstone-facing wiring
  `indistinguishingHalves_of_not_bigConfusionCover` (`∀T over-B, ¬cover(X_T) ⟹ IndistinguishingHalves`). §CC.21
  balanced-splitter defs parked (left in place) as the 1-WL-cell model. **The entire open content of A2 is now packaged
  as one predicate: `¬ BigConfusionCover (X_T)`.**
- **Step 5 (G-cite) ✅ LANDED** (2026-06-15, the conditional capstone + non-vacuity, then citations SEPARATED) — the
  capstone `reachesRigidOrCameron_viaNoConfusionCover` factors the dichotomy `cover ⟹ Cameron`: the **Cameron step
  reuses the canonical G3** `hClassify` (via `exhaustiveObstruction_scheme`), the only **new** citation is the **Neumaier
  direction** `hNeumaier : (∃ T over-B, BigConfusionCover (X_T)) → IsLarge` (case-split: cover → IsLarge → primitive → G3
  → Cameron / imprimitive → `hImprim`; no cover → `…viaShattering`) + the non-vacuity counting
  `card_bigClasses_mul_ge_of_cover` (`cover ⟹ n ≤ #bigClasses·c`, the explicit near-pencil structure).
  **The §4c build-order is COMPLETE, and the citation is sealed up.** Seal **`modulo {G3 (hClassify) + hNeumaier +
  hcatch + hImprim}`**. **★ Faithfulness scoped (2026-06-16, route-doc §8):** `hNeumaier`'s faithful citation is **Babai's
  SRG structure theorem (rank 3) + Kivva (rank 4), NOT "Neumaier"** ("geometric ⟹ large Aut" alone is false — CGGP), and
  it is faithful **only at the sub-exponential largeness threshold**; the polynomial version is the open rank-3 base case
  (this §5 route 2). So the seal is **sub-exponential-base** at its established citation thresholds; polynomial is
  GI-adjacent open. Residual risk = `hNeumaier`'s row-4 faithfulness — i.e. exactly **route 3, the honest floor (§5)**.
  Full citation map + what proving each takes: **route-doc §8**.

**Read `chain-descent-a2-potential-route.md` STATUS + §4c first.** The probe (`A2MonovariantProbe.cs`, 2026-06-15)
reframed the row-4 gap: the drop-obstruction is the **partial-geometry line system**, not the smallest-eigenvalue
magnitude (§4 there). The conditional-predicate floor is route 3, retained. Old probe plan archived:
`Archive/ChainDescent/chain-descent-a2-monovariant-probe.md`.

**▶ FRONTIER MOVED (2026-06-16) — the live work is now route-doc §8–§9, not §4c.** Citation adjustment Phases 1–2 landed
(the faithful-direction capstone `reachesRigidOrCameron_viaSmallAutShatters`; §8.5). The `B(n)` research (§8.6) confirmed
route 1/route 3's verdict: **polynomial is the OPEN rank-3 base case — no citation reaches it** (sub-exp `Õ(n^{1/3})` = Spielman
is the citable floor). The poly side was decomposed into **five nodes by line-system structure (§9.0)**; the open crux is
**node 4** (primitive non-geometric non-conference SRG), anchored by `reachesRigidOrCameron_viaNoCover` (node-4 ⟹ poly seal, no
largeness citation). Best handle = the **multiplicity reframe (§9.6):** node 4 ⟺ confusion-cover multiplicity `L` bounded
(computable). This §5 route-2 (the rank-3 base case) = node 4.

**▶ FRONTIER (2026-06-16, HANDOFF) — multiplicity probe DONE, endgame scoped, PART 1 LANDED (route-doc §9.7.1–§9.7.2, §9.8).**
The probe killed the tight/loose (2a) framing (covers are intrinsically loose; the axis is multiplicity *magnitude*) and showed
the residue separates from Cameron cleanly **on its amorphic scheme** (not the rank-2 graph). **Endgame correction:** polynomial
is NOT "unreachable" — that earlier claim wrongly imported the *citation* route's sub-exp ceiling; the seal's split is
large-Aut→G3 / small-Aut→cascade (no SRG citation beyond G3), so **polynomial-unconditional-`modulo {G3+hcatch}` is the target,
reachable in principle** (= this §5 route 2, open & hard but unbarred; route 3 = fallback). **PART 1 (cascade-rate engine)
LANDED, axiom-clean** (`§CC.20b`/`§S-gate2`): `BoundedConfusionMultiplicity B M ⟹` `O(M·log n)` base, capstone
`reachesRigidOrCameron_viaBoundedMultiplicity` — "residue cascades ⟹ polynomial seal" is now a theorem; the lone open content is
the discharge `BoundedConfusionMultiplicity`. **NEXT = PART 2: discharge it** (sub-classes first — PV sparse re-activation, then
the generic rank-3 core). Read route-doc §9.7.1–§9.7.2 + §9.8.

**Reading order for a fresh reader:** build doc STATUS → its §1A (why not GI∈P) / §1B (everything ⟹ `c(X_T)`) → THIS
doc §0–§5 (the A2 target, evidence, and the route to the unconditional seal) → `CoherentConfig.lean §CC.10`–`§CC.19` (the
δ′ engine + the A1 abundance substrate + the A2 monotonicity interface) → `chain-descent-a1-cc-substrate.md` only if the
A1 build detail / route-not-taken is needed.
