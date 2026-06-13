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

### M1 — PROBE: measure `c(X_T)` and extract the `X_T` mechanism across a DIVERSE family `[do this first]`
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

### M2 — literature check (citable bounds) `[parallel to M1; deep-research-able]`
Search the CC/separability literature for any citable `c(X)` / `s(X)` / domination bound for primitive small CCs:
Evdokimov–Ponomarenko (*Separability number and Schurity number*, EJC 2000 — ref [4]); the Chen–Ponomarenko monograph
(*Coherent Configurations*, ref [3]); Ponomarenko's later separability papers. Goal: know precisely **what is citable vs
must be proved** before investing in a from-scratch proof. (A `/deep-research` run on "separability number / base number
bounds for primitive coherent configurations" is the efficient form.)

### M3 — formulate the precise lemma (the math)
From M1/M2, state the load-bearing lemma at the right generality:
- Route δ′: *"for the residue family, `X_T` (at a bounded base) is forced-triangle-rigid"* — the uniform pinning rule M1
  extracts, fed to `dominatorReachable_of_rank`.
- Route (A)+(B): *"the residue's `X_T` satisfies `DominationCondition`"* — via the parameter bound (needs the `c(X_T)`
  bound) or a direct geometric domination argument (the probe found (ii)-witnesses geometric — check (i) likewise).
Decide uniform-theorem vs structured-sub-family vs honest-carried-predicate (§5).

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

**Immediate next action: M1** — extend the probe to measure `c(X_T)` + extract the `X_T` mechanism across the diverse
family. It is low-cost, de-risks the whole route choice, and is the project's probe-before-Lean discipline.
