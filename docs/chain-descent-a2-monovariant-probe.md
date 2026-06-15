# A2 — the monovariant probe (does a potential drop geometrically per seed?)

> **What this is.** A small investigatory plan + probe for the one question that decides whether A2 closes
> *uniformly and Lean-portably* or only via a carving ladder. Live frontier doc is
> [`chain-descent-cxt-scoping.md`](./chain-descent-cxt-scoping.md) (§5 routes, §6 handoff); the build map +
> A1 substrate are [`chain-descent-general-cc-separability.md`](./chain-descent-general-cc-separability.md)
> and [`chain-descent-a1-cc-substrate.md`](./chain-descent-a1-cc-substrate.md). Read those for context; this
> doc is scoped to one experiment.

---

## 1. The question

A1 reduced the seal's open input to: **bound `(k(X_T)−1)·c(X_T)` at a small base `T`** for the primitive /
small / non-abelian / non-Cameron residue. Equivalently (the dynamical reframe, cxt-scoping §5): individualize a
few "seed" vertices and let 1-WL propagate — the cost is the seeds (propagation is free), and the seed count is
the number of times propagation **stalls** (a `c`-tie that no forced triangle breaks).

The only route to an **unconditional, Lean-portable** A2 is a **potential-drop argument**:

> **Monovariant hypothesis.** There is a potential `Φ` (a structural quantity of the 1-WL-refined,
> partially-individualized configuration) that drops by a constant *factor* `ρ < 1` per seed on the non-carved
> residue. Then `O(log n)` seeds drive `Φ → 1` (discrete), uniformly.

The group side already has this for free (`|Aut|` at least halves per genuine seed → `b(G) ≤ log₂|Aut|`,
`exists_greedy_base_le_log`). A2 is the *same statement for a scheme-level potential*, where the geometric drop
is **not** known. This probe asks, empirically: **does such a `Φ` exist?**

## 2. Why it decides the route (calibration)

- **Yes — a `Φ` drops by a constant factor on the residue, and plateaus / drops slowly on the carved families.**
  Then we have a candidate uniform theorem (the potential argument, families A1/A3 in cxt-scoping §5), and it is
  the *only* outcome that is simultaneously a real proof and Lean-portable. Pursue it.
- **No clean factor, but a clean carve** (some invariant cleanly separates the stallers from the tame).
  Then we are in the carving regime (Family B) — expect a finite ladder (Neumaier / eigenvalue-multiplicity /
  p-rank rungs), not a uniform theorem. The conditional-predicate seal is the honest floor.
- **No factor and no carve** (a tame-looking residue graph stalls as badly as a carved one). That would be a
  warning the residue is not as tame as the no-falsifier record suggests — itself a finding.

`O(log n)` is the target (poly); `O(1)` would exceed expectations (it has so far). The probe measures the actual
drop, so it distinguishes these.

## 3. Candidate potentials + correlates

**Per-step potentials** (recomputed at each individualization depth `t`, on the 1-WL fixpoint):
- **`Φ_cell` = max 1-WL cell size** — the primary monovariant. `Φ_cell = 1` ⟺ discrete. Its drop factor
  `Φ_cell(t+1)/Φ_cell(t)` is the headline measurement.
- `#cells` (the inverse view), and the implied `c`/`k` proxies (max cell pins `c`; cell out-degree spread pins `k`).

**Per-graph correlates** (computed once, to test what *predicts* the base — the carving invariants of Family B):
- parameters `(n,k,λ,μ)`;
- spectrum + eigenvalue multiplicities (closed form from SRG params; **conference ⟹ min-mult `(n−1)/2`**);
- **p-rank** mod 2 and mod 3 (the finest classical SRG invariant; Brouwer–Peeters–Sin).

The hypothesis to test against the correlates: does the base track min-eigenvalue-multiplicity, or p-rank, or
neither — i.e. is the monovariant *structural* (beyond spectrum/parameters)?

## 4. The sweep — residue vs carved-contrast

Each graph is a small SRG constructed in-code (Cayley / combinatorial), with `(n,k,λ,μ)` and SRG-validity verified.

| Class | Graphs | Expected |
|---|---|---|
| **RESIDUE** (tame, the A2 target) | Shrikhande `(16,6,2,2)`, Clebsch `(16,5,0,2)`, Clebsch-complement `(16,10,6,6)` | small base, **geometric `Φ_cell` drop** |
| **CARVED — lattice/Hamming** (Cameron, geometric) | rook `L(m)` `(m²,2(m−1),m−2,2)`, `m=4,5,6` | **large base ≈ √n**, slow drop |
| **CARVED — Johnson** (Cameron) | triangular `T(m)` `(C(m,2),2(m−2),m−2,4)`, `m=6,7,8` | large base, slow drop |
| **CARVED — conference** (cyclotomic → abelian leg B) | Paley`(q)`, `q=13,17,29,37` | reported (base likely small but consumed by a *different* leg) |

**The headline test: Shrikhande vs rook `L(4)`.** Both are `(16,6,2,2)` and are **cospectral** (identical
parameters *and* identical eigenvalues/multiplicities). If they show **different base / drop**, then base size is
**not** a function of parameters or spectrum — it is genuinely structural, and the probe must check whether a
finer invariant (**p-rank** separates them: `L(4)` and Shrikhande have different 2-rank) tracks it. This single
pair is the cleanest possible isolation of "what is the monovariant a function of."

## 5. Measurement protocol

For each graph:
1. Verify it is an SRG; record `(n,k,λ,μ)`, spectrum/min-mult, 2-rank, 3-rank.
2. **Greedy-best 1-WL individualization** (an upper bound on `b(X)`, and a witness that a fast-drop sequence
   exists): from `S = ∅`, at each step try every vertex in a non-singleton cell, individualize the one whose
   1-WL refinement minimizes the resulting max cell, append it. Record `Φ_cell(t)` for `t = 0,1,…` until discrete.
3. Report: base `= |S|` at discreteness, the `Φ_cell` curve, and the **worst per-step drop factor**
   `max_t Φ_cell(t+1)/Φ_cell(t)` (closest to 1 = worst stall; a geometric drop keeps every factor `≤ ρ < 1`).

All residue/carved outcomes are **reported, not asserted** (every answer is a finding); only SRG-validity and the
two cospectral params are asserted (checker faithfulness).

## 6. Success criteria

- **Monovariant candidate found** if every RESIDUE graph keeps `Φ_cell(t+1)/Φ_cell(t) ≤ ρ` for a uniform
  `ρ < 1` (geometric), while at least the lattice/Johnson carved graphs show a plateau (factor ≈ 1 for several
  steps). Then `Φ_cell` (max cell size) is the candidate potential for the A1/A3 portable argument.
- **Carve found** if `Φ_cell` does *not* drop geometrically on the residue but some correlate (min-mult /
  p-rank / smallest eigenvalue) cleanly separates large-base from small-base graphs. Then record the carve as a
  Family-B rung.
- **The cospectral verdict:** does `b(Shrikhande) ≠ b(L(4))`? If yes, base is sub-spectral; report which of
  {2-rank, 3-rank} separates them — that is the candidate carving invariant.

## 7. Caveats

- **1-WL, not 2-WL.** `Φ_cell` is the `warmRefine` (1-WL) potential — the object the canonizer's cost model
  actually uses. `c(X_T)` is a 2-WL/coherent quantity; A1 connects them, and the `hcatch` gap is exactly 1-WL vs
  2-WL. A follow-up can recompute `Φ` on the coherent (2-WL) closure if the 1-WL signal is ambiguous.
- **Greedy = upper bound on `b(X)`.** Greedy-best gives *a* fast sequence (hence an upper bound on the base and a
  witness that a geometric drop is *achievable*); it does not certify the minimum. For the monovariant question —
  "does a fast-drop sequence exist?" — an upper bound is exactly the right measurement.
- **Small `n`.** `n ≤ 41` here. The drop *factor* (not the absolute base) is the scale-free signal to watch;
  re-run at larger `n` for any candidate `Φ` before trusting a constant `ρ`.

**Next after the probe:** if a monovariant candidate survives, draft the potential-drop lemma (the A1/A3 thread)
and look for the counting argument that forces the factor on the non-carved residue. If only a carve survives,
record the rung and fall back to the conditional-predicate floor (cxt-scoping §5 route 3).

---

## 8. Findings (run 1, 2026-06-15 — `A2MonovariantProbe.Probe_CellSizeDropAcrossSRGs`)

Run green. Three confirmations, two falsified predictions, one decisive gap.

**Confirmed:**
- **The lens works on the carved side.** Rook `L(m)` has base **exactly `m = √n`** (`L(4)→4, L(5)→5, L(6)→6`)
  and its worst per-step drop factor **rises toward 1 with `n`** (`0.562 → 0.640 → 0.694`). That rising-toward-1
  trend is the large-base (√n) signature — so a *non-geometric* drop is visible and the carve does remove it.
- **Base is sub-spectral (the headline).** The cospectral `(16,6,2,2)` pair splits: `b(Shrikhande)=3`,
  `b(rook L(4))=4` on *identical* parameters and spectrum. So base is genuinely structural, below the spectrum.
- **Conference (Paley) is base-2 universally** (`q=13..37`, fastest drop ≈0.47, curve `n→(n−1)/2→1`). Not a
  base-size obstacle — confirming it is carved for the *abelian-consumption* mechanism, not for a large base.

**Falsified (corrections to record):**
- **Plain adjacency `2-rank` does NOT separate the `(16,6,2,2)` pair** — both are 6. The separating invariant for
  Shrikhande vs `L(4)` is finer (Smith normal form / 2-rank of `A+I`, per Brouwer–van Eijl), not the bare 2-rank
  this probe computes. Don't use bare p-rank as the carving invariant.
- **At fixed `n=16` the residue does NOT cleanly beat the carved families.** `b(Clebsch)=5 > b(rook L(4))=4`;
  residue worst-drop `0.667` ≈ lattice worst-drop `0.694`. The auto-verdict "candidate found" fired only on a lone
  Johnson stall (`T(8)`: curve `…→4→4→1`, factor 1.000) and is an **overcall** — there is no robust
  residue-vs-carved separation *at a single `n`*.

**The decisive gap:** the residue set is **entirely `n=16`** (Shrikhande, Clebsch, complement), so we have no
**scaling trend** for it. The real monovariant signal is *how the drop factor scales with `n`* — does the residue
stay bounded `< 1` while rook's `→ 1`? That cannot be read off one `n`. **Run 2 must add non-carved residue SRGs
at `n = 25, 36, 49`** — the natural choice is **Latin-square graphs from non-cyclic (non-isotopic) Latin squares**
(the residue analogue of "Shrikhande, not rook": same parameters as `L(m)`, different structure), reusing the
order-`m` Latin-square construction already in `CatalogueSchemeProbe`. Then plot worst-drop and base against `n`
for residue vs rook on the *same parameter series* — that comparison is what decides monovariant-vs-ladder.
