# Scoping the genuine core: a poly iso-invariant read that separates rigid coords, ties gauge

## The problem, precisely
Produce `read adj χ v : ℕ` that (①) transports under σ, (②-tie) gives automorphic vertices equal reads,
(②-sep) gives non-automorphic co-cellular vertices distinct reads — on the rigid **linear** residue
(CFI / multipede / Z_{2^k}), in polynomial time.

## Why the generic reads are all dead (probe-confirmed)
| read | verdict |
|---|---|
| single-bit `forcedVal` (`baseReadPin`) | **0/30 forced** on the homogeneous code — empty |
| WL / colour-keyed neighbourhood (`baseReadWL`), even iterated | **10–16 classes** — WL is provably blind to multipedes |
| RREF-column signature over a **full** column order | **discretizes (30/30)** but a poly *equivariant* full order is **2^β-impossible** (free gauge left-mult) |
| base-frame pin + RREF (pin all segment orientations) | **over-forces** — pins the gauge itself (gauge = orientation freedom) |

**Root cause (not circular — it's a theorem):** generic linear-code canonization (permutation/monomial code
equivalence) is **GI-hard** (Petrank–Roth 1997). So *no* generic linear-algebra/WL read canonizes the residue in
poly time — that would put GI ∈ P for all linear codes. The poly-ness of Algorithm R comes **only** from the
**bounded rank of the recovered base** (C# B1d: `|A|^{r+1}` affine frames, poly for bounded r), never from a clever
generic read.

## The viable plan — the R/K decomposition (probe-confirmed sound)
Split the residue by **automorphism**:
- **K = ⋃ nontrivial Aut-orbits** = the gauge coordinates (moved by some colour-aut) → **tie** (consume's job).
- **R = the Aut-fixed complement** = the rigid coordinates (moved by NO colour-aut) → **separate**.
This split is **iso-invariant** and R is rigid **by construction** (nothing in R is moved by an automorphism —
that is what puts it in R). ⚠ **The node is NOT fully rigid** — it keeps its full gauge K; only the sub-object R is
rigid. This is the escape from the whole-node-rigid trap (order only R; the gauge is *allowed*, it lives on K).

**⚠⚠ CORRECTION (automorphism-split, 2026-07-26): `support(ker H)` is only the LINEAR sub-handle of K.** `ker H`
is the **linear** kernel (the flip/diagonal gauge). A cell can also carry **scheme symmetry** — base collineations
that *permute* coordinates (monomial/permutation symmetry), which is **NOT** in `ker H`. If a colour-preserving
collineation swaps two *forced* coords, they are automorphic (an orbit) yet sit in `complement(support ker H)`, so
the ker-H split would wrongly mark them "rigid" and R would not be rigid there. So:
- **`support(ker H) ⊆ K`** (poly, iso-invariant, the linear component) — **force ties this for free** (9D
  `readAgg_eq_of_aut`);
- **`K ∖ support(ker H)` = scheme symmetry** — **consume** ties it (the `deepen`/`Tinhofer` contribution, §9.1);
- **R = what remains non-automorphic after both** — rigid by construction, canonized by the whole-R order.
So `support(ker H)` is the **poly linear handle** on K, not the whole split; the scheme part is consume's, via the
interleaving. "R rigid" is the **output** of the two-seal interleaving (consume ties ALL symmetry, force canonizes
the rigid remainder), never a precondition on the node. Equality `support(ker H) = K` holds **iff** the only
symmetry is the linear gauge (the fine-coloured multipede) — see the scheme-symmetric witness in the adjusted probe.
This is already how the landed machinery behaves: step-7 `ReadSeparatesRigid` is quantified over *non-automorphic*
pairs, and an **equivariant** read auto-ties every automorphic pair (linear OR scheme) — the reader always split by
automorphism, never by `ker H`.

Measured (linear-gauge witnesses): mixed multipede → R=12 rigid / K=18 gauge, and **the RREF-column read separates R
perfectly (12/12)**; rigid case R=30 (30/30); pure-gauge K=42 (all tied). ⚠ The *tie* over-splits/over-separates
under the **natural** (non-equivariant) RREF order — that is precisely the "you need the canonical R-order"
carried piece; an equivariant order auto-ties orbits.

Then the reader is:
1. **Canonize R** (rigid subspace) with the **whole-R-rigid** order — the landed 9A–9C machinery, *restricted to R*.
   R has trivial gauge (rigid), so `min`-over-frames is unique ⟹ an equivariant order on R exists.
2. **Tie K** — the proven 9D `readAgg` aggregate symmetry (`readAgg_eq_of_aut`) ties gauge coords by construction;
   equivalently, K is handed to consume via the interleaving (§9.1 Tinhofer coupling). Either way K ties *provably*.

This exactly matches the project's stated architecture (§9.1): **consume ties the gauge (K), the rigid solver
canonizes R** — the R/K split makes the handoff explicit and poly, and reduces the whole reader to **one** carried
obligation (below).

## The main blocking feature (honestly isolated) = the poly order on R = the recover core = the wall
The one thing the plan carries: **a poly iso-invariant canonical order on the rigid residue R.**
- The **exponential** version already exists and is correct: `min` over all `|R|!` column orders (9A–9C over
  `framesUniv`), ① unconditional.
- The **poly** version requires exploiting the **bounded-rank base** — recover the base (rank r), enumerate the
  `|base|^{r+1}` affine frames (poly for bounded r), solve each to an R-order, take the min. This is C# B1d, ported.
- This carries the **bounded-rank hypothesis** — which is *exactly the class boundary*: if the residue is
  bounded-rank-linear it canonizes in poly; if not, it is the **non-linear rigid residue = the honest flag** (the
  wall, claim #2/#3). So the blocker is **not new** — it is THE wall, and the plan correctly isolates it into this
  single predicate ("R is bounded-rank canonizable"), = `ForcingModel.bridge` / L4.

## Recommendation
Build the **R/K decomposition + the reduction** (buildable now, reuses landed 9A–9C order engine + 9D tie):
- `gaugeCoords adj χ = support(ker (recovered H))`, `rigidCoords = complement` — poly, iso-invariant.
- reader = `readAgg` over R-orders, tying K — ① unconditional (9D), ② `AggFaithful` restricted to R.
- Carry **one** predicate: `RigidResidueOrderable` (R admits a poly iso-invariant order via bounded-rank frames) =
  the recover core = the wall.
Result: the rigid-linear seal reduces to `{R/K split (built), tie-K (built, 9D), RigidResidueOrderable (the wall)}`
— the exponential `framesUniv` order is the correct-but-exp witness, and the poly order is the one carried wall,
precisely the bounded-rank class boundary the whole project isolates.
