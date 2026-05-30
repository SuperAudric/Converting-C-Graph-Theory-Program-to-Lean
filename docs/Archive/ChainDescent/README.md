# Archive — chain-descent closed sub-threads

Retired documents from the **chain-descent** line of investigation. Unlike
`../V4/` (a retired canonizer) and `../Exploration/` (a retired era), these are
*sub-threads of the still-active chain-descent design*: investigations that
reached a definite verdict, and build briefs whose implementation has shipped.
They are kept for the historical record and for the detail their parent docs
delegate to. Their conclusions are already distilled into the active docs (see
the "live home" column); nothing here is load-bearing for the current design.

## Closed investigations

| Doc | Verdict | Live home of the conclusion |
|---|---|---|
| `chain-descent-matroid.md` | **CLOSED 2026-05-23** — neither candidate closure of the propagation relation is a matroid (`cl` fails essentially every closure axiom; `cl_prov` is a topological closure but M3 is refuted by machine-checked `decide`). The matroid framing of T-C is a dead end. | One-line verdict + finding in [`chain-descent-calculator.md`](../../chain-descent-calculator.md) §7. Cited as *historical / non-binding* by linear-oracle §"output is a binary matroid" and cascade-oracle §"Tier-2 detector". The §2/§7/§8.4 shape is reused (not relied on) by [`chain-descent-tier3-decomposability.md`](../../chain-descent-tier3-decomposability.md). |
| `chain-descent-tier2-decomposition-experiment.md` | **CONCLUDED 2026-05-26** — single-instance probe of Luks/Babai structure-tree recursion on CFI(Petersen): the CFI ladder is **Tier-1, not Tier-2** (cascade depth ≈ tw(H)). Surfaced F7 (1-WL recovers Aut_v orbits at depth 1). | Subsumed by [`chain-descent-orbit-recovery.md`](../../chain-descent-orbit-recovery.md) (Theorem 1) and noted in [`chain-descent-calculator.md`](../../chain-descent-calculator.md) §7. |

## Completed build briefs

Temporary C#/Lean working notes, each explicitly "archive once the
implementation lands." All milestones complete; detail folded back into the
authoritative spec.

| Doc | Status | Authoritative spec |
|---|---|---|
| `chain-descent-cascade-oracle-build-brief.md` | **Done 2026-05-28** — M1–M5 complete (M3/M4 folded into M2); CFI(K7) branching 555→0, leaves 941→1. | [`chain-descent-cascade-oracle.md`](../../chain-descent-cascade-oracle.md) (§8.1 build status, §9 constraints, §10 risk 1). |
| `chain-descent-cascade-oracle-lean-brief.md` | **Done** — Lean contract Phases A/B/C built axiom-clean. | [`chain-descent-cascade-oracle.md`](../../chain-descent-cascade-oracle.md) §8.2 + `GraphCanonizationProofs/ChainDescent/CascadeOracle.lean`. |
| `chain-descent-linear-oracle-build-brief.md` | **Done 2026-05-28** — M1–M6 complete; twist construction validated on CFI(K4/K33/Petersen), leaf collapse measured through K7. | [`chain-descent-linear-oracle.md`](../../chain-descent-linear-oracle.md) (§8 status) + `GraphCanonizationProofs/ChainDescent/LinearOracle.lean`. |
