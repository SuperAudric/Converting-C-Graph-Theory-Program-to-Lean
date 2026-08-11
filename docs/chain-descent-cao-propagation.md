# CAO propagation — does refinement preserve `CellsAreOrbits` under individualization?

> ## ⛔⛔ 2026-08-11 — THE 2-WL LEG OF THE 2026-08-01 CLOSURE IS **RETRACTED**. Read §0.0a.
> The closure below rested on identifying this doc's target with *"a one-point extension of a schurian
> coherent configuration is schurian"*. **That identification is false in both directions** — weaker
> hypothesis (CAO ⊂ schurian) *and* weaker conclusion (fibres = orbits ⊂ all relations = orbitals) ⟹
> the two statements are **incomparable**, so the literature leg (M–P per-class, Wielandt, the
> Evdokimov–Ponomarenko schurity number) is evidence about a **different statement** and does not bear
> on the target. Named witness: **Shrikhande** — a non-schurian S-ring (genuine entry ticket) whose
> one-point extension has fibres `[1,3,6,6]` = exactly the `Aut_e`-orbits, i.e. **propagation holds on
> a paid ticket**. §0.0a carries the full correction.
>
> **What survives, unchanged:** the **four 1-WL refutations** (STATUS table); the **route** refutations
> §4.1 (coset transfer circular), §4.2 (no counting proof), §4.3 (bounded shattering depth, killed by
> `G ⊔ G`) — note these are statements about *proof routes*, not about the target; and every
> measurement in §5–§6 and §12.5b.
>
> **The honest status is the one the STATUS table always carried: at 2-WL, OPEN — no counterexample.**
> This doc contradicted itself: §4.5, §7.2, §8.4, §12.5b's E1-vs-E2 split and §14.5b all hold the
> CAO-vs-schurity distinction correctly; only this banner, §0.0a, wind-down §1's row and `MEMORY.md`
> conflated them.
>
> ▶ **Live again as of 2026-08-11 (user):** the thread's purpose is to provide **Lean footing for a CAO
> propagation argument**. Un-suspended for that purpose: §12.5a (mechanism), the `triCount` pin.
> §13 (the conversion gap) stays suspended — it is a cost question, not a footing question.
> ★ The landed Lean (`CaoFibring`, `CaoRound` — incl. the unconditional round-1/round-2 barriers) is
> axiom-clean and is now **load-bearing**, not merely an extraction candidate (wind-down W3).

### 0.0a ▶ LITERATURE VERIFICATION OF THE CLOSURE — ⛔⛔ **THE IDENTIFICATION IS WRONG** (corrected 2026-08-11)

The closure above was taken on an external check whose citations were never written down. They were
recorded here on 2026-08-04. **The object leg verifies. The identification built on it does not, and
it is the leg the whole closure rested on.**

**✅ The object is the literature's, exactly.** Muzychuk–Ponomarenko, *On quasi-thin association
schemes* ([arXiv:1010.4450](https://arxiv.org/abs/1010.4450)) §2.4 defines, verbatim: *"The coherent
configuration `Xα = (Ω, Sα)` is called the **α-extension** (or a **one point extension**) of the
coherent configuration `X`"* — `Sα` = the basic relations of the smallest CC on `Ω` with `1α ∈ Sα`
refining `S`, i.e. **the 2-WL closure with one point individualized**. Same paper, §2: *"given `α ∈ Ω`
we have `Aut(X)α = Aut(Xα)`."* Both quotes are accurate and both are useful: they name the object and
they let the stabilizer be computed on the extension.

> ## ⛔⛔ AND THE STEP AFTER THEM IS FALSE — *"the target **is** `Xα` is schurian"* (2026-08-11)
>
> The M–P quotes are about the **object** and about **automorphism groups**. Neither says anything
> about schurity. The inference from them to *"this doc's target is `Xα` is schurian"* fails on **both**
> quantifiers:
>
> | | this doc's target | *"extensions preserve schurity"* |
> |---|---|---|
> | **hypothesis** | `X` is **CAO** — the *fibres* are `Aut(X)`-orbits | `X` is **schurian** — *every* basic relation is an orbital |
> | **conclusion** | `Xα`'s **fibres** are `Aut(X)α`-orbits | `Xα` is **schurian** — every basic relation of `Xα` is an orbital |
>
> Schurian ⟹ CAO (the diagonal relations of a schurian CC are orbits), so the target has the
> **weaker hypothesis**; and fibres are only the diagonal part, so the target has the **weaker
> conclusion**. Weaker-in, weaker-out ⟹ **the two statements are incomparable.** Neither implies the
> other, and evidence about one is not evidence about the other.
>
> ### ★ THE NAMED WITNESS — Shrikhande, measured
>
> `Cay(Z₄², S)`: the S-ring `⟨S⟩` has **3** basic sets while `Aut_e` has **4** orbits `[1,3,6,6]` ⟹
> **non-schurian S-ring**, a genuine §7.2-shaped entry ticket. Its one-point extension `X_e` has
> fibres `[1,3,6,6]` = **exactly the `Aut_e`-orbits** ⟹ **propagation holds.** A non-schurian input on
> which the target is *true*. (Root vs extension: 3 vs 4 — see the §12.5b correction below.)
>
> ⟹ **The literature leg is retracted.** M–P's per-class positive results, the Wielandt non-schurian
> S-ring, and Evdokimov–Ponomarenko's schurity number `t(X)` are all evidence about *"extensions
> preserve schurity"*. That statement is genuinely false in general and genuinely only per-class — and
> **none of it bears on the target.** ⚠ The "unchecked step" recorded below is therefore doubly moot:
> even if Wielandt's base CC were verified schurian, it would refute the wrong statement.
>
> ### ▶ THIS DOC ALREADY HELD THE DISTINCTION EVERYWHERE ELSE — it is an internal inconsistency
>
> §4.5 (*"the fibre hypothesis is doing real work, and any route that would also prove the unrestricted
> version is doomed"*) · §7.2 (states the ticket as an **extension** condition, correctly) · §8.4
> (*"the S-ring is the **ROOT** closure only"*) · §12.5b (measures **E1** fibre-schurity and **E2** full
> schurity **separately**, 0 vs 477) · §14.5b (*"CAO gives cells = orbits; it does **NOT** give pair
> classes = orbitals"*) · the STATUS table (*2-WL: OPEN*). Only the banner, this block, wind-down §1's
> row and `MEMORY.md` conflated the two.

**✅ The literature only ever proves it per-class.** Schurity of one-point extensions appears as a
*sufficient condition* on a restricted class, never as a general theorem: M–P Thm 6.5 (quasi-thin with
≥ 2 orthogonals, *given* that every algebraic isomorphism has a one-point extension) + Thm 8.1
(non-Kleinian, degree ≥ 9) — and the same paper constructs **infinitely many non-schurian** Kleinian
quasi-thin schemes. Evdokimov–Ponomarenko's *schurity number* `t(X)`
([EJC 7 (2000) R31](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v7i1r31)) exists
precisely to measure how many extensions schurity costs — machinery that would be vacuous if extension
preserved it. So §4.3's own "per-family only" conclusion is the literature's position too.

**⚠ The "known false in general" leg is NOT a located citation** — and after the correction above it is
also **aimed at the wrong statement**. Kept as provenance. No paper was found stating *"the
one-point extension of a schurian coherent configuration need not be schurian"* in those words. What
supports it:

* the closest published instance of the right shape — **Wielandt's non-schurian Schur ring** over the
  elementary abelian group of order `p²`, `p > 3` (recorded in
  [arXiv:2109.01385](https://arxiv.org/abs/2109.01385), *On a huge family of non-schurian Schur rings*);
* ⛔ ~~this project's own identification, `remaining-work.md` §1T: *"S-ring non-schurian **is** 'the
  one-point extension at `e` is non-schurian'"*~~ — **RETRACTED 2026-08-11.** The S-ring is the **root**
  closure (§8.4); the extension's fibres are strictly finer (Shrikhande 3 vs 4). ⚠ The same wrong
  identification appears in `remaining-work.md` §1T and §12.5b — both are corrected in place;
* this project's own measurement, §12.5b: **477 nodes where fibre-schurity holds but full schurity
  fails** ⟹ unrestricted "extensions preserve schurity" cannot prove the target. ★ **This bullet is
  the one that survives, and it is now read the other way**: it is the project's own evidence that the
  two statements are **incomparable**, i.e. against the identification, not for it.

⚠⚠ **The unchecked step.** Wielandt's example refutes the target *only if* the base CC in the S-ring
correspondence is itself **schurian** — otherwise it is a non-schurian object with a non-schurian
extension, which proves nothing about propagation. Nobody has checked that. Until someone does, the
honest statement of the closure is **"no route to a general theorem — the literature proves it only
per-class, and the project's own measurement shows the unrestricted form fails"**, *not* "known false".
The distinction does not reopen the track (per-class is what §4.3 already concluded), but it must not
be quoted as a refutation in the W4 write-up.

> ⚠ **NOT the same doc as [`chain-descent-cellsareorbits-route.md`](./chain-descent-cellsareorbits-route.md).**
> That one is the *demoted* forms-graph bounded-WL-dimension route. **This** doc owns the question
> *"start from the orbit partition, individualize one vertex, refine — are the cells still orbits?"*,
> which is the domain hypothesis behind `Tinhofer` / `DeepenTinhofer.lean`.

---

## STATUS (read first)

| level | verdict | witness |
|---|---|---|
| **1-WL** | ⛔ **REFUTED** | `net(Z₄) ≅ CFI[K4]-tw` (n=28); also Shrikhande (n=16, VT), Chang-2 (n=28), `Cay(Z₁₂⋊₅Z₂)` (n=24, VT) |
| **2-WL** | **OPEN — no counterexample; evidence upgraded 2026-07-30/31 (see §6)** | — |
| `VT ⟹ Tinhofer` | ⛔ **REFUTED at 1-WL** by the parallel branch — see [`../scratchpad/HANDOFF_2wl.md`](../scratchpad/HANDOFF_2wl.md) §5 | `Cay(Z₁₂⋊₅Z₂)` |
| `CAO ⟹ Tinhofer` | ⛔ **REFUTED at 1-WL** | `net(Z₄)` |
| **separation before round 3** | ⛔ **IMPOSSIBLE — PROVED** (`CaoRound.round1_barrier` + `round2_barrier_real`, unconditional, CC axioms only) | — |
| **route (A), resolver-level** ("try cells, keep one the supply certifies") | ⛔ **MEASURED DEAD 2026-07-31** — 0 of 58 reached nodes helped (§10.5) | `probe_route_a.py` / `.out` |

**⚠⚠ READ §0.0 BEFORE ANYTHING ELSE.** This doc is a probe into a **design change** — swapping the
refiner 1-WL → 2-WL — **not** a lemma for the `Tinhofer` in `build.sh`, which is a **1-WL** predicate.
Two readers have already reconstructed the wrong target.

**The live target is §2's sharpened statement**, now sharpened again by the barriers to the **triple
count** `N(a,b;i,j,k)` (§12.5a). It is union-stable, strictly weaker than "schurity of point
extensions", and it isolates the one thing that actually has to happen (§3's coupling principle).

**Why the project cares.** Per [`00-START-HERE.md`](./00-START-HERE.md) §2, *"the SOLE remaining `①c`
condition, `Tinhofer`, IS `CellsAreOrbits`"*, and `deepenSupply` stays out of `Publication.canonForm?`
until that totality is **populated per family (T1)**. This doc is the T1 obligation's evidence base.
Two fragments are **already landed** — do not re-prove them:
`CascadeOracle.cellsAreOrbits_of_discrete` (:292, the discrete end) and
`cellsAreOrbits_of_compl_card_le_two`.

**Everything here was measured with the clean-room machinery in §8, never with
`probe_orbit_oracle` — which is PROVEN BROKEN (§8.2).**

---

## 0. ▶ HANDOFF — start here

**Where the work stands, in a few sentences.** At **1-WL the question is settled: refuted**, four
independent witnesses (§ STATUS). At **2-WL it is open**, no counterexample, and §3 explains *why* the
search keeps failing. **Two Lean modules are landed and gated** — `CaoFibring.lean` (the reduction to
orbital separation) and `CaoRound.lean` (that reduction applied to the **real** closure, plus the
round-1 and round-2 barriers). What remains is **one hypothesis**, and the barriers have sharpened it
to a single named quantity.
⛔ **And the cheap competitor is closed:** §10.5's route (A), in its resolver-level form, is
**measured dead** (2026-07-31, `probe_route_a.py` — 0 of 58 reached nodes). That does *not* promote
this track (§0.0: it is a **probe, not a program**, and the other resolutions are unranked); it only
removes the one alternative that would have been cheap.

**The remaining obligation has a name — use the `CaoRound` form.** The statement that applies to the
object the algorithm actually builds is

```
CaoRound.step2_closure :   hsep → (closure v u = closure v w  ↔  SameStabOrbit adj χ v u w)
    hsep : ∀ u w, f v u = f v w → SameStabOrbit adj χ v u w
```

⚠ **Do not use `CaoFibring.levelSet_iff_stabOrbit_of_separates` for applications** — it requires
`PairInvariant` (invariance under *all* of `IsColAut adj χ`), which the **individualized** closure does
not have; it has only `PairInvariantAt` (the `v`-stabilizer). `CaoRound` fixes exactly that.
**Do not attack the target in its graph form** — the graph content is gone after §1's reduction.

**What the barriers bought (2026-07-31, unconditional, CC axioms only).** Rounds 1 **and** 2 are
provably blind on `v`'s row, so separation cannot occur before **round 3** — which is what M3 measured
11/11. Round 2 gives far pairs the **triple count** `N(a,b;i,j,k) = #{x : X(a,x)=i, X(v,x)=j,
X(x,b)=k}`, the first quantity **coherence does not determine**. ⟹ the crux is now a statement about
*that* object (§12.5a), not about the closure in the abstract.

> ### ★★★ THE ONE THING TO KNOW — the crux has a SUFFICIENT PIN: one inequality
> **`CaoRound.round3_separates_iff_triCount_ne`** (§6, axiom-clean): round-3 row colours differ **iff**
> some triangle type of the round-2 colouring has a different `triCount` at `(v,u)` vs `(v,w)`.
> ⟹ **pin the per-family R2/R3 certificate to `triCount`**, and read §12.5a for how to attack it.
>
> ⚠⚠ **READ THE DIRECTION — corrected 2026-07-31. This is a SUFFICIENT condition, NOT a reduction of
> the crux.** Refinement is monotone, so *`triCount` differs at round 3* ⟹ round 3 separates ⟹ the
> closure separates ⟹ the crux holds on that pair. **The converse FAILS:** if `triCount` agrees at
> round 3 the row can still separate at round 4+, because the round-3 colours of **far** pairs go on
> refining. So *"∀ such `u,w`, some `triCount` differs"* is **strictly stronger than the crux** — the
> same fact §12.6's "Must it occur AT round 3?" box states in prose. An earlier version of this box
> read *"rounds, the row and the closure are all discharged"*; that is an **OVERCLAIM, do not inherit
> it.** What is discharged is everything **up to** round 3. In particular a measured `triCount`
> agreement would **not** be a counterexample to CAO propagation.
> ★ Why it is still the right object: it fires at **11/11** fused classes on record, it is finite,
> explicit and `K_v`-invariant, and proving it proves the crux. Treat it as the **pin**, not the crux.
> ⚠ It carries one hypothesis, `Function.Injective enc` (a faithful re-encoding). ⚠⚠ **NOT satisfied
> by the rank renumbering** — an earlier version of this doc claimed it was. A renumbering has bounded
> range on an unbounded domain, so it is not globally injective; it is injective only on the values
> that **occur**. The hypothesis is satisfiable in the abstract (take a pairing encode, which computes
> the same partition), but any instantiation at the real refiner must weaken it to `Set.InjOn` over
> the occurring pairs, or carry an enc-independence lemma. **Repair = §12.5a R1g.**
> ⛔ **Do not try to strengthen the barrier to "separation MUST occur at round 3"** — **§12.6's
> "Must it occur AT round 3?" box** explains why the method cannot yield it (barriers give
> *equalities*; separation needs an *inequality*).

**Read in this order.** **§0.0 (why this question exists, and why it is a PROBE — non-optional)** →
§ STATUS → **§13 (the conversion gap — what this track would cost to cash)** → §1 (the reduction) →
§2 (the target) → §3 (the mechanism; the conceptual core) → **§14 (that mechanism exhibited on the
smallest witness, plus the arity ladder and the falsifier filter it yields)** →
**§12.5a (the crux work plan)** →
§12.3/§12.6 (the barriers and what M3 measured). Then §4/§5 before proposing anything, and §7 before
investing in anything.

> ### ▶▶▶ WHERE THE LAST SESSION STOPPED (2026-07-31) — pick up here
> Four things landed, in this order, and each has its own section:
> 1. **Two statement-level defects fixed** — the `triCount` pin is **sufficient, not equivalent**
>    (§0's box), and `Injective enc` is **not** the rank renumbering (§12.5a **R1g**).
> 2. **Route (A)'s cheap form measured DEAD** (§10.5) — and its two failing nodes turned out to be
>    **all-mixed = force's domain**, so the harvest was right to fail (§13.6b).
> 3. **The conversion gap scoped, then INVERTED by measurement** (§13, then **§13.6**): swapping
>    `Deepen.step` alone buys nothing; the **descent's refiner** is what recovers the orbit partition
>    exactly. §5's "CFI over any base" row is **narrowed** (a random cubic base breaks it at 1-WL),
>    and the matching 2-WL result is **worthless** — §7.2's ticket is unpaid there.
> 4. **R1c RAN — §12.5b.** The E1/E2 descent instrument now covers the sharp Cayley population
>    (`probe_r1c.py`, replacing a ≤ ~24-input cap): **465 of the recorded 729 sharp inputs, 462
>    instrumented, 56,811 descent nodes to depth 8.**
>    **★ E2 ANSWERED — 477 nodes where fibre-schurity holds but FULL schurity fails ⟹ the fibre
>    hypothesis is LOAD-BEARING**, so unrestricted "extensions preserve schurity" cannot prove the
>    target (this *measures* §4.5). **★ E1: 0 failures — no 2-WL CAO counterexample**, at every node
>    of a descent rather than depth 1 only. ⚠ **64% coverage, not a population result** — see §12.5b's
>    four named gaps.
>
> **▶ The single next action: close R1c's coverage gaps — §12.5b's "To close R1c properly".** It is
> the only step that can end the track, and it is now bounded work, not open research.

> ### ▶▶ ADDED 2026-08-01 — §14, the anatomy and the ARITY LADDER
> Prompted by a reader question about *why* 1-WL fails; it produced three things worth having.
> 1. **§14.1 — the failure, dissected.** The far cell's split is the **pullback of the exposed local
>    shape's PAIR-orbits**; Shrikhande vs rook 4×4 (same `SRG(16,6,2,2)`, one fails, one propagates)
>    isolates the 1-WL blind spot to one sentence: *a 2-regular graph on 6 vertices is a hexagon or two
>    triangles, and counting neighbours cannot tell which.*
> 2. **§14.2 — a plausible proof route killed cheaply.** *"Mixed cells must chain back to `v`, which is
>    a pure singleton"*: the **premise is measured TRUE** (14/14 mixed cells have mixed support) and the
>    **inference is unsound** — the support is **circular** (self-adjacent in Shrikhande; a closed
>    2-cycle in bipartite `net(Z₄)`), so no chain reaches `v`. **Do not re-derive this.**
> 3. **§14.4 — a NEW FALSIFIER FILTER for §10 item 3**, orthogonal to R1c's coverage work and cheap:
>    hunt for a VT graph whose **point stabilizer acts 2-transitively but not symmetrically on a cell**
>    (= a **not-2-closed** local group). Also records the obstruction that makes rung 2 hard — a
>    2-transitive group's 2-closure is `Sym`, so **no binary structure on a cell can expose one**
>    (brute-forced: 0 of all 32,768 graphs on 6 vertices).

> ### ▶▶ ADDED 2026-08-05 — §14.5, the PATH-CONDENSATION lead: **RAISED AND CLOSED THE SAME DAY**
> A route proposed from outside the doc: compare vertices by the **multiset of paths between them**,
> which under a CAO residue should collapse to a cheap object. Three things came out of measuring it.
> 1. **§14.5a — the project's own path canonizer IS 2-WL.** `Archive/V4/CanonGraphOrdererV4.cs`'s
>    recursion equals the 2-WL pair closure **as a partition, 7/7 objects**. ⟹ *"V4 fell to CFI
>    because it condensed partway"* is **retired**: it condenses exactly onto 2-WL, and 2-WL fails
>    on CFI.
> 2. **§14.5c — the UNCONDENSED path objects and 2-WL are incomparable *at bounded length*.**
>    Shrikhande: `A1` reaches the orbitals (4) where 2-WL cannot (3), by **repeat-tracking alone**.
>    CFI[K4] plain at length 12: 2-WL is exact (10) where `A2` is not (9) — but that direction is
>    **truncation**, not a deficiency of the object; at full length `A2` is an orbit oracle.
>    ⚠ **This does NOT contradict §14.5a.** V4 **condenses at every step** and lands exactly on 2-WL;
>    `A1`/`A2` **never condense**. They are different objects, and the variable between them is how
>    many steps of vertex identity are retained — which §14.5e turns into the whole story.
> 3. **§14.5b — FROM vs BETWEEN**, the distinction any condensation argument turns on: *paths from a
>    vertex agree across a cell* is true but is CAO restated; *paths between a pair are determined by
>    `[cell, conn, cell]`* is **false at a CAO root**, with a named witness in Shrikhande.
>
> ★ §14.5d(i): the lead's "path type" **is** the orbital, so its own question is §12.3's crux reached
> independently — and §14.4's rung-2 obstruction is now a **one-line proof at every degree**, not a
> degree-6 brute force.
>
> ⛔⛔ **§14.5e — THE ROUTE IS CLOSED (2026-08-05, same day).** Two independent measured reasons, each
> sufficient alone. **(1)** All of the path object's strength over 2-WL is repeat-tracking; the rung
> 2-WL can afford (**window 2**, pair state) buys **exactly zero on all four objects**, and the first
> paying rung is **window 3 = triple state**, which 2-WL provably cannot compute. **(2)** The proposed
> repair — *"under CAO the loop is detected even if the loop-start vertex is forgotten"* — has a
> **true premise and a false conclusion**, with a minimal witness at Shrikhande: **length 7, window 3,
> 3880 vs 3882**. ⟹ **path length is NOT the resource that tracks WL dimension — window is.**

**First actions — ▶▶ §13 (THE CONVERSION GAP) FIRST, then §12.5a.** Revised 2026-07-31: **nothing in
this track can reach the built object until the `Deepen.step` swap is scoped and decided** (§13), so
that scoping gates the value of every crux row. Only then §12.5a: **R1a** coordinate-level ablation of
`N` (the class-level one came back *over-determined* — §12.6); **R1b** base-point uniformity (∀`v` or
∃`v`?); **R1c** the falsifier = §12.6's M1 — a Cayley root over a **transitive** group satisfies CAO
*automatically*, so the 729 non-schurian S-rings **are** the sharp inputs ⚠ *and the probe silently
caps at ~24, not 729* ⚠⚠ *this is a POPULATION FIX to an existing instrument, **not** a new falsifier
hunt — an extensive hunt already ran before the track was formalized (§6), which is why no further
sweep is queued*; **R1d** the literature check; **R1e** ✅ *landed* (`CaoRound.lean` §6 — the
`triCount` pin, ⚠ *sufficient, not equivalent* — see the box above); **R1f** the aggregate/rank
attempt; **R1g** the `enc`-hypothesis repair.
⚠ **R1c can end the track** — if 2-WL falls, §10.5's selector route (A) becomes the only path.
⚠ **§12.6's M2 is ANSWERED** (see §12.3's convention box) and **M3 is DONE** (§12.6); M4–M6 stand.

**Before proposing any new route or invariant, apply §7 in order.** Two proof routes and two
falsifier habitats died to those filters in one session each; they are cheap and they are decisive.

### 0.0 ▶▶ WHY THIS QUESTION IS WORTH ITS COST — the unrecorded reason (added 2026-07-30)

⚠ **This was understood but never written down, and a fresh reader reconstructs the wrong target
without it.** Two readings have now been made and corrected: (a) that this doc serves the *existing*
`Tinhofer` predicate, and (b) that a 2-WL result would feed the **force** resolver. Both are wrong.

**The Lean `Tinhofer` is a 1-WL predicate.** `Deepen.step = Refine.warmRefineVec ∘ Descend.indivOne`,
and `warmRefineVec` iterates `sigKey`, whose `signature` is the multiset of `(χ u, adj v u, P v u)`
over `u ≠ v` — plain colour refinement. `CellSingleOrbit` is stated at `IsColAut adj χc` for that
1-WL `χc`. **So proving §2 (a 2-WL statement) does not discharge `Tinhofer` as it stands**, and it is
not meant to: 2-WL cells refine 1-WL cells, and a 1-WL cell is a *union* of 2-WL cells, so nothing
transfers. Measured on the flagship witness (`net(Z₄)`, n = 28, from the exact orbit partition,
either root-orbit rep): 1-WL → 5 cells, **2 mixed**; 2-WL → 7 cells, **0 mixed**.

**This doc is a probe into a DESIGN CHANGE, not a lemma for the current object.** The question is:
*if the refiner were swapped 1-WL → 2-WL — a direct polynomial cost increase, `n²` → `n³` per round —
does the architecture gain a theorem it provably cannot have at 1-WL?* The chain that would cash it:

> **CAO all the way down ⟹ Layer 1 (`Tinhofer ⟹ R1`) ⟹ the deepen supply is COMPLETE ⟹ consume
> resolves every node.** Force is not fed by this; it is made *unnecessary* on the consume domain.

**Why nothing weaker will do — the obstruction is not about mixed cells.** The recorded refutation
(`scratchpad/DUAL_resolver_scoping.md` §1.2; CFI over a random cubic base, m = 8, n = 56, the
`|C| = 16` node) has the *opposite* shape from what one expects: the cell **is one true orbit**
(explicit σ, `is_aut ✓`, colour-preserving ✓, σ(24) = 26 crossing the harvest's 8+8 split), so consume
fails from **supply incompleteness**, and at a single-orbit cell `Force.forceBy_no_narrowing_on_orbit`
**forbids** force from acting. ⟹ *no theorem of the shape "consume fails at `χ` ⟹ force can act at
`χ`" can hold.* Force is structurally barred from precisely the failure mode that occurs.
`Tinhofer ⟹ R1` closes that mode at its source — with single-orbit cells at every level the
re-relating induction makes the harvest complete, so supply incompleteness cannot arise. **All the
load therefore sits on "every level's cell is a single orbit" = CAO propagation.**

⚠⚠ **"The 1-WL design is provably dead" IS TOO STRONG — walked back 2026-07-30 (user), after
independent verification between iterations.** On the existing VT-non-`Tinhofer`-at-1-WL witnesses
**consume _can_ fire, and measurably does**: the index-min vertex selection usually happens to choose
vertices in the same orbit (this is the same selector luck as §7.5's Shrikhande, and it is why the
force-key tally in limit 2 below finds zero blind cells). What is missing is a **guarantee** — nothing
says the selector is lucky on an antagonistic input, and in particular nothing covers the **root**.
⟹ the honest verdict is **"no completeness theorem at 1-WL", not "dead"**, and there are **two**
routes to one, not one:
- **(A) the SELECTOR route** — see §10.5. Prove index-min (or a better canonical selector) always
  lands on a resolvable cell. ⛔ **Its cheap, resolver-level form is MEASURED DEAD (2026-07-31,
  `probe_route_a.py`): on 58 nodes across three witnesses there is not one node where the selected
  cell fails and another cell certifies** — at the two failing nodes (the m=8 root, and an 8-cell
  node sharing the `|C|=16` shape) *every* cell fails together, and **measurably because no cell at
  either node is a single orbit at all** (`|Aut_χ| = 512` / `64`, every cell mixed — §13.6b). The
  harvest's `✗` is therefore *correct*: these are **force-domain** nodes, and there was nothing for
  any selector to find. ⟹ route (A)'s cheap form is dead for a sharper reason than "supply
  incompleteness" — that phrasing was my first write-up and is **retracted**.
- **(B) the MECHANISM route** — the 2-WL swap, this doc's subject. Plan = §12.6 (M1–M6).

**⚠ TWO SCOPE LIMITS on "revived at 2-WL" — do not overclaim.**
1. **Propagation is the induction STEP; the base case is separate.** A descent starts at the uniform
   colouring, so "root CAO" is *"k-WL computes the orbit partition of the input"* — false at every
   fixed `k` for rigid multipedes. The revival is on the **consume domain** (inputs whose k-WL root
   partition already is the orbit partition); rigid and mixed roots stay Track R's. It makes consume's
   ownership of its domain *complete*, not the whole design safe.
2. **The known 1-WL witnesses do NOT exhibit a concrete stall.** Measured 2026-07-30
   (`probe_stall.py`/`probe_stall3.py`/`probe_stall4.py`): across **all four** recorded witnesses —
   `net(Z₄)`, Shrikhande, Chang-2 and the named VT witness `Cay(Z₁₂⋊₅Z₂)` — **13 manufactured mixed
   cells, and the force key separates the true `Aut_v`-orbits at every one of them**: lookahead depth 1
   (which *is* `lookaheadKey`'s non-discrete branch) on 10, depth 2 on 3 (one size-3 `net(Z₄)` cell and
   the two size-2 cells of the VT witness). **Zero blind cells.** 2-WL splits all 13 at depth 0.
   ⟹ **the death is the missing theorem, not a failing run.** Do not cite these graphs as "the design
   dies here" exhibits. ⚠ This does *not* rescue 1-WL: bounded lookahead depth is not a theorem either,
   and "some bounded depth always suffices" is the WL-dimension question in another costume.

**⚠⚠ THIS IS A PROBE, NOT A PROGRAM — and that is deliberate (user steer, 2026-07-31).** The track
earns promotion to *"the pursued route"* **only by being shown viable**. Until then it is one
candidate resolution of a theoretical CAO-unconsumable residue among several, and the others are not
ranked below it:
- **prove the residue cannot exist**, by a route that never needs CAO propagation;
- **run force at every step of the descent** — straightforward, expensive, and *not yet costed*
  (⚠ note it is not free of the m=8 shape either: `forceBy_no_narrowing_on_orbit` still forbids force
  on a single-orbit cell, so "force everywhere" buys *relocation depth*, not the cell itself — costing
  it is the open question, not whether it fires);
- **a method not yet thought of.**

⚠⚠ **BUT "probe" DOES NOT MEAN "budget-capped" — an earlier version of this block said *"do not spend
past the cheap decisive steps"* and the user RETRACTED it (2026-07-31).** The standing position:
**a clear answer that takes a while beats giving up on a viable route and stalling the project.**
So "probe" governs *what may be claimed* — the track is not the pursued route until viability is
shown, and the competitors above stay unranked — **not how much may be spent** deciding it. Run the
work that produces a verdict, cheap or not. ⚠ Still true, and the only pacing note that survives:
**the falsifier hunt is not the lever** (an extensive one preceded formalization); R1c is a
*population fix* to an existing instrument.

**▶ And the stakes of the negative branch.** If CAO propagation fails at *every* `k`, the design
cannot be made viable by refiner strength and needs deeper structural change. The reason to expect
otherwise is §5's **self-limiting** lesson, which has never been connected to this question: the CAO
hypothesis *excludes* the standard "no bounded `k` works" constructions — rigid ⟹ discrete orbit
partition ⟹ vacuous kills the multipede/Lichter family, and CFI is excluded separately (it is about
distinguishing two graphs, not orbit recovery within one; its large gauge group keeps orbits coarse
enough that even 1-WL matches). A "fails at every `k`" witness would have to be simultaneously
non-rigid, orbit-coarse, and closure-deficient **at the same cell pair** — §3's coupling requirement,
which no falsifier has ever met. **That branch currently has no candidate witness at all.**

### 0.1 How to reproduce anything here

*Probes* — pure Python 3 stdlib, **no dependencies** (no networkx/sympy/nauty; none are installed).
Every probe that another probe **imports** is `__main__`-guarded, so importing it does not run its
sweep (verified — the import graph was checked and the two stragglers fixed). Leaf drivers are not
guarded; they are meant to be run directly. ⚠ If you add a probe that imports another, re-check
(§9: this trap fired three times in one session):

```bash
cd /workspace/scratchpad && python3 -u probe_cao_cleanroom.py     # the core witnesses
python3 -u probe_cao_provenance.py                                # 11 known |Aut| values + the broken-oracle proof
```

Long sweeps write logs; **do not pipe them through `tail`** (§9). Run them detached and read the log.

*Lean* — the gate is the **absolute** path (it self-`cd`s via `$0`; a relative path fails):

```bash
bash /workspace/scripts/build.sh          # full serial gate, ~235 s, 109 modules (measured 2026-07-31)
cd /workspace/GraphCanonizationProofs && lake build ChainDescent.CaoFibring   # this module alone
lake env lean /workspace/scratchpad/CaoFibringAxioms.lean                     # #print axioms, all 18 decls
```

⚠ bare `lake build` builds a **partial** 14-module subset and omits this cluster — always use
`build.sh`. Lean probe files live **outside** the package root so they cannot enter any build.

---

## 1. The question, stated three ways

**Graph form.** Let `χ` be the exact `Aut(G)`-orbit partition (so `CellsAreOrbits` holds by
construction, *however obtained* — the hypothesis does not require refinement to have found it).
Individualize `v`, take the `k`-WL closure. Is every cell still a single `Aut(G, v)`-orbit?

**CC form (the useful one).** Under CAO the start cells *are* `Aut`-orbits, so for cells `D ∋ v` and
`C`, transitivity on `D` puts the `Aut_v`-orbits on `C` in bijection with the **`Aut`-orbitals inside
`D × C`**. Hence

> **`k`-WL preserves `CellsAreOrbits` ⟺ the one-point extension separates the orbitals between
> fibres ⟺ the class of *fibre-schurian* coherent configurations is closed under one-point extension.**

No graph, CFI or gauge content survives the reduction. **Do the reduction before attempting anything** —
it is what makes §3 and §4 visible.

**⚠ Do not conflate these.**

```
CAO propagation (∀ inputs)   ⟹   CAO at every node of a descent from a CAO root   ⊋   Tinhofer
```
The first two are equivalent along a descent from a CAO root (propagation applied inductively); the
universal form is stronger only in that it quantifies over all inputs. **The strict gap is the last
one:** `Tinhofer` (`DeepenTinhofer.lean`) inspects **only the `chooseIdK`-selected** cell at each
level, so CAO may break at a node — even on a cell the descent will later visit — and the graph can
still be `Tinhofer` (Shrikhande does exactly this, §7.5). **Proving CAO propagation is proving
strictly more than the chain needs**; check whether the weaker statement suffices before starting.

⚠⚠ **The ladder above holds at a FIXED WL level and does NOT cross levels.** The built `Tinhofer` is
**1-WL** (`step = warmRefineVec ∘ indivOne`); this doc's target (§2) is **2-WL**. Since 1-WL cells are
unions of 2-WL cells, the 2-WL statement implies nothing about the 1-WL one — measured, `net(Z₄)`:
2-WL 0 mixed cells, 1-WL 2 mixed. **A proof of §2 is a result about a 2-WL-refined descent, i.e. about
a proposed design change, not about the object in `build.sh`.** See §0.0 for why that change is the
point rather than a defect.

---

## 2. ▶▶ THE LIVE TARGET

> **If individualizing `v ∈ D` splits `C` (i.e. `Aut_v` is intransitive on `C`), then the 2-WL
> extension separates the `D–C` orbitals.**

Why this phrasing and not another:
- **union-stable by construction** (stated per cell pair) — it survives the stress test in §7.1 that
  killed two earlier formulations;
- **strictly weaker** than "schurity of point extensions" — it only asks about orbitals the group
  actually splits;
- it states the coupling requirement (§3) explicitly, which is what every falsifier attempt missed.

**Counterexample design implied by it:** find `D, C` with `Aut` transitive on both, `Aut_v`
**intransitive** on `C`, and two `D–C` orbitals still algebraically fused **in the extension**.

**▶ The proof plan for this statement is §12.** Steps 1–2 there are free and already discharge
~99% of instances; the crux is isolated in §12.3.

---

## 3. ★ THE MECHANISM, AND THE COUPLING PRINCIPLE

**Exactly what individualization does to other orbits.** Individualizing `v ∈ D` changes cell `C`'s
orbits **only** by fibring `C` over the `Aut`-orbitals inside `D × C`: orbital `O` contributes
`{u ∈ C : (v,u) ∈ O}`, of size `|O|/|D|`. **Nothing else can happen.** Therefore

- if `Aut_v` is still transitive on `C`, nothing changes there and CAO is **trivially safe**;
- `k`-WL detects the change iff its closure **separates** those orbitals; the blind spot is a
  **fusion** of ≥ 2 orbitals into one class.

> ### ⟹ A CAO failure needs the GROUP-CHANGE and the CLOSURE-DEFICIENCY at the **same** cell pair `D × C`.

This one principle explains every negative result on record (all measured, `probe_cao_mechanism2.py`):

| construction | group-change | deficiency | outcome |
|---|---|---|---|
| `G ⊔ G` | copy A | copy B | **all 144 fused pairs are BB**; copy B's `Aut_v`-orbits are `[16]` = one orbit ⟹ safe |
| non-rigid multipede | everywhere (\|Aut\|=2) | none — the CAO start hands WL the labelling | 1-WL discretizes |
| CFI over big bases | none (`Aut_v` stays transitive) | gauge parity | propagates even at 1-WL |
| **`net(Z₄)` at 1-WL** | **same place** | **same place** | **the one that works** |

**Fusion structure at deficient roots** (merged orbitals, valencies from one point): Shrikhande `[3,6]`;
`net(Z₄)` four classes `[3,6] [3,6] [4,8] [1,2]` (ratio 1:2 = the `Z₄` order-2-vs-order-4 signature);
Chang-2 two classes `[4,4]`. ⟹ **fusions occur at both equal and unequal valency, so no valency
argument can shortcut this.**

**▶ §14.1 exhibits this principle constructively on the smallest witness** — the far cell's split is
the *pullback of the exposed local shape's pair-orbits*, and Shrikhande vs rook 4×4 (identical
`SRG(16,6,2,2)` parameters, opposite verdicts) shows the coupling as a single fact. Read it with §3.

**Why 2-WL is different in kind from 1-WL (not merely stronger).** The gap to close is the orbital
structure on `D × C` — a *pair-level* object. 1-WL is a vertex-level tool aimed at a pair-level gap: a
**type mismatch**, which is why 1-WL counterexamples are easy. 2-WL computes the coarsest invariant
approximation *of that very object*. This is a reason, not a guarantee.

---

## 4. ⛔ DEAD PROOF ROUTES — with the reason each died

**4.1 Coset transfer — CIRCULAR.** `u,w` in one extension cell ⟹ CAO gives `τ ∈ Aut` with `τu = w`;
you need `σ ∈ Aut_v`. That holds iff `τ⁻¹(v) ∈ Aut_u·v` — and the `Aut_u`-orbits on `D` are the
orbitals in `C × D`, **the transpose of what is being proved**. This is the recorded 1-WL sketch's
defect one dimension up. ⟹ **CAO alone can never close the gap.**

**4.2 No purely counting/local proof can exist.** `k`-WL computes only structure constants;
"an automorphism exists" is not a counting statement. A proof needs a Schur–Wielandt-style
classification of the algebraic automorphisms, or a genuine restriction of the class.

**4.3 The bounded-shattering-depth route — killed by `G ⊔ G`.** `Discrete ⟹ CAO` is free and already
proved (`CascadeOracle.cellsAreOrbits_of_discrete`), so a bound "the descent discretizes within `d`
individualizations" would give CAO propagation with no schurity theorem. But **depth is linear in the
number of components**: Shrikhande ×1/×2/×3 → **3/6/9**, while VT and CAO hold throughout. The target
property is union-closed; a depth bound is not. ⟹ **usable only as a per-family statement (§10.4).**

**4.4 "Full schurity" as the induction invariant — killed by the same construction.** Measured law
*"non-schurity occurs only at depth 0 and the first individualization destroys it"* is **FALSE**:
Shrikhande ⊔ Shrikhande has root CAO ✓ and depth-1 CAO ✓ but full schurity fails at **both** — one
individualization lands in one copy and the other still carries the whole deficient scheme.

**4.5 Proving the stronger "schurian CCs are closed under point extension".** Not available: the
fibre hypothesis is doing real work, and any route that would also prove the unrestricted version is
doomed. (Also: it fails §7.1.)

---

## 5. ⛔ DEAD FALSIFIER HABITATS — do not re-sweep

| habitat | why it cannot work | measured |
|---|---|---|
| **CFI over any base** ⚠⚠ **NARROWED 2026-07-31 — see the correction below the table** | CFI is about *distinguishing two graphs*, not orbit recovery inside one; the gauge group is huge, so orbits stay coarse and WL matches them | twisted over prism, K3,3, Q3, cubic8, K5, Petersen (treewidth ≤ 4) propagate **even at 1-WL**; only `CFI[K4]-tw` fails, and that graph *is* `net(Z₄)` |
| **rigid multipedes** | theorem `Cascade.recoverableAt_base_iff_discrete`: rigid ⟹ orbit partition discrete ⟹ CAO start is discrete ⟹ vacuous | — |
| **non-rigid multipedes** | the loophole, and it is closed: F₂ kernel = ⟨all-ones⟩ ⟹ \|Aut\|=2, CAO start = all 2-element orbits, `\|Aut_v\|=1` so *any* non-singleton cell would be a hit | 10 instances, W=6–10, n=52–114: **1-WL already discretizes** |
| **abelian Cayley, generalized dicyclic** | `x ↦ x⁻¹` fixes `e` ⟹ `\|Aut_e\| ≥ 2`, no GRR exists (⚠ a *GRR-hunt* exclusion only — these remain legitimate 2-WL inputs, and the Schur-ring sweep uses them) | 3681/3681, 1312 resp. — parallel branch, `HANDOFF_2wl.md` §3 |
| **group-derived generally** (Cayley, Johnson, Kneser, Paley, rook, nets over abelian groups) | tend to be schurian outright ⟹ the sharp case never arises | see §6 vacuity ledger |

> ### ⚠⚠ CORRECTION to row 1 (2026-07-31, `probe_step2.py --propagate`, output `probe_step2_prop.out`)
> **"CFI over any base propagates even at 1-WL" is FALSE as stated — every base ever swept was a
> SYMMETRIC NAMED graph.** `cubic8` in that row is the circulant `C₈(1,4)`. Taking instead a **random
> cubic base on 8 nodes** (`probe_route_a.cubic(8, 19)`), CFI over it — **twisted *and* plain**,
> n = 56, `|Aut| = 512` — is a genuine **1-WL CAO-propagation counterexample**: from the exact orbit
> partition (5 orbit-cells), individualizing a rep of the `|C| = 4` cell leaves **1** mixed cell and of
> the `|C| = 16` cell leaves **3**. ⟹ the habitat is **not** dead at 1-WL; the sampling was.
> ★ Note it fails for the **untwisted** CFI too, so this is not a twist phenomenon.
> ★★ **And every 1-WL failure on record from this sweep is at DEPTH 0.** Across 58 reached nodes on
> three witnesses (~800 propagation tests), 1-WL fails **5** times — the m=8 twisted root (2), the
> m=8 plain root (2), the Shrikhande root (1) — and **never at any deeper node**. That is §10.5's and
> §0.0's *"nothing covers the root"* showing up as a measurement, and it is the shape §4.4 warns is
> **not** a general law (`Shrikhande ⊔ Shrikhande` breaks it) — so read it as a property of these
> witnesses, not as an invariant.
> ⛔⛔ **AND THE MATCHING 2-WL RESULT IS WORTHLESS — I ran §7.2 on my own population and it FAILS.**
> 2-WL repaired all 5 and gave 0 failures in ~800 tests, but `probe_step2.py --ticket`
> (`probe_step2_ticket.out`): the roots ARE non-schurian (2-WL rank 78 vs orbital rank 82 / 83), yet
> **every one-point extension is schurian** (`[True, True, True, True, True]`) ⟹ 2-WL success is
> **forced**, exactly the recorded vacuity failure of the 21-object sweep (§6's last-but-one row).
> **Do not enter it in §6's ledger.** ★ What it *does* show, and what is worth chasing: at this root
> the non-schurity lives **entirely off-diagonal** and dies under a single individualization — §7.2's
> own warning (`G ⊔ G`) observed in a new place, and a concrete handle for M1/R1c.

**★ The general lesson from all five rows:** these all fail for the *same* reason — they separate the
group-change from the deficiency (§3). **The CAO hypothesis is self-limiting**: a small group means a
fine start, which hands WL the entire labelling; a large group means a coarse start but coarse orbits
too. Every "shrink the group" design dies on this.

---

## 6. THE EVIDENCE LEDGER — weighted honestly

**⚠ Read the discounts. Two of these numbers were once quoted at face value and were worth nothing.**

| evidence | strength |
|---|---|
| **S-ring sweep, COMPLETE**: 38 verified groups, orders 8–32, **66,888 connection sets · 62,147 non-discrete S-rings · 729 NON-SCHURIAN (genuine entry tickets) · 0 counterexamples** | **the strongest evidence on record.** The entry ticket actually occurs here |
| Parameter-determined SRGs (T(8) + 3 Chang graphs, nets, Paley, Johnson/Kneser) | moderate; Chang-2 is a real 1-WL failure repaired exactly by 2-WL |
| **2-WL recovers the `Aut_v`-orbits EXACTLY on the named VT witness** `Cay(Z₁₂⋊₅Z₂)` (n=24, \|Aut\|=48, \|Aut_v\|=2): `same_partition(2-WL diag, Aut_v-orbits) = True`, while 1-WL = `False` with **all 6** non-singleton cells mixed (2026-07-30, `probe_stall4.py`) | **strong, and sharp.** The input class is known-capable — this is the graph that refutes `VT ⟹ Tinhofer` at 1-WL — so the §7.2 entry ticket is paid, unlike the worthless 21-object sweep |
| VT voltage covers (`Z₂`/`Z₃`/`Z₄` over 9 VT bases): 122 covers, 0 failures | moderate — imprimitive, blocks of size 2–4, not circulant-dominated |
| Descent instrumentation: 11 objects, **16,048 nodes**, fibre-schurian everywhere | ⚠ **DISCOUNT HEAVILY** — only **364** of those nodes still have a cell of size ≥ 3; the rest are near-discrete where schurity is trivial. **The honest figure is 364, not 16k** |
| **★ E1/E2 descent sweep over the sharp Cayley population (2026-07-31, `probe_r1c.py`)**: **465** non-schurian S-rings reached of the recorded 729, **462** instrumented, **56,811 descent nodes to depth 8**, **0 fibre-schurity failures at any node** | **strong, and it upgrades the row above** — that one tested **depth 1 only**; this tests the induction step at **every node of a descent**, which is what a proof needs (E1). ⚠ **Discount for coverage:** 64% of the sharp population (three order-32 groups short), 77 descents truncated at a 400-node budget, 3 inputs' Aut search blown, and 12 groups **sampled** at `CAP_SETS = 4000` (`Z2^5`: 4000 of 2.1×10⁹). **Not yet a population result** — §12.5b lists what closes it |
| **★★ E2 from the same sweep: 477 nodes where fibre-schurity HOLDS but FULL schurity FAILS** | **decisive, and it is a measurement of §4.5** (previously an assertion): the **fibre hypothesis is load-bearing**, so unrestricted *"extensions preserve schurity"* cannot prove the target. ⚠ Does **not** touch §12.4's per-family **R2** |
| The original 2-WL sweep (21 objects) | ⛔ **WORTHLESS** — 0/21 had a non-schurian one-point extension, so it could not possibly have found a counterexample. The recorded vacuity failure |
| **CFI cubic m=8, node sweep (2026-07-31)**: 58 nodes, ~800 propagation tests, **1-WL fails 5× (all at depth 0), 2-WL fails 0×** | ⛔ **THE 2-WL HALF IS WORTHLESS — same failure as the row above**, and I checked it on myself: `--ticket` shows the roots are non-schurian but **all 5 one-point extensions are schurian**, so 2-WL could not have failed. ✅ **The 1-WL half is real and new** — it narrows §5's "CFI over any base" row (which sampled only symmetric named bases) |
| The old 498 + 313 VT pins | ⛔ **UNSOUND** — produced by the broken oracle (§8.2), which errs by *merging* ⟹ false "ok"s |
| **★ P-vs-S separation sweep (2026-08-11, S0)**: 10 named witnesses, `n ≤ 32`, 238 descent nodes, **(P) propagation 0 failures / (S) full schurity 22 failures**, and **every one of the 22 is at a node where (P) holds** | ⚠ **DISCOUNT — near-zero new propagation evidence, and it is not why it matters.** All **16** §7.2-paid tests are on the two union witnesses (`Shrikhande ⊔ rook4×4`, `Shrikhande ⊔ Shrikhande`) — the weakest kind of paid ticket, since `G ⊔ G` is §7.2's own named "non-schurity lives off-diagonal" case. Shrikhande's own (P) tests are **vacuous** (its depth-1 nodes are schurian). 10 witnesses is a beachhead, not a population. **The strong (P) evidence remains the S-ring sweep two rows up.** ★ Its actual value is the **P/S separation itself**: 22 clean instances of *"fibres accurate, pairs not"*, which is §0.0a's incomparability exhibited on named graphs |

⚠ **Two items the S0 sweep flagged, both unresolved and both worth a line before they are re-quoted:**
* **Chang-2 and `Shrikhande ⊔ rook4×4` do not reach CAO from the plain 2-WL root** (1 fibre vs 2
  orbits, each). That is **base-case refiner strength**, not propagation — the sweep seeded from the
  exact orbit partition, so its (P) verdicts are unaffected. But this row's *"Chang-2 is a real 1-WL
  failure repaired exactly by 2-WL"* is ambiguous against it: 2-WL repairs the *propagation* failure,
  it does not necessarily *reach* CAO from the raw graph. **Pin which one is meant before quoting.**
* The same distinction is §13.6(c)'s pattern (failure at the **base case**, not in propagation) and
  §4.4/step-0c's cograph finding. Three sightings; nobody has stated it as one fact.

**Why the descent numbers collapse:** max cell size drops per level (Shrikhande 16→6→4→2→1;
T(8) 28→15→10→6→4→2→1). Descents are over in 4–6 levels, so almost every node is trivially schurian.

---

## 7. ★ STANDING FILTERS — apply these before investing in anything

**7.1 The `G ⊔ G` stress test.** The target is closed under disjoint union. **Any proposed invariant
or proof route must be union-stable, or be applied component-wise.** It is nearly free and it killed
two routes in one call (§4.3, §4.4). Run it *first*.

**7.2 The vacuity / entry-ticket check.** A 2-WL vertex-level failure **requires a non-schurian
one-point extension** (if the extension is schurian the diagonal classes *are* the orbits).
`probe_2wl_vacuity.py` decides both root- and extension-schurity for any candidate in one call.
**Run it on any candidate family before sweeping it.** ⚠ Necessary, **not sufficient** — non-schurity
can live entirely off-diagonal (`G ⊔ G` is exactly that).

**7.3 The Lagrange certificate.** Orbit sizes divide `|Aut_χ|`, so a cell of size `c` with `c ∤ |Aut_χ|`
is **automatically mixed** — no orbit oracle needed. This found every 1-WL counterexample. Extremal
form: trivial stabiliser with a non-discrete colouring.

**7.4 Aim for the convention-independent falsifier.** ⚠ *Naming collision: the parallel handoff calls
these "T1/T2"; that is unrelated to the project's **T1** = the per-family `CellsAreOrbits` totality
obligation. Avoid the T1/T2 labels here.*
- *selector-dependent* (weak): "`chooseIdK` picks a mixed cell" — depends on the colour-id convention,
  so it needs the Lean `#eval` cross-check of §8.3 to be believed;
- ★ *convention-independent* (aim here): **"every non-singleton cell is mixed at a reachable node"** —
  needs no id convention and kills backtracking selectors too. Structural form: *the descent reaches a
  node whose stabiliser is too small for any of its cells*; extremal case, a trivial stabiliser with a
  non-discrete colouring. Note the node need not be at depth 1 — along a legal descent every picked
  cell is a full orbit, so `|Aut_χ|` divides by the cell size each step and shrinks fast.

**7.5 `Tinhofer` is a (graph, SELECTOR) property.** Shrikhande carries a genuine `RigidObstructionAt`
at a node the descent visits, yet **is** `Tinhofer` because `chooseIdK` looks elsewhere — twice.
Measured EXISTS-Tinhofer = True, FORALL-Tinhofer = False. ⟹ **any proof of a `… ⟹ Tinhofer` lemma
must use the concrete `chooseIdK` + `warmRefineVec` id numbering; a selector-free proof cannot exist.**

---

## 8. TOOLING

### 8.1 Sound machinery (validated)
- `probe_cao_cleanroom.py` — own CFI/net construction, own 1-WL, `all_isos` = complete I-R leaf
  enumeration with **every accepted leaf re-verified as a permutation automorphism**.
- `probe_cao_vtcover.py::iso_exists` — early-exit pairwise search. Agrees with `all_isos` on orbits.
- **Validation** (`probe_cao_provenance.py`): 11 independently known `|Aut|` values — K4 24, C6 12,
  K3,3 72, Q3 48, Petersen 120, Kneser(5,2) 120, Kneser(6,2) 720, Paley(13) 78, Heawood 336,
  rook4×4 1152, Shrikhande 192. All match.
- ⚠ `iso_exists` returns `None` on budget exhaustion. **Treat only `is True` as same-orbit and only a
  completed `False` as different-orbit** — conflating `None` with `False` manufactures counterexamples.

### 8.2 ⛔⛔ BROKEN — never use
`probe_orbit_oracle.orbit_partition` (= `canon` **with automorphism pruning** + `leafcap`). Proved on
`multipede[6x5]` (n=30, `|Aut| = 8`, *not* rigid): true orbit partition has **15** blocks; the oracle
returns **11** at the root and **6** when handed the correct partition. **It errs by MERGING** ⟹ it
yields **false "ok"s, never false counterexamples** ⟹ every "0 counterexamples" verdict it ever gave
is unsound, including the 498 + 313 VT pins.

### 8.3 The Lean cross-check pattern
`#eval` on `chooseIdK` / `step`, file placed **outside the package root** so it cannot enter any build;
no `native_decide`. Example: `scratchpad/ShrikhandeTinhoferProbe.lean`.
⛔ **Do NOT hand-reason the colour-id order** from `indivOne χ v = 2·χv + 1`: the `2χ+1` makes `v`
largest, but `sigKey`'s **Cantor-paired** tuples reverse the cell order. This was gotten wrong twice;
only `#eval` settles it. (Irrelevant if you aim for T2 — another reason to.)

### 8.4 Cheap computational identities worth reusing
- For a Cayley graph the **root** closure is translation-invariant, hence the **Schur ring** ⟨S⟩ —
  computable on `G` in `O(n²)` per round from the structure constants, a ~1000× filter versus an `n³`
  pair colouring. ⚠ **But the S-ring is the ROOT closure only**: individualizing `e` destroys
  translation-invariance and the real extension refines **strictly past** it (measured:
  `[1,1,2,4,4,4] → [1,1,2,2,2,4,4]`). Sound as a necessary-condition filter, **never as the verdict**.
- `Aut(G ⊔ G) = Aut(G) wr S₂` — build it programmatically from `Aut(G)`; orbits/orbitals by union-find
  **from generators** (exact, no enumeration). Makes n=32 with `|Aut| = 73728` instant.
- Under CAO, **one representative per cell suffices** when descending: the cell is one orbit, so other
  representatives give conjugate children.

---

## 9. PROCESS TRAPS (each cost real time)

- **Importing a probe module re-runs its module-level sweep.** `__main__`-guard everything. *(Hit three
  times across two sessions — including once while writing the fix for it.)*
- **`pkill -f <script>.py` matches your own launcher's command line** ⟹ self-kill, exit 144. Kill by PID.
- **`str.replace`-based edits silently no-op.** Assert the marker is present and assert the edit landed.
- **Piping a long background command through `tail` buffers everything** — you see nothing until exit,
  and nothing at all if it is killed. Write to a log file.
- **Wrap `all_isos` budget exceptions.** An unguarded `RuntimeError` killed a sweep at its last stage.
- Connection-set / voltage enumerations blow up combinatorially. Cap, and **log what you skipped**.
- **⚠⚠ A FIXED-SEED SAMPLE MAKES A RESTART A NO-OP (2026-07-31, cost a full run).** `probe_r1c.sets_for`
  / `probe_2wl_sring.main` sample capped groups with `random.Random(12345)`, so the sets come out in
  the *same order every time*. Re-running a group that was cut off re-covers its **prefix** and adds
  **zero** coverage — it looks like progress and is not. Offset the sample (`probe_r1c.py --skip=N`).
- **⚠⚠ CHECK A WALL DEADLINE IN THE INNERMOST LOOP (2026-07-31, cost two runs).** A deadline tested
  only *between groups* let one order-32 group overrun it by hours; both runs were then killed by the
  shell timeout with **no summary at all** (EXIT 124), so hours of compute produced nothing quotable.
  Test it in the item loop, and always print a summary on the way out.
- **A wall-clock "elapsed" figure is not compute time.** A suspended machine turned a 65-minute budget
  into a `wall: 33873s` line. Trust per-checkpoint timings, not the total.
- **Check the exit code, not the completion notice.** A background task reporting "completed" may have
  been *killed* by its timeout — `EXIT 124`. Two partial sweeps were briefly read as finished results.

---

## 10. OPEN ITEMS

> ✅ **Closed since this doc was written:** (a) the reduction (Steps 1–2) — `CaoFibring.lean`,
> §12.1–12.2; (b) **that reduction applied to the REAL closure, plus the round-1 and round-2
> barriers** — `CaoRound.lean`, §12.3/§12.6; (c) **M2 is answered** (§12.3's convention box) and
> **M3 is done** (§12.6). The open items below are what is left.

1. **The live target (§2), unproven — and now sharpened past "a single named hypothesis" to a single
   named QUANTITY.** The barriers reduce it to the **triple count** `N(a,b;i,j,k)` and the round-3
   aggregate over it; the full statement and the ordered attack are **§12.5a (R1a–R1g)** — after §13.
   Treat it as
   a genuine question of algebraic combinatorics — the schurity of one-point extensions — not a lemma
   to discharge. ⚠ Use the `CaoRound.step2_closure` form, not `CaoFibring`'s (§0). The practical
   fallback is a **per-family certificate** (§12.4 R2/R3); note `ChainDescent/Separability.lean` and
   `ChainDescent/CoherentConfig.lean` already carry `Separable` / `SeparablePointed` /
   `ExtensionSeparable` — R2's vocabulary — and `CoherentConfig` also carries `IsPointExtension`, the
   *construction* `pointExtension`, and `Theorem41Statement` (§12.6 M5).
2. ✅ **RAN 2026-07-31 — E2 ANSWERED, E1 clean at 64% coverage. FULL RECORD = §12.5b.** The `E1/E2`
   descent instrumentation over the **sharp Cayley inputs** (= §12.5a R1c = §12.6 M1). The ≤ ~24-input
   cap is fixed: **`scratchpad/probe_r1c.py`** runs the instrument over the 38-group population with
   every sample/skip/truncation logged (§9). **465** of the recorded **729** sharp inputs reached,
   **462** instrumented, **56,811 descent nodes to depth 8** — **E1: 0 fibre-schurity failures;
   E2: 477 nodes where fibre-schurity holds but FULL schurity fails ⟹ the fibre hypothesis is
   load-bearing.** ⚠ Four named coverage gaps remain (three order-32 groups, 77 truncated descents,
   3 blown Aut searches, 12 sampled groups) — §12.5b lists exactly what closes them. ★ Why this
   population and no other: a Cayley root over a **transitive** group satisfies CAO *automatically*,
   and — unlike the CFI population measured the same day — it **genuinely pays §7.2's entry ticket**
   (§12.5b explains why the two differ).
3. **The coupling construction (§2, §3).** Nobody has yet tried to *build* an object with the
   group-change and the deficiency at the same cell pair. That is the falsifier design, and it is the
   only one not already excluded by §5.
   **★ §14.4 (2026-08-01) gives it a CRITERION instead of a blank page:** the 1-WL failure is the
   pullback of a local group that is transitive on points but not pairs (§14.1), so the 2-WL analogue
   needs one transitive on pairs but not triples — i.e. a **not-2-closed** point stabilizer, which by
   the 2-closure obstruction **cannot be exposed by any binary structure on the cell** and must be
   carried by far vertices attaching to **triples** (designs, not graphs). ⟹ **the filter: hunt a VT
   graph whose point stabilizer acts 2-transitively but not symmetrically on some cell.** Cheap on any
   family with computable stabilizers; ⚠ read §14.4's scope caveats before treating a hit as a
   counterexample.
4. **Per-family route.** The project's hard families (forms graphs, Cameron) have known classical
   groups, so their orbitals are computable and schurity is provable *per family* — no general theorem
   needed. Related but distinct: the node-4 families reportedly shatter under ≤ 4 individualizations.
   ⚠ Bounded depth is **not** union-stable (§4.3), so it can only ever be a per-family statement.

5. **★ THE SELECTOR ROUTE (A) — ⛔ ITS CHEAP (RESOLVER-LEVEL) FORM IS NOW MEASURED DEAD (2026-07-31);
   the expensive form (a stronger supply) is what is left.** The alternative to
   the whole 2-WL swap. **Measured fact it rests on:** on every recorded VT-non-`Tinhofer`-at-1-WL
   witness, consume *does* fire, because index-min selection happens to pick vertices in one orbit.
   (§7.5's Shrikhande is the same phenomenon; limit 2 of §0.0 is the force-side tally). 
   Disjoint antagonistic copies of VT graphs can be made to fail comparisons between them,
   but some consumable comparisons survive. **The target:**
   *prove the lowest-index selector — or a better canonical one — always lands on a resolvable cell.*
   User's concrete variant: **lowest index, with priority to vertices shared under both descents.**
   - **⚠ Do NOT kill this with the `⛔⛔ NO STABILIZER CHAIN` steer — it does not apply.** That steer
     forbids an *iso-invariant within-cell vertex pick* as the guarded object. Here (i) choosing a
     **cell** is canonical (`targetColour` transports), and (ii) `deepen`'s within-cell pick is already
     non-canonical and is legitimised downstream by the all-anchors quantification + the verification
     gate, not by canonicity of the pick. A *better* pick is therefore legal where a *canonical* one is
     not.
   - **The obstruction to state plainly:** "pick a single-orbit cell if one exists" is not a selector a
     refinement can compute — orbit membership is the thing being decided. The realistic form is
     **resolver-level, not selector-level**: try cells, keep one where the supply certifies
     transitivity (poly: ≤ n cells × one supply call). That is a `Select`-layer change, and it converts
     the question from "is the selector lucky" into "does *some* cell resolve", which is strictly
     weaker and matches `Select.NodeResolved`'s shape.
   - **⛔⛔ AND THAT RESOLVER-LEVEL VARIANT IS NOW MEASURED — IT BUYS NOTHING (2026-07-31,
     `probe_route_a.py`, result at `probe_route_a.out`).** The experiment: at every reached node, run
     the record's own deepen harvest (`DeepenSupply.lean` ported faithfully — all anchors, `coupled`
     footprint match, `twistOf` re-verified, transitivity by BFS closure over the *verified generator
     set*, never per-pair) on the `chooseIdK`-**selected** cell **and on every other non-singleton
     cell**, and ask whether any cell certifies where the selected one does not.

     | witness | nodes | selected cell certifies | **selected fails, another certifies** | no cell certifies |
     |---|---|---|---|---|
     | CFI cubic m=8 **twisted** (n=56, the recorded obstruction) | 27 | 25 | **0** | 2 |
     | CFI cubic m=8 plain (n=56) | 27 | 26 | **0** | 1 |
     | Shrikhande (n=16) | 4 | 4 | **0** | 0 |

     **Zero nodes on any witness where trying other cells helps.** The two twisted failures are the
     **root** (cells 32 and 24, both uncertified) and **`root/id1/id9`** — the recorded shape, an
     8-cell node sharing the **`|C| = 16`** shape of DUAL §2.1 — where **all eight** cells fail
     together.
     ⚠⚠ **CORRECTED SAME DAY (§13.6b): the failure is NOT "supply incompleteness".** Measured against
     the exact automorphism group: root `|Aut_χ| = 512` with **both** cells mixed (32 → 2 orbits,
     24 → 3), and `root/id1/id9` `|Aut_χ| = 64` with **all eight** cells mixed. **No cell at either
     node is a single orbit**, so the harvest's `✗` is *correct* — there was nothing for any selector
     or supply to certify. These are **force-domain** nodes. ⚠ They are also **not** DUAL §2.1's node
     (which is one force-key refinement below the root and whose `|C| = 16` cell *is* one orbit).
     ⟹ **route (A)'s cheap form is dead at the recorded witnesses.** What survives of (A) is only the
     expensive form: a *stronger supply*, which is not a selector question at all.
     ★ Note the positive half is also confirmed: **25/27** nodes resolve at the selected cell — §0.0's
     "consume measurably does fire (selector luck)", now with a denominator.
     ⚠ **Read the verdict correctly.** "Not certified" means *this supply did not certify*, never
     "different orbits" (the probe uses **no orbit oracle**; every ✓ is a verified certificate). And
     the id order is Python's, not Lean's `sigKey` (§8.3) — so "which cell is *selected*" is
     convention-dependent; the **0 in the middle column is not**, since it quantifies over all cells.
   - **⚠ The gap the user named and it is the load-bearing one:** no guarantee at the **root**, where
     there is no parent structure to exploit and an antagonistic input has the most freedom. Any
     attempt should attack the root case first — if it fails there, the route is over cheaply.
   - **⚠ Selector claims are convention-dependent** (§7.4, §8.3): anything proved here must be pinned
     against the concrete `chooseIdK` + `warmRefineVec` id numbering by Lean `#eval`, never by
     hand-reasoning the colour order (gotten wrong twice).

---

## 11. FILE INDEX

**Falsifier hunts** — `probe_cao_propagates.py` (the original 1-WL hit) · `probe_cao_bases.py`
(CFI over many bases) · `probe_cao_net.py` (the `net(G)` family + the `CFI[K4] ≅ net` identification) ·
`probe_cao_vtcover.py` (VT voltage covers) · `probe_2wl_sring.py` (the 66,888-set Schur-ring sweep) ·
`probe_2wl_chang.py` (T(8) + Chang) · `probe_2wl_multipede.py` (non-rigid multipedes).

**Instrumentation / calibration** — `probe_2wl_vacuity.py` (entry-ticket check, §7.2) ·
`probe_cao_2wl.py` (1-WL vs 2-WL side by side) · `probe_cao_net2wl.py` · `probe_cao_induction.py`
(fibre- and full-schurity at every descent node) · `probe_cao_coarse.py` (the discount in §6) ·
`probe_cao_union.py` (the `G ⊔ G` stress test) · `probe_cao_mechanism.py` (the `CFI[K4]` twisted-vs-
untwisted dissection: wire-pairs as a block system, and the `|Aut|` 192-vs-576 accident) ·
`probe_cao_mechanism2.py` (the coupling / fused-orbital measurements of §3) · `probe_cao_rounds.py` (§12.3: the round at which the extension separates fused orbitals — 3 for Shrikhande/Chang-2, 4 for `net(Z₄)`) ·
**★ `probe_cao_cause.py`** (§12.6 M3 — the cause-chain instrument: witness triangle types at the
separating round, birth-round trace, recursive explanation. **The uniform depth-3 chain**) ·
**★ `probe_cao_round2.py`** (§12.6: round 1 == `zAug` and NO separation before round 3 — the measurement behind `round2_barrier`; also checks the transpose axiom) ·
**★ `probe_cao_cause2.py`** (M3 follow-ups: the **ablation** — necessary class distinctions, measured
**0** ⟹ over-determined — and the **population** run over deficient roots at diameters 3–4 via
Shrikhande □ `C_m`; takes explicit automorphism generators, so no `all_isos` at n = 80) ·
**`probe_cao_diameter.py`** (§12.3 convention box, term 1: Johnson recovers `Aut_v`-orbits at round
⌈diam/2⌉ — the construction refuting a constant bound on the *total* count) ·
**`probe_cao_diam_deficient.py`** (term 2: Shrikhande □ `C_m`, a **deficient** root at growing
diameter — the Doob-graph shape — fused orbitals separate at round **3** at diameters 3/4/5, removing
the diameter-2 confound) ·
**`probe_stall.py` / `probe_stall2.py` / `probe_stall3.py` / `probe_stall4.py`** (§0.0 limit 2 — at each
1-WL *manufactured* mixed cell, the minimum lookahead depth at which the force key separates the true
`Aut_v`-orbits; depth 1 = `lookaheadKey`'s own non-discrete branch. `probe_stall4.py` is the named VT
witness `Cay(Z₁₂⋊₅Z₂)` — ⚠ its connection-set search is slow (~2048 masks × `all_isos` at n = 24), so
run it detached per §9; **result recorded at `probe_stall4.out`**).
**★★★ `probe_r1c.py`** (§12.5b = R1c/M1/§10 item 2 — the **E1/E2 descent instrument over the sharp
Cayley population**, replacing `probe_cao_induction.py`'s ≤ ~24-input cap. **Main run
`probe_r1c.out`**: 465/729 sharp inputs, 462 instrumented, 56,811 nodes to depth 8 — **E1 0 failures,
E2 477 fibre-ok/full-fail**. Flags: `--smoke` · `--groups=A,B` · `--wall=SECS` · **`--skip=N`**
(⚠ mandatory when resuming a cut-off group — the sample is fixed-seed, so a plain restart re-covers
the prefix; §9). Tail runs: `probe_r1c_tail.out` (`Z4^2xZ2` prefix re-run — **no added coverage**),
`probe_r1c_z8xz4.out`. **Read §12.5b before quoting any of it.**) ·
**★★★ `probe_step2.py`** — four modes, and **run `--ticket` before quoting any 2-WL number from it**
(`--calibrate` · `--nodes` · **`--propagate`** = §5's correction: the propagation test run at every
reached descent node, from that node's CAO start, 1-WL vs 2-WL, output `probe_step2_prop.out` ·
**`--ticket`** = §7.2's entry ticket, output `probe_step2_ticket.out`). (§13.5 **S1 + S4**: the concrete **2-WL `Deepen.step`** — individualize,
2-WL pair closure, read `(diag u, c(v,u), c(u,v))` — and the **A/B** running the harvest at the 1-WL
step vs the 2-WL step on the two nodes where the 1-WL harvest certified nothing. ★ **`--calibrate`
reproduces doc §0.0's `net(Z₄)` figures exactly** (1-WL 5 cells/2 mixed, 2-WL 7 cells/0 mixed) — run
it before believing anything else in the file. Three modes: `--calibrate` · `--nodes` (**the decisive
diagnostic of §13.6** — cells-vs-exact-orbits, the 2-WL closure vs the orbit partition, and the
step-by-step path comparison; output **`probe_step2_nodes.out`**) · no flag = the A/B, output
**`probe_step2.out`**) ·
**★★ `probe_route_a.py`** (§10.5 — the **route (A) resolver-level experiment**: at every reached node,
the record's deepen harvest run on the `chooseIdK`-selected cell *and on every other cell*, asking
whether any cell certifies where the selected one fails. **Answer: 0 of 58 nodes, on all three
witnesses.** Faithful port of `DeepenSupply.lean`; every verdict is a re-verified certificate and **no
orbit oracle is used**; skips are logged per §9. Result recorded at **`probe_route_a.out`**, ~9 s).
**★★ `probe_cao_anatomy.py`** (**§14**, output **`probe_cao_anatomy.out`**, ~22 s; `--closure` adds the
32,768-graph brute force — several minutes, run detached per §9; its verdict is already in the `.out`).
Four measurements: **(A)** the exposed local shape and the far
cell's split as a **pullback of its pair-orbits** — Shrikhande vs rook 4×4, the two `SRG(16,6,2,2)`
graphs; **(B)** the **support structure of mixed cells** at depth ≤ 2 over every deficient root — 14
mixed cells, **0 without mixed support**, and the support is **circular** (§14.2's steer); **(C)** the
concrete distinguisher (*are `v`'s two common neighbours with `u` adjacent?* — 9/9); **(D)** the arity
lift — `A₅` on 6 points is transitive on pairs, `[10,10]` on triples, and the **2-closure obstruction**
(0 of 32,768 graphs on 6 vertices have a 2-transitive-but-not-`S₆` group).
**★★ §14.5 — the PATH-CONDENSATION probe set** (2026-08-05, seconds each unless noted).
`probe_pathcondense.py` (the five pair-objects side by side: orbitals · 2-WL · walk counts · V4's
recursion · `[cell,adj,cell]`, at a CAO root) · `probe_pathcondense2.py` (transpose-artifact control
via symmetrized partitions, **plus** the post-individualization half: 2-WL fibres vs `Aut_v`-orbits) ·
**`probe_v4_vs_2wl.py`** (§14.5a — **V4's recursion == the 2-WL pair closure as a PARTITION, 7/7**) ·
`probe_pathanno.py` (the `A0`/`A1`/`A2` ladder — walk counts, simple-path counts, annotated simple
paths; `simple_paths_profiles` is the reusable enumerator, takes a `deadline`) ·
`probe_pathanno2.py` (the same at **fair truncation** — ⚠ comparing `A0` at length `n` against
`A1`/`A2` at a short `maxlen` produces a spurious "does not refine"; truncate all three alike) ·
`probe_pathanno3.out` (longer CFI lengths; **reached length 14 only** — 16/18 were not run) ·
**`probe_shrikhande_explain.py`** (§14.5b's named witness `v=0, u=2, w=6`, and the round trace) ·
**`probe_arity_ladder.py`** (§14.1's pullback re-verified on Shrikhande + rook, and §14.4's rung-2
check on `A₅ = PSL(2,5)`: point/pair/triple orbits and the 2-closure).
**★★ §14.5e — the three probes that CLOSED the route** (2026-08-05): **`probe_window.py`** (the
**window ladder** `r=1..7` vs 2-WL vs orbitals; `ravoid_profile` is the reusable enumerator — the
`r=2`-buys-nothing and `r=3`-first-pays results) · **`probe_loopdetect.py`** (per-walk purity of the
**most generous** condensed key — pair colours to *both* endpoints, the **fibre colour** `c(x,x)`
i.e. the vertex's whole loop profile, and every consecutive edge colour; plus the per-separation
breakdown. ⚠⚠ **read the separation column only through its vacuity filter** — CFI is **bipartite**
so odd separations never occur, and `s ≥ L−1` has an empty range; both print as "RECOVERABLE" and
**both are artifacts**) · **`probe_loopcompare.py`** (§14.5e(2)'s count-level refutation: the premise
check — loop profile orbit-uniform — and the **length-7 / window-3, 3880 vs 3882** witness.
⚠ It ships `ML = 9`; at `ML ≤ 6` every window agrees and the probe reports a **false PASS**).
Shared machinery lives in `probe_cao_cleanroom.py` (§8.1); most files import it, so they are
`__main__`-guarded — keep them that way (§9). ⚠ `probe_pathanno.py`, `probe_pathcondense.py`,
`probe_window.py` and `probe_loopcompare.py` are **imported** by the later probes and are guarded;
keep them so.

**Provenance** — `probe_cao_provenance.py` (§8.1/§8.2).

**Lean (this doc's own results)** — both in `build.sh`, axiom-clean, all declarations described in
`PublicTheoremIndex.md` / `PrivateTheoremIndex.md`:
- **`ChainDescent/CaoFibring.lean`** (18 decls) — Steps 1–2: the fibring lemma and the reduction to
  orbital separation, for an *abstract* invariant pair colouring.
- **`ChainDescent/CaoRound.lean`** (**42 decls**) — §1 `PairInvariantAt` + **`step2_closure`** (Step 2
  at the **real** individualized closure — the version applications must use); §2 the round and that it
  preserves invariance; §3 **`round1_barrier`** + `witness_ne_base`; §4 `zAug`/`Transposable` +
  **`round2_barrier`**; §5 `sig_ext0_congr` → **`exists_factor_roundBy_ext0`** (`hg` discharged) →
  **`round2_barrier_real`** (unconditional); **§6 the conditional converse = R1e** — `triCount`,
  `roundBy_ne_iff_sig_ne`, `sig_ne_iff_exists_triCount_ne`, `round2_row_colour_eq` ⟹
  **`round3_separates_iff_triCount_ne`**: round-3 row colours differ **iff** some triangle type of the
  round-2 colouring has a different `triCount` at `(v,u)` vs `(v,w)`. ⚠ carries one hypothesis,
  `Function.Injective enc` (faithful re-encoding) — ⚠⚠ **NOT met by the rank renumbering**; repair =
  §12.5a R1g. ⟹ **everything up to round 3 is discharged; pin the per-family R2/R3 certificate to
  that inequality** — ⚠⚠ it is **sufficient, not equivalent** (§0's box: the closure is *not*
  discharged, round 4+ remains free).

Checks and cross-checks (**outside** the package root by design, §8.3) — `scratchpad/CaoFibringAxioms.lean`,
`scratchpad/CaoRoundAxioms.lean` (`#print axioms` for all of both modules) ·
`scratchpad/ShrikhandeTinhoferProbe.lean` (the `chooseIdK` `#eval` cross-check of §8.3).

**Parallel branch (1-WL VT hunt, succeeded)** — [`../scratchpad/HANDOFF_2wl.md`](../scratchpad/HANDOFF_2wl.md),
`probe_vt_witness.py`, `VTNotTinhoferProbe.lean`.

**Lean definitions this doc is about** — `ChainDescent/DeepenTinhofer.lean` (`CellSingleOrbit`,
`RigidObstructionAt`, `TinhoferPath`, `Tinhofer`), `ChainDescent/DeepenSupply.lean` (`chooseIdK`,
`step`), `ChainDescent/Refine.lean` (`warmRefineVec`, `keyOf`, `refineRound`).

---

## 12. ▶▶ PROOF PLAN for the live target (§2)

**Setup.** `X` = the 2-WL closure of `(G, χ_orb)`, whose fibres are the `K`-orbits (CAO), `K = Aut(G)`,
`v ∈ D`, and `X_v` = the coherent closure of `X` with `v` individualized. Target: the fibres of `X_v`
on `C` are the `K_v`-orbits on `C`.

### 12.1 Step 1 — the fibring lemma  ✅ **LANDED** (`ChainDescent/CaoFibring.lean`, in `build.sh`)

> `K` is transitive on `D` ⟹ the map `O ↦ {u ∈ C : (v,u) ∈ O}` is a bijection from the `K`-orbitals
> inside `D × C` onto the `K_v`-orbits on `C`.

Pure group theory (no WL, no graphs). It converts the target into orbital separation and is the
reason §3's mechanism table is exhaustive. Axiom-clean (`[propext, Classical.choice, Quot.sound]`),
no `sorry`, stated in the project's own `IsColAut` / `CellSingleOrbit` idiom so it composes with
`DeepenTinhofer.lean`:

| name | content |
|---|---|
| `isColAut_one` / `_mul` / `_inv` | `IsColAut adj χ` is a group (needed: the argument composes and inverts) |
| `SameOrbital` / `SameStabOrbit` | the 2-orbit relation and the point-stabilizer orbit relation, + refl/symm/trans for both |
| `sameStabOrbit_iff_sameOrbital_row` | on `v`'s row the two coincide — the statement Step 2 consumes |
| **`exists_row_transport`** | **every orbital meets `v`'s row**; the surjectivity half, and *the only place transitivity on `D` is used* |
| `sameStabOrbit_of_transports` | the row transport is well defined up to `K_v` |
| **`sameOrbital_iff_sameStabOrbit_of_transport`** | the row transport is a **complete invariant** of the orbital class ⟹ with `exists_row_transport`, the bijection. Needs **no** hypothesis — `CellSingleOrbit` is required only for *existence* of transports |

⚠ **Not** formalized: the size statement `|O| = |D| · |fibre|`. It needs `Finset` cardinality work and
nothing downstream uses it; the logical content Steps 2–3 consume is complete without it.

### 12.2 Step 2 — reduction to the FUSED classes  ✅ **LANDED** (same module, §4)

> If `X` already separates the orbitals inside `D × C`, the target holds automatically.

*Proof.* The `X`-colour of the pair `(v,u)` is an invariant `X_v` inherits, and by Step 1 its level
sets are exactly the `K_v`-orbits. ∎

Formalized for an arbitrary `IsColAut`-invariant pair colouring `f` (`PairInvariant`) — which is what
any 2-WL closure supplies, so the statement is independent of the refinement's details:
- `pairInvariant_eq_of_sameOrbital` — **soundness**: `f` is constant on orbitals, i.e. its classes
  are *unions* of orbitals. This is why refinement can never split an orbit.
- **`levelSet_iff_stabOrbit_of_separates`** — if `f` merely *separates the orbitals in `v`'s row*
  (`hsep`), then `u ↦ f v u` has level sets **exactly** the `K_v`-orbits.

⟹ preservation reduces to orbital separation **with no remainder**, and `hsep` is precisely the open
crux of §12.3 — now isolated as a single named hypothesis rather than diffused through the problem.

> ### ⚠ CORRECTION + ✅ FIX — Step 2 did not literally apply to the real object (`CaoRound.lean`, 2026-07-30)
> `levelSet_iff_stabOrbit_of_separates` asks for `PairInvariant adj χ f` = invariance under **all** of
> `IsColAut adj χ`. But the colouring the algorithm builds is the closure of the configuration with `v`
> **individualized**, which is invariant only under the **stabilizer of `v`**. So the landed Step 2 was
> a true theorem about an abstract `f` that the real closure did not satisfy.
> **Fixed and gated — `ChainDescent/CaoRound.lean` (11 theorems, axiom-clean):**
> - **`PairInvariantAt`** — invariance under `{σ ∈ IsColAut adj χ : σ v = v}`, exactly the group
>   `SameStabOrbit` is about; **`levelSet_iff_stabOrbit_of_separatesAt`** = Step 2 at it. Nothing is
>   lost — the `←` direction only ever used a `σ` fixing `v`, because it *comes from* `SameStabOrbit`.
> - **`pairInvariantAt_ext0`** (individualizing `v` keeps stabilizer-invariance) +
>   **`sig_congr`**/**`pairInvariantAt_roundBy`**/**`pairInvariantAt_iterRoundBy`** (a refinement round
>   preserves it — the content is that `σ` may be absorbed into the intermediate point, since it
>   permutes the universe) ⟹ **`step2_closure`**: start from any invariant root colouring,
>   individualize `v`, take **any** number of rounds — if the result separates the orbitals in `v`'s
>   row, its level sets there are exactly the `K_v`-orbits. **Step 2 now applies to the real object,
>   with `hsep` the only thing left.**

⟹ **all content is confined to `X`-classes that fuse ≥ 2 orbitals meeting `v`'s row.** This is not a
cosmetic reduction: in the completed Schur-ring sweep only **729 of 62,147** non-discrete instances
(≈ 1.2%) had a non-schurian root at all, and §6's other families are mostly schurian outright. Steps
1–2 therefore discharge the overwhelming majority of inputs with no new mathematics, and they extend
the free territory well beyond the two landed fragments (`cellsAreOrbits_of_discrete`,
`cellsAreOrbits_of_compl_card_le_two`).

### 12.3 Step 3 — the crux, and why it cannot be local

Remaining case: a fused class `R = O₁ ⊎ O₂ ⊎ …  ⊆ D × C` meeting `v`'s row in ≥ 2 orbitals. Show
`X_v` separates them.

> **⛔ THE ROUND-1 BARRIER — ✅ NOW MACHINE-CHECKED** (`CaoRound.round1_barrier`, axiom-clean; it was
> prose until 2026-07-30, and per the project's own steer a pinned statement nobody has tried to prove
> can be false — this one is not). Coherence is stated in the form that actually says it: a coherent
> colouring is a **fixpoint** of the round (`CaoRound.Coherent`). The proof splits the signature at the
> base point: the flags contribute the *same single term* to both sides, and the remaining multisets are
> equal by coherence + multiset cancellation. Its positive companion **`witness_ne_base`** is the other
> half of what M3 measures: if a round *does* separate `(v,u)` from `(v,w)` while they share a colour,
> the difference provably lives in the intermediate points **`x ≠ v`** — so *the marking must leave `v`
> and come back* is a theorem, not an observation. The round-1
> refinement of the pair `(v,u)` is the multiset over `x` of `(col(v,x), col(x,u))`, and by
> **coherence** that count is the intersection number `p^k_{ij}` with `k = X`-class`(v,u)` —
> *identical for every `u` in the same `X`-class*. **The base point learns nothing directly.**

So the marking must travel: a far pair `(a,b)` acquires its **triangle type**
`(X`-class`(a,v), X`-class`(v,b))`, that splits the far classes, and only the feedback from those
splits reaches `(v,u)`. **Measured** (`probe_cao_rounds.py`): separation first occurs at
**round 3** (Shrikhande `[3,6]`; Chang-2 `[4,4]`, both classes) and **round 4** (`net(Z₄)`, both
classes) — never earlier, exactly as the barrier predicts. **Any proof is a statement about this
feedback loop, not about the base point.**

> ### ⚠⚠ ROUND-COUNT CONVENTION — the "3/3/4" above is a CONFLATED figure (corrected 2026-07-30)
> `probe_cao_rounds.py` counts from the **raw** colouring, so its figure is the sum of two terms
> that behave completely differently:
>
> **`rounds_total = rounds_to_BUILD X  +  rounds_of_the_EXTENSION from X`**
>
> - **Term 1 grows with DIAMETER and is unbounded** — refinement carries information ~2 hops per
>   round. Measured (`probe_cao_diameter.py`): Johnson `J(m,k)` recovers its `Aut_v`-orbits at round
>   **⌈diam/2⌉** exactly — `J(6,2)/J(6,3)/J(8,4)/J(10,5)` → **1/2/2/3** at diameters 2/3/4/5. **So no
>   constant bounds `rounds_total`, by construction** (user, 2026-07-30: any VT family of growing
>   diameter does it).
> - **Term 2 is the one §12.3 and M2 are about**, and it is measured **constant 3** across every
>   deficient root on record — including at growing diameter (`probe_cao_diam_deficient.py`):
>   Shrikhande □ `C₃`/`C₅`/`C₇`, diameters 3/4/5, **all fused classes separate at round 3**, while
>   term 1 goes 3/3/3 and 4 at diameter 6.
>
> ⚠ **PARTIAL confound in the old figures** — ⚠ and a correction to an earlier version of this box,
> which claimed *all three* original roots were diameter 2. **Measured**: Shrikhande **2**, Chang-2
> **2**, but `net(Z₄)` is **diameter 4**. So `net(Z₄)` was already a >2-diameter deficient root and
> still separates at term-2 round 3. The □`C_m` family widens it further — and it is the **Doob-graph
> shape** (distance-regular, *not* distance-transitive), so the deficiency is real at every diameter;
> it simply stays localized in the Shrikhande factor, so separating it never needs long-range
> information.
> ⟹ **State which term you mean.** A bound on term 1 is refuted; a bound on term 2 is live and now
> has evidence at diameter > 2.

### 12.5a ▶▶ THE CRUX WORK PLAN (R1a–R1g) — added 2026-07-31, re-ordered the same day (§13 first)

**What the crux now is, exactly.** Rounds 1 and 2 are proved blind on `v`'s row
(`CaoRound.round1_barrier`, `round2_barrier`), so the whole question is what **round 3** does. Round 2
gives a far pair `(a,b)` the **triple count**

```
N(a,b; i,j,k) = #{ x : X(a,x) = i,  X(v,x) = j,  X(x,b) = k }
```

and this is the first quantity **coherence does not determine** — coherence fixes only the *pair*
intersection numbers `c^{X(a,b)}_{ik}`. Round 3 at `(v,u)` then aggregates it:

> **R1, fully sharpened.** For `u, w` in different `K_v`-orbits inside one `X`-class on `v`'s row,
> the multiset over `x` of `(X(v,x), N(x,u; ·,·,·))` differs from the same multiset for `w`.

This is a **single explicit finite invariant**, computable, and `K_v`-invariant by construction. The
target is that it is *injective on `K_v`-orbits within an `X`-class*.

| # | step | cost | why / what it decides |
|---|---|---|---|
| **R1a** | **Coordinate-level ablation of `N`.** Which *projection* of the triple count does the work — the full `N`, or a marginal (e.g. fixing `j`, the relation to `v`)? | hours | §12.6's ablation was at *class* granularity and came back "over-determined"; at **coordinate** granularity it can still be sharp, and it names the smallest object a proof must control |
| **R1b** | **Base-point uniformity.** CAO makes `D` a single `K`-orbit, so the invariant transports across base points. Measure whether separating power is uniform over `v ∈ D` | hours | decides whether the theorem is *"for all `v`"* or only *"for some `v`"* — materially different statements, and §7.4/§7.5 show selector-dependence is a real hazard here |
| **R1c** ✅ **RAN 2026-07-31 — see §12.5b** | **The falsifier, in the one place it can live** (= M1, sharpened). A Cayley root over a **transitive** group satisfies CAO *automatically* (one fibre = one orbit), so the **729 non-schurian S-rings are exactly the sharp inputs.** Fix the probe cap and run them | ~1 h/run, several runs | **did not end the track — E1 found 0 counterexamples** over 465/729 sharp inputs and 56,811 descent nodes to depth 8. ★ **E2 answered: the fibre hypothesis is load-bearing.** ⚠ 64% coverage; four named gaps in §12.5b |
| **R1d** | **Literature check.** *"Point extensions of schurian CCs need not be schurian"* is standard ⟹ **the CAO hypothesis must be doing essential work**, and any known non-schurian point extension whose root is *fibre*-schurian is an immediate counterexample | hours | far cheaper than §10.3's build-one-from-scratch, and it tests the same thing |
| **R1e** ✅ **LANDED** (`CaoRound.lean` §6) | **Lean: name the invariant.** **`round3_separates_iff_triCount_ne`** — round 3 separates **iff** some triangle type of the round-2 colouring has a different `triCount` at `(v,u)` vs `(v,w)`. Everything **up to round 3** is discharged | done | the R2/R3 per-family pin is a *deliverable*: pin it to `triCount`. R1a still sharpens *which projection* of the count to pin. ⚠⚠ **SUFFICIENT, NOT EQUIVALENT** — see §0's box: `triCount` agreement at round 3 does **not** refute the crux (round 4+ can still separate), so this target is strictly stronger than the crux |
| **R1f** | **The aggregate/rank attempt.** Informed by R1a/R1b | open | the actual proof. ⚠ Expect a sharper statement, not a proof. ⚠ And note it would be aimed at the *strengthened* statement (R1e's caveat) — if that resists, the fallback target is the crux itself (separation at the fixpoint), which no current instrument addresses |
| **R1g** | **The `enc`-hypothesis repair.** `Function.Injective enc` is **not** satisfied by the rank renumbering (bounded range, unbounded domain). Weaken to `Set.InjOn` over the pairs that occur, or add an enc-independence lemma (the induced *partition* is the same for any faithful-on-occurring-values encode) | hours | the per-family certificate is pinned to a theorem whose hypothesis the real refiner does not meet as stated — the project's recurring statement-level trap. Cheap, and it makes the pin instantiable |

**⚠ Two constraints any attempt must respect.** (i) §4.2 — `k`-WL sees only structure constants, so
the argument must conclude **separation**, never *"an automorphism exists"*. (ii) §12.6's ablation —
do **not** hunt a distinguished witness class; it does not exist.

**▶ Order (revised 2026-07-31, user).** **§13's conversion-gap scoping FIRST** — it gates the value of
every row here. Then **R1c + R1d** in parallel (either can end the track; ⚠ R1c is a *population fix*,
not a new falsifier hunt — §0.0). **R1g** is a cheap statement-level repair, do it alongside any §6
work. **R1a + R1b** only if the track survives that, and **R1f** last — and as a per-family
certificate program (§12.4 R2/R3 + §12.6 M5), not a general proof attempt.

### 12.5b ▶▶ R1c / M1 / §10 item 2 — RAN 2026-07-31: E2 ANSWERED, E1 clean on 64% of the population

**Read this before running or quoting anything from `probe_r1c.py`.**

**What was wrong, and what is now built.** `probe_2wl_sring.py` sweeps the whole population (66,888
connection sets, 38 verified groups of orders 8–32 → 62,147 non-discrete S-rings → **729
non-schurian**) but tests **depth 1 only**. `probe_cao_induction.py` has the instrument a proof needs
— **E1/E2**, fibre- *and* full-schurity at **every node of a descent to discreteness** — but its
sharp-Cayley section iterates 8 groups of order 16 and `break`s at `hits > 3`, so it exercises
**≤ ~24 inputs**. ✅ **`scratchpad/probe_r1c.py` runs the E1/E2 instrument over the full population**,
with the cap removed and every sample/skip/truncation logged (§9).

**★ The entry ticket here is genuinely PAID — and that is not automatic.** For a Cayley graph the root
2-WL closure is the Schur ring `⟨S⟩`. A **schurian** S-ring has basic sets = `Aut_e`-orbits; the
extension's fibres refine the basic sets and are unions of `Aut_e`-orbits, so they are forced to equal
both ⟹ **a schurian S-ring makes failure impossible.** Hence *"S-ring non-schurian"* is a **necessary**
condition for a failure at `e`, i.e. a valid entry ticket, and the 465 sharp inputs are genuinely
sharp. **E1's evidential value is unchanged by the correction below.**

> ### ⛔ CORRECTION (2026-08-11) — the ticket is valid, its NAME was wrong
> An earlier version of this paragraph said the basic sets *"are exactly the diagonal classes of the
> one-point extension at the identity"*, hence *"S-ring non-schurian **is** the one-point extension at
> `e` is non-schurian — §7.2's ticket, literally"*. **Both halves are false.** §8.4 states it in this
> doc's own words: **the S-ring is the ROOT closure only**; individualizing `e` and re-closing gives a
> *strictly finer* partition. **Shrikhande, measured: 3 basic sets, 4 extension fibres** — and those 4
> are exactly the `Aut_e`-orbits, so the extension is fibre-accurate while the S-ring is not.
> ⟹ the 729 are **root-deficiency** tickets (necessary, as re-derived above), **not** §7.2's
> *extension*-non-schurity ticket, which was never checked on this population. ⚠ §7.2's ticket is
> also only necessary, not sufficient — non-schurity can live entirely off-diagonal (`G ⊔ G`).
⚠ **Contrast the CFI population measured the same day** (§5's correction block): there the **root** was
non-schurian but every one-point **extension** was schurian, so the ticket was **UNPAID** and the 2-WL
result was worthless. Two different populations, opposite verdicts — do not conflate them.

**★ THE RESULT (2026-07-31, `probe_r1c.out`, wall 3300 s, summary printed — EXIT 0).**

| | measured | recorded population |
|---|---|---|
| connection sets tried | **57,014** | 66,888 |
| S-ring non-discrete | **52,378** | 62,147 |
| **S-ring NON-SCHURIAN** (= §7.2's ticket, PAID) | **465** | **729** |
| of those, E1/E2 instrumented | **462** (3 Aut-budget blown, each logged) | — |
| descent nodes visited | **56,811**, max depth **8** | — |
| **★ E1 — fibre-schurity failures at ANY node** | **0** | — |
| **★ E2 — nodes where fibre holds but FULL schurity fails** | **477** (462 inputs with a full-schurity failure) | — |

**▶ E2 IS ANSWERED, and it is a real finding.** Fibre-schurity survives at 477 nodes where **full**
schurity fails. ⟹ **the fibre hypothesis is load-bearing**, so the unrestricted *"extensions preserve
schurity"* is **not** a route to the target. This **measures** §4.5, which had only asserted it.
⚠ It does **not** touch §12.4's **R2** (per-family *separability*), which stays live.

**▶ E1 — no counterexample, on 64% of the population, at every node.** This is a real strengthening of
§6's row (which was **depth 1 only**): 462 sharp inputs, 56,811 descent nodes, to depth 8. **But it is
not the whole population** and must not be quoted as if it were:

- **465 of the recorded 729 sharp inputs (64%).** The shortfall is entirely three order-32 groups:
  `Z4^2xZ2` stopped at **2126/4000** sampled sets, and `Z8xZ4` / `Z16xZ2` were **not reached** before
  the 55-min deadline. Follow-ups:
  · ✅ **`Z16xZ2` completes in 61 s with 0 sharp inputs** — it contributes nothing to the 729.
  · ⛔ **The `Z4^2xZ2` re-run (`probe_r1c_tail.out`) added NO coverage** — see the process trap below.
  · `Z8xZ4` — run separately (`probe_r1c_z8xz4.out`).

> **⚠⚠ PROCESS TRAP — it cost a whole run, and it is not obvious (2026-07-31).** `sets_for` samples
> the capped groups with a **fixed seed** (`random.Random(12345)`), so the 4000 sets are the *same
> sequence in the same order* on every invocation. **Restarting a cut-off group therefore re-covers
> its PREFIX and adds nothing.** The `Z4^2xZ2` re-run processed 575 sets — a strict prefix of the
> main run's 2126 — reporting 78 sharp inputs, 16,308 nodes, **0 E1 failures, 83 E2 nodes**: all of it
> already inside the main run's coverage, and none of it additive. (It is a clean *consistency*
> re-run — same verdicts on the same inputs — and nothing more.) ⟹ **to extend a cut-off group you
> must OFFSET the sample**: `--skip=N` now does that (`--groups=Z4^2xZ2 --skip=2126`).
> ⚠ Its `wall: 33873s` line is also not compute time — the machine suspended mid-run and the
> wall-clock deadline fired on resume. Read the per-checkpoint timings, not the total.
- **77 of the 462 descents hit the 400-node budget**, so those inputs are covered only partially.
- **3 inputs were never instrumented** (automorphism search blew its `2e6` budget), all in `Z4^2xZ2`,
  each printed with its connection set.
- **12 groups are SAMPLED, not enumerated** (`CAP_SETS = 4000`) — `Z2^5` has 2¹⁴⁷ᐟ… (2,147,483,648)
  sets and is sampled at 4000, i.e. ~0.0002%. That cap predates this work (it is
  `probe_2wl_sring.CAP_SETS`) and it bounds *every* number ever quoted from this population,
  including the recorded 729.

**Why it costs what it costs — structural, not a bad constant.** `descend` recurses on one rep of
**every** cell, so the tree branches multiplicatively (node counts went 6k → 48k between checkpoints
once order ≥ 18 groups appeared). The other cost is stage 2 (`iso_exists` per basic-set pair) at
n = 24–32, run on every non-discrete S-ring. Two earlier attempts died on shell timeouts with **no
summary** (EXIT 124) because the wall deadline was checked only *between* groups; it is now checked
inside the connection-set loop, which is what made this run reportable.

**▶ To close R1c properly — four bounded steps, no research in any of them.**
1. **Finish `Z4^2xZ2` from its offset** — `python3 -u probe_r1c.py --groups=Z4^2xZ2 --skip=2126
   --wall=3000`. ⚠ **Without `--skip` this re-covers the prefix and adds nothing** (trap above).
2. **Finish `Z8xZ4`** — `--groups=Z8xZ4` (in flight as `probe_r1c_z8xz4.out`; `Z16xZ2` is already
   done and contributes 0).
3. **Re-run the 77 truncated descents** with a larger `node_budget` (they are partial coverage
   *within* an input, which the summary counts but does not identify — printing their connection sets
   would make this step targetable).
4. **Decide the sampling.** Either raise `CAP_SETS` on the 12 sampled groups or state the sampling as
   a permanent bound. ⚠ It bounds the recorded **729** just as much as it bounds this sweep.

Only after 1–4 does an E1 row belong in §6's ledger as a **population** result.

### 12.4 Candidate resolutions, ranked

| route | content | gap |
|---|---|---|
| **R1 triangle-type / `v`-profile** (most promising — it is what the measurement points at) | define a pair's `v`-profile `(X`-class`(a,v), X`-class`(v,b))`; the target becomes *two orbitals in one `X`-class have different `v`-profile distributions* | why must they differ? This is where the CAO hypothesis has to bite, and it is the one place it plausibly can — CAO is what forces the fibres to be full orbits, hence the profiles to be group-theoretically meaningful |
| **R2 separability** (the standard tool, and the right Lean pin) | if `X` is *separable* — every algebraic isomorphism is induced by a combinatorial one — the extension is schurian and the target follows | separability is **not** implied by fibre-schurity; it must be proved per class. ⟹ **carry it as a per-family certificate**, matching the project's existing obligation pattern |
| **R3 classification ladder** | free for schurian roots (§12.2) · S-rings over cyclic groups (schurian by classification) · families with known classical groups (forms graphs, Cameron — orbitals computable) · general = open | each rung is a separate piece of work; mirrors `KEY_scoping`'s tie-group ladder |
| **R4 ⛔ excluded** | coset transfer (circular, §4.1) · pure counting (structure constants only, §4.2) · bounded depth (not union-stable, §4.3) · full-schurity invariant (killed by `G ⊔ G`, §4.4) | — |

### 12.5 Honest assessment

Steps 1–2 are real, free, and formalizable now, and they reduce the problem to ≈1% of instances.
**Step 3 is a genuine open question of algebraic combinatorics** (schurity of one-point extensions
under a fibre hypothesis), not a lemma to be discharged by effort. The practical route is therefore
R2 + R3: pin the crux as a per-family certificate and prove it for the families that matter.

### 12.6 ▶▶ THE PLAN for route (B) — the mechanism track (2026-07-30, user-directed)

**What "the mechanism" means, and how much of it is already settled.** The question is *how
individualizing `v` changes the other cells' orbits, and whether 2-WL's classes coincide with that
change*. **The first half is DONE and formalized**: §3's fibring — individualizing `v ∈ D` changes
`C`'s orbits **only** by fibring `C` over the `K`-orbitals inside `D × C`, and **nothing else can
happen** (`CaoFibring.exists_row_transport` +
`sameOrbital_iff_sameStabOrbit_of_transport`). So the whole remaining question is the **second** half:

> **when does a 2-WL class properly contain ≥ 2 orbitals meeting `v`'s row?** (= `hsep` = §12.3)

**The organising fact for the plan.** The target is an *induction along the descent*, so its step is
applied where the input **arose from individualization** — a strictly wider class than "orbit
partitions of plain graphs", which is the only class ever swept. Every step below is chosen against
that.

| # | step | cost | what it DECIDES |
|---|---|---|---|
| **M1** ▶ **LIVE** (= §12.5a R1c) | **Run the step on its real input class, at a population that pays the entry ticket** (= the old §12.6(1)/§10.2, but *fixed* — see the ⚠ below) | hours | whether "no 2-WL counterexample" survives a population where §7.2's ticket is genuinely paid. **If it falls, route (B) ends** and §10.5's selector route (A) becomes the only path |
| **M2** ✅ **ANSWERED** | **Is the EXTENSION round count bounded?** ⚠ **RESTATED 2026-07-30** — see §12.3's convention box. The *total* count is **refuted** by any VT family of growing diameter (Johnson, measured ⌈diam/2⌉); only **term 2**, the rounds *after* coherent `X`, is the live quantity. Measured **constant 3** on every deficient root incl. Shrikhande □ `C₃`/`C₅`/`C₇` at diameters 3/4/5 | hours | pursue a **bounded-extension-round** theorem, or drop it. Still the only shape that is *both* union-stable (unlike bounded depth, §4.3) *and* formalizable. **▶ The falsifier to hunt: a deficiency that is inherently LONG-RANGE** — in a Cartesian product the fusion stays factor-local, which is why □`C_m` does not refute it |
| **M3** ✅ **DONE** (results below) | **★ Instrument the FEEDBACK LOOP, not the round number** — the actual mechanism ask, and new work | days | supplies R1's missing *"why must the `v`-profile distributions differ?"* |
| **M4** | **The coupling construction** (§10.3) — build an object with group-change and deficiency at the **same** cell pair | open-ended | kills the track cheaply, or its principled failure *is* the mechanism. Run **in parallel with M3** — same question from opposite sides |
| **M5** | **Lean: reuse the CC substrate that already exists** (see below — it is not referenced anywhere in this plan and should be) | days | turns R2's "carry a per-family certificate" from a plan into a deliverable |
| **M6** ▶ partly subsumed by `CaoRound` §1 (`PairInvariantAt`/`step2_closure`) | the group-identification bridge (`IsColAut` of a refined colouring ↔ the point stabilizer) | hours | needed by **any** consumer of `CaoFibring`, at either WL level |

**⚠ M1 — the measurement is not what §10.2 says it is.** `probe_cao_induction.py`'s
sharp-Cayley section iterates **8 groups of order 16 only** and `break`s at `hits > 3` per group ⟹ at
most ~24 sharp inputs, **not** "the 729 non-schurian S-rings" (which came from 38 groups of orders
8–32). Remove the cap, extend to the full population, and **log what was skipped** (§9's discipline —
a silent cap reads as full coverage). Until then the "729" figure describes the *hunt*, not the
*instrumentation*.

**★ M3 — what to actually record.** §12.3's round-1 barrier is proved: coherence makes the round-1
count of `(v,u)` an intersection number, identical across the class, so **the base point learns
nothing directly**; the marking must travel — a far pair `(a,b)` acquires its triangle type
`(X`-class`(a,v), X`-class`(v,b))`, that splits far classes, and only their feedback reaches `(v,u)`.
Measured round 3 / 3 / 4 confirms it. **Nobody has measured *which* far split does the work.** Per
round, record: (a) how many orbital-fusions remain; (b) which triangle types were newly created;
(c) the **minimal cause chain** — the specific far class whose split, on removal, leaves the target
pair fused. Output is the mechanism *in the form a proof consumes*: "the marking travels via `X`, and
`X` is forced to exist because `Y`". This is the one step that attacks the crux rather than
characterising it.

#### ★★ M3 — FIRST RESULT (2026-07-30, `probe_cao_cause.py`): the cause chain is UNIFORM

Built and run on every deficient root on record (Shrikhande, `net(Z₄)`, Chang-2 — **7 fused classes**,
all counted from the coherent `X`). The instrument extracts, at the round `r*` where `(v,u)` and
`(v,w)` first separate, the **triangle types** `(c1, c2) = (class of (v,x), class of (x,u))` whose
multiplicity differs — literally §12.3's object — then traces each witness class to its **birth
round** and recursively explains the later-born one. **Every chain has the same shape and the same
depth 3:**

```
r0   v's flag           — the only new information in the extension
r1   FAR classes split  — witness = a triangle type of two r0 classes, ≥1 of them v-ROW / v-COL
r2   deeper FAR split   — witness = a triangle type of two r1 FAR classes
r3   THE TARGET SEPARATES — witness = (v-ROW class born r0,  FAR class born r2)
```

**Three things this pins down, and they are what a proof needs.**
1. **The barrier is confirmed constructively, not just by counting**: the target pair is never
   separated by anything on `v`'s row alone — the returning half of every final witness is a **far**
   class, and one that did not exist before round 2.
2. **The final witness is always the SAME SHAPE** — `(v-ROW born r0, FAR born r2)`. Never two far
   classes, never two `v`-row classes. So the feedback returns through **exactly one** twice-refined
   far class, and R1's *"two orbitals in one `X`-class have different `v`-profile distributions"* is
   the right statement: the profile that differs is a count of one triangle type.
3. **The chain always grounds at `v`'s flag** in 3 steps, on every witness, at every diameter tested
   (§12.3's convention box: Shrikhande □ `C_m` also separates at round 3, diameters 3–5).

#### ★★ M3 — FOLLOW-UP RESULTS (`probe_cao_cause2.py`): the law holds, the "minimal cause" does not

**(b) The law survives beyond diameter 2 — POSITIVE.** Extended to the deficient **Shrikhande □ `C_m`**
family (Doob shape, diameters 3 and 4) and re-measured on `net(Z₄)` (**diameter 4**, not 2 as an
earlier version of §12.3's box claimed). **11 fused classes across 5 objects at diameters 2/2/3/4/4:
every one separates at round 3, and every final witness is `(v-ROW born r0, FAR born r2)`.** Depth and
witness shape are *not* artifacts of diameter-2 SRGs.

**(a) The ablation — NEGATIVE, and it retracts a framing this doc proposed.** M3 was scoped to find
*"the specific far class whose split, on removal, leaves the target pair fused."* **There is no such
class.** For every one of the 11 fused classes, the number of single class-merges at round `r*-1` that
kill the separation is **0**, and a greedy merge sequence must collapse *almost the entire* partition
before separation dies (21 of 22 classes, 60/61, 130/157, 107/110, 281/286, 285/286, …). The
separation is **massively over-determined**: 6–40 differing triangle types per witness, no one of them
necessary.

⟹ **the instrument's "minimal cause chain" is one path among many, not a minimal cause** — the
max-|Δ| pick is a heuristic. The depth-3 *structure* is real and reproducible; the *uniqueness* of the
deciding class is not, and was my inference rather than a measurement.

#### ★★★ M3 → R1: the uniform depth 3 is FORCED — `round2_barrier` (proved, `CaoRound.lean` §4)

The follow-ups left one thing unexplained: *why is the separation round always exactly 3?* It is not a
coincidence. **Rounds 1 and 2 are both provably blind on `v`'s row**, so round 3 is the earliest that
can see anything — and 3 is what all 11 measurements give.

**The mechanism, now explicit and machine-checked.** One round of the individualized configuration
gives each pair exactly its **triangle type through the base point**,
`zAug f v a b = (f a b, f a v, f v b)` — *measured to be exactly the round-1 partition on 5/5 objects*
(`probe_cao_round2.py`; the transpose axiom also holds 5/5). And on `v`'s row that augmentation adds
**nothing independent**: the intermediate point `x` contributes `(X v x, X v v, X v x)` and
`(X x u, X x v, X v u)`, and the transpose axiom makes `X x v = T(X v x)` — so the entire round-2
signature is the image of the round-**0** signature under one fixed map `Φ`, and coherence equates it
across an `X`-class.

| landed | content |
|---|---|
| `Transposable` / `zAug` | the transpose axiom, and the round-1 information made explicit |
| **`sig_zAug_row_eq`** | the barrier core: `sig (zAug f v) v u = sig (zAug f v) v w` whenever `X v u = X v w` |
| `sig_factor` | a colouring factoring through `zAug` has its signature the `Ψ`-image of `zAug`'s |
| **`round2_barrier`** | ⟹ **any** colouring factoring through the triangle-type-through-`v` data still fails to separate `v`'s row |

⟹ with `round1_barrier`: **separation cannot occur before round 3.** The crux is not merely non-local
(§12.3) — it needs the *third* round, i.e. the feedback from far pairs that have themselves been
refined by a count `X` does not determine.

**✅ AND THE LAST HYPOTHESIS IS NOW DISCHARGED (2026-07-31, `CaoRound.lean` §5).** `round2_barrier`
carried `hg` — that the colouring factors through `zAug` — which was *measured* (5/5) but not proved.
It is now proved **from the coherent-configuration axioms and nothing else**:

| landed | content |
|---|---|
| `DiagSep` | the diagonal axiom at `v` (`X a v = X v v ⟹ a = v`), in the two forms used |
| `sig_split` / `sig_ext0_split` | the base-point split, general form (the `a = v` cases were §3's) |
| **`sig_ext0_congr`** | ★ the round-1 **signature** is determined by `zAug`: the `x = v` term is `(X a v, X v b)` outright, and the far part is `sig X a b` minus that term — coherence-determined |
| `flag_left` / `flag_right` | the base-point flags are recoverable from `zAug` (this is the *only* use of the diagonal axiom) |
| `roundBy_ext0_congr` | the whole round-1 **colour**, not just its signature |
| **`exists_factor_roundBy_ext0`** | ★★ `hg`, as a genuine factorization |
| **`round2_barrier_real`** | ★★★ **the round-2 barrier with NO factorization hypothesis** |

⟹ **"separation cannot occur before round 3" is now unconditional on the real object**, from
`{Coherent, Transposable, DiagSep}` — all three literally the CC axioms, all three present in
`CoherentConfig.lean` (`inter_card_eq` / `transpose_eq` / `diag_eq`). The measured uniform depth 3
(11/11) is *explained*, not just observed.

#### ★★★ "Must it occur AT round 3?" — NO, and the method cannot say so (2026-07-31)

Asked directly, and worth recording because the answer is structural, not a gap in effort.

**1. It is strictly stronger than the crux.** The crux says separation happens *eventually* (at the
fixpoint); *"at round 3"* says it happens **and** by round 3. Proving it proves the open problem plus a
round bound, so it cannot follow from the barrier.

**2. The method is one-directional by construction.** Every step of §§3–5 shows two objects are
**equal** — which is exactly what coherence hands you, since coherence *is* the statement that certain
counts are determined. Separation needs an **inequality**, and no "these counts are determined"
statement produces one. This is the dual of §4.2's *"`k`-WL computes only structure constants"*.

**3. Where the chain breaks is the useful part.** The barrier propagates while the data feeding `v`'s
row is coherence-determined, and stops at round 3 because the round-2 far colours carry the **triple
count**, which coherence does *not* fix. So the barrier **localizes the freedom** — it proves the only
thing that *can* separate the row is that count. But "there is room" ≠ "the room is used".

**✅ WHAT IS PROVABLE — the conditional converse, LANDED (`CaoRound.lean` §6).**

| landed | content |
|---|---|
| **`triCount`** | the **triangle count** `#{x : (f a x, f x b) = q}` (+ `triCount_eq_card`) — R1's object, named |
| `roundBy_eq_of_sig_eq` | a round cannot separate what the signature does not (no hypothesis on `enc`) |
| **`roundBy_ne_iff_sig_ne`** | for a *faithful* re-encoding, a round separates equal-coloured pairs **exactly when** their signatures differ |
| `sig_ne_iff_exists_triCount_ne` | signatures differ **iff** some triangle type has a different count |
| `round2_row_colour_eq` | the colour-level form of §§3–5: through round 2 the row colours themselves agree |
| **`round3_separates_iff_triCount_ne`** | ★★★ **THE CRUX, REDUCED TO ONE INEQUALITY** |

⟹ **round 3 separates `iff` some triangle type of the round-2 colouring has a different count at
`(v,u)` than at `(v,w)`.** Everything **up to round 3** — the rounds, the row, the closure's first
three steps — is discharged; what remains at round 3 is one inequality between finite explicit counts.
**That is the object the per-family certificate (§12.4 R2/R3) should be pinned to** — and the honest
form of "must it occur at round 3": *not unconditionally, but exactly when `triCount` differs.*

> **⚠⚠ DIRECTION CORRECTION (2026-07-31) — an earlier version of this paragraph and of §0's box said
> "rounds, the row and the closure are **fully** discharged; what remains is one inequality."** That
> is wrong in one direction and must not be inherited. Refinement is **monotone**, so
> `triCount` differs ⟹ round 3 separates ⟹ the closure separates ⟹ the crux holds *on that pair*.
> **The converse fails:** `triCount` agreement at round 3 leaves round 4+ free to separate the row,
> because the round-3 colours of **far** pairs keep refining and nothing here bounds them. So the
> `triCount` statement is a **sufficient pin, strictly stronger than the crux** — which is exactly
> what the box above this one says about *"must it occur AT round 3"*, stated there in prose and
> contradicted here in the summary. Two consequences: (i) a family where `triCount` agrees is **not**
> a counterexample to CAO propagation — it is a family whose certificate needs a different pin;
> (ii) R1f aims at the strengthened statement, and if that resists, the crux itself (separation at the
> **fixpoint**) is still open and currently has no instrument at all.

**▶ What this changes for R1 — and it is a sharpening, not a setback.** R1 asks *"why must two orbitals
in one `X`-class have different `v`-profile distributions?"* The ablation says they differ in **many
coordinates at once**, none load-bearing. So a proof should **not** try to construct a distinguished
witness class — that object does not exist. It should target the **whole profile vector**: an
aggregate or rank argument showing that agreement across all coordinates would force a coincidence the
CAO hypothesis forbids. Over-determination is *evidence the statement is robustly true* and a
redirection of how to prove it. ⚠ Note the constraint from §4.2: `k`-WL sees only structure constants,
so the aggregate argument must conclude *separation*, never *"an automorphism exists"*.

**★ M5 — the substrate is already built and gated, and this plan never mentions it.**
`ChainDescent/CoherentConfig.lean` (in `build.sh`, axiom-clean) carries: **`IsPointExtension X T Y`**
(the coarsest coherent fission with `T` singled out — *the object of Step 3*), the **construction**
`pointExtension` via `pairStep`/`pairIter`/`stableSetoid` with the universal property discharged
(`isPointExtension_pointExtension`, `exists_isPointExtension`, `isPointExtension_unique`),
`AlgIso`/`AlgIso.InducedBy`, **`Separable`/`SeparablePointed`**, **`ExtensionSeparable`** (= R2's
statement, verbatim), and **`Theorem41Statement`** — Ponomarenko arXiv:2006.13592 Thm 4.1 as a
citation-carrier, whose hypotheses a probe found **hold precisely on the one-point extension and fail
on the residue itself**. §12.4 ranks R2 as "must be proved per class" without noting that a cited
route to it is already in-build. ⚠ Two honest gaps before it closes anything: **`Separable ⟹
schurian`** (standard, must be cited or proved — it is what converts R2 into the target) and the
**D0/T4 modelling seam** (`CoherentConfig` is abstract; connecting it to graphs is the faithfulness
obligation W2 already tracks).

**▶ Order:** M1 + M2 first (cheap, and M1 can end the track). Then M3 and M4 in parallel — they are
the same question from both sides. M5 is the Lean deliverable and can start once M1 has not falsified.
M6 anytime.

**▶ If 2-WL falls (M1 turns up a counterexample).** Re-run M1/M2 at **3-WL** before concluding
anything: the same measurements decide whether this is a ladder that continues or whether refiner
strength cannot fix the design at all — and only the second warrants the structural change. ⚠ Note
§0.0's negative branch: a "fails at every `k`" witness has **no candidate** today, because §5's
self-limiting lesson excludes every standard unbounded-WL family from the CAO hypothesis.

> *(The former §12.6, "the two measurements that would most inform Step 3", is absorbed into §12.6's
> **M1** and **M2** above — with the correction that the sharp-Cayley instrumentation does **not**
> currently cover the 729. Old cross-references to "§12.6(1)/(2)" resolve to M1/M2.)*

---

## 13. ▶▶ THE CONVERSION GAP — what this track would cost to cash (scoping, 2026-07-31)

**The gap, stated once.** Every result in this doc is about a **2-WL** closure. The `Tinhofer` in
`build.sh` is a **1-WL** predicate. So **nothing landed here can affect the built object until the
step the predicate is stated over is swapped** — and *whether that swap is affordable* is a separate
question from *whether the crux is true*. It is cheaper to answer, and it gates the value of §12.5a.
**This section is the scoping; it is not a decision to do the swap.**

### 13.1 ⚠ "Swap the refiner" was the wrong description — three docs said it

`00-START-HERE.md` §2, `chain-descent-remaining-work.md` §1T and this doc's §0.0 all described the
design change as *"swap the refiner 1-WL → 2-WL, `n²` → `n³` per round"*. **Source-checked and
corrected:**

```
Tinhofer / TinhoferPath / CellSingleOrbit   are stated over   Deepen.step   ONLY
Deepen.step adj χ v = Refine.warmRefineVec adj (Descend.indivOne χ v)      (DeepenSupply.lean:147)
```

`Deepen.step` is the **supply-internal** deepening step. The descent's own refiner — `Refine`'s
`warmRefineVec` as consumed by `Descend.descend` — the `Colouring` type, `Select`, and
`Publication.canonForm?`'s object are **not** mentioned by `Tinhofer` and would **not** change. The
`n² → n³` framing describes a change to the canonizer that this predicate never asked for.

⚠ **It is not free either, and the earlier framing hid that too, in the other direction.**
`DeepenGuard.CertPath` also calls `step` (`DeepenGuard.lean:138`), `orbKeyG` is defined from
`CertPath`, and **`recordKey := pairKey holKeyFast (orbKeyG guardSupply)` is the record object's key**.
So the swap *does* reach `Publication.canonForm?` — through the key, not through the refiner.

### 13.2 The blast radius, measured

| measure | value | how |
|---|---|---|
| modules mentioning `Deepen.step` | **13** — `DeepenTinhofer` (44 refs), `DeepenGuard` (27), `DeepenKey` (20), `KeyComplete` (9), `DeepenLocated` (9), `PerformanceTest` (8), `DeepenExact` (7), `DeepenCertified` (7), `Regression` (5), `DeepenSupply` (3), `DeepenRef` (3, parked), `DeepenTransport` (1), `DeepenCrux` (1) | grep |
| **definitions** that call it | **~20** — `deepen`, `replay`, `deepenGens`, `TinhoferPath`, `Tinhofer`, `cidCell`, `CertPath`, `CertifiedG`, `certPathCost`, `orbKeyG`, `CertifiedPath`, `Certified`, `GateAt`, `leafOf`, `readKey`, `Refines`, `rawKey`, … | awk over `def` blocks |
| places that **unfold** it | **3**, all inside its own cluster — `DeepenTransport.lean:188`, `DeepenTinhofer.lean:148`, `:181` | grep `unfold step` |
| modules **outside** the cluster | **0** (`Descend`, `Refine`, `Select`, `Force`, `RecordKey`, `RecordCost`, `Publication` never mention it) | grep |

### 13.3 ★ THE FINDING THAT MAKES THIS CHEAP — `step` is used through a **4-lemma interface**

Only three proofs ever look inside `step`. Every other proof in the 13 modules goes through these:

| lemma | content | where |
|---|---|---|
| `step_transport` / `step_aut` / `step_isColAut` / `step_rerelate` | **equivariance** — an automorphism transports one step | `DeepenTransport:185`, `DeepenTinhofer:54/65/77` |
| `step_refines` | the step only **splits** the parent colouring | `DeepenTinhofer:146` |
| `step_indiv_singleton` | the individualized vertex is a **singleton** afterwards | `DeepenTinhofer:178` |
| `step_preserves_singleton` | a singleton **stays** a singleton (corollary of `step_refines`) | `DeepenTinhofer:169` |

⟹ **the swap is an interface swap, not a rewrite.** Abstract `step` to a parameter carrying those
four properties, make the ~20 definitions step-generic, and the 1-WL step becomes one instance and a
2-WL step another. The downstream proofs are re-usable **verbatim** — they never see the refiner.

★ And **`CaoRound` already supplies the hard half for the 2-WL instance**: `pairInvariantAt_ext0` +
`pairInvariantAt_iterRoundBy` are the equivariance of the individualized 2-WL closure, and
`step2_closure` says its induced vertex colouring `u ↦ f v u` has level sets **exactly** the
`K_v`-orbits — which is `CellSingleOrbit` for that step, given `hsep`. That is the whole point of the
track, arriving in the right shape.

### 13.4 The cost side — and a pre-existing `②` hole it surfaced

`certPathCost` (`DeepenGuard.lean:329`) bills, per level, `n⁴` (the reachability test) **plus one
supply call** — and **does not bill `step` at all**. `orbKeyG`'s read term is likewise a **declared
flat `n⁴`** covering `readKey ∘ leafOf`, where `leafOf` runs an entire `n`-level deepening. Two
consequences, and they point opposite ways:

- **For the swap: no current cost theorem changes.** `certPathCost_le`, `keyCost_orbKeyG_le`,
  `descentCostS_selNode_recordKey_le`, `costConst = 57` (53 pre-`stepCost`) / `costDeg = 13` are all statements about ⛔ **SUPERSEDED 2026-08-08**: `Publication`'s numerals are now `RecordDeepenCell.costConst = 69` / `costDeg = 13` at the cell-indexed object (degree unchanged; the constant absorbs per-cell supply billing + the newly-billed deepen guard). `RecordKey`'s 57 still describes `RecordKey`'s own object.
  *declared* costs that never mention `step`. A 2-WL step would leave every one of them true and
  every proof unchanged.
- **⚠ Which is exactly the problem.** That is the project's own recorded failure mode — *"the key
  declared a flat `n⁴` that was true by definition and therefore priced nothing"*
  (`remaining-work` §1T T2) — recurring one level over: the guard's *recursion* was billed
  (2026-07-27) but the *read* it delegates was not. Today the omission is `warmRefineVec` per level;
  with a 2-WL step it grows by roughly a factor of `n`. **So `②` would not notice the swap, and that
  is a defect of `②`, not a licence.** ▶ Worth fixing regardless of this track: it is a `RecordCost`
  item, not a CAO item.

### 13.5 The scoping plan (S1–S5) — hours, not weeks, and each is separately abandonable

| # | step | cost | acceptance |
|---|---|---|---|
| **S1** ✅ **DONE (python) 2026-07-31 — `probe_step2.py`** | **Write the 2-WL step concretely.** `step2 adj χ v` = individualize `v`, close under 2-WL (`c'(a,b) = (c(a,b), {{(c(a,x), c(x,b))}}_x)` — literally `CaoRound.roundBy`), read back the vertex colouring `(diag u, c(v,u), c(u,v))`. ▶ The **Lean** half (return `ColData`, §8.3 placement) is still to do | done (py) | ✅ **CALIBRATED against doc §0.0**, `python3 -u probe_step2.py --calibrate`: `net(Z₄)` n=28, `\|Aut\|=192`, from the EXACT orbit partition — **1-WL → 5 cells, 2 MIXED; 2-WL → 7 cells, 0 MIXED**, matching the 7 `Aut_v`-orbits exactly. The recorded figures reproduce |
| **S2** | **Prove the four interface lemmas for `step2`** | ~a day | equivariance from `pairInvariantAt_iterRoundBy`; refines/singleton are structural. ⚠ trap #1: never return `… → Colouring n`; `ColData` only |
| **S3** | **Abstract the interface** — make `deepen`/`replay`/`TinhoferPath`/`CertPath`/`leafOf`/… take the step as a parameter with the four properties | ~a day | gate stays EXIT 0 with the 1-WL instance plugged in, and **`Regression` §18/§19 numbers are unchanged** (`G8` still FLAGS under `holKeyFast`, ANSWERS under `recordKey`) |
| **S4** | **Instantiate at `step2` and measure** — not on the gate; a scratch `#eval` on the m=8 witness and on `net(Z₄)` | hours | does `CertPath` certify where it previously failed? This is the first evidence the swap *buys* anything |
| **S5** | **Cost re-model** (§13.4) — bill the read and the step | open | `②` becomes sensitive to the swap; do it before any claim that the swap is "a direct polynomial increase" |

**⛔ Do not start S3 before S1/S2.** The abstraction is only justified if a second instance exists;
otherwise it is churn on 13 modules for one implementation.

**▶ The decision S1–S4 informs.** *"Is the 2-WL swap affordable?"* — separate from, and cheaper than,
*"is the crux true?"* If S4 shows the swap does not fix the recorded obstruction, the track ends
without anyone attacking the crux. If it does, §12.5a becomes worth its cost and the track is a
candidate for promotion (§0.0: promotion needs viability, and the competitors — a residue-cannot-exist
proof, or force at every descent step — are still unranked).

### 13.6 ★★★ S4 RESULT (2026-07-31) — and it INVERTS §13.1's conclusion

**⚠⚠ §13.1 above is right about the PREDICATE and wrong about the PAYOFF. Read this before acting on
it.** `Tinhofer` is indeed stated over `Deepen.step` alone — but the benefit measured at the recorded
obstruction comes from swapping the **descent's refiner**, which §13.1 said would not need to change.
Both halves are measured (`probe_step2.py`, calibrated against §0.0's `net(Z₄)` figures first; raw
output `probe_step2.out` + `probe_step2_nodes.out`).

**(a) Swapping `Deepen.step` alone buys NOTHING here — measured.** The A/B ran the harvest at the
1-WL step and at the 2-WL step on the two nodes where the 1-WL harvest certified nothing:

| node | cells | 1-WL harvest | 2-WL harvest |
|---|---|---|---|
| m=8 twisted **root** | 32, 24 | ✗ ✗ (480 / 264 gens, 5 / 6 levels) | ✗ ✗ (**480 / 264 gens, 5 / 6 levels — identical**) |
| **`root/id1/id9`** (carries the `\|C\|=16` cell) | 4,4,16,4,4,8,4,8 | all ✗ | all ✗, **every gen count and level count identical** |

Not merely "also fails" — *the same object*. Diagnosis (iii): along the harvest's own deepening path
from the `|C| = 16` cell, the 2-WL step produces **partitions identical to the 1-WL step at every
level, on 4/4 anchors**. Nothing at that depth is left for a stronger refiner to split. (⚠ 2-WL is
*not* globally equal to 1-WL on this graph — a random-descent sweep found it strictly finer at 9 of
59 colourings, all shallow. It coincides exactly where the harvest works.)

**(b) Why the harvest was right to fail — and why route (A) could not have helped.** Measured against
the **exact** automorphism group (`all_isos`, not an oracle): at the root `|Aut_χ| = 512` and **both**
cells are mixed (32 → 2 orbits, 24 → 3); at `root/id1/id9` `|Aut_χ| = 64` and **all eight** cells are
mixed. ⟹ **no cell at either node is a single orbit**, so no supply and no selector could certify one:
the harvest's `✗` is **correct, not incomplete**, and these are **force-domain** nodes (mixed cells —
`forceBy_no_narrowing_on_orbit` does *not* forbid force there). ⚠ **This corrects §10.5's first
write-up**, which called the two failures "supply incompleteness". They are not.
⚠ **And these are not DUAL §2.1's node.** That one is *one equivariant force-key refinement* below the
root and its `|C| = 16` cell **is** one true orbit; these two are 1-WL descent nodes that merely share
the `|C| = 16` shape. Reproducing DUAL's node needs the force key — **that is the outstanding S4
target**, and it is the one that tests CAO *propagation* rather than the base case.

**(c) ★★★ But the full refiner swap recovers the orbit partition EXACTLY — at both nodes.**

| node | 1-WL (what the descent builds) | **2-WL closure of the same colouring** | exact orbits |
|---|---|---|---|
| m=8 twisted **root** | 2 cells, **2 mixed** | **5 cells, 0 mixed** | 5 classes |
| **`root/id1/id9`** | 8 cells, **8 mixed** | **16 cells, 0 mixed** | 20 classes |

⟹ **on this witness the consume failure is entirely a refiner-strength failure, and 2-WL removes it
completely** — both nodes go from *"no cell is an orbit"* (force's domain) to *"every cell is an
orbit"* (consume's domain, where the harvest's re-relating induction is exactly what applies).

**▶ What this changes.**
1. **The swap that pays is the DESCENT's refiner, not `Deepen.step`.** §13.1's "the refiner does not
   change" is right about what `Tinhofer` *mentions* and wrong about what the payoff *needs*. The
   original three-doc framing ("swap the refiner, `n²` → `n³`") had the target right; what it got
   wrong was only the implication that `Tinhofer` alone forces it. **The two swaps are different
   projects.** §13.2/§13.3's cheap 4-lemma interface finding applies to the `step` half; the refiner
   half is the expensive one — it moves `Refine`, `Descend`'s cost model, `costDeg`, and every
   `Regression`/`PerformanceTest` number — and is **not yet scoped.**
2. **This is evidence about §0.0's scope limit 1 (the BASE case), not about propagation.** These nodes
   are not CAO starts — 1-WL from uniform gives 2 cells against 5 orbit classes — so the crux does not
   apply to them. What is measured is *"2-WL computes the orbit partition of this input"*, which
   limit 1 flags as false in general (rigid multipedes) and is **true here**. It raises the track's
   viability without touching the crux.
3. ⚠ **It does not contradict §5's "CFI is a dead falsifier habitat".** §5 is about CAO *propagation
   from a CAO start*, where CFI propagates even at 1-WL. This is about **reaching** a CAO start at
   all. Two different statements about the same graphs — worth keeping straight, because §0.0's
   motivating exhibit (m=8) lives in §5's "dead" habitat and nobody had connected them.

---

## 14. ★★ THE ANATOMY OF A FAILURE, AND THE ARITY LADDER ABOVE IT (added 2026-08-01)

**What this section is for.** §3 states the coupling principle abstractly; this section exhibits it
**constructively at the smallest witness**, which turns out to (i) kill a natural-looking proof route
before anyone spends a session on it (§14.2), and (ii) yield a **falsifier filter** for §10 item 3 that
is cheaper than sweeping more families (§14.4), and (iii) record the **path-condensation lead**, what
it hands the crux, and **why it closes** (**§14.5**, raised and closed 2026-08-05 — verdict in
**§14.5e**). §14.1–§14.4 are measured by
**`scratchpad/probe_cao_anatomy.py`** (clean-room machinery of §8.1, ~22 s; output
`probe_cao_anatomy.out`); **§14.5 has its own probe list** — see its header.

### 14.1 ★ The far cell's split is a PULLBACK of the exposed shape's PAIR-orbits

Put the two `SRG(16,6,2,2)` graphs side by side. **1-WL cannot tell them apart at any parameter**, and
both give cells `[1, 6, 9]` after individualizing — one splits, one does not.

| | Shrikhande — **CAO fails** | rook 4×4 — **CAO propagates** |
|---|---|---|
| shape induced on `N(v)` | **one hexagon** | **two triangles** |
| degrees inside `N(v)` | 2,2,2,2,2,2 | 2,2,2,2,2,2 |
| `\|Aut_v\|` | **12** = `D₆` | **72** = `S₃≀S₂` |
| `Aut_v` transitive on `N(v)` | yes | yes |
| `Aut_v` orbits on **pairs** in `N(v)` | **6 edge + 6 + 3** | **6 edge + 9** |
| the 9 far vertices attach to | 6 edge-pairs **and** 3 antipodal | all 9 across-triangle pairs |
| far cell | 1-WL `[9]`, orbits **`[3,6]`** | 1-WL `[9]`, orbits **`[9]`** |

**The mechanism.** Individualizing `v` injects no new fact; it **exposes a shape** — the graph induced
on `N(v)` — which `Aut_v` must now preserve. Here `Aut_v` *is* that shape's symmetry group: it embeds
(measured: the attachment map far-vertex ↦ its pair of common neighbours with `v` is a **bijection**,
so fixing `N(v)` pointwise fixes everything) and the orders match, 12 = `|D₆|`, 72 = `|S₃≀S₂|`.
Since `µ = 2`, every far vertex **is the address of a pair** inside `N(v)`. Therefore

> **the far cell's orbit partition is the pullback, along the attachment map, of `Aut_v`'s orbits on
> the pairs of the exposed shape.** The group is transitive on the shape's *points* and not on its
> *pairs* — that gap is the whole failure.

The numbers are the shape's: a hexagon has exactly **3** antipodal pairs and **6** edges. In the rook
all 9 attachments land in one pair-orbit, so there is nothing to split.

> ### ⟹ THE 1-WL BLIND SPOT IN ONE LINE
> **A 2-regular graph on 6 vertices is either a hexagon or two triangles, and no counting of
> neighbours can tell which.** `λ = 2` tells 1-WL that `N(v)` is 2-regular and nothing further.

This is §3's coupling principle made concrete: the group-change and the deficiency are here the *same
fact about the same cell pair*, which is why the witness is so small.

### 14.2 ⛔ STEER — "mixed must touch mixed, so the chain leads back to `v`" — premise TRUE, inference UNSOUND

A natural route (a reader reconstructed it independently): *a cell can only be mixed if it touches a
mixed cell, or 1-WL would split it; a chain of mixed cells not involving `v` would already apply
before individualization, contradicting the CAO start; so the chain must reach `v` — whose cell is a
singleton, hence pure. Contradiction.*

**⚠ Do not attack the premise — it is measured TRUE.** Over Shrikhande / Chang-2 / `net(Z₄)` at depth
≤ 2 (rook 4×4 and `T8` have no mixed cell at all): **14 mixed cells, 0 with no mixed support.**

**The inference fails on well-foundedness: the support is CIRCULAR.**
- **Shrikhande**: the mixed cell is **self-adjacent** — it is its own support.
- **`net(Z₄)`**: bipartite, so no cell is self-adjacent — and its **two mixed cells support each
  other**. A closed 2-cycle. `v`'s singleton is pure and is never needed.

⟹ **the mixed set is closed under "is supported by", so no chain ever bottoms out at `v`.** Any
argument of the form *"trace the mixedness back to the individualized vertex"* dies here.

⚠ The local twin fails too: *"if `u, w` have all their neighbours in single-orbit cells they are
interchangeable"* is inapplicable, because where the failure lives the shared cell is **itself** mixed.
Measured in Shrikhande — by **orbit** the two are genuinely different (3-piece: 4 nbrs in the 6-piece,
0 in its own; 6-piece: 2 and 2), while by **cell** they are identical (`{N(v): 2, own cell: 4}`).
The distinction is real and invisible, and what hides it is the very cell you would need already split.

### 14.3 The distinguisher is a RELATION, not a property

Measured, 9/9 and no shared value: **"are `v`'s two common neighbours with `u` adjacent to each
other?"** — 0 edges for the 3-orbit, 1 edge for the 6-orbit.

- It **exists at the root but says nothing there**: by vertex-transitivity every vertex has 3
  non-neighbours of one type and 6 of the other. **Individualization converts a uniform fact into a
  partition** — which is the precise sense in which "the reason leads back to `v`".
- It is **invisible to 1-WL** because both types have 2 neighbours in the (pure) `N(v)` cell; the fact
  lives on the **pair** `(x, y)`, and vertex colours are exactly the projection that discards it.

⟹ the concrete form of §12.3's *"the marking must leave `v` and come back"* and of `witness_ne_base`:
the information is born inside `N(v)` as a relation between two of `v`'s neighbours, and no vertex
holds it.

### 14.4 ★★ THE ARITY LADDER — the falsifier design one rung up, and the obstruction to it

The mechanism is **not 2-WL-specific**; it is an arity ladder, and it names what a 2-WL counterexample
would have to be.

| | the 1-WL failure | what a 2-WL failure needs |
|---|---|---|
| local group transitive on | points of `N(v)` | points **and pairs** |
| …but not on | **pairs** | **triples** |
| far vertices addressed by | pairs (`µ = 2`) | triples (`µ = 3`) |
| the blindness required | both shapes 2-regular | both triple-orbits share all pair statistics |

**The canonical level-up object exists** — measured: `A₅ ≅ PSL(2,5)` on 6 points has orbits on pairs
`[15]` (2-transitive) and orbits on triples **`[10, 10]`**. Exactly hexagon-vs-two-triangles one rung
up: the points are interchangeable, *every pair* is interchangeable, the triples are not.

> ### ⛔ THE OBSTRUCTION — why rung 2 is not a re-run of rung 1
> A group is **2-closed iff it is the automorphism group of an edge-coloured graph**. A 2-transitive
> group's only orbitals are `{diagonal, rest}`, so its **2-closure is the full symmetric group**.
> ⟹ **no binary structure on the cell can ever expose such a group.** Brute-forced over **all 32,768
> graphs on 6 vertices: 0** have a 2-transitive-but-not-`S₆` automorphism group (`--closure`).
>
> ★★ **AND IT IS A ONE-LINE PROOF AT EVERY DEGREE, not a fact about degree 6 (2026-08-05).** If
> `Aut(G)` is 2-transitive then for any two off-diagonal pairs some automorphism carries one to the
> other, so **all** off-diagonal pairs have the same adjacency ⟹ `G` is complete or empty ⟹
> `Aut(G) = Sym`. Verbatim the same for edge-coloured graphs (all off-diagonal pairs get one colour).
> ⟹ the brute force above is a **special case**, and the obstruction holds at **every cell size**.
> Confirmed on the canonical candidate (`scratchpad/probe_arity_ladder.py`): `A₅ = PSL(2,5)` on 6
> points, `|G| = 60`, orbits on points `[6]` / pairs `[15]` / triples `[10, 10]`, orbitals `[6, 30]`
> — **one** non-diagonal orbital — and **2-closure = 720 = |S₆|**.

⟹ at 1-WL the deficiency could hide **inside** the cell — hexagon-vs-two-triangles is a plain graph on
`N(v)` that 1-WL merely failed to read. **At 2-WL that route is closed by definition**: the
distinguishing structure cannot live on the cell at all, and must be carried by *other* vertices
attaching to **triples**. ⟹ **the search leaves graphs for designs / incidence structures.**

⚠ **And the naive gadget dies immediately**, which is the design tension in miniature: those carriers
are themselves vertices, so the closure colours `(carrier, point)` and `(carrier, carrier)` and reads
the triple system back out. Measured for `A₅`'s two classes — within A `{1: 60, 2: 30}`, within B
`{1: 60, 2: 30}`, across `{0: 10, 1: 30, 2: 60}` — **separated by `|T ∩ T'|` alone**, the crudest
invariant a coherent closure has.

> **▶ THE FILTER (for §10 item 3 — the coupling construction).**
> **Hunt for a VT graph whose point stabilizer, restricted to a cell, acts as a 2-transitive PROPER
> subgroup of the symmetric group.** That is precisely a **not-2-closed** local group, hence the only
> habitat where this shape of blind spot can live. It is cheap on any family with computable
> stabilizers, and each hit costs one 2-WL run to test. Per §5's ledger it has not been used as a
> filter — the sweeps were by *family* (Cayley, CFI, multipede), never by this property.

⚠⚠ **Scope, honestly.** Not-2-closed is necessary for **this** mechanism, **not** proved necessary for a
2-WL CAO failure in general — §12.3's crux is the general feedback loop and other mechanisms may exist.
And a hit is a counterexample only if the fusion survives the **global** closure, not merely the local
group's own pair-orbits: **Shrikhande is the cautionary case** — a pair-level fact, locally hidden,
globally recovered by 2-WL (§0.0's calibration figures).

**▶ Weak evidence FOR the §2 target — ⚠ UNVERIFIED, do not cite without checking.** The ladder looks
**short**: candidate local groups are those transitive on `k`-sets but not on `(k+1)`-sets, and by
Livingstone–Wagner plus the CFSG classification of highly transitive groups, the `k`-homogeneous groups
for `k ≥ 5` (with `n ≥ 2k`) are only the symmetric and alternating ones — which are 2-closed. If that
is right, this shape of failure is **confined to low arity**. ⚠ **The citation has not been checked
in-project**, and per this project's own steer a pinned statement nobody has tried to prove can be
false. Treat as a lead, not a fact.

### 14.5 ★★ THE PATH-CONDENSATION LEAD — RAISED AND CLOSED (2026-08-05)

> ⛔⛔ **CLOSED THE DAY IT WAS RAISED — read §14.5e before spending anything here.** §14.5a–d are the
> anatomy and remain correct; **§14.5e is the verdict.** The route cannot deliver a 2-WL CAO-propagation
> argument, for two independent measured reasons. What survives is diagnostic, not constructive:
> §14.5d(i)'s independent arrival at `triCount`, and §14.5e's arity reading of the whole ladder.

**The idea.** Compare two vertices not by refining colours but by the **multiset of paths between
them**, taken up to length `n` (the short lengths must be included or cycles alias). Uncondensed
that object is exponential. But under a **fibre-Schurian / CAO residue** two vertices in one cell
are Aut-conjugate, so every path statistic already agrees across a cell — which suggests the
expensive object is recoverable from a cheap one by **single-step increments**, and if it is,
§12.3's `hsep` follows and the target with it.

Everything below is measured with the clean-room machinery of §8.1 (**no orbit oracle**;
automorphisms from `all_isos`, complete I-R enumeration with every leaf re-verified):
`scratchpad/probe_pathcondense.py` · `probe_pathcondense2.py` · `probe_v4_vs_2wl.py` ·
`probe_pathanno.py` · `probe_pathanno2.py` (+ `probe_pathanno3.out`) ·
`probe_shrikhande_explain.py` · `probe_arity_ladder.py`; and for §14.5e
**`probe_window.py` · `probe_loopdetect.py` · `probe_loopcompare.py`**. Seconds each, except the
long-`maxlen` CFI runs (~45 s at length 14; lengths 16/18 were **not** reached — do not quote them).

#### 14.5a ★★ THE PROJECT'S OWN PATH CANONIZER **IS** THE 2-WL PAIR CLOSURE

`GraphCanonizationProject/Archive/V4/CanonGraphOrdererV4.cs` (built, then archived on cost)
implements a path-multiset recursion — `:70-75`, `:294-301`:

```
P_d(a,b) = {{ ( rank P_{d-1}(a,mid), adj(mid,b) ) : mid }},   keyed also by the endpoint's type
```

Ported faithfully, it is **equal as a PARTITION** — not merely in class counts — to the 2-WL pair
closure on **7/7** objects: Shrikhande, rook 4×4, `net(Z₄)`, CFI[K4] plain + twisted, CFI[K3,3]
plain + twisted.

⟹ **the archived condensation lands *exactly* on 2-WL**, and 2-WL is what fails on CFI. Any path
object stronger than 2-WL must come from something that recursion does not build (§14.5c says what).

★ **Independent validation of the constructions used in this section:** a from-scratch `net(Z₄)`
came out identical to `CFI[K4]`-twisted on every column measured (n = 28, `|Aut| = 192`, orbitals
14, 2-WL 10, walk counts 8) — §5's stated identification, reproduced by accident.

#### 14.5b ⚠⚠ FROM vs BETWEEN — the distinction the lead turns on

Two readings of *"the path multiset condenses under CAO"*. They have **opposite** verdicts, and the
composition step of any condensation argument needs the second one.

| reading | statement | at a CAO root |
|---|---|---|
| **FROM** | paths **from** `u` = paths **from** `w`, for `u,w` in one cell | ✅ **TRUE** — but it is CAO restated: *every* Aut-invariant is constant on cells. It says the cheap and the expensive object are **both** constant on cells, **not** that they are equal to each other |
| **BETWEEN** | the path multiset **between** `a,b` is determined by `[cell(a), conn, cell(b)]` | ⛔ **FALSE — measured** |

**The BETWEEN witness — Shrikhande, `v = 0`** (`probe_shrikhande_explain.py`). Root CAO holds
(vertex-transitive: one cell = one orbit). `Aut_v`-orbits are `[1, 3, 6, 6]`; take `u = 2` from the
3-orbit and `w = 6` from the 6-orbit — both non-adjacent to `v`, both in the single root cell:

| quantity at `(v,u)` vs `(v,w)` | |
|---|---|
| `[cell, adj, cell]` · 2-WL root class · walk counts **at every length** | **identical** |
| the true orbital | **different** |
| simple-path counts, len ≤ 6 | identical |
| **simple-path counts, len ≤ 7** | **differ** |
| **annotated paths, len ≤ 3** | **differ** |

`v`'s common neighbours with `u` are `[1,3]`, **non-adjacent**; with `w` they are `[1,5]`,
**adjacent** — §14.3's distinguisher, located on named vertices.

⚠ **CAO gives cells = orbits; it does NOT give pair classes = orbitals.** Shrikhande's root is
**non-schurian** (2-WL rank 3 vs orbital rank 4) while being **fully CAO**. That gap is exactly
§12.5b's E2 (477 nodes), and it is why the FROM reading cannot be freely upgraded to the BETWEEN one, this is the piece that has to be shown computable from iterated single step extensions.

#### 14.5c ★★★ THE **UNCONDENSED** PATH OBJECTS vs 2-WL — INCOMPARABLE AT BOUNDED LENGTH

> ⚠ **Read this against §14.5a, not as a contradiction of it.** §14.5a's V4 **condenses at every
> step**, keeping no vertex identity beyond the current pair, and lands *exactly* on 2-WL. `A1`/`A2`
> below **never condense**, keeping the whole path. Both statements are true of **different objects**;
> the single variable separating them — how many steps of vertex identity survive — is §14.5e.
> ⚠ And the incomparability is **bounded-length**: at full length `A2` is an orbit oracle, hence
> strictly above 2-WL. The CFI column below is **truncation**, not a property of the object.

Three nested path objects — `A0` walk counts · `A1` **simple**-path counts (repeats excluded) ·
`A2` simple paths annotated with the full induced ordered adjacency — against 2-WL and the truth:

| | Shrikhande (CAO root) | rook 4×4 | CFI[K4] plain | `net(Z₄)` (CAO root) |
|---|---|---|---|---|
| `A0` walk counts, any length | 3 | 3 | 8 | 8 |
| `A1` simple paths, len ≤ 6 → best reached | 3 → **4** (len 7) | 3 | 7 (len 12) | 7 → 8 (len 14) |
| `A2` annotated, len ≤ 3 → best reached | **4** | 3 | 7 → 9 (len 12) | 7 → 13 (len 14) |
| **2-WL pair closure** | **3** | 3 | **10** | **10** |
| **orbitals (truth)** | **4** | 3 | **10** | **14** |

- **Shrikhande: the path object beats 2-WL** (4 vs 3), and `A1` alone does it — **repeat-tracking,
  no annotation**, at length 7. Walk counts never do at any length: they are entries of products of
  class-indicator matrices, hence coherence-determined, hence never finer than 2-WL.
- **CFI[K4] plain: 2-WL beats the truncated path object** (10 = exact, vs ≤ 9 at length 12).
  ⚠ **This direction is truncation** — at full length the annotated object reconstructs the graph.
- **`net(Z₄)`: neither refines the other** — checked as a refinement relation rather than by
  counting: `A2 refines 2-WL? False`, `2-WL refines A2? False`, at length 14.

⟹ **the uncondensed path object is not "consumed within 2-WL's comparison base".** Its extra strength
on Shrikhande is real, and its source is exact: the whole gain is `A0 → A1`, i.e. tracking **repeated
vertices** — the mechanism CFI exploits. That strength is **not available to 2-WL** (§14.5e proves
the bound). ⚠ **A result proved for the uncondensed path closure therefore does not transfer to
2-WL**; at bounded length the gap is measured open in *both* directions.

#### 14.5d ▶ WHAT THE LEAD CONTRIBUTES (⚠ read with §14.5e — (ii) is moot for the 2-WL target)

**(i) "Path type" = orbital, so the lead reaches `hsep` from a new side.** *"If I am individualized,
how would I split the orbits of other cells"* for the pair `(v,u)` **is** the Aut-orbital of
`(v,u)` — that is `CaoFibring.exists_row_transport` + `sameOrbital_iff_sameStabOrbit_of_transport`,
already landed. So the lead's own question — *is the path type derivable from single-step increments
on a fibre-Schurian residue?* — **is** §12.3's crux, arrived at independently.
★ And the barriers already answer part of it: increments 1 and 2 are **provably** blind on `v`'s row
(`round1_barrier`, `round2_barrier_real`, unconditional, CC axioms only), so the floor is **three**
increments, and the third one's content is the **triple count** — the first quantity coherence does
not fix. ⟹ *"single-step increments"* and §12.5a's `triCount` are the same object from opposite ends.
✅ Reproduced on Shrikhande from the coherent root + flags (so this is **term 2**, §12.3's convention
box): rounds 1 and 2 separate nothing, **round 3 separates**, final fibres = `Aut_v`-orbits, 4 = 4.
⚠ Do **not** quote round numbers from a probe that starts at the CAO colouring when that colouring
is *not* already coherent (`net(Z₄)`) — that is the conflated term1 + term2 figure.

**(ii) ▶ THE ONE STATEMENT STILL UNTESTED — but it no longer serves the 2-WL target.** `A1`, the
**repeat-aware** simple-path count, is orbit-exact on Shrikhande at length 7 where 2-WL is one class
short. *"Are `A1`'s cells preserved under one-point extension?"* is a **different** statement from the
2-WL one, and the E1/E2 instrument (`probe_r1c.py`, §12.5b) would take it with the refiner swapped.
⛔ **After §14.5e, answering it would say nothing about 2-WL** — `A1` sits at window ≥ 3, provably
above what 2-WL computes. ⚠ Two further caveats if it is ever spent on anyway: `A1` at length `k` is
**not** polynomial in general, and `A1` is **not** universally orbit-exact — on `net(Z₄)` it had
reached only 8 of the 14 orbitals by length 14.

#### 14.5e ⛔⛔ THE VERDICT — WHY THE ROUTE CANNOT REACH 2-WL (2026-08-05)

Two independent refutations, **each sufficient alone**. Both are **count-level**: neither rests on
the per-walk purity argument, which is only *sufficient*, never *necessary* (counts could in principle
come out right by cancellation — so the purity probe alone would not have closed anything).

**(1) THE WINDOW LADDER — the cost, and what 2-WL can afford** (`probe_window.py`).
Define *r-avoiding walks*: `x_i ≠ x_j` whenever `0 < j−i ≤ r`. `r=1` is plain walks, `r=2`
non-backtracking, `r=L` full simple paths. Avoiding repeats at separation `r` requires an
**`r`-vertex transfer state** ⟹ **window `r` ≈ arity `r`**.

| object | r=1 | r=2 | r=3 | 2-WL | orbitals |
|---|---|---|---|---|---|
| **Shrikhande** | 3 | 3 | **4 = orbitals** | 3 | 4 |
| rook 4×4 | 3 | 3 | 3 | 3 | 3 |
| CFI[K4] plain (len ≤ 8) | 8 | 8 | 8 (…r=7: 8) | **10 = orbitals** | 10 |
| `net(Z₄)` (len ≤ 8) | 8 | 8 | 8 (…r=7: 8) | 10 | 14 |

- **(a)** All of the path object's strength over 2-WL **is** repeat-tracking (`r=1` ≡ 2-WL at Shrikhande).
- **(b)** The rung 2-WL can afford — `r=2`, **pair state** — buys **exactly ZERO on all four objects**.
  This is Ihara/Hashimoto: for regular graphs non-backtracking counts are polynomials in `A`.
- **(c)** The first paying rung is **`r=3` = triple state**, and 2-WL **cannot compute it**: at
  Shrikhande 2-WL (3 classes) does **not refine** the `r=3` object (4 classes).
- **(d)** Truncate length *or* window and 2-WL wins (CFI `r=7`/len 8 → 8 < 10) ⟹ the object is an
  orbit oracle only at **unbounded length AND unbounded window** — precisely what condensation removes.

**(2) THE LOOP REPAIR — TRUE PREMISE, FALSE CONCLUSION** (`probe_loopdetect.py`, `probe_loopcompare.py`).

The proposal: an interior repeat factors as prefix + closed walk at `loopStart` + suffix; the closed
walk *is* visible (a vertex's loop profile `(Aᵏ)ₓₓ` is a coherent-algebra diagonal 2-WL already holds);
only **which vertex** `loopStart` is gets forgotten by the condense step; and under CAO every cell
member carries the same loop, so the comparison should be unnecessary.

★ **The diagnosis is exactly right, and it IS the arity ladder restated:** retaining vertex identity
for `k` steps **is** arity `k`. *"The next condense step forgets it"* and *"the state is a pair, not a
triple"* are the same sentence — which is why window 2 is free and worthless, and window 3 is the
first rung that pays.

**PREMISE — verified TRUE.** At the Shrikhande root CAO holds maximally (vertex-transitive, 1 cell =
1 orbit) and every vertex carries the identical closed-walk profile `(0,6,12,96,480,2976,17472,105216)`.

**CONCLUSION — measured FALSE.** Pairs `(0,2)` and `(0,6)`: same 2-WL class, different orbitals (the
48-pair and 96-pair orbitals sit inside **one** 2-WL class), all four endpoints in the single root cell.

| window | counts by length 1…9, `(0,2)` vs `(0,6)` |
|---|---|
| `r=1` plain walks | **identical through length 9** |
| `r=2` non-backtracking | **identical through length 9** |
| **`r=3`** | …180, 802, **3880**, 18752, 88012  vs  …180, 802, **3882**, 18746, 88012 |
| `r=4` | …696, **3124**  vs  …696, **3130** |
| full self-avoidance | …696, **2500**  vs  …696, **2522** |

⟹ **minimal witness: length 7, window 3, 3880 vs 3882.** Validated constant on each orbital (an
isomorphism invariant must be). ★ Through **length 6 every window agrees** — the argument genuinely
*is* correct there, which is why it reads as sound.

**Why orbit-uniformity does not close it.** CAO gives the loop-start's **cell**, and that every member
of that cell carries an isomorphic loop. What the recursion needs is whether the loop-start **is the
same vertex** as one already on the path — a **coincidence between two positions**, not a property of
either one. Residue witness, `v=0`: simple `(0,1,2,3,4,9)` vs looped `(0,1,2,1,5,9)`; position 3 is
vertex 3 in the first and vertex 1 in the second — **same cell, identical loops**, and only the second
coincides with position 1. Orbit-uniformity makes the candidates interchangeable **in isolation**,
which is exactly what fails to determine their coincidence.
⟹ **cell-level support does not fix vertex-level identity** — the same shape as the standing
no-stabilizer-chain-supply steer, and as §14.2's cell-vs-vertex distinction.

**Scope of the refutation.** §2's target carries the **schurian** hypothesis, and Shrikhande is **not**
schurian (2-WL 3 vs orbitals 4) — so it is not an instance of *that*. But the argument **nowhere uses
schurity**, only CAO; an argument valid on the CAO hypothesis must hold at **every** CAO root, and
Shrikhande is one where its conclusion fails. ⟹ **refuted independently of which hypothesis the target
carries.** Any repair must begin consuming schurity, at which point it assumes most of the target.

⚠⚠ **VACUITY TRAP, FIRED HERE — do not re-read the raw column.** `probe_loopdetect.py`'s
per-separation output: CFI graphs are **bipartite** ⟹ odd separations never occur, and `s ≥ L−1` has
an **empty position range** — both print as "RECOVERABLE". The first run reported `s=3 RECOVERABLE`
on CFI and `s=4` on Shrikhande; **both are artifacts.** Filter by *"was this separation ever
witnessed"*. After filtering, **every non-vacuous separation is LOST**, at root **and** residue, on
all four objects.

★★ **CONSOLIDATED READING — path LENGTH is not the resource that tracks WL dimension; WINDOW is.**
One round of 2-WL *is* the length-2 path `(a,x,b)`. But iterating length-2 condensation stays at 2-WL
forever (§14.5a, at unbounded length), and plain walks of *every* length never beat 2-WL. Length-`k`
paths reach `k`-WL only if all `k` intermediates' identities are held **simultaneously**; condense
between steps and it falls back to 2.

> ⚠⚠ **Scope.** Nothing here reopens §0.0a's closure: the §2 target remains open, proved only
> per-class in the literature, with no counterexample anywhere in this project's data — and CAO was
> measurably **preserved** at every representative of every object above (2-WL fibres = `Aut_v`-orbits,
> Shrikhande 4/4, rook 3/3, `net(Z₄)` 7/7 at both reps, and CFI[K4] plain 5/5) — consistent with
> §12.5b's E1. **§14.5e refutes the ROUTE, not the TARGET**: the conclusion *"2-WL preserves CAO"* was
> true at every object measured; what is refuted is the claim that the path-condensation argument is
> the *reason*. **Premise false, conclusion true** — the same shape §12.5b already records.
>
> The section is kept, closed rather than deleted, because four things in it are durable: §14.5a and
> §14.5c are facts about the project's **own artefacts** not previously on record; §14.5d(i) reaches
> `triCount` from an independent direction; and §14.5e's **window ≈ arity** reading is the third
> independent probe to land on **arity 3** — alongside §14.4's ladder (a 2-WL failure needs a group
> transitive on pairs but not triples) and §12.5a's `triCount` (three anchors `a,b,v`). ⚠ That
> convergence is an **observation, not a proof of equivalence** between the three.
