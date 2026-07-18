# The fold/tower resolution — closing the F_k cover gap (native + tower, polynomial)

> ## STATUS (2026-07-18 late: F2b LANDED — GENERALIZED; F2a landed same day; created 2026-07-17)
>
> **✅ F2b — `deckSupply` (`ChainDescent/DeckSupply.lean`, axiom-clean, in `build.sh`; guards `Regression` §11,
> measurements `PerformanceTest` §9), GENERALIZED beyond the planned parallel-class port.** Plan-correctness
> finding first: **every consume constructor on BOTH sides emitted involutions only** (`matchCol` rank-swap, F1,
> F2a, C# `CopySwapAut`/`BuildParallelMatching`; `TryDoublingPeel` is `s % 2 ≠ 0 → null`), so a cover whose deck
> group is cyclic of odd order — `Aut` **involution-free** — was unreachable at any size, and force cannot
> substitute (one `Aut`-orbit). The §6 claim "F2 closes the `Z_pᵏ` gauge" was overstated for odd `p`; §4b below
> is the corrected design. `deckSupply` = seed every branch-cell pair, **constraint-propagate** (force a vertex
> iff a UNIQUE candidate matches colour and agrees — edges, non-edges, weights, injectivity — with every
> assigned vertex; `n` rounds; two-sided-inverse gate; `IsColAut` verify). Soundness = the invariant `m ⊆ ρ`
> (`propagate_sound`) ⟹ reconstruction `deckCand_eq_of_isColAut`; equivariance `gensEquivariant_deckSupply`;
> capstones for both objects + `foldDeckSupply_selNode_canonizer` over the new `appendSupply` combinator.
> **This subsumes the parallel-class σ port** (a `Z₂ᵏ`-tower σ is a deck element with unique extension;
> arc-consistency-with-non-edges ⊇ the induced-4-cycle rule) — §9.2's port spec is superseded, kept as the C#
> parity reference. **MEASURED:** wcyc9 (`Aut = Z₃`): fold narrow 3 (identity-only) vs deck narrow 1 (nine
> verified order-3 rotations); wcyc27 (`Z₉` — **odd part 9 ≥ 7, the case with NO C# path**; height 2): one
> propagation constructs an order-9 generator (`g⁹ = 1, g³ ≠ 1`), narrow 9 → 1; vring18 (`Z₃` voltage ring,
> rigid core): fold dead, deck 9 verified, narrow → 1; vfold2 mirror-tie: deck STALLS exactly where fold fires
> (complementarity machine-checked; `appendSupply` covers both, end-to-end fused descent answers).
> **Arity and height in one mechanism:** a `Z_{p^k}` deck is ONE propagation constructing the order-`p^k`
> generator — height enters only through `n`. **Honest firing scope:** graded + measured, never claimed —
> trivial-stabilizer seeds complete (regular deck over rigid core = every tower gadget); nontrivial seed
> stabilizers (per-copy twin gauges = wreath-type, NOT linear-over-a-ring) stall and correctly fall through.
> ⚠ Trap #1 hit LIVE again: a function-typed forcing round compounds **exponentially** under iterate (2 rounds
> ≈ 1 s, 9 rounds > 300 s at n = 9); cure = Vector-state rounds (`roundVecD`, data → data) + `uniqueFilter`,
> bridge `propagateVec_eq`. **Still open: F3** (the ring key — the force half: ordering genuinely
> distinguishable copies + native arity; on those, every deck seed propagation contradicts and emits nothing,
> correctly).
>
> **✅ F2a — `foldSupply` (`ChainDescent/FoldSupply.lean`, axiom-clean, in `build.sh`; guards `Regression` §10,
> measurements `PerformanceTest` §8).** The structural fold supply of §4, copy-swap half: fibers = same-cell-
> adjacency components, copies = cross-cell components (`relComp`, a fixed-`n` closure needing **no convergence
> proof** — every statement is relative to what it computes, with membership-level transport
> `mem_relComp_transport`); candidates = the fiber-wise copy swap from every **branch-cell seed pair** (no
> choice), unique-partner lookups + involution gate + `IsColAut` verification. Reconstruction
> `swapCand_eq_of_foldSwap` (hypotheses = exactly the cover geometry); `gensEquivariant_foldSupply`; capstones
> for **both** objects (`foldSupply_guarded_canonizer`, `foldSupply_selNode_canonizer` — the fused selector
> probes every cell with it). ζ-equal rfl-twins (`swapFunFast`/`swapCandFast`) carry the runtime (~500×).
> **MEASURED — the F1/F2 separation is real:** on 2-/3-fold vertical covers of `C₄`+pendant (n = 10/15) the
> within-copy mirror survives every pin, so `deepMatchSupply 0` **and** `partialMatchSupply 0` leave the copy
> cell un-narrowed — while `foldSupply` verifies 4/9 generators and collapses it to ONE branch. That is the
> WL-blind mechanism in miniature: F1 needs the copy refinement-visible; F2a does not.
> **Still open:** F2b (parallel-class involutions — the `Z₂ᵏ` tower gauge; spec in §4 step 3) and F3 (the ring
> key; odd-part ≥ 7 + native arity + tower peel). A cell that is an orbit only under a non-copy-swap symmetry
> (e.g. the global mirror) is correctly left to `matchSupply`/F1 at the node where it surfaces, or to F3.
>
> ## Original STATUS (2026-07-17, at creation)
>
> **What this is.** The resolution plan for the **F_k fold-cover gap** found by the 2026-07-16 blocker audit
> (`memory: project_blocker_audit_2026-07-16` item 4), and the build record of its first Lean increment. The gap:
> k-fold covers of a rigid core ("F_k towers") are handled by the C# only for odd-part(k) ≤ 5 / fully-symmetric,
> and by the Lean **not at all** — every built supply needs `SeparatesAt` depth `d ≥ k−2` on a k-fold cover, so the
> whole family (including the parts C# handles in poly) costs `n^{Ω(k)}` and lands in the flag.
>
> **The resolution is THREE moves, one per architecture slot** (nothing new is bolted on; each lands in an
> existing seam with its existing ① story):
> - **F1 — `partialMatchSupply d` (consume; support-local matching). ✅ LANDED 2026-07-17**
>   (`ChainDescent/PartialMatch.lean`, axiom-clean, in `build.sh`; guards in `Regression.lean` §8). Kills the
>   depth-grows-with-k failure for **refinement-visible** folds: a copy transposition is caught at the depth that
>   discretizes **one copy**, independent of `k` (measured: `d = 0` on a 4-fold cover where `deepMatchSupply 0`
>   certifies nothing).
> - **F2 — the structural fold supply (consume; the C# B4 port).** Designed §4, **not built**. For **WL-blind**
>   cores (multipede folds — refinement cannot discretize a copy, so no matching supply can fire): detect
>   fibers/copies structurally from `(adj, χ)`, emit fiber-wise copy-swap + parallel-class involutions, verify via
>   `IsColAut`. Equivariant because every seed is enumerated (no choice).
> - **F3 — the ring key (force; canonical-coset ordering).** Designed §5, **not built** (= the rigid-seal track
>   §11.12, entering as a `Force.Key`). Covers the **native** encoding (gadget arity `exp(A) ≤ |A| ≤ n`), the
>   **tower** depth peel, and — via CRT + Smith canonical cosets — the **distinguishable copy ordering**, which is
>   the piece missing on BOTH sides (C# odd-part ≥ 7 `null`; Lean nothing). It replaces the `s! ≤ 6` cap and the
>   p=2-only doubling peel with ring arithmetic that has no parallel-class obstruction.
>
> **Poly headline for both encodings** (§6): native = arity ≤ n (F3); tower = per-level consume of the
> elementary-abelian gauge (F1/F2) + value peel across descent levels ≤ n (F3). No move claims the WL-blind
> **non-linear** residue — that stays the named wall, unchanged.
>
> **Doc corrections carried by this plan:** `chain-descent-ir-blindspot-solver.md` §STATUS "Fold covers s > 6 —
> RESOLVED, poly, any s" / "Q1 CLOSED" are **overstated** (its own scope note eight lines later concedes odd-part
> ≤ 6): corrected 2026-07-17 with banners pointing here. The endgame-spec "rigid node-4 … handled" leg
> (`chain-descent-endgame-spec.md` §1a) is scoped by §7 below until F3 lands.

---

## 1. The gap, precisely (evidence)

**C# (`Option2Solver.TryCanonicalOrderWithFold`, all landed):** detects a fold structurally at the descent root —
FIBERS = connected components of the same-cell-neighbour graph, COPIES = components of the graph minus same-cell
edges, layout table `vertexAt[fiber*s + copy]` a bijection. Then:
- **Fully symmetric** (every copy-0↔c fiber-wise transposition `CopySwapAut` verifies edge-by-edge, `O(s·n²)`):
  identity copy order — **poly for any `s`**.
- **Distinguishable, `s ≤ MaxFoldMultiplicity = 6`**: exact lex-min of the serialized permuted adjacency matrix
  over the `s!` copy orderings (fiber order fixed by the recursively-canonized core).
- **Distinguishable, `s > 6`**: `TryDoublingPeel` — build a parallel class (perfect matching on copies via induced
  4-cycles), 2-colour across it, recurse on one half, lift; lex-min over the ≤ log₂ s directions. **Only peels
  factors of 2** (`s % 2 != 0 → null`).
- ⟹ **odd-part(s) ≥ 7 returns `null`** (sound fall-through) → exhaustive descent on WL-invisible copies → budget
  flag. Base-p peeling (p ≥ 3) is explicitly out of scope (the rook's-graph K_p□K_p fiber has matching-shaped
  parallel classes, not a removable clique coordinate).

**Lean (before this plan):** no fold mechanism of any kind. The supplies (`matchSupply`, `deepMatchSupply d`,
`prunedSupply d`) construct candidates only from **fully discrete** colourings (`matchCol` dif-gates on
`Discrete` both sides), so certifying any copy symmetry of a k-fold cover requires discretizing all but one copy:
`SeparatesAt` forces `d ≥ k−2`, cost `n^{Ω(k)}`. **Even the C#-poly cases (fully symmetric, Z₂ᵏ towers) exit the
Lean poly regime.** The force side (`lookaheadKey`) cannot help on the symmetric part — an equivariant key is
constant on orbits (`keyV_aut_invariant`).

**Why it blocks the project:** the family is *linear-over-a-ring*, i.e. inside the rigid seal's claimed-handled
leg (`endgame-spec.md` §1a "CFI / multipede / Z_{2^k} … handled"), and an odd-part-≥ 7 tower is a **constructible,
not-believed-GI-hard** member of the residue — a falsifier for the planned ③ characterization ("the only unhandled
inputs coincide with a known GI-hardness frontier"). The landed `residue_if_flag` (residue = `¬Handled`) stays
true; the *endgame narrative* does not, until this plan closes the family.

---

## 2. The design in one paragraph

A fold cover presents exactly the project's two decision types, layered: the **copy symmetry** (deck
transformations — consume's domain) and the **copy ordering + rigid core** (real decisions — force's domain).
The failure was never architectural; it was that (a) the only *candidate constructor* on the consume side demanded
**global** discreteness where verification (`IsColAut`) never needed it, and (b) the only force key is a look-ahead
heuristic with no ring arithmetic. So: **F1** generalizes the constructor from global matching to **support-local**
matching (catches involutions whose support is half-discretized — copy transpositions and gauge flips — at depth
independent of `k`); **F2** constructs the same involutions **structurally** where refinement is blind (the C# B4
detection, ported as an untrusted supply); **F3** gives force the ring solve (Smith/CRT canonical cosets) that
orders distinguishable copies and forces native-arity gadgets. All three are untrusted-or-key instances of the
existing contract: **① is never re-proved.**

---

## 3. F1 — `partialMatchSupply d` (✅ landed; `ChainDescent/PartialMatch.lean`)

**The observation.** `matchCol ψ₁ ψ₂` requires `Discrete ψ₁ ∧ Discrete ψ₂` because it matches by global colour
ranks. But an automorphism worth catching on a fold — a **copy transposition** — is the identity outside two
copies, and pinning ONE vertex discretizes one copy (for a refinement-visible core). Everything the candidate
needs is already in the colours:

- **forward**: a `ψ₁`-singleton vertex maps to the unique `ψ₂`-vertex of the same colour;
- **backward**: a `ψ₂`-singleton vertex maps to the unique `ψ₁`-vertex of its colour (correct for **involutions**:
  `ψ₂ = ψ₁ ∘ α⁻¹` and `α = α⁻¹`);
- **identity** elsewhere (correct wherever `α` doesn't move);
- then a **two-sided inverse check** builds the `Equiv.Perm`, and `Consume.verified` re-checks `IsColAut` as
  always — the supply stays untrusted.

**What it provably catches** (`partialMatch_transport_of_catches`): `partialMatch ψ (transportColouring α ψ) =
some α` whenever **either** (i) every moved vertex is a `ψ`-singleton (subsumes the full-discrete case — so every
`deepMatchSupply` firing is also a `partialMatchSupply` firing, `supportSeparatesAt_of_separatesAt`), **or**
(ii) `α` is an **involution** and every moved vertex is a singleton **on one side** (`SingletonAt ψ x ∨
SingletonAt ψ (α x)`). Firing predicate: `SupportSeparatesAt adj χ d`; capstone
`cellIsOrbit_partialMatchSupply`; canonizer `partialMatchSupply_guarded_canonizer` (via `GensEquivariant` — the
construction makes **no choice**, so equivariance has the same shape as `deepMatchSupply`'s; standing trap #7
respected).

**What it buys on folds.** A k-fold cover of a refinement-visible core: the transposition `copy_a ↔ copy_b` has
support = two copies; pinning `x_a` discretizes copy `a`; every moved vertex is singleton on one side ⟹ caught at
**`d = 0`**, any `k`. All `k−1` transpositions verify ⟹ the branch cell is one `WordReach` class ⟹ consume
collapses it to ONE branch. Measured (Regression §8, 4 disjoint copies of a 6-vertex asymmetric core, n = 24):
`deepMatchSupply 0` leaves the 4-way fan-out (its constructor needs the other three copies discrete);
`partialMatchSupply 0` collapses it to 1. `deepMatchSupply` needs `d ≥ 2` there — and `d ≥ k−2` in general, which
is the `n^{Ω(k)}` this kills.

**Cost.** Identical table to `deepMatchSupply d` (`deepTable`), pairwise `partialMatch` at `O(n²)` each: `c₂ =
|table|·(d+1)·warmRefineCost + |table|²·n²`, poly for fixed `d` — and the point is that `d` no longer scales with
`k`. (The P3c reference-matching / online-pruning line applies to this table verbatim if it ever needs the
`|table|²` cut; `OrbitPrune.SameOrbits` is supply-agnostic.)

**Scope honesty.** F1 needs the support **refinement-visible** (a pin discretizes a copy). A multipede core is
WL-blind — no matching supply can fire there at any depth. That case is F2/F3's, by design.

---

## 4. F2 — the structural fold supply (designed; the C# B4 port)

**Why it must exist.** On a WL-blind core, copies never contain singletons, so F1's condition is unsatisfiable —
yet the C# certifies the copy symmetry in `O(s·n²)` with **no refinement at all**, because the fold is visible in
the *cell structure*: same-cell adjacency components (fibers) × cross-cell components (copies).

**The supply** (`foldSupply : Supply n`, a pure function of `(adj, χ)` — stateless, per the P1 constraint):
1. Compute fibers (components of `{(v,w) : adj v w ≠ 0 ∧ χ v = χ w}`) and copies (components of the complement
   predicate); require uniform fiber size `s ≥ 2`, `#copies = s`, and the `(fiber, copy) ↦ vertex` table to be a
   bijection — else emit `[]` (a supply that emits nothing costs branches, never correctness).
2. Emit **every** fiber-wise copy transposition (the C# `CopySwapAut`: swap copy `a` and copy `b` inside every
   fiber, identity elsewhere) for **all** pairs `a < b` — not just `0↔c`; enumerating all pairs is what makes the
   emission choice-free.
3. Emit every **parallel-class involution**: for every same-cell seed edge in every fiber (all seeds enumerated),
   propagate the induced-4-cycle matching rule; on success, the whole-graph involution `v ↦ vertexAt(fiber(v),
   τ(copy(v)))`. These are the Z₂ᵏ-tower gauge generators the doubling peel uses — harvested here as *consume*
   generators instead.
4. `Consume.verified` filters everything through `IsColAut` — soundness free, broken detection harmless.

**Obligations.** ①a/①b free (untrusted). ①c: `GensEquivariant` — the fiber/copy decomposition is a structural
function of `(adj, χ)` and every candidate family is enumerated over *all* seeds/pairs, so the emitted list
transports as a set; alternatively run it through `OrbitPrune.SameOrbits` against its all-seeds closure. Firing:
graded per verified pair (each transposition merges its orbit); endpoint = fully-symmetric fold ⟹ branch cell is
one orbit. Cost: `O(n²)` detection + `O(s·n²)` per candidate, ≤ `s(s−1)/2 + s·log s` candidates ⟹ poly,
**no dependence on refinement depth at all**.

**Relation to the Lean gauge assets.** `CFI.lean` already has computable local gauge flips
(`IsCFI'.cfiFlipAut`, involutive, `Z₂^β → Perm` homomorphism `cfiFlipAut_xorF`) — but keyed to a recognized
`IsCFI'` structure. F2 is the same move keyed to the *fold* structure, which is cheaper to recognize (components,
not gadget isomorphism). A later unification (one "structural involution supply" parameterized by a recognizer)
is natural but not required.

---

## 4b. F2b — `deckSupply`, the propagation harvest (✅ landed; GENERALIZES steps 2–3 of §4)

**The gap that forced the generalization (2026-07-18).** Steps 2–3 of §4 (fiber-wise transpositions +
parallel-class involutions) emit only elements of order 2 — as does every other consume constructor on both
sides. So the *group* the supply can certify is generated by involutions, and a fold whose deck group is cyclic
of odd order has **no involutions in `Aut` to harvest at all**: constructible witnesses are the weighted cycles
`C_{3s}` (edge weights (1,2,3) repeating — `Aut = Z_s` exactly, the weight pattern kills every reflection) and
`Z_s` voltage rings over rigid cores (the true tower-gadget shape). On these, `foldSupply` degenerates to
identity candidates, both matching supplies see no singletons at the root, and force is blocked by
`keyV_aut_invariant` (the cell is one orbit). The C# has the same boundary from the other end: odd part ≥ 7
returns `null`. **The consume side needs generators of arbitrary order** — that is what "handle a Z tower of
arbitrary arity" means at the supply level.

**The design.** `deckSupply : Supply n` — for every branch-cell seed pair `(u₁, u₂)`:
1. Start from the one-point partial map `u₁ ↦ u₂` and run **forced constraint propagation**: an unassigned
   vertex `v` is assigned `w` exactly when `w` is the *unique* vertex with `χ w = χ v` that agrees with **every
   already-assigned pair** `(v₃, w₃)` on adjacency in both directions with full weight equality (non-edges
   included) and injectivity (`w ≠ w₃`). Iterate `n` rounds (monotone; a round that assigns nothing is a
   fixpoint; no convergence proof needed — every statement is relative to the computed value).
2. Gate: forward and reverse (`(u₂, u₁)`) propagations must be **two-sided inverses** (decidable); build the
   `Equiv.Perm`; `Consume.verified` re-checks `IsColAut` as always. Stalls and contradictions emit junk that
   fails a gate — sound by construction, untrusted as ever.
3. No choice anywhere (standing trap #7): forcing fires only on unique candidates, seeds are the whole cell.

**Why it subsumes the §4-step-3 parallel-class port.** The C# induced-4-cycle rule (`τ c` = the unique `d` with
`F c d ∧ F y d ∧ ¬F x d`) is arc-consistency at the copy level with one edge + one non-edge constraint; the
vertex-level forcing above imposes a strict superset of those constraints over a candidate pool restricted by
colour, so wherever `BuildParallelMatching` propagates uniquely, `deckSupply` forces uniquely — and it also
constructs what no matching can: rotations of any order, in one propagation (`Z_{p^k}` towers included — the
order-`p^k` generator directly, so **height** costs nothing beyond `n`).

**The theorems** (`ChainDescent/DeckSupply.lean`, axiom-clean):
- `propagate_sound` — the invariant: anything the propagation assigns agrees with ANY colour-automorphism
  extending the seed (the forced value is the unique constraint-satisfier, and `ρ`'s value satisfies).
- `deckCand_eq_of_isColAut` — reconstruction: if some `ρ ∈ Aut_χ` extends the seed and both propagations
  complete, the candidate **is** `ρ`. Corollary: at most one automorphism extends a completed seed — so
  completion is exactly the trivial-stabilizer regime, decidable per seed, measured per family.
- `gensEquivariant_deckSupply` / `supplyEquivariant_deckSupply` — the forcing rule transports (`mconj`; the
  `uniqueMem_transport` engine), so ①c is discharged with no new class.
- Capstones: `deckSupply_guarded_canonizer`, `deckSupply_selNode_canonizer`, and
  `foldDeckSupply_selNode_canonizer` over **`appendSupply`** (new: supply concatenation, gens appended, costs
  summed, equivariance splits — the combinator §10 predicted).
- Firing: `wordReach_deckSupply` / `cellIsOrbit_deckSupply`, graded per pair as house style demands.

**Measured (all in `Regression` §11 / `PerformanceTest` §9).** wcyc9: branch cell `[1,4,7]`; fold narrow **3**
vs deck **1** (9 verified, the three order-3 rotations); equivariance sanity under relabelling. wcyc15 (`Z₅`):
25/25 seeds complete, narrow → 1. wcyc27 (`Z₉` — odd part ≥ 7, no C# path; height 2): narrow 9 → 1; a single
propagation yields `g` with `g⁹ = 1 ∧ g³ ≠ 1`. vring18 (`Z₃` voltage ring, rigid 6-vertex core, reversal ghost
killed by asymmetric pendant paths): fold 3 / deck 9 verified, narrow → 1. vfold2 (mirror-tied): deck stalls
(every cross-copy seed has TWO extensions — copy-swap and copy-swap∘mirror — so no forcing step on the mirror
class is ever unique), fold fires: the two supplies are **complementary**, and `appendSupply fold deck` narrows
both families (guarded) with the fused end-to-end descent answering on wcyc9.

**Honest scope.**
- Firing needs **trivial seed stabilizers** (unique extension ⟹ forcing can complete). Regular deck action over
  a rigid core — every native gadget and tower encoding in the family — is exactly that. This is a *graded,
  measured* firing story, mirroring `SeparatesAt`/`CatchesAt`: no completeness theorem is claimed.
- A fold with **per-copy independent gauge** (twin swaps localizing per copy — deck = a wreath `Z₂ ≀ Z_s`, not a
  ring) gives every seed ≥ 2 extensions at unbounded depth: deckSupply stalls, and the family is **outside the
  linear-over-a-ring leg** the rigid seal claims — it lands in the residue, correctly (not a retreat: nothing in
  the endgame narrative claimed wreaths).
- On genuinely **distinguishable** copies, no automorphism extends any cross-copy seed: propagations contradict,
  nothing is emitted, the cell is not narrowed — that ordering is F3's force-side job, unchanged.
- On small witnesses a **pin discretizes** these cycles/rings, so the matching supplies also fire there; the
  machine-checked separation in the gate is against the involution-based structural supply, and the odd-arity +
  refinement-free claims are the design content. The WL-blind separation witness at scale remains the multipede
  fold port (as with F2a), staged with F3.

---

## 5. F3 — the ring key (designed; force side; = §11.12 entering as a `Force.Key`)

**What force must do on this family:** order the genuinely-different branches — the **distinguishable** copy
orderings and the **rigid core's** decisions — structurally, without knowing the answer. The C# already validates
the core solve (extended Smith over BigInteger, ring-general for bounded rank, native Z6/Z8/Z9/Z2×Z4). What is
missing on both sides is the **copy-ordering primitive for odd-part(s) ≥ 7**. The fix is to stop ordering copies
combinatorially (parallel-class peels are a p = 2 accident) and order them **at the linear level**:

- **Recover** the copy coordinate as a ring value: the F_k tower family is linear-over-`Z_s` by construction (the
  copy relation is a union of Cayley classes of `Z_s`, resp. the module structure recovered relationally per
  §11.13a — Albert/Latin-square, poly).
- **CRT-decompose** `Z_s = ⊕_p Z_{p^{e_p}}`; the odd part stops being special — each Sylow component is peeled by
  the **same** move (project to the component, solve, order), which for `p = 2` *specializes to* the doubling
  peel. No parallel-class/matching shape is needed because nothing combinatorial is peeled — the projection is
  ring arithmetic on the recovered coordinate.
- **Order canonically**: per component, Smith normal form ⟹ canonical coset representative; the residual freedom
  is the unit group / automorphisms of `Z_{p^e}` (≤ `p^e ≤ s ≤ n` candidates) — lex-min over it replaces the
  `s!` cap with an `≤ n` scan.
- **Key shape in Lean:** `ringKey : Force.Key n` ranking a branch vertex by the canonical coset data of the
  solved system after individualizing it. Sole ① obligation `KeyEquivariant` (the solve is a structural function
  of `(adj, χ, v)`; no vertex-index tie-breaks). Firing obligation = `KeySeparates` on the distinguishable fold /
  native multipede families — §11.12's P1/P3 content, landing on the ② side as designed.

**The two encodings, closed by F3 + F1/F2** (this is the direct answer to "handle both native and tower
encodings in polynomial time"):
- **Native** (value of order `e` occupies `e` fiber states): gadget arity = `exp(A) ≤ |A| ≤ n` ⟹ the recovered
  system has ≤ `n`-ary rows; Smith solve poly; the cost appears as **arity** and is bounded by the vertex count.
- **Tower** (compressed `Z/2^k` or `Z/p^k` register, `|A| = p^k` possibly `> n`): the graph's *gauge* is
  elementary-abelian (exponent `p`) — consumed level-by-level by F1/F2 as **involutions** (p = 2) resp. the
  verified structural generators (odd p); the large exponent lives only in the solver's arithmetic, peeled across
  ≤ `n` descent levels (each level's exposed layer is an inhomogeneous linear system over the residue ring — the
  2-adic/`p`-adic content of Smith). The cost appears as **depth** ≤ n, each level poly.

**Scope honesty.** F3's ordering claim is for **linear-over-a-ring copy relations** — exactly the family the
rigid seal's leg claims. A cover whose copy relation is not linear falls through to the flag; that is correct
(an arbitrary copy graph embeds full GI into the fold, and "flag on it" is the designed poly-or-flag behaviour —
NOT an "impossible, therefore" argument; a stronger future key shrinks it like any residue).

**C# parity fix (same design, so the testbed and the proofs stay aligned):** replace `TryDoublingPeel`'s
recursion with the CRT peel above (`MaxFoldMultiplicity` cap then only guards the final unit-group lex-min, which
is ≤ s, so the cap can go entirely); keep `CopySwapAut` harvest as-is. Until then, the C# scope note (odd-part
≤ 5) is the truth and the §STATUS headline is corrected (see banner).

---

## 5b. F3 SCOPED AND STAGED (2026-07-18 scoping pass — read this before starting F3 work)

**What the re-based contract makes F3 (from IR §11.12's 2026-07-13 re-base + handoff §6.3):** a `Force.Key`
whose ONLY ① obligation is `KeyEquivariant`; all P1/P3 content is **firing/②** — a `KeySeparates` predicate
(force's dual of `CellIsOrbit`) plus measured separation and honestly-charged cost. No solve-correctness
theorem is owed for soundness.

**Scoping findings (each changes the build):**
1. **`lookaheadKey` already covers the pin-discretizing half.** Its leaf-matrix branch is a complete invariant
   of the pinned refinement, so any distinguishable fold whose copies discretize under one pin is ALREADY
   ordered canonically — including odd-part ≥ 7 (no C# analog needed on that half). The genuine F3 residue is
   **distinguishable-but-WL-merged**: twisted covers where the pin leaves ties (the mirror survives) and the
   histogram/leaf branches are blind. This is the CFI-parity family — exactly where the C# needs the solve.
2. **Propagation-signature keys are NOT the vehicle.** Two independent reasons: (a) the C#'s own B1d finding —
   unit propagation stalls on cyclic constraint graphs (m ≥ 8 circulants) and needed the *simultaneous* Smith
   solve; a key built from `deckSupply`-style forcing traces inherits that ceiling; (b) the twist invariant is
   **coset/solvability** data — kernels, ranks and local forcing profiles are IDENTICAL for twisted vs
   untwisted covers (both sides of the witness below have the same gauge kernel; the twist sits in the
   inhomogeneous class). Local signatures cannot rank it.
3. **The structurally-readable form of the coset data is the HOLONOMY of the fold.** Compose the vertical
   matchings (F2a's unique-fiber-partner maps) around closed walks of the copy graph: the composite is a
   permutation of the start fiber — identity for straight cycles, the mirror/deck twist otherwise. This is the
   cover's monodromy: gauge-independent (no reference pairing is ever chosen — composition of canonical partner
   maps), arbitrary-arity (a `Z_s` twist appears as an order-`s` composite), and it is precisely the object the
   Smith solve canonicalizes, read combinatorially. Conjugation (choice of base copy) is quotiented by using
   conjugation-invariant signatures (cycle types); tree/walk enumeration is quotiented by enumerating ALL
   closed walks of bounded length (no spanning-tree choice — trap #7).
4. **The measured witness (F3 probes 2026-07-18, n = 30):** `U3 ⊔ T3` — vfold3 (all-straight triangle of
   matchings over the mirror-tied `C₄`+pendant core) unioned with its one-pair-twisted variant (`1₀—3₁,
   3₀—1₁` on copy-pair (0,1); construction recipe: copy `c = i/5`, core `v = i%5` with `Regression.vcoreB`,
   vertical `vᵢ—vⱼ` iff `v` equal — except the (0,1)-pair's `{1,3}` fiber crossed in `T3`; union
   block-diagonal at 15). Twist parity around the copy triangle ⟹ `T3 ≇ U3`; the gauge (per-copy mirrors)
   makes each component's pendant cell ONE orbit; 1-WL merges the two components. Measured: branch cell = all
   6 pendants `[4,9,14,19,24,29]` (WL-merged ✓); `lookaheadKey` keeps all 6 (dead ✓). Consume cannot resolve
   the cell as a matter of principle — a verified generator is an automorphism and no automorphism maps
   between non-isomorphic components — so the root cell holds ≥ 2 orbits ⟹ **the union needs force, and only
   a beyond-1-WL key fires**. **The L = 3 holonomy signature separates it 3|3, measured:** every U-pendant
   gets the value set `{0, 5}` (straight triangles = identity holonomy; cross-component walks all-undefined)
   and every T-pendant `{2, 5}` (the twisted triangle moves exactly the two mirror vertices), uniform within
   each orbit, ~0.5 s interpreted with materialised id-tables. (Disjoint union is the minimal form; a
   connected variant — path-joined at one pendant each — keeps the WL-merge and is the follow-on witness.)

**The staging:**
- **F3a — `KeySeparates` infrastructure + the holonomy key (`holKey`). ▶ FIRST TRANCHE LANDED 2026-07-18
  (`ChainDescent/HolKey.lean`, compile-clean, axiom-clean, in `build.sh`):** `KeySeparates` (force's firing
  dual of `CellIsOrbit`) + **the firing theorem `keepMin_pairwise_aut_of_separates`** (separates ⟹ the kept
  branches are pairwise `Aut`-equivalent — inside ONE orbit, which consume then collapses; the graded mirror
  of `cellIsOrbit_*`), and the spec-level key: `partnerTo` (the one-sided F2a partner lookup, target copy
  designated by a VERTEX — no ids, no representatives), `walkOk`/`holMoved`/`holSig` (moved-count of the
  composite `copy(v) → copy(t₁) → copy(t₂) → copy(v)`, sorted dedup over ALL target pairs; `L = 3` is the v1
  grading — the witness's parity lives there; the ladder extends like every other oracle's `d`), `holKey` with
  flat `n⁵` cost. **STAGED (the remaining tranche):** (i) the **component-closure lemma set** — `relComp` of a
  symmetric relation is membership-equivalence (closedness after `n` monotone rounds; the convergence content
  F2a deliberately never needed, F3a genuinely does: well-definedness of vertex copy-designators is what the
  evaluation twin's per-copy dedup and several transport steps factor through); (ii) the **evaluation twins**
  (materialised id-tables, the probe's shape — the spec forms recompute `relComp` per membership test, trap
  #1's shape, do not `#eval` them at `n ≥ 15`); (iii) **`KeyEquivariant holKey`** via the F2a toolkit
  (matchings conjugate by `uniqueMem_transport` + `mem_relComp_transport`; walk enumeration reindexes;
  dedup+sort invariant); (iv) witness guards (`holKey` splits the 6-pendant cell 3|3 where `lookaheadKey`
  keeps 6) + capstone `forceThenConsume holKey (appendSupply foldSupply deckSupply)` + fused mirror.
- **F3b — the Smith/CRT coset canonicalization** (= §11.12 P3's real weight, §5 above): needed where holonomy
  *signatures* exist but must be ORDERED at the module level (large holonomy groups; native-arity gadget
  systems with no fold skeleton; canonical coset reps of `coker`). **Gated on a concrete witness where F3a
  measurably fails to separate** — do not build speculatively. Mathlib has Smith over PIDs; the computable +
  equivariance story is the heavy build the plan always priced.
- **C# parity** unchanged (§8 item 5: CRT peel; odd-part ≥ 7 red-bar test first).
- **Sequencing vs §6.4 (duplicate-refine):** `holKey` does no refinement look-ahead, so it sidesteps the
  triple-refine loss entirely; `lookaheadKey`'s hand-forward retirement stays coupled to the §6.1 interface
  work, not to F3a.

---

## 6. Polynomial accounting (per descent node; single guarded path ⟹ ≤ n+1 nodes)

| move | trigger | per-node cost | closes |
|---|---|---|---|
| F1 `partialMatchSupply d` | support half-discretized involution / any α with discretized support | `|table|²·n²`, `|table| = |cell|·n^d`, **`d` fixed small** (0–1 on folds) | symmetric folds over refinement-visible cores, any `k`; point-stabilizer cases beyond `deepMatchSupply` |
| F2a `foldSupply` | fiber/copy structure present | `|cell|²·n⁵` flat | **involution part** of symmetric folds over WL-blind cores (copy swaps; mirror-tied copies included) |
| F2b `deckSupply` | trivial-stabilizer seed (regular deck over rigid core) | `|cell|²·n⁵` flat (n rounds × n vertices × n candidates × n checks per seed) | deck generators of **ANY order**: cyclic/abelian gauges of arbitrary arity AND height (`Z_{p^k}` in one propagation); subsumes the parallel-class σ |
| F3 `ringKey` | recovered linear system solvable | Smith `poly(n)` + unit-group scan ≤ n | native arity ≤ n; **distinguishable ordering incl. odd-part ≥ 7** (the force half — deck seeds have no extension there and correctly emit nothing) |

(The original "F2 closes symmetric folds + Z_pᵏ gauge" row conflated the involution harvest with the odd-`p`
gauge — corrected 2026-07-18; the odd/arbitrary-order half is F2b's, and it is landed.)

② stays as-is: every cost is billed in `supplyCost`/`keyCost`, so `descentCost_guard_le` sees it; nothing here
touches the node bound. ③: F1/F2 firing populates `CellIsOrbit` directly at fold nodes (no seal import needed for
this family — localisation is *proved by the verified generators themselves*), so the fold families enter
`Residue.Handled` through the same `HandledBridge` hooks (`handled_of_seal_selected`-shape statements with the
fold's own localisation) once F2/F3 land.

---

## 7. What this plan does NOT close (kept explicit, per the vacuity steer)

- **The WL-blind non-linear residue** — unchanged, the named wall (`hSmallAutThin`). No move above claims it.
- **F2/F3 are designs**, not theorems: until they land, the *Lean* fold coverage is exactly F1's (refinement-
  visible folds), and the endgame-spec "rigid node-4 handled" leg remains scoped to what the C# validates
  (odd-part ≤ 5 towers + native rings, bounded rank) **plus nothing on the Lean side**.
- **`lookaheadKey` retirement**: F3 replaces it as the force instance of record (user 2026-07-17: the current
  force consumer is prospective and freely replaceable); until F3 lands, force keeps firing-but-not-paying
  (handoff §6.4) and the duplicate-refine/`sel` signature change remains the scheduled vehicle to fix both.

## 8. Build order

1. ✅ **F1** (`PartialMatch.lean` + Regression §8 guards) — landed 2026-07-17.
2. ✅ **F2a** `foldSupply` (`FoldSupply.lean` + Regression §10 + PerformanceTest §8) — landed 2026-07-18. Pure
   supply build, no contract changes, exactly as planned. ⚠ The demo family CHANGED from the plan: a multipede-core
   port was unnecessary — a **mirror-tied core** (`C₄`+pendant, vertical cover) already exhibits the WL-blind
   mechanism (the within-copy mirror survives every pin, so no matching supply ever sees a singleton) at n = 10,
   which is what makes the guards build-gateable. A true multipede fold is still the right *eventual* witness for
   the F2b+F3 composition; port it when F2b lands.
3. ✅ **F2b** `deckSupply` (`DeckSupply.lean` + Regression §11 + PerformanceTest §9) — landed 2026-07-18,
   **GENERALIZED** (§4b): the planned parallel-class port would have kept the exponent-2 ceiling; the
   propagation harvest subsumes it and closes arbitrary arity + height on the consume side. Includes
   `appendSupply` (supply concatenation + split equivariance + fold++deck capstone).
4. **F3** `ringKey` — after (or with) the key-side duplicate-refine residual (handoff §6.1 landed the interface;
   `lookaheadKey` still recomputes internally), since a solve-derived key is exactly the look-ahead worth handing
   forward; Lean content = §11.12 P1 (extraction soundness) + P3 (solve iso-invariance) instantiated as
   `KeyEquivariant` + `KeySeparates`. With F3, port a true **multipede fold** as the joint F2+F3 witness at
   scale (the WL-blind separation the small witnesses cannot show — a pin discretizes them).
5. C# parity, now TWO items: (a) the CRT peel replacing `TryDoublingPeel` (§5); (b) optionally the propagation
   harvest itself (`deckSupply` is straightforwardly portable and strictly more general than
   `BuildParallelMatching`). Then re-run the fold suite with a failing odd-part ≥ 7 case added FIRST as the red
   bar — today that case has no C# test at all. The **Lean** side no longer has this gap (wcyc27 measured).

---

## 9. HANDOFF — build state + pickup (2026-07-18)

**Read first:** the STATUS block above, then this section. Everything below is source-verified as of 2026-07-18;
build green 164 s serial; all new theorems axiom-clean `[propext, Classical.choice, Quot.sound]`.

### 9.1 What exists, where

| piece | file | capstones | witness |
|---|---|---|---|
| F1 support-local matcher | `ChainDescent/PartialMatch.lean` | `partialMatchSupply_guarded_canonizer`, `cellIsOrbit_partialMatchSupply` (+ graded `wordReach_…`), `supportSeparatesAt_of_separatesAt` (subsumption) | `Regression` §8 (`fold4`, n = 24: deep dead d=0, partial fires d=0), `PerformanceTest` §7 (descent answers/flags `(true,false)`; deep d=1 dead at 132× cost) |
| F2a structural fold supply | `ChainDescent/FoldSupply.lean` | `foldSupply_guarded_canonizer`, `foldSupply_selNode_canonizer` (fused), `cellIsOrbit_foldSupply`, reconstruction `swapCand_eq_of_foldSwap`, `gensEquivariant_foldSupply` | `Regression` §10 (`vfold2`, n = 10: deep AND partial dead, fold verifies 4, narrow 2→1), `PerformanceTest` §8 (n = 15: 9 verified, narrow 3→1; costs 6 834 375 vs 12 150) |
| F2b propagation supply (§4b) | `ChainDescent/DeckSupply.lean` | `deckSupply_guarded_canonizer`, `deckSupply_selNode_canonizer`, `foldDeckSupply_selNode_canonizer` (over `appendSupply`), `cellIsOrbit_deckSupply`, reconstruction `deckCand_eq_of_isColAut` (via invariant `propagate_sound`), `gensEquivariant_deckSupply`, `gensEquivariant_appendSupply` | `Regression` §11 (`wcyc9`: fold narrow 3 vs deck 1, 9 verified rotations; vfold2 complementarity: deck stalls, append narrows both), `PerformanceTest` §9 (`wcyc15`/`wcyc27` = `Z₅`/`Z₉` odd-part ≥ 7, order-9 generator from one propagation; `vring18` voltage ring; fused end-to-end answers) |

Supplies plug into **both** objects unchanged: the guarded blind object via `SupplyTransport.guarded_mixed_canonizer`
and the fused selector via `Select.selNode_canonizer` — each needs only `SupplyEquivariant` (from `GensEquivariant`).
The `SameOrbits` route (`OrbitPrune`) remains available for any pruned variant.

**Traps hit this build (beyond the standing §7 list of the handoff):**
- Guard graphs must use **arithmetic** edge predicates and **`ColData`-materialised roots**; a List-membership
  `decide` edge predicate made an n = 15 supply call cost minutes (the supply's closures call back into the
  interpreted adjacency on every `rel` evaluation).
- A full guarded **descent** at n = 24 costs ~80 s interpreted *even when it stalls at the root* — never put one in
  `Regression`; supply-level `narrow`/`verified` guards carry the same content (narrowing ≥ 2 ⟹ flag is
  `Stall.resolvedAll_guard`, a theorem).
- `swapFun`'s spec form recomputes `relComp` inside the `uniqueMem` scan; the ζ-equal rfl-twins
  (`swapFunFast`/`swapCandFast`, proved by literal `rfl`) are ~500×. Any F2b candidate constructor should be
  written twin-first.

### 9.2 F2b — the parallel-class involutions (⊘ SUPERSEDED 2026-07-18 by §4b's `deckSupply`; kept as the C#
parity reference — `Option2Solver.cs:303-426`)

> **⊘ Do not build this port.** The propagation harvest (§4b, landed) imposes a strict superset of the 4-cycle
> rule's constraints, so every σ this spec would construct is already constructed by `deckSupply` — and the
> port would have kept the exponent-2 ceiling this plan exists to remove. The mechanics below remain the source
> of truth for C#-side parity work only (§8 item 5b).

The `Z₂ᵏ` tower gauge: for a **distinguishable** cover the fiber-wise copy transposition is NOT an automorphism,
but the *matching* involution σ (copy `c ↔ τ(c)` simultaneously in every fiber, for a perfect matching τ on
copies) is. The C# builds τ per "direction" and uses it to peel; here it becomes more *consume generators* in
`foldSupply` — no peel, no recursion, the descent's own levels do the peeling.

C# mechanics to port (verified against source 2026-07-17):
1. **The copy graph** `F[a,b]` ⟺ copies `a ≠ b` are same-cell-adjacent within a fiber (C# uses fiber 0 — a
   choice; the Lean port must either take `F` from **every** fiber-seed or phrase it per-vertex through
   `relComp`, keeping the enumeration choice-free).
2. **Seed + propagation**: a parallel class is grown from a seed `F`-edge `(a₀, b₀)`: for a rung `x—y` (`y = τ x`)
   and side-edge `x—c`, set `τ c :=` the **unique** `d` with `F c d ∧ F y d ∧ ¬ F x d` (the induced-4-cycle rule);
   ambiguity, incompleteness, or inconsistency ⟹ reject the seed. Enumerate **all** seeds (C# dedups serialized
   τ's, ≤ log₂ s survive) — all-seeds is what keeps it choice-free in Lean.
3. **Two-colour check**: components of `F` minus τ-edges must be exactly 2, equal size, τ matching across.
   (Optional in Lean — it guards the *peel*; as a mere generator emitter, the involution + `IsColAut` gates
   already carry soundness, so the check is only a firing-quality filter.)
4. **The whole-graph involution**: `σ v :=` the unique same-cell-component partner of `v` in copy `τ(copy v)` —
   the same `uniqueMem`-shaped lookup `swapFun` already uses, so the reconstruction/equivariance proofs are the
   `swapCand` ones with τ in place of the two-copy swap.

Lean shape: extend `foldSupply`'s candidate list (or a `foldSupplyB`) with the τ-involutions; `GensEquivariant`
via the same membership-transport toolkit (`mem_relComp_transport`, `uniqueMem_transport`); firing theorem =
reconstruction under the matching geometry (mirror of `swapCand_eq_of_foldSwap` with a τ-indexed hypothesis).
**Witness to port**: the smallest C# `DoubleAndMatch` instance (a genuine s = 4 `Z₂²` tower where no plain
transposition verifies but the parallel-class σ does) — that is also the honest moment to port a multipede core.

### 9.3 What a fresh reader should NOT redo

- Do not re-derive the F1/F2 boundary: F1 provably needs a singleton on one side of every moved vertex
  (`CatchesAt`); the mirror-tied covers refute anything stronger — it is **measured**, `Regression` §10.
- Do not add a convergence/completeness proof for `relComp` OR for `deckSupply`'s `propagate` — nothing needs
  one (all statements are relative to the computed value); adding one buys no theorem.
- Do not try to make `foldSupply` catch the global mirror (reflection) — that is deliberate scope (§10); the
  mirror is `matchSupply`/F1's or F3's, at the node where it surfaces.
- Do not try to make `deckSupply` complete under **nontrivial seed stabilizers** (mirror-tied folds, per-copy
  twin gauges): ≥ 2 automorphism extensions make every forcing step on the moved class permanently ambiguous —
  no local rule can pick one, and picking is trap #7. The mirror-tied case is `foldSupply`'s (complementarity is
  guarded, `Regression` §11); the wreath case is outside the linear-over-a-ring leg.
- Do not "optimize" the Vector rounds back into a function-typed round or let-bound tables under a lambda — the
  exponential compounding is measured (2 rounds ≈ 1 s → 9 rounds > 300 s at n = 9). Data → data or nothing.
- The cost bills are **deliberately flat** (`|cell|²·n⁵`); tightening them is the same counting-lemma tranche as
  audit item 5 (no poly-c₂ theorem anywhere yet), not a per-supply chore.

---

## 10. ⚠ `foldSupply` is REFLECTION-BLIND — selector interaction, and a candidate witness (test later)

**The fact.** `foldSupply` certifies **copy-swap symmetry only**. An orbit that needs a non-copy-swap
automorphism — the global mirror ρ of the `vfold` family (1↔3 in every copy simultaneously) — is invisible to it:
the merged mirror class `{1,3} × copies` narrows only to the two `⟨copy-swaps⟩`-orbits (`{1_*}`, `{3_*}`), never
to 1. Force cannot help there either: the class is ONE `Aut`-orbit, and an equivariant key is constant on
`Aut`-orbits (`keyV_aut_invariant`). This is honest, documented behaviour — but it has a selector-level
consequence worth testing:

**The candidate selector-strict witness.** The sel-rewrite analysis (memory `project-sel-rewrite-2026-07-18`;
handoff §6.1) left "blind flags / fused answers at the SAME supply" open, estimating it needs SRG-land (n ≥ 25),
because with `matchSupply`-style supplies a pin-discretizing least cell self-resolves. `foldSupply` changes that
calculus: take a fold whose **least-coloured cell is the merged mirror class** — then
- **blind** (`Stall.guard`, targets least colour): `narrow` length 2 ⟹ **flags at the root**;
- **fused** (`selNode`, least *resolvable* colour): a pure copy-cell narrows to 1 ⟹ **selects it and proceeds**.
Same supply both sides, n ≈ 10–15. The sel analysis's defeater #2 (self-resolving pins) does not bite: the mirror
cell's pins do NOT discretize (1-WL is chirality-blind — their finding #3) and force cannot fire (one orbit).

**Test procedure (when picked up):** the colour order of `vfold2`/`vfold3` puts the pendant cell least (measured:
`branches = [4, 9]`), so tune the core so the mirror class ranks least — e.g. drop the pendant's degree-1
distinction or add decoration raising the other classes' colours — then compare
`canonForm? … (guard (forceThenConsume constKey foldSupply))` (expect `none`) against
`Select.canonFormS? … (selNode … constKey foldSupply)` (expect progress past the root; whether it *answers*
end-to-end depends on the deep mirror-pair cells — combining `foldSupply ++ matchSupply` generators is the
natural completion, and a supply-concatenation combinator is a trivial add). Caveat honestly: root-level
separation is the designed part; the full-descent claim needs the trace. If it lands, it closes the §6.1 open
witness at a quarter of the estimated size.
