# The fold/tower resolution — closing the F_k cover gap (native + tower, polynomial)

> ## STATUS (2026-07-17, created)
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

## 6. Polynomial accounting (per descent node; single guarded path ⟹ ≤ n+1 nodes)

| move | trigger | per-node cost | closes |
|---|---|---|---|
| F1 `partialMatchSupply d` | support half-discretized involution / any α with discretized support | `|table|²·n²`, `|table| = |cell|·n^d`, **`d` fixed small** (0–1 on folds) | symmetric folds over refinement-visible cores, any `k`; point-stabilizer cases beyond `deepMatchSupply` |
| F2 `foldSupply` | fiber/copy structure present | `O(n²) + O(s·n²)·(s²/2 + s log s)` | symmetric folds + Z_pᵏ gauge over **WL-blind** cores |
| F3 `ringKey` | recovered linear system solvable | Smith `poly(n)` + unit-group scan ≤ n | native arity ≤ n; tower peel depth ≤ n; **distinguishable ordering incl. odd-part ≥ 7** |

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

1. ✅ **F1** (`PartialMatch.lean` + Regression §8 guards) — this increment.
2. **F2** `foldSupply` — pure supply build, no contract changes; its demo family = folds of a multipede core
   (port `MultipedeGenerator`'s smallest instance to a Lean literal).
3. **F3** `ringKey` — after (or with) the `sel`/duplicate-refine signature change (handoff §6.1/§6.4), since a
   solve-derived key is exactly the look-ahead worth handing forward; Lean content = §11.12 P1 (extraction
   soundness) + P3 (solve iso-invariance) instantiated as `KeyEquivariant` + `KeySeparates`.
4. C# CRT peel (parity), then re-run the fold suite with a negative test for odd-part ≥ 7 **removed** (it should
   pass) — today that case has **no test at all**; add the failing case first as the red bar.
