/-
# ChainDescent/ClosureCalculus.lean — §13/§14 propagation-closure investigation
(Split out of `ChainDescent.lean`.) A self-contained development modelling warm-refinement propagation as a
candidate matroid / closure system. **Negative-result investigation**: `cl_prov` is a topological closure but
NOT a matroid (M3 refuted); nothing else in the project depends on it. Kept building for provenance.
-/
import ChainDescent

namespace ChainDescent

/-! ## §13 — propagation closure as a candidate matroid

Working development per [`docs/chain-descent-matroid.md`](../docs/chain-descent-matroid.md).
The goal is to model the propagation behaviour of warm refinement as a *matroid*
(or a slightly-weaker threshold structure) on the set of pair-guesses, then use
binary/non-binary classification as a polynomial Tier-2 detection scheme.

**The ground set `Egnd n`.** Canonical ordered pairs `(i, j)` with `i < j` —
equivalent to unordered pairs of distinct vertices, but with a fixed
orientation that makes the P-write antisymmetric. A "pair-guess" is an element
of `Egnd n`.

**The closure `cl S`.** Pairs whose endpoints are separated by warm refinement
after committing `S`'s pair-orderings.

**The four matroid axioms:**

* **M0 monotone** — `S ⊆ T → cl S ⊆ cl T` (more commits → finer partition)
* **M1 extensive** — `S ⊆ cl S` (a committed pair separates its endpoints)
* **M2 idempotent** — `cl (cl S) = cl S` (cross-cell commits don't refine further)
* **M3 exchange** — `y ∈ cl (S ∪ {x}) ∖ cl S → x ∈ cl (S ∪ {y}) ∖ cl S`

M0, M1, M2 are expected to be reachable from existing theorems plus moderate
helper lemmas; M3 is the load-bearing open claim. This section sets up the
definitions and statements; proofs in progress.
-/

/-- The canonical ground set: ordered pairs `(i, j)` with `i < j`. -/
def Egnd (n : Nat) : Set (Fin n × Fin n) := { p | p.1 < p.2 }

private theorem mem_Egnd {n : Nat} {p : Fin n × Fin n} : p ∈ Egnd n ↔ p.1 < p.2 :=
  Iff.rfl

private theorem Egnd_ne {n : Nat} {p : Fin n × Fin n} (hp : p ∈ Egnd n) : p.1 ≠ p.2 :=
  Fin.ne_of_lt hp

/-- Commit a set `S ⊆ Egnd n` of pair-guesses to a P-matrix: for each
`(u, v) ∈ S` write `P u v := less` and `P v u := greater`; leave other entries
unchanged.

If `S` is *not* canonical and contains both `(i, j)` and `(j, i)`, the
`less`-branch wins for `(i, j)` and is *also* picked for `(j, i)` — breaking
antisymmetry. Stick to `S ⊆ Egnd n` to avoid this. -/
noncomputable def Pof {n : Nat} (P₀ : PMatrix n) (S : Set (Fin n × Fin n)) :
    PMatrix n := fun i j =>
  haveI : Decidable ((i, j) ∈ S) := Classical.propDecidable _
  haveI : Decidable ((j, i) ∈ S) := Classical.propDecidable _
  if (i, j) ∈ S then .less
  else if (j, i) ∈ S then .greater
  else P₀ i j

/-- The propagation closure: pairs in the canonical ground set whose endpoints
are separated by warm refinement after committing `S`. -/
def cl {n : Nat} (adj : AdjMatrix n) (P₀ : PMatrix n)
    (χι : Colouring n) (S : Set (Fin n × Fin n)) : Set (Fin n × Fin n) :=
  { p | p ∈ Egnd n ∧
    warmRefine adj (Pof P₀ S) χι p.1 ≠ warmRefine adj (Pof P₀ S) χι p.2 }

/-! ### M1 — extensiveness

A pair-guess committed under fresh-colour individualisation has its endpoints
in distinct singleton cells, which warm refinement preserves. So the pair is
in `cl`. The fresh-colour hypothesis is the matroid-friendly individualisation
model already used by `warm_6_2` and `warmRefine_agree_off'`.
-/

/-- The fresh-colour hypothesis at a pair: both endpoints are `χι`-singletons. -/
def SingletonAt {n : Nat} (χι : Colouring n) (p : Fin n × Fin n) : Prop :=
  (∀ u, u ≠ p.1 → χι u ≠ χι p.1) ∧ (∀ u, u ≠ p.2 → χι u ≠ χι p.2)

/-- **M1 — extensiveness of `cl`.** For canonical `S` whose vertices are all
`χι`-singletons, every pair in `S` lies in `cl S`. -/
theorem cl_extensive {n : Nat} (adj : AdjMatrix n) (P₀ : PMatrix n)
    (χι : Colouring n) (S : Set (Fin n × Fin n))
    (hScanon : S ⊆ Egnd n)
    (hsing : ∀ p ∈ S, SingletonAt χι p) :
    S ⊆ cl adj P₀ χι S := by
  intro p hp
  refine ⟨hScanon hp, ?_⟩
  have hne : p.1 ≠ p.2 := Egnd_ne (hScanon hp)
  -- p.1 is a χι-singleton, so it stays a singleton under warm refinement.
  have h1 := (hsing p hp).1
  have hkeep := iterate_refineStep_preserves_singleton adj (Pof P₀ S) p.1 n χι h1
  -- warmRefine = iterate^[n]; hkeep p.2 (hne.symm) gives the inequality.
  intro heq
  exact hkeep p.2 hne.symm heq.symm

/-! ### M0 — monotonicity (the unhypothesised form is FALSE)

The naive M0 — `S ⊆ T → cl S ⊆ cl T`, for arbitrary `χι` — does **not** hold.

**Counterexample.** `n = 4`, `adj ≡ 0`, `χι ≡ 0`, `S = {(0,1)}`,
`T = {(0,1), (2,3)}`. Under `S`'s `P`-matrix the signatures at round 1 split
`0` from `2` (vertex 0 has a `.less` entry, vertex 2 has all `.unknown`).
Under `T`'s `P`-matrix the involution `(0 2)(1 3)` is an automorphism of
`(adj, P)`, so refineStep keeps `{0,2}` and `{1,3}` co-classed. So
`(0,2) ∈ cl S \ cl T` — adding `(2,3)` to `S` *destroys* the separation of `0`
and `2` by introducing a new symmetry.

**Diagnosis.** The closure operator on pair-guesses is not monotone in `S`
because more commits can introduce new automorphisms of `(adj, Pof S)`. A
single asymmetric commit (only `(0,1)`) breaks more symmetry than two
symmetric commits (`(0,1)` *and* `(2,3)`, jointly invariant under swap).

**Fresh-colour fix.** Individualising the endpoints of `T` to distinct
`χι`-singletons breaks the swap symmetry mechanically: vertices `0,1,2,3`
have distinct `χι` colours and stay singletons under iteration
(`iterate_refineStep_preserves_singleton`), so they cannot be merged by
refinement regardless of `Pof`. With that hypothesis, M0 is the natural
target.

We do not state a refuted `cl_monotone_unknown` in Lean (the unhypothesised
version is false, recorded here and in `docs/chain-descent-matroid.md`).
-/

/-- **Pof is entry-wise monotone in `S` when `P₀` decides nothing.** For the
all-unknown starting `P₀`, `S ⊆ T` (with `T` canonical) gives
`Pof P₀ S i j = .unknown ∨ Pof P₀ S i j = Pof P₀ T i j` at every entry. Pure
fact about `Pof` — does *not* extend to a `cl` monotonicity result, since the
warm refinement step is not monotone in `P` without the fresh-colour
hypothesis above. -/
private theorem Pof_mono_entry_of_unknown {n : Nat}
    {S T : Set (Fin n × Fin n)} (hST : S ⊆ T) (hTcanon : T ⊆ Egnd n)
    (i j : Fin n) :
    Pof (fun _ _ => POE.unknown) S i j = .unknown ∨
      Pof (fun _ _ => POE.unknown) S i j =
        Pof (fun _ _ => POE.unknown) T i j := by
  classical
  by_cases h1 : (i, j) ∈ S
  · right
    have h1T : (i, j) ∈ T := hST h1
    simp [Pof, h1, h1T]
  · by_cases h2 : (j, i) ∈ S
    · right
      have h2T : (j, i) ∈ T := hST h2
      have hji : j < i := hTcanon h2T
      have hijT : (i, j) ∉ T := fun h => absurd (hTcanon h) (lt_asymm hji)
      simp [Pof, h1, h2, hijT, h2T]
    · left
      simp [Pof, h1, h2]

/-! ### M0 (hypothesised) — attempt 1: every vertex individualised

The strongest reasonable hypothesis: `χι` makes *every* vertex of `Fin n` a
singleton (fully discrete starting partition). Under this, the warm-refined
partition is also fully discrete (singletons stay singletons), so `cl S` is
*all* canonical pairs for every `S`. Monotonicity is then vacuous: every `cl`
equals every other. The theorem holds but conveys no information about the
matroid structure.
-/

/-- A colouring is fully discrete: every vertex is a `χι`-singleton. -/
def FullyDiscrete {n : Nat} (χι : Colouring n) : Prop :=
  ∀ v u, u ≠ v → χι u ≠ χι v

/-- **M0 under the discrete hypothesis (trivial).** When `χι` is fully discrete,
every canonical pair lies in every `cl S` — so `cl S = Egnd n` for every `S` and
monotonicity is vacuous. Recorded for the record; provides no structural info. -/
theorem cl_monotone_discrete {n : Nat} (adj : AdjMatrix n) (P₀ : PMatrix n)
    (χι : Colouring n) (hχι : FullyDiscrete χι)
    {S T : Set (Fin n × Fin n)} (_hST : S ⊆ T) :
    cl adj P₀ χι S ⊆ cl adj P₀ χι T := by
  intro p hp
  refine ⟨hp.1, ?_⟩
  -- Under FullyDiscrete, p.1 and p.2 are χι-singletons; warm refinement
  -- preserves singletons, so their warm-refined colours stay distinct
  -- regardless of which P-matrix is used.
  have hne : p.1 ≠ p.2 := Egnd_ne hp.1
  have hsing : ∀ u, u ≠ p.1 → χι u ≠ χι p.1 := fun u hu => hχι p.1 u hu
  have hkeep :=
    iterate_refineStep_preserves_singleton adj (Pof P₀ T) p.1 n χι hsing
  intro heq
  exact hkeep p.2 hne.symm heq.symm

/-! ### M0 (hypothesised) — attempt 2: T-individualised

The real target: `χι` makes the vertices of `T` (the larger set) singletons,
but leaves vertices not in any `T`-pair unconstrained. Under this hypothesis
the M0 counterexample is killed (the swap symmetry across `T`'s pairs is broken
by distinct `χι`-colours on the `T`-vertices), but the closure is not vacuous —
non-`T` vertices can still merge into multi-vertex cells.

This is *not yet proved*; see the matroid doc for the proof obligation.
-/

/-- `χι`-singletons for every endpoint of every pair in `T`. -/
def TVerticesSingletons {n : Nat} (χι : Colouring n) (T : Set (Fin n × Fin n)) :
    Prop := ∀ p ∈ T, SingletonAt χι p

/-- **Strong form of M0 under T-individualised.** The partitions induced by
`Pof P₀ S` and `Pof P₀ T` warm-refinements *coincide* (`samePartition`) when
`S ⊆ T` and `χι` makes every endpoint of every `T`-pair a singleton.

Mechanism in three pieces:
1. `T`-endpoints are `χι`-singletons (hypothesis) and stay singletons under
   either refinement (`iterate_refineStep_preserves_singleton`), so any pair
   `(i, j)` with `i` or `j` a `T`-endpoint is vacuously `samePartition`-equal
   on both sides (both False ↔ both False).
2. For `(i, j)` with neither endpoint in any `T`-pair, `Pof P₀ S` and
   `Pof P₀ T` agree on rows `i` and `j` (no commit in `S ⊆ T` touches a
   non-`T`-endpoint), so the signatures at `i` and `j` are literally equal
   when computed against the same colouring.
3. `signature_eq_of_samePartition` plus the inductive hypothesis transports
   the signature-equality between `χ_S^k` and `χ_T^k`.

Stronger than monotonicity: `cl S = cl T` under this hypothesis. -/
theorem warmRefine_samePartition_T_individualised {n : Nat} (adj : AdjMatrix n)
    (P₀ : PMatrix n) (χι : Colouring n)
    {S T : Set (Fin n × Fin n)} (hST : S ⊆ T)
    (hsing : TVerticesSingletons χι T) :
    samePartition (warmRefine adj (Pof P₀ S) χι)
                  (warmRefine adj (Pof P₀ T) χι) := by
  suffices key : ∀ k, samePartition
      ((refineStep adj (Pof P₀ S))^[k] χι)
      ((refineStep adj (Pof P₀ T))^[k] χι) from key n
  intro k
  induction k with
  | zero => exact samePartition.refl χι
  | succ k ih =>
    intro i j
    simp only [Function.iterate_succ', Function.comp_apply]
    rw [refineStep_iff, refineStep_iff]
    set χ_S := (refineStep adj (Pof P₀ S))^[k] χι
    set χ_T := (refineStep adj (Pof P₀ T))^[k] χι
    by_cases hij : i = j
    · subst hij; simp
    · -- Helper: vertex v in some T-pair is a χι-singleton; iterate preserves.
      have h_singleton : ∀ v : Fin n, (∃ p ∈ T, p.1 = v ∨ p.2 = v) →
          (∀ u, u ≠ v → χ_S u ≠ χ_S v) ∧ (∀ u, u ≠ v → χ_T u ≠ χ_T v) := by
        rintro v ⟨p, hpT, hv⟩
        have hv_χι : ∀ u, u ≠ v → χι u ≠ χι v := by
          rcases hv with rfl | rfl
          · exact (hsing p hpT).1
          · exact (hsing p hpT).2
        exact ⟨iterate_refineStep_preserves_singleton adj (Pof P₀ S) v k χι hv_χι,
               iterate_refineStep_preserves_singleton adj (Pof P₀ T) v k χι hv_χι⟩
      -- Helper: for v not in any T-pair, Pof S and Pof T agree on v's row.
      have h_Pof_eq : ∀ v : Fin n, (¬ ∃ p ∈ T, p.1 = v ∨ p.2 = v) →
          ∀ u, Pof P₀ S v u = Pof P₀ T v u := by
        intro v hv u
        classical
        simp only [Pof]
        have h1T : (v, u) ∉ T := fun h => hv ⟨(v, u), h, Or.inl rfl⟩
        have h2T : (u, v) ∉ T := fun h => hv ⟨(u, v), h, Or.inr rfl⟩
        have h1S : (v, u) ∉ S := fun h => h1T (hST h)
        have h2S : (u, v) ∉ S := fun h => h2T (hST h)
        simp [h1S, h1T, h2S, h2T]
      -- Case analysis: i in T-pair / j in T-pair / neither.
      by_cases hi_T : ∃ p ∈ T, p.1 = i ∨ p.2 = i
      · obtain ⟨hSi, hTi⟩ := h_singleton i hi_T
        refine ⟨fun h => ?_, fun h => ?_⟩
        · exact absurd h.1 (fun e => hSi j (Ne.symm hij) e.symm)
        · exact absurd h.1 (fun e => hTi j (Ne.symm hij) e.symm)
      · by_cases hj_T : ∃ p ∈ T, p.1 = j ∨ p.2 = j
        · obtain ⟨hSj, hTj⟩ := h_singleton j hj_T
          refine ⟨fun h => ?_, fun h => ?_⟩
          · exact absurd h.1 (fun e => hSj i hij e)
          · exact absurd h.1 (fun e => hTj i hij e)
        · -- Main case: i, j not in any T-pair.
          have hPi := h_Pof_eq i hi_T
          have hPj := h_Pof_eq j hj_T
          have hSigi : signature adj (Pof P₀ S) χ_T i
              = signature adj (Pof P₀ T) χ_T i := by
            unfold signature
            apply Multiset.map_congr rfl
            intro u _
            rw [hPi u]
          have hSigj : signature adj (Pof P₀ S) χ_T j
              = signature adj (Pof P₀ T) χ_T j := by
            unfold signature
            apply Multiset.map_congr rfl
            intro u _
            rw [hPj u]
          rw [ih i j, signature_eq_of_samePartition adj (Pof P₀ S) ih i j,
              hSigi, hSigj]

/-- **M0 under the T-individualised hypothesis.** The genuine M0 target,
provable. Follows immediately from the stronger `samePartition` result. -/
theorem cl_monotone_T_individualised {n : Nat} (adj : AdjMatrix n)
    (P₀ : PMatrix n) (χι : Colouring n)
    {S T : Set (Fin n × Fin n)} (hST : S ⊆ T)
    (hsing : TVerticesSingletons χι T) :
    cl adj P₀ χι S ⊆ cl adj P₀ χι T := by
  intro p hp
  refine ⟨hp.1, ?_⟩
  intro heq
  exact hp.2 ((warmRefine_samePartition_T_individualised adj P₀ χι hST hsing
    p.1 p.2).mpr heq)

/-! ### M2 — idempotence

`cl (cl S) = cl S`, under fresh-colour individualisation of *both* `S`'s
pairs and `cl S`'s pairs.

The proof reduces to the M0 strong form: applying
`warmRefine_samePartition_T_individualised` with `T = cl S` (the larger set)
gives `samePartition (warmRefine_S) (warmRefine_{cl S})`, hence the sets of
separated pairs literally coincide. The two-direction set equality is then
just unfolding the `samePartition`.

The hypothesis `∀ p ∈ S ∪ cl S, SingletonAt χι p` packages both the M1
hypothesis (for `S`) and the M0-strong hypothesis (for `cl S`).

**Note on the original M2 attempt.** An earlier formulation conjectured that
`cl_idempotent` holds without any individualisation hypothesis, via a per-
cell-symmetry argument (within-cell multisets stay equal after committing
cross-cell pairs). That argument is correct *under fresh colours* (which break
the would-be symmetries that wreck M0) but cannot be true unhypothesised —
the M0 counterexample (§13 above) is itself a witness that committing
cross-cell pairs *can* coarsen the partition when those cells contain
non-individualised vertices that can pair-swap.
-/

/-- **M2 — idempotence of `cl` under fresh-colour individualisation.** -/
theorem cl_idempotent {n : Nat} (adj : AdjMatrix n) (P₀ : PMatrix n)
    (χι : Colouring n) (S : Set (Fin n × Fin n))
    (hScanon : S ⊆ Egnd n)
    (hsing : ∀ p ∈ S ∪ cl adj P₀ χι S, SingletonAt χι p) :
    cl adj P₀ χι (cl adj P₀ χι S) = cl adj P₀ χι S := by
  have hsing_S : ∀ p ∈ S, SingletonAt χι p := fun p hp => hsing p (Or.inl hp)
  have hsing_cl : TVerticesSingletons χι (cl adj P₀ χι S) :=
    fun p hp => hsing p (Or.inr hp)
  have hSsubcl : S ⊆ cl adj P₀ χι S := cl_extensive adj P₀ χι S hScanon hsing_S
  have hsame := warmRefine_samePartition_T_individualised adj P₀ χι hSsubcl hsing_cl
  apply Set.ext
  intro p
  refine ⟨fun hp => ⟨hp.1, fun heq => hp.2 ((hsame p.1 p.2).mp heq)⟩,
          fun hp => ⟨hp.1, fun heq => hp.2 ((hsame p.1 p.2).mpr heq)⟩⟩

/-! ### Closure-system status of `cl` (negative result, 2026-05-23)

After investigating M0, M1, M2, M3 and additional standard closure axioms, the
finding is that **`cl` as defined here satisfies essentially no standard
closure-system axiom unhypothesised** — only extensiveness survives. Each
failure has an explicit witness (see
[`docs/chain-descent-matroid.md`](../docs/chain-descent-matroid.md) §6).

| Axiom | Unhypothesised | Witness against |
|-------|----------------|------------------|
| CL0 `cl(∅) = ∅` | ✓ under all-same χι | — |
| CL1 extensive `S ⊆ cl S` | ✓ for canonical `S` (conjectured, used as M1) | — |
| CL2 idempotent | ✗ | `S = {(0,1),(2,3)}` (4-vertex empty graph) |
| CL3 monotone | ✗ | `S = {(0,1)}, T = {(0,1),(2,3)}` |
| Matroid M3 exchange | ✗ | `S = {(0,1)}, x = (0,2), y = (2,3)` |
| Anti-exchange | ✗ | `S = ∅, x = (0,1), y = (0,2)` |
| Additivity `cl(S∪T) = cl S ∪ cl T` | ✗ | follows from monotone failure |
| **Subadditivity** `cl(S∪T) ⊆ cl S ∪ cl T` | ✗ | `S = {(0,2),(1,3)}, T = {(0,2),(1,4)}` |

So `cl` is in **no** standard closure-system family (topological closure,
matroid, convex geometry, polymatroid, Moore family, …). The matroid framing
is dead in its current form — see `docs/chain-descent-matroid.md` for the
full story and the proposed pivot to provenance-tracking closure.

**What survives, under fresh-colour:** when `χι` makes every endpoint of every
pair in the relevant set a singleton, M0–M2 hold (M0 and M2 actually hold as
*equalities*, not just `⊆`). M3 is vacuously true because the closure becomes
constant under that hypothesis. This is captured by `cl_extensive`,
`cl_monotone_T_individualised`, `cl_idempotent` (above). The closure is then
structurally degenerate — a rank-0 matroid where every element is a loop —
which is *trivially binary*, so it can't distinguish Tier-1 from Tier-2.
Documented for completeness; no Tier-2-detection power.

**M3 unhypothesised — concrete counterexample (kept as record).** With
`n = 4`, `adj ≡ 0`, `χι ≡ 0`, `S = {(0,1)}`, `x = (0,2)`, `y = (2,3)`: the
M3 premise holds (`y ∈ cl(S ∪ {x}) ∖ cl S`) but the conclusion's `x ∉ cl S`
clause fails — `(0,2) ∈ cl({(0,1)})`. Not encoded as a Lean refutation: although
`warmRefine` is computable, a `decide` would have to reduce the `n`-fold
refinement iterate (impractical), so the refutation would instead need
invariance-based equality arguments for the surviving direction. Manual
verification in `docs/chain-descent-matroid.md` §6.

**If matroid-like-structure work is revived in the future**, the natural
next object to study is `cl_prov` — closure tracking the *provenance* of
each forced relation back to a driving commit, in the style of strategy
doc §10's `DERIVED` records. That object likely satisfies the matroid
axioms (the binary case literally being `F_2`-linear-algebra on derived
relations), and is the right level for Tier-2 detection via binary-matroid
classification. §14 below tests the simplest such candidate.
-/

/-! ## §14 — Provenance closure (TC-based) — `cl_prov`

After §13's negative result on warm-refinement `cl`, the natural next layer
to test is **provenance closure** via transitive closure of the partial
order. This uses only TC propagation — no 1-WL cascade — so it captures
the "what does S transitively imply as an ordering?" question.

**Result** (this section): cl_prov is a **topological closure** (Kuratowski
CL0–CL3 hold) but **NOT a matroid** (M3 exchange fails — concrete
machine-checked counterexample `cl_prov_M3_false`).

**Implication.** Standard TC-based provenance gives a clean topological
closure structure but is insufficient for binary-matroid representability
(which would be needed for Tier-2 detection). Richer provenance — tracking
the `F_2`-linear-algebraic dependencies between commits and derived
relations, à la strategy doc §10 `DERIVED` records — would be needed, and
is significantly more modelling work. That extension is out of scope here.
-/

/-- A computable, Finset-based version of `Pof` (the Set-based one in §13
is `noncomputable`, blocking `decide`-checkable refutations). -/
def Pof_fs {n : Nat} (P₀ : PMatrix n) (S : Finset (Fin n × Fin n)) :
    PMatrix n := fun i j =>
  if (i, j) ∈ S then .less
  else if (j, i) ∈ S then .greater
  else P₀ i j

/-- All-unknown commits-to-matrix: shortcut for `Pof_fs (·,· ↦ .unknown) S`. -/
def commitsToP {n : Nat} (S : Finset (Fin n × Fin n)) : PMatrix n :=
  Pof_fs (fun _ _ => .unknown) S

/-- Provenance closure (TC-based). `cl_prov S` = canonical pair-guesses
whose direction is decided by transitive closure of `S`'s commits. -/
def cl_prov {n : Nat} (S : Finset (Fin n × Fin n)) : Finset (Fin n × Fin n) :=
  (Finset.univ : Finset (Fin n × Fin n)).filter fun p =>
    p.1.val < p.2.val ∧
      transitiveClose (commitsToP S) p.1 p.2 ≠ .unknown

/-! ### Helper lemmas for the closure axioms -/

/-- `closeStep` returns `.unknown` on the all-unknown matrix at every entry. -/
private theorem closeStep_unknown {n : Nat} (i j : Fin n) :
    closeStep (fun _ _ : Fin n => POE.unknown) i j = POE.unknown := by
  unfold closeStep
  simp

/-- The all-unknown matrix is a fixpoint of `closeStep`. -/
private theorem closeStep_unknown_fixpoint {n : Nat} :
    closeStep (fun _ _ : Fin n => POE.unknown) = fun _ _ => POE.unknown := by
  funext i j; exact closeStep_unknown i j

/-- `transitiveClose` of the all-unknown matrix is the all-unknown matrix. -/
private theorem transitiveClose_unknown {n : Nat} :
    transitiveClose (fun _ _ : Fin n => POE.unknown) = fun _ _ => POE.unknown := by
  unfold transitiveClose
  -- iterate^[n*n] of identity-on-unknown = identity-on-unknown
  have key : ∀ k, (closeStep^[k]) (fun _ _ : Fin n => POE.unknown)
      = fun _ _ => POE.unknown := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ', Function.comp_apply, ih,
                       closeStep_unknown_fixpoint]
  exact key (n * n)

/-! ### CL0–CL3 for `cl_prov` -/

/-- **CL0 — empty closure.** `cl_prov ∅ = ∅`. -/
theorem cl_prov_empty {n : Nat} : cl_prov (∅ : Finset (Fin n × Fin n)) = ∅ := by
  ext p
  refine ⟨fun hp => ?_, fun hp => absurd hp (by simp)⟩
  simp only [cl_prov, Finset.mem_filter] at hp
  have hP : commitsToP (∅ : Finset (Fin n × Fin n)) = fun _ _ => POE.unknown := by
    funext i j
    simp [commitsToP, Pof_fs]
  rw [hP, transitiveClose_unknown] at hp
  exact absurd rfl hp.2.2

/-- **CL1 — extensiveness.** For canonical `S`, every commit is decided
by TC (its direct `.less` write survives). -/
theorem cl_prov_extensive {n : Nat} (S : Finset (Fin n × Fin n))
    (hScanon : ∀ p ∈ S, p.1.val < p.2.val) :
    S ⊆ cl_prov S := by
  intro p hpS
  simp only [cl_prov, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨hScanon p hpS, ?_⟩
  -- Pof_fs S p.1 p.2 = .less since p ∈ S
  have hPof : commitsToP S p.1 p.2 = .less := by
    simp [commitsToP, Pof_fs, hpS]
  -- transitiveClose preserves .less by iterate_closeStep_keeps_less
  unfold transitiveClose
  rw [iterate_closeStep_keeps_less p.1 p.2 (n * n) (commitsToP S) hPof]
  decide

/-! ### M3 (matroid exchange) — REFUTED

The exchange axiom of matroid theory:
> `y ∈ cl(S ∪ {x}) ∖ cl(S) → x ∈ cl(S ∪ {y}) ∖ cl(S)`.

**Refuted.** With `n = 5`, `S = {(1,2), (3,4)}`, `x = (2,3)`, `y = (1,4)`:

- `y ∈ cl_prov(S ∪ {x})`: the chain `1 → 2 → 3 → 4` derives `(1,4)`. ✓
- `y ∉ cl_prov(S)`: `(1,2)` and `(3,4)` share no vertex, no chain. ✓
- `x ∉ cl_prov(S ∪ {y})`: `{(1,2), (3,4), (1,4)}` has no chain reaching
  `(2,3)` — none of `(2,?)` or `(?,3)` is decided. ✗

So cl_prov_TC is not a matroid. Machine-checked via `decide` on the
concrete 5-vertex instance.
-/

/-- Concrete counterexample: with `n=5`, `S = {(1,2), (3,4)}`,
`x = (2,3)`, `y = (1,4)`, the matroid exchange premise holds but the
conclusion's `x ∈ cl_prov(S ∪ {y})` clause fails. -/
theorem cl_prov_M3_false :
    let S : Finset (Fin 5 × Fin 5) := {(1, 2), (3, 4)}
    let x : Fin 5 × Fin 5 := (2, 3)
    let y : Fin 5 × Fin 5 := (1, 4)
    y ∈ cl_prov (S ∪ {x}) ∧
    y ∉ cl_prov S ∧
    x ∉ cl_prov (S ∪ {y}) := by
  decide

/-! ### Direction-monotonicity infrastructure for CL3 / CL2

Both CL3 and CL2 reduce to a "less-direction entry-mono" argument lifted
through `transitiveClose`. The naive "decidedness-only" mono fails because
`closeStep`'s `.less`-first tie-break can shift direction between two
related matrices. The fix is to carry **canonical-consistency** as a joint
invariant — under it, no pair can host both a `.less`-chain and a
`.greater`-chain, killing the bad case.

Both CL3 and CL2 filter to canonical pairs `i.val < j.val`, so we only
need the `.less` direction of mono throughout. -/

/-- A `.less`-chain in `P` from `i` to `j`: some intermediate `k` with
both edges `.less`. -/
def hasLessChain {n : Nat} (P : PMatrix n) (i j : Fin n) : Prop :=
  ∃ k : Fin n, P i k = .less ∧ P k j = .less

/-- A `.greater`-chain in `P` from `i` to `j`. -/
def hasGreaterChain {n : Nat} (P : PMatrix n) (i j : Fin n) : Prop :=
  ∃ k : Fin n, P i k = .greater ∧ P k j = .greater

/-- A `PMatrix` is **canonical-consistent** if every `.less` entry sits at
`i.val < j.val` and every `.greater` entry at `i.val > j.val`. -/
def CanConsistent {n : Nat} (P : PMatrix n) : Prop :=
  (∀ i j : Fin n, P i j = .less → i.val < j.val) ∧
  (∀ i j : Fin n, P i j = .greater → i.val > j.val)

/-- One-sided (`.less`) entry-wise mono. Sufficient for CL3 and CL2 since
both filter to canonical pairs. -/
def LessMono {n : Nat} (P Q : PMatrix n) : Prop :=
  ∀ i j : Fin n, P i j = .less → Q i j = .less

/-- Under canonical-consistency, no pair has both a `.less`-chain and a
`.greater`-chain (the chain endpoints' canonical ordering constraints
conflict). -/
private theorem canConsistent_no_conflict {n : Nat} {P : PMatrix n}
    (hP : CanConsistent P) (i j : Fin n)
    (hL : hasLessChain P i j) (hG : hasGreaterChain P i j) : False := by
  obtain ⟨k, hik, hkj⟩ := hL
  obtain ⟨m, him, hmj⟩ := hG
  have h1 : i.val < j.val := Nat.lt_trans (hP.1 i k hik) (hP.1 k j hkj)
  have h2 : j.val < i.val := Nat.lt_trans (hP.2 m j hmj) (hP.2 i m him)
  exact Nat.lt_irrefl _ (Nat.lt_trans h1 h2)

/-- **Classification of `commitsToP S i j`** based on `S`-membership.
Three mutually exclusive cases under canonical `S`. -/
private theorem commitsToP_classify {n : Nat} (S : Finset (Fin n × Fin n))
    (i j : Fin n) :
    (commitsToP S i j = .less ∧ (i, j) ∈ S) ∨
    (commitsToP S i j = .greater ∧ (i, j) ∉ S ∧ (j, i) ∈ S) ∨
    (commitsToP S i j = .unknown ∧ (i, j) ∉ S ∧ (j, i) ∉ S) := by
  by_cases h1 : (i, j) ∈ S
  · left
    refine ⟨?_, h1⟩
    simp [commitsToP, Pof_fs, h1]
  · by_cases h2 : (j, i) ∈ S
    · right; left
      refine ⟨?_, h1, h2⟩
      simp [commitsToP, Pof_fs, h1, h2]
    · right; right
      refine ⟨?_, h1, h2⟩
      simp [commitsToP, Pof_fs, h1, h2]

/-- `commitsToP` of a canonical `S` is canonical-consistent. -/
private theorem commitsToP_canConsistent {n : Nat} (S : Finset (Fin n × Fin n))
    (hScanon : ∀ p ∈ S, p.1.val < p.2.val) :
    CanConsistent (commitsToP S) := by
  refine ⟨?_, ?_⟩
  · intro i j h
    rcases commitsToP_classify S i j with ⟨_, hmem⟩ | ⟨heq, _⟩ | ⟨heq, _⟩
    · exact hScanon (i, j) hmem
    · rw [heq] at h; cases h
    · rw [heq] at h; cases h
  · intro i j h
    rcases commitsToP_classify S i j with ⟨heq, _⟩ | ⟨_, _, hmem⟩ | ⟨heq, _⟩
    · rw [heq] at h; cases h
    · exact hScanon (j, i) hmem
    · rw [heq] at h; cases h

/-! ### closeStep helpers -/

/-- `closeStep` never demotes a decided `.greater` entry. -/
private theorem closeStep_keeps_greater {n : Nat} (Q : PMatrix n) {i j : Fin n}
    (h : Q i j = .greater) : closeStep Q i j = .greater := by
  simp only [closeStep, h]

/-- Iterating `closeStep` preserves a `.greater` entry — once decided, frozen. -/
private theorem iterate_closeStep_keeps_greater {n : Nat} (i j : Fin n) :
    ∀ (k : Nat) (Q : PMatrix n), Q i j = .greater →
      ((closeStep^[k]) Q) i j = .greater := by
  intro k
  induction k with
  | zero => intro Q h; exact h
  | succ k ih =>
    intro Q h
    rw [Function.iterate_succ, Function.comp_apply]
    exact ih (closeStep Q) (closeStep_keeps_greater Q h)

/-- `closeStep` preserves any decided entry. -/
private theorem closeStep_decided {n : Nat} (P : PMatrix n) (i j : Fin n)
    (hP : P i j ≠ .unknown) : closeStep P i j = P i j := by
  cases hPij : P i j with
  | less    => exact closeStep_keeps_less P hPij
  | greater => exact closeStep_keeps_greater P hPij
  | unknown => exact absurd hPij hP

/-- `closeStep` at an `.unknown` entry, expanded. -/
private theorem closeStep_unknown_eq {n : Nat} (P : PMatrix n) (i j : Fin n)
    (hP : P i j = .unknown) :
    closeStep P i j =
      (if (List.finRange n).any
            (fun k => decide (P i k = .less) && decide (P k j = .less))
        then .less
        else if (List.finRange n).any
              (fun k => decide (P i k = .greater) && decide (P k j = .greater))
          then .greater
          else .unknown) := by
  unfold closeStep
  rw [hP]

/-- **Classification of `closeStep P i j`'s output for `.less` case.** -/
private theorem closeStep_eq_less_iff {n : Nat} (P : PMatrix n) (i j : Fin n) :
    closeStep P i j = .less ↔
      P i j = .less ∨ (P i j = .unknown ∧ hasLessChain P i j) := by
  constructor
  · intro h
    cases hPij : P i j with
    | less => left; rfl
    | greater =>
      rw [closeStep_keeps_greater P hPij] at h; cases h
    | unknown =>
      right
      refine ⟨rfl, ?_⟩
      rw [closeStep_unknown_eq P i j hPij] at h
      by_cases h1 : (List.finRange n).any
            (fun k => decide (P i k = .less) && decide (P k j = .less))
      · rw [List.any_eq_true] at h1
        obtain ⟨k, _, hk⟩ := h1
        rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hk
        exact ⟨k, hk.1, hk.2⟩
      · -- No .less-chain: closeStep outputs .greater or .unknown, not .less
        rw [if_neg h1] at h
        by_cases h2 : (List.finRange n).any
              (fun k => decide (P i k = .greater) && decide (P k j = .greater))
        · rw [if_pos h2] at h; cases h
        · rw [if_neg h2] at h; cases h
  · rintro (hP | ⟨hP, k, hik, hkj⟩)
    · exact closeStep_keeps_less P hP
    · rw [closeStep_unknown_eq P i j hP]
      have : (List.finRange n).any
            (fun k' => decide (P i k' = .less) && decide (P k' j = .less)) = true := by
        rw [List.any_eq_true]
        refine ⟨k, List.mem_finRange _, ?_⟩
        simp [hik, hkj]
      rw [if_pos this]

/-- A direction for `closeStep` outputs: if it's `.less` (or `.greater`),
the `.less`-chain (or `.greater`-chain) plus underlying `.less`/`.greater`
entries determine it. The `.greater` case below mirrors. -/
private theorem closeStep_eq_greater_iff {n : Nat} (P : PMatrix n) (i j : Fin n) :
    closeStep P i j = .greater ↔
      P i j = .greater ∨
        (P i j = .unknown ∧ ¬ hasLessChain P i j ∧ hasGreaterChain P i j) := by
  constructor
  · intro h
    cases hPij : P i j with
    | less => rw [closeStep_keeps_less P hPij] at h; cases h
    | greater => left; rfl
    | unknown =>
      right
      refine ⟨rfl, ?_, ?_⟩
      · -- No .less-chain
        intro ⟨k, hik, hkj⟩
        rw [closeStep_unknown_eq P i j hPij] at h
        have : (List.finRange n).any
              (fun k' => decide (P i k' = .less) && decide (P k' j = .less)) = true := by
          rw [List.any_eq_true]
          refine ⟨k, List.mem_finRange _, ?_⟩
          simp [hik, hkj]
        rw [if_pos this] at h; cases h
      · -- .greater-chain
        rw [closeStep_unknown_eq P i j hPij] at h
        by_cases h1 : (List.finRange n).any
              (fun k => decide (P i k = .less) && decide (P k j = .less))
        · rw [if_pos h1] at h; cases h
        · rw [if_neg h1] at h
          by_cases h2 : (List.finRange n).any
                (fun k => decide (P i k = .greater) && decide (P k j = .greater))
          · rw [List.any_eq_true] at h2
            obtain ⟨k, _, hk⟩ := h2
            rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hk
            exact ⟨k, hk.1, hk.2⟩
          · rw [if_neg h2] at h; cases h
  · rintro (hP | ⟨hP, hNoLess, k, hik, hkj⟩)
    · exact closeStep_keeps_greater P hP
    · rw [closeStep_unknown_eq P i j hP]
      have h_no_less : (List.finRange n).any
          (fun k' => decide (P i k' = .less) && decide (P k' j = .less)) = false := by
        rw [List.any_eq_false]
        intro k' _ hbad
        rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hbad
        exact hNoLess ⟨k', hbad.1, hbad.2⟩
      rw [if_neg (by rw [h_no_less]; decide)]
      have h_greater : (List.finRange n).any
          (fun k' => decide (P i k' = .greater) && decide (P k' j = .greater)) = true := by
        rw [List.any_eq_true]
        refine ⟨k, List.mem_finRange _, ?_⟩
        simp [hik, hkj]
      rw [if_pos h_greater]

/-- `closeStep` preserves canonical-consistency. -/
private theorem closeStep_canConsistent {n : Nat} {P : PMatrix n}
    (hP : CanConsistent P) : CanConsistent (closeStep P) := by
  refine ⟨?_, ?_⟩
  · intro i j hij
    rcases (closeStep_eq_less_iff P i j).mp hij with hLess | ⟨_, k, hik, hkj⟩
    · exact hP.1 i j hLess
    · exact Nat.lt_trans (hP.1 i k hik) (hP.1 k j hkj)
  · intro i j hij
    rcases (closeStep_eq_greater_iff P i j).mp hij with hGreat | ⟨_, _, k, hik, hkj⟩
    · exact hP.2 i j hGreat
    · exact Nat.lt_trans (hP.2 k j hkj) (hP.2 i k hik)

/-- Iterating `closeStep` preserves canonical-consistency. -/
private theorem iterate_closeStep_canConsistent {n : Nat} (P : PMatrix n)
    (hP : CanConsistent P) : ∀ k, CanConsistent ((closeStep^[k]) P) := by
  intro k
  induction k with
  | zero => exact hP
  | succ k ih =>
    rw [Function.iterate_succ', Function.comp_apply]
    exact closeStep_canConsistent ih

/-- `transitiveClose` preserves canonical-consistency. -/
private theorem transitiveClose_canConsistent {n : Nat} (P : PMatrix n)
    (hP : CanConsistent P) : CanConsistent (transitiveClose P) :=
  iterate_closeStep_canConsistent P hP (n * n)

/-- **Joint inductive step for `LessMono`.** Under canonical-consistency of
both matrices and `.less`-mono between them, `closeStep` preserves
`.less`-mono.

Threats to the `.less`-chain case: `Q i j = .greater` (ruled out by chain
+ canonical-consistency of `Q`) or a `Q .greater`-chain pre-empting the
tie-break (irrelevant — the if-chain prioritizes `.less`). -/
private theorem closeStep_lessMono {n : Nat} {P Q : PMatrix n}
    (hQ : CanConsistent Q) (hPQ : LessMono P Q) :
    LessMono (closeStep P) (closeStep Q) := by
  intro i j hLess
  rcases (closeStep_eq_less_iff P i j).mp hLess with hP | ⟨_, k, hik, hkj⟩
  · -- P i j = .less; transport to Q
    exact closeStep_keeps_less Q (hPQ i j hP)
  · -- P i j = .unknown with .less-chain through k
    have hQik : Q i k = .less := hPQ i k hik
    have hQkj : Q k j = .less := hPQ k j hkj
    -- Show closeStep Q i j = .less
    cases hQij : Q i j with
    | less    => exact closeStep_keeps_less Q hQij
    | greater =>
      exfalso
      have h_lt : i.val < j.val := Nat.lt_trans (hQ.1 i k hQik) (hQ.1 k j hQkj)
      have h_gt : j.val < i.val := hQ.2 i j hQij
      exact Nat.lt_irrefl _ (Nat.lt_trans h_lt h_gt)
    | unknown =>
      exact (closeStep_eq_less_iff Q i j).mpr (Or.inr ⟨hQij, k, hQik, hQkj⟩)

/-- Iterating `closeStep` preserves `.less`-mono. -/
private theorem iterate_closeStep_lessMono {n : Nat} {P Q : PMatrix n}
    (_ : CanConsistent P) (hQ : CanConsistent Q) (hPQ : LessMono P Q) :
    ∀ k, LessMono ((closeStep^[k]) P) ((closeStep^[k]) Q) := by
  intro k
  induction k with
  | zero => exact hPQ
  | succ k ih =>
    simp only [Function.iterate_succ', Function.comp_apply]
    exact closeStep_lessMono (iterate_closeStep_canConsistent Q hQ k) ih

/-- `transitiveClose` preserves `.less`-mono. -/
private theorem transitiveClose_lessMono {n : Nat} {P Q : PMatrix n}
    (hP : CanConsistent P) (hQ : CanConsistent Q) (hPQ : LessMono P Q) :
    LessMono (transitiveClose P) (transitiveClose Q) :=
  iterate_closeStep_lessMono hP hQ hPQ (n * n)

/-- Base case for CL3: under `S ⊆ T` both canonical,
`commitsToP S → commitsToP T` is `.less`-mono. -/
private theorem commitsToP_lessMono {n : Nat} {S T : Finset (Fin n × Fin n)}
    (hST : S ⊆ T) :
    LessMono (commitsToP S) (commitsToP T) := by
  intro i j h
  rcases commitsToP_classify S i j with ⟨_, hmem⟩ | ⟨heq, _⟩ | ⟨heq, _⟩
  · -- (i,j) ∈ S ⊆ T, so commitsToP T i j = .less
    rcases commitsToP_classify T i j with ⟨heqT, _⟩ | ⟨_, hnot, _⟩ | ⟨_, hnot, _⟩
    · exact heqT
    · exact absurd (hST hmem) hnot
    · exact absurd (hST hmem) hnot
  · rw [heq] at h; cases h
  · rw [heq] at h; cases h

/-! ### CL3 — monotonicity (proved) -/

/-- **CL3 — monotonicity.** For canonical `S ⊆ T`, `cl_prov S ⊆ cl_prov T`. -/
theorem cl_prov_monotone {n : Nat} {S T : Finset (Fin n × Fin n)}
    (hST : S ⊆ T) (hScanon : ∀ p ∈ S, p.1.val < p.2.val)
    (hTcanon : ∀ p ∈ T, p.1.val < p.2.val) :
    cl_prov S ⊆ cl_prov T := by
  intro p hp
  simp only [cl_prov, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  obtain ⟨hlt, hdec⟩ := hp
  refine ⟨hlt, ?_⟩
  have hCanS : CanConsistent (commitsToP S) := commitsToP_canConsistent S hScanon
  have hCanT : CanConsistent (commitsToP T) := commitsToP_canConsistent T hTcanon
  have hCanTCS : CanConsistent (transitiveClose (commitsToP S)) :=
    transitiveClose_canConsistent _ hCanS
  -- Under canonical-consistency, TC decided + p.1 < p.2 ⟹ TC value = .less
  have hLess : transitiveClose (commitsToP S) p.1 p.2 = .less := by
    cases h : transitiveClose (commitsToP S) p.1 p.2 with
    | less    => rfl
    | unknown => exact absurd h hdec
    | greater => exact absurd hlt (Nat.not_lt_of_lt (hCanTCS.2 p.1 p.2 h))
  -- Lift through LessMono
  have hLifted : LessMono (transitiveClose (commitsToP S))
                          (transitiveClose (commitsToP T)) :=
    transitiveClose_lessMono hCanS hCanT (commitsToP_lessMono hST)
  have hLessT : transitiveClose (commitsToP T) p.1 p.2 = .less :=
    hLifted p.1 p.2 hLess
  rw [hLessT]; decide

/-! ### TC idempotence (for CL2)

`closeStep` is monotone on decidedness: each entry transitions
`.unknown → .less/.greater` at most once. So after `n*n` rounds the iterate
has saturated. Argument via the strictly-decreasing potential
`numUnknown`. -/

/-- Number of `.unknown` entries in a `PMatrix`. -/
def numUnknown {n : Nat} (P : PMatrix n) : Nat :=
  ((Finset.univ : Finset (Fin n × Fin n)).filter
    (fun p => P p.1 p.2 = .unknown)).card

/-- `numUnknown ≤ n * n`. -/
private theorem numUnknown_le {n : Nat} (P : PMatrix n) : numUnknown P ≤ n * n := by
  unfold numUnknown
  calc _ ≤ (Finset.univ : Finset (Fin n × Fin n)).card :=
            Finset.card_filter_le _ _
    _ = n * n := by rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]

/-- The unknown set of `closeStep P` is contained in the unknown set of `P`. -/
private theorem closeStep_unknown_subset {n : Nat} (P : PMatrix n) :
    ((Finset.univ : Finset (Fin n × Fin n)).filter
        (fun p => closeStep P p.1 p.2 = .unknown)) ⊆
    ((Finset.univ : Finset (Fin n × Fin n)).filter
        (fun p => P p.1 p.2 = .unknown)) := by
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  by_contra hPp
  exact hPp (by rw [← closeStep_decided P p.1 p.2 hPp]; exact hp)

/-- If `closeStep P ≠ P`, then `numUnknown` strictly drops. -/
private theorem closeStep_numUnknown_lt {n : Nat} {P : PMatrix n}
    (hne : closeStep P ≠ P) : numUnknown (closeStep P) < numUnknown P := by
  -- Some pair where closeStep P differs from P
  have hExists : ∃ (p : Fin n × Fin n), closeStep P p.1 p.2 ≠ P p.1 p.2 := by
    by_contra hAll
    apply hne
    funext i j
    by_contra hne'
    exact hAll ⟨(i, j), hne'⟩
  obtain ⟨p, hpne⟩ := hExists
  have hPunk : P p.1 p.2 = .unknown := by
    by_contra hdec
    exact hpne (closeStep_decided P p.1 p.2 hdec)
  have hCSdec : closeStep P p.1 p.2 ≠ .unknown := by
    intro hUnk; apply hpne; rw [hUnk, hPunk]
  unfold numUnknown
  refine Finset.card_lt_card ?_
  refine ⟨closeStep_unknown_subset P, ?_⟩
  intro hSub
  have hp_in : p ∈ ((Finset.univ : Finset (Fin n × Fin n)).filter
      (fun p => P p.1 p.2 = .unknown)) := by
    simp [hPunk]
  have := hSub hp_in
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
  exact hCSdec this

/-- After `k` iterations of `closeStep`, either a fixed point has been
reached at some step `≤ k`, or `numUnknown` has dropped by at least `k`. -/
private theorem iterate_closeStep_progress {n : Nat} (P : PMatrix n) :
    ∀ k, (∃ j ≤ k, (closeStep^[j+1]) P = (closeStep^[j]) P) ∨
         numUnknown ((closeStep^[k]) P) + k ≤ numUnknown P := by
  intro k
  induction k with
  | zero => right; simp
  | succ k ih =>
    rcases ih with ⟨j, hj_le, hFix⟩ | hDrop
    · -- Already at fixed point at step j ≤ k → still at fixed point
      left; exact ⟨j, Nat.le_succ_of_le hj_le, hFix⟩
    · -- numUnknown drop ≥ k at step k. Either step k+1 reaches fixed point or strict drop.
      by_cases hFixAtK : (closeStep^[k+1]) P = (closeStep^[k]) P
      · left; exact ⟨k, Nat.le_succ k, hFixAtK⟩
      · right
        -- closeStep^[k+1] P = closeStep (closeStep^[k] P); the step from k to k+1 differs
        have hkStep : (closeStep^[k+1]) P = closeStep ((closeStep^[k]) P) := by
          rw [Function.iterate_succ' closeStep k, Function.comp_apply]
        have hStepNe : closeStep ((closeStep^[k]) P) ≠ (closeStep^[k]) P := by
          intro hAbs
          apply hFixAtK
          rw [hkStep, hAbs]
        have hLt : numUnknown (closeStep ((closeStep^[k]) P)) <
                    numUnknown ((closeStep^[k]) P) :=
          closeStep_numUnknown_lt hStepNe
        rw [hkStep]
        omega

/-- After `n*n` iterations, `closeStep` has reached a fixed point. -/
private theorem transitiveClose_is_fixpoint {n : Nat} (P : PMatrix n) :
    closeStep (transitiveClose P) = transitiveClose P := by
  unfold transitiveClose
  rcases iterate_closeStep_progress P (n * n) with ⟨j, hj_le, hFix⟩ | hDrop
  · -- fixed point at step j ≤ n*n; iterate it forward
    have hExt : ∀ m, (closeStep^[j+m]) P = (closeStep^[j]) P := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih =>
        rw [show j + (m + 1) = (j + m) + 1 from by omega,
            Function.iterate_succ' closeStep (j+m), Function.comp_apply, ih]
        -- now goal: closeStep ((closeStep^[j]) P) = (closeStep^[j]) P
        rw [← Function.comp_apply (f := closeStep), ← Function.iterate_succ' closeStep,
            hFix]
    have h1 : (closeStep^[n*n + 1]) P = (closeStep^[j]) P := by
      have := hExt (n * n + 1 - j)
      rw [show j + (n * n + 1 - j) = n * n + 1 from by omega] at this
      exact this
    have h2 : (closeStep^[n*n]) P = (closeStep^[j]) P := by
      have := hExt (n * n - j)
      rw [show j + (n * n - j) = n * n from by omega] at this
      exact this
    rw [show closeStep ((closeStep^[n*n]) P) = (closeStep^[n*n + 1]) P from by
        rw [Function.iterate_succ' closeStep (n*n), Function.comp_apply]]
    rw [h1, h2]
  · -- numUnknown ((closeStep^[n*n]) P) + n*n ≤ numUnknown P ≤ n*n
    --  ⟹ numUnknown ((closeStep^[n*n]) P) ≤ 0; but then... actually this branch
    -- still needs argument. The drop tells us many transitions happened; we
    -- still need that the NEXT step is a fixed point.
    -- Alternative: numUnknown P ≤ n*n, hDrop: numUnknown ((closeStep^[n*n]) P) + n*n ≤ numUnknown P
    -- So numUnknown ((closeStep^[n*n]) P) = 0 and numUnknown P = n*n.
    -- If numUnknown ((closeStep^[n*n]) P) = 0, no entry is .unknown, so closeStep is identity
    -- (closeStep on all-decided is identity).
    have hUnkZero : numUnknown ((closeStep^[n*n]) P) = 0 := by
      have hPle := numUnknown_le P
      omega
    -- closeStep on a matrix with no .unknown entries is identity
    apply funext; intro i
    apply funext; intro j
    by_cases hP : (closeStep^[n*n]) P i j = .unknown
    · -- Contradiction: numUnknown should include (i,j) but is 0
      exfalso
      have : (i, j) ∈ ((Finset.univ : Finset (Fin n × Fin n)).filter
          (fun p => (closeStep^[n*n]) P p.1 p.2 = .unknown)) := by simp [hP]
      have hCard : ((Finset.univ : Finset (Fin n × Fin n)).filter
          (fun p => (closeStep^[n*n]) P p.1 p.2 = .unknown)).card ≠ 0 :=
        Finset.card_ne_zero.mpr ⟨(i, j), this⟩
      exact hCard hUnkZero
    · exact closeStep_decided _ i j hP

/-- **TC idempotence.** -/
theorem transitiveClose_idempotent {n : Nat} (M : PMatrix n) :
    transitiveClose (transitiveClose M) = transitiveClose M := by
  have hFix : closeStep (transitiveClose M) = transitiveClose M :=
    transitiveClose_is_fixpoint M
  unfold transitiveClose at hFix ⊢
  exact iterate_closeStep_fix ((closeStep^[n*n]) M) hFix (n * n)

/-! ### CL2 — idempotence (proved) -/

/-- `cl_prov S` is canonical. -/
private theorem cl_prov_canonical {n : Nat} (S : Finset (Fin n × Fin n)) :
    ∀ p ∈ cl_prov S, p.1.val < p.2.val := by
  intro p hp
  simp only [cl_prov, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  exact hp.1

/-- `commitsToP (cl_prov S)` is `.less`-bounded by `transitiveClose
(commitsToP S)`. -/
private theorem commitsToP_cl_prov_lessMono {n : Nat} (S : Finset (Fin n × Fin n))
    (hScanon : ∀ p ∈ S, p.1.val < p.2.val) :
    LessMono (commitsToP (cl_prov S)) (transitiveClose (commitsToP S)) := by
  have hCanS : CanConsistent (commitsToP S) := commitsToP_canConsistent S hScanon
  have hCanTCS : CanConsistent (transitiveClose (commitsToP S)) :=
    transitiveClose_canConsistent _ hCanS
  intro i j h
  rcases commitsToP_classify (cl_prov S) i j with ⟨_, hmem⟩ | ⟨heq, _⟩ | ⟨heq, _⟩
  · -- (i,j) ∈ cl_prov S: extract hlt and hdec
    simp only [cl_prov, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    obtain ⟨hlt, hdec⟩ := hmem
    cases hTC : transitiveClose (commitsToP S) i j with
    | less    => rfl
    | unknown => exact absurd hTC hdec
    | greater => exact absurd hlt (Nat.not_lt_of_lt (hCanTCS.2 i j hTC))
  · rw [heq] at h; cases h
  · rw [heq] at h; cases h

/-- **CL2 — idempotence.** `cl_prov (cl_prov S) = cl_prov S`. -/
theorem cl_prov_idempotent {n : Nat} (S : Finset (Fin n × Fin n))
    (hScanon : ∀ p ∈ S, p.1.val < p.2.val) :
    cl_prov (cl_prov S) = cl_prov S := by
  apply Finset.Subset.antisymm
  · intro p hp
    simp only [cl_prov, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    obtain ⟨hlt, hdec⟩ := hp
    refine ⟨hlt, ?_⟩
    have hCanCl : CanConsistent (commitsToP (cl_prov S)) :=
      commitsToP_canConsistent (cl_prov S) (cl_prov_canonical S)
    have hCanS : CanConsistent (commitsToP S) := commitsToP_canConsistent S hScanon
    have hCanTCS : CanConsistent (transitiveClose (commitsToP S)) :=
      transitiveClose_canConsistent _ hCanS
    have hLess : LessMono (commitsToP (cl_prov S)) (transitiveClose (commitsToP S)) :=
      commitsToP_cl_prov_lessMono S hScanon
    have hLifted : LessMono (transitiveClose (commitsToP (cl_prov S)))
                            (transitiveClose (transitiveClose (commitsToP S))) :=
      transitiveClose_lessMono hCanCl hCanTCS hLess
    rw [transitiveClose_idempotent] at hLifted
    have hCanTCcl : CanConsistent (transitiveClose (commitsToP (cl_prov S))) :=
      transitiveClose_canConsistent _ hCanCl
    have hLessCl : transitiveClose (commitsToP (cl_prov S)) p.1 p.2 = .less := by
      cases h : transitiveClose (commitsToP (cl_prov S)) p.1 p.2 with
      | less    => rfl
      | unknown => exact absurd h hdec
      | greater => exact absurd hlt (Nat.not_lt_of_lt (hCanTCcl.2 p.1 p.2 h))
    have : transitiveClose (commitsToP S) p.1 p.2 = .less :=
      hLifted p.1 p.2 hLessCl
    rw [this]; decide
  · exact cl_prov_extensive (cl_prov S) (cl_prov_canonical S)

/-! ### Status summary

`cl_prov` (TC-based provenance closure):

| axiom | status |
|-------|--------|
| CL0 `cl_prov ∅ = ∅` | **proved** (`cl_prov_empty`) |
| CL1 extensive `S ⊆ cl_prov S` | **proved** for canonical S (`cl_prov_extensive`) |
| CL2 idempotent `cl_prov (cl_prov S) = cl_prov S` | **proved** (`cl_prov_idempotent`) |
| CL3 monotone `S ⊆ T → cl_prov S ⊆ cl_prov T` | **proved** (`cl_prov_monotone`) |
| **M3 exchange** | **REFUTED** by decide (`cl_prov_M3_false`) on `n=5`, `S={(1,2),(3,4)}`, `x=(2,3)`, `y=(1,4)` |

CL2/CL3 proved via direction-monotonicity (`LessMono`) lifted through
`transitiveClose` under joint canonical-consistency (`CanConsistent`).
The `closeStep` `.less`-first tie-break would shift direction in general,
but `canConsistent_no_conflict` rules out the bad case (a pair carrying
both a `.less`-chain and a `.greater`-chain) under canonical-consistency.
TC idempotence (`transitiveClose_idempotent`) is via a `numUnknown`
potential argument: each round strictly decreases the unknown count if not
at a fixed point, bounded by `n*n`.

M3's failure remains the decisive structural finding: **`cl_prov` is a
topological closure but not a matroid**, so it doesn't support binary-
matroid representability and the intended Tier-2 detection scheme. See
`docs/chain-descent-matroid.md` §8 for the closed-framework verdict.
-/


end ChainDescent
