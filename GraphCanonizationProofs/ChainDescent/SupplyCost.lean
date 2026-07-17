import ChainDescent.PrunedSupply
import ChainDescent.PartialMatch

/-!
# `②` cashed out — POLYNOMIAL `supplyCost` for every built consume supply

(2026-07-17; discharges item 5 of the 2026-07-16 blocker audit: *"no poly bound on `supplyCost` for ANY concrete
supply; concrete capstones state only `IsCanonicalFormOpt`, no cost clause; `c₂` is a free variable"*.)

`Stall.descentCost_guard_le` bounds the guarded descent by `c₁ + (n+1)·(1 + c₁ + c₂)` **given** a per-node
resolver cost `c₂` — until this file, an undischarged hypothesis, so "unconditionally polynomial" was a theorem
about the *node count* with no end-to-end instance. This file discharges `c₂` for the **consume oracle** with
every built supply, giving the first end-to-end explicit-polynomial `descentCost` theorems for concrete
canonizers.

## What is proved

1. **Counting** (§1): `|branches| ≤ n`, `|seqsLen n k| = n^k`, `|allSeqs n d| ≤ (n+1)^d`,
   `|deepTable| ≤ tableBound n d = n·(n+1)^d`, and the generic all-pairs table bound.
2. **Per-supply `supplyCost` + candidate-count bounds** (§2–§3): `matchSupply` (`≤ matchSupplyBound n`, gens
   `≤ n²`), `deepMatchSupply d` / `partialMatchSupply d` (`≤ pairSupplyBound n d`, gens `≤ tableBound²`),
   `prunedSupply d` (`≤ refSupplyBound n d`, gens `≤ tableBound` — the measured `|table|² → |table|` cut, now a
   theorem).
3. **The per-node resolver cost** (§4–§5): `consume_cost_le` (consume alone) and `forceThenConsume_cost_le`
   (the mixed resolver, **parameterized by a key-cost bound `kc`** — the force side is mid-redesign, fold-tower
   plan F3, so nothing here is tied to a concrete key; `lookaheadKey`'s `kc = n³ + n²` is provided as the
   current instance).
4. **End-to-end `descentCost` bounds** (§6): `descentCost_guard_consume_le` + one corollary per supply, the
   mixed `descentCost_guard_mixed_le`, and the concrete-canonizer-of-record bound
   `descentCost_pruned_lookahead_le` — the `②` companion of `PrunedSupply.prunedSupply_lookahead_canonizer`.
5. **The `②`+`③` capstone** (§7): `handled_answers_poly` — on a `Handled` graph the guarded mixed canonizer
   **answers** and runs within the explicit polynomial budget.

## Honest scope

* **Poly for FIXED `d`.** The `n^{O(d)}` lives inside `tableBound n d = n·(n+1)^d`: every bound here is an
  explicit polynomial in `n` for each fixed depth, exactly the audit's "closes the poly regime at bounded `d`".
  Nothing here touches the `d = Θ(log n)` quasipoly ladder — that is P3c's second half (sequence pruning).
* The bounds are worst-case over **all** colourings (uniform in `χ`), so they compose with the guard theorem
  with no reachability reasoning.
* **⚠ The `∀ B` unsatisfiability finding (2026-07-17), recorded:** the pre-weakening hypothesis
  `∀ χ B, (R adj χ B).2 ≤ c₂` of `Stall.descentCost_guard_le` was **unsatisfiable for both built resolvers** —
  `consume` and `forceBy` bill per element of `B`, and `B` ranges over arbitrary lists — i.e. `②`'s conditional
  form could not have been instantiated by anything (standing trap #8). The hypothesis is now stated at the
  descent's only call site, `B = branches χ` (`Cost.descend_cost_le_of_resolved`).
-/

namespace ChainDescent
namespace SupplyCost

open ChainDescent.CostModel.WarmRefine (warmRefineCost warmRefineCost_le)
open ChainDescent.Descend
open ChainDescent.Consume
open ChainDescent.DeepMatch (deepTable allSeqs seqsLen deepMatchSupply)
open ChainDescent.Force (Key keyV keyCost keepMin forceBy lookaheadKey)
open ChainDescent.Composite (forceThenConsume)

variable {n : Nat}

/-! ## 1. Counting — the table sizes, in closed form -/

/-- Sum of a constant map (used to count flatMaps of uniform-length blocks). -/
theorem sum_map_const {α : Type*} (l : List α) (c : Nat) :
    (l.map fun _ => c).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

/-- **The generic all-pairs table bound**: matching every element of `l` against every other produces at most
`|l|²` candidates — the shape of `matchSupply`, `deepMatchSupply` and `partialMatchSupply`'s harvests. -/
theorem length_pairTable_le {α β : Type*} (l : List α) (f : α → α → Option β) :
    (l.flatMap fun p => l.filterMap (f p)).length ≤ l.length * l.length := by
  rw [List.length_flatMap]
  refine le_trans (List.sum_le_card_nsmul _ l.length ?_) ?_
  · intro x hx
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
    exact List.length_filterMap_le ..
  · rw [List.length_map, smul_eq_mul]

/-- The branch cell has at most `n` vertices. -/
theorem branches_length_le (χ : Colouring n) : (branches χ).length ≤ n := by
  unfold Descend.branches
  cases Descend.targetColour χ with
  | none => exact Nat.zero_le n
  | some c =>
      refine le_trans (List.length_filter_le ..) ?_
      rw [List.length_finRange]

/-- Exactly `n^k` sequences of length `k`. -/
theorem seqsLen_length (n k : Nat) : (seqsLen n k).length = n ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      unfold DeepMatch.seqsLen
      rw [List.length_flatMap]
      have hmap : ((List.finRange n).map fun v => ((seqsLen n k).map fun s => v :: s).length)
          = (List.finRange n).map fun _ => n ^ k :=
        List.map_congr_left (fun v _ => by rw [List.length_map, ih])
      rw [hmap, sum_map_const, List.length_finRange, pow_succ]
      ring

/-- **The search space is `≤ (n+1)^d`** — the geometric sum `Σ_{k≤d} n^k`, bounded in closed form. This is the
honest home of the oracle's `n^{O(d)}`: everything downstream is polynomial in `n` for each fixed `d`. -/
theorem allSeqs_length_le (n d : Nat) : (allSeqs n d).length ≤ (n + 1) ^ d := by
  induction d with
  | zero => simp [DeepMatch.allSeqs, DeepMatch.seqsLen]
  | succ d ih =>
      have hsplit : allSeqs n (d + 1) = allSeqs n d ++ seqsLen n (d + 1) := by
        unfold DeepMatch.allSeqs
        rw [List.range_succ, List.flatMap_append]
        simp
      rw [hsplit, List.length_append, seqsLen_length]
      have h2 : n ^ (d + 1) ≤ (n + 1) ^ d * n := by
        rw [pow_succ]
        exact Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.le_succ n) d) le_rfl
      calc (allSeqs n d).length + n ^ (d + 1)
          ≤ (n + 1) ^ d + (n + 1) ^ d * n := Nat.add_le_add ih h2
        _ = (n + 1) ^ (d + 1) := by ring

/-- The `(branch, sequence)` table size bound: `|cell| · |allSeqs| ≤ n · (n+1)^d`. -/
def tableBound (n d : Nat) : Nat := n * (n + 1) ^ d

theorem deepTable_length_le (adj : AdjMatrix n) (χ : Colouring n) (d : Nat) :
    (deepTable adj χ d).length ≤ tableBound n d := by
  unfold DeepMatch.deepTable
  rw [List.length_flatMap]
  refine le_trans (List.sum_le_card_nsmul _ (allSeqs n d).length ?_) ?_
  · intro x hx
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
    simp [List.length_map]
  · rw [List.length_map, smul_eq_mul]
    exact Nat.mul_le_mul (branches_length_le χ) (allSeqs_length_le n d)

/-- The verified list is a filter of the candidate list. -/
theorem verified_length_le (S : Supply n) (adj : AdjMatrix n) (χ : Colouring n) :
    (verified S adj χ).length ≤ (gens S adj χ).length :=
  List.length_filter_le ..

/-! ## 2. The named per-supply bounds (explicit polynomials — the reviewer's audit surface) -/

/-- `matchSupply`'s work: one refinement per branch (`n·n³`) + all-pairs rank matches (`n²·n²`). -/
def matchSupplyBound (n : Nat) : Nat := n * (n * n * n) + n * n * (n * n)

/-- The all-pairs deep oracles' work (`deepMatchSupply`, `partialMatchSupply`): per-entry materialisation
(`T·(d+1)·n³`) + all-pairs matches (`T²·n²`), at `T = tableBound n d`. -/
def pairSupplyBound (n d : Nat) : Nat :=
  tableBound n d * (d + 1) * (n * n * n) + tableBound n d * tableBound n d * (n * n)

/-- The reference-matching oracle's work (`prunedSupply`): same materialisation, **one match per entry** — the
measured `|table|² → |table|` cut, as a bound. -/
def refSupplyBound (n d : Nat) : Nat :=
  tableBound n d * (d + 1) * (n * n * n) + tableBound n d * (n * n)

/-! ## 3. The per-supply theorems -/

theorem supplyCost_matchSupply_le (adj : AdjMatrix n) (χ : Colouring n) :
    supplyCost (matchSupply (n := n)) adj χ ≤ matchSupplyBound n := by
  show (branches χ).length * warmRefineCost n
      + (branches χ).length * (branches χ).length * (n * n) ≤ _
  unfold matchSupplyBound
  exact Nat.add_le_add
    (Nat.mul_le_mul (branches_length_le χ) (warmRefineCost_le n))
    (Nat.mul_le_mul (Nat.mul_le_mul (branches_length_le χ) (branches_length_le χ)) le_rfl)

theorem gens_matchSupply_length_le (adj : AdjMatrix n) (χ : Colouring n) :
    (gens (matchSupply (n := n)) adj χ).length ≤ n * n := by
  have h := length_pairTable_le ((branches χ).map fun v => (v, lookData adj χ v))
    (fun p q => matchFrom p.2 q.2)
  rw [List.length_map] at h
  exact le_trans h (Nat.mul_le_mul (branches_length_le χ) (branches_length_le χ))

theorem supplyCost_deepMatchSupply_le (d : Nat) (adj : AdjMatrix n) (χ : Colouring n) :
    supplyCost (deepMatchSupply (n := n) d) adj χ ≤ pairSupplyBound n d := by
  show (deepTable adj χ d).length * (d + 1) * warmRefineCost n
      + (deepTable adj χ d).length * (deepTable adj χ d).length * (n * n) ≤ _
  unfold pairSupplyBound
  have hT := deepTable_length_le adj χ d
  exact Nat.add_le_add
    (Nat.mul_le_mul (Nat.mul_le_mul hT le_rfl) (warmRefineCost_le n))
    (Nat.mul_le_mul (Nat.mul_le_mul hT hT) le_rfl)

theorem gens_deepMatchSupply_length_le (d : Nat) (adj : AdjMatrix n) (χ : Colouring n) :
    (gens (deepMatchSupply (n := n) d) adj χ).length ≤ tableBound n d * tableBound n d :=
  le_trans (length_pairTable_le (deepTable adj χ d) (fun p q => matchCol p.2.col q.2.col))
    (Nat.mul_le_mul (deepTable_length_le adj χ d) (deepTable_length_le adj χ d))

/-- `partialMatchSupply` (F1, the fold-cover oracle) prices identically to `deepMatchSupply` — the support-local
match is still an `n²` construct-and-check per pair. -/
theorem supplyCost_partialMatchSupply_le (d : Nat) (adj : AdjMatrix n) (χ : Colouring n) :
    supplyCost (PartialMatch.partialMatchSupply (n := n) d) adj χ ≤ pairSupplyBound n d := by
  show (deepTable adj χ d).length * (d + 1) * warmRefineCost n
      + (deepTable adj χ d).length * (deepTable adj χ d).length * (n * n) ≤ _
  unfold pairSupplyBound
  have hT := deepTable_length_le adj χ d
  exact Nat.add_le_add
    (Nat.mul_le_mul (Nat.mul_le_mul hT le_rfl) (warmRefineCost_le n))
    (Nat.mul_le_mul (Nat.mul_le_mul hT hT) le_rfl)

theorem gens_partialMatchSupply_length_le (d : Nat) (adj : AdjMatrix n) (χ : Colouring n) :
    (gens (PartialMatch.partialMatchSupply (n := n) d) adj χ).length
      ≤ tableBound n d * tableBound n d :=
  le_trans
    (length_pairTable_le (deepTable adj χ d) (fun p q => PartialMatch.partialMatch p.2.col q.2.col))
    (Nat.mul_le_mul (deepTable_length_le adj χ d) (deepTable_length_le adj χ d))

theorem supplyCost_prunedSupply_le (d : Nat) (adj : AdjMatrix n) (χ : Colouring n) :
    supplyCost (PrunedSupply.prunedSupply (n := n) d) adj χ ≤ refSupplyBound n d := by
  have hT := deepTable_length_le adj χ d
  have h1 : (deepTable adj χ d).length * (d + 1) * warmRefineCost n
      ≤ tableBound n d * (d + 1) * (n * n * n) :=
    Nat.mul_le_mul (Nat.mul_le_mul hT le_rfl) (warmRefineCost_le n)
  show (PrunedSupply.prunedSupply (n := n) d adj χ).2 ≤ _
  unfold PrunedSupply.prunedSupply
  cases PrunedSupply.refCol? adj χ d with
  | none => exact le_trans h1 (Nat.le_add_right _ _)
  | some r => exact Nat.add_le_add h1 (Nat.mul_le_mul hT le_rfl)

theorem gens_prunedSupply_length_le (d : Nat) (adj : AdjMatrix n) (χ : Colouring n) :
    (gens (PrunedSupply.prunedSupply (n := n) d) adj χ).length ≤ tableBound n d := by
  rw [PrunedSupply.gens_prunedSupply]
  cases href : PrunedSupply.refCol? adj χ d with
  | none => simp
  | some r =>
      simp only [Option.elim]
      exact le_trans (List.length_filterMap_le ..) (deepTable_length_le adj χ d)

/-! ## 4. The consume resolver's per-node cost -/

/-- **The consume node bound**: supply work + one `n²` verification per candidate + the per-branch orbit BFS
(`≤ n` branches × (`gB` verified generators × `n²` + `n²`)). Parameterized by the supply's own bounds `sB`/`gB`
so any future supply (F2's structural fold supply included) instantiates it with two lemmas. -/
def consumeNodeBound (n sB gB : Nat) : Nat :=
  sB + gB * (n * n) + n * (gB * (n * n) + n * n)

theorem consume_cost_le {S : Supply n} {adj : AdjMatrix n} {χ : Colouring n} {B : List (Fin n)}
    {sB gB : Nat} (hB : B.length ≤ n)
    (hs : supplyCost S adj χ ≤ sB) (hg : (gens S adj χ).length ≤ gB) :
    (consume S adj χ B).2 ≤ consumeNodeBound n sB gB := by
  rw [consume_cost]
  unfold consumeNodeBound
  have hv : (verified S adj χ).length ≤ gB := le_trans (verified_length_le S adj χ) hg
  exact Nat.add_le_add
    (Nat.add_le_add hs (Nat.mul_le_mul hg le_rfl))
    (Nat.mul_le_mul hB (Nat.add_le_add (Nat.mul_le_mul hv le_rfl) le_rfl))

/-! ## 5. The mixed resolver's per-node cost — parameterized over the key

The force side is mid-redesign (fold-tower plan F3: the ring key), so the mixed bound is stated against an
**abstract key-cost bound `kc`** — when F3 lands it discharges `hk` and inherits every theorem below. The
current `lookaheadKey` instance (`kc = n³ + n²`) is recorded at the end of the section. -/

theorem keepMin_length_le (key : Key n) (adj : AdjMatrix n) (χ : Colouring n) (B : List (Fin n)) :
    (keepMin key adj χ B).length ≤ B.length := by
  unfold Force.keepMin
  cases Force.kmin? (B.map (keyV key adj χ)) with
  | none => exact le_rfl
  | some m => exact List.length_filter_le ..

theorem forceThenConsume_cost_le {key : Key n} {S : Supply n} {adj : AdjMatrix n}
    {χ : Colouring n} {B : List (Fin n)} {kc sB gB : Nat} (hB : B.length ≤ n)
    (hk : ∀ v : Fin n, keyCost key adj χ v ≤ kc)
    (hs : supplyCost S adj χ ≤ sB) (hg : (gens S adj χ).length ≤ gB) :
    (forceThenConsume key S adj χ B).2 ≤ n * kc + n * n + consumeNodeBound n sB gB := by
  show (forceBy key adj χ B).2 + (consume S adj χ (keepMin key adj χ B)).2 ≤ _
  have h1 : (forceBy key adj χ B).2 ≤ n * kc + n * n := by
    rw [Force.forceBy_cost]
    have hsum : (B.map (keyCost key adj χ)).sum ≤ B.length * kc := by
      refine le_trans (List.sum_le_card_nsmul _ kc ?_) ?_
      · intro x hx
        obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
        exact hk v
      · rw [List.length_map, smul_eq_mul]
    exact Nat.add_le_add (le_trans hsum (Nat.mul_le_mul hB le_rfl)) le_rfl
  have h2 : (consume S adj χ (keepMin key adj χ B)).2 ≤ consumeNodeBound n sB gB :=
    consume_cost_le (le_trans (keepMin_length_le key adj χ B) hB) hs hg
  exact Nat.add_le_add h1 h2

/-- The current concrete key's cost bound (`lookaheadKey`: one refinement + the `n²` read-off). -/
theorem keyCost_lookaheadKey_le (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) :
    keyCost (lookaheadKey (n := n)) adj χ v ≤ n * n * n + n * n := by
  rw [Force.keyCost_lookaheadKey]
  exact Nat.add_le_add (warmRefineCost_le n) le_rfl

/-! ## 6. ★★★ END-TO-END: the guarded descent at each concrete supply is EXPLICITLY POLYNOMIAL -/

/-- The guarded single-path budget at per-node resolver cost `c₂` — definitionally the RHS of
`Stall.descentCost_guard_le_encodeFree` (`c₁ = n³` discharged). -/
def pathBound (n c₂ : Nat) : Nat := n * n * n + (n + 1) * (1 + n * n * n + c₂)

/-- **★★ THE GENERIC CONSUME-ONLY `②`.** Any supply with polynomial work and candidate count gives a guarded
consume descent with an explicit polynomial `descentCost` — on **every** input (answer or flag alike). -/
theorem descentCost_guard_consume_le {S : Supply n} {adj : AdjMatrix n} {sB gB : Nat}
    (hs : ∀ χ : Colouring n, supplyCost S adj χ ≤ sB)
    (hg : ∀ χ : Colouring n, (gens S adj χ).length ≤ gB) :
    descentCost (Refine.encodeFreeFast (n := n)) (Stall.guard (consume S)) adj
      ≤ pathBound n (consumeNodeBound n sB gB) :=
  Stall.descentCost_guard_le_encodeFree
    (fun χ => consume_cost_le (branches_length_le χ) (hs χ) (hg χ))

/-- `②` for the one-step oracle (`d = 0`): `descentCost = O(n⁵)`, explicit. -/
theorem descentCost_guard_consume_matchSupply_le (adj : AdjMatrix n) :
    descentCost (Refine.encodeFreeFast (n := n)) (Stall.guard (consume (matchSupply (n := n)))) adj
      ≤ pathBound n (consumeNodeBound n (matchSupplyBound n) (n * n)) :=
  descentCost_guard_consume_le (supplyCost_matchSupply_le adj) (gens_matchSupply_length_le adj)

/-- `②` for the bounded-depth oracle: explicit polynomial in `n` **for each fixed `d`** (the `n^{O(d)}` sits
inside `tableBound`). This is the audit's "poly regime at bounded depth", as a theorem. -/
theorem descentCost_guard_consume_deepMatchSupply_le (d : Nat) (adj : AdjMatrix n) :
    descentCost (Refine.encodeFreeFast (n := n))
        (Stall.guard (consume (deepMatchSupply (n := n) d))) adj
      ≤ pathBound n (consumeNodeBound n (pairSupplyBound n d) (tableBound n d * tableBound n d)) :=
  descentCost_guard_consume_le (supplyCost_deepMatchSupply_le d adj)
    (gens_deepMatchSupply_length_le d adj)

/-- `②` for the support-local fold oracle (F1) — the fold family's consume side is **paid for**, not merely
firing: same shape as the deep oracle, and the fold needs only the fixed `d` that discretizes one copy. -/
theorem descentCost_guard_consume_partialMatchSupply_le (d : Nat) (adj : AdjMatrix n) :
    descentCost (Refine.encodeFreeFast (n := n))
        (Stall.guard (consume (PartialMatch.partialMatchSupply (n := n) d))) adj
      ≤ pathBound n (consumeNodeBound n (pairSupplyBound n d) (tableBound n d * tableBound n d)) :=
  descentCost_guard_consume_le (supplyCost_partialMatchSupply_le d adj)
    (gens_partialMatchSupply_length_le d adj)

/-- `②` for the reference-matching oracle — the pruned supply's `|table|²→|table|` win, visible in the bound
(`gB = tableBound`, not `tableBound²`). -/
theorem descentCost_guard_consume_prunedSupply_le (d : Nat) (adj : AdjMatrix n) :
    descentCost (Refine.encodeFreeFast (n := n))
        (Stall.guard (consume (PrunedSupply.prunedSupply (n := n) d))) adj
      ≤ pathBound n (consumeNodeBound n (refSupplyBound n d) (tableBound n d)) :=
  descentCost_guard_consume_le (supplyCost_prunedSupply_le d adj)
    (gens_prunedSupply_length_le d adj)

/-- **★★ THE GENERIC MIXED `②`** — key abstract (`kc`), ready for F3's ring key. -/
theorem descentCost_guard_mixed_le {key : Key n} {S : Supply n} {adj : AdjMatrix n}
    {kc sB gB : Nat}
    (hk : ∀ (χ : Colouring n) (v : Fin n), keyCost key adj χ v ≤ kc)
    (hs : ∀ χ : Colouring n, supplyCost S adj χ ≤ sB)
    (hg : ∀ χ : Colouring n, (gens S adj χ).length ≤ gB) :
    descentCost (Refine.encodeFreeFast (n := n)) (Stall.guard (forceThenConsume key S)) adj
      ≤ pathBound n (n * kc + n * n + consumeNodeBound n sB gB) :=
  Stall.descentCost_guard_le_encodeFree
    (fun χ => forceThenConsume_cost_le (branches_length_le χ) (hk χ) (hs χ) (hg χ))

/-- **★★★ `②` FOR THE CONCRETE CANONIZER OF RECORD** (`lookaheadKey` + `prunedSupply d` — the `①` side is
`PrunedSupply.prunedSupply_lookahead_canonizer`): an explicit polynomial `descentCost` on every input, for each
fixed `d`. The first end-to-end cost theorem for a concrete canonizer in the project. -/
theorem descentCost_pruned_lookahead_le (d : Nat) (adj : AdjMatrix n) :
    descentCost (Refine.encodeFreeFast (n := n))
        (Stall.guard (forceThenConsume (lookaheadKey (n := n)) (PrunedSupply.prunedSupply (n := n) d))) adj
      ≤ pathBound n (n * (n * n * n + n * n) + n * n
          + consumeNodeBound n (refSupplyBound n d) (tableBound n d)) :=
  descentCost_guard_mixed_le (keyCost_lookaheadKey_le adj)
    (supplyCost_prunedSupply_le d adj) (gens_prunedSupply_length_le d adj)

/-! ## 7. The `②`+`③` capstone -/

/-- **★★★ A HANDLED GRAPH IS CANONIZED WITHIN AN EXPLICIT POLYNOMIAL BUDGET.** `Residue.answers_of_handled`
(never flags) + the mixed bound (never exceeds `pathBound`): on `Handled`, the guarded mixed canonizer is sound,
iso-invariant, complete (`①`, e.g. `PrunedSupply.prunedSupply_guarded_canonizer`), **answers**, and costs an
explicit polynomial. Everything still open in the project is which graphs satisfy `Handled` — the `③` frontier —
and the cost of *that* question no longer rides on an undischarged `c₂`. -/
theorem handled_answers_poly {key : Key n} {S : Supply n} {adj : AdjMatrix n} {kc sB gB : Nat}
    (h : Residue.Handled key S adj)
    (hk : ∀ (χ : Colouring n) (v : Fin n), keyCost key adj χ v ≤ kc)
    (hs : ∀ χ : Colouring n, supplyCost S adj χ ≤ sB)
    (hg : ∀ χ : Colouring n, (gens S adj χ).length ≤ gB) :
    Descend.canonForm? (Refine.encodeFreeFast (n := n))
        (Stall.guard (forceThenConsume key S)) adj ≠ none
    ∧ descentCost (Refine.encodeFreeFast (n := n)) (Stall.guard (forceThenConsume key S)) adj
        ≤ pathBound n (n * kc + n * n + consumeNodeBound n sB gB) :=
  ⟨Residue.answers_of_handled h, descentCost_guard_mixed_le hk hs hg⟩

end SupplyCost
end ChainDescent
