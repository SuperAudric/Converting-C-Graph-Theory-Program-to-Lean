import ChainDescent.CaoTarget

/-!
# FT2b — the **runnable** 2-WL closure (`docs/chain-descent-cao-propagation.md` §15.4)

`CaoTarget.wl2` is a specification: `round2^[n²]` under `Function.iterate` over **function-typed**
intermediates, so evaluating it re-evaluates the whole tower. Measured at `n = 7`: two rounds in
seconds, three rounds not in 300 s. This file removes that, keeping the spec as the reference.

## The three costs, and what fixes each

| cost | in the spec | here |
|---|---|---|
| **colour lookup** | `c : Fin n × Fin n → Nat` is a closure tower `k` deep ⟹ `n^{3k}` | `PairVec` = `Vector (Vector Nat n) n`, `getP` is O(1) |
| **key recomputation** | `rankOf (pairKey c) p` recomputes **every** `pairKey c q` for **every** `p` ⟹ `n⁴` keys/round | keys computed **once** into `K`, read O(1) — this is the W-j defect, avoided by construction |
| **ranking** | `Finset.filter` over all `n²` pairs, per pair ⟹ `n⁴` key comparisons/round | rank against the `d` **distinct** keys (sorted + adjacent-deduped once) ⟹ `n²·d`, and `d` is the class count |
| **round count** | `n²` rounds, unconditionally | `iterFast` **exits at the fixpoint**, and `iterFast_eq` proves it equals the full iterate |

⟹ per round `O(n³ log n)` to build the keys, `O(n² log n)` to sort them, `O(n²·d)` to rank.

## ★ How it is tied to the spec — and why a PARTITION equation is the right one

`round2Fast` uses a **denser** renumbering than `round2` (`0..d-1` rather than "count of strictly
smaller keys"), so the two are **not** value-equal. They are tied by

> **`samePart_round2Fast`** — `SamePart (getP (round2Fast c)) (round2 (getP c))`

and that is exactly the level every theorem in FT1/FT2 is stated at (`SamePart`, `Refines`, `IsRound`,
and `Propagates`, whose content is a colour *equality* between two pairs). `samePart_wl2Fast` and
`samePart_extFast` carry it through the closure, and **`propagates_fast_iff`** transfers the target
itself. ⚠ A colour *value* here is meaningless on its own — only its kernel is ever read (that is
`PartitionClosure`'s premise), so this is a complete tie, not a weaker one.

⛔ **This is not a second object carrying an obligation.** Nothing is *proved* here that is not proved
of the spec; `round2Fast` is an implementation, tied by a proved equation, exactly as
`Refine.warmRefineVec` is tied to `Refine.warmRefineR` by `warmRefineVec_col_eq`.
⚠ **No `@[implemented_by]`** — that can assert a false equation and make `#eval` lie.

Axiom target `[propext, Classical.choice, Quot.sound]`.
-/

namespace ChainDescent
namespace CaoFast

open ChainDescent.PartitionClosure
open ChainDescent.CaoTarget

variable {n : Nat}

/-! ## 1. The materialized pair colouring -/

/-- A pair colouring as nested vectors — `getP` is O(1), which is the whole point. -/
abbrev PairVec (n : Nat) := Vector (Vector Nat n) n

/-- Read the colour of a pair. -/
def getP (c : PairVec n) (p : Fin n × Fin n) : Nat := (c[p.1])[p.2]

/-- Materialize a pair colouring. -/
def ofFnP (f : Fin n × Fin n → Nat) : PairVec n :=
  Vector.ofFn (fun i => Vector.ofFn (fun j => f (i, j)))

@[simp] theorem getP_ofFnP (f : Fin n × Fin n → Nat) (p : Fin n × Fin n) :
    getP (ofFnP f) p = f p := by
  simp [getP, ofFnP]

/-! ## 2. Ranking against the distinct keys

Correctness needs **only** that a pair's own key occurs in `D`. Sorting and deduplication are pure
performance — they shrink `D` from `n²` to the number of colour classes and cost nothing in proof. -/

/-- Remove adjacent duplicates. On a sorted list this is full deduplication, in one pass. -/
def dedupAdj : List (List Nat) → List (List Nat)
  | [] => []
  | [a] => [a]
  | a :: b :: t => if a = b then dedupAdj (b :: t) else a :: dedupAdj (b :: t)

theorem mem_dedupAdj_of_mem {a : List Nat} : ∀ {l : List (List Nat)}, a ∈ l → a ∈ dedupAdj l
  | [], h => by simp at h
  | [_], h => by simpa [dedupAdj] using h
  | b :: c :: t, h => by
      have hrec : a ∈ c :: t → a ∈ dedupAdj (c :: t) := mem_dedupAdj_of_mem
      by_cases hbc : b = c
      · have he : dedupAdj (b :: c :: t) = dedupAdj (c :: t) := by simp [dedupAdj, hbc]
        rw [he]
        rcases List.mem_cons.mp h with rfl | h'
        · exact hrec (by simp [hbc])
        · exact hrec h'
      · have he : dedupAdj (b :: c :: t) = b :: dedupAdj (c :: t) := by simp [dedupAdj, hbc]
        rw [he]
        rcases List.mem_cons.mp h with rfl | h'
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (hrec h')

/-- The rank of a key: how many **distinct** keys are strictly below it. -/
def denseRank (D : List (List Nat)) (x : List Nat) : Nat :=
  D.countP (fun d => Refine.keyLt d x)

theorem countP_le_of_imp {p q : List Nat → Bool} (h : ∀ a, p a = true → q a = true)
    (l : List (List Nat)) : l.countP p ≤ l.countP q := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.countP_cons, List.countP_cons]
      cases hp : p a with
      | true => rw [h a hp]; simp; omega
      | false => cases hq : q a with
        | true => simp; omega
        | false => simp; omega

/-- **★ The rank separates.** If `x` occurs in `D` and `x` is strictly below `y`, its rank is strictly
smaller — `x` itself is counted for `y` and not for `x`. Note this needs **no** `Nodup`, which is why
deduplication carries no proof obligation. -/
theorem denseRank_lt {D : List (List Nat)} {x y : List Nat}
    (hx : x ∈ D) (hxy : Refine.keyLt x y = true) : denseRank D x < denseRank D y := by
  have himp : ∀ a : List Nat, Refine.keyLt a x = true → Refine.keyLt a y = true :=
    fun a ha => Refine.keyLt_trans ha hxy
  unfold denseRank
  induction D with
  | nil => simp at hx
  | cons a t ih =>
      rw [List.countP_cons, List.countP_cons]
      rcases List.mem_cons.mp hx with rfl | hx'
      · rw [Refine.keyLt_irrefl _, hxy]
        have hle := countP_le_of_imp himp t
        simp
        omega
      · have ih' := ih hx'
        cases hp : Refine.keyLt a x with
        | true => rw [himp a hp]; simp; omega
        | false => cases hq : Refine.keyLt a y with
          | true => simp; omega
          | false => simp; omega

/-- **★★ The rank is injective on keys that occur.** -/
theorem denseRank_eq_iff {D : List (List Nat)} {x y : List Nat} (hx : x ∈ D) (hy : y ∈ D) :
    denseRank D x = denseRank D y ↔ x = y := by
  constructor
  · intro h
    by_contra hne
    rcases Refine.keyLt_of_ne hne with hlt | hgt
    · exact absurd h (Nat.ne_of_lt (denseRank_lt hx hlt))
    · exact absurd h.symm (Nat.ne_of_lt (denseRank_lt hy hgt))
  · intro h; rw [h]

/-! ## 3. One round, materialized -/

/-- Every pair index, row-major. -/
def allPairs (n : Nat) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap (fun i => (List.finRange n).map (fun j => (i, j)))

theorem mem_allPairs (p : Fin n × Fin n) : p ∈ allPairs n := by
  simp [allPairs, List.mem_flatMap]

/-! ### The key, computed without rebuilding the index list or boxing tuples

`pairKey (getP c)` is correct but pays three avoidable costs per pair: it rebuilds
`(Finset.univ : Finset (Fin n)).val` (an `O(n)` allocation, `n²` times), it allocates a tuple per
intermediate point before mapping `Nat.pair` over them, and it re-reads `c[p.1]` for every `x`.
`sigNats` takes the index list as a parameter, pairs directly, and hoists the row. -/

/-- The triangle types at `p` as bare `Nat`s, over a **supplied** index list, with `p.1`'s row hoisted. -/
def sigNats (c : PairVec n) (idx : List (Fin n)) (p : Fin n × Fin n) : List Nat :=
  let row := c[p.1]
  idx.map (fun x => Nat.pair (row[x]) ((c[x])[p.2]))

/-- The key, computed fast. -/
def keyFast (c : PairVec n) (idx : List (Fin n)) (p : Fin n × Fin n) : List Nat :=
  getP c p :: (sigNats c idx p).mergeSort (· ≤ ·)

/-- ★ **And it is the spec's key.** The only proof obligation the optimization creates. -/
theorem keyFast_eq (c : PairVec n) (p : Fin n × Fin n) :
    keyFast c (List.finRange n) p = pairKey (getP c) p := by
  show getP c p :: ((List.finRange n).map
      (fun x => Nat.pair (getP c (p.1, x)) (getP c (x, p.2)))).mergeSort (· ≤ ·)
    = getP c p :: Multiset.sort ((pairSig (getP c) p).map (fun t => Nat.pair t.1 t.2)) (· ≤ ·)
  congr 1
  show _ = Multiset.sort (Multiset.map (fun t => Nat.pair t.1 t.2)
      ((Finset.univ : Finset (Fin n)).val.map
        (fun x => (getP c (p.1, x), getP c (x, p.2))))) (· ≤ ·)
  rw [Multiset.map_map]
  rfl

/-- The key table — computed **once** per round. This is the W-j defect avoided by construction: the
spec's `rankOf` recomputes every key `n²` times. -/
def keyTable (c : PairVec n) : Vector (Vector (List Nat) n) n :=
  let idx := List.finRange n
  Vector.ofFn (fun i => Vector.ofFn (fun j => keyFast c idx (i, j)))

/-- Read the key table. Mirrors `getP`. -/
def keyAt (K : Vector (Vector (List Nat) n) n) (p : Fin n × Fin n) : List Nat := (K[p.1])[p.2]

@[simp] theorem keyAt_keyTable (c : PairVec n) (p : Fin n × Fin n) :
    keyAt (keyTable c) p = pairKey (getP c) p := by
  have : keyAt (keyTable c) p = keyFast c (List.finRange n) p := by
    simp [keyAt, keyTable]
  rw [this, keyFast_eq]

/-- The distinct keys present, sorted. Pure performance: `D` shrinks from `n²` to the class count.

⚠ It takes the **already-built** key table. Taking `c` instead would rebuild the table — the W-j
defect, and it cost a 2× before it was caught. -/
def distinctKeysOf (K : Vector (Vector (List Nat) n) n) : List (List Nat) :=
  dedupAdj (((allPairs n).map (keyAt K)).mergeSort Descend.lexLeList)

theorem mem_distinctKeysOf (K : Vector (Vector (List Nat) n) n) (p : Fin n × Fin n) :
    keyAt K p ∈ distinctKeysOf K := by
  refine mem_dedupAdj_of_mem ?_
  rw [(List.mergeSort_perm _ Descend.lexLeList).mem_iff]
  exact List.mem_map.mpr ⟨p, mem_allPairs p, rfl⟩

/-- **One 2-WL round, materialized.** -/
def round2Fast (c : PairVec n) : PairVec n :=
  let K := keyTable c
  let D := distinctKeysOf K
  ofFnP (fun p => denseRank D (keyAt K p))

theorem getP_round2Fast (c : PairVec n) (p : Fin n × Fin n) :
    getP (round2Fast c) p = denseRank (distinctKeysOf (keyTable c)) (keyAt (keyTable c) p) := by
  show getP (ofFnP (fun p => denseRank (distinctKeysOf (keyTable c)) (keyAt (keyTable c) p))) p = _
  rw [getP_ofFnP]

/-- The round's partition, in the same terms as `CaoTarget.round2_eq_iff`. -/
theorem round2Fast_eq_iff (c : PairVec n) (p q : Fin n × Fin n) :
    getP (round2Fast c) p = getP (round2Fast c) q ↔
      pairKey (getP c) p = pairKey (getP c) q := by
  rw [getP_round2Fast, getP_round2Fast,
      denseRank_eq_iff (mem_distinctKeysOf (keyTable c) p) (mem_distinctKeysOf (keyTable c) q),
      keyAt_keyTable, keyAt_keyTable]

/-- **★★★ THE TIE.** The materialized round has the same partition as the spec's round. -/
theorem samePart_round2Fast (c : PairVec n) :
    SamePart (getP (round2Fast c)) (round2 (getP c)) := by
  intro p q
  rw [round2Fast_eq_iff, round2_eq_iff]
  exact (pairKey_eq_iff (getP c) p q)

/-! ## 4. Iterating to the fixpoint -/

theorem samePart_iterate {a b : Col2 n} (h : SamePart a b) :
    ∀ k : Nat, SamePart ((round2 (n := n))^[k] a) ((round2 (n := n))^[k] b)
  | 0 => h
  | k + 1 => by
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      exact samePart_iterate (isRound_round2.congr h) k

/-- **Refine until nothing changes.** The colour vector is a fixpoint exactly when the partition
stabilizes, so this is an exact early exit — not an approximation. -/
def iterFast : Nat → PairVec n → PairVec n
  | 0, c => c
  | k + 1, c => let c' := round2Fast c; if c' = c then c else iterFast k c'

/-- **★ The early exit is sound**: it computes the full iterate. -/
theorem iterFast_eq : ∀ (k : Nat) (c : PairVec n), iterFast k c = (round2Fast (n := n))^[k] c
  | 0, _ => rfl
  | k + 1, c => by
      show (if round2Fast c = c then c else iterFast k (round2Fast c))
        = (round2Fast (n := n))^[k + 1] c
      by_cases h : round2Fast c = c
      · rw [if_pos h, Function.iterate_succ_apply, h, Function.iterate_fixed h]
      · rw [if_neg h, iterFast_eq k, Function.iterate_succ_apply]

/-- **★ THE RUNNABLE 2-WL CLOSURE.** -/
def wl2Fast (c : PairVec n) : PairVec n := iterFast (n * n) c

theorem samePart_iterFast : ∀ (k : Nat) (c : PairVec n),
    SamePart (getP ((round2Fast (n := n))^[k] c)) ((round2 (n := n))^[k] (getP c))
  | 0, _ => SamePart.refl _
  | k + 1, c => by
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      exact (samePart_iterFast k (round2Fast c)).trans
        (samePart_iterate (samePart_round2Fast c) k)

private theorem card_pair (n : Nat) : Fintype.card (Fin n × Fin n) = n * n := by
  simp

/-- **★★★ THE CLOSURE TIE.** The runnable closure has the same partition as `CaoTarget.wl2`. -/
theorem samePart_wl2Fast (c : PairVec n) : SamePart (getP (wl2Fast c)) (wl2 (getP c)) := by
  have hspec : wl2 (getP c) = (round2 (n := n))^[n * n] (getP c) := by
    unfold wl2 wl
    rw [card_pair]
  have hfast : wl2Fast c = (round2Fast (n := n))^[n * n] c := iterFast_eq (n * n) c
  rw [hspec, hfast]
  exact samePart_iterFast (n * n) c

/-! ## 5. The extension, and the target transferred -/

/-- The meet, materialized. -/
def meetVec (c d : PairVec n) : PairVec n := ofFnP (fun p => Nat.pair (getP c p) (getP d p))

@[simp] theorem getP_meetVec (c d : PairVec n) (p : Fin n × Fin n) :
    getP (meetVec c d) p = Nat.pair (getP c p) (getP d p) := by simp [meetVec]

/-- The 2-WL start colouring of a graph, materialized. -/
def initVec (adj : AdjMatrix n) : PairVec n := ofFnP (initCol2 adj)

/-- The one-point extension, runnable. -/
def extFast (c : PairVec n) (v : Fin n) : PairVec n :=
  wl2Fast (meetVec c (ofFnP (ptsPair v)))

/-- **★★★ THE EXTENSION TIE.** -/
theorem samePart_extFast (c : PairVec n) (v : Fin n) :
    SamePart (getP (extFast c v)) (ext (getP c) v) := by
  refine (samePart_wl2Fast _).trans (wl_congr isRound_round2 ?_)
  intro p q
  simp only [getP_meetVec, getP_ofFnP]
  rfl

/-- **★★★ THE TARGET, AT THE RUNNABLE OBJECT.** `Propagates` holds of the spec exactly when it holds
of what the machine computes — so a measurement on `extFast` is a measurement of the target. -/
theorem propagates_fast_iff {adj : AdjMatrix n} {χ : Colouring n} (c : PairVec n) :
    (∀ v u w : Fin n, getP (extFast c v) (v, u) = getP (extFast c v) (v, w) ↔
        CaoFibring.SameStabOrbit adj χ v u w) ↔ Propagates adj χ (getP c) := by
  constructor
  · intro h v u w
    exact ((samePart_extFast c v (v, u) (v, w)).symm).trans (h v u w)
  · intro h v u w
    exact (samePart_extFast c v (v, u) (v, w)).trans (h v u w)

end CaoFast
end ChainDescent
