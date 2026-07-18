import ChainDescent.PrunedSupply

/-!
# `P3c` SECOND HALF — `treeSupply`: collapsing the `n^d` sequence enumeration

`PrunedSupply.prunedSupply` killed the `|table|²` **pairing** (match from one discrete reference instead of every
pair). What it did **not** touch is the `n^d` *inside* `|table|`: the sequence enumeration itself still walks every
individualization sequence of length `≤ d`. This file closes that.

## The object

The search space is grown **level by level as a tree** over *entries* `(v, s)` (branch vertex + individualization
sequence), and each level is **orbit-pruned** by a supplied group `G`: an entry is dropped the moment it is
exhibited as `w · e` for an already-kept `e` and a `w` that is a **word in `G`**. Under localisation each level
collapses to a handful of orbit representatives (measured: `seqReps = 2` vs `|allSeqs 7 1| = 8`), so the cost
becomes a **sum over levels** rather than the product `n^d` — the quasipoly→poly ladder-break at `d = Θ(log n)`.

`G` comes from a **seed supply** and is completely **untrusted**: `treeSupply` reads it through `Consume.verified`,
so every element of `G` is a machine-checked automorphism *by construction*, and a junk seed costs pruning, never
correctness. (The intended instance is `prunedSupply (d-1)` — the group found one level shallower.)

## Why it is provable — and why it is NOT set-equality

⚠ The first half enjoyed **equal verified sets** (`PrunedSupply.verified_mem_iff`). **Sequence pruning breaks
that**: on `C₇`/`d=1` the kept entries yield only `10` of the `14` automorphisms of `D₇` — the missing `4` are
**words** of the kept ones. So this is a genuine **group-closure** argument, and it runs on three bricks:

1. **`exists_rep`** — every full-enumeration entry `(v, s)` reduces to a **kept** entry by a word in `G`
   (the tree induction: a dropped node's descendants are the `w`-images of the kept representative's).
2. **`OrbitPrune.matchCol_left_mul`** — `matchCol r (w · ψ) = w * matchCol r ψ`, so a dropped entry's candidate is
   `w * c` with `c` a **kept** candidate.
3. **`IsColAut`'s subgroup bricks** (`one`/`comp`/`inv`) — `w` is an automorphism (a word in verified generators),
   hence so is `c = w⁻¹ * g`, so the kept candidate is itself **verified** and available as a generator.

Then `Reaches` (§1) turns "`g` is a *product* of verified generators" into `WordReach`, which is the only channel
the descent reads a supply through — giving `OrbitPrune.SameOrbits` and, through it, `①`/`②`/`③` wholesale.

⛔ **Do NOT replace this with "keep one entry per `G`-orbit and match within the kept set".** That deletes exactly
the entry-vs-`G`-image matches the automorphisms are constructed from, so matches between distinct orbit
representatives yield only the identity. The pruning is a **tree** prune (nauty's shape): the kept set is matched
against the *reference*, and a pruned subtree's candidates survive as **conjugates/products** of kept ones.
-/

namespace ChainDescent
namespace TreePrune

open ChainDescent.Descend
open ChainDescent.Consume
  (Supply gens verified supplyCost rep WordReach IsColAut CellIsOrbit matchCol
   isColAut_of_mem_verified exists_targetColour_of_mem)
open ChainDescent.DeepMatch
  (deepTable deepMatchSupply deepCol deepData allSeqs mem_deepTable_iff deepTable_col
   matchCol_self_transport mem_allSeqs mem_allSeqs_map supplyEquivariant_deepMatchSupply)
open ChainDescent.Force (Key KeyEquivariant lookaheadKey keyEquivariant_lookahead)
open ChainDescent.Composite (forceThenConsume)
open ChainDescent.PrunedSupply
  (refCol? discrete_refCol refCol_eq_deepCol refCol_isSome_of_discrete mem_branches_of_isColAut
   exists_image_entry wordReach_congr_mem sameOrbits_of_verified_mem mem_gens_deepMatchSupply_raw)

variable {n : Nat}

/-! ## 1. Words in a generator list, and the reachability they give

`WordReach` is a *one-generator-at-a-time* relation. A pruned-away candidate is recovered as a **product**, so the
bridge from "`g` is a product of generators" to "`g` moves points inside a `WordReach` class" has to be built. -/

/-- `w` is a **product of elements of `G`** (the empty product is `1`). -/
inductive GWord (G : List (Equiv.Perm (Fin n))) : Equiv.Perm (Fin n) → Prop
  | one : GWord G 1
  | mul {g w : Equiv.Perm (Fin n)} (hg : g ∈ G) (hw : GWord G w) : GWord G (g * w)

theorem GWord.comp {G : List (Equiv.Perm (Fin n))} {a b : Equiv.Perm (Fin n)}
    (ha : GWord G a) (hb : GWord G b) : GWord G (a * b) := by
  induction ha with
  | one => simpa using hb
  | mul hg _ ih => rw [mul_assoc]; exact GWord.mul hg ih

/-- A word in **verified** generators is itself a colouring-preserving automorphism (`IsColAut.one`/`comp`). -/
theorem isColAut_of_gword {adj : AdjMatrix n} {χ : Colouring n} {G : List (Equiv.Perm (Fin n))}
    (hG : ∀ g ∈ G, IsColAut adj χ g) {w : Equiv.Perm (Fin n)} (hw : GWord G w) :
    IsColAut adj χ w := by
  induction hw with
  | one => exact IsColAut.one adj χ
  | mul hg _ ih => exact IsColAut.comp (hG _ hg) ih

/-- `g` moves **every** point within its `WordReach` class over `K` — i.e. `g` acts inside the orbit partition
that `K` proves. This is the property that is closed under products, and it is all the descent ever needs. -/
def Reaches (K : List (Equiv.Perm (Fin n))) (g : Equiv.Perm (Fin n)) : Prop :=
  ∀ u : Fin n, WordReach K u (g u)

theorem Reaches.one (K : List (Equiv.Perm (Fin n))) : Reaches K 1 := fun u => by
  show WordReach K u ((1 : Equiv.Perm (Fin n)) u)
  simpa using WordReach.refl u

theorem Reaches.gen {K : List (Equiv.Perm (Fin n))} {g : Equiv.Perm (Fin n)} (hg : g ∈ K) :
    Reaches K g := fun u => (WordReach.refl u).step hg

theorem Reaches.mul {K : List (Equiv.Perm (Fin n))} {a b : Equiv.Perm (Fin n)}
    (ha : Reaches K a) (hb : Reaches K b) : Reaches K (a * b) := fun u => by
  show WordReach K u (a (b u))
  exact (hb u).trans (ha (b u))

theorem Reaches.ofGWord {G K : List (Equiv.Perm (Fin n))} (hsub : ∀ g ∈ G, g ∈ K)
    {w : Equiv.Perm (Fin n)} (hw : GWord G w) : Reaches K w := by
  induction hw with
  | one => exact Reaches.one K
  | mul hg _ ih => exact Reaches.mul (Reaches.gen (hsub _ hg)) ih

/-- **★ THE BRIDGE.** If every generator of `K₁` acts inside `K₂`'s orbit partition, then `K₂` proves everything
`K₁` does. (`K₁`'s generators need not be *in* `K₂` — being **products** of `K₂`'s is enough.) -/
theorem wordReach_of_reaches {K₁ K₂ : List (Equiv.Perm (Fin n))}
    (h : ∀ g ∈ K₁, Reaches K₂ g) {u w : Fin n} (hr : WordReach K₁ u w) : WordReach K₂ u w := by
  induction hr with
  | refl => exact WordReach.refl _
  | step _ hg ih => exact ih.trans (h _ hg _)

/-! ## 2. The orbit-pruned search tree

Entries are `(branch vertex, individualization sequence)`. ⚠ The group acts on the **whole** entry — pruning the
sequence while holding the branch vertex fixed is *not* licensed, because `deepCol_aut` transports `v :: s` as a
unit. -/

/-- A search-tree node: a branch vertex plus the sequence individualized after it. -/
abbrev Entry (n : Nat) := Fin n × List (Fin n)

/-- The action of a permutation on an entry — the whole entry, vertex included. -/
def actEntry (g : Equiv.Perm (Fin n)) (e : Entry n) : Entry n := (g e.1, e.2.map g)

theorem actEntry_one (e : Entry n) : actEntry (1 : Equiv.Perm (Fin n)) e = e := by
  cases e; simp [actEntry]

theorem actEntry_mul (a b : Equiv.Perm (Fin n)) (e : Entry n) :
    actEntry a (actEntry b e) = actEntry (a * b) e := by
  cases e; simp [actEntry, List.map_map]

/-- All products of at most `K` generators. **Completeness is not needed for correctness** — a shorter word list
prunes less, never wrongly, because every drop carries its witness. -/
def wordsOf (G : List (Equiv.Perm (Fin n))) : Nat → List (Equiv.Perm (Fin n))
  | 0 => [1]
  | k + 1 => wordsOf G k ++ G.flatMap (fun g => (wordsOf G k).map (fun w => g * w))

theorem gword_of_mem_wordsOf (G : List (Equiv.Perm (Fin n))) :
    ∀ (k : Nat) (w : Equiv.Perm (Fin n)), w ∈ wordsOf G k → GWord G w := by
  intro k
  induction k with
  | zero => intro w hw; simp [wordsOf] at hw; subst hw; exact GWord.one
  | succ k ih =>
      intro w hw
      rcases List.mem_append.mp hw with h | h
      · exact ih w h
      · obtain ⟨g, hg, hmem⟩ := List.mem_flatMap.mp h
        obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hmem
        exact GWord.mul hg (ih w' hw')

/-- The pruning test: has this entry already been exhibited as a known-word image of a kept one? -/
def reducible (G : List (Equiv.Perm (Fin n))) (K : Nat) (kept : List (Entry n)) (e : Entry n) : Bool :=
  kept.any (fun t => (wordsOf G K).any (fun w => decide (e = actEntry w t)))

/-- One pruning pass: keep an entry unless it is a known-word image of one already kept. -/
def reduceStep (G : List (Equiv.Perm (Fin n))) (K : Nat) (acc : List (Entry n)) (e : Entry n) :
    List (Entry n) :=
  if reducible G K acc e then acc else acc ++ [e]

def entryReduce (G : List (Equiv.Perm (Fin n))) (K : Nat) (L : List (Entry n)) : List (Entry n) :=
  L.foldl (reduceStep G K) []

theorem foldl_subset (G : List (Equiv.Perm (Fin n))) (K : Nat) :
    ∀ (L acc : List (Entry n)), acc ⊆ L.foldl (reduceStep G K) acc := by
  intro L
  induction L with
  | nil => intro acc; exact fun _ h => h
  | cons e L ih =>
      intro acc
      refine fun x hx => ih (reduceStep G K acc e) ?_
      unfold reduceStep
      by_cases hr : reducible G K acc e
      · rw [if_pos hr]; exact hx
      · rw [if_neg hr]; exact List.mem_append.mpr (Or.inl hx)

theorem foldl_subset_append (G : List (Equiv.Perm (Fin n))) (K : Nat) :
    ∀ (L acc : List (Entry n)), L.foldl (reduceStep G K) acc ⊆ acc ++ L := by
  intro L
  induction L with
  | nil => intro acc; simpa using fun _ h => h
  | cons e L ih =>
      intro acc x hx
      have h := ih (reduceStep G K acc e) hx
      rcases List.mem_append.mp h with h' | h'
      · unfold reduceStep at h'
        by_cases hr : reducible G K acc e
        · rw [if_pos hr] at h'; exact List.mem_append.mpr (Or.inl h')
        · rw [if_neg hr] at h'
          rcases List.mem_append.mp h' with h'' | h''
          · exact List.mem_append.mpr (Or.inl h'')
          · simp at h''; subst h''; simp
      · exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ h'))

/-- `acc ⊆ reduceStep G K acc x` — the accumulator only ever grows. -/
theorem foldl_subset_cons (G : List (Equiv.Perm (Fin n))) (K : Nat) (acc : List (Entry n))
    (x : Entry n) {e : Entry n} (he : e ∈ acc) : e ∈ reduceStep G K acc x := by
  unfold reduceStep
  by_cases hr : reducible G K acc x
  · rw [if_pos hr]; exact he
  · rw [if_neg hr]; exact List.mem_append.mpr (Or.inl he)

/-- **★ THE PRUNING IS WITNESSED.** Everything fed to `entryReduce` is a known-word image of something kept. -/
theorem foldl_covers (G : List (Equiv.Perm (Fin n))) (K : Nat) :
    ∀ (L acc : List (Entry n)) (e : Entry n), (e ∈ acc ∨ e ∈ L) →
      ∃ t ∈ L.foldl (reduceStep G K) acc, ∃ w, GWord G w ∧ e = actEntry w t := by
  intro L
  induction L with
  | nil =>
      rintro acc e (he | he)
      · exact ⟨e, he, 1, GWord.one, (actEntry_one e).symm⟩
      · exact absurd he (List.not_mem_nil)
  | cons x L ih =>
      rintro acc e (he | he)
      · exact ih (reduceStep G K acc x) e
          (Or.inl (foldl_subset_cons G K acc x he))
      · rcases List.mem_cons.mp he with rfl | he'
        · by_cases hr : reducible G K acc e
          · obtain ⟨t, ht, hw⟩ := List.any_eq_true.mp hr
            obtain ⟨w, hwmem, hwe⟩ := List.any_eq_true.mp hw
            refine ⟨t, ?_, w, gword_of_mem_wordsOf G K w hwmem, of_decide_eq_true hwe⟩
            exact foldl_subset G K L _ (by unfold reduceStep; rw [if_pos hr]; exact ht)
          · refine ih (reduceStep G K acc e) e (Or.inl ?_)
            unfold reduceStep; rw [if_neg hr]; simp
        · exact ih (reduceStep G K acc x) e (Or.inr he')

theorem entryReduce_covers (G : List (Equiv.Perm (Fin n))) (K : Nat) {L : List (Entry n)}
    {e : Entry n} (he : e ∈ L) :
    ∃ t ∈ entryReduce G K L, ∃ w, GWord G w ∧ e = actEntry w t :=
  foldl_covers G K L [] e (Or.inr he)

theorem entryReduce_subset (G : List (Equiv.Perm (Fin n))) (K : Nat) (L : List (Entry n)) :
    entryReduce G K L ⊆ L := by
  intro x hx
  have := foldl_subset_append G K L [] hx
  simpa using this

/-- **The pruned search tree, level by level.** Level `0` is the branch cell (already orbit-pruned — the `v`-side
prune); level `k+1` extends each **kept** level-`k` entry by every vertex and prunes again. Descendants of a
dropped node are never generated: they are the `w`-images of the kept representative's descendants. -/
def entryLevels (G : List (Equiv.Perm (Fin n))) (K : Nat) (χ : Colouring n) : Nat → List (Entry n)
  | 0 => entryReduce G K ((branches χ).map (fun v => (v, [])))
  | k + 1 => entryReduce G K ((entryLevels G K χ k).flatMap
      (fun e => (List.finRange n).map (fun x => (e.1, e.2 ++ [x]))))

/-- Every entry the tree keeps is a genuine `(branch, sequence of that length)` pair. -/
theorem entryLevels_spec (G : List (Equiv.Perm (Fin n))) (K : Nat) (χ : Colouring n) :
    ∀ (k : Nat) (e : Entry n), e ∈ entryLevels G K χ k → e.1 ∈ branches χ ∧ e.2.length = k := by
  intro k
  induction k with
  | zero =>
      intro e he
      have := entryReduce_subset G K _ he
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp this
      exact ⟨hv, rfl⟩
  | succ k ih =>
      intro e he
      have := entryReduce_subset G K _ he
      obtain ⟨e', he', hmem⟩ := List.mem_flatMap.mp this
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hmem
      obtain ⟨h1, h2⟩ := ih e' he'
      exact ⟨h1, by simp [h2]⟩

/-- **★★★ THE TREE COVERS THE FULL ENUMERATION.** Every `(branch, sequence)` pair of the unpruned search space is
the image, under a **word in `G`**, of an entry the tree actually kept.

The induction is the whole point: a length-`k+1` sequence `s ++ [x]` reduces because its length-`k` prefix does —
`(v, s ++ [x]) = w · (t.1, t.2 ++ [w⁻¹ x])`, and `(t.1, t.2 ++ [w⁻¹ x])` is a *generated* child of the kept `t`. -/
theorem exists_rep (G : List (Equiv.Perm (Fin n))) (K : Nat) (χ : Colouring n) :
    ∀ (k : Nat) (v : Fin n), v ∈ branches χ → ∀ (s : List (Fin n)), s.length = k →
      ∃ t ∈ entryLevels G K χ k, ∃ w, GWord G w ∧ (v, s) = actEntry w t := by
  intro k
  induction k with
  | zero =>
      intro v hv s hs
      obtain rfl : s = [] := List.length_eq_zero_iff.mp hs
      exact entryReduce_covers G K (List.mem_map.mpr ⟨v, hv, rfl⟩)
  | succ k ih =>
      intro v hv s hs
      rcases List.eq_nil_or_concat s with rfl | ⟨s', x, rfl⟩
      · simp at hs
      · simp only [List.concat_eq_append] at hs ⊢
        have hs' : s'.length = k := by simpa using hs
        obtain ⟨t, ht, w, hw, hvt⟩ := ih v hv s' hs'
        have hv1 : v = w t.1 := congrArg Prod.fst hvt
        have hs1 : s' = t.2.map w := congrArg Prod.snd hvt
        -- the generated child of the kept representative
        refine ?_
        have hchild : (t.1, t.2 ++ [w⁻¹ x]) ∈ (entryLevels G K χ k).flatMap
            (fun e => (List.finRange n).map (fun y => (e.1, e.2 ++ [y]))) :=
          List.mem_flatMap.mpr ⟨t, ht, List.mem_map.mpr ⟨w⁻¹ x, List.mem_finRange _, rfl⟩⟩
        obtain ⟨t', ht', u, hu, hchild'⟩ := entryReduce_covers G K hchild
        refine ⟨t', ht', w * u, hw.comp hu, ?_⟩
        have hkey : (v, s' ++ [x]) = actEntry w (t.1, t.2 ++ [w⁻¹ x]) := by
          have : actEntry w (t.1, t.2 ++ [w⁻¹ x]) = (w t.1, t.2.map w ++ [x]) := by
            simp [actEntry]
          rw [this, ← hv1, ← hs1]
        rw [hkey, hchild', actEntry_mul]

/-- The pruned entry set at depth `d` — every level up to `d`. -/
def prunedEntries (G : List (Equiv.Perm (Fin n))) (K : Nat) (χ : Colouring n) (d : Nat) :
    List (Entry n) :=
  (List.range (d + 1)).flatMap (entryLevels G K χ)

theorem mem_prunedEntries_of_level {G : List (Equiv.Perm (Fin n))} {K : Nat} {χ : Colouring n}
    {d k : Nat} (hk : k ≤ d) {e : Entry n} (he : e ∈ entryLevels G K χ k) :
    e ∈ prunedEntries G K χ d :=
  List.mem_flatMap.mpr ⟨k, List.mem_range.mpr (Nat.lt_succ_of_le hk), he⟩

theorem prunedEntries_spec {G : List (Equiv.Perm (Fin n))} {K : Nat} {χ : Colouring n} {d : Nat}
    {e : Entry n} (he : e ∈ prunedEntries G K χ d) : e.1 ∈ branches χ ∧ e.2.length ≤ d := by
  obtain ⟨k, hk, hmem⟩ := List.mem_flatMap.mp he
  obtain ⟨h1, h2⟩ := entryLevels_spec G K χ k e hmem
  exact ⟨h1, by rw [h2]; exact Nat.le_of_lt_succ (List.mem_range.mp hk)⟩

/-- **★★★ THE COVERING, PACKAGED.** Every entry of the *full* depth-`d` search space reduces to a pruned one. -/
theorem exists_rep_prunedEntries (G : List (Equiv.Perm (Fin n))) (K : Nat) (χ : Colouring n)
    {d : Nat} {v : Fin n} (hv : v ∈ branches χ) {s : List (Fin n)} (hs : s.length ≤ d) :
    ∃ t ∈ prunedEntries G K χ d, ∃ w, GWord G w ∧ (v, s) = actEntry w t := by
  obtain ⟨t, ht, w, hw, hvt⟩ := exists_rep G K χ s.length v hv s rfl
  exact ⟨t, mem_prunedEntries_of_level hs ht, w, hw, hvt⟩

/-! ## 3. The supply -/

/-- The colouring an entry reaches, materialised once (`ColData`, standing trap #1). -/
def entryData (adj : AdjMatrix n) (χ : Colouring n) (e : Entry n) : Refine.ColData n :=
  deepData adj (Refine.warmRefineVec adj (indivOne χ e.1)) e.2

theorem entryData_col (adj : AdjMatrix n) (χ : Colouring n) (e : Entry n) :
    (entryData adj χ e).col = deepCol adj χ (e.1 :: e.2) := by
  show (deepData adj (Refine.warmRefineVec adj (indivOne χ e.1)) e.2).col
      = deepCol adj (Refine.warmRefineR adj (indivOne χ e.1)) e.2
  rw [DeepMatch.deepData_col, Refine.warmRefineVec_col_eq]

/-- A pruned entry is a genuine row of the **full** table — so anything the tree finds, the full oracle has. -/
theorem mem_deepTable_of_prunedEntries {G : List (Equiv.Perm (Fin n))} {K : Nat}
    {adj : AdjMatrix n} {χ : Colouring n} {d : Nat} {e : Entry n}
    (he : e ∈ prunedEntries G K χ d) : (e, entryData adj χ e) ∈ deepTable adj χ d := by
  obtain ⟨h1, h2⟩ := prunedEntries_spec he
  exact mem_deepTable_iff.mpr ⟨e.1, h1, e.2, (mem_allSeqs d e.2).mpr h2, rfl⟩

/-- The pruned table: one materialised colouring per kept entry. -/
def treeTable (G : List (Equiv.Perm (Fin n))) (K : Nat) (adj : AdjMatrix n) (χ : Colouring n)
    (d : Nat) : List (Entry n × Refine.ColData n) :=
  (prunedEntries G K χ d).map (fun e => (e, entryData adj χ e))

/-- The reference entry of a pruned table: the first one that discretizes. -/
def treeRef (tbl : List (Entry n × Refine.ColData n)) : Option (Entry n × Refine.ColData n) :=
  tbl.find? (fun z => decide (Discrete z.2.col))

/-- The emitted generators: the seed group (the words the pruning spent) **plus** the reference matches. -/
def treeGens (G : List (Equiv.Perm (Fin n))) (tbl : List (Entry n × Refine.ColData n)) :
    List (Equiv.Perm (Fin n)) :=
  (treeRef tbl).elim [] (fun p => G ++ tbl.filterMap (fun q => matchCol p.2.col q.2.col))

/-- **★ THE TREE-PRUNED ORACLE.** Grow the search tree level by level, pruning each level by the orbits of the
**seed** group; match every surviving entry against one discrete reference; emit the seed generators alongside the
matches (they are the words the pruning spent). Untrusted on both counts — `Consume.verified` re-checks. -/
def treeSupply (seed : Supply n) (K d : Nat) : Supply n := fun adj χ =>
  (treeGens (verified seed adj χ) (treeTable (verified seed adj χ) K adj χ d),
   supplyCost seed adj χ
     + (treeTable (verified seed adj χ) K adj χ d).length * (d + 1)
         * CostModel.WarmRefine.warmRefineCost n
     + (treeTable (verified seed adj χ) K adj χ d).length * (n * n))

theorem gens_treeSupply (seed : Supply n) (K d : Nat) (adj : AdjMatrix n) (χ : Colouring n) :
    gens (treeSupply seed K d) adj χ
      = treeGens (verified seed adj χ) (treeTable (verified seed adj χ) K adj χ d) := rfl

/-- Membership in the emitted list, unpacked. -/
theorem mem_treeGens {G : List (Equiv.Perm (Fin n))} {tbl : List (Entry n × Refine.ColData n)}
    {g : Equiv.Perm (Fin n)} (hg : g ∈ treeGens G tbl) :
    ∃ p, treeRef tbl = some p ∧
      (g ∈ G ∨ ∃ q ∈ tbl, matchCol p.2.col q.2.col = some g) := by
  unfold treeGens at hg
  rcases hp : treeRef tbl with _ | p
  · rw [hp] at hg; simp at hg
  · rw [hp] at hg
    simp only [Option.elim_some, List.mem_append] at hg
    rcases hg with h | h
    · exact ⟨p, rfl, Or.inl h⟩
    · obtain ⟨q, hq, hmc⟩ := List.mem_filterMap.mp h
      exact ⟨p, rfl, Or.inr ⟨q, hq, hmc⟩⟩

/-- Conversely: once the reference exists, both the seed group and every match are emitted. -/
theorem mem_treeGens_of_seed {G : List (Equiv.Perm (Fin n))}
    {tbl : List (Entry n × Refine.ColData n)} {p : Entry n × Refine.ColData n}
    (hp : treeRef tbl = some p) {g : Equiv.Perm (Fin n)} (hg : g ∈ G) : g ∈ treeGens G tbl := by
  unfold treeGens; rw [hp]; exact List.mem_append.mpr (Or.inl hg)

theorem mem_treeGens_of_match {G : List (Equiv.Perm (Fin n))}
    {tbl : List (Entry n × Refine.ColData n)} {p q : Entry n × Refine.ColData n}
    (hp : treeRef tbl = some p) (hq : q ∈ tbl) {g : Equiv.Perm (Fin n)}
    (hmc : matchCol p.2.col q.2.col = some g) : g ∈ treeGens G tbl := by
  unfold treeGens; rw [hp]
  exact List.mem_append.mpr (Or.inr (List.mem_filterMap.mpr ⟨q, hq, hmc⟩))

theorem treeRef_mem {tbl : List (Entry n × Refine.ColData n)} {p : Entry n × Refine.ColData n}
    (hp : treeRef tbl = some p) : p ∈ tbl := List.mem_of_find?_eq_some hp

theorem discrete_treeRef {tbl : List (Entry n × Refine.ColData n)}
    {p : Entry n × Refine.ColData n} (hp : treeRef tbl = some p) : Discrete p.2.col := by
  have h := List.find?_some
    (p := fun z : Entry n × Refine.ColData n => decide (Discrete z.2.col)) (l := tbl) hp
  exact of_decide_eq_true h

/-- A discrete row forces the reference to exist. -/
theorem treeRef_isSome_of_discrete {tbl : List (Entry n × Refine.ColData n)}
    {q : Entry n × Refine.ColData n} (hq : q ∈ tbl) (hd : Discrete q.2.col) :
    ∃ p, treeRef tbl = some p := by
  rcases hp : treeRef tbl with _ | p
  · rw [treeRef, List.find?_eq_none] at hp
    exact absurd (by simpa using hd) (hp q hq)
  · exact ⟨p, rfl⟩


/-! ## 4. `SameOrbits` — the group-closure proof

The first half could compare *sets*. Here the pruned generators are a **strict subset** of the automorphisms the
full oracle finds (measured: `10` of `D₇`'s `14` on `C₇`/`d=1`), so the argument has to run at the level of the
**generated group**: every full-oracle generator is exhibited as a **product** `u * c` of pruned ones, and
`Reaches` (§1) converts that product into `WordReach`. -/

section Proof

variable {seed : Supply n} {K d : Nat} {adj : AdjMatrix n} {χ : Colouring n}

/-- Shorthand for the seed group at a node. Every member is a machine-checked automorphism. -/
local notation "G!" => verified seed adj χ

theorem isColAut_of_gword_seed {w : Equiv.Perm (Fin n)} (hw : GWord G! w) : IsColAut adj χ w :=
  isColAut_of_gword (fun _ hg => isColAut_of_mem_verified hg) hw

/-- **★ THE COVERING, IN COLOURINGS.** Every colouring the *full* search space reaches is the `w`-transport of one
the **pruned tree** reaches, for `w` a word in the seed group — hence an automorphism. -/
theorem exists_pruned_transport {v : Fin n} (hv : v ∈ branches χ) {s : List (Fin n)}
    (hs : s.length ≤ d) :
    ∃ t ∈ prunedEntries G! K χ d, ∃ w, IsColAut adj χ w ∧
      deepCol adj χ (v :: s) = transportColouring w (deepCol adj χ (t.1 :: t.2)) := by
  obtain ⟨t, ht, w, hw, hvt⟩ := exists_rep_prunedEntries G! K χ hv hs
  have haut : IsColAut adj χ w := isColAut_of_gword_seed hw
  refine ⟨t, ht, w, haut, ?_⟩
  have hcons : v :: s = (t.1 :: t.2).map w := by
    have h1 : v = w t.1 := congrArg Prod.fst hvt
    have h2 : s = t.2.map w := congrArg Prod.snd hvt
    rw [h1, h2, List.map_cons]
  rw [hcons, OrbitPrune.deepCol_aut haut]

/-- The same, carrying the word itself (needed to *left-multiply* the candidate). -/
theorem exists_pruned_transport_word {v : Fin n} (hv : v ∈ branches χ) {s : List (Fin n)}
    (hs : s.length ≤ d) :
    ∃ t ∈ prunedEntries G! K χ d, ∃ w, GWord G! w ∧ IsColAut adj χ w ∧
      deepCol adj χ (v :: s) = transportColouring w (deepCol adj χ (t.1 :: t.2)) := by
  obtain ⟨t, ht, w, hw, hvt⟩ := exists_rep_prunedEntries G! K χ hv hs
  have haut : IsColAut adj χ w := isColAut_of_gword_seed hw
  refine ⟨t, ht, w, hw, haut, ?_⟩
  have hcons : v :: s = (t.1 :: t.2).map w := by
    have h1 : v = w t.1 := congrArg Prod.fst hvt
    have h2 : s = t.2.map w := congrArg Prod.snd hvt
    rw [h1, h2, List.map_cons]
  rw [hcons, OrbitPrune.deepCol_aut haut]

theorem mem_treeTable {e : Entry n} (he : e ∈ prunedEntries G! K χ d) :
    (e, entryData adj χ e) ∈ treeTable G! K adj χ d :=
  List.mem_map.mpr ⟨e, he, rfl⟩

/-- **The tree discretizes whenever the full table does.** A discrete full entry transports onto a pruned one, and
discreteness is transport-invariant. -/
theorem exists_treeRef_of_full {p : (Fin n × List (Fin n)) × Refine.ColData n}
    (hp : p ∈ deepTable adj χ d) (hd : Discrete p.2.col) :
    ∃ pr, treeRef (treeTable G! K adj χ d) = some pr := by
  obtain ⟨v, hv, s, hs, rfl⟩ := mem_deepTable_iff.mp hp
  have hcol : deepCol adj χ (v :: s) = (entryData adj χ (v, s)).col := (entryData_col adj χ (v, s)).symm
  have hdisc : Discrete (deepCol adj χ (v :: s)) := by rw [hcol]; exact hd
  obtain ⟨t, ht, w, haut, heq⟩ := exists_pruned_transport (seed := seed) (K := K) (d := d) hv
    ((mem_allSeqs d s).mp hs)
  have ht' : Discrete (deepCol adj χ (t.1 :: t.2)) := by
    rw [heq] at hdisc; exact (discrete_transport w _).mp hdisc
  refine treeRef_isSome_of_discrete (mem_treeTable (seed := seed) (K := K) (d := d) ht) ?_
  rw [entryData_col]; exact ht'

/-- Every element of the seed group is emitted, hence **verified**, by the tree — provided it emitted anything. -/
theorem seed_subset_verified {pr : Entry n × Refine.ColData n}
    (hpr : treeRef (treeTable G! K adj χ d) = some pr) :
    ∀ g ∈ G!, g ∈ verified (treeSupply seed K d) adj χ := by
  intro g hg
  refine List.mem_filter.mpr ⟨?_, by simpa using isColAut_of_mem_verified hg⟩
  rw [gens_treeSupply]
  exact mem_treeGens_of_seed hpr hg

/-! ### Direction A — everything the tree proves, the full oracle proves -/

/-- If the tree emits anything, it found a discrete entry, which is a row of the **full** table too. -/
theorem exists_full_ref_of_mem_gens {g : Equiv.Perm (Fin n)}
    (hg : g ∈ gens (treeSupply seed K d) adj χ) : ∃ r, refCol? adj χ d = some r := by
  rw [gens_treeSupply] at hg
  obtain ⟨pr, hpr, _⟩ := mem_treeGens hg
  obtain ⟨e, he, hpe⟩ := List.mem_map.mp (treeRef_mem hpr)
  refine refCol_isSome_of_discrete (mem_deepTable_of_prunedEntries (K := K) he) ?_
  have := discrete_treeRef hpr
  rw [← hpe] at this
  exact this

/-- **Direction A.** The tree emits only automorphisms, and once *any* entry discretizes the full oracle contains
**every** automorphism (`PrunedSupply.exists_image_entry`). So this direction needs no closure at all. -/
theorem verified_tree_subset_deep {g : Equiv.Perm (Fin n)}
    (hg : g ∈ verified (treeSupply seed K d) adj χ) :
    g ∈ verified (deepMatchSupply d) adj χ := by
  have haut : IsColAut adj χ g := isColAut_of_mem_verified hg
  obtain ⟨r, hr⟩ := exists_full_ref_of_mem_gens (List.mem_of_mem_filter hg)
  obtain ⟨p, hp, hpr⟩ := refCol_eq_deepCol hr
  obtain ⟨q, hq, hmc⟩ := exists_image_entry haut hr
  refine List.mem_filter.mpr ⟨?_, by simpa using haut⟩
  exact mem_gens_deepMatchSupply_raw.mpr ⟨p, hp, q, hq, by rw [hpr]; exact hmc⟩

/-! ### Direction B — the closure: every full-oracle generator is a PRODUCT of pruned ones -/

/-- **★★★ THE CLOSURE.** Take a full-oracle generator `g` (an automorphism). The tree's reference `r` sits at a
pruned entry `e`; the *full* entry `g · e` therefore reduces to some pruned `t` by a word `u`, so

    some g = matchCol r (g · r) = matchCol r (u · deepCol t) = (matchCol r (deepCol t)).map (u * ·)

giving `g = u * c` with `c` a **kept** reference match. `c = u⁻¹ * g` is an automorphism (`IsColAut.inv`/`comp`),
so `c` survives verification; `u` is a word in the seed group, which the tree also emits. Hence `g` acts inside the
orbit partition the tree proves. -/
theorem deep_reaches_tree {g : Equiv.Perm (Fin n)}
    (hg : g ∈ verified (deepMatchSupply d) adj χ) :
    Reaches (verified (treeSupply seed K d) adj χ) g := by
  have haut : IsColAut adj χ g := isColAut_of_mem_verified hg
  obtain ⟨p, hp, q, hq, hmc⟩ := mem_gens_deepMatchSupply_raw.mp (List.mem_of_mem_filter hg)
  have hdp : Discrete p.2.col := by
    by_contra hnd; simp [matchCol, dif_neg hnd] at hmc
  obtain ⟨pr, hpr⟩ := exists_treeRef_of_full (seed := seed) (K := K) hp hdp
  -- the reference sits at a pruned entry `e`
  obtain ⟨e, he, hpe⟩ := List.mem_map.mp (treeRef_mem hpr)
  obtain ⟨hev, hes⟩ := prunedEntries_spec (K := K) he
  have hrcol : pr.2.col = deepCol adj χ (e.1 :: e.2) := by
    rw [← hpe]; exact entryData_col adj χ e
  have hrd : Discrete pr.2.col := discrete_treeRef hpr
  -- the `g`-image of that entry is in the full space, hence reduces to a pruned `t` by a word `u`
  have hgev : g e.1 ∈ branches χ := mem_branches_of_isColAut haut hev
  have hgs : (e.2.map g).length ≤ d := by simpa using hes
  obtain ⟨t, ht, u, hu, huaut, hteq⟩ :=
    exists_pruned_transport_word (seed := seed) (K := K) (d := d) hgev hgs
  -- both descriptions of the image colouring
  have himg : deepCol adj χ (g e.1 :: e.2.map g) = transportColouring g pr.2.col := by
    have h1 : g e.1 :: e.2.map g = (e.1 :: e.2).map g := by rw [List.map_cons]
    rw [h1, OrbitPrune.deepCol_aut haut, hrcol]
  have hchain : transportColouring g pr.2.col
      = transportColouring u (deepCol adj χ (t.1 :: t.2)) := by rw [← himg, hteq]
  -- match both against the reference
  have hself : matchCol pr.2.col (transportColouring g pr.2.col) = some g :=
    matchCol_self_transport g hrd
  have hleft : matchCol pr.2.col (transportColouring u (deepCol adj χ (t.1 :: t.2)))
      = (matchCol pr.2.col (deepCol adj χ (t.1 :: t.2))).map (fun z => u * z) :=
    OrbitPrune.matchCol_left_mul u _ _
  rw [hchain, hleft] at hself
  obtain ⟨c, hc, hgc⟩ := Option.map_eq_some_iff.mp hself
  -- `c` is a kept reference match, and it is an automorphism because `c = u⁻¹ * g`
  have hcmem : c ∈ gens (treeSupply seed K d) adj χ := by
    rw [gens_treeSupply]
    refine mem_treeGens_of_match hpr (mem_treeTable (seed := seed) (K := K) (d := d) ht) ?_
    rw [entryData_col]; exact hc
  have hcaut : IsColAut adj χ c := by
    have : c = u⁻¹ * g := by rw [← hgc]; group
    rw [this]; exact IsColAut.comp huaut.inv haut
  have hcver : c ∈ verified (treeSupply seed K d) adj χ :=
    List.mem_filter.mpr ⟨hcmem, by simpa using hcaut⟩
  -- assemble: `g = u * c`, `u` a word in the seed group (all emitted), `c` a generator
  have hured : Reaches (verified (treeSupply seed K d) adj χ) u :=
    Reaches.ofGWord (seed_subset_verified (seed := seed) (K := K) (d := d) hpr) hu
  have hcred : Reaches (verified (treeSupply seed K d) adj χ) c := Reaches.gen hcver
  rw [← hgc]
  exact hured.mul hcred

end Proof

/-! ## 5. ★★★ The capstones -/

/-- **★★★ `treeSupply` PROVES THE SAME ORBITS AS `deepMatchSupply`.** Direction A is membership; direction B is the
group closure above. This is the *entire* `①` obligation of the tree-pruned supply — and note it holds for an
**arbitrary, untrusted seed supply**: a bad seed prunes less, never wrongly. -/
theorem sameOrbits_treeSupply (seed : Supply n) (K d : Nat) :
    OrbitPrune.SameOrbits (deepMatchSupply (n := n) d) (treeSupply seed K d) := by
  intro adj χ u w
  constructor
  · exact wordReach_of_reaches (fun g hg => deep_reaches_tree hg)
  · exact wordReach_of_reaches (fun g hg => Reaches.gen (verified_tree_subset_deep hg))

/-- **★★★ THE TREE-PRUNED MIXED CANONIZER.** `①a`/`①b`/`①c` for the guarded composite over the supply whose
sequence enumeration is orbit-pruned level by level — inherited wholesale through the `SameOrbits` reduction, with
**no** equivariance proof on `treeSupply` (which has none: it picks orbit representatives). -/
theorem treeSupply_guarded_canonizer {seed : Supply n} {K d : Nat} {key : Key n}
    (hk : KeyEquivariant key) :
    CanonSpec.IsCanonicalFormOpt
      (Descend.canonForm? (Refine.encodeFreeFast (n := n))
        (Stall.guard (forceThenConsume key (treeSupply seed K d)))) :=
  OrbitPrune.guarded_mixed_canonizer_of_sameOrbits hk
    (supplyEquivariant_deepMatchSupply d) (sameOrbits_treeSupply seed K d)

/-- The canonizer of record for the second half: tree-pruned supply seeded by the **reference-matching** supply one
level shallower (the first half), with the concrete `lookaheadKey`. -/
theorem treeSupply_lookahead_canonizer (K d : Nat) :
    CanonSpec.IsCanonicalFormOpt
      (Descend.canonForm? (Refine.encodeFreeFast (n := n))
        (Stall.guard (forceThenConsume (lookaheadKey (n := n))
          (treeSupply (PrunedSupply.prunedSupply (n := n) d) K (d + 1))))) :=
  treeSupply_guarded_canonizer keyEquivariant_lookahead

/-- `Residue.Handled`, `Consume.CellIsOrbit` and `Cost.CellResolved` transfer too — the residue is **unchanged**
by the pruning, which is the whole point of running on `SameOrbits` rather than on equivariance. -/
theorem cellIsOrbit_treeSupply {seed : Supply n} {K d : Nat} {adj : AdjMatrix n} {χ : Colouring n}
    (h : CellIsOrbit (deepMatchSupply (n := n) d) adj χ) :
    CellIsOrbit (treeSupply seed K d) adj χ :=
  OrbitPrune.cellIsOrbit_congr (sameOrbits_treeSupply seed K d) h

end TreePrune
end ChainDescent
