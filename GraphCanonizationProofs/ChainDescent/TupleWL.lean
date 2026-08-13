import ChainDescent.CaoTarget

/-!
# `k`-WL on tuples, and the **block lemma** — increment 2 of the §6f transfer bound

(`docs/chain-descent-cao-carrier-falsifiers.md` §6f, and §6f.4a for the scoping. `FrameEncoding.lean`
is the consumer: its one open clause `Adequate.blocks` is what this file exists to supply.)

## The obligation this file attacks

`FrameEncoding.pairSigG_split` decomposes the encoding's 2-WL signature into

```
   a sum over ONE fresh label (the payload vertices)  +  a sum over TWO fresh labels and a bit
   (the frame vertices)
```

so discharging `Adequate.blocks` needs exactly one thing from the bounding colouring: **adding up to
two fresh coordinates must not break determinacy.** That is §6f's dimension count, stated without any
logic: it is why a *bounded* number of extra coordinates suffices, and it is the whole content of
"the encoding's WL gain is bounded".

## ★★★ The block lemma

`k`-WL stability is a statement about replacing **one** coordinate. What the consumer needs is a
statement about **two**. They are not the same, and the gap is closed by nesting:

> `subst2_of_stable` — for a stable `s`, the multiset over `u` of the *pair* `(s (x[i:=u]), the
> multiset over v of s (x[i:=u][j:=v]))` is determined by `s x`.

The proof is the one move worth remembering: the inner multiset **factors through `s`** (stability at
`j` says equal colours give equal inner multisets), so the outer sum is the image of a
*one*-coordinate substitution multiset under a fixed map — and *that* is determined by `s x` by
stability at `i`. ⟹ two coordinates cost one nesting, `j` coordinates cost `j`.

`substJoin_of_stable` is the flattened form, which is the shape a WL signature actually has.

## ⚠ What is NOT here

The **assembly** — instantiating `FrameEncoding.Adequate` from a stable tuple colouring — is the next
step, and it needs one further ingredient this file does not provide: a **restriction/covariance**
lemma saying the colour of a big tuple determines the colours of its sub-tuples (the consumer's
summand is a *pair* `(b (P₁, Z), b (Z, P₂))`, i.e. two different reindexings of one combined tuple).
⚠ Recorded here so it is not discovered late: the block lemma alone does not close `blocks`.

Quality bar: axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`, no fresh `axiom`.
-/

namespace ChainDescent
namespace TupleWL

open ChainDescent.PartitionClosure
open ChainDescent.CaoTarget (rankOf rankOf_eq_iff)

variable {k L : Nat}

/-! ## 1. Tuples, and an injective encoding of their colour vectors

The round's signature is a multiset of *vectors* of colours, one entry per coordinate; `rankOf` wants
a `List Nat`. `encVec` bridges the two, and is injective at fixed arity — which is all the key needs. -/

/-- A `k`-tuple over `L` labels. -/
abbrev Tup (k L : Nat) : Type := Fin k → Fin L

/-- Fold a list of colours into one natural number. Injective **at fixed length** (§1's remark). -/
def encList : List Nat → Nat
  | [] => 0
  | a :: l => Nat.pair a (encList l)

theorem encList_inj : ∀ (l₁ l₂ : List Nat), l₁.length = l₂.length → encList l₁ = encList l₂ → l₁ = l₂
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => absurd h (by simp)
  | _ :: _, [], h, _ => absurd h (by simp)
  | a :: l₁, b :: l₂, h, he => by
      have hlen : l₁.length = l₂.length := by simpa using h
      obtain ⟨hab, hl⟩ := Nat.pair_eq_pair.mp he
      rw [hab, encList_inj l₁ l₂ hlen hl]

/-- The colour vector of a tuple, as one natural number. -/
def encVec (f : Fin k → Nat) : Nat := encList (List.ofFn f)

theorem encVec_injective : Function.Injective (encVec (k := k)) := by
  intro f g h
  have hlen : (List.ofFn f).length = (List.ofFn g).length := by simp
  have := encList_inj _ _ hlen h
  exact List.ofFn_injective this

/-! ## 2. The `k`-WL round

One round replaces each coordinate in turn by every label and records the resulting colour **vector**;
the signature is the multiset of those vectors. At `k = 2` this is `CaoTarget.round2`'s content with
the two half-colours read off the two coordinates. -/

section Round

/-- The `k`-WL signature: over every label `v`, the vector `i ↦ s (x with coordinate i set to v)`. -/
def tupSig (s : Col (Tup k L)) (x : Tup k L) : Multiset (Fin k → Nat) :=
  (Finset.univ : Finset (Fin L)).val.map (fun v => fun i => s (Function.update x i v))

/-- The `k`-WL key of a tuple: its own colour, then its sorted signature. -/
def tupKey (s : Col (Tup k L)) (x : Tup k L) : List Nat :=
  s x :: Multiset.sort ((tupSig s x).map encVec) (· ≤ ·)

theorem tupKey_eq_iff (s : Col (Tup k L)) (x y : Tup k L) :
    tupKey s x = tupKey s y ↔ (s x = s y ∧ tupSig s x = tupSig s y) := by
  unfold tupKey
  rw [List.cons.injEq]
  refine and_congr_right (fun _ => ?_)
  constructor
  · intro hsort
    have hmap : (tupSig s x).map encVec = (tupSig s y).map encVec := by
      have := congrArg (fun l : List Nat => (↑l : Multiset Nat)) hsort
      simpa only [Multiset.sort_eq] using this
    exact Multiset.map_injective encVec_injective hmap
  · intro h; rw [h]

/-- **One `k`-WL refinement round.** Ranked, so no encoding hypothesis is ever needed. -/
def roundT (s : Col (Tup k L)) : Col (Tup k L) := rankOf (tupKey s)

theorem roundT_eq_iff (s : Col (Tup k L)) (x y : Tup k L) :
    roundT s x = roundT s y ↔ (s x = s y ∧ tupSig s x = tupSig s y) :=
  (rankOf_eq_iff _ x y).trans (tupKey_eq_iff s x y)

theorem tupSig_map_of_factor {s d : Col (Tup k L)} {g : Nat → Nat} (hg : ∀ x, g (s x) = d x)
    (x : Tup k L) : tupSig d x = (tupSig s x).map (fun t => g ∘ t) := by
  unfold tupSig
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl (fun v _ => ?_)
  funext i
  exact (hg _).symm

/-- **The `k`-WL round is an `IsRound`** — so FT1's closure theory applies at every arity. -/
theorem isRound_roundT : IsRound (roundT (k := k) (L := L)) where
  splits := fun s x y h => ((roundT_eq_iff s x y).mp h).1
  mono := by
    intro s d hsd x y h
    obtain ⟨hc, hs⟩ := (roundT_eq_iff s x y).mp h
    obtain ⟨g, hg⟩ := exists_factor hsd
    refine (roundT_eq_iff d x y).mpr ⟨hsd x y hc, ?_⟩
    rw [tupSig_map_of_factor hg x, tupSig_map_of_factor hg y, hs]

/-- **The `k`-WL closure**, as a function. -/
def wlT (s : Col (Tup k L)) : Col (Tup k L) := wl roundT s

/-- The method (§6d.1) at arity `k`: a stable guess bounds the closure from above. -/
theorem refines_wlT_of_stable {s c : Col (Tup k L)} (hs : Stable (roundT (k := k) (L := L)) s)
    (h : PartitionClosure.Refines s c) : PartitionClosure.Refines s (wlT c) :=
  refines_wl_of_stable isRound_roundT hs h

/-- Stability, in the signature form every proof below uses. -/
theorem stable_iff_tupSig {s : Col (Tup k L)} :
    Stable (roundT (k := k) (L := L)) s ↔ ∀ x y : Tup k L, s x = s y → tupSig s x = tupSig s y := by
  constructor
  · intro hs x y h; exact ((roundT_eq_iff s x y).mp (hs x y h)).2
  · intro h x y hxy; exact (roundT_eq_iff s x y).mpr ⟨hxy, h x y hxy⟩

/-- **The only property of a round that the block lemma uses**: equal colours force equal signatures.
`stable_iff_tupSig` supplies it from `roundT`-stability, and §4's substitution-closed round supplies it
too — so the block lemma is stated at this weaker hypothesis and serves both rounds. -/
def SigDet (s : Col (Tup k L)) : Prop := ∀ x y : Tup k L, s x = s y → tupSig s x = tupSig s y

theorem sigDet_of_stable {s : Col (Tup k L)} (hs : Stable (roundT (k := k) (L := L)) s) : SigDet s :=
  stable_iff_tupSig.mp hs

/-! ## 3. ★★★ The block lemma — one fresh coordinate, then two

`subst1` is what stability hands you directly. `subst2` is what the consumer needs. -/

/-- **One fresh coordinate**: the multiset over `v` of `s` at `x` with coordinate `i` replaced. -/
def subst1 (s : Col (Tup k L)) (x : Tup k L) (i : Fin k) : Multiset Nat :=
  (Finset.univ : Finset (Fin L)).val.map (fun v => s (Function.update x i v))

theorem subst1_eq_tupSig (s : Col (Tup k L)) (x : Tup k L) (i : Fin k) :
    subst1 s x i = (tupSig s x).map (fun t => t i) := by
  unfold subst1 tupSig
  rw [Multiset.map_map]
  rfl

/-- **One fresh coordinate is free**: it is the projection of stability's own signature. -/
theorem subst1_of_sigDet {s : Col (Tup k L)} (hs : SigDet s)
    {x y : Tup k L} (h : s x = s y) (i : Fin k) : subst1 s x i = subst1 s y i := by
  rw [subst1_eq_tupSig, subst1_eq_tupSig, hs x y h]

/-- A colouring-indexed family that respects `s`'s classes factors through `s`. The `Multiset`-valued
analogue of `PartitionClosure.exists_factor`, and the move the block lemma turns on. -/
private theorem exists_factor_ms {s : Tup k L → Nat} {g : Tup k L → Multiset Nat}
    (h : ∀ z z' : Tup k L, s z = s z' → g z = g z') : ∃ f : Nat → Multiset Nat, ∀ z, f (s z) = g z := by
  classical
  refine ⟨fun n => if hn : ∃ z : Tup k L, s z = n then g hn.choose else 0, fun z => ?_⟩
  have hz : ∃ w : Tup k L, s w = s z := ⟨z, rfl⟩
  show (if hn : ∃ w : Tup k L, s w = s z then g hn.choose else 0) = g z
  rw [dif_pos hz]
  exact h _ _ hz.choose_spec

/-- **Two fresh coordinates, nested**: over `u`, the pair of `x[i:=u]`'s colour and its own
one-coordinate substitution multiset at `j`. -/
def subst2 (s : Col (Tup k L)) (x : Tup k L) (i j : Fin k) : Multiset (Nat × Multiset Nat) :=
  (Finset.univ : Finset (Fin L)).val.map
    (fun u => (s (Function.update x i u), subst1 s (Function.update x i u) j))

/-- **★★★ THE BLOCK LEMMA.** For a stable `s`, two fresh coordinates are still determined by the
tuple's own colour.

★ The proof is the move worth remembering: the inner multiset **factors through `s`** (that is
`subst1_of_stable`), so the outer multiset is the image of a *one*-coordinate substitution multiset
under a fixed map — and that one is determined by `s x`. ⟹ each extra coordinate costs one nesting,
which is exactly why §6f's bound is a constant. -/
theorem subst2_of_sigDet {s : Col (Tup k L)} (hs : SigDet s)
    {x y : Tup k L} (h : s x = s y) (i j : Fin k) : subst2 s x i j = subst2 s y i j := by
  obtain ⟨f, hf⟩ := exists_factor_ms (g := fun z => subst1 s z j)
    (fun z z' hz => subst1_of_sigDet hs hz j)
  have key : ∀ w : Tup k L, subst2 s w i j = (subst1 s w i).map (fun n => (n, f n)) := by
    intro w
    show (Finset.univ : Finset (Fin L)).val.map
        (fun u => (s (Function.update w i u), subst1 s (Function.update w i u) j))
      = ((Finset.univ : Finset (Fin L)).val.map (fun v => s (Function.update w i v))).map
          (fun n => (n, f n))
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl (fun v _ => ?_)
    show (s (Function.update w i v), subst1 s (Function.update w i v) j)
        = (s (Function.update w i v), f (s (Function.update w i v)))
    rw [hf]
  rw [key, key, subst1_of_sigDet hs h i]

/-- **The flattened form** — the shape a WL signature actually has: the multiset over *both* fresh
coordinates at once. -/
def substJoin (s : Col (Tup k L)) (x : Tup k L) (i j : Fin k) : Multiset Nat :=
  Multiset.join ((Finset.univ : Finset (Fin L)).val.map
    (fun u => subst1 s (Function.update x i u) j))

theorem substJoin_eq_subst2 (s : Col (Tup k L)) (x : Tup k L) (i j : Fin k) :
    substJoin s x i j = Multiset.join ((subst2 s x i j).map Prod.snd) := by
  unfold substJoin subst2
  rw [Multiset.map_map]
  rfl

/-- **★★ THE CONSUMER FORM.** A two-coordinate WL signature is determined by the tuple's colour. -/
theorem substJoin_of_sigDet {s : Col (Tup k L)} (hs : SigDet s)
    {x y : Tup k L} (h : s x = s y) (i j : Fin k) : substJoin s x i j = substJoin s y i j := by
  rw [substJoin_eq_subst2, substJoin_eq_subst2, subst2_of_sigDet hs h i j]

/-- The block lemma at plain `roundT`-stability — the form §3's headline states. -/
theorem substJoin_of_stable {s : Col (Tup k L)} (hs : Stable (roundT (k := k) (L := L)) s)
    {x y : Tup k L} (h : s x = s y) (i j : Fin k) : substJoin s x i j = substJoin s y i j :=
  substJoin_of_sigDet (sigDet_of_stable hs) h i j

/-! ## 4. ★★★ Substitution closure — the covariance the assembly needs

⚠ **Why a second round.** §3 closes the *counting* half of `FrameEncoding.Adequate.blocks`. It does
not close the whole thing, and the reason is worth stating precisely: `blocks`'s summand is a **pair**
`(b (P₁, Z), b (Z, P₂))`, and those two evaluations use *different* four-label sub-tuples of one
six-label tuple. So the assembly needs the colour of a tuple to determine the colours of its
**reindexings** `x ∘ σ` — including non-injective `σ`, which drop and repeat coordinates.

⛔ **That does NOT follow from `roundT`-stability.** For a *permutation* `σ` it would:
`(x ∘ σ)[i := v] = (x[σ i := v]) ∘ σ`, so the signature transports. For a **collapse** it fails —
`(x ∘ σ)[i := v]` is not a reindexing of any update of `x`, and the natural rescue (identify `v = x i`
inside the signature by its colour) breaks, because a tuple whose `i`-th coordinate is distinct from
all others has the same equality pattern as one with a *fresh* value there. ★ Recorded so the dead
route is not re-walked.

▶ **The fix is to put it in the round.** `roundTS` records, alongside the signature, the colours of
**every** reindexing `x ∘ σ`. It is a legitimate refinement round (`isRound_roundTS`), it still gives
`SigDet`, and its stable colourings are covariant by construction. ⚠ It is *finer* than `roundT`, so
the bound it yields is **weaker** — which is the safe direction for an upper bound — and it is still
bounded-arity, so the CFI input (§6f.3) is unaffected in kind. -/

section Subst

variable {k L : Nat}

private theorem map_eq_pointwise {α β : Type*} {f g : α → β} :
    ∀ {l : List α}, l.map f = l.map g → ∀ a ∈ l, f a = g a
  | [], _, a, ha => absurd ha (by simp)
  | b :: t, h, a, ha => by
      simp only [List.map_cons, List.cons.injEq] at h
      rcases List.mem_cons.mp ha with rfl | ht
      · exact h.1
      · exact map_eq_pointwise h.2 a ht

/-- The colours of **all** reindexings of `x`, folded into one natural number.
⚠ `noncomputable` (via `Finset.toList`) — §4 is proof-side only; the *runnable* 2-WL closure is
`CaoFast.wl2Fast`, and nothing here is meant to execute. -/
noncomputable def subEnc (s : Col (Tup k L)) (x : Tup k L) : Nat :=
  encList ((Finset.univ : Finset (Fin k → Fin k)).toList.map (fun σ => s (x ∘ σ)))

theorem subEnc_eq_iff (s : Col (Tup k L)) (x y : Tup k L) :
    subEnc s x = subEnc s y ↔ ∀ σ : Fin k → Fin k, s (x ∘ σ) = s (y ∘ σ) := by
  constructor
  · intro h σ
    have hlen : (((Finset.univ : Finset (Fin k → Fin k)).toList).map (fun τ => s (x ∘ τ))).length
        = (((Finset.univ : Finset (Fin k → Fin k)).toList).map (fun τ => s (y ∘ τ))).length := by
      simp
    exact map_eq_pointwise (encList_inj _ _ hlen h) σ (Finset.mem_toList.mpr (Finset.mem_univ σ))
  · intro h
    unfold subEnc
    congr 1
    exact List.map_congr_left (fun σ _ => h σ)

/-- The **substitution-closed** `k`-WL key: colour, all reindexing colours, then the signature. -/
noncomputable def tupKeyS (s : Col (Tup k L)) (x : Tup k L) : List Nat :=
  s x :: subEnc s x :: Multiset.sort ((tupSig s x).map encVec) (· ≤ ·)

theorem tupKeyS_eq_iff (s : Col (Tup k L)) (x y : Tup k L) :
    tupKeyS s x = tupKeyS s y ↔
      (s x = s y ∧ subEnc s x = subEnc s y ∧ tupSig s x = tupSig s y) := by
  unfold tupKeyS
  rw [List.cons.injEq, List.cons.injEq]
  refine and_congr_right (fun _ => and_congr_right (fun _ => ?_))
  constructor
  · intro hsort
    have hmap : (tupSig s x).map encVec = (tupSig s y).map encVec := by
      have := congrArg (fun l : List Nat => (↑l : Multiset Nat)) hsort
      simpa only [Multiset.sort_eq] using this
    exact Multiset.map_injective encVec_injective hmap
  · intro h; rw [h]

/-- **The substitution-closed round.** -/
noncomputable def roundTS (s : Col (Tup k L)) : Col (Tup k L) := rankOf (tupKeyS s)

theorem roundTS_eq_iff (s : Col (Tup k L)) (x y : Tup k L) :
    roundTS s x = roundTS s y ↔
      (s x = s y ∧ subEnc s x = subEnc s y ∧ tupSig s x = tupSig s y) :=
  (rankOf_eq_iff _ x y).trans (tupKeyS_eq_iff s x y)

/-- **It is a genuine refinement round**, so FT1's closure theory applies to it verbatim. -/
theorem isRound_roundTS : IsRound (roundTS (k := k) (L := L)) where
  splits := fun s x y h => ((roundTS_eq_iff s x y).mp h).1
  mono := by
    intro s d hsd x y h
    obtain ⟨hc, hsub, hsig⟩ := (roundTS_eq_iff s x y).mp h
    obtain ⟨g, hg⟩ := exists_factor hsd
    refine (roundTS_eq_iff d x y).mpr ⟨hsd x y hc, ?_, ?_⟩
    · refine (subEnc_eq_iff d x y).mpr (fun σ => ?_)
      rw [← hg (x ∘ σ), ← hg (y ∘ σ), (subEnc_eq_iff s x y).mp hsub σ]
    · rw [tupSig_map_of_factor hg x, tupSig_map_of_factor hg y, hsig]

/-- The substitution-closed closure. -/
noncomputable def wlTS (s : Col (Tup k L)) : Col (Tup k L) := wl roundTS s

theorem refines_wlTS_of_stable {s c : Col (Tup k L)} (hs : Stable (roundTS (k := k) (L := L)) s)
    (h : PartitionClosure.Refines s c) : PartitionClosure.Refines s (wlTS c) :=
  refines_wl_of_stable isRound_roundTS hs h

/-- A `roundTS`-stable colouring still has `SigDet`, so **the whole block lemma of §3 applies to it**. -/
theorem sigDet_of_stableS {s : Col (Tup k L)} (hs : Stable (roundTS (k := k) (L := L)) s) :
    SigDet s := fun x y h => ((roundTS_eq_iff s x y).mp (hs x y h)).2.2

/-- **★★★ COVARIANCE.** For a `roundTS`-stable colouring, the colour of a tuple determines the colour
of **every** reindexing — dropped and repeated coordinates included. This is the ingredient §3 could
not supply, and the one `FrameEncoding.Adequate.blocks` needs on top of the block lemma. -/
theorem cov_of_stableS {s : Col (Tup k L)} (hs : Stable (roundTS (k := k) (L := L)) s)
    {x y : Tup k L} (h : s x = s y) (σ : Fin k → Fin k) : s (x ∘ σ) = s (y ∘ σ) :=
  (subEnc_eq_iff s x y).mp ((roundTS_eq_iff s x y).mp (hs x y h)).2.1 σ

/-- ★ Both halves at once, in the shape the assembly consumes: a `roundTS`-stable colouring is
covariant **and** its two-coordinate signatures are determined. -/
theorem cov_and_block_of_stableS {s : Col (Tup k L)} (hs : Stable (roundTS (k := k) (L := L)) s)
    {x y : Tup k L} (h : s x = s y) :
    (∀ σ : Fin k → Fin k, s (x ∘ σ) = s (y ∘ σ)) ∧
      (∀ i j : Fin k, substJoin s x i j = substJoin s y i j) :=
  ⟨fun σ => cov_of_stableS hs h σ, fun i j => substJoin_of_sigDet (sigDet_of_stableS hs) h i j⟩

/-! ## 5. The assembly-ready forms

`FrameEncoding.pairSigG_split` sums a **pair** `(b (P₁, Z), b (Z, P₂))` — two *different* reindexings
of one combined tuple — over one fresh label (payload `Z`) and over two (frame `Z`). §5 states exactly
those two shapes, so the consumer never has to redo the factoring. -/

/-- **Covariance as a FUNCTION of the colour.** `cov_of_stableS` is an implication; mapping over a
multiset needs it as a map, and choice supplies one. -/
theorem exists_factor_cov {s : Col (Tup k L)} (hs : Stable (roundTS (k := k) (L := L)) s)
    (σ : Fin k → Fin k) : ∃ f : Nat → Nat, ∀ z : Tup k L, f (s z) = s (z ∘ σ) := by
  classical
  refine ⟨fun n => if hn : ∃ z : Tup k L, s z = n then s (hn.choose ∘ σ) else 0, fun z => ?_⟩
  have hz : ∃ w : Tup k L, s w = s z := ⟨z, rfl⟩
  show (if hn : ∃ w : Tup k L, s w = s z then s (hn.choose ∘ σ) else 0) = s (z ∘ σ)
  rw [dif_pos hz]
  exact cov_of_stableS hs hz.choose_spec σ

/-- **★★ ONE fresh coordinate, paired reindexings** — the shape the encoding's **payload** sum has. -/
theorem substPair1_of_stableS {s : Col (Tup k L)} (hs : Stable (roundTS (k := k) (L := L)) s)
    {x y : Tup k L} (h : s x = s y) (i : Fin k) (σ₁ σ₂ : Fin k → Fin k) :
    (Finset.univ : Finset (Fin L)).val.map
        (fun v => (s (Function.update x i v ∘ σ₁), s (Function.update x i v ∘ σ₂)))
      = (Finset.univ : Finset (Fin L)).val.map
        (fun v => (s (Function.update y i v ∘ σ₁), s (Function.update y i v ∘ σ₂))) := by
  obtain ⟨f₁, hf₁⟩ := exists_factor_cov hs σ₁
  obtain ⟨f₂, hf₂⟩ := exists_factor_cov hs σ₂
  have key : ∀ w : Tup k L, (Finset.univ : Finset (Fin L)).val.map
      (fun v => (s (Function.update w i v ∘ σ₁), s (Function.update w i v ∘ σ₂)))
      = (subst1 s w i).map (fun n => (f₁ n, f₂ n)) := by
    intro w
    show _ = ((Finset.univ : Finset (Fin L)).val.map
      (fun v => s (Function.update w i v))).map (fun n => (f₁ n, f₂ n))
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl (fun v _ => ?_)
    show (s (Function.update w i v ∘ σ₁), s (Function.update w i v ∘ σ₂))
        = (f₁ (s (Function.update w i v)), f₂ (s (Function.update w i v)))
    rw [hf₁, hf₂]
  rw [key, key, subst1_of_sigDet (sigDet_of_stableS hs) h i]

/-- **★★★ TWO fresh coordinates, paired reindexings** — the shape the encoding's **frame** sum has,
and the last generic ingredient the assembly needs. Block lemma (two coordinates) and covariance
(two reindexings) combined in one statement. -/
theorem substPair2_of_stableS {s : Col (Tup k L)} (hs : Stable (roundTS (k := k) (L := L)) s)
    {x y : Tup k L} (h : s x = s y) (i j : Fin k) (σ₁ σ₂ : Fin k → Fin k) :
    Multiset.join ((Finset.univ : Finset (Fin L)).val.map (fun u =>
        (Finset.univ : Finset (Fin L)).val.map (fun v =>
          (s (Function.update (Function.update x i u) j v ∘ σ₁),
           s (Function.update (Function.update x i u) j v ∘ σ₂)))))
      = Multiset.join ((Finset.univ : Finset (Fin L)).val.map (fun u =>
        (Finset.univ : Finset (Fin L)).val.map (fun v =>
          (s (Function.update (Function.update y i u) j v ∘ σ₁),
           s (Function.update (Function.update y i u) j v ∘ σ₂))))) := by
  obtain ⟨f₁, hf₁⟩ := exists_factor_cov hs σ₁
  obtain ⟨f₂, hf₂⟩ := exists_factor_cov hs σ₂
  have inner : ∀ (w : Tup k L) (u : Fin L),
      (Finset.univ : Finset (Fin L)).val.map (fun v =>
        (s (Function.update (Function.update w i u) j v ∘ σ₁),
         s (Function.update (Function.update w i u) j v ∘ σ₂)))
      = (subst1 s (Function.update w i u) j).map (fun n => (f₁ n, f₂ n)) := by
    intro w u
    show _ = ((Finset.univ : Finset (Fin L)).val.map
      (fun v => s (Function.update (Function.update w i u) j v))).map (fun n => (f₁ n, f₂ n))
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl (fun v _ => ?_)
    show (s (Function.update (Function.update w i u) j v ∘ σ₁),
          s (Function.update (Function.update w i u) j v ∘ σ₂))
        = (f₁ (s (Function.update (Function.update w i u) j v)),
           f₂ (s (Function.update (Function.update w i u) j v)))
    rw [hf₁, hf₂]
  have key : ∀ w : Tup k L,
      Multiset.join ((Finset.univ : Finset (Fin L)).val.map (fun u =>
        (Finset.univ : Finset (Fin L)).val.map (fun v =>
          (s (Function.update (Function.update w i u) j v ∘ σ₁),
           s (Function.update (Function.update w i u) j v ∘ σ₂)))))
      = (substJoin s w i j).map (fun n => (f₁ n, f₂ n)) := by
    intro w
    unfold substJoin
    rw [Multiset.map_join, Multiset.map_map]
    exact congrArg Multiset.join (Multiset.map_congr rfl (fun u _ => inner w u))
  rw [key, key, substJoin_of_sigDet (sigDet_of_stableS hs) h i j]

end Subst

end Round

end TupleWL
end ChainDescent
