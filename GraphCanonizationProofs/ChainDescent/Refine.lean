import ChainDescent.Descend
import ChainDescent.RouteCTransport

/-!
# The encode-free refinement round — the `Refiner` instance for `descend`

(`docs/chain-descent-cost-model.md` D7 fork ii; `docs/chain-descent-mixed-composition.md` §1.4 bake-in 3.)

`descend` (`Descend.lean`) takes its refinement round as a **parameter** precisely so that the
`Encodable.encode` colour blow-up is not baked into the object. This file supplies **the instance** and
discharges both of its obligations:

* **`RefineEquivariant`** — the round commutes with relabelling. This is the hypothesis the whole of `①b`
  (`isoInvariantOpt_canonForm?`) was carrying.
* **`RefineSplits`** — the round only ever *refines* (it never merges two colour classes). This is what
  discharges **totality** (`canonForm?_ne_none`): individualization then strictly increases the colour count each
  level, so a leaf is reached within `n` levels and the descent **never flags on fuel**.

## Why encode-free — and why "renumber the output" is NOT enough (a corrected finding)

The stock round is `refineStep adj P χ v = Encodable.encode (sigKey adj P χ v)` (`ChainDescent.lean`), and
`Encodable.encode : List ℕ → ℕ` is a **pairing tower**. The earlier diagnosis (cost-model D7, `ScratchRenumber`)
was that the problem is *cross-round compounding* (`encode ∘ encode ∘ …`) and that the cure is to **renumber each
round's output** to its rank `0..n-1` (`vertexRankNat ∘ refineStep`). **That diagnosis is incomplete.** Measured
here: a **single** `refineStep` at `n = 3` already fails to `#eval` to completion — the encoded *value* is
infeasible after **one** round, before any compounding. Renumbering the output cannot help, because the encode is
still paid once per vertex per round.

**The genuinely encode-free round drops `Encodable.encode` entirely.** `sigKey` is *already* a canonically-sorted
`List Nat`, and `Descend.lexLeList` is *already* proved a total order (`lexLeList_{refl,total,trans,antisymm}`), so
the round can rank the **keys themselves** under that order and never form a `Nat` encoding at all. Colours land in
`0..n-1` by construction (`refineRound_lt`), and the partition is unchanged (`sigKey_eq_iff`).

Two further notes, both load-bearing:

* **Reification must be on the DATA, not inside a closure** — see `roundVec` / `warmRefineMat`. Materialising a
  round as `let keys := …; fun v => …` does *not* memoise; the compiler floats the `let` into the lambda and the
  work is redone on every lookup.
* **No `@[implemented_by]`.** The fast version is tied to the slow one by a *proved equation* (`warmRefineMat_eq`),
  never by an unchecked implementation swap (which can assert a false equation and make `#eval` lie — a firewall
  risk).

The `PMatrix` argument of `sigKey` is instantiated to the **constant** `constP`; the descent's refiner takes only
`(adj, χ)`, and a constant `P` transports trivially (`hP` below is `rfl`).

## ⚠ KNOWN EXECUTABLE LIMIT (proofs unaffected)

The refiner itself evaluates fine at every depth. But the **exhaustive** descent (`deferAll`) currently completes
only up to `n = 4`: `Colouring n = Fin n → Nat` means each descent level's colouring is a *closure* over its
parent's, and Lean's compiler does not reliably share the materialised vector across levels (`@[noinline]` on
`fromVec` / `warmRefineMat` does not suffice), so a depth-`d` colour lookup can re-run the refinement. It is easy
to miss: a **top-level `def`** colouring *is* cached, so testing the levels in isolation looks fine.

This is a *runtime-representation* issue, **not** a correctness one — every theorem in this file and in
`Descend.lean` is unaffected. The clean fix is to thread a materialised `Vector Nat n` through `descend` instead of
a `Colouring n` (a signature change to the object, to be decided deliberately).
-/

namespace ChainDescent
namespace Refine

open ChainDescent.CostModel (CostM)
open ChainDescent.Descend (transportColouring RefineEquivariant RefineSplits Refiner)

variable {n : Nat}

/-! ## 1. Rank compression is a partition congruence -/

/-- `vertexRankNat` is strictly monotone in the colour value. -/
theorem rankNat_strict_mono {ψ : Colouring n} {v w : Fin n} (hvw : ψ v < ψ w) :
    Colouring.vertexRankNat ψ v < Colouring.vertexRankNat ψ w := by
  unfold Colouring.vertexRankNat
  apply Finset.card_lt_card
  refine ⟨fun u hu => ?_, fun hsub => ?_⟩
  · rw [Finset.mem_filter] at hu ⊢
    exact ⟨hu.1, lt_trans hu.2 hvw⟩
  · have hvf : v ∈ Finset.univ.filter (fun u => ψ u < ψ w) := by
      rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hvw⟩
    have hnotv : v ∉ Finset.univ.filter (fun u => ψ u < ψ v) := by
      rw [Finset.mem_filter]; intro hh; exact lt_irrefl _ hh.2
    exact hnotv (hsub hvf)

/-- **Rank compression preserves the partition**: two vertices share a rank iff they share a colour. This is why
renumbering is *canonical* — same fibres, same order — and it is what makes `refineRound` interchangeable with
`refineStep` at the partition level. -/
theorem vertexRankNat_eq_iff {ψ : Colouring n} {v w : Fin n} :
    Colouring.vertexRankNat ψ v = Colouring.vertexRankNat ψ w ↔ ψ v = ψ w := by
  constructor
  · intro h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact absurd h (Nat.ne_of_lt (rankNat_strict_mono hlt))
    · exact absurd h.symm (Nat.ne_of_lt (rankNat_strict_mono hgt))
  · intro h
    unfold Colouring.vertexRankNat
    rw [h]

/-- **Rank compression transports.** If `ψ₂ ∘ g = ψ₁` then the ranks agree along `g`. (The rank counts
strictly-smaller vertices, and `g` is a bijection of that set.) -/
theorem vertexRankNat_transport {ψ₁ ψ₂ : Colouring n} {g : Equiv.Perm (Fin n)}
    (h : ∀ v, ψ₂ (g v) = ψ₁ v) (v : Fin n) :
    Colouring.vertexRankNat ψ₂ (g v) = Colouring.vertexRankNat ψ₁ v := by
  unfold Colouring.vertexRankNat
  rw [h v]
  apply Finset.card_bij (fun u _ => g.symm u)
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    rw [← h (g.symm a), Equiv.apply_symm_apply]
    exact ha
  · intro a _ b _ hab
    exact g.symm.injective hab
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    refine ⟨g b, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [h b]
    exact hb

/-! ## 2. The encode-free round

**★ The fix is to drop `Encodable.encode` ENTIRELY, not to compress its output.** The stock round is
`refineStep = Encodable.encode ∘ sigKey`, and `Encodable.encode : List ℕ → ℕ` is a pairing tower — the encoded
*value* is already infeasible after one round (measured: a single `refineStep` on `n = 3` does not `#eval` to
completion). So renumbering the round's *output* (`vertexRankNat ∘ refineStep`, the earlier `ScratchRenumber`
primitive) does **not** fix the executable: it breaks the cross-round compounding but still pays the encode once
per vertex per round.

The genuinely encode-free round ranks the **`sigKey` lists directly** under a computable lexicographic order.
`sigKey` is *already* a canonically-sorted `List Nat` (`ChainDescent.lean`), and `Descend.lexLeList` is *already*
proved to be a total order (`lexLeList_{refl,total,trans,antisymm}`) — so the rank is well-defined and no `Nat`
encoding is ever formed. Colours land in `0..n-1` by construction. -/

/-- The constant pair-matrix. The descent's refiner sees only `(adj, χ)`, and a constant `P` transports
trivially — so the `PMatrix` layer contributes no obligation. -/
def constP (n : Nat) : PMatrix n := fun _ _ => POE.unknown

/-- The refinement **key** of a vertex: its old colour followed by its sorted signature. Already a `List Nat`. -/
def keyOf (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) : List Nat :=
  sigKey adj (constP n) χ v

/-- Strict lexicographic order on keys (computable; `Descend.lexLeList` is a proved total order). -/
def keyLt (a b : List Nat) : Bool := Descend.lexLeList a b && !Descend.lexLeList b a

theorem keyLt_irrefl (a : List Nat) : keyLt a a = false := by
  simp [keyLt, Descend.lexLeList_refl a]

theorem keyLt_trans {a b c : List Nat} (h1 : keyLt a b = true) (h2 : keyLt b c = true) :
    keyLt a c = true := by
  simp only [keyLt, Bool.and_eq_true, Bool.not_eq_true'] at h1 h2 ⊢
  refine ⟨Descend.lexLeList_trans a b c h1.1 h2.1, ?_⟩
  by_contra hca
  simp only [Bool.not_eq_false] at hca
  exact absurd (Descend.lexLeList_trans c a b hca h1.1) (by rw [h2.2]; simp)

/-- Distinct keys are strictly comparable (the order is total, and antisymmetric). -/
theorem keyLt_of_ne {a b : List Nat} (h : a ≠ b) : keyLt a b = true ∨ keyLt b a = true := by
  rcases Descend.lexLeList_total a b with hab | hba
  · by_cases hba : Descend.lexLeList b a = true
    · exact absurd (Descend.lexLeList_antisymm a b hab hba) h
    · have hba' : Descend.lexLeList b a = false := by simpa using hba
      exact Or.inl (by simp [keyLt, hab, hba'])
  · by_cases hab : Descend.lexLeList a b = true
    · exact absurd (Descend.lexLeList_antisymm a b hab hba) h
    · have hab' : Descend.lexLeList a b = false := by simpa using hab
      exact Or.inr (by simp [keyLt, hba, hab'])

/-- **One encode-free refinement round** — recolour each vertex by the **rank of its key** among all keys. No
`Encodable.encode` anywhere; colours land in `0..n-1` by construction. -/
def refineRound (adj : AdjMatrix n) (χ : Colouring n) : Colouring n :=
  fun v => (Finset.univ.filter (fun u => keyLt (keyOf adj χ u) (keyOf adj χ v) = true)).card

/-- **Colours never blow up** — the whole point of the fork. (`v` is never strictly below itself, so the rank
counts a *proper* subset of the vertices.) -/
theorem refineRound_lt (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) :
    refineRound adj χ v < n := by
  show (Finset.univ.filter (fun u => keyLt (keyOf adj χ u) (keyOf adj χ v) = true)).card < n
  have hlt : (Finset.univ.filter (fun u => keyLt (keyOf adj χ u) (keyOf adj χ v) = true)).card
      < (Finset.univ : Finset (Fin n)).card := by
    apply Finset.card_lt_card
    refine ⟨Finset.filter_subset _ _, fun hsub => ?_⟩
    have hv := hsub (Finset.mem_univ v)
    rw [Finset.mem_filter] at hv
    exact absurd hv.2 (by rw [keyLt_irrefl]; simp)
  rw [Finset.card_univ, Fintype.card_fin] at hlt
  exact hlt

/-- The rank is **strictly monotone** in the key. -/
theorem refineRound_strict_mono {adj : AdjMatrix n} {χ : Colouring n} {v w : Fin n}
    (h : keyLt (keyOf adj χ v) (keyOf adj χ w) = true) :
    refineRound adj χ v < refineRound adj χ w := by
  apply Finset.card_lt_card
  refine ⟨fun u hu => ?_, fun hsub => ?_⟩
  · rw [Finset.mem_filter] at hu ⊢
    exact ⟨hu.1, keyLt_trans hu.2 h⟩
  · have hvf : v ∈ Finset.univ.filter (fun u => keyLt (keyOf adj χ u) (keyOf adj χ w) = true) := by
      rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, h⟩
    have hnotv : v ∉ Finset.univ.filter (fun u => keyLt (keyOf adj χ u) (keyOf adj χ v) = true) := by
      rw [Finset.mem_filter]; intro hh
      exact absurd hh.2 (by rw [keyLt_irrefl]; simp)
    exact hnotv (hsub hvf)

/-- **The round has the same partition as the key**: equal rank ⟺ equal key. -/
theorem refineRound_eq_iff (adj : AdjMatrix n) (χ : Colouring n) (v w : Fin n) :
    refineRound adj χ v = refineRound adj χ w ↔ keyOf adj χ v = keyOf adj χ w := by
  constructor
  · intro h
    by_contra hne
    rcases keyLt_of_ne hne with hlt | hgt
    · exact absurd h (Nat.ne_of_lt (refineRound_strict_mono hlt))
    · exact absurd h.symm (Nat.ne_of_lt (refineRound_strict_mono hgt))
  · intro h
    unfold refineRound
    rw [h]

/-- **The round only REFINES** — it never merges two colour classes. (`sigKey_eq_iff`: equal keys ⟹ equal old
colour ∧ equal signature.) -/
theorem refineRound_splits (adj : AdjMatrix n) (χ : Colouring n) (x y : Fin n)
    (h : refineRound adj χ x = refineRound adj χ y) : χ x = χ y :=
  ((sigKey_eq_iff adj (constP n) χ x y).mp ((refineRound_eq_iff adj χ x y).mp h)).1

/-- **The key transports** — rides `sigKey_transport_iso` (`RouteCTransport`); the `PMatrix` hypothesis is `rfl`
because `constP` is constant. -/
theorem keyOf_transport (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) :
    keyOf (relabelAdj σ adj) (transportColouring σ χ) (σ v) = keyOf adj χ v := by
  have hf : ∀ v w : Fin n, (relabelAdj σ adj).adj (σ v) (σ w) = adj.adj v w := by
    intro v w; simp
  have hP : ∀ v u : Fin n, constP n (σ v) (σ u) = constP n v u := fun _ _ => rfl
  have hχ : ∀ v : Fin n, transportColouring σ χ (σ v) = χ v := by
    intro v; show χ (σ.symm (σ v)) = χ v; simp
  exact sigKey_transport_iso hf hP hχ v

/-- **The round is EQUIVARIANT** — it commutes with relabelling. The rank counts strictly-smaller keys, and `σ` is
a bijection of that set. -/
theorem refineRound_equivariant (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n) :
    refineRound (relabelAdj σ adj) (transportColouring σ χ)
      = transportColouring σ (refineRound adj χ) := by
  funext u
  show (Finset.univ.filter (fun x =>
        keyLt (keyOf (relabelAdj σ adj) (transportColouring σ χ) x)
              (keyOf (relabelAdj σ adj) (transportColouring σ χ) u) = true)).card
      = (Finset.univ.filter (fun x =>
        keyLt (keyOf adj χ x) (keyOf adj χ (σ.symm u)) = true)).card
  have hu : keyOf (relabelAdj σ adj) (transportColouring σ χ) u = keyOf adj χ (σ.symm u) := by
    have := keyOf_transport σ adj χ (σ.symm u)
    rwa [Equiv.apply_symm_apply] at this
  rw [hu]
  apply Finset.card_bij (fun x _ => σ.symm x)
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    have ha' : keyOf (relabelAdj σ adj) (transportColouring σ χ) a = keyOf adj χ (σ.symm a) := by
      have := keyOf_transport σ adj χ (σ.symm a)
      rwa [Equiv.apply_symm_apply] at this
    rwa [ha'] at ha
  · intro a _ b _ hab
    exact σ.symm.injective hab
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    refine ⟨σ b, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rwa [keyOf_transport σ adj χ b]

/-! ## 3. The warm round (`n` iterations) — the actual `Refiner` -/

/-- **Encode-free warm refinement**: `n` encode-free rounds. -/
def warmRefineR (adj : AdjMatrix n) (χ : Colouring n) : Colouring n :=
  (refineRound adj)^[n] χ

theorem iterate_splits (adj : AdjMatrix n) :
    ∀ (k : Nat) (χ : Colouring n) (x y : Fin n),
      ((refineRound adj)^[k] χ) x = ((refineRound adj)^[k] χ) y → χ x = χ y := by
  intro k
  induction k with
  | zero => intro χ x y h; exact h
  | succ k ih =>
      intro χ x y h
      rw [Function.iterate_succ_apply] at h
      exact refineRound_splits adj χ x y (ih (refineRound adj χ) x y h)

theorem iterate_equivariant (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) :
    ∀ (k : Nat) (χ : Colouring n),
      ((refineRound (relabelAdj σ adj))^[k] (transportColouring σ χ))
        = transportColouring σ ((refineRound adj)^[k] χ) := by
  intro k
  induction k with
  | zero => intro χ; rfl
  | succ k ih =>
      intro χ
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
          refineRound_equivariant σ adj χ, ih (refineRound adj χ)]

/-- **★ THE REFINER** — the encode-free warm round, with the cost model's own refinement cost (`n³`). This is the
instance `descend`'s `refine` parameter was left open for. -/
def encodeFree : Refiner n :=
  fun adj χ => (warmRefineR adj χ, CostModel.WarmRefine.warmRefineCost n)

@[simp] theorem refineV_encodeFree (adj : AdjMatrix n) (χ : Colouring n) :
    Descend.refineV (encodeFree (n := n)) adj χ = warmRefineR adj χ := rfl

/-- **★ OBLIGATION 1 DISCHARGED — the refiner is EQUIVARIANT.** This is the hypothesis `①b`
(`isoInvariantOpt_canonForm?`) has been carrying. -/
theorem refineEquivariant_encodeFree : RefineEquivariant (encodeFree (n := n)) := by
  intro σ adj χ
  show warmRefineR (relabelAdj σ adj) (transportColouring σ χ)
      = transportColouring σ (warmRefineR adj χ)
  exact iterate_equivariant σ adj n χ

/-- **★ OBLIGATION 2 DISCHARGED — the refiner genuinely REFINES.** This is what makes the descent *total*
(`canonForm?_ne_none`): the flag is never a fuel artefact. -/
theorem refineSplits_encodeFree : RefineSplits (encodeFree (n := n)) := by
  intro adj χ x y h
  exact iterate_splits adj n χ x y h

/-! ## 4. The `#eval`-able version — reification (value-equal, NOT `@[implemented_by]`)

`refineRound` recomputes every vertex's `keyOf` once per *comparison*, so a round costs `n²` signature builds and
the `χ` it reads is the previous round's closure — nesting the rounds explodes exponentially. The fast version is
tied to the slow one by a **proved equation** (`warmRefineMat_eq`), so all the theorems above transfer and `#eval`
cannot lie.

**⚠ The reification must be on the DATA, not inside a closure.** Writing a round as
`let keys := Vector.ofFn …; fun v => ranked.get v` does *not* memoise: iterating it nests closures, each call
rebuilds the vector, and the cost is exponential in the round count (measured — a warm round over such a
"reified" round hangs at `n = 3`, while the unreified `refineRound` runs instantly). The cure is to iterate on a
strict `Vector Nat n` and only expose a `Colouring` at the very end. -/

/-- One encode-free round **on materialised data**. Every vertex's key is computed **once** (otherwise `sigKey`,
and with it the whole signature multiset, is recomputed `n²` times per round). -/
def roundVec (adj : AdjMatrix n) (c : Vector Nat n) : Vector Nat n :=
  let keys := Vector.ofFn (fun v => keyOf adj (fun u => c.get u) v)
  Vector.ofFn (fun v =>
    (Finset.univ.filter (fun u => keyLt (keys.get u) (keys.get v) = true)).card)

theorem roundVec_get (adj : AdjMatrix n) (c : Vector Nat n) (v : Fin n) :
    (roundVec adj c).get v = refineRound adj (fun u => c.get u) v := by
  simp [roundVec, refineRound, keyOf, Vector.get]

theorem roundVec_ofFn (adj : AdjMatrix n) (χ : Colouring n) :
    roundVec adj (Vector.ofFn χ) = Vector.ofFn (refineRound adj χ) := by
  apply Vector.ext
  intro i hi
  have h := roundVec_get adj (Vector.ofFn χ) ⟨i, hi⟩
  simpa [Vector.get, Vector.getElem_ofFn] using h

/-- View a materialised vector as a colouring. **`@[noinline]` is load-bearing** — see `warmRefineMat`. -/
@[noinline] def fromVec (out : Vector Nat n) : Colouring n := fun v => out.get v

/-- **The runnable warm round** — `n` rounds, iterated on strict `Vector` data.

**⚠ The vector is passed as an ARGUMENT to `fromVec`, and that is the whole trick.** The descent threads
colourings as *functions* (`Colouring n = Fin n → Nat`). A colouring built as `let out := <expensive>; fun v =>
out.get v` does **not** memoise — the compiler floats the `let` into the lambda, so `<expensive>` re-runs on every
lookup. Since each descent level's colouring closes over its parent's, that makes a depth-`d` colour lookup cost
*exponential in `d`*, and the exhaustive descent hangs at `n = 5` (measured; it is easy to miss, because a
top-level `def` colouring **is** cached, so testing the levels in isolation looks fine). Lean's compiled code is
**call-by-value**, so making the vector a function *argument* forces it exactly once, when the colouring is
constructed. Each level's colouring is then a genuine lookup table. -/
@[noinline] def warmRefineMat (adj : AdjMatrix n) (χ : Colouring n) : Colouring n :=
  fromVec ((roundVec adj)^[n] (Vector.ofFn χ))

theorem iterate_roundVec (adj : AdjMatrix n) :
    ∀ (k : Nat) (χ : Colouring n),
      (roundVec adj)^[k] (Vector.ofFn χ) = Vector.ofFn ((refineRound adj)^[k] χ) := by
  intro k
  induction k with
  | zero => intro χ; rfl
  | succ k ih =>
      intro χ
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, roundVec_ofFn adj χ]
      exact ih (refineRound adj χ)

/-- **The runnable version computes exactly the reasoned-about one.** -/
theorem warmRefineMat_eq (adj : AdjMatrix n) (χ : Colouring n) :
    warmRefineMat adj χ = warmRefineR adj χ := by
  funext v
  show ((roundVec adj)^[n] (Vector.ofFn χ)).get v = ((refineRound adj)^[n] χ) v
  rw [iterate_roundVec adj n χ]
  simp [Vector.get, Vector.getElem_ofFn]

/-- **The runnable refiner** — value-equal to `encodeFree` (`encodeFreeFast_eq`), so it inherits *every* theorem
above; only the evaluation strategy differs. This is the one to `#eval`. -/
def encodeFreeFast : Refiner n :=
  fun adj χ => (warmRefineMat adj χ, CostModel.WarmRefine.warmRefineCost n)

theorem encodeFreeFast_eq : encodeFreeFast (n := n) = encodeFree (n := n) := by
  funext adj χ
  show (warmRefineMat adj χ, _) = (warmRefineR adj χ, _)
  rw [warmRefineMat_eq]

theorem refineEquivariant_encodeFreeFast : RefineEquivariant (encodeFreeFast (n := n)) := by
  rw [encodeFreeFast_eq]; exact refineEquivariant_encodeFree

theorem refineSplits_encodeFreeFast : RefineSplits (encodeFreeFast (n := n)) := by
  rw [encodeFreeFast_eq]; exact refineSplits_encodeFree

/-! ## 5. ★ THE PAYOFF — the descent, fully instantiated on its refiner

With the encode-free round plugged in, the only hypothesis left on the whole canonizer is the **resolver**
contract (`NarrowTransport`). For the exhaustive resolver (`deferAll`, which satisfies it) there is **no
hypothesis at all**: the object is unconditionally a canonical form, and it unconditionally **answers**. -/

/-- **The canonizer, on the encode-free refiner, modulo ONLY the resolver contract.** -/
theorem isCanonicalFormOpt_encodeFree {R : Descend.Resolver n}
    (hnt : Descend.NarrowTransport (encodeFree (n := n)) R) :
    CanonSpec.IsCanonicalFormOpt (Descend.canonForm? (encodeFree (n := n)) R) :=
  Descend.isCanonicalFormOpt_canonForm? refineEquivariant_encodeFree hnt

/-- **★★ THE EXHAUSTIVE CANONIZER IS UNCONDITIONALLY A CANONICAL FORM THAT ANSWERS.**

No carried hypotheses whatsoever: `①a`, `①b`, `①c` hold, **and** the descent never flags. This is the
non-vacuity anchor for the whole track — every resolver added from here only *narrows*, shrinking the flagged
residue, and can never break this. -/
theorem exhaustive_canonizer :
    CanonSpec.IsCanonicalFormOpt (Descend.canonForm? (encodeFree (n := n)) Descend.deferAll)
    ∧ ∀ adj : AdjMatrix n, Descend.canonForm? (encodeFree (n := n)) Descend.deferAll adj ≠ none :=
  ⟨Descend.isCanonicalFormOpt_canonForm? refineEquivariant_encodeFree
      (Descend.narrowTransport_deferAll refineEquivariant_encodeFree),
   fun adj => Descend.canonForm?_ne_none refineSplits_encodeFree Descend.narrowProper_deferAll adj⟩

end Refine
end ChainDescent
