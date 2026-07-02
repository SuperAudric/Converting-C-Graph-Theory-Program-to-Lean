/-
# Route A, Step C — the accumulation predicate, made INDUCTIVE (the pinning closure)

**Why this module exists (recovery doc §9.7; the scoping correction of 2026-07-02).** `ScratchPlaneSep` isolated the
accumulation as the *one-shot* predicate `ChiProfileSeparatesPlane Q S₀ W` — "some pair in a **fixed** `S₀` χ-separates any
two distinct plane points." That form is subtly wrong as the target: its truth is hostage to what `S₀` is.

* With `S₀ = {0,a,b}` (the actual span-dim-2 base) it is **false** — O(1) base pairs give O(1) `χ`-bits, and Insight 1
  (`levelset_count_factors_through_chiDet`, each count is `χ(det)`-valued = 2-valued) says O(1) bits cannot separate the
  `Θ(q²)` plane points.
* With `S₀` large enough to be true, those anchor points must themselves be **pinned / 1-WL-colour-distinct** — which is
  precisely the "1-WL-computability wiring", and that wiring is an **induction** (the pinned set grows round by round), not
  a deferral. `jointIsoCountK Q w {t,t₀}` is 1-WL-visible **iff** `t, t₀` are colour-distinguished (individualised).

So the honest target is the **inductive closure** described in the doc's Route α: grow a pinned set `P ⊆ W`, anchored at
`{0,a,b}`; a plane point is pinned once its `χ(pairForm)`-profile over **already-pinned** anchor pairs separates it from
every other plane point. This module lands that reformulation (as a `Nat`-indexed closure of a monotone operator — the
nested-inductive form fails positivity) and threads it back into the existing reduction:

* `SeparatedBy Q P w w'` — one-round `χ(pairForm)` separation of `w, w'` using an anchor pair drawn from `P` (the body of
  `ChiProfileSeparatesPlane`, factored out); monotone in `P` (`SeparatedBy.mono`), symmetric (`SeparatedBy.symm`).
* `pinStep`/`pinIter`/`PinClosure` — the pinning closure: `pinIter 0 = {0,a,b}` (pinned by individualisation),
  `pinIter (n+1)` adds every `w ∈ W` that is `SeparatedBy (pinIter n)` from all of `W`; `PinClosure x := ∃ n, x ∈ pinIter n`.
* `PlanePinnable Q W a b := ∀ w ∈ W, PinClosure … w` — the **inductive Gauss target** (replaces the one-shot predicate as
  the thing to prove: the closure reaches all of `W`).
* `chiProfileSeparatesPlane_of_pinnable` — **the composition:** `PlanePinnable` (+ a small explicit `hbase` for the ≤3
  base–base pairs, discharged by individualisation, + `S₀ ⊇ pinned`) ⟹ `ChiProfileSeparatesPlane Q S₀ W`. So the inductive
  predicate plugs **directly** into `ScratchPlaneSep.count_profile_separates_of_kernel`.
* `count_profile_separates_of_pinnable` — the end-to-end: `PlanePinnable` ⟹ distinct plane points have different joint
  counts at some base pair (count-level, no fixed magic `S₀`).

**The wiring, stated precisely (the remaining obligation, now named).** The step's use of `pinIter n` anchors *is* the
1-WL-computability content: each pinned anchor is individualised in the descent (pinned in order via the closure), so its
colour is distinct, so `jointIsoCountK(·, {t,t₀})` for pinned `t,t₀` is a **1-WL increment** (determined by the stable
colour `C^∞`). Turning "joint-count profile injective on `W`" into "`C^∞` refines `zSet`" is the residual wiring — it needs
a WL-colour object (Route β) and is *not* re-proved here, but the closure structure is exactly what makes it dischargeable
(the anchors are reachable/individualisable in order, which the one-shot `S₀` did not certify).

Reuses `ScratchPlaneSep` (`ChiProfileSeparatesPlane`, `count_profile_separates_of_kernel`). Axiom-clean
`[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchPlaneSep

namespace ChainDescent.PlanePinInduction

open QuadraticMap ChainDescent.PlaneSep

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {d : ℕ}

set_option linter.unusedSectionVars false

/-- **One-round `χ(pairForm)` separation via an anchor pair from `P`.** `w, w'` are separated by `P` if some ordered pair
`t, t₀ ∈ P` is nondegenerate at both and gives different `χ(pairForm)` values. This is the inner body of
`ChiProfileSeparatesPlane`, with the anchors ranging over a set `P` (the pinned set) rather than a fixed base finset. -/
def SeparatedBy (Q : QuadraticForm K (Fin d → K)) (P : Set (Fin d → K)) (w w' : Fin d → K) : Prop :=
  ∃ t ∈ P, ∃ t₀ ∈ P,
    (pairForm Q (t₀ - w) (t - w) ≠ 0 ∧ pairForm Q (t₀ - w') (t - w') ≠ 0
      ∧ Q (t₀ - w) ≠ 0 ∧ Q (t₀ - w') ≠ 0)
    ∧ quadraticChar K (pairForm Q (t₀ - w) (t - w))
        ≠ quadraticChar K (pairForm Q (t₀ - w') (t - w'))

/-- Separation is monotone in the anchor set: more pinned anchors can only help. -/
theorem SeparatedBy.mono {Q : QuadraticForm K (Fin d → K)} {P P' : Set (Fin d → K)} (h : P ⊆ P')
    {w w' : Fin d → K} (hs : SeparatedBy Q P w w') : SeparatedBy Q P' w w' := by
  obtain ⟨t, htP, t₀, ht₀P, hnd, hchi⟩ := hs
  exact ⟨t, h htP, t₀, h ht₀P, hnd, hchi⟩

/-- Separation is symmetric up to reordering (the `χ` inequality is `Ne`, the nondegeneracy is a conjunction): if `P`
separates `w'` from `w`, it separates `w` from `w'` with the *same* anchors. -/
theorem SeparatedBy.symm {Q : QuadraticForm K (Fin d → K)} {P : Set (Fin d → K)} {w w' : Fin d → K}
    (hs : SeparatedBy Q P w' w) : SeparatedBy Q P w w' := by
  obtain ⟨t, htP, t₀, ht₀P, ⟨h1, h2, h3, h4⟩, hchi⟩ := hs
  exact ⟨t, htP, t₀, ht₀P, ⟨h2, h1, h4, h3⟩, hchi.symm⟩

/-- The seed of the pinning closure: the span-dim-2 base `{0, a, b}`, pinned by individualisation. -/
def seed (a b : Fin d → K) : Set (Fin d → K) := {0, a, b}

theorem mem_seed_iff {a b x : Fin d → K} : x ∈ seed a b ↔ x = 0 ∨ x = a ∨ x = b := by
  simp only [seed, Set.mem_insert_iff, Set.mem_singleton_iff]

/-- **One round of pinning.** Given a pinned set `P`, add every `w ∈ W` that is `SeparatedBy P` from every other point of
`W` (so its `χ`-profile over `P`-anchors is now distinctive). -/
def pinStep (Q : QuadraticForm K (Fin d → K)) (W : Set (Fin d → K)) (P : Set (Fin d → K)) :
    Set (Fin d → K) :=
  P ∪ {w | w ∈ W ∧ ∀ w' ∈ W, w' ≠ w → SeparatedBy Q P w w'}

/-- **The pinning closure, `Nat`-indexed.** `pinIter 0 = {0,a,b}`; each round applies `pinStep`. Monotone increasing. -/
def pinIter (Q : QuadraticForm K (Fin d → K)) (W : Set (Fin d → K)) (a b : Fin d → K) :
    ℕ → Set (Fin d → K)
  | 0 => seed a b
  | (n + 1) => pinStep Q W (pinIter Q W a b n)

/-- **The pinned set (the closure's union).** `x` is pinned if it enters at some round. -/
def PinClosure (Q : QuadraticForm K (Fin d → K)) (W : Set (Fin d → K)) (a b x : Fin d → K) : Prop :=
  ∃ n, x ∈ pinIter Q W a b n

/-- **The inductive Gauss target** (replaces the one-shot `ChiProfileSeparatesPlane`): the pinning closure, anchored at
`{0,a,b}`, reaches **all** of the plane `W`. This is what the WL iteration must achieve ("`C^∞` pins `W`"); proving it is
the seal's per-anchor + union assembly re-run over `W ≅ K²`, but now with the anchors *reachable in order* rather than a
fixed magic set. -/
def PlanePinnable (Q : QuadraticForm K (Fin d → K)) (W : Set (Fin d → K)) (a b : Fin d → K) : Prop :=
  ∀ w ∈ W, PinClosure Q W a b w

/-- Every element of any `pinIter n` is pinned. -/
theorem pinClosure_of_mem_pinIter {Q : QuadraticForm K (Fin d → K)} {W : Set (Fin d → K)}
    {a b x : Fin d → K} {n : ℕ} (h : x ∈ pinIter Q W a b n) : PinClosure Q W a b x :=
  ⟨n, h⟩

/-- **The extraction lemma — a pinned non-seed point carries its separation certificate.** If `x` is pinned but not a base
point, then at some round `m` it was `SeparatedBy (pinIter m)` from every other point of `W` — the certificate that pinned
it. Proved by induction on the round it enters. -/
theorem sep_of_mem_pinIter {Q : QuadraticForm K (Fin d → K)} {W : Set (Fin d → K)} {a b x : Fin d → K} :
    ∀ n, x ∈ pinIter Q W a b n → x ∉ seed a b →
      ∃ m, x ∈ W ∧ ∀ w' ∈ W, w' ≠ x → SeparatedBy Q (pinIter Q W a b m) x w' := by
  intro n
  induction n with
  | zero => intro hn hseed; exact absurd hn hseed
  | succ k ih =>
      intro hn hseed
      simp only [pinIter, pinStep, Set.mem_union, Set.mem_setOf_eq] at hn
      rcases hn with hk | hfresh
      · exact ih hk hseed
      · exact ⟨k, hfresh.1, hfresh.2⟩

/-- **★ The composition — the inductive target ⟹ the one-shot predicate.** If the pinning closure reaches all of `W`
(`PlanePinnable`), `S₀` contains every pinned point, and the ≤3 base–base pairs are separated (`hbase`, discharged by
individualisation), then the one-shot `ChiProfileSeparatesPlane Q S₀ W` holds — so the inductive predicate plugs straight
into `count_profile_separates_of_kernel`.

For a distinct pair `w, w'`: whichever of the two is a non-base pinned point supplies the separating anchor pair (its
anchors sit in some `pinIter m ⊆ S₀`); if only `w'` is non-base it is symmetrised (`SeparatedBy.symm`); if **both** are
base points the explicit `hbase` covers it. -/
theorem chiProfileSeparatesPlane_of_pinnable {Q : QuadraticForm K (Fin d → K)} {W : Set (Fin d → K)}
    {a b : Fin d → K} {S₀ : Finset (Fin d → K)}
    (hpinned : ∀ x, PinClosure Q W a b x → x ∈ S₀)
    (hbase : ∀ w ∈ W, ∀ w' ∈ W, (w = 0 ∨ w = a ∨ w = b) → (w' = 0 ∨ w' = a ∨ w' = b) → w ≠ w' →
      ∃ t ∈ S₀, ∃ t₀ ∈ S₀,
        (pairForm Q (t₀ - w) (t - w) ≠ 0 ∧ pairForm Q (t₀ - w') (t - w') ≠ 0
          ∧ Q (t₀ - w) ≠ 0 ∧ Q (t₀ - w') ≠ 0)
        ∧ quadraticChar K (pairForm Q (t₀ - w) (t - w))
            ≠ quadraticChar K (pairForm Q (t₀ - w') (t - w')))
    (hpin : PlanePinnable Q W a b) :
    ChiProfileSeparatesPlane Q S₀ W := by
  -- SeparatedBy over the pinned set ⟹ the ChiProfileSeparatesPlane body over `S₀`.
  have toS₀ : ∀ {u u' : Fin d → K}, SeparatedBy Q (setOf (PinClosure Q W a b)) u u' →
      ∃ t ∈ S₀, ∃ t₀ ∈ S₀,
        (pairForm Q (t₀ - u) (t - u) ≠ 0 ∧ pairForm Q (t₀ - u') (t - u') ≠ 0
          ∧ Q (t₀ - u) ≠ 0 ∧ Q (t₀ - u') ≠ 0)
        ∧ quadraticChar K (pairForm Q (t₀ - u) (t - u))
            ≠ quadraticChar K (pairForm Q (t₀ - u') (t - u')) := by
    intro u u' hsep
    obtain ⟨t, htP, t₀, ht₀P, hnd, hchi⟩ := hsep
    exact ⟨t, hpinned t htP, t₀, hpinned t₀ ht₀P, hnd, hchi⟩
  -- A non-base pinned point separates from any other point of `W` (via its certificate + monotonicity).
  have sepNonseed : ∀ {u u' : Fin d → K}, u ∈ W → u' ∈ W → u' ≠ u → u ∉ seed a b →
      SeparatedBy Q (setOf (PinClosure Q W a b)) u u' := by
    intro u u' huW hu'W hne huseed
    obtain ⟨n, hn⟩ := hpin u huW
    obtain ⟨m, _, hsep⟩ := sep_of_mem_pinIter n hn huseed
    exact (hsep u' hu'W hne).mono (fun y hy => pinClosure_of_mem_pinIter hy)
  intro w hwW w' hw'W hne
  by_cases hws : w ∈ seed a b
  · by_cases hw's : w' ∈ seed a b
    · exact hbase w hwW w' hw'W (mem_seed_iff.mp hws) (mem_seed_iff.mp hw's) hne
    · exact toS₀ (sepNonseed hw'W hwW hne hw's).symm
  · exact toS₀ (sepNonseed hwW hw'W (Ne.symm hne) hws)

/-- **★ End-to-end (count level) — the inductive target ⟹ the joint-count profile separates the plane.** With the seal's
global data, `PlanePinnable` (+ `hbase` + `S₀ ⊇ pinned`) makes the 2-round joint-count observable injective on `W`: distinct
plane points differ in `jointIsoCountK` at some base pair. Same conclusion as `count_profile_separates_of_kernel`, but keyed
on the **inductive** (reachable-anchor) predicate rather than a fixed magic `S₀` — so it composes with the wiring. -/
theorem count_profile_separates_of_pinnable {Q : QuadraticForm K (Fin d → K)} [Invertible (2 : K)]
    (hF : ringChar K ≠ 2) (hcardK : 2 < Fintype.card K) (hd : Even d)
    {R' : Type*} [Field R'] [CharZero R'] {ψ : AddChar K R'} (hψ : ψ.IsPrimitive)
    (vb : Module.Basis (Fin (Module.finrank K (Fin d → K))) K (Fin d → K))
    (hv : (QuadraticMap.associated (R := K) Q).IsOrthoᵢ vb) (hw : ∀ i, Q (vb i) ≠ 0)
    {W : Set (Fin d → K)} {a b : Fin d → K} {S₀ : Finset (Fin d → K)}
    (hpinned : ∀ x, PinClosure Q W a b x → x ∈ S₀)
    (hbase : ∀ w ∈ W, ∀ w' ∈ W, (w = 0 ∨ w = a ∨ w = b) → (w' = 0 ∨ w' = a ∨ w' = b) → w ≠ w' →
      ∃ t ∈ S₀, ∃ t₀ ∈ S₀,
        (pairForm Q (t₀ - w) (t - w) ≠ 0 ∧ pairForm Q (t₀ - w') (t - w') ≠ 0
          ∧ Q (t₀ - w) ≠ 0 ∧ Q (t₀ - w') ≠ 0)
        ∧ quadraticChar K (pairForm Q (t₀ - w) (t - w))
            ≠ quadraticChar K (pairForm Q (t₀ - w') (t - w')))
    (hpin : PlanePinnable Q W a b)
    {w w' : Fin d → K} (hwW : w ∈ W) (hw'W : w' ∈ W) (hne : w ≠ w') :
    ∃ t ∈ S₀, ∃ t₀ ∈ S₀, jointIsoCountK Q w {t, t₀} ≠ jointIsoCountK Q w' {t, t₀} :=
  count_profile_separates_of_kernel Q hF hcardK hd hψ vb hv hw
    (chiProfileSeparatesPlane_of_pinnable hpinned hbase hpin) hwW hw'W hne

end ChainDescent.PlanePinInduction
