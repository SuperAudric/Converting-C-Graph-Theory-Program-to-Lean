/-
# Route A, Step C — Piece 1c: discharging `GramCountsRecoverGram` — the factorization core

**What this module builds (recovery doc §9.7, the discharge of `GramCountsRecoverGram`).** The open Gauss content of
Route A is `GramCountsRecoverGram`: at a `GoodBase`, `SameGramStratCounts u u'` ⟹ `SameExactGram Q {a,b} u u'` + the
plane flag. This module lands the **correct analytic core** of that discharge — the *factorization* of the count's
`g`-Fourier transform — which pinpoints exactly where `u`'s Gram lives and reduces the whole lemma to a classical
character-sum non-degeneracy over the isotropic cone.

**★ Why this is the right core (a correction to the older "fibre-sum" plan).** The older plan (recovery §9.7,
Piece 1c(ii)/(iii)) proposed to *Fourier-invert the `innerZ` fibre sums* and read `u`'s Gram off the bulk term. That
step is **empty**: the `r₃`-marginal of `innerZ` that `sameGramStratCounts_transform` produces is exactly `|K|` times
the `g`-Fourier transform of the count itself (see `countHat_eq_isoSum` below), so equal counts give it *for free* — the
individual `innerZ_u(r)` that carry the Gram are **not** recoverable from the observable. Dually, the *elementary*
first-moment shortcut (`∑_g g · count u g = N · gramK u`, `N = #{w : Q w = 0}`) **fails in characteristic `p`**: `N` is
divisible by `q = |K|`, so `N` cannot be cancelled in `K`. Both dead ends have the same moral: `u`'s Gram must be read
off the **phase** `ψ(⟨t, gramK u⟩) ∈ R'` (no char-`p` degeneracy), which is what the factorization below exposes.

* `countHat Q a b u ψ t = ∑_g ψ(⟨t,g⟩) · gramStratCount u g` — the `g`-Fourier transform of the count profile.
* `isoConeSum Q ψ y = ∑_{w : Q w = 0} ψ(polar Q w y)` — the isotropic-cone character sum (the classical object).
* **`countHat_eq_isoSum`** — `countHat u t = ∑_{z : Q(u−z)=0} ψ(⟨t, gramK z⟩)`: the transform is the character sum over
  the vertices isotropic to `u`, stratified by their Gram to the base (pull the count into the sum, fibrewise).
* **`countHat_factor`** — **the core.** Shifting `z = u + w`, `⟨t, gramK(u+w)⟩ = ⟨t, gramK u⟩ + polar w y`
  (`y = t₀•u + t₁•a + t₂•b`, using `Q w = 0`), so
  `countHat u t = ψ(⟨t, gramK u⟩) · isoConeSum Q ψ (t₀•u + t₁•a + t₂•b)`.
  `u` enters **only** through the phase `ψ(⟨t, gramK u⟩)` (its exact Gram to `{a,b}`) and through `y` inside
  `isoConeSum` (whose value depends on `y` only through `Q y` — the dual Gram — and the flag `y = 0 ⟺ …`).
* **`countHat_eq_of_sameGramStratCounts`** — `SameGramStratCounts u u' ⟹ countHat u = countHat u'` (trivial).

**Remaining crux (isolated, classical).** With the factorization, `GramCountsRecoverGram` reduces to: the equality of
`ψ(⟨t, gramK u⟩) · isoConeSum(t₀•u+t₁•a+t₂•b)` for all `t` forces `gramK u = gramK u'` (⟹ `SameExactGram`) and the flag.
This is a **non-degeneracy of the isotropic-cone Gauss sum** (`isoConeSum`), a classical finite-field character-sum fact
(Lidl–Niederreiter-style), independent of the whole `gramStrat` apparatus — the honest single remaining Gauss statement.
The attack: on the `t₀ = 0` slice `y = t₁•a + t₂•b` is `u`-independent, so `isoConeSum` factors out and the phase pins
`polar u a`, `polar u b` (modulo the zero-set of the cone sum); the `t₀ ≠ 0` part then pins `Q u`; the flag is
`u ∈ span{a,b} ⟺ ∃ t₀≠0, t₀•u+t₁•a+t₂•b = 0`. `isoConeSum`'s closed form (complete the square, `GaussCount` Brick D1
`sum_addChar_quadForm_linear` on `𝟙[Qw=0] = |K|⁻¹∑_s ψ(s·Qw)`) is `|K|⁻¹(|V|·𝟙[y=0] + ∑_{s≠0} ψ(−s⁻¹·Qy)·G(s))`, the
input to the zero-set analysis. See `ScratchGramStratGaussReduce` / recovery §9.7 for the isolated predicate + status.

Reuses `ScratchGramStratCount` (`gramK`, `gramStratCount`, `SameGramStratCounts`). Factorization needs **no** Gauss
brick, no primitivity, no `IsDomain` — any `CommRing R'`, any `ψ`. Axiom-clean `[propext, Classical.choice, Quot.sound]`,
`lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchGramStratCount

namespace ChainDescent.GramStrat

open QuadraticMap Finset

set_option linter.unusedSectionVars false

variable {K V : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V] {Q : QuadraticForm K V}

/-- **The `g`-Fourier transform of the round-3 count profile.** `∑_g ψ(t₀g₀+t₁g₁+t₂g₂) · gramStratCount u g`. -/
noncomputable def countHat (Q : QuadraticForm K V) (a b u : V) {R' : Type*} [CommRing R']
    (ψ : AddChar K R') (t : K × K × K) : R' :=
  ∑ g : K × K × K, ψ (t.1 * g.1 + t.2.1 * g.2.1 + t.2.2 * g.2.2) * (gramStratCount Q a b u g : R')

/-- **The isotropic-cone character sum** `∑_{w : Q w = 0} ψ(polar Q w y)`. Classical finite-field Gauss object; the
carrier of the remaining non-degeneracy. -/
noncomputable def isoConeSum (Q : QuadraticForm K V) {R' : Type*} [CommRing R']
    (ψ : AddChar K R') (y : V) : R' :=
  ∑ w : V, if Q w = 0 then ψ (QuadraticMap.polar Q w y) else 0

/-- **Trivial direction — equal counts ⟹ equal transforms.** `countHat` is `R'`-linear in the count, so
`SameGramStratCounts` gives it for free. This is *all* the observable-equality yields (no Gram info yet); the content is
the factorization. -/
theorem countHat_eq_of_sameGramStratCounts (a b : V) {u u' : V}
    (h : SameGramStratCounts Q a b u u') {R' : Type*} [CommRing R'] (ψ : AddChar K R')
    (t : K × K × K) : countHat Q a b u ψ t = countHat Q a b u' ψ t := by
  unfold countHat
  exact Finset.sum_congr rfl (fun g _ => by rw [h g])

/-- **The transform is the isotropy-stratified character sum.** `countHat u t = ∑_{z : Q(u−z)=0} ψ(⟨t, gramK z⟩)` —
pull the count into the sum fibrewise over `gramK`. -/
theorem countHat_eq_isoSum (Q : QuadraticForm K V) (a b u : V) {R' : Type*} [CommRing R']
    (ψ : AddChar K R') (t : K × K × K) :
    countHat Q a b u ψ t
      = ∑ z ∈ Finset.univ.filter (fun z => Q (u - z) = 0),
          ψ (t.1 * Q z + t.2.1 * QuadraticMap.polar Q z a + t.2.2 * QuadraticMap.polar Q z b) := by
  unfold countHat gramStratCount
  -- distribute ψ over the card (= sum of ones), and on each fibre replace g by gramK z
  have step1 : ∀ g : K × K × K,
      ψ (t.1 * g.1 + t.2.1 * g.2.1 + t.2.2 * g.2.2)
          * ((Finset.univ.filter (fun z => gramK Q a b z = g ∧ Q (u - z) = 0)).card : R')
        = ∑ z ∈ Finset.univ.filter (fun z => gramK Q a b z = g ∧ Q (u - z) = 0),
            ψ (t.1 * Q z + t.2.1 * QuadraticMap.polar Q z a + t.2.2 * QuadraticMap.polar Q z b) := by
    intro g
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun z hz => ?_)
    rw [Finset.mem_filter] at hz
    obtain ⟨-, hgz, -⟩ := hz
    rw [Nat.cast_one, mul_one, ← hgz]
    simp only [gramK]
  rw [Finset.sum_congr rfl (fun g _ => step1 g)]
  -- collapse the fibrewise double sum
  have hfib := Finset.sum_fiberwise (Finset.univ.filter (fun z => Q (u - z) = 0))
    (fun z => gramK Q a b z)
    (fun z => ψ (t.1 * Q z + t.2.1 * QuadraticMap.polar Q z a + t.2.2 * QuadraticMap.polar Q z b))
  rw [← hfib]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  refine Finset.sum_congr ?_ (fun z _ => rfl)
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_comm]

/-- **★ The factorization — the analytic core of `GramCountsRecoverGram`.** Shifting `z = u + w`
(`Q(u−z) = Q(−w) = Q w`), for `w` isotropic `⟨t, gramK(u+w)⟩ = ⟨t, gramK u⟩ + polar w (t₀•u + t₁•a + t₂•b)`, so
`countHat u t = ψ(⟨t, gramK u⟩) · isoConeSum Q ψ (t₀•u + t₁•a + t₂•b)`. `u`'s exact Gram to `{a,b}` sits in the phase
`ψ(⟨t, gramK u⟩)`; the complement/flag data sits in `isoConeSum` (through `y = t₀•u+t₁•a+t₂•b`). -/
theorem countHat_factor (Q : QuadraticForm K V) (a b u : V) {R' : Type*} [CommRing R']
    (ψ : AddChar K R') (t : K × K × K) :
    countHat Q a b u ψ t
      = ψ (t.1 * Q u + t.2.1 * QuadraticMap.polar Q u a + t.2.2 * QuadraticMap.polar Q u b)
        * isoConeSum Q ψ (t.1 • u + t.2.1 • a + t.2.2 • b) := by
  rw [countHat_eq_isoSum, Finset.sum_filter]
  -- reindex z = u + w
  rw [← Equiv.sum_comp (Equiv.addLeft u)
    (fun z => if Q (u - z) = 0 then
      ψ (t.1 * Q z + t.2.1 * QuadraticMap.polar Q z a + t.2.2 * QuadraticMap.polar Q z b) else 0)]
  simp only [Equiv.coe_addLeft]
  -- simplify the isotropy guard and the phase under z = u + w
  have hguard : ∀ w : V, (u - (u + w)) = -w := fun w => by abel
  rw [isoConeSum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [hguard w, QuadraticMap.map_neg]
  by_cases hw : Q w = 0
  · rw [if_pos hw, if_pos hw]
    -- ⟨t, gramK (u+w)⟩ = ⟨t, gramK u⟩ + polar w y
    have hQuw : Q (u + w) = QuadraticMap.polar Q u w + Q u + Q w := by
      rw [QuadraticMap.polar]; ring
    have hkey : t.1 * Q (u + w)
          + t.2.1 * QuadraticMap.polar Q (u + w) a + t.2.2 * QuadraticMap.polar Q (u + w) b
        = (t.1 * Q u + t.2.1 * QuadraticMap.polar Q u a + t.2.2 * QuadraticMap.polar Q u b)
          + QuadraticMap.polar Q w (t.1 • u + t.2.1 • a + t.2.2 • b) := by
      rw [hQuw, hw, QuadraticMap.polar_add_left, QuadraticMap.polar_add_left,
        QuadraticMap.polar_add_right, QuadraticMap.polar_add_right,
        QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_right,
        QuadraticMap.polar_comm Q w u, smul_eq_mul, smul_eq_mul, smul_eq_mul]
      ring
    rw [hkey, AddChar.map_add_eq_mul]
  · rw [if_neg hw, if_neg hw, mul_zero]

end ChainDescent.GramStrat
