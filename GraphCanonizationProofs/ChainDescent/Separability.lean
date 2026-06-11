import ChainDescent.Scheme

/-!
# §S — Coherent-configuration separability theory (the S-ring layer)

This file begins the **separability layer** on top of the `AssociationScheme` substrate of
`Scheme.lean` — the destination of the seal program (`chain-descent-module-adjoin-plan.md` §9). The
goal of the layer is to discharge the seal's open crux (`PersistentTwinYieldsBlock` /
`SelfDetectsWhileSymmetric`) *by proof* rather than by the per-family cyclotomic citation, via the
Ponomarenko / Cartan separability theory.

This first increment lands the **parameter substrate** of Ponomarenko–Vasil'ev,
*Cartan coherent configurations* (arXiv:1602.07132): the **valency** `n_i`, the **maximum valency**
`k(X)`, the **indistinguishing number** `c(X)`, and the sparsity predicate `2c(k−1) < n` that heads
their Theorem 3.1 (a general sufficient condition for `b(X) ≤ 2 ∧ s(C) ≤ 2`). These are computed from
the intersection numbers the project already carries, so the whole layer sits on `Scheme.lean` with no
new axioms.

**The on-ramp role.** Theorem 3.1 (`2c(k−1) < n ⟹` one-point extension 1-regular `⟹ b(X) ≤ 2`) is the
*sparse* special case of the general sufficient condition (Ponomarenko arXiv:2006.13592 Thm 4.1) the
full program needs. Its proof is **elementary connectivity counting** (no deep classification), so it is
the lowest-risk first piece — and proving it forces building exactly the `valency` / `indistinguishing
number` / one-point-extension substrate that Thm 4.1 reuses. The empirical probe (`CatalogueSchemeProbe`)
confirmed the inequality is genuine where it holds (all such schemes recover at WL-depth ≤ 2) but narrow
(only the sparse end); the dense amorphic residue violates it and needs Thm 4.1's full strength.

Quality bar: axiom-clean `[propext, Classical.choice, Quot.sound]`, full build green.
-/

namespace ChainDescent

namespace AssociationScheme

variable {n : Nat} (S : AssociationScheme n)

/-! ### §S.1 — Valency `n_i` and the maximum valency `k(X)`

In a homogeneous coherent configuration the **valency** of a basis relation `R_i` is the constant
out-degree `n_i = |αR_i|`, equal to the intersection number `c^{1Ω}_{i,i*}` (Ponomarenko–Vasil'ev §2.1).
Our `AssociationScheme` is single-fiber homogeneous with symmetric relations (`i* = i`), so the valency
is `intersectionNumber i i 0`. The `valency_eq_card` lemma certifies this equals the literal out-degree
count from any vertex. -/

/-- **Valency of `R_i`** — `n_i = c^0_{i,i}` (the out-degree, constant in a homogeneous scheme). -/
def valency (i : Fin (S.rank + 1)) : Nat := S.intersectionNumber i i 0

/-- **Valency is the out-degree.** `n_i` equals the number of `w` with `(v, w) ∈ R_i`, from any `v`
(independent of `v` — this is the homogeneity built into `intersectionNumber_well_defined`). -/
theorem valency_eq_card (i : Fin (S.rank + 1)) (v : Fin n) :
    S.valency i = (Finset.univ.filter (fun w => S.rel i v w = true)).card := by
  have h0 : S.rel 0 v v = true := (S.rel_zero_iff_eq v v).2 rfl
  have hwd := S.intersectionNumber_well_defined i i 0 v v h0
  rw [valency, ← hwd]
  congr 1
  ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  rw [S.rel_symm i u v]; exact h

/-- The diagonal `R_0` has valency `1` (out-degree one — only the vertex itself). -/
theorem valency_zero (v : Fin n) : S.valency 0 = 1 := by
  rw [S.valency_eq_card 0 v]
  have hset : (Finset.univ.filter (fun w => S.rel 0 v w = true)) = {v} := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [S.rel_zero_iff_eq v w]
    exact eq_comm
  rw [hset, Finset.card_singleton]

/-- **The maximum valency `k(X)`** — the largest out-degree over all basis relations. -/
def maxValency : Nat := Finset.univ.sup (fun i : Fin (S.rank + 1) => S.valency i)

/-- Every valency is `≤ k(X)`. -/
theorem valency_le_maxValency (i : Fin (S.rank + 1)) : S.valency i ≤ S.maxValency :=
  Finset.le_sup (Finset.mem_univ i)

/-! ### §S.2 — The indistinguishing number `c(X)`

The **indistinguishing number** of a basis relation `R_r` is `c(r) = Σ_s c^r_{s,s*}` (Ponomarenko–
Vasil'ev §2.4); `c(X) = max_{r ≠ 1Ω} c(r)`. Equation (7) of that paper gives the geometric meaning:
for `(α, β) ∈ R_r`, `c(r)` is the number of vertices `γ` that **fail to distinguish** `α` from `β`
(`r(γ, α) = r(γ, β)`). That counting form (`indistinguishingNumberOf_eq_card`) is the shape the
Theorem-3.1 connectivity argument consumes. -/

/-- **Indistinguishing number of `R_r`** — `c(r) = Σ_s c^r_{s,s*}` (`s* = s`, relations symmetric). -/
def indistinguishingNumberOf (r : Fin (S.rank + 1)) : Nat :=
  Finset.univ.sum (fun s : Fin (S.rank + 1) => S.intersectionNumber s s r)

/-- **The indistinguishing number `c(X)`** — `max_{r ≠ 0} c(r)`. -/
def indistinguishingNumber : Nat :=
  (Finset.univ.filter (fun r : Fin (S.rank + 1) => r ≠ 0)).sup
    (fun r => S.indistinguishingNumberOf r)

/-- `c(r) ≤ c(X)` for every non-diagonal relation `R_r`. -/
theorem indistinguishingNumberOf_le {r : Fin (S.rank + 1)} (hr : r ≠ 0) :
    S.indistinguishingNumberOf r ≤ S.indistinguishingNumber :=
  Finset.le_sup (Finset.mem_filter.2 ⟨Finset.mem_univ r, hr⟩)

/-- **The geometric meaning of `c(r)` (Ponomarenko–Vasil'ev (7)).** For a pair `(α, β) ∈ R_r`, the
indistinguishing number `c(r)` counts the vertices `γ` that relate to `α` and to `β` by the *same*
relation — the ones that cannot tell `α` from `β`. This is the counting form the connectivity argument
for Theorem 3.1 uses. -/
theorem indistinguishingNumberOf_eq_card {r : Fin (S.rank + 1)} {α β : Fin n}
    (hr : S.rel r α β = true) :
    S.indistinguishingNumberOf r
      = (Finset.univ.filter (fun γ => S.relOfPair γ α = S.relOfPair γ β)).card := by
  rw [indistinguishingNumberOf]
  -- Partition `{γ : relOfPair γ α = relOfPair γ β}` by the common value `b = relOfPair γ α`.
  rw [Finset.card_eq_sum_card_fiberwise
        (f := fun γ => S.relOfPair γ α) (t := Finset.univ)
        (fun γ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  -- Each fiber has `intersectionNumber b b r` elements.
  have hwd := S.intersectionNumber_well_defined b b r α β hr
  rw [← hwd]
  congr 1
  ext γ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  -- LHS (well-defined filter): `rel b α γ ∧ rel b γ β`; RHS (fiber): `relOfPair γ α = relOfPair γ β ∧ relOfPair γ α = b`.
  constructor
  · rintro ⟨hαγ, hγβ⟩
    -- `rel b α γ ∧ rel b γ β` ⟹ `relOfPair γ α = b = relOfPair γ β`.
    have hβ : S.relOfPair γ β = b := (S.relOfPair_unique hγβ).symm
    have hα : S.relOfPair γ α = b := by
      have hγα : S.rel b γ α = true := by rw [S.rel_symm b γ α]; exact hαγ
      exact (S.relOfPair_unique hγα).symm
    exact ⟨hα.trans hβ.symm, hα⟩
  · rintro ⟨heq, hb⟩
    -- `relOfPair γ α = relOfPair γ β` and `= b` ⟹ `rel b α γ ∧ rel b γ β`.
    have hbα : S.rel b γ α = true := by have h := S.rel_relOfPair γ α; rw [hb] at h; exact h
    have hbβ : S.rel b γ β = true := by
      have h := S.rel_relOfPair γ β; rw [← heq, hb] at h; exact h
    exact ⟨by rw [S.rel_symm b α γ]; exact hbα, hbβ⟩

/-! ### §S.3 — The Theorem-3.1 sparsity hypothesis `2c(k−1) < n`

Ponomarenko–Vasil'ev Theorem 3.1: a homogeneous coherent configuration whose indistinguishing number
`c` and maximum valency `k` satisfy `2c(k−1) < n` has every one-point extension 1-regular, hence
`b(X) ≤ 2`; combined with their Theorem 2.5 (`m`-separable ⟺ 1-regular `(m−1)`-point extension) this
gives `s(C) ≤ 2`. This predicate names the hypothesis; the theorem itself is the next increment. -/

/-- **The Ponomarenko–Vasil'ev Theorem 3.1 sparsity hypothesis** `2c(k−1) < n`. When it holds, the
scheme is `2`-separable with base number `≤ 2` (recovery depth `≤ 4`) — the sparse end of the
separability spectrum, provable by elementary connectivity counting (the next increment). -/
def SparseSeparable : Prop := 2 * S.indistinguishingNumber * (S.maxValency - 1) < n

/-! ### §S.4 — The maximum-valency graph `smax`, the local-rigidity relation `sα`, and `pᵤ(δ)`

The combinatorial substrate of Ponomarenko–Vasil'ev §3 (increment 2a). `Smax` is the set of basis
relations of maximum valency `k`; `smax = ⋃ Smax` is the corresponding (symmetric) graph on the points.
For a base point `α`, `sα` is the local-rigidity relation on `αsmax`: pairs `(β,γ)` whose colored
triangle `{α,β,γ}` is forced (`cᵗ_{rs}=1`). The pair-count `pᵤ(δ)` counts the `(β,γ) ∈ αu×αu` that
`δ` fails to distinguish. The whole §3 argument shows: under `2c(k−1)<n` both graphs are connected,
which forces a two-point base, i.e. `b(X) ≤ 2`. -/

/-- **`Smax` — the basis relations of maximum valency.** -/
def Smax : Finset (Fin (S.rank + 1)) := Finset.univ.filter (fun s => S.valency s = S.maxValency)

/-- Membership in `Smax`: a relation of maximum valency `k`. -/
def InSmax (s : Fin (S.rank + 1)) : Prop := S.valency s = S.maxValency

theorem mem_Smax_iff {s : Fin (S.rank + 1)} : s ∈ S.Smax ↔ S.InSmax s := by
  simp only [Smax, Finset.mem_filter, Finset.mem_univ, true_and, InSmax]

/-- A maximum-valency relation has out-degree exactly `k = maxValency` from any vertex. -/
theorem card_relNeighbors_of_inSmax {s : Fin (S.rank + 1)} (hs : S.InSmax s) (v : Fin n) :
    (Finset.univ.filter (fun w => S.rel s v w = true)).card = S.maxValency := by
  rw [← S.valency_eq_card s v]; exact hs

/-- **The `smax` graph adjacency** — `(a, b) ∈ smax` iff some maximum-valency relation joins them. -/
def smaxAdj (a b : Fin n) : Prop := ∃ s, S.InSmax s ∧ S.rel s a b = true

/-- `smax` is symmetric (each relation is symmetric, and valency is fixed). -/
theorem smaxAdj_symm {a b : Fin n} (h : S.smaxAdj a b) : S.smaxAdj b a := by
  obtain ⟨s, hs, hrel⟩ := h
  exact ⟨s, hs, by rw [S.rel_symm s b a]; exact hrel⟩

/-- **Connectedness of the `smax` graph** — every two points are joined by an `smax`-path. -/
def SmaxConnected : Prop := ∀ a b : Fin n, Relation.ReflTransGen S.smaxAdj a b

/-- **The local-rigidity relation `sα`** — for `β, γ ∈ αsmax`, the colored triangle `{α,β,γ}` is forced
by its side colors: `c^{r(α,γ)}_{r(α,β),r(β,γ)} = 1`. (Ponomarenko–Vasil'ev §3.2.) -/
def saAdj (α β γ : Fin n) : Prop :=
  S.smaxAdj α β ∧ S.smaxAdj α γ ∧
    S.intersectionNumber (S.relOfPair α β) (S.relOfPair β γ) (S.relOfPair α γ) = 1

/-- **Connectedness of `sα` on `αsmax`** — every two `smax`-neighbours of `α` are joined by an
`sα`-path. (Ponomarenko–Vasil'ev §3.2; the form used by Lemma 3.3.) -/
def SaConnected (α : Fin n) : Prop :=
  ∀ β γ : Fin n, S.smaxAdj α β → S.smaxAdj α γ → Relation.ReflTransGen (S.saAdj α) β γ

/-- **The pair-count `pᵤ(δ)`** — the number of ordered pairs `(β, γ) ∈ αu × αu` with `β ≠ γ` that the
point `δ` fails to distinguish (`r(β, δ) = r(γ, δ)`). The workhorse of the §3 counting estimates. -/
noncomputable def pu (α : Fin n) (u : Fin (S.rank + 1)) (δ : Fin n) : Nat :=
  (Finset.univ.filter (fun bg : Fin n × Fin n =>
      S.rel u α bg.1 = true ∧ S.rel u α bg.2 = true ∧ bg.1 ≠ bg.2 ∧
      S.relOfPair bg.1 δ = S.relOfPair bg.2 δ)).card

/-! ### §S.5 — The homogeneous summation identity

`Σ_w c^v_{uw} = n_u`: fixing the source relation `u` and target relation `v`, summing the intersection
number over the middle relation `w` recovers the valency `n_u`. (Used implicitly throughout §3, e.g. in
the penultimate equality of the Lemma 3.5(1) bound.) Each `β ∈ αu` lands in exactly one fiber by its
relation `w = r(β, δ)` to a fixed `δ ∈ αv`. -/
theorem sum_intersectionNumber_eq_valency (u v : Fin (S.rank + 1)) (α δ : Fin n)
    (hv : S.rel v α δ = true) :
    (Finset.univ.sum (fun w : Fin (S.rank + 1) => S.intersectionNumber u w v)) = S.valency u := by
  rw [S.valency_eq_card u α,
    Finset.card_eq_sum_card_fiberwise (f := fun β => S.relOfPair β δ) (t := Finset.univ)
      (fun β _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [← S.intersectionNumber_well_defined u w v α δ hv]
  congr 1
  ext β
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hu, hw⟩
    exact ⟨hu, (S.relOfPair_unique hw).symm⟩
  · rintro ⟨hu, hw⟩
    refine ⟨hu, ?_⟩
    have h := S.rel_relOfPair β δ; rw [hw] at h; exact h

/-! ### §S.6 — The global estimate (19): `Σ_{δ∈Δ} pᵤ(δ) ≤ k(k−1)·c`

The workhorse upper bound (Ponomarenko–Vasil'ev (19), increment 2b). For a maximum-valency relation `u`
and any vertex set `Δ`, the total `Σ_{δ∈Δ} pᵤ(δ)` is bounded by `k(k−1)·c`. The proof swaps the order of
summation — `Σ_δ Σ_{(β,γ)} [δ fails to split β,γ] = Σ_{(β,γ)} Σ_δ [⋯] = Σ_{(β,γ)} |{δ∈Δ : ⋯}|` — bounds
each inner term by the indistinguishing number `c(r(β,γ)) ≤ c(X)` (increment 1's
`indistinguishingNumberOf_eq_card`), and counts the `k(k−1)` ordered distinct pairs of `αu` via
`Finset.offDiag`. -/

/-- Reformulation of `pᵤ(δ)` over the off-diagonal of the neighbour set `αu`. -/
theorem pu_eq (α : Fin n) (u : Fin (S.rank + 1)) (δ : Fin n) :
    S.pu α u δ
      = ((Finset.univ.filter (fun w => S.rel u α w = true)).offDiag.filter
          (fun bg => S.relOfPair bg.1 δ = S.relOfPair bg.2 δ)).card := by
  unfold pu
  congr 1
  ext bg
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_offDiag]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨h1, h2, h3⟩, h4⟩
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩; exact ⟨h1, h2, h3, h4⟩

private theorem nat_kk_sub_self (k : ℕ) : k * k - k = k * (k - 1) := by
  cases k with
  | zero => rfl
  | succ m => simp only [Nat.succ_sub_one, Nat.mul_succ, Nat.add_sub_cancel]

/-- **The global estimate (19)** — `Σ_{δ∈Δ} pᵤ(δ) ≤ k(k−1)·c` for a maximum-valency relation `u` and any
vertex set `Δ`. The upper half of Ponomarenko–Vasil'ev (19); the workhorse of the Lemma 3.6 contradiction. -/
theorem sum_pu_le (α : Fin n) {u : Fin (S.rank + 1)} (hu : S.InSmax u) (Δ : Finset (Fin n)) :
    (Δ.sum (fun δ => S.pu α u δ))
      ≤ S.maxValency * (S.maxValency - 1) * S.indistinguishingNumber := by
  set A := Finset.univ.filter (fun w => S.rel u α w = true) with hA
  have hAcard : A.card = S.maxValency := S.card_relNeighbors_of_inSmax hu α
  -- Swap the order of summation: `Σ_δ pᵤ(δ) = Σ_{(β,γ)∈A.offDiag} |{δ∈Δ : δ fails to split β,γ}|`.
  have hstep : (Δ.sum (fun δ => S.pu α u δ))
      = A.offDiag.sum (fun bg => (Δ.filter
          (fun δ => S.relOfPair bg.1 δ = S.relOfPair bg.2 δ)).card) := by
    simp_rw [S.pu_eq α u, Finset.card_filter]
    rw [Finset.sum_comm]
  -- Each inner term is bounded by `c(X)`.
  have hbound : ∀ bg ∈ A.offDiag,
      (Δ.filter (fun δ => S.relOfPair bg.1 δ = S.relOfPair bg.2 δ)).card
        ≤ S.indistinguishingNumber := by
    intro bg hbg
    rw [Finset.mem_offDiag] at hbg
    obtain ⟨_, _, hne⟩ := hbg
    calc (Δ.filter (fun δ => S.relOfPair bg.1 δ = S.relOfPair bg.2 δ)).card
        ≤ (Finset.univ.filter (fun δ => S.relOfPair bg.1 δ = S.relOfPair bg.2 δ)).card :=
          Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ Δ))
      _ = (Finset.univ.filter (fun δ => S.relOfPair δ bg.1 = S.relOfPair δ bg.2)).card := by
          congr 1; ext δ
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [S.relOfPair_symm bg.1 δ, S.relOfPair_symm bg.2 δ]
      _ = S.indistinguishingNumberOf (S.relOfPair bg.1 bg.2) :=
          (S.indistinguishingNumberOf_eq_card (S.rel_relOfPair bg.1 bg.2)).symm
      _ ≤ S.indistinguishingNumber :=
          S.indistinguishingNumberOf_le (by rw [Ne, S.relOfPair_eq_zero_iff]; exact hne)
  -- Assemble: `Σ ≤ |A.offDiag|·c = (k²−k)·c = k(k−1)·c`.
  rw [hstep]
  calc A.offDiag.sum (fun bg => (Δ.filter
          (fun δ => S.relOfPair bg.1 δ = S.relOfPair bg.2 δ)).card)
      ≤ A.offDiag.sum (fun _ => S.indistinguishingNumber) := Finset.sum_le_sum hbound
    _ = A.offDiag.card * S.indistinguishingNumber := by rw [Finset.sum_const, smul_eq_mul]
    _ = (S.maxValency * S.maxValency - S.maxValency) * S.indistinguishingNumber := by
        rw [Finset.offDiag_card, hAcard]
    _ = S.maxValency * (S.maxValency - 1) * S.indistinguishingNumber := by
        rw [nat_kk_sub_self]

/-! ### §S.7 — Identity (20): `pᵤ(δ) = Σ_w cᵛ_{uw}(cᵛ_{uw}−1)`

Ponomarenko–Vasil'ev (20) (increment 2c-i). Grouping the `(β,γ) ∈ αu×αu` counted by `pᵤ(δ)` by their
common relation `w = r(β,δ) = r(γ,δ)` to the test point `δ` (with `v = r(α,δ)`): each `w` contributes
the `cᵛ_{uw}(cᵛ_{uw}−1)` ordered distinct pairs from the `cᵛ_{uw}`-element set `{β ∈ αu : r(β,δ)=w}`.
This is the bridge from the geometric pair-count to the intersection numbers, used by both halves of
Lemma 3.5. -/
theorem pu_eq_sum (α : Fin n) (u : Fin (S.rank + 1)) (δ : Fin n) :
    S.pu α u δ
      = Finset.univ.sum (fun w : Fin (S.rank + 1) =>
          S.intersectionNumber u w (S.relOfPair α δ)
            * (S.intersectionNumber u w (S.relOfPair α δ) - 1)) := by
  unfold pu
  rw [Finset.card_eq_sum_card_fiberwise (f := fun bg : Fin n × Fin n => S.relOfPair bg.1 δ)
        (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  -- The `w`-fiber is the off-diagonal of `{β ∈ αu : r(β,δ) = w}`.
  have hfib : ((Finset.univ.filter (fun bg : Fin n × Fin n =>
          S.rel u α bg.1 = true ∧ S.rel u α bg.2 = true ∧ bg.1 ≠ bg.2 ∧
          S.relOfPair bg.1 δ = S.relOfPair bg.2 δ)).filter
            (fun bg => S.relOfPair bg.1 δ = w))
        = (Finset.univ.filter (fun β => S.rel u α β = true ∧ S.relOfPair β δ = w)).offDiag := by
    ext bg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_offDiag]
    constructor
    · rintro ⟨⟨h1, h2, hne, heq⟩, hw⟩
      exact ⟨⟨h1, hw⟩, ⟨h2, heq ▸ hw⟩, hne⟩
    · rintro ⟨⟨h1, hw1⟩, ⟨h2, hw2⟩, hne⟩
      exact ⟨⟨h1, h2, hne, hw1.trans hw2.symm⟩, hw1⟩
  rw [hfib, Finset.offDiag_card]
  -- The fiber's vertex set has `cᵛ_{uw}` elements.
  have hcard : (Finset.univ.filter (fun β => S.rel u α β = true ∧ S.relOfPair β δ = w)).card
      = S.intersectionNumber u w (S.relOfPair α δ) := by
    rw [← S.intersectionNumber_well_defined u w (S.relOfPair α δ) α δ (S.rel_relOfPair α δ)]
    congr 1
    ext β
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, hw⟩
      refine ⟨h1, ?_⟩
      have h := S.rel_relOfPair β δ; rw [hw] at h; exact h
    · rintro ⟨h1, hw⟩
      exact ⟨h1, (S.relOfPair_unique hw).symm⟩
  rw [hcard, nat_kk_sub_self]

/-! ### §S.8 — The homogeneous triangle identity `n_k·cᵏ_{ij} = n_i·cⁱ_{kj}`

Increment 2c-ii. Double-count the colored triangles `x–y–z` (colors `i` on `x→y`, `j` on `y→z`, `k` on
`x→z`) through a fixed apex `x`: counting by the `z`-leg gives `n_k·cᵏ_{ij}`, by the `y`-leg gives
`n_i·cⁱ_{kj}`. Fixing the apex avoids the global `n`-factor. (Ponomarenko–Vasil'ev eq. (4), symmetric
case.) This alone discharges the `nᵤ>nᵥ` subcase of Lemma 3.5(1): if `cᵏ_{ij} ≥ 1` then this identity
forces `cⱽ_{uw}` up whenever `nᵤ > nᵥ`. -/
theorem valency_mul_intersectionNumber (i j k : Fin (S.rank + 1)) (x : Fin n) :
    S.valency k * S.intersectionNumber i j k = S.valency i * S.intersectionNumber k j i := by
  classical
  -- `D` = the (y, z) legs of triangles `x–y–z` with the prescribed colors.
  -- Count `D` by the `z`-coordinate ⟹ `n_k · cᵏ_{ij}`.
  have hA : (Finset.univ.filter (fun p : Fin n × Fin n =>
        S.rel i x p.1 = true ∧ S.rel j p.1 p.2 = true ∧ S.rel k x p.2 = true)).card
      = S.valency k * S.intersectionNumber i j k := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun p : Fin n × Fin n => p.2)
          (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    have hfz : ∀ z : Fin n,
        ((Finset.univ.filter (fun p : Fin n × Fin n =>
            S.rel i x p.1 = true ∧ S.rel j p.1 p.2 = true ∧ S.rel k x p.2 = true)).filter
              (fun p => p.2 = z)).card
        = if S.rel k x z = true then S.intersectionNumber i j k else 0 := by
      intro z
      by_cases hk : S.rel k x z = true
      · rw [if_pos hk, ← S.intersectionNumber_well_defined i j k x z hk]
        apply Finset.card_bij (fun p _ => p.1)
        · intro p hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
          obtain ⟨⟨hi1, hj1, _⟩, hz⟩ := hp
          exact ⟨hi1, hz ▸ hj1⟩
        · intro p hp q hq hpq
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
          exact Prod.ext hpq (hp.2.trans hq.2.symm)
        · intro y hy
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
          refine ⟨(y, z), ?_, rfl⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨⟨hy.1, hy.2, hk⟩, ?_⟩
          trivial
      · rw [if_neg hk, Finset.card_eq_zero]
        apply Finset.eq_empty_of_forall_notMem
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
        obtain ⟨⟨_, _, hk1⟩, hz⟩ := hp
        exact hk (hz ▸ hk1)
    rw [Finset.sum_congr rfl (fun z _ => hfz z), ← Finset.sum_filter, Finset.sum_const,
      smul_eq_mul, ← S.valency_eq_card k x]
  -- Count `D` by the `y`-coordinate ⟹ `n_i · cⁱ_{kj}`.
  have hB : (Finset.univ.filter (fun p : Fin n × Fin n =>
        S.rel i x p.1 = true ∧ S.rel j p.1 p.2 = true ∧ S.rel k x p.2 = true)).card
      = S.valency i * S.intersectionNumber k j i := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun p : Fin n × Fin n => p.1)
          (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    have hfy : ∀ y : Fin n,
        ((Finset.univ.filter (fun p : Fin n × Fin n =>
            S.rel i x p.1 = true ∧ S.rel j p.1 p.2 = true ∧ S.rel k x p.2 = true)).filter
              (fun p => p.1 = y)).card
        = if S.rel i x y = true then S.intersectionNumber k j i else 0 := by
      intro y
      by_cases hi' : S.rel i x y = true
      · rw [if_pos hi', ← S.intersectionNumber_well_defined k j i x y hi']
        apply Finset.card_bij (fun p _ => p.2)
        · intro p hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
          obtain ⟨⟨_, hj1, hk1⟩, hy⟩ := hp
          refine ⟨hk1, ?_⟩
          rw [S.rel_symm j p.2 y]; exact hy ▸ hj1
        · intro p hp q hq hpq
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
          exact Prod.ext (hp.2.trans hq.2.symm) hpq
        · intro z hz
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
          refine ⟨(y, z), ?_, rfl⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨⟨hi', ?_, hz.1⟩, ?_⟩
          · rw [S.rel_symm j y z]; exact hz.2
          · trivial
      · rw [if_neg hi', Finset.card_eq_zero]
        apply Finset.eq_empty_of_forall_notMem
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
        obtain ⟨⟨hi1, _, _⟩, hy⟩ := hp
        exact hi' (hy ▸ hi1)
    rw [Finset.sum_congr rfl (fun y _ => hfy y), ← Finset.sum_filter, Finset.sum_const,
      smul_eq_mul, ← S.valency_eq_card i x]
  exact hA.symm.trans hB

/-! ### §S.9 — Lemma 3.5(1), the `nᵤ > nᵥ` half: `pᵤ(δ) ≥ nᵤ`

Increment 2c-iv (the component-free half). When the test relation `v = r(α,δ)` has strictly smaller
valency than `u`, every `cᵛ_{uw}` that occurs is `≥ 2` (a `cᵛ_{uw}=1` would force, via the triangle
identity, `nᵥ = nᵤ·cᵛ′ ≥ nᵤ > nᵥ`, or `nᵥ = 0`, both impossible). Hence each term
`cᵛ_{uw}(cᵛ_{uw}−1) ≥ cᵛ_{uw}` and summing (identity (20) + the valency identity) gives `pᵤ(δ) ≥ nᵤ`.
This is the half of Lemma 3.5(1) that needs no `sα`-component analysis; it powers Lemma 3.6's
*smax*-connectedness directly. -/
theorem valency_le_pu_of_valency_lt (α : Fin n) (u : Fin (S.rank + 1)) (δ : Fin n)
    (hlt : S.valency (S.relOfPair α δ) < S.valency u) :
    S.valency u ≤ S.pu α u δ := by
  rw [S.pu_eq_sum α u δ]
  set v := S.relOfPair α δ with hv
  have hrv : S.rel v α δ = true := by rw [hv]; exact S.rel_relOfPair α δ
  rw [← S.sum_intersectionNumber_eq_valency u v α δ hrv]
  apply Finset.sum_le_sum
  intro w _
  -- `cᵛ_{uw} ≠ 1`: a `1` would contradict `nᵥ < nᵤ` via the triangle identity.
  have hne1 : S.intersectionNumber u w v ≠ 1 := by
    intro h1
    have hid : S.valency v * S.intersectionNumber u w v
        = S.valency u * S.intersectionNumber v w u := S.valency_mul_intersectionNumber u w v α
    rw [h1, Nat.mul_one] at hid
    have hvpos : 1 ≤ S.valency v := by
      rw [S.valency_eq_card v α]
      apply Finset.card_pos.2
      exact ⟨δ, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hrv⟩
    rcases Nat.eq_zero_or_pos (S.intersectionNumber v w u) with hm | hm
    · rw [hm, Nat.mul_zero] at hid; omega
    · have hle : S.valency u ≤ S.valency v :=
        calc S.valency u = S.valency u * 1 := (Nat.mul_one _).symm
          _ ≤ S.valency u * S.intersectionNumber v w u := Nat.mul_le_mul (le_refl _) hm
          _ = S.valency v := hid.symm
      omega
  -- so `cᵛ_{uw} = 0` or `≥ 2`, giving `cᵛ_{uw} ≤ cᵛ_{uw}(cᵛ_{uw}−1)`.
  rcases Nat.eq_zero_or_pos (S.intersectionNumber u w v) with hc0 | hc0
  · simp [hc0]
  · calc S.intersectionNumber u w v = S.intersectionNumber u w v * 1 := (Nat.mul_one _).symm
      _ ≤ S.intersectionNumber u w v * (S.intersectionNumber u w v - 1) :=
          Nat.mul_le_mul (le_refl _) (by omega)

/-! ### §S.10 — Connectivity infrastructure + Lemma 3.6 (the *smax* half)

Increment 2c-iii (the reachability foundation + the easier half of Lemma 3.6). For a symmetric relation
`r` on the points, a disconnected graph has a *closed* (adjacency-stable) vertex set of size `≤ n/2`.
Applied to the `smax` graph (with the `nᵤ>nᵥ` bound `valency_le_pu_of_valency_lt` and the (19) estimate
`sum_pu_le`), this proves `smax` is connected under `2c(k−1)<n` — the half of Lemma 3.6 that needs no
`sα`-component analysis. The same infrastructure is reused later for the `sα` graph. -/

/-- **Disconnected ⟹ a small closed set.** If a symmetric relation `r` is not reflexive-transitively
connected, there is a nonempty vertex set closed under `r`-adjacency of size `≤ n/2`. -/
theorem exists_small_closed_of_not_connected (r : Fin n → Fin n → Prop)
    (hsymm : ∀ a b, r a b → r b a)
    (hcon : ¬ ∀ a b : Fin n, Relation.ReflTransGen r a b) :
    ∃ C : Finset (Fin n), (∀ a ∈ C, ∀ b, r a b → b ∈ C) ∧ C.Nonempty ∧ 2 * C.card ≤ n := by
  classical
  push Not at hcon
  obtain ⟨x, y, hxy⟩ := hcon
  set R : Finset (Fin n) := Finset.univ.filter (fun z => Relation.ReflTransGen r x z) with hR
  have hxR : x ∈ R := by
    rw [hR]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact Relation.ReflTransGen.refl
  have hyR : y ∉ R := by
    rw [hR]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hxy
  have hRclosed : ∀ a ∈ R, ∀ b, r a b → b ∈ R := by
    intro a ha b hab
    rw [hR, Finset.mem_filter] at ha ⊢
    exact ⟨Finset.mem_univ _, ha.2.tail hab⟩
  have hRcclosed : ∀ a ∈ Finset.univ \ R, ∀ b, r a b → b ∈ Finset.univ \ R := by
    intro a ha b hab
    rw [Finset.mem_sdiff] at ha ⊢
    refine ⟨Finset.mem_univ _, fun hbR => ha.2 ?_⟩
    rw [hR, Finset.mem_filter] at hbR ⊢
    exact ⟨Finset.mem_univ _, hbR.2.tail (hsymm a b hab)⟩
  have hRle : R.card ≤ n := by
    have h := Finset.card_le_card (Finset.subset_univ R)
    rwa [Finset.card_univ, Fintype.card_fin] at h
  have hcompl : (Finset.univ \ R).card = n - R.card := by
    rw [Finset.card_univ_diff, Fintype.card_fin]
  by_cases hsz : 2 * R.card ≤ n
  · exact ⟨R, hRclosed, ⟨x, hxR⟩, hsz⟩
  · refine ⟨Finset.univ \ R, hRcclosed, ⟨y, ?_⟩, ?_⟩
    · rw [Finset.mem_sdiff]; exact ⟨Finset.mem_univ _, hyR⟩
    · rw [hcompl]; omega

/-- **A maximum-valency relation exists** (`Smax` is nonempty): the `Finset.sup` defining `k(X)` is
attained. -/
theorem exists_inSmax : ∃ u : Fin (S.rank + 1), S.InSmax u := by
  obtain ⟨u, _, hu⟩ := Finset.exists_mem_eq_sup Finset.univ ⟨0, Finset.mem_univ 0⟩ S.valency
  exact ⟨u, hu.symm⟩

/-- **Lemma 3.6, the *smax* half.** Under `2c(k−1) < n` (and `k ≥ 2`) the maximum-valency graph `smax`
is connected. If it were disconnected, a small closed set `C` (`2|C| ≤ n`) would have every outside point
`δ` satisfy `n_{r(α,δ)} < k` (else `δ` is `smax`-adjacent to `α ∈ C`, so `δ ∈ C`), giving `pᵤ(δ) ≥ k`
(`valency_le_pu_of_valency_lt`); summing over the `≥ n/2` outside points against the (19) estimate
(`sum_pu_le`) forces `n ≤ 2c(k−1)`, contradicting the hypothesis. -/
theorem smaxConnected_of_sparseSeparable (hsep : S.SparseSeparable) (hk : 2 ≤ S.maxValency) :
    S.SmaxConnected := by
  by_contra hcon
  obtain ⟨C, hClosed, ⟨α, hα⟩, hCsize⟩ :=
    exists_small_closed_of_not_connected S.smaxAdj (fun a b h => S.smaxAdj_symm h) hcon
  obtain ⟨u, hu⟩ := S.exists_inSmax
  have huk : S.valency u = S.maxValency := hu
  -- Each outside point gives `pᵤ(δ) ≥ k`.
  have hbound : ∀ δ ∈ Finset.univ \ C, S.valency u ≤ S.pu α u δ := by
    intro δ hδ
    rw [Finset.mem_sdiff] at hδ
    apply S.valency_le_pu_of_valency_lt
    rw [huk]
    have hnotmax : ¬ S.InSmax (S.relOfPair α δ) := fun hin =>
      hδ.2 (hClosed α hα δ ⟨S.relOfPair α δ, hin, S.rel_relOfPair α δ⟩)
    have hnotmax' : ¬ (S.valency (S.relOfPair α δ) = S.maxValency) := hnotmax
    have hle := S.valency_le_maxValency (S.relOfPair α δ)
    omega
  have hlow : (Finset.univ \ C).card * S.valency u
      ≤ (Finset.univ \ C).sum (fun δ => S.pu α u δ) := by
    have h := Finset.card_nsmul_le_sum (Finset.univ \ C) (fun δ => S.pu α u δ) (S.valency u) hbound
    rwa [smul_eq_mul] at h
  have hhigh := S.sum_pu_le α hu (Finset.univ \ C)
  rw [huk] at hlow
  have hcomb : (Finset.univ \ C).card * S.maxValency
      ≤ S.maxValency * (S.maxValency - 1) * S.indistinguishingNumber := le_trans hlow hhigh
  have hCle : C.card ≤ n := by
    have h := Finset.card_le_card (Finset.subset_univ C)
    rwa [Finset.card_univ, Fintype.card_fin] at h
  have hcompl : (Finset.univ \ C).card = n - C.card := by
    rw [Finset.card_univ_diff, Fintype.card_fin]
  set k := S.maxValency with hkdef
  set c := S.indistinguishingNumber with hcdef
  set m := (Finset.univ \ C).card with hmdef
  have hsep' : 2 * c * (k - 1) < n := hsep
  have h2m : n ≤ 2 * m := by rw [hcompl]; omega
  have key : n * k ≤ 2 * (k * (k - 1) * c) :=
    calc n * k ≤ (2 * m) * k := mul_le_mul_left h2m k
      _ = 2 * (m * k) := by ring
      _ ≤ 2 * (k * (k - 1) * c) := mul_le_mul_right hcomb 2
  have key2 : k * n ≤ k * (2 * (k - 1) * c) :=
    calc k * n = n * k := Nat.mul_comm k n
      _ ≤ 2 * (k * (k - 1) * c) := key
      _ = k * (2 * (k - 1) * c) := by ring
  have hn : n ≤ 2 * (k - 1) * c := Nat.le_of_mul_le_mul_left key2 (by omega)
  have heq : 2 * (k - 1) * c = 2 * c * (k - 1) := by ring
  omega

end AssociationScheme

end ChainDescent
