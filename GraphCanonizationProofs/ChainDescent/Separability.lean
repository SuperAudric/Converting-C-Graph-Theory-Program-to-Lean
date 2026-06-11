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

end AssociationScheme

end ChainDescent
