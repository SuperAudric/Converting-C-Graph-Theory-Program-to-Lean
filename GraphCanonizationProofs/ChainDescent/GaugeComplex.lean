import ChainDescent.WLGeneric

/-!
# W2 localization spine — Tier A, piece 1: the split-vs-count base lemma

Planning doc: `docs/chain-descent-w2-solvability-route.md` §2 (the gauge complex) and §5 (Tier A).

This is the base lemma the W2 solvability route rests on — the object the completeness
(dual-of-the-seal) argument localizes onto. It is the current-API realization of the
open Lean lemma stated in `docs/Archive/ChainDescent/chain-descent-matroid.md:146-151`:

> at every warm-refine round, a vertex `v` breaks from its cell `C` iff the count vector
> `(|N(v) ∩ Dᵢ|)ᵢ` over the sub-cells `Dᵢ` of some neighbour cell differs from at least one
> other vertex in `C` — a multiset-cardinality reformulation of `refineStep_iff`.

In `WLGeneric`'s vocabulary the "sub-cells of a neighbour cell" are the
`(neighbour-colour, adjacency-value, P-relation)` classes `t : Nat × Nat × POE`, and the
"count vector" is `fun t => Multiset.count t (signature adj P χ v)`. So the lemma is:
`refineStep` separates two co-cellular vertices iff some class-count differs
(`refineStep_ne_iff_exists_count_ne`), plus the gloss that each class-count *is* a literal
neighbour cardinality `|{u ≠ v : class of u = t}|` (`count_signature_eq_card`).

Nothing here assumes anything about the *group* structure of the gauge — that is Tier B
(`forceSolvable`). This piece is the non-circular skeleton: it says *what warm refinement
does at each step*, and is exactly the "1 of k, unless cancellation" mechanism of
`chain-descent-matroid.md:141-144` made precise (cancellation = two class-counts that both
change but leave the multiset fixed — impossible here, since the multiset IS the count
vector, so a real split is exactly a real count difference).
-/

namespace ChainDescent
namespace GaugeComplex

-- NB: do NOT `open WLGeneric` — the enclosing `ChainDescent` namespace also exposes the
-- top-level `signature`/`refineStep` (over `AdjMatrix`), which would shadow the generic
-- `WLGeneric.*` versions. Qualify explicitly.

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The split-vs-count base lemma (W2 Tier A, piece 1).** Two vertices `v, w` in the same
cell (`χ v = χ w`) are *separated* by one round of 1-WL refinement iff their neighbour
class-count vectors differ in *some* class `t = (colour, adj-value, P-relation)`.

This is `refineStep_iff` (equal refined colour ⟺ same old colour ∧ same signature) composed
with multiset extensionality (`Multiset.ext`: two multisets agree iff every count agrees).
It is the precise, current-API form of `chain-descent-matroid.md:146-151`, and the base case
of the gauge-complex localization: a mixed cell splits under warm refinement exactly where a
neighbour-class count separates its vertices. -/
theorem refineStep_ne_iff_exists_count_ne
    (adj : WLGeneric.GAdj V) (P : WLGeneric.GPOE V) (χ : V → Nat) {v w : V} (hcol : χ v = χ w) :
    WLGeneric.refineStep adj P χ v ≠ WLGeneric.refineStep adj P χ w ↔
      ∃ t : Nat × Nat × POE,
        Multiset.count t (WLGeneric.signature adj P χ v)
          ≠ Multiset.count t (WLGeneric.signature adj P χ w) := by
  have hstep : WLGeneric.refineStep adj P χ v = WLGeneric.refineStep adj P χ w ↔
      WLGeneric.signature adj P χ v = WLGeneric.signature adj P χ w := by
    rw [WLGeneric.refineStep_iff, and_iff_right hcol]
  rw [ne_eq, hstep, Multiset.ext, not_forall]

/-- The **`t`-neighbour class** of `v`: the vertices `u ≠ v` whose own class
`(χ u, adj v u, P v u)` is exactly `t = (colour, adj-value, P-relation)`. This is the
literal "sub-cell `Dᵢ` of a neighbour cell" the base lemma's count vector ranges over —
the fully-refined local fibre over `v` in class `t`. -/
def nbhdClass (adj : WLGeneric.GAdj V) (P : WLGeneric.GPOE V) (χ : V → Nat) (v : V)
    (t : Nat × Nat × POE) : Finset V :=
  Finset.univ.filter (fun u => u ≠ v ∧ t = (χ u, adj v u, P v u))

/-- **The gloss — a class-count is a literal neighbour cardinality.** For any class
`t = (colour, adj-value, P-relation)`, the multiset count `Multiset.count t (signature …)`
equals the size of the neighbour class `nbhdClass … v t = {u ≠ v : (χ u, adj v u, P v u) = t}`.
This is what makes "count vector over neighbour sub-cells" in the base lemma literal:
`Multiset.count t (signature adj P χ v) = |nbhdClass adj P χ v t|`. -/
theorem count_signature_eq_card
    (adj : WLGeneric.GAdj V) (P : WLGeneric.GPOE V) (χ : V → Nat) (v : V) (t : Nat × Nat × POE) :
    Multiset.count t (WLGeneric.signature adj P χ v) = (nbhdClass adj P χ v t).card := by
  unfold WLGeneric.signature nbhdClass
  rw [Multiset.count_map]
  simp only [Finset.card, Finset.filter_val, Multiset.filter_filter, and_comm]

/-! ## Flatness — equitability ⟹ a local exchange exists (W2 Tier A, piece 2)

The *positive* twin of the base lemma. Where piece 1 says a real split ⟺ a real count
difference, flatness says: when two co-cellular vertices are *not* split (which equitability
forces for every co-cellular pair), their neighbour classes are equinumerous in every class,
so a **local exchange** — a bijection between `v`'s and `w`'s class-`t` neighbours — *exists*.

The exchange is **non-canonical** (`Finset.equivOfCardEq` is noncomputable — it picks one of
the many bijections via choice). That non-canonicity is exactly the **gauge freedom**: locally
there is nothing to prefer one exchange over another. "Flat" = every local exchange exists
(local triviality); whether a globally-consistent choice exists is the **holonomy** (Tier A
piece 3), and this lemma says nothing about it. This is the precise "1 of k, *unless
cancellation*" mechanism of `chain-descent-matroid.md:141-144` on its no-split side: co-cellular
and unsplit ⟺ the fibres match, class by class. -/

/-- **The equal-count twin of the base lemma.** Two vertices get the same refined colour iff
they are co-cellular AND their neighbour class-count vectors agree in every class. (Piece 1 is
the contrapositive-in-the-second-conjunct of this.) -/
theorem refineStep_eq_iff_forall_card_eq
    (adj : WLGeneric.GAdj V) (P : WLGeneric.GPOE V) (χ : V → Nat) (v w : V) :
    WLGeneric.refineStep adj P χ v = WLGeneric.refineStep adj P χ w ↔
      χ v = χ w ∧ ∀ t : Nat × Nat × POE,
        (nbhdClass adj P χ v t).card = (nbhdClass adj P χ w t).card := by
  rw [WLGeneric.refineStep_iff]
  refine and_congr_right (fun _ => ?_)
  rw [Multiset.ext]
  refine forall_congr' (fun t => ?_)
  rw [count_signature_eq_card adj P χ v t, count_signature_eq_card adj P χ w t]

/-- **Flatness / the local exchange exists.** If `v` and `w` are not separated by one round
(`refineStep … v = refineStep … w` — equitability delivers this for every co-cellular pair),
then for every class `t` there is a bijection between their `t`-neighbour classes. Non-canonical
(choice): the set of such bijections is the local gauge freedom. -/
theorem localExchange_of_refineStep_eq
    (adj : WLGeneric.GAdj V) (P : WLGeneric.GPOE V) (χ : V → Nat) {v w : V}
    (h : WLGeneric.refineStep adj P χ v = WLGeneric.refineStep adj P χ w)
    (t : Nat × Nat × POE) :
    Nonempty (nbhdClass adj P χ v t ≃ nbhdClass adj P χ w t) :=
  ⟨Finset.equivOfCardEq (((refineStep_eq_iff_forall_card_eq adj P χ v w).mp h).2 t)⟩

/-- **Equitability ⟹ local exchange (the Tier A piece-2 headline).** Spelling equitability as
the fixpoint / no-further-split condition (co-cellular ⟹ same refined colour = the equitable
partition condition), every pair of co-cellular vertices admits a local exchange in every class.
This is the flat structure the gauge complex is built on; the group/holonomy content is Tier B/
piece 3 and is untouched here. -/
theorem localExchange_of_equitable
    (adj : WLGeneric.GAdj V) (P : WLGeneric.GPOE V) (χ : V → Nat)
    (hstab : ∀ x y : V, χ x = χ y →
      WLGeneric.refineStep adj P χ x = WLGeneric.refineStep adj P χ y)
    {v w : V} (hcol : χ v = χ w) (t : Nat × Nat × POE) :
    Nonempty (nbhdClass adj P χ v t ≃ nbhdClass adj P χ w t) :=
  localExchange_of_refineStep_eq adj P χ (hstab v w hcol) t

/-! ## Holonomy — different-orbits ⟺ nontrivial holonomy (W2 Tier A, piece 3)

Flatness (piece 2) says the local exchanges *exist* everywhere. The **holonomy** is the
obstruction to gluing them into a *global* section — a colour-automorphism realizing the
exchange. We make this precise as the **flat-but-not-globally-trivial defect**:

* `IsColAut σ` — a global section: a permutation preserving adjacency, `P`, and colour.
* `SameOrbit u v` — a global section carries `u` to `v` (= `u, v` in one orbit of the
  colour-automorphism group).
* `HolonomyNontrivial u v` — `u, v` are **locally flat** (the local exchanges exist) yet **no**
  global section relates them (`¬ SameOrbit`). This is the precise "twist that blocks collapse"
  of the gauge complex: everywhere-locally-exchangeable, globally obstructed.

The load-bearing content — what makes the flat locus the *right* domain — is the equivariance
theorem `sameOrbit_imp_locallyFlat`: **every orbit pair is flat** (a global section restricts to
local exchanges). So on the flat locus, holonomy is *exactly* the orbit defect, and piece 3 is
the equivalence `holonomyNontrivial_iff_diff_orbit`.

Non-vacuity is external (a Lean witness = a WL lower bound): CFI / multipede pairs are flat
(WL-indistinguishable) yet different-orbit (non-isomorphic) — the standing evidence in
`ChainDescent/CFI.lean` and the probe record. The finer structure of this holonomy — that it is
a *linear* (F₂/ring) cocycle when the gauge group is abelian, composing around cycles — is
Tier B (`forceSolvable`) and is deliberately untouched here. -/

/-- A **global section** / colour-automorphism over `V`: a permutation preserving adjacency,
the `P`-relation, and colour. (The generic-`V` analogue of `Consume.IsColAut` over `Fin n`.) -/
def IsColAut (adj : WLGeneric.GAdj V) (P : WLGeneric.GPOE V) (χ : V → Nat)
    (σ : Equiv.Perm V) : Prop :=
  (∀ x y, adj (σ x) (σ y) = adj x y) ∧ (∀ x y, P (σ x) (σ y) = P x y) ∧ (∀ x, χ (σ x) = χ x)

/-- **Signature equivariance.** A colour-automorphism preserves each vertex's signature:
`signature (σ x) = signature x`. The reindexing `u ↦ σ u` is a bijection of the neighbour
multiset, and `IsColAut` makes the integrand invariant class by class. -/
theorem signature_eq_of_colAut {adj : WLGeneric.GAdj V} {P : WLGeneric.GPOE V} {χ : V → Nat}
    {σ : Equiv.Perm V} (h : IsColAut adj P χ σ) (x : V) :
    WLGeneric.signature adj P χ (σ x) = WLGeneric.signature adj P χ x := by
  unfold WLGeneric.signature
  have hfilter : Finset.univ.filter (· ≠ σ x)
      = (Finset.univ.filter (· ≠ x)).map σ.toEmbedding := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Equiv.coe_toEmbedding]
    constructor
    · intro hu
      refine ⟨σ.symm u, ?_, by simp⟩
      intro hw; apply hu; rw [← hw]; simp
    · rintro ⟨w, hw, rfl⟩
      intro hh; exact hw (σ.injective hh)
  rw [hfilter, Finset.map_val, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro w _
  obtain ⟨hadj, hP, hχ⟩ := h
  simp only [Function.comp_apply, Equiv.coe_toEmbedding]
  rw [hχ w, hadj x w, hP x w]

/-- A colour-automorphism preserves the refined colour: `refineStep (σ x) = refineStep x`. -/
theorem refineStep_eq_of_colAut {adj : WLGeneric.GAdj V} {P : WLGeneric.GPOE V} {χ : V → Nat}
    {σ : Equiv.Perm V} (h : IsColAut adj P χ σ) (x : V) :
    WLGeneric.refineStep adj P χ (σ x) = WLGeneric.refineStep adj P χ x :=
  (WLGeneric.refineStep_iff adj P χ (σ x) x).mpr ⟨h.2.2 x, signature_eq_of_colAut h x⟩

/-- **Same orbit** of the colour-automorphism group: a global section carries `u` to `v`. -/
def SameOrbit (adj : WLGeneric.GAdj V) (P : WLGeneric.GPOE V) (χ : V → Nat) (u v : V) : Prop :=
  ∃ σ : Equiv.Perm V, IsColAut adj P χ σ ∧ σ u = v

/-- **Locally flat** (co-cellular and unsplit by one round — equitability delivers it for every
co-cellular pair): the condition under which the per-class local exchanges exist (piece 2). -/
def LocallyFlat (adj : WLGeneric.GAdj V) (P : WLGeneric.GPOE V) (χ : V → Nat) (u v : V) : Prop :=
  WLGeneric.refineStep adj P χ u = WLGeneric.refineStep adj P χ v

/-- `LocallyFlat` is exactly "co-cellular and every class has a local exchange" — the flat
structure spelled in terms of the exchanges themselves (both directions; `⟸` reads a
cardinality back off each bijection). -/
theorem locallyFlat_iff (adj : WLGeneric.GAdj V) (P : WLGeneric.GPOE V) (χ : V → Nat) (u v : V) :
    LocallyFlat adj P χ u v ↔
      χ u = χ v ∧ ∀ t : Nat × Nat × POE,
        Nonempty (nbhdClass adj P χ u t ≃ nbhdClass adj P χ v t) := by
  unfold LocallyFlat
  rw [refineStep_eq_iff_forall_card_eq]
  refine and_congr_right (fun _ => ?_)
  constructor
  · intro hcard t; exact ⟨Finset.equivOfCardEq (hcard t)⟩
  · intro hex t
    obtain ⟨e⟩ := hex t
    have := Fintype.card_congr e
    rwa [Fintype.card_coe, Fintype.card_coe] at this

/-- **Every orbit pair is flat.** A global section carries `u` to `v`, so it preserves the
refined colour: `SameOrbit u v ⟹ LocallyFlat u v`. This is the equivariance that makes the flat
locus the correct domain for holonomy — holonomy can only be the *global* obstruction, because
locally, orbit pairs and merely-flat pairs are indistinguishable. -/
theorem sameOrbit_imp_locallyFlat {adj : WLGeneric.GAdj V} {P : WLGeneric.GPOE V} {χ : V → Nat}
    {u v : V} (h : SameOrbit adj P χ u v) : LocallyFlat adj P χ u v := by
  obtain ⟨σ, hσ, hσuv⟩ := h
  unfold LocallyFlat
  rw [← hσuv]
  exact (refineStep_eq_of_colAut hσ u).symm

/-- **Nontrivial holonomy** = locally flat but no global section: the local exchanges exist yet
no colour-automorphism realizes them. The flat-but-not-globally-trivial defect of the gauge
complex. -/
def HolonomyNontrivial (adj : WLGeneric.GAdj V) (P : WLGeneric.GPOE V) (χ : V → Nat)
    (u v : V) : Prop :=
  LocallyFlat adj P χ u v ∧ ¬ SameOrbit adj P χ u v

/-- **Piece 3 — different-orbits ⟺ nontrivial holonomy, on the flat locus.** For a flat pair
(the local exchanges exist), being in different orbits is exactly nontrivial holonomy. Together
with `sameOrbit_imp_locallyFlat` (every orbit pair is flat), this says: holonomy is precisely
the gap between local exchangeability and global sectionability. -/
theorem holonomyNontrivial_iff_diff_orbit {adj : WLGeneric.GAdj V} {P : WLGeneric.GPOE V}
    {χ : V → Nat} {u v : V} (hflat : LocallyFlat adj P χ u v) :
    HolonomyNontrivial adj P χ u v ↔ ¬ SameOrbit adj P χ u v :=
  ⟨fun h => h.2, fun h => ⟨hflat, h⟩⟩

/-- Soundness of the force side: nontrivial holonomy ⟹ different orbits (the local exchanges
never manufacture a spurious automorphism). -/
theorem not_sameOrbit_of_holonomyNontrivial {adj : WLGeneric.GAdj V} {P : WLGeneric.GPOE V}
    {χ : V → Nat} {u v : V} (h : HolonomyNontrivial adj P χ u v) :
    ¬ SameOrbit adj P χ u v := h.2

--#print axioms refineStep_ne_iff_exists_count_ne
--#print axioms count_signature_eq_card
--#print axioms localExchange_of_equitable
--#print axioms signature_eq_of_colAut
--#print axioms sameOrbit_imp_locallyFlat
--#print axioms holonomyNontrivial_iff_diff_orbit

end GaugeComplex
end ChainDescent
