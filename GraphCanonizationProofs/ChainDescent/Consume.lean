import ChainDescent.Descend
import ChainDescent.Refine

/-!
# `consume` — the ORACLE resolver instance (the `Covering` route)

(`docs/chain-descent-mixed-composition.md` §1.3 + Stage 3.)

The first of the two resolver instances. At a branch cell, `consume` keeps **one representative per orbit** of the
cell under the *colouring-preserving automorphisms* of the graph, and discards the rest. Discarding them is sound
because they are **redundant, not losing**: an automorphism carries a discarded branch onto a kept one, so the two
subtrees have *equal* `descend` values. That is the **`Covering`** route of the resolver contract.

## ★ THE ORACLE IS UNTRUSTED — the resolver VERIFIES

`consume` is parameterized by a **`Supply`**: an arbitrary, unconstrained function handing back *candidate*
permutations (in the real system: `matchOracle` / the cascade oracle / the rigid solver's kernel). The supply
carries **no proof obligation whatsoever**. The resolver filters it through a *decidable* check
(`IsColAut` — "`α` is an automorphism of `adj` and preserves `χ`") and uses only the survivors.

Consequently **`coveringAt_consume` holds for EVERY supply** — even a malicious or buggy one. A supply that returns
junk is filtered to nothing and the resolver simply defers; a supply that returns genuine automorphisms lets it
prune. This is the project's own rule — *never merge two vertices into one orbit without a proof, verified
edge-by-edge* — as a Lean contract, and it is what puts the oracle's **completeness** entirely on the `②`/firing
side of the ledger and **nothing** on the `①` soundness side.

⚠ *Relocation is not elimination*: a supply that never produces automorphisms is sound but useless — the descent
then branches exhaustively and flags. Making the supply *fire often* is the oracle's real job; it just is not a
correctness obligation.

## The fuel-graded contract

`consume` satisfies **`CoveringAt`**, not the unconditional `Covering`. Its covering witness is an automorphism
`α`, and "the discarded branch and the kept one have the same `descend` value" *is* `descend_transport` at
`σ = α` — so the proof needs the descent's own iso-invariance, one fuel level down. `CoveringAt` threads that
induction hypothesis in, which is exactly why it exists (`Descend.lean` §9).
-/

namespace ChainDescent
namespace Consume

open ChainDescent.CanonSpec (Labelled)
open ChainDescent.CostModel (CostM)
open ChainDescent.Descend

variable {n : Nat}

/-! ## 1. Colouring-preserving automorphisms — the *verified* object -/

/-- **`α` is an automorphism of `adj` that preserves the colouring `χ`.** Decidable, and checked at runtime — this
is the "verified edge-by-edge" gate. -/
def IsColAut (adj : AdjMatrix n) (χ : Colouring n) (α : Equiv.Perm (Fin n)) : Prop :=
  (∀ i j : Fin n, adj.adj (α i) (α j) = adj.adj i j) ∧ (∀ v : Fin n, χ (α v) = χ v)

/-- The verification check is **decidable** — it is a finite edge-by-edge test, and it is what makes the untrusted
supply safe to consume. -/
instance decidableIsColAut (adj : AdjMatrix n) (χ : Colouring n) (α : Equiv.Perm (Fin n)) :
    Decidable (IsColAut adj χ α) := inferInstanceAs (Decidable (_ ∧ _))

/-- A verified automorphism fixes the graph: `relabelAdj α adj = adj`. -/
theorem IsColAut.relabel {adj : AdjMatrix n} {χ : Colouring n} {α : Equiv.Perm (Fin n)}
    (h : IsColAut adj χ α) : relabelAdj α adj = adj := by
  cases adj with
  | mk f =>
      have key : (fun i j => f (α.symm i) (α.symm j)) = f := by
        funext i j
        simpa using (h.1 (α.symm i) (α.symm j)).symm
      show AdjMatrix.mk (fun i j => f (α.symm i) (α.symm j)) = AdjMatrix.mk f
      rw [key]

/-- A verified automorphism fixes the colouring: `transportColouring α χ = χ`. -/
theorem IsColAut.transport {adj : AdjMatrix n} {χ : Colouring n} {α : Equiv.Perm (Fin n)}
    (h : IsColAut adj χ α) : transportColouring α χ = χ := by
  funext u
  show χ (α.symm u) = χ u
  simpa using (h.2 (α.symm u)).symm

/-- The identity is a colouring-preserving automorphism (the base of the orbit search). -/
theorem IsColAut.one (adj : AdjMatrix n) (χ : Colouring n) : IsColAut adj χ 1 :=
  ⟨fun _ _ => rfl, fun _ => rfl⟩

/-- Colouring-preserving automorphisms are **closed under composition** — so a word in the verified generators is
itself verified, which is what lets the orbit BFS accumulate a witness. -/
theorem IsColAut.comp {adj : AdjMatrix n} {χ : Colouring n} {g α : Equiv.Perm (Fin n)}
    (hg : IsColAut adj χ g) (hα : IsColAut adj χ α) : IsColAut adj χ (g * α) := by
  constructor
  · intro i j
    show adj.adj (g (α i)) (g (α j)) = adj.adj i j
    rw [hg.1 (α i) (α j), hα.1 i j]
  · intro v
    show χ (g (α v)) = χ v
    rw [hg.2 (α v), hα.2 v]

/-- Colouring-preserving automorphisms are **closed under inverse** — completing `one`/`comp` into a subgroup.
Needed by any orbit-pruning argument, where a candidate reconstructed as a product/conjugate of verified
generators (the P3b license) must itself be certified an automorphism. -/
theorem IsColAut.inv {adj : AdjMatrix n} {χ : Colouring n} {α : Equiv.Perm (Fin n)}
    (hα : IsColAut adj χ α) : IsColAut adj χ α⁻¹ := by
  refine ⟨fun i j => ?_, fun v => ?_⟩
  · have := hα.1 (α⁻¹ i) (α⁻¹ j)
    simpa using this.symm
  · have := hα.2 (α⁻¹ v)
    simpa using this.symm

/-! ## 2. Reachability — the covering witness

`Reach adj χ b m` says a *verified* automorphism carries `b` to `m`. It is exactly the certificate the covering
argument needs, and it is closed under the moves the orbit search makes. -/

/-- Some colouring-preserving automorphism carries `b` to `m`. -/
def Reach (adj : AdjMatrix n) (χ : Colouring n) (b m : Fin n) : Prop :=
  ∃ α : Equiv.Perm (Fin n), IsColAut adj χ α ∧ α b = m

/-- Every vertex is reachable from itself (via the identity). -/
theorem Reach.rfl' (adj : AdjMatrix n) (χ : Colouring n) (b : Fin n) : Reach adj χ b b :=
  ⟨1, IsColAut.one adj χ, rfl⟩

/-- Reachability extends along a verified generator: `Reach b m` and `g` verified give `Reach b (g m)`. -/
theorem Reach.step {adj : AdjMatrix n} {χ : Colouring n} {b m : Fin n} {g : Equiv.Perm (Fin n)}
    (h : Reach adj χ b m) (hg : IsColAut adj χ g) : Reach adj χ b (g m) := by
  obtain ⟨α, hα, hαb⟩ := h
  exact ⟨g * α, hg.comp hα, by show g (α b) = g m; rw [hαb]⟩

/-- **Reachable vertices share a colour** — so an orbit never leaves the branch cell. -/
theorem Reach.colour {adj : AdjMatrix n} {χ : Colouring n} {b m : Fin n} (h : Reach adj χ b m) :
    χ m = χ b := by
  obtain ⟨α, hα, hαb⟩ := h
  rw [← hαb]
  exact hα.2 b

/-! ## 3. The orbit search (computable) -/

/-- One step of the orbit BFS: close the current set under the generators. -/
def orbStep (G : List (Equiv.Perm (Fin n))) (S : List (Fin n)) : List (Fin n) :=
  (S ++ G.flatMap (fun g => S.map (fun v => g v))).dedup

/-- The BFS step is **extensive** — it never loses a vertex it already had. -/
theorem mem_orbStep_of_mem (G : List (Equiv.Perm (Fin n))) (S : List (Fin n)) {x : Fin n}
    (h : x ∈ S) : x ∈ orbStep G S := by
  unfold orbStep
  exact List.mem_dedup.mpr (List.mem_append_left _ h)

/-- The orbit of `b` under `G`. `n` BFS rounds suffice for soundness (which is all the contract needs — a *short*
orbit search only keeps more branches, never fewer). -/
def orbit (G : List (Equiv.Perm (Fin n))) (b : Fin n) : List (Fin n) :=
  (orbStep G)^[n] [b]

/-- `b` survives every BFS round (needed so that `rep` has something to be the minimum of). -/
theorem mem_iterate_self (G : List (Equiv.Perm (Fin n))) (b : Fin n) :
    ∀ k : Nat, b ∈ (orbStep G)^[k] [b]
  | 0 => by simp
  | k + 1 => by
      rw [Function.iterate_succ_apply']
      exact mem_orbStep_of_mem G _ (mem_iterate_self G b k)

/-- `b` is in its own orbit. -/
theorem mem_orbit_self (G : List (Equiv.Perm (Fin n))) (b : Fin n) : b ∈ orbit G b :=
  mem_iterate_self G b n

/-- **Everything the orbit search finds is genuinely reachable by a verified automorphism.** This is the whole
soundness content of the search — and note it holds *whatever* the generator list is, provided each generator was
verified. -/
theorem reach_of_mem_orbit {adj : AdjMatrix n} {χ : Colouring n} {G : List (Equiv.Perm (Fin n))}
    (hG : ∀ g ∈ G, IsColAut adj χ g) (b : Fin n) :
    ∀ (k : Nat) (m : Fin n), m ∈ (orbStep G)^[k] [b] → Reach adj χ b m := by
  intro k
  induction k with
  | zero =>
      intro m hm
      simp only [Function.iterate_zero, id_eq, List.mem_singleton] at hm
      exact hm ▸ Reach.rfl' adj χ b
  | succ k ih =>
      intro m hm
      rw [Function.iterate_succ_apply'] at hm
      unfold orbStep at hm
      rw [List.mem_dedup, List.mem_append] at hm
      rcases hm with h | h
      · exact ih m h
      · obtain ⟨g, hg, hgm⟩ := List.mem_flatMap.mp h
        obtain ⟨x, hx, hxm⟩ := List.mem_map.mp hgm
        exact hxm ▸ (ih x hx).step (hG g hg)

/-! ## 4. Picking the representative -/

/-- Least element of `b :: l` (computable; `Fin n` is linearly ordered). -/
def minList (b : Fin n) : List (Fin n) → Fin n
  | [] => b
  | x :: xs => minList (if x < b then x else b) xs

/-- The minimum is either the seed or a member of the list — so `rep b` always lies in `b`'s orbit. -/
theorem minList_mem : ∀ (l : List (Fin n)) (b : Fin n), minList b l = b ∨ minList b l ∈ l
  | [], _ => Or.inl rfl
  | x :: xs, b => by
      by_cases hx : x < b
      · have hstep : minList b (x :: xs) = minList x xs := by
          show minList (if x < b then x else b) xs = minList x xs
          rw [if_pos hx]
        rcases minList_mem xs x with h | h
        · exact Or.inr (by rw [hstep, h]; exact List.mem_cons_self)
        · exact Or.inr (by rw [hstep]; exact List.mem_cons_of_mem _ h)
      · have hstep : minList b (x :: xs) = minList b xs := by
          show minList (if x < b then x else b) xs = minList b xs
          rw [if_neg hx]
        rcases minList_mem xs b with h | h
        · exact Or.inl (by rw [hstep, h])
        · exact Or.inr (by rw [hstep]; exact List.mem_cons_of_mem _ h)

/-- **The orbit representative of `b`** — the least vertex the orbit search reached from `b`.

The *choice* of representative is deliberately **not** equivariant (orbit members are indistinguishable to
refinement, so no canonical choice exists). That is fine, and it is precisely what the `Covering` route licenses:
only the *result* has to transport, and it does, because the discarded branches are covered. -/
def rep (G : List (Equiv.Perm (Fin n))) (b : Fin n) : Fin n := minList b (orbit G b)

/-- The chosen representative lies in the orbit it represents. -/
theorem rep_mem_orbit (G : List (Equiv.Perm (Fin n))) (b : Fin n) : rep G b ∈ orbit G b := by
  unfold rep
  rcases minList_mem (orbit G b) b with h | h
  · rw [h]; exact mem_orbit_self G b
  · exact h

/-- **The representative is reachable from the branch it replaces** — the covering witness, packaged. -/
theorem reach_rep {adj : AdjMatrix n} {χ : Colouring n} {G : List (Equiv.Perm (Fin n))}
    (hG : ∀ g ∈ G, IsColAut adj χ g) (b : Fin n) : Reach adj χ b (rep G b) :=
  reach_of_mem_orbit hG b n _ (rep_mem_orbit G b)

/-! ## 5. The resolver -/

/-- **An oracle supply — UNTRUSTED, but no longer FREE.** Hands back candidate permutations; carries no *soundness*
obligation. In the real system this is `matchOracle` / the cascade oracle / the rigid solver's kernel.

⚠ **The `CostM` is load-bearing.** With a cost-free supply the oracle's own work is billed at **zero** — and "the
work per node is polynomial" (T-C) is *the* open oracle problem, so a cost model that cannot see it makes `②` a
statement about node count wearing the clothes of a statement about runtime. A supply that ran Schreier–Sims, or
brute-forced all `n!` permutations, would cost the descent nothing. Now it is charged, and `②` has to face it. -/
abbrev Supply (n : Nat) := AdjMatrix n → Colouring n → CostM (List (Equiv.Perm (Fin n)))

/-- The supply's **value** projection — the candidate generators. -/
def gens (S : Supply n) (adj : AdjMatrix n) (χ : Colouring n) : List (Equiv.Perm (Fin n)) :=
  (S adj χ).1

/-- The supply's **cost** projection — the oracle's own work, billed to the descent. -/
def supplyCost (S : Supply n) (adj : AdjMatrix n) (χ : Colouring n) : Nat := (S adj χ).2

/-- The supply, **filtered by the decidable automorphism check**. Everything downstream uses only this. -/
def verified (S : Supply n) (adj : AdjMatrix n) (χ : Colouring n) : List (Equiv.Perm (Fin n)) :=
  (gens S adj χ).filter (fun g => decide (IsColAut adj χ g))

/-- **Everything that survives the filter is a genuine colouring-preserving automorphism.** This single lemma is
what makes the untrusted supply harmless. -/
theorem isColAut_of_mem_verified {S : Supply n} {adj : AdjMatrix n} {χ : Colouring n}
    {g : Equiv.Perm (Fin n)} (h : g ∈ verified S adj χ) : IsColAut adj χ g := by
  have := (List.mem_filter.mp h).2
  exact of_decide_eq_true this

/-- **★ THE CONSUME RESOLVER.** Keep one representative per orbit of the branch cell under the *verified*
colouring-preserving automorphisms; discard the rest.

Cost: the **supply's own work**, plus one edge-by-edge verification (`n²`) per candidate, plus one orbit BFS per
branch (`n` rounds × `|G|` generators × ≤ `n` vertices). Every summand is work the resolver actually does. -/
def consume (S : Supply n) : Resolver n := fun adj χ B =>
  (some ((B.map (rep (verified S adj χ))).dedup),
   supplyCost S adj χ
     + (gens S adj χ).length * (n * n)
     + B.length * ((verified S adj χ).length * (n * n) + n * n))

@[simp] theorem narrow_consume (S : Supply n) (adj : AdjMatrix n) (χ : Colouring n) :
    narrow (consume S) adj χ = ((branches χ).map (rep (verified S adj χ))).dedup := rfl

/-- **The oracle's own work is billed.** -/
theorem consume_cost (S : Supply n) (adj : AdjMatrix n) (χ : Colouring n) (B : List (Fin n)) :
    (consume S adj χ B).2
      = supplyCost S adj χ + (gens S adj χ).length * (n * n)
          + B.length * ((verified S adj χ).length * (n * n) + n * n) := rfl

/-! ## 6. Soundness — `CoveringAt` for EVERY supply -/

/-- The branch list's colour, when it is nonempty. -/
theorem exists_targetColour_of_mem {χ : Colouring n} {v : Fin n} (h : v ∈ branches χ) :
    ∃ c, targetColour χ = some c ∧ χ v = c := by
  unfold branches at h
  cases hc : targetColour χ with
  | none => rw [hc] at h; exact absurd h (List.not_mem_nil)
  | some c =>
      rw [hc] at h
      exact ⟨c, rfl, by simpa using (List.mem_filter.mp h).2⟩

/-- **The narrowing stays inside the branch cell** — orbits never leave it, because a verified automorphism
preserves the colouring. -/
theorem narrow_consume_subset (S : Supply n) (adj : AdjMatrix n) (χ : Colouring n) {v : Fin n}
    (h : v ∈ narrow (consume S) adj χ) : v ∈ branches χ := by
  rw [narrow_consume] at h
  obtain ⟨b, hb, hbv⟩ := List.mem_map.mp (List.mem_dedup.mp h)
  obtain ⟨c, hc, hbc⟩ := exists_targetColour_of_mem hb
  have hreach : Reach adj χ b (rep (verified S adj χ) b) :=
    reach_rep (fun _ hg => isColAut_of_mem_verified hg) b
  refine (mem_branches_iff hc v).mpr ?_
  rw [← hbv, hreach.colour, hbc]

/-- The narrowing is never empty on a non-discrete node (it contains a representative of every branch). -/
theorem narrow_consume_ne_nil (S : Supply n) (adj : AdjMatrix n) {χ : Colouring n}
    (h : ¬ Discrete χ) : narrow (consume S) adj χ ≠ [] := by
  obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil _ (branches_ne_nil h)
  intro hnil
  have : rep (verified S adj χ) b ∈ narrow (consume S) adj χ := by
    rw [narrow_consume]
    exact List.mem_dedup.mpr (List.mem_map.mpr ⟨b, hb, rfl⟩)
  rw [hnil] at this
  exact absurd this (List.not_mem_nil)

/-- `consume` is a **proper** narrowing: it stays inside the branch cell and never empties it — the hypothesis
`canonForm?_ne_none` (totality) needs. -/
theorem narrowProper_consume (S : Supply n) : NarrowProper (consume S) :=
  ⟨fun adj χ h => narrow_consume_ne_nil S adj h, fun adj χ _ h => narrow_consume_subset S adj χ h⟩

/-- **★★ THE COVERING WITNESS — a verified automorphism makes two branches VALUE-EQUAL.**

If `α` is a colouring-preserving automorphism then branching on `v` and branching on `α v` give the *same*
`descend` value. This is `descend_transport` at `σ = α`: `relabelAdj α adj = adj` and `transportColouring α χ = χ`,
so the transport equation degenerates to an equality between two branches of the *same* graph. It is exactly here
that the fuel-graded `CoveringAt` earns its keep — the induction hypothesis `ih` is what makes this available. -/
theorem branchVal_eq_of_isColAut {rf : Refiner n} {R : Resolver n} (hre : RefineEquivariant rf)
    {fuel : Nat} (ih : TransportAt rf R fuel) (adj : AdjMatrix n) (χ : Colouring n)
    {α : Equiv.Perm (Fin n)} (hα : IsColAut adj χ α) (v : Fin n) :
    (descend rf R adj fuel (refineV rf adj (indivOne χ (α v)))).1
      = (descend rf R adj fuel (refineV rf adj (indivOne χ v))).1 := by
  have h := branchVal_transport hre ih adj α χ v
  rw [hα.relabel, hα.transport] at h
  exact h

/-- **★★★ `consume` IS SOUND — for EVERY supply, however wrong.** The narrowed aggregate equals the full one,
because each discarded branch is *value-equal* to the kept representative of its orbit. -/
theorem coveringAt_consume {rf : Refiner n} (hre : RefineEquivariant rf) (S : Supply n) :
    CoveringAt rf (consume S) := by
  intro fuel ih adj χ
  set G := verified S adj χ with hG
  set f : Fin n → Option (Labelled n) :=
    fun v => (descend rf (consume S) adj fuel (refineV rf adj (indivOne χ v))).1 with hf
  -- every branch is value-equal to its orbit representative
  have hval : ∀ b : Fin n, f (rep G b) = f b := by
    intro b
    obtain ⟨α, hα, hαb⟩ := reach_rep (adj := adj) (χ := χ)
      (fun _ hg => isColAut_of_mem_verified hg) b
    rw [hf]
    simp only
    rw [← hαb]
    exact branchVal_eq_of_isColAut hre ih adj χ hα b
  refine aggregate_congr_mem ?_
  intro x
  constructor
  · -- kept ⟹ present in the full list (the narrowing stays inside the cell)
    intro hx
    obtain ⟨v, hv, hvx⟩ := List.mem_map.mp hx
    exact List.mem_map.mpr ⟨v, narrow_consume_subset S adj χ hv, hvx⟩
  · -- full ⟹ present among the kept (its representative carries the same value)
    intro hx
    obtain ⟨b, hb, hbx⟩ := List.mem_map.mp hx
    refine List.mem_map.mpr ⟨rep G b, ?_, ?_⟩
    · rw [narrow_consume]
      exact List.mem_dedup.mpr (List.mem_map.mpr ⟨b, hb, rfl⟩)
    · rw [hval b]; exact hbx

/-- **`consume` satisfies the resolver contract.** -/
theorem narrowTransport_consume {rf : Refiner n} (hre : RefineEquivariant rf) (S : Supply n) :
    NarrowTransport rf (consume S) :=
  narrowTransport_of_coveringAt hre (coveringAt_consume hre S)

/-! ## 7. ★ THE CAPSTONE — the oracle-driven canonizer -/

/-- **★★★ THE ORACLE-DRIVEN CANONIZER IS A CANONICAL FORM THAT ANSWERS — for EVERY oracle supply.**

`①a`, `①b`, `①c` all hold, and the descent never flags, **with no hypothesis on the oracle at all**. A broken
oracle costs branches; it cannot cost correctness. -/
theorem consume_canonizer (S : Supply n) :
    CanonSpec.IsCanonicalFormOpt
        (Descend.canonForm? (Refine.encodeFree (n := n)) (consume S))
    ∧ ∀ adj : AdjMatrix n,
        Descend.canonForm? (Refine.encodeFree (n := n)) (consume S) adj ≠ none :=
  ⟨Descend.isCanonicalFormOpt_canonForm? Refine.refineEquivariant_encodeFree
      (narrowTransport_consume Refine.refineEquivariant_encodeFree S),
   fun adj => Descend.canonForm?_ne_none Refine.refineSplits_encodeFree
      (narrowProper_consume S) adj⟩

/-- The runnable version (the `encodeFreeFast` refiner — value-equal, so it inherits everything). -/
theorem consume_canonizer_fast (S : Supply n) :
    CanonSpec.IsCanonicalFormOpt
        (Descend.canonForm? (Refine.encodeFreeFast (n := n)) (consume S))
    ∧ ∀ adj : AdjMatrix n,
        Descend.canonForm? (Refine.encodeFreeFast (n := n)) (consume S) adj ≠ none := by
  rw [Refine.encodeFreeFast_eq]
  exact consume_canonizer S

/-! ## 8. ★ FIRING — consume provably removes ALL branching on a symmetric cell

`narrowProper_consume` says the narrowing is nonempty and inside the cell. **A resolver that returned the whole
cell satisfies exactly that** — so properness certifies nothing about *firing*: sound, and silently useless. The
theorems below pin consume's firing precisely, and they are what make the oracle route worth having.

The engine is that the orbit BFS **converges**. `orbit G b = (orbStep G)^[n] [b]` runs a fixed `n` rounds; a priori
that only reaches vertices at generator-distance ≤ `n`, and `rep` could then differ between two vertices of the
same orbit — leaving both in the narrowing. In fact `n` rounds always suffice: every non-closed round adds at least
one vertex and there are only `n`. Closure makes `orbit G b` the **smallest `G`-closed set containing `b`**, hence
a genuine orbit, hence `rep` (its least element) is **constant on it**. -/

/-- `S` is closed under the generators — the BFS's fixpoint condition. -/
def Closed (G : List (Equiv.Perm (Fin n))) (S : List (Fin n)) : Prop :=
  ∀ g ∈ G, ∀ v ∈ S, g v ∈ S

theorem mem_orbStep_iff (G : List (Equiv.Perm (Fin n))) (S : List (Fin n)) (x : Fin n) :
    x ∈ orbStep G S ↔ x ∈ S ∨ ∃ g ∈ G, ∃ v ∈ S, g v = x := by
  unfold orbStep
  rw [List.mem_dedup, List.mem_append]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · obtain ⟨g, hg, hgx⟩ := List.mem_flatMap.mp h
      obtain ⟨v, hv, hvx⟩ := List.mem_map.mp hgx
      exact Or.inr ⟨g, hg, v, hv, hvx⟩
  · rintro (h | ⟨g, hg, v, hv, hvx⟩)
    · exact Or.inl h
    · exact Or.inr (List.mem_flatMap.mpr ⟨g, hg, List.mem_map.mpr ⟨v, hv, hvx⟩⟩)

/-- A closed set is a **fixpoint** of the BFS step. -/
theorem mem_orbStep_of_closed {G : List (Equiv.Perm (Fin n))} {S : List (Fin n)} (hcl : Closed G S)
    (x : Fin n) : x ∈ orbStep G S ↔ x ∈ S := by
  rw [mem_orbStep_iff]
  exact ⟨fun h => h.elim id (fun ⟨g, hg, v, hv, hgv⟩ => hgv ▸ hcl g hg v hv), Or.inl⟩

/-- Once closed, always closed: iterating the BFS from a closed set changes nothing. -/
theorem mem_iterate_of_closed {G : List (Equiv.Perm (Fin n))} :
    ∀ (j : Nat) (S : List (Fin n)), Closed G S → ∀ x, x ∈ (orbStep G)^[j] S ↔ x ∈ S := by
  intro j
  induction j with
  | zero => intro S _ x; simp
  | succ j ih =>
      intro S hcl x
      rw [Function.iterate_succ_apply]
      have hcl' : Closed G (orbStep G S) := fun g hg v hv =>
        (mem_orbStep_of_closed hcl (g v)).mpr (hcl g hg v ((mem_orbStep_of_closed hcl v).mp hv))
      rw [ih (orbStep G S) hcl' x, mem_orbStep_of_closed hcl x]

/-- The BFS is monotone. -/
theorem iterate_subset_succ (G : List (Equiv.Perm (Fin n))) (b : Fin n) (k : Nat) :
    ((orbStep G)^[k] [b]).toFinset ⊆ ((orbStep G)^[k + 1] [b]).toFinset := by
  intro x hx
  rw [List.mem_toFinset] at hx ⊢
  rw [Function.iterate_succ_apply']
  exact mem_orbStep_of_mem G _ hx

/-- **Every non-closed BFS round strictly grows the reached set.** The monovariant behind convergence. -/
theorem card_lt_of_not_closed {G : List (Equiv.Perm (Fin n))} {b : Fin n} {k : Nat}
    (h : ¬ Closed G ((orbStep G)^[k] [b])) :
    ((orbStep G)^[k] [b]).toFinset.card < ((orbStep G)^[k + 1] [b]).toFinset.card := by
  unfold Closed at h
  push_neg at h
  obtain ⟨g, hg, v, hv, hgv⟩ := h
  refine Finset.card_lt_card ⟨iterate_subset_succ G b k, fun hsub => ?_⟩
  have hmem : g v ∈ (orbStep G)^[k + 1] [b] := by
    rw [Function.iterate_succ_apply']
    exact (mem_orbStep_iff G _ _).mpr (Or.inr ⟨g, hg, v, hv, rfl⟩)
  exact hgv (List.mem_toFinset.mp (hsub (List.mem_toFinset.mpr hmem)))

/-- **★ THE BFS CONVERGES — `n` rounds are enough.** If it had not closed by round `n`, every one of the `n + 1`
rounds `0 … n` would have strictly grown the reached set, forcing more than `n` distinct vertices into `Fin n`. -/
theorem orbit_closed (G : List (Equiv.Perm (Fin n))) (b : Fin n) : Closed G (orbit G b) := by
  by_contra hnc
  -- If round `n` is not closed, no earlier round was either (closure propagates forward).
  have hnotclosed : ∀ k, k ≤ n → ¬ Closed G ((orbStep G)^[k] [b]) := by
    intro k hk hcl
    refine hnc ?_
    -- `orbit = (orbStep)^[n-k] ((orbStep)^[k] [b])`, and iterating a closed set preserves membership
    have hsplit : orbit G b = (orbStep G)^[n - k] ((orbStep G)^[k] [b]) := by
      unfold orbit
      rw [← Function.iterate_add_apply]
      congr 1
      omega
    intro g hg v hv
    rw [hsplit] at hv ⊢
    rw [mem_iterate_of_closed _ _ hcl] at hv ⊢
    exact hcl g hg v hv
  -- Hence the reached set grows by ≥ 1 every round: `card (round k) ≥ k + 1`.
  have hgrow : ∀ k, k ≤ n → k + 1 ≤ ((orbStep G)^[k] [b]).toFinset.card := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
        intro hk
        have hlt := card_lt_of_not_closed (hnotclosed k (by omega))
        have := ih (by omega)
        omega
  -- But a `Finset (Fin n)` has at most `n` elements.
  have hle : ((orbStep G)^[n] [b]).toFinset.card ≤ n := by
    simpa using Finset.card_le_univ ((orbStep G)^[n] [b]).toFinset
  have := hgrow n (le_refl n)
  omega

/-! ### Reachability by a word in the generators -/

/-- `m` is reachable from `b` by a **word** in the generators. (`Reach` says *some* automorphism does it;
`WordReach` says the supply's own generators do — which is what the oracle must actually deliver.) -/
inductive WordReach (G : List (Equiv.Perm (Fin n))) : Fin n → Fin n → Prop
  | refl (b : Fin n) : WordReach G b b
  | step {b m : Fin n} (h : WordReach G b m) {g : Equiv.Perm (Fin n)} (hg : g ∈ G) :
      WordReach G b (g m)

/-- **The orbit list contains everything a word reaches** — this is what convergence buys: the BFS is not merely a
depth-`n` approximation, it is the whole orbit. -/
theorem mem_orbit_of_wordReach {G : List (Equiv.Perm (Fin n))} {b m : Fin n}
    (h : WordReach G b m) : m ∈ orbit G b := by
  induction h with
  | refl => exact mem_orbit_self G b
  | step _ hg ih => exact orbit_closed G b _ hg _ ih

/-! ### `rep` is constant on an orbit -/

theorem minList_le_seed : ∀ (l : List (Fin n)) (b : Fin n), minList b l ≤ b
  | [], b => le_refl b
  | x :: xs, b => by
      have hstep : minList b (x :: xs) = minList (if x < b then x else b) xs := rfl
      rw [hstep]
      refine le_trans (minList_le_seed xs _) ?_
      by_cases h : x < b
      · rw [if_pos h]; exact le_of_lt h
      · rw [if_neg h]

theorem minList_le : ∀ (l : List (Fin n)) (b : Fin n) (x : Fin n), x ∈ l → minList b l ≤ x
  | [], _, _, hx => absurd hx (List.not_mem_nil)
  | y :: ys, b, x, hx => by
      have hstep : minList b (y :: ys) = minList (if y < b then y else b) ys := rfl
      rw [hstep]
      rcases List.mem_cons.mp hx with rfl | hx'
      · refine le_trans (minList_le_seed ys _) ?_
        by_cases h : x < b
        · rw [if_pos h]
        · rw [if_neg h]; exact not_lt.mp h
      · exact minList_le ys _ x hx'

/-- **★★ `rep` IS CONSTANT ON AN ORBIT.** If two branch vertices reach the *same* set of vertices under the
verified generators, they get the *same* representative — so `consume` maps them to one branch, not two. This is
the lemma properness could never give. -/
theorem rep_eq_of_orbit_eq {G : List (Equiv.Perm (Fin n))} {u w : Fin n}
    (h : ∀ x, x ∈ orbit G u ↔ x ∈ orbit G w) : rep G u = rep G w := by
  have hle : ∀ a b : Fin n, (∀ x, x ∈ orbit G a ↔ x ∈ orbit G b) → rep G a ≤ rep G b := by
    intro a b hab
    -- `rep G b` lies in `b`'s orbit = `a`'s orbit, and `rep G a` is ≤ everything in `a`'s orbit.
    have hmem : rep G b ∈ orbit G a := (hab (rep G b)).mpr (rep_mem_orbit G b)
    exact minList_le _ _ _ hmem
  exact le_antisymm (hle u w h) (hle w u (fun x => (h x).symm))

/-! ### ★ THE FIRING THEOREM -/

/-- **The oracle's FIRING obligation, stated exactly.** The branch cell is a single orbit of the supply's *verified*
generators — i.e. the supply really does hand over enough automorphisms to connect the cell.

This is the whole of `matchOracle`'s remaining job. It is a **②** obligation, not a **①** one (`consume_canonizer`
holds for every supply), but it is not optional: without it consume defers and the descent branches. -/
def CellIsOrbit (S : Supply n) (adj : AdjMatrix n) (χ : Colouring n) : Prop :=
  ∀ u ∈ branches χ, ∀ w ∈ branches χ, WordReach (verified S adj χ) u w

/-- Every orbit stays inside the branch cell (a verified automorphism preserves the colouring). -/
theorem orbit_subset_branches {S : Supply n} {adj : AdjMatrix n} {χ : Colouring n} {u : Fin n}
    (hu : u ∈ branches χ) {x : Fin n} (hx : x ∈ orbit (verified S adj χ) u) : x ∈ branches χ := by
  obtain ⟨c, hc, huc⟩ := exists_targetColour_of_mem hu
  have hreach : Reach adj χ u x :=
    reach_of_mem_orbit (fun _ hg => isColAut_of_mem_verified hg) u n x hx
  exact (mem_branches_iff hc x).mpr (by rw [hreach.colour, huc])

/-! ### ★★ THE GRADED FIRING LEMMA — consume merges *exactly* what its generators connect

The singleton theorem below is the **perfect endpoint** (the whole cell is one orbit). It is not the useful case: a
real cell splits into *several* orbits, and consume should collapse `|cell|` branches to *the number of orbits*.
`rep_eq_of_wordReach` is the statement that actually delivers that, with **no hypothesis on the supply at all** —
whatever the supply proves, consume merges; whatever it does not, consume keeps. **Partial power, partial progress.**

Getting it requires the orbit to be **inverse-closed**, not merely forward-closed: `rep u = rep w` needs the two
orbits to be the *same set*, and forward-closure alone only gives one inclusion. A generator permutes a finite
forward-closed set, so it maps it *onto* itself — that is where the inverses come from. -/

/-- A finite forward-closed set is **inverse-closed**: `g` maps it injectively into itself, hence onto itself. -/
theorem closed_inv {G : List (Equiv.Perm (Fin n))} {S : List (Fin n)} (hcl : Closed G S) :
    ∀ g ∈ G, ∀ v ∈ S, g.symm v ∈ S := by
  intro g hg v hv
  have himg : S.toFinset.image g ⊆ S.toFinset := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
    exact List.mem_toFinset.mpr (hyx ▸ hcl g hg y (List.mem_toFinset.mp hy))
  have hcard : S.toFinset.card ≤ (S.toFinset.image g).card :=
    le_of_eq (Finset.card_image_of_injective _ g.injective).symm
  have heq : S.toFinset.image g = S.toFinset := Finset.eq_of_subset_of_card_le himg hcard
  have hv' : v ∈ S.toFinset.image g := by rw [heq]; exact List.mem_toFinset.mpr hv
  obtain ⟨y, hy, hyv⟩ := Finset.mem_image.mp hv'
  have : g.symm v = y := by rw [← hyv]; simp
  exact this ▸ List.mem_toFinset.mp hy

/-- **Minimality** — the orbit is contained in *every* closed set containing its seed. -/
theorem mem_of_mem_orbit_of_closed {G : List (Equiv.Perm (Fin n))} {T : List (Fin n)}
    (hcl : Closed G T) {b : Fin n} (hb : b ∈ T) :
    ∀ (k : Nat) (x : Fin n), x ∈ (orbStep G)^[k] [b] → x ∈ T := by
  intro k
  induction k with
  | zero => intro x hx; simpa using (by simpa using hx : x = b) ▸ hb
  | succ k ih =>
      intro x hx
      rw [Function.iterate_succ_apply'] at hx
      rcases (mem_orbStep_iff G _ x).mp hx with h | ⟨g, hg, v, hv, hgv⟩
      · exact ih x h
      · exact hgv ▸ hcl g hg v (ih v hv)

/-- The orbit is inverse-closed (convergence + `closed_inv`). -/
theorem orbit_closed_inv (G : List (Equiv.Perm (Fin n))) (b : Fin n) :
    ∀ g ∈ G, ∀ v ∈ orbit G b, g.symm v ∈ orbit G b :=
  closed_inv (orbit_closed G b)

/-- **The reachability relation is symmetric on orbits**: if a word takes `u` to `w`, then `u` lies in `w`'s orbit.
(The inverse word does it — available because the orbit is inverse-closed.) -/
theorem self_mem_orbit_of_wordReach {G : List (Equiv.Perm (Fin n))} {u w : Fin n}
    (h : WordReach G u w) : u ∈ orbit G w := by
  induction h with
  | refl => exact mem_orbit_self G u
  | @step m _ g hg ih =>
      -- `m = g⁻¹ (g m)` lies in `(g m)`'s orbit, so `m`'s whole orbit does — and `u` is in `m`'s orbit.
      have hm : m ∈ orbit G (g m) := by
        have := orbit_closed_inv G (g m) g hg (g m) (mem_orbit_self G (g m))
        simpa using this
      exact mem_of_mem_orbit_of_closed (orbit_closed G (g m)) hm n u ih

/-- Connected vertices have the **same orbit set**. -/
theorem orbit_eq_of_wordReach {G : List (Equiv.Perm (Fin n))} {u w : Fin n} (h : WordReach G u w) :
    ∀ x, x ∈ orbit G u ↔ x ∈ orbit G w := by
  have hw : w ∈ orbit G u := mem_orbit_of_wordReach h
  have hu : u ∈ orbit G w := self_mem_orbit_of_wordReach h
  exact fun x =>
    ⟨fun hx => mem_of_mem_orbit_of_closed (orbit_closed G w) hu n x hx,
     fun hx => mem_of_mem_orbit_of_closed (orbit_closed G u) hw n x hx⟩

/-- **★★★ THE GRADED FIRING LEMMA. Consume merges exactly the branches its generators connect** — with **no
hypothesis on the supply**. A supply that proves one automorphism merges one pair; a supply that proves the whole
cell's symmetry collapses the cell. **Partial power gives partial progress**, which is what the perfect-endpoint
theorems below cannot say. -/
theorem rep_eq_of_wordReach {G : List (Equiv.Perm (Fin n))} {u w : Fin n} (h : WordReach G u w) :
    rep G u = rep G w :=
  rep_eq_of_orbit_eq (orbit_eq_of_wordReach h)

theorem rep_const_of_cellIsOrbit {S : Supply n} {adj : AdjMatrix n} {χ : Colouring n}
    (horb : CellIsOrbit S adj χ) {u w : Fin n} (hu : u ∈ branches χ) (hw : w ∈ branches χ) :
    rep (verified S adj χ) u = rep (verified S adj χ) w :=
  rep_eq_of_wordReach (horb u hu w hw)

/-- **The dedup of a constant map over a nonempty list is a singleton** — the shape both firing theorems land in
(here, and for the composite in `Composite.lean`). -/
theorem dedup_map_length_one {L : List (Fin n)} (hne : L ≠ []) {f : Fin n → Fin n}
    (hconst : ∀ a ∈ L, ∀ b ∈ L, f a = f b) : ((L.map f).dedup).length = 1 := by
  obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil _ hne
  set D := (L.map f).dedup with hD
  have hmem : ∀ x, x ∈ D ↔ x = f u := by
    intro x
    rw [hD, List.mem_dedup]
    constructor
    · rintro hx
      obtain ⟨b, hb, hbx⟩ := List.mem_map.mp hx
      rw [← hbx, hconst b hb u hu]
    · intro hx; exact List.mem_map.mpr ⟨u, hu, by rw [hx]⟩
  have hfin : D.toFinset = {f u} :=
    Finset.eq_singleton_iff_unique_mem.mpr
      ⟨List.mem_toFinset.mpr ((hmem _).mpr rfl),
       fun x hx => (hmem x).mp (List.mem_toFinset.mp hx)⟩
  have hcard := List.toFinset_card_of_nodup (hD ▸ List.nodup_dedup (L.map f))
  rw [hfin] at hcard
  simpa using hcard.symm

/-- **A merge is a strict shortening.** If two *distinct* branches get the same representative, the deduplicated
narrowing is strictly shorter than the list it came from — one merged pair is one branch saved. -/
theorem dedup_map_length_lt {L : List (Fin n)} (hL : L.Nodup) {f : Fin n → Fin n} {a b : Fin n}
    (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b) (hfab : f a = f b) :
    ((L.map f).dedup).length < L.length := by
  -- the image of `L` is the image of `L` with `a` removed (b covers a's value), so it is strictly smaller
  have himg : L.toFinset.image f = (L.toFinset.erase a).image f := by
    refine Finset.Subset.antisymm (fun x hx => ?_)
      (Finset.image_subset_image (Finset.erase_subset _ _))
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
    by_cases hya : y = a
    · exact Finset.mem_image.mpr
        ⟨b, Finset.mem_erase.mpr ⟨fun hc => hab hc.symm, List.mem_toFinset.mpr hb⟩,
         by rw [← hfab, ← hya]; exact hyx⟩
    · exact Finset.mem_image.mpr ⟨y, Finset.mem_erase.mpr ⟨hya, hy⟩, hyx⟩
  have hcardL : L.toFinset.card = L.length := List.toFinset_card_of_nodup hL
  have hpos : 0 < L.toFinset.card := by
    rw [hcardL]; exact List.length_pos_of_mem ha
  have hdedup : ((L.map f).dedup).length = (L.toFinset.image f).card := by
    rw [← List.toFinset_card_of_nodup (List.nodup_dedup (L.map f))]
    congr 1
    ext x
    simp [List.mem_toFinset, List.mem_dedup]
  have hlt : (L.toFinset.image f).card < L.toFinset.card := by
    rw [himg]
    refine lt_of_le_of_lt (Finset.card_image_le) ?_
    rw [Finset.card_erase_of_mem (List.mem_toFinset.mpr ha)]
    omega
  omega

theorem consume_singleton_of_cellIsOrbit {S : Supply n} {adj : AdjMatrix n} {χ : Colouring n}
    (hd : ¬ Discrete χ) (horb : CellIsOrbit S adj χ) :
    (narrow (consume S) adj χ).length = 1 := by
  rw [narrow_consume]
  exact dedup_map_length_one (branches_ne_nil hd)
    (fun a ha b hb => rep_const_of_cellIsOrbit horb ha hb)

/-- **★★ CONSUME FIRES ON PARTIAL POWER.** A *single* verified automorphism connecting two distinct branches
already shortens the narrowing — no need for the cell to be one orbit. This is the theorem that says the oracle
does **not** have to be perfect to be useful: it is rewarded for exactly as much symmetry as it can prove, and
penalized for nothing. -/
theorem consume_narrows_of_wordReach {S : Supply n} {adj : AdjMatrix n} {χ : Colouring n}
    {u w : Fin n} (hu : u ∈ branches χ) (hw : w ∈ branches χ) (huw : u ≠ w)
    (h : WordReach (verified S adj χ) u w) :
    (narrow (consume S) adj χ).length < (branches χ).length := by
  rw [narrow_consume]
  exact dedup_map_length_lt (branches_nodup χ) hu hw huw (rep_eq_of_wordReach h)

/-! ## 9. ★★ `rep` MERGES **EXACTLY** THE ORBIT — the converse of `rep_eq_of_wordReach`

`rep_eq_of_wordReach` is one direction: connected ⟹ merged. The other direction — **merged ⟹ connected** — is
what turns `rep` from "a sound merge" into "*the* orbit relation", and it is what the **flag** needs. The flag
reads the narrowing's *length*, i.e. the number of distinct representatives; to know that this count is
`σ`-invariant we must know it counts **orbits**, not an artefact of the least-index choice (which is emphatically
*not* equivariant). So the iff below is the hinge of `SupplyTransport.lean` / `Stall.StallEquivariant`.

The engine is that `orbit` is not a depth-`n` approximation but **exactly** the word-reachable set
(`mem_orbit_iff_wordReach`, from convergence), so `WordReach` is a genuine equivalence relation on it. -/

/-- Everything the orbit search reaches is reached by a **word** (the converse of `mem_orbit_of_wordReach`). -/
theorem wordReach_of_mem_iterate {G : List (Equiv.Perm (Fin n))} {b : Fin n} :
    ∀ (k : Nat) (m : Fin n), m ∈ (orbStep G)^[k] [b] → WordReach G b m := by
  intro k
  induction k with
  | zero =>
      intro m hm
      simp only [Function.iterate_zero, id_eq, List.mem_singleton] at hm
      rw [hm]
      exact WordReach.refl b
  | succ k ih =>
      intro m hm
      rw [Function.iterate_succ_apply'] at hm
      rcases (mem_orbStep_iff G _ m).mp hm with h | ⟨g, hg, v, hv, hgv⟩
      · exact ih m h
      · exact hgv ▸ (ih v hv).step hg

/-- **The orbit list IS the word-reachable set.** -/
theorem mem_orbit_iff_wordReach {G : List (Equiv.Perm (Fin n))} {b m : Fin n} :
    m ∈ orbit G b ↔ WordReach G b m :=
  ⟨wordReach_of_mem_iterate n m, mem_orbit_of_wordReach⟩

/-- **★ `WordReach` IS DECIDABLE, and the decision procedure is the orbit BFS itself.** `orbit` is a
computable `n`-round fixpoint and the equivalence above is already proved, so this is one
`decidable_of_iff` — no `Classical.dec`, no search over `Equiv.Perm (Fin n)`.

This is what lets a *supply-guarded* object be **executable** rather than classically stubbed; see
`Deepen.orbKeyG`, whose guard was a `Classical.dec` placeholder until this instance existed. -/
instance decidableWordReach (G : List (Equiv.Perm (Fin n))) (u w : Fin n) :
    Decidable (WordReach G u w) :=
  decidable_of_iff (w ∈ orbit G u) mem_orbit_iff_wordReach

/-- Hence **`CellIsOrbit` is decidable** — two bounded `∀`s over the branch cell, each disjunct decided
by the BFS above. The cost is the honest one: `≤ |cell|²` orbit closures. -/
instance decidableCellIsOrbit (S : Supply n) (adj : AdjMatrix n) (χ : Colouring n) :
    Decidable (CellIsOrbit S adj χ) := by
  unfold CellIsOrbit
  infer_instance

/-- Word-reachability is **transitive**. -/
theorem WordReach.trans {G : List (Equiv.Perm (Fin n))} {u m w : Fin n}
    (h₁ : WordReach G u m) (h₂ : WordReach G m w) : WordReach G u w := by
  induction h₂ with
  | refl => exact h₁
  | step _ hg ih => exact ih.step hg

/-- Word-reachability is **symmetric** (the orbit is inverse-closed, `closed_inv`). -/
theorem WordReach.symm {G : List (Equiv.Perm (Fin n))} {u w : Fin n} (h : WordReach G u w) :
    WordReach G w u :=
  wordReach_of_mem_iterate n u (self_mem_orbit_of_wordReach h)

/-- A branch reaches its own representative. -/
theorem wordReach_rep (G : List (Equiv.Perm (Fin n))) (b : Fin n) : WordReach G b (rep G b) :=
  wordReach_of_mem_iterate n _ (rep_mem_orbit G b)

/-- **★★★ `rep` MERGES EXACTLY THE ORBIT.** Two branches share a representative **iff** the verified generators
connect them. The `←` is `rep_eq_of_wordReach` (partial power ⟹ partial progress); the `→` is what says consume
merges **nothing more** — the least-index choice adds no spurious identifications. Together: the length of the
narrowing **counts orbits**, which is exactly what `Stall.StallEquivariant` needs and what a merely-sound `rep`
could never give. -/
theorem rep_eq_iff_wordReach {G : List (Equiv.Perm (Fin n))} {u w : Fin n} :
    rep G u = rep G w ↔ WordReach G u w := by
  refine ⟨fun h => ?_, rep_eq_of_wordReach⟩
  have h1 : WordReach G u (rep G w) := by rw [← h]; exact wordReach_rep G u
  exact h1.trans (wordReach_rep G w).symm

/-! ## 10. Conjugation — `IsColAut` transports -/

/-- **The verification check transports.** `α` is a colouring-preserving automorphism of `(adj, χ)` **iff** its
`σ`-conjugate is one of `(σ·adj, σ·χ)`. This is the reason a *structural* supply can be equivariant at all: the
thing it must hand back on the relabelled graph is the conjugate of what it hands back here. -/
theorem isColAut_conj_iff (σ : Equiv.Perm (Fin n)) {adj : AdjMatrix n} {χ : Colouring n}
    {α : Equiv.Perm (Fin n)} :
    IsColAut (relabelAdj σ adj) (transportColouring σ χ) (σ * α * σ⁻¹) ↔ IsColAut adj χ α := by
  have happ : ∀ u : Fin n, (σ * α * σ⁻¹) u = σ (α (σ.symm u)) := fun u => rfl
  constructor
  · rintro ⟨hadj, hχ⟩
    refine ⟨fun i j => ?_, fun v => ?_⟩
    · have h := hadj (σ i) (σ j)
      simp only [happ, relabelAdj_adj, Equiv.symm_apply_apply] at h
      exact h
    · have h := hχ (σ v)
      show χ (α v) = χ v
      simp only [happ, transportColouring, Equiv.symm_apply_apply] at h
      exact h
  · rintro ⟨hadj, hχ⟩
    refine ⟨fun i j => ?_, fun v => ?_⟩
    · simp only [happ, relabelAdj_adj, Equiv.symm_apply_apply]
      exact hadj (σ.symm i) (σ.symm j)
    · simp only [happ, transportColouring, Equiv.symm_apply_apply]
      exact hχ (σ.symm v)

end Consume
end ChainDescent
