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

/-- **An oracle supply — UNTRUSTED.** Hands back candidate permutations; carries no proof obligation. In the real
system this is `matchOracle` / the cascade oracle / the rigid solver's kernel. -/
abbrev Supply (n : Nat) := AdjMatrix n → Colouring n → List (Equiv.Perm (Fin n))

/-- The supply, **filtered by the decidable automorphism check**. Everything downstream uses only this. -/
def verified (S : Supply n) (adj : AdjMatrix n) (χ : Colouring n) : List (Equiv.Perm (Fin n)) :=
  (S adj χ).filter (fun g => decide (IsColAut adj χ g))

/-- **Everything that survives the filter is a genuine colouring-preserving automorphism.** This single lemma is
what makes the untrusted supply harmless. -/
theorem isColAut_of_mem_verified {S : Supply n} {adj : AdjMatrix n} {χ : Colouring n}
    {g : Equiv.Perm (Fin n)} (h : g ∈ verified S adj χ) : IsColAut adj χ g := by
  have := (List.mem_filter.mp h).2
  exact of_decide_eq_true this

/-- **★ THE CONSUME RESOLVER.** Keep one representative per orbit of the branch cell under the *verified*
colouring-preserving automorphisms; discard the rest. -/
def consume (S : Supply n) : Resolver n := fun adj χ B =>
  (some ((B.map (rep (verified S adj χ))).dedup),
   (S adj χ).length * (n * n) + n * n * n)

@[simp] theorem narrow_consume (S : Supply n) (adj : AdjMatrix n) (χ : Colouring n) :
    narrow (consume S) adj χ = ((branches χ).map (rep (verified S adj χ))).dedup := rfl

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

end Consume
end ChainDescent
