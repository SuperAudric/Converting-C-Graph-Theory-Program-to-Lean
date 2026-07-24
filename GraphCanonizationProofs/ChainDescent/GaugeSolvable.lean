import ChainDescent.GaugeAbelian

/-!
# W2 Tier B — the solvable branch (Luks reduction skeleton)

Planning doc: `docs/chain-descent-w2-solvability-route.md` §5 (Tier B, solvable branch) + §3/§4a.

The solvable branch is the genuinely-new solver — the delta beyond abelian (S₃/D₄, dihedral,
Heisenberg). Its mathematical heart is the group-theoretic **reduction**: a solvable group has a
terminating **derived series** `⊤ = D₀ ⊇ D₁ ⊇ … ⊇ Dₙ = ⊥` with each successive quotient **abelian**
(`Dₖ₊₁ = ⁅Dₖ, Dₖ⁆`), so canonization reduces along the series to a **tower of abelian steps** — each
the abelian branch (`GaugeAbelian`).

This module builds the **reduction skeleton** (`of_solvable_tower` / `of_solvable_abelian_base`): a
capability `P` holding at the base and preserved across each derived-series step holds for the whole
solvable gauge. It is a **proved** downward induction on the terminating derived series — axiom-clean,
and it makes **no poly claim of its own** (`P` is any predicate).

## The citation (carried, precise)

Instantiated with `P H` = "the gauge `H` has a polynomial-time canonical form," the per-level
hypothesis `hstep` (`P ⁅H,H⁆ → P H`, survival across one abelian-quotient step) is **Luks's reduction**
of the group-theoretic method:

> **Luks, E. M. (1982).** *Isomorphism of graphs of bounded valence can be tested in polynomial time.*
> J. Comput. System Sci. **25**(1), 42–65. · **Babai, L. & Luks, E. M. (1983).** *Canonical labeling
> of graphs.* Proc. 15th STOC, 171–183.

Used only in these known-true forms:
* canonical form under a permutation group of **polynomial order** is poly (brute-force min) — trivial;
* canonical form under an **abelian** group is poly — the abelian branch (`GaugeAbelian`; F₂-Gaussian
  for the CFI kernel, general-abelian by Luks's method);
* **Luks 1982:** canonical form under a group whose composition factors embed in `S_d` for **bounded**
  `d` (the class `Γ_d`) is poly, `n^{O(d)}`.

⚠ **Honest scope of the poly bound.** The classical poly bound covers **bounded** composition-factor
degree (`Γ_d`, Luks) and **bounded-order** gauge (trivial). For a general **solvable** gauge of
**unbounded** degree the end-to-end poly bound is **"plausibly poly"** — this project's standing
assessment (`docs/chain-descent-cameron-entanglement.md:124`), **NOT** a settled classical theorem
(the abelian quotient can be exponential-order, so `n^{O(d)}` does not apply verbatim). This module
therefore carries the **reduction structure** (proved) plus the **known-true per-level facts** (Luks);
the general-unbounded-solvable poly bound is flagged *plausible*, not asserted. Cited results are
theorem-statement content, never fresh `axiom`s (project G3 pattern).
-/

namespace ChainDescent
namespace GaugeComplex

variable {Γ : Type*} [Group Γ]

/-- **The reduction skeleton (proved; no poly claim).** A capability `P` on subgroups that holds for
the trivial subgroup (`hbot`) and is preserved across each derived-series step (`hstep : P ⁅H, H⁆ →
P H`, one abelian-quotient step) holds for the **whole** solvable group (`P ⊤`). Proof = downward
induction on the terminating derived series `⊤ = D₀ ⊇ … ⊇ Dₙ = ⊥`.

Instantiation for the solvable branch: `P H` = "the gauge `H` has a poly canonical form"; `hbot` =
the trivial/rigid gauge (the abelian branch's base); `hstep` = **Luks's reduction** across the
abelian quotient (carried — see the module note for the precise citation and the honest poly scope). -/
theorem of_solvable_tower (P : Subgroup Γ → Prop)
    (hbot : P ⊥) (hstep : ∀ H : Subgroup Γ, P ⁅H, H⁆ → P H)
    (hsol : IsSolvable Γ) : P ⊤ := by
  obtain ⟨n, hn⟩ := hsol.solvable
  have key : ∀ k, k ≤ n → P (derivedSeries Γ (n - k)) := by
    intro k
    induction k with
    | zero => intro _; simpa [hn] using hbot
    | succ k ih =>
      intro hk
      have hstep' := hstep (derivedSeries Γ (n - (k + 1)))
      rw [← derivedSeries_succ] at hstep'
      have he : n - (k + 1) + 1 = n - k := by omega
      rw [he] at hstep'
      exact hstep' (ih (Nat.le_of_succ_le hk))
  simpa [derivedSeries_zero] using key n (le_refl n)

/-- **The solvable branch reduces to the abelian branch.** A capability holding for every **abelian**
gauge subgroup (`habelian` = the abelian branch, `GaugeAbelian`) and preserved across the derived
step (`hstep` = Luks's reduction, carried — module note) holds for the whole **solvable** gauge. The
`⊥` base is discharged from `habelian` (the trivial subgroup is abelian). -/
theorem of_solvable_abelian_base (P : Subgroup Γ → Prop)
    (habelian : ∀ H : Subgroup Γ, (∀ a b : H, a * b = b * a) → P H)
    (hstep : ∀ H : Subgroup Γ, P ⁅H, H⁆ → P H)
    (hsol : IsSolvable Γ) : P ⊤ :=
  of_solvable_tower P
    (habelian ⊥ (fun a b => Subsingleton.elim (a * b) (b * a))) hstep hsol

--#print axioms of_solvable_tower
--#print axioms of_solvable_abelian_base

end GaugeComplex
end ChainDescent
