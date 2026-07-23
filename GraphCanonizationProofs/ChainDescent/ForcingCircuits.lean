import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# P1 — extraction soundness for the rigid solver (Algorithm R), pure F₂

This is the **standalone F₂ / linear-algebra brick** of the rigid seal's Lean roadmap
(`docs/chain-descent-rigid-seal.md` §8.2 P1; `chain-descent-ir-blindspot-solver.md` §11.3–§11.4a). It has
**no graph model** — it is a fact about a constraint matrix over `ZMod 2` and its row space, exactly what
the doc calls for ("pure F₂/matroid, no graph model").

## What P1 is

Algorithm R recovers the rigid residue's linear system by running the descent oracle (1-WL forcing ≈ F₂
**unit propagation**) and extracting the forced dependencies as rows of a constraint matrix `H`. **P1 is the
soundness of that recovery:** everything the forcing oracle deduces must be a genuine consequence of the row
space `rowspace(H)`, never an artefact.

The subtlety the prototype found (`§11.4a` correction #2): the *unit-prop* closure `cl_up` is **not** the
linear closure `cl_lin`, so the naive "forcing-dependent set `W` ⟹ its indicator `e_W ∈ rowspace`" is
**unsound** (chained `x_a=x_b=x_c` makes `{a,b,c}` forcing-dependent yet `e_a+e_b+e_c ∉ rowspace`); the fix
was to keep only *minimal* circuits. We formalise the **stronger, unconditional** statement that dissolves the
subtlety: every forced variable is backed by an **actual row-space codeword** `c` (not the indicator `e_W`),
with support confined to `insert j S`. Minimal-circuit soundness is then a corollary, and no minimality
bookkeeping is needed — the extracted object is the real codeword.

## The main theorem

`forced_certificate` : if unit propagation forces `j` from the known set `S` (`Forced H S j`), then either
`j ∈ S` already, or there is a codeword `c ∈ rowspace H` with `c j ≠ 0` whose support lies in `insert j S`.

## Scope / what is carried

P1 is *soundness* only. The **completeness** direction ("the extracted circuits *generate* `rowspace(H)`")
is the forcing-model bridge **P2**, carried as a hypothesis (`§8.2`): it holds when the gadget rows are
themselves minimal forcing circuits, a property supplied by the graph model, not by pure F₂.
-/

namespace ChainDescent
namespace ForcingCircuits

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **row space** of a finite set of F₂ constraint vectors — the `ZMod 2`-span of the rows. A "codeword"
is any element; `rowspace H` is the linear closure the forcing oracle must be sound against. -/
def rowspace (H : Finset (ι → ZMod 2)) : Submodule (ZMod 2) (ι → ZMod 2) :=
  Submodule.span (ZMod 2) (H : Set (ι → ZMod 2))

/-- **Unit-propagation forcing (the descent oracle, `cl_up`).** `Forced H S j` means variable `j` is deduced
from the known set `S` by iterated unit propagation over the constraint rows `H`:
* `base` — `j` is already known (`j ∈ S`);
* `step` — some row `v` has `j` in its support (`v j ≠ 0`) and every *other* variable of `v` is itself
  already forced, so `v` fixes `j`'s value.

This is `cl_up`: confluent (order-independent) but **not** a matroid closure in general. -/
inductive Forced (H : Finset (ι → ZMod 2)) (S : Finset ι) : ι → Prop
  | base {j : ι} : j ∈ S → Forced H S j
  | step {v : ι → ZMod 2} {j : ι} : v ∈ H → v j ≠ 0 →
      (∀ k, v k ≠ 0 → k ≠ j → Forced H S k) → Forced H S j

/-- Over `ZMod 2` any two nonzero elements sum to zero (`1 + 1 = 0`) — the cancellation that makes the
forcing certificate's support collapse to `insert j S`. -/
private theorem addTwo_eq_zero : ∀ (a b : ZMod 2), a ≠ 0 → b ≠ 0 → a + b = 0 := by decide

/-- **★ P1 — extraction soundness (the forcing certificate).** If unit propagation forces `j` from `S`, the
deduction is backed by a **genuine row-space codeword**: either `j` was already known, or there is
`c ∈ rowspace H` with `c j ≠ 0` and support inside `insert j S`. The codeword is built by induction on the
forcing derivation — the base row `v`, plus (over F₂) the certificates of every intermediate forced variable,
whose supports cancel. -/
theorem forced_certificate (H : Finset (ι → ZMod 2)) (S : Finset ι) (j : ι) (h : Forced H S j) :
    j ∈ S ∨ ∃ c ∈ rowspace H, c j ≠ 0 ∧ ∀ k, c k ≠ 0 → k = j ∨ k ∈ S := by
  classical
  induction h with
  | base hj => exact Or.inl hj
  | @step v j hv hvj _ ih =>
    by_cases hjS : j ∈ S
    · exact Or.inl hjS
    refine Or.inr ?_
    -- `T` = the intermediate forced variables of `v` (its support, minus `j`, minus the known set `S`)
    set T : Finset ι := Finset.univ.filter (fun k => v k ≠ 0 ∧ k ≠ j ∧ k ∉ S) with hT
    have hTmem : ∀ {k}, k ∈ T ↔ (v k ≠ 0 ∧ k ≠ j ∧ k ∉ S) := by
      intro k; rw [hT, Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
    -- choose a certificate codeword for every intermediate forced variable
    have hex : ∀ k, ∃ c : ι → ZMod 2,
        k ∈ T → (c ∈ rowspace H ∧ c k ≠ 0 ∧ ∀ i, c i ≠ 0 → i = k ∨ i ∈ S) := by
      intro k
      by_cases hk : k ∈ T
      · obtain ⟨hvk, hkj, hkS⟩ := hTmem.mp hk
        rcases ih k hvk hkj with hS | ⟨c, hc1, hc2, hc3⟩
        · exact absurd hS hkS
        · exact ⟨c, fun _ => ⟨hc1, hc2, hc3⟩⟩
      · exact ⟨0, fun h => absurd h hk⟩
    choose cert hcert using hex
    -- the certificate for `j`: the base row plus the intermediate certificates
    refine ⟨v + ∑ k ∈ T, cert k, ?_, ?_, ?_⟩
    · -- membership in the row space
      exact Submodule.add_mem _ (Submodule.subset_span hv)
        (Submodule.sum_mem _ (fun k hk => (hcert k hk).1))
    · -- `c j ≠ 0`: the intermediate certificates avoid `j`, so `c j = v j ≠ 0`
      have hsum : (∑ k ∈ T, cert k) j = 0 := by
        rw [Finset.sum_apply]
        refine Finset.sum_eq_zero (fun k hk => ?_)
        obtain ⟨_, hkj, _⟩ := hTmem.mp hk
        by_contra hne
        rcases (hcert k hk).2.2 j hne with h | h
        · exact hkj h.symm
        · exact hjS h
      simp only [Pi.add_apply, hsum, add_zero]; exact hvj
    · -- support ⊆ `insert j S`: every other variable cancels
      intro k' hk'
      by_contra hcon
      push_neg at hcon
      obtain ⟨hk'j, hk'S⟩ := hcon
      apply hk'
      -- the intermediate certificates contribute only their own diagonal at `k'`
      have hsum : (∑ k ∈ T, cert k) k' = if k' ∈ T then cert k' k' else 0 := by
        rw [Finset.sum_apply]
        by_cases hk'T : k' ∈ T
        · rw [if_pos hk'T]
          refine Finset.sum_eq_single_of_mem k' hk'T (fun k hk hkne => ?_)
          by_contra hne
          rcases (hcert k hk).2.2 k' hne with h | h
          · exact hkne h.symm
          · exact hk'S h
        · rw [if_neg hk'T]
          refine Finset.sum_eq_zero (fun k hk => ?_)
          by_contra hne
          rcases (hcert k hk).2.2 k' hne with h | h
          · exact hk'T (h ▸ hk)
          · exact hk'S h
      simp only [Pi.add_apply, hsum]
      by_cases hk'T : k' ∈ T
      · -- `k' ∈ T`: `v k' ≠ 0` and `cert k' k' ≠ 0`, so `v k' + cert k' k' = 0`
        rw [if_pos hk'T]
        exact addTwo_eq_zero _ _ (hTmem.mp hk'T).1 (hcert k' hk'T).2.1
      · -- `k' ∉ T` with `k' ≠ j`, `k' ∉ S`: forces `v k' = 0`, and no certificate term survives
        rw [if_neg hk'T]
        have hvk'0 : v k' = 0 := by
          by_contra hv0
          exact hk'T (hTmem.mpr ⟨hv0, hk'j, hk'S⟩)
        rw [hvk'0, add_zero]

/-- **P1 soundness, the clean form.** When the forced variable `j` is genuinely new (`j ∉ S`), the forcing is
witnessed by a **row-space codeword** `c` through `j`, supported inside `insert j S`. This is the object the
extraction records — the recovery never manufactures a constraint outside `rowspace H`. -/
theorem certificate_of_forced_notMem (H : Finset (ι → ZMod 2)) (S : Finset ι) (j : ι)
    (hj : j ∉ S) (h : Forced H S j) :
    ∃ c ∈ rowspace H, c j ≠ 0 ∧ ∀ k, c k ≠ 0 → k = j ∨ k ∈ S :=
  (forced_certificate H S j h).resolve_left hj

/-- **Soundness against the row space (matroid form).** Anything unit propagation forces from `S` lies in the
`cl_lin`-closure of `S` witnessed *linearly*: the certificate codeword `c ∈ rowspace H` expresses `j` in terms
of `S`. In particular the extracted certificates all lie in `rowspace H` — `cl_up ⊆ cl_lin` at the level of
witnesses, which is exactly what P3's Smith/rank solve may then consume. (The reverse inclusion — that the
certificates *generate* `rowspace H` — is the P2 forcing-model bridge, carried: it needs the rows to be
minimal forcing circuits, a property of the graph model, not of pure F₂.) -/
theorem certificate_mem_rowspace (H : Finset (ι → ZMod 2)) (S : Finset ι) (j : ι)
    (hj : j ∉ S) (h : Forced H S j) :
    ∃ c, c ∈ rowspace H ∧ c j ≠ 0 :=
  let ⟨c, hc, hcj, _⟩ := certificate_of_forced_notMem H S j hj h
  ⟨c, hc, hcj⟩

end ForcingCircuits
end ChainDescent
