import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring
/-!
# B-M3 bridge — abstract `VO⁻₄(3)` restricted count = kernel-fast `Nat`-predicate count over `Fin 81`.

Bridges the Lemma-B count object (over `Fin 4 → ZMod 3`, `Pi.fintype` — ~321ms/count) to a pure-`Nat`-predicate
count over `Finset (Fin 81)` (`Function.Injective` directly decidable, ~20s), transported along the **computable**
digit equiv `encV = finFunctionFinEquiv` (NOT the opaque `affineE`). Arithmetic core: `co (encV a).val i = (a i).val`
(`finFunctionFinEquiv_symm_apply_val`), ZMod-3 leaf identities by `decide`, `%3` normalization by `omega`.
-/
namespace BM3Bridge

abbrev encV : (Fin 4 → ZMod 3) ≃ Fin (3 ^ 4) := finFunctionFinEquiv

/-- concrete VO⁻₄(3) quadratic form (unbundled; bundled at ASM). -/
def Qvo (y : Fin 4 → ZMod 3) : ZMod 3 := y 0 * y 1 + y 2 * y 2 + y 3 * y 3

/-- `co n i` = `i`-th base-3 digit of `n` (index `Fin 4`, matching `encV`). -/
def co (n : Nat) (i : Fin 4) : Nat := (n / 3 ^ (i : ℕ)) % 3
def Qc (n : Nat) : Nat := (co n 0 * co n 1 + co n 2 * co n 2 + co n 3 * co n 3) % 3
def Qsh (y u tc : Nat) : Nat :=
  let c0 := (co y 0 + co u 0 + (3 - co tc 0)) % 3
  let c1 := (co y 1 + co u 1 + (3 - co tc 1)) % 3
  let c2 := (co y 2 + co u 2 + (3 - co tc 2)) % 3
  let c3 := (co y 3 + co u 3 + (3 - co tc 3)) % 3
  (c0 * c1 + c2 * c2 + c3 * c3) % 3

/-- **Foundational:** the Nat digit-decode of the code recovers the coordinate's `val`. -/
lemma co_encV (a : Fin 4 → ZMod 3) (i : Fin 4) : co (encV a).val i = (a i).val := by
  rw [co, ← finFunctionFinEquiv_symm_apply_val (encV a) i,
    show finFunctionFinEquiv.symm (encV a) = a from finFunctionFinEquiv.symm_apply_apply a]
  rfl

/-- ZMod-3 leaf identities (finite ⟹ `decide`). -/
lemma val_zero (x : ZMod 3) : x = 0 ↔ x.val = 0 := by revert x; decide
lemma coord_id (x z w : ZMod 3) :
    (x - z + w).val = (x.val + w.val + (3 - z.val)) % 3 := by revert x z w; decide

/-- `(Qvo w).val` as a flat `Nat` polynomial mod 3 (products as atoms; `%3` nesting by `omega`). -/
lemma QvoVal (w : Fin 4 → ZMod 3) :
    (Qvo w).val
      = ((w 0).val * (w 1).val + (w 2).val * (w 2).val + (w 3).val * (w 3).val) % 3 := by
  rw [Qvo, ZMod.val_add, ZMod.val_add, ZMod.val_mul, ZMod.val_mul, ZMod.val_mul]
  omega

/-- `Qc` of a code = `(Qvo ·).val` of the decoded vector. -/
lemma Qc_encV (a : Fin 4 → ZMod 3) : Qc (encV a).val = (Qvo a).val := by
  rw [Qc, QvoVal]; simp only [co_encV]

/-- coordinatewise: the shifted coordinate's `val` in `Nat` form. -/
lemma coord_sub (y b v : Fin 4 → ZMod 3) (i : Fin 4) :
    ((y - (b - v)) i).val = ((y i).val + (v i).val + (3 - (b i).val)) % 3 := by
  rw [Pi.sub_apply, Pi.sub_apply,
    show y i - (b i - v i) = (y i) - (b i) + (v i) from by ring, coord_id]

/-- `Qsh` of codes = `(Qvo (y − (b − v))).val` (the shifted incidence value). -/
lemma Qsh_encV (y v b : Fin 4 → ZMod 3) :
    Qsh (encV y).val (encV v).val (encV b).val = (Qvo (y - (b - v))).val := by
  rw [Qsh, QvoVal]
  simp only [co_encV]
  rw [← coord_sub y b v 0, ← coord_sub y b v 1, ← coord_sub y b v 2, ← coord_sub y b v 3]

/-- `encV` sends the zero vector to the zero code. -/
lemma encV_zero : encV (0 : Fin 4 → ZMod 3) = 0 := by decide

/-- the code is zero iff the vector is zero. -/
lemma encV_val_zero (a : Fin 4 → ZMod 3) : (encV a).val = 0 ↔ a = 0 := by
  rw [Fin.val_eq_zero_iff, ← encV_zero, encV.apply_eq_iff_eq]

/-- the kernel-fast count: pure `Nat` predicate over `Finset (Fin 81)`. -/
def restrictedF (u t1 t2 : Nat) : Nat :=
  (Finset.univ.filter (fun n : Fin (3 ^ 4) =>
    n.val ≠ 0 ∧ Qc n.val = 0 ∧ Qsh n.val u t1 = 0 ∧ Qsh n.val u t2 = 0)).card

/-- **THE BRIDGE** — the abstract `VO⁻₄(3)` restricted count (over `Fin 4 → ZMod 3`, the Lemma-B object) equals
the `Nat`-predicate count over `Fin 81` at the codes of `v, b₁, b₂`. -/
theorem restricted_bridge (v b₁ b₂ : Fin 4 → ZMod 3) :
    (Finset.univ.filter (fun y : Fin 4 → ZMod 3 =>
        y ≠ 0 ∧ Qvo y = 0 ∧ Qvo (y - (b₁ - v)) = 0 ∧ Qvo (y - (b₂ - v)) = 0)).card
      = restrictedF (encV v).val (encV b₁).val (encV b₂).val := by
  rw [restrictedF]
  refine Finset.card_nbij' (fun y => encV y) (fun n => encV.symm n) ?_ ?_ ?_ ?_
  · intro y hy
    rw [Finset.mem_coe, Finset.mem_filter] at hy
    rw [Finset.mem_coe, Finset.mem_filter]
    obtain ⟨_, h0, hQ, h1, h2⟩ := hy
    refine ⟨Finset.mem_univ _, ?_, ?_, ?_, ?_⟩
    · rw [Ne, encV_val_zero]; exact h0
    · rw [Qc_encV, ← val_zero]; exact hQ
    · rw [Qsh_encV, ← val_zero]; exact h1
    · rw [Qsh_encV, ← val_zero]; exact h2
  · intro n hn
    rw [Finset.mem_coe, Finset.mem_filter] at hn
    rw [Finset.mem_coe, Finset.mem_filter]
    obtain ⟨_, h0, hQ, h1, h2⟩ := hn
    refine ⟨Finset.mem_univ _, ?_, ?_, ?_, ?_⟩
    · rw [Ne, ← encV_val_zero, Equiv.apply_symm_apply]; exact h0
    · rw [val_zero, ← Qc_encV, Equiv.apply_symm_apply]; exact hQ
    · rw [val_zero, ← Qsh_encV, Equiv.apply_symm_apply]; exact h1
    · rw [val_zero, ← Qsh_encV, Equiv.apply_symm_apply]; exact h2
  · intro y _; exact encV.symm_apply_apply y
  · intro n _; exact encV.apply_symm_apply n

/-- the injective 6-pair separating family (T₉ nat-codes), from `/tmp/bm3_lean_targets.py`. -/
def fam : List (Nat × Nat) := [(0, 9), (27, 10), (1, 3), (27, 70), (9, 54), (1, 40)]
def sigF (u : Fin (3 ^ 4)) : List Nat := fam.map (fun p => restrictedF u.val p.1 p.2)

/-- **THE DECIDED INJECTIVITY** (kernel `decide`, ~20s, no `native_decide`). -/
theorem sigF_injective : Function.Injective sigF := by decide

end BM3Bridge

#print axioms BM3Bridge.restricted_bridge
#print axioms BM3Bridge.sigF_injective
