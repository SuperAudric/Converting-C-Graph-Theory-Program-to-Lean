import ChainDescent.TupleWL

/-!
# Covariance of the tuple closure — closing the `roundTS` ↔ standard `k`-WL bridge

(`docs/chain-descent-cao-carrier-falsifiers.md` §6f.5a(α). Read `TupleWL` §4 first — this file
attacks the dead route recorded there.)

## The gap this closes

§6f.4c needed the colour of a tuple to determine the colours of its **reindexings** `x ∘ σ`, found
that it does not follow from `roundT`-stability, and put it **into the round** as `roundTS`. That is
sound but it has a price nobody billed: `roundTS` is *finer* than `roundT`, so it is **not** standard
`k`-WL — while the CFI input the whole refutation rests on ((iii), §6f.3) is a theorem about
**standard `k`-WL**: *base treewidth `≥ k+1` ⟹ the two CFI graphs are `k`-WL indistinguishable.*
A colouring finer than standard `k`-WL is not entitled to that input.

## ⚠⚠ The dead route was not as dead as recorded

§6f.4c rejects *"identify `v = x i` inside the signature by its colour"* because **a tuple whose
`i`-th coordinate differs from all others has the same equality pattern as one with a fresh value
there.** That is correct — for `v = x i`. ★ **But a collapse never needs that case.** A collapse
writes into position `i` the value standing at a *different* position `j`, and `x[i := x j]` with
`i ≠ j` has coordinates `i` and `j` **equal** — which the equality pattern does see.

⟹ `subst_of_stable` below: from `roundT`-stability alone, plus the colouring seeing one equality
`i ≐ j`, the colour of `x` determines the colour of every `x[m := x j]`. The extraction is a
one-element argument: exactly one `v` puts coordinate `i` equal to coordinate `j`, so the signature
has exactly one entry carrying that mark, and matching entries across `x` and `y` identifies it.

## Where this sits in the plan

```
  σ = π ∘ ρ        π a permutation, ρ idempotent (a section of σ; ρ = s ∘ σ)
  ├── π  : CovPerm — §3, by induction ON THE ROUNDS (needs a covariant start)
  ├── ρ  : iterated `subst_of_stable` — ρ fixes `im ρ` pointwise, so the writes never
  │        clobber a position that is later read.  §4, PROVED
  └── ⟹ `stableS_wlT` (§6): `Stable roundTS (wlT init)` ⟹ the chain consumes STANDARD
         `k`-WL and (iii) applies in its literature form.  ✅ ALL THREE PROVED HERE.
```

⚠ `CovPerm` is a statement about the **closure**, not about an arbitrary stable colouring — an
arbitrary `roundT`-stable colouring need not be permutation-covariant, and that is exactly why the
induction is run over the rounds rather than over the fixpoint. `subst_of_stable`, by contrast, needs
only stability, which is why the two halves are proved by different means.

Quality bar: axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`, no fresh `axiom`.
-/

namespace ChainDescent
namespace TupleCov

open ChainDescent.PartitionClosure
open ChainDescent.TupleWL

variable {k L : Nat}

/-! ## 1. Covariance, and what `roundTS`-stability really is -/

/-- The colouring is closed under **reindexing**: equal colours stay equal after any `x ↦ x ∘ σ`,
including non-injective `σ`. -/
def Cov (s : Col (Tup k L)) : Prop :=
  ∀ (σ : Fin k → Fin k) (x y : Tup k L), s x = s y → s (x ∘ σ) = s (y ∘ σ)

/-- Covariance under **permutations** only — the half that a round induction can carry. -/
def CovPerm (s : Col (Tup k L)) : Prop :=
  ∀ (π : Equiv.Perm (Fin k)) (x y : Tup k L), s x = s y → s (x ∘ π) = s (y ∘ π)

theorem covPerm_of_cov {s : Col (Tup k L)} (h : Cov s) : CovPerm s :=
  fun π => h (⇑π)

/-- ★ **`roundTS`-stability is exactly `roundT`-stability plus covariance.** This is the statement
that prices §6f.4c's move: the *only* thing `roundTS` adds over standard `k`-WL is `Cov`. -/
theorem stableS_iff {s : Col (Tup k L)} :
    Stable (roundTS (k := k) (L := L)) s ↔ (Stable (roundT (k := k) (L := L)) s ∧ Cov s) := by
  constructor
  · intro hs
    refine ⟨?_, fun σ x y h => cov_of_stableS hs h σ⟩
    exact stable_iff_tupSig.mpr (fun x y h => sigDet_of_stableS hs x y h)
  · rintro ⟨hst, hcov⟩ x y h
    refine (roundTS_eq_iff s x y).mpr ⟨h, ?_, stable_iff_tupSig.mp hst x y h⟩
    exact (subEnc_eq_iff s x y).mpr (fun σ => hcov σ x y h)

/-! ## 2. ★★★ The substitution lemma — from `roundT`-stability alone -/

/-- The colouring sees whether coordinates `i` and `j` coincide. For the standard start colouring
(the atomic type of a tuple) this holds for every pair. -/
def SeesEq (s : Col (Tup k L)) (i j : Fin k) : Prop :=
  PartitionClosure.Refines s (fun z : Tup k L => if z i = z j then 1 else 0)

/-- **★★★ THE EXTRACTION LEMMA — and it retracts `TupleWL` §4's dead route for `i ≠ j`.**

If `s` is `roundT`-stable and sees the equality `i ≐ j` for some `i ≠ j`, then the colour of `x`
determines the colour of **every** substituted tuple `x[m := x j]`.

★ The proof is the rescue §6f.4c thought was unavailable: among all `v`, exactly one — namely `x j` —
makes coordinate `i` of `x[i := v]` equal to coordinate `j`, so that entry of the signature is marked
and can be matched against `y`'s. ⚠ The rejected case was `v = x i`, which a **collapse never needs**:
a collapse always reads from a coordinate other than the one it writes. -/
theorem subst_of_stable {s : Col (Tup k L)}
    (hs : Stable (roundT (k := k) (L := L)) s) {i j : Fin k} (hij : i ≠ j)
    (hsee : SeesEq s i j) {x y : Tup k L} (h : s x = s y) (m : Fin k) :
    s (Function.update x m (x j)) = s (Function.update y m (y j)) := by
  obtain ⟨d, hd⟩ := exists_factor hsee
  -- The marker: `d (s (x[i := v])) = 1` holds exactly when `v = x j`.
  have hmark : ∀ (z : Tup k L) (v : Fin L),
      d (s (Function.update z i v)) = 1 ↔ v = z j := by
    intro z v
    rw [hd]
    rw [Function.update_self, Function.update_of_ne (Ne.symm hij)]
    by_cases hv : v = z j
    · simp [hv]
    · simp [hv]
  -- `x`'s marked signature entry lands in `y`'s signature.
  have hmem : (fun m => s (Function.update x m (x j))) ∈ tupSig s y := by
    rw [← stable_iff_tupSig.mp hs x y h]
    exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val (x j))
  obtain ⟨v, -, hv⟩ := Multiset.mem_map.mp hmem
  have hvi : d (s (Function.update y i v)) = 1 := by
    rw [congrFun hv i, (hmark x (x j)).mpr rfl]
  have : v = y j := (hmark y v).mp hvi
  subst this
  exact (congrFun hv m).symm

/-! ## 3. Covariance under permutations — by induction on the rounds -/

/-- ⚠ Unlike §2 this is **not** available from stability: it is proved by carrying the property
through `roundT`, so it applies to a closure whose start colouring already has it. -/
theorem covPerm_roundT {c : Col (Tup k L)} (hc : CovPerm c) : CovPerm (roundT c) := by
  intro π x y h
  obtain ⟨hcc, hsig⟩ := (roundT_eq_iff c x y).mp h
  obtain ⟨f, hf⟩ :=
    exists_factor (c := c) (d := fun z : Tup k L => c (z ∘ π)) (fun z z' hz => hc π z z' hz)
  have key : ∀ z : Tup k L,
      tupSig c (z ∘ π) = (tupSig c z).map (fun w => fun i => f (w (π i))) := by
    intro z
    unfold tupSig
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl (fun v _ => ?_)
    funext i
    show c (Function.update (z ∘ ⇑π) i v) = f (c (Function.update z (π i) v))
    rw [hf]
    congr 1
    funext m
    by_cases hm : m = i
    · subst hm
      show (Function.update (z ∘ ⇑π) m v) m = (Function.update z (π m) v) (π m)
      rw [Function.update_self, Function.update_self]
    · have hpm : π m ≠ π i := fun hcon => hm (π.injective hcon)
      show (Function.update (z ∘ ⇑π) i v) m = (Function.update z (π i) v) (π m)
      rw [Function.update_of_ne hm, Function.update_of_ne hpm]
      rfl
  exact (roundT_eq_iff c (x ∘ ⇑π) (y ∘ ⇑π)).mpr ⟨hc π x y hcc, by rw [key x, key y, hsig]⟩

theorem covPerm_iterate : ∀ (n : Nat) {c : Col (Tup k L)}, CovPerm c → CovPerm (roundT^[n] c)
  | 0, _, hc => hc
  | n + 1, c, hc => by
      rw [Function.iterate_succ_apply]
      exact covPerm_iterate n (covPerm_roundT hc)

/-- **★ The standard `k`-WL closure of a permutation-covariant start is permutation-covariant.** -/
theorem covPerm_wlT {c : Col (Tup k L)} (hc : CovPerm c) : CovPerm (wlT c) :=
  covPerm_iterate _ hc

/-! ## 4. Covariance under an **idempotent** reindex — iterated substitution -/

/-- Every coordinate has a partner it can be marked against. ⚠ This is what carries the `k ≥ 2`
requirement; at `k ≤ 1` every reindex is the identity and nothing is needed. -/
def SeesEqAll (s : Col (Tup k L)) : Prop := ∀ j : Fin k, ∃ i, i ≠ j ∧ SeesEq s i j

/-- `ρ` on `S`, the identity off it — the partial reindex the induction walks along. -/
def part (ρ : Fin k → Fin k) (S : Finset (Fin k)) (i : Fin k) : Fin k :=
  if i ∈ S then ρ i else i

theorem part_empty (ρ : Fin k → Fin k) : part ρ ∅ = id := by
  funext i; simp [part]

theorem part_univ (ρ : Fin k → Fin k) : part ρ Finset.univ = ρ := by
  funext i; simp [part]

/-- ★ **One step of the walk is a single substitution.** This is where idempotence pays: the value
being read sits at `ρ a`, which `part ρ S` fixes whether or not `ρ a ∈ S`, so the write never
clobbers a position that a later step reads. -/
theorem comp_part_insert {ρ : Fin k → Fin k} (hρ : ∀ i, ρ (ρ i) = ρ i)
    (x : Tup k L) {a : Fin k} {S : Finset (Fin k)} :
    x ∘ part ρ (insert a S) = Function.update (x ∘ part ρ S) a ((x ∘ part ρ S) (ρ a)) := by
  funext m
  by_cases hm : m = a
  · subst hm
    rw [Function.update_self]
    show x (part ρ (insert m S) m) = x (part ρ S (ρ m))
    have h1 : part ρ (insert m S) m = ρ m := by simp [part]
    have h2 : part ρ S (ρ m) = ρ m := by
      unfold part; split
      · exact hρ m
      · rfl
    rw [h1, h2]
  · rw [Function.update_of_ne hm]
    show x (part ρ (insert a S) m) = x (part ρ S m)
    congr 1
    unfold part
    simp [Finset.mem_insert, hm]

/-- **★★ Covariance under any idempotent reindex, from `roundT`-stability alone.** -/
theorem cov_idem_of_stable {s : Col (Tup k L)}
    (hs : Stable (roundT (k := k) (L := L)) s) (hsee : SeesEqAll s)
    {ρ : Fin k → Fin k} (hρ : ∀ i, ρ (ρ i) = ρ i) {x y : Tup k L} (h : s x = s y) :
    s (x ∘ ρ) = s (y ∘ ρ) := by
  have main : ∀ S : Finset (Fin k), s (x ∘ part ρ S) = s (y ∘ part ρ S) := by
    intro S
    induction S using Finset.induction_on with
    | empty => rw [part_empty]; exact h
    | insert a S _ ih =>
        obtain ⟨i, hij, hsee'⟩ := hsee (ρ a)
        rw [comp_part_insert hρ x, comp_part_insert hρ y]
        exact subst_of_stable hs hij hsee' ih a
  have hmain := main Finset.univ
  rwa [part_univ] at hmain

/-! ## 5. The decomposition `σ = π ∘ ρ` — pure finite combinatorics, no colouring in sight -/

section Decomp

variable {k : Nat}

open Classical in
/-- A section of `σ` over its image. -/
noncomputable def sect (σ : Fin k → Fin k) (a : Fin k) : Fin k :=
  if h : ∃ i, σ i = a then h.choose else a

theorem sect_spec (σ : Fin k → Fin k) (i : Fin k) : σ (sect σ (σ i)) = σ i := by
  have h : ∃ j, σ j = σ i := ⟨i, rfl⟩
  simp only [sect, dif_pos h]
  exact h.choose_spec

/-- ★ The idempotent factor of `σ`. -/
noncomputable def idem (σ : Fin k → Fin k) : Fin k → Fin k := fun i => sect σ (σ i)

theorem idem_idem (σ : Fin k → Fin k) (i : Fin k) : idem σ (idem σ i) = idem σ i := by
  exact congrArg (sect σ) (sect_spec σ i)

open Classical in
/-- **★★ Every reindex factors as a permutation after an idempotent.** -/
theorem exists_perm_comp_idem (σ : Fin k → Fin k) :
    ∃ π : Equiv.Perm (Fin k), ∀ i, π (idem σ i) = σ i := by
  classical
  set q : Fin k → Prop := fun a => ∃ j, σ j = a with hq
  set p : Fin k → Prop := fun i => ∃ a, q a ∧ sect σ a = i with hp
  have hσsect : ∀ a, q a → σ (sect σ a) = a := by
    rintro a ⟨j, rfl⟩
    exact sect_spec σ j
  let e : {a // q a} ≃ {i // p i} :=
    { toFun := fun a => ⟨sect σ a.1, ⟨a.1, a.2, rfl⟩⟩
      invFun := fun i => ⟨σ i.1, ⟨i.1, rfl⟩⟩
      left_inv := by rintro ⟨a, ha⟩; exact Subtype.ext (hσsect a ha)
      right_inv := by
        rintro ⟨i, a, ha, rfl⟩
        exact Subtype.ext (congrArg (sect σ) (hσsect a ha)) }
  have hev : ∀ (a : Fin k) (ha : q a), ((e ⟨a, ha⟩ : {i // p i}) : Fin k) = sect σ a :=
    fun _ _ => rfl
  refine ⟨(e.extendSubtype).symm, fun i => ?_⟩
  have hmem : q (σ i) := ⟨i, rfl⟩
  have happ : e.extendSubtype (σ i) = idem σ i :=
    (Equiv.extendSubtype_apply_of_mem e (σ i) hmem).trans (hev (σ i) hmem)
  rw [← happ, Equiv.symm_apply_apply]

end Decomp

/-! ## 6. ★★★ The bridge: `roundTS` adds nothing to the standard closure -/

/-- **★★★ Full covariance, from `roundT`-stability + the equality marker + permutation covariance.**
§2 (collapses) and §3 (permutations) meet here through §5's factorization. -/
theorem cov_of_covPerm {s : Col (Tup k L)}
    (hs : Stable (roundT (k := k) (L := L)) s) (hsee : SeesEqAll s) (hperm : CovPerm s) : Cov s := by
  intro σ x y h
  obtain ⟨π, hπ⟩ := exists_perm_comp_idem σ
  have hfun : ∀ z : Tup k L, z ∘ σ = (z ∘ ⇑π) ∘ idem σ := by
    intro z; funext i; show z (σ i) = z (π (idem σ i)); rw [hπ]
  rw [hfun x, hfun y]
  exact cov_idem_of_stable hs hsee (idem_idem σ) (hperm π x y h)

/-- **★★★ THE BRIDGE — the standard `k`-WL closure is already `roundTS`-stable.**

⟹ `roundTS` buys nothing over standard `k`-WL on a closure, so `FrameTransfer`'s chain is entitled
to the CFI input (iii) in its literature form (*base treewidth `≥ k+1` ⟹ `k`-WL indistinguishable*).
⚠ The two side conditions are exactly what the standard atomic start colouring supplies. -/
theorem stableS_wlT {c : Col (Tup k L)} (hc : CovPerm c) (hsee : SeesEqAll (wlT c)) :
    Stable (roundTS (k := k) (L := L)) (wlT c) := by
  have hst : Stable (roundT (k := k) (L := L)) (wlT c) := wl_stable isRound_roundT c
  exact stableS_iff.mpr ⟨hst, cov_of_covPerm hst hsee (covPerm_wlT hc)⟩

/-! ## 7. ▶ WHAT IS LEFT ON (α) — and it is no longer the bridge

✅ **The internal bridge is closed.** `stableS_wlT`: the standard `k`-WL closure is already
`roundTS`-stable, so `roundTS` adds **nothing** on a closure and `FrameTransfer`'s consumer is
entitled to the CFI input in its standard form. ⟹ §6f.4c's *"put covariance in the round"* was a
sound but **unnecessary** detour, and `TupleWL` §4's dead-route note is retracted for `i ≠ j`.

▶ **Two side conditions remain, both instantiation rather than mathematics:**
1. `CovPerm c` for the start colouring — free for the atomic type of a tuple, which is covariant by
   construction; it has to be *written* for whichever start `FrameTransfer` ends up using.
2. `SeesEqAll (wlT c)` — the closure sees each equality `i ≐ j`; likewise free from the atomic start,
   since the closure refines it. ⚠ It carries the `k ≥ 2` requirement (`∃ i, i ≠ j`), which is
   harmless at `k = 6` and vacuous at `k ≤ 1`.

⛔ **What this does NOT do.** It does not formalize (iii) — *base treewidth `≥ k+1` ⟹ the two CFI
graphs are `k`-WL indistinguishable* is still literature and still a named hypothesis. What changed
is that the hypothesis may now be stated about **standard `k`-WL**, which is the form the theorem
actually has, instead of about a strictly finer round nobody has a citation for. -/

end TupleCov
end ChainDescent
