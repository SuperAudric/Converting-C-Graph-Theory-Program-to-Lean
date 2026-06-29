# No rigid-Cameron — the Lean attack (Route B: non-abelian symmetry is not hideable)

> **What this is.** The Lean build plan for the **rigid-Cameron** target — proving that a *rigid* graph cannot carry a
> hidden **Cameron** (large non-abelian) symmetry, which **closes the seal's "or Cameron" escape**. It is the
> *formalization* companion to the strategy doc [`chain-descent-cameron-entanglement.md`](./chain-descent-cameron-entanglement.md)
> (the problem statement + the full attack menu + the family battery); this doc carries the **Lean** pieces that are
> already built and the staged plan to turn them into a discharge of (a formalizable fragment of) **Route B** there.
> Provenance: the `NonAbelianCfiProbe` arc (memory `project_nonabelian_cfi_witness_2026-06-28`), the Phase-0 cores
> (`project_wl_visibility_lean_2026-06-28`), cameron-entanglement §3–§4.
>
> **Filename note.** This file was formerly "WL-visibility of group structure" (a 1-WL-dichotomy formalization). It was
> **retargeted 2026-06-29** to the direct rigid-Cameron attack — the dichotomy theorems are now *lemmas*, not the goal.
> The path is kept so existing cross-references resolve; rename to `chain-descent-rigid-cameron-attack.md` is optional.

---

## STATUS (read first)

**Retargeted 2026-06-29.** The previous target ("formalize the 1-WL-visibility dichotomy: S₃ ≡ Z₆, commutator-gadget
visible") was the **mechanism**, not a result the project needs in its own right. The dichotomy certifies *why* a
construction hides or exposes group structure — which is exactly what a **Route-B** (no-rigid-Cameron) attack consumes.
So this doc now plans the attack, with the dichotomy demoted to its load-bearing lemmas.

**Why this is on the critical path** (corrected understanding, 2026-06-29). "No rigid-Cameron" closes the rigid seal's
**"or Cameron"** escape (cameron-entanglement §3): a rigid graph has `b(Aut)=0`, Cameron's hardness *is* `b(Aut)`
(gap ≈ 0), so a rigid graph cannot be Cameron-hard — *unless* a Cameron symmetry can be **hidden** (carried by the
WL-closure, non-schurian, not as a graph automorphism). The CFI/multipede shows the **abelian** analogue of hidden
symmetry is real (the cycle-space gauge). **Route B = prove the non-abelian analogue cannot exist** ⟹ no hidden
Cameron ⟹ "or Cameron" deleted. This is the **Cameron facet** of the seal's flag floor — distinct from the
bounded-WL-dim core (the *poly* facet); see cameron-entanglement §2's opposite-corners.

**Phase 0 cores — built, axiom-clean, repositioned (not rebuilt)** (`ChainDescent/ScratchWLVisibility.lean`,
`[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`):
- **`product_coord_regular`** — the **hideability mechanism**. The product relation `g₁·…·g_d = 1` is
  coordinate-regular (a perfect quasigroup), so 1-WL counts depend only on `|Γ|`, *not* on whether Γ is abelian. This is
  *how* an abelian gauge hides — and the reason the non-abelian content of a group-CFI is **invisible to refinement**.
- **`commDeg_const_iff_comm`** — the **visibility mechanism**. The commuting-degree varies ⟺ Γ is non-abelian, so a
  commutator-type relation **exposes** non-abelian structure. Non-abelian content is hideable *only* in
  coordinate-regular relations; the moment a relation sees commutativity, it is 1-WL-visible.
- **`linear_eq_unique` / `product_fix_two_indep`** (added 2026-06-29) — the **degree-2 kernel** for the `≥2`-WL
  altitude. Hidden symmetry lives in the WL-closure (the coherent configuration, `≥2`-WL counting *pairs*), not in
  1-WL — at 1-WL these regular gadgets are stuck for trivial regularity reasons, independent of the hiding question.
  The 2-WL count on the minimal `d=3` gadget fixes *two* coordinates, leaving a linear equation `u·z·w = 1` in the
  third with a **unique** solution (`z = u⁻¹·w⁻¹`): count `= 1`, `Γ`-blind. This is `product_coord_regular` one degree
  up — the same noncommutative-quasigroup algebra — so the load-bearing `≥2`-WL rung (R1′) is reachable via the cores,
  not "high/open". (General-`d` aggregate `|Γ|^{d−2}` = a `List.ofFn`-product counting wrapper; deferred to R2.)

**Phase 1 DONE (2026-06-29, axiom-clean).** `ChainDescent/WLGeneric.lean` re-states the 1-WL primitives
(`signature`, `sigKey_eq_iff`, `refineStep`, `refineStep_iff`, `warmRefine`, `samePartition`) over an arbitrary
`[Fintype V] [DecidableEq V]`, reusing the top-level `POE`/`encTuple` (re-deriving the two `private` injectivity
lemmas locally). The canonizer's `Fin n` invariants are untouched. `refineStep_iff` — the only lemma the rungs
consume — is `[propext, Classical.choice, Quot.sound]`. (`lake env lean`, not in `build.sh`.)

**Altitude decision (2026-06-29, user-approved): algebra-core-first, defer the refinement altitude.** R1a-at-1-WL is
correct but certifies only 1-WL-mediated hiding (the weak rung); the load-bearing statement is `≥2`-WL. Rather than
commit Phase 2 to either altitude blind, land the degree-2 kernel (above, done) — which feeds *both* a multi-`d` 1-WL
R1a and the 2-WL statement — then choose the graph/refinement altitude with the foundation in hand.

**The plan (rungs, increasing difficulty / decreasing reachability):**
- **R1 — the group-CFI carries no hidden non-abelian symmetry** (one rung of the family battery; reachable). Its
  non-abelian structure is *visible-or-killed, never hidden*. Cores are the load-bearing lemmas. **Next.**
- **R2 — the characterization** "a single-relation gadget is 1-WL-hideable ⟺ its relation is coordinate-regular, and
  coordinate-regular content is abelian-equivalent." Generalizes R1 off the product gadget.
- **R3 — Route B general** ("the only hideable symmetry is abelian") — GI-adjacent; the *target*, not the near-term.

Quality bar: axiom-clean, no `sorry` / no fresh `axiom` / `native_decide` banned; full build green when ported.

---

## 1. The target, precisely

From cameron-entanglement §1 (read it for the full statement):

> **(No rigid-Cameron.)** A rigid graph cannot carry a hidden Cameron symmetry — equivalently, a Cameron's
> (non-abelian) symmetry is **non-separable** from the structure that makes it hard.

It splits (cameron-entanglement §1):
- **(a) schurian / visible** — the Cameron group sits in `Aut(G)`. *Trivially impossible* for rigid `G`. No work.
- **(b) non-schurian / hidden** — `G` is rigid, but its **WL-closure** (the coherent configuration refinement computes)
  is Cameron-like, its symmetry *combinatorial*, not a graph automorphism. **This is the whole problem.** The CFI gauge
  is the *abelian* instance of (b); the question is whether a **non-abelian** instance exists.

**What the cores buy.** The natural way to *try* to build a non-abelian instance of (b) is the **group-CFI**: take the
CFI/multipede and replace the F₂ gauge with an arbitrary finite group Γ (gadget relation `g₁·…·g_d = 1`). The
`NonAbelianCfiProbe` arc showed this attempt **fails** — its WL view depends only on `|Γ|`, so the non-abelian
structure never becomes a hidden symmetry. The Phase-0 cores are the *algebra* of that failure. R1 turns the probe's
empirical finding into a Lean theorem; R2/R3 generalize the mechanism toward the real Route B.

---

## 2. The pieces that are available (Phase 0) — repositioned

File `ChainDescent/ScratchWLVisibility.lean`, namespace `WLVis`, all axiom-clean. (Build/lemma detail unchanged from the
prior version; only the *role* is reframed.)

**Hideability mechanism — `product_coord_regular`.**
`product_coord_regular (a : G) : Fintype.card {p : G × G // a * p.1 * p.2 = 1} = Fintype.card G` (+ `_indep`). Fixing
one coordinate to *any* value leaves `|G|` completions, independent of the value **and of commutativity**. Proof: the
explicit `Equiv` `(y,z) ↦ y`, inverse `y ↦ (y,(a*y)⁻¹)` (`eq_inv_of_mul_eq_one_right`, `mul_inv_cancel`). *Role in the
attack:* this is exactly why refinement on a group-CFI cannot separate any segment by group structure — the WL-closure
of the group-CFI over Γ is the **same coherent configuration** as for any group of order `|Γ|`, i.e. **abelian-equivalent**.
A hidden symmetry lives in that closure; if the closure is abelian-equivalent, the only symmetry it can hide is too.

**Visibility mechanism — `commDeg` / `commDeg_const_iff_comm`.**
`commDeg g := Fintype.card {h // g*h=h*g}`; constant `= |G|` ⟺ Γ abelian (`commDeg_const_of_comm` /
`commDeg_nonconst_of_noncomm`, via `Equiv.subtypeUnivEquiv` / `Fintype.card_subtype_lt`). *Role:* the contrapositive of
hideability — non-abelian structure **is** 1-WL-visible *when the relation exposes commutativity*. So a construction
hides non-abelian structure **only** by using coordinate-regular (commutativity-blind) relations; the moment it doesn't,
rigidity kills the now-visible symmetry. This is the "non-abelian ⟹ visible ⟹ killed by rigidity" half of Route B.

> Gotchas (carry forward): subtypes need `[DecidableEq G]` for `Fintype`; spell `{h // g*h=h*g}`, not opaque `Commute`;
> annotate `(1 : G)` in statements (bare `1` defaults to ℕ). `push Not` (not deprecated `push_neg`).

---

## 3. R1 — the group-CFI carries no hidden non-abelian symmetry

**The claim (the first family-battery rung).** The group-CFI over Γ is **not** a rigid-Cameron: its non-abelian
structure is **visible** (an actual automorphism, when present) or **killed** (by rigidification), never **hidden** in
the WL-closure. Concretely, two statements that together rule out the construction:

- **R1a (hidden ⟹ abelian-equivalent, 1-WL level).** The 1-WL closure (color refinement) of the group-CFI over Γ is
  group-blind beyond `|Γ|` — `samePartition (warmRefine …) initial` holds for the segment colouring, for every Γ,
  because every value-vertex's signature is the coordinate-regular count (`product_coord_regular`). Hence the closure is
  the same for Γ and any Γ′ with `|Γ|=|Γ′|`; in particular the same as for the *abelian* Z_{|Γ|}. **Any symmetry the
  1-WL closure carries is abelian-equivalent** — there is no hidden *non-abelian* content at the refinement level.
- **R1b (the genuine Γ-symmetry is visible, and rigidity kills it).** The un-anchored group-CFI has `Aut = Γ` acting as
  the global gauge — for non-abelian Γ a real, **visible**, non-abelian automorphism group of order `|Γ|` (schurian,
  consumed by the cascade). Anchoring one segment yields `Aut = 1` (rigid): the non-abelian content survives only as a
  fixed CSP relation with **no** automorphism realizing it. So the non-abelian symmetry is never simultaneously
  *large* and *hidden*.

**Why this is the right first target.** It is *one* Cameron family (the group-CFI) shown to have no rigid version —
exactly the per-family shape cameron-entanglement §4 prescribes — and it is the family the project's own probe flagged
as the most natural non-abelian-CFI candidate. Ruling it out removes the most plausible counterexample to no-rigid-Cameron.

**Honest scope of R1.** The *formal* cores are **1-WL**; R1a as stated is a 1-WL statement. The probe found the
blindness at full IR-depth `b_WL` (S₃ ≡ Z₆ in depth, not just one round), which is the statement rigid-Cameron really
wants. Strengthening R1a from 1-WL to `b_WL`/`k`-WL is **R1′** (harder; the same altitude gap noted in §6). R1 at 1-WL
is the right first deliverable: it is what the cores reach cleanly and it already rules out 1-WL-mediated hiding.

---

## 4. R2 / R3 — generalizing the mechanism

- **R2 — the hideability characterization.** Abstract over a relation `R ⊆ Γ^d` with a predicate `CoordRegular R` (any
  `d−1` coordinates plus a value of the last leave a completion count independent of choices). Prove: a single-relation
  gadget is **1-WL-hideable ⟺ `CoordRegular R`**, and coordinate-regular content is **abelian-equivalent** (1-WL sees
  only the quasigroup, hence only `|Γ|`). The product relation (hideable, `product_coord_regular`) and the commutator
  relation (visible, `commDeg`) are the ± instances. This lifts R1 off the specific product gadget and is the clean
  general statement of "what can hide."
- **R3 — Route B in general** ("the only hideable symmetry a graph can carry is abelian"). Characterize *hideable
  symmetry* across all constructions and show it is abelian (cameron-entanglement §4 Route B). **GI-adjacent** — the
  target of the whole line, not a near-term build. R2 is the formalizable down-payment on it.

---

## 5. The complementary angle (Route C / gap = 0) — note, not this doc's build

cameron-entanglement §3–§4 also give a **construction-free** route: a rigid graph has `b(Aut)=0`; a hidden Cameron
would force `b_WL > 0` with all of it structural (gap), but Cameron's hardness is *symmetry* (gap ≈ 0) — a
contradiction. This is conceptually cleaner and family-uniform, but the Phase-0 cores **do not serve it** (it is about
`b(Aut)` vs `b_WL`, not about coordinate-regularity of a gadget). Worth keeping as the parallel angle: if R2 stalls, the
`b(Aut)`/gap argument is the other way in. Do **not** duplicate it here — it belongs in cameron-entanglement; this doc
owns the **mechanism / construction-battery** side that the cores support.

---

## 6. Tools, gaps, sequencing

**1-WL engine (reuse) — top-level `ChainDescent.lean`:** `signature` (the neighbour `(colour, adj, POE)` multiset —
the object whose Γ-(in)dependence is the proof), `refineStep_iff` (same refined colour ⟺ same old colour ∧ same
signature — the splitting lever: equal ⟹ hidden, unequal ⟹ visible), `warmRefine`, `samePartition`. Defined on `Fin n`.

**Gaps, ordered:**
1. **Generalize 1-WL to `[Fintype V] [DecidableEq V]`** (settled decision; do in a new `ChainDescent/WLGeneric.lean`,
   leaving the canonizer's `Fin n` invariants untouched). Mechanical: `signature` already sums over `Finset.univ`;
   iteration count `n ↦ Fintype.card V`; re-derive `refineStep_iff` generically (the only lemma the rungs need). The
   `warmRefine` termination lemma is *not* on the critical path for R1a (a "stuck at fixpoint" statement follows from
   `refineStep_iff` directly).
2. **Build the group-CFI graph** (R1): vertices `= (Σ _ : Fin d, Γ) ⊕ {t : Fin d → Γ // ∏ t = 1}` (segments ⊕ tuples),
   `adj` = incidence `tuple t — (i, t i)`; anchoring = pin one segment's colours. R1a's signature-is-coordinate-regular
   step plugs `product_coord_regular` into `refineStep_iff`. The minimal single-gadget form suffices; the full
   multipede over a base graph is an optional later generalization (only if the literal CFI object is wanted).
3. **Signature ↔ count bridge** (R1a): relate `signature (i,a)` to the gadget-incidence count = the coordinate-regular
   count; `Multiset.count` / `Finset.card` rewriting. The load-bearing lemma.
4. **Cross-graph 1-WL-equivalence** (R1a's "same closure for Γ, Γ′"): a small `WLEquiv` def = equality of the multiset
   of stable-colour class sizes. Keep minimal.
5. **The `Aut`/visibility side of R1b**: model `Aut(group-CFI)` and the anchoring that trivializes it. This is the
   genuinely new infra vs. the old plan — it connects the gadget to a permutation-automorphism statement (reuse
   `ChainDescent/Group.lean` scaffolding). Scope it before committing: R1b may be cleanest as a *concrete* statement
   (the global Γ-action is an automorphism; pinning a segment forces the identity) rather than a general theorem.
6. **R2 predicate `CoordRegular`** and the ⟺; **R3** deferred.

**Sequencing:**

| Phase | Deliverable | Consumes | Risk |
|---|---|---|---|
| **0 ✓** | cores (`ScratchWLVisibility.lean`) | — | done |
| **1 ✓** | `Fintype V`-generic 1-WL (`WLGeneric.lean`) — `signature`/`sigKey_eq_iff`/`refineStep_iff`/`warmRefine`/`samePartition` over `[Fintype V][DecidableEq V]`, axiom-clean (`lake env lean`, not in build) | top-level `ChainDescent.lean` | done |
| **2** | **R1a** (group-CFI 1-WL closure is abelian-equivalent) | `product_coord_regular`, P1, gaps 3–4 | med (signature↔count) |
| **3** | **R1b** (Γ-symmetry visible; anchoring ⟹ rigid) | `commDeg`, `Group.lean`, gap 5 | med (Aut modelling) |
| **4** | **R2** characterization (`CoordRegular` ⟺ hideable) | R1, R2 predicate | med |
| **5** | R1′ (1-WL → `b_WL`/`k`-WL) ; R3 (general Route B) | all above | high / open |

Do **R1a before R1b** — R1a is the cleaner core-consumer and exercises P1 + the cross-graph notion end-to-end;
R1b adds the automorphism-modelling that is the new infra.

---

## 7. Honest scope

- This proves **no-rigid-Cameron for the group-CFI construction** (R1) and characterizes hideability (R2). It does
  **not** prove the general "no hideable non-abelian symmetry" (R3, GI-adjacent) — that is the target of the whole
  Route-B line, not this build. The probe already showed the group-CFI family is *tame* (visible-or-killed, poly even
  rigidified — fixed-group CSP), and that the residual wall candidate is **growing non-solvable** groups, outside any
  feasible construction (theory).
- R1 as built is at **1-WL**; the project-relevant statement is at `b_WL`. The 1-WL rung rules out refinement-mediated
  hiding and is the honest first step; R1′ is the strengthening.
- This is the **Cameron facet** of the flag floor. Closing it removes "or Cameron"; it does **not** touch the
  bounded-WL-dim *poly* core (the box-1 recovery mirror) — that is a different object (cameron-entanglement §2,
  opposite corners) pursued separately.

---

## 8. Pointers

- **Strategy / problem / attack menu / family battery:** [`chain-descent-cameron-entanglement.md`](./chain-descent-cameron-entanglement.md)
  (§1 claim, §3 why-it-closes-the-escape, §4 Routes A–E, §5 step list). **This doc is its Lean companion.**
- **Built cores:** `GraphCanonizationProofs/ChainDescent/ScratchWLVisibility.lean` (axiom-clean, not in build).
- **1-WL engine to generalize:** top-level `GraphCanonizationProofs/ChainDescent.lean`.
- **Empirical source:** `GraphCanonizationProject.Tests/NonAbelianCfiProbe.cs` (group-CFI; visible/killed/extraction).
- **Memory:** `project_nonabelian_cfi_witness_2026-06-28` (the probe arc + the fixed/varying × abelian/non-abelian map),
  `project_wl_visibility_lean_2026-06-28` (the cores).
- **Seal context:** the rigid seal's flag floor — `chain-descent-ir-blindspot-solver.md` §11.14;
  `chain-descent-remaining-work.md` §3a/§4.
