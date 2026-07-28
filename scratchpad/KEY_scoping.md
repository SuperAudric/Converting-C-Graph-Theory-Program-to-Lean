# Scoping — the **equivariant, separating, poly force key**

> **What this doc is.** A scoping pass (2026-07-28) on the object `ForcePick.forcePick_record` names as
> sufficient for the whole canonizer: a `Force.Key` that is `KeyEquivariant`, satisfies `KeySeparates`,
> and has a polynomial `keyCost`. It answers: what does the conjunction actually demand, what is the
> design space, which corners are occupied and by what, is it viable, and what to build next.
>
> **Companions.** `scratchpad/DUAL_resolver_scoping.md` §10.2 (the decomposition) + §10.8 (`ForcePick`);
> `docs/chain-descent-rigid-seal.md` §8.2 (Track R = this object under another name);
> `docs/chain-descent-w2-solvability-route.md` §3a/§3b (the coefficient ladder).
> **⚠ Nothing here is a new attack.** The pass's value is (i) an exact restatement of the obligation,
> (ii) a map showing the live tracks are rungs of ONE ladder rather than independent attempts, (iii) two
> concrete increments, and (iv) two defects found in the existing stack.

---

> **✅ STATUS 2026-07-28 (later) — §0's BOTH defects are PAID, and increment 1 + increment 2 are LANDED.**
> Gate EXIT 0, 107 modules, axiom-clean. Full record: `DUAL_resolver_scoping.md` §10.9.
> · **§0.1** — `KeyComplete.KeySeparates` renamed **`KeySeparatesAll`** (the bare identifier is left to
>   F3a's earlier `Hol.KeySeparates`), `keySeparates_rawKey` → `keySeparatesAll_rawKey`, bridge
>   **`KeyComplete.keySeparatesAt_iff_hol`**, and a `⚠` cross-reference added to *both* files stating
>   plainly that `forcedSet_single_orbit_of_keySeparatesAt` re-proves
>   `Hol.keepMin_pairwise_aut_of_separates`, and that only `ForcePick.forceThenPick` is new.
> · **§0.2 / §4** — **`readMin` LANDED** exactly as designed (`ForcePick` §8): `colOf` → `readSet`
>   (indexed by `Perm (Fin n)`) → `readSet_transport` → `keyEquivariant_readMin` →
>   `keySeparatesAll_readMin` (**unconditional**) → **`forcePick_readMin`**, plus
>   **`forcePick_open_clause_is_poly`** stating the reduction. All four clauses of §4's table went
>   through as predicted; no new machinery was needed, and `Force.kmin?` already had `kmin?_mem` and
>   `kmin?_eq_none_iff`. The one deviation: indexing by `Finset.univ.image` (as §4 recommended) made
>   equivariance a *Finset equality*, so `kmin?` needed no permutation-invariance lemma at all.
> · **Increment 3's prerequisite is also done** — the record object's `②` (`RecordCost.lean`,
>   `descentCostS_selNode_record_le`), i.e. the measurement instrument §4's "Sequence unchanged" line
>   names.
> · **✅ AND 3g IS DONE TOO (`ChainDescent/RecordKey.lean`, DUAL §10.10).** `pairKey` = plain
>   concatenation under **`ConstLen k₁`**; `recordKey = pairKey holKeyFast (orbKeyG guardSupply)` with
>   `①` + `②`. ⚠ Measured non-vacuous: `G8` cell **8 → 2** where `holKeyFast` keeps all 8.
>   ⚠⚠ **A trap this increment found:** the "obvious" product encoding `(len a :: a) ++ (len b :: b)`
>   is **wrong** — it orders the first component by *shortlex*, which `lexLeList` is not, so it
>   re-orders `holKeyFast`'s own narrowing. Do not re-propose it.
>
> **▶ NEXT (unchanged in shape, one step advanced): the `Publication` swap — `canonForm?` onto
> `RecordKey.recordKey` TOGETHER WITH reshaping the `②` bound into the pinned `costConst * n ^ costDeg`
> monomial (one pass; both touch pinned statements) → then item 1's equivariance half → then Track R
> P2.** §3's ladder is unchanged by any of this: the `F₂` rung is Track R's `②`, and the poly clause is
> still the only open one (`ForcePick.forcePick_open_clause_is_poly`).

## 0. Two defects found while scoping — read these first

### 0.1 ⚠⚠ `KeySeparates` EXISTS TWICE, and `KeyComplete` §2 re-derived F3a

`ChainDescent/HolKey.lean` §1 (F3a, earlier) already defines

```lean
def Hol.KeySeparates (key) (adj) (χ) : Prop :=            -- PER-NODE, 3 args
  ∀ u ∈ branches χ, ∀ w ∈ branches χ,
    keyV key adj χ u = keyV key adj χ w → ∃ ρ, IsColAut adj χ ρ ∧ ρ u = w
```

and `KeyComplete.lean` (2026-07-27) defines `KeySeparatesAt` — **the same predicate, contrapositive
form** — plus a *global* `KeyComplete.KeySeparates key adj` (2 args). So:

* **The names collide.** `Hol.KeySeparates` is per-node; `KeyComplete.KeySeparates` is the global
  ∀-χ form. Same identifier, different arities, both `open`-able. A reader grepping `KeySeparates`
  gets two different things and neither file mentions the other.
* **`KeyComplete.forcedSet_single_orbit_of_keySeparatesAt` duplicates
  `Hol.keepMin_pairwise_aut_of_separates`.** `Composite.forcedSet key adj χ` *is*
  `keepMin key adj χ (branches χ)` definitionally, and both theorems conclude that its members are
  pairwise `IsColAut`-related. The 2026-07-27 increment re-proved an F3a brick.
* **What is NOT duplicated:** F3a hands the pairwise-`Aut` conclusion to **consume**
  (its docstring: *"which is exactly what the consume side can then collapse (`forceThenConsume`)"*),
  i.e. it still routes through a computed certificate. `ForcePick.forceThenPick` is the part that was
  genuinely missing — discarding on the *uncomputed* automorphism.

▶ **Fix (small):** add `keySeparatesAt_iff_holKeySeparates` to `KeyComplete` (both directions are a
`by_contra`), rename one of the two, and cross-reference. This makes the duplication visible instead of
silent, and it is the T6 statement-audit discipline applied to my own increment.

### 0.2 ⚠ `forcePick_record`'s hypothesis set is currently claimed for NO key — a vacuity risk I created

`ForcePick` states the sufficiency theorem and explicitly declines to instantiate it. That is honest but
it is *exactly* the shape the project has been bitten by before (`ConfinementCitations.hflag` was
machine-checked **uninhabited**, making four showcase theorems vacuously true — memory
[[project_confinement_bundle_vacuity_2026-07-10]]). The vacuity rule is: a new predicate needs a
discharged instance in the same pass. It did not get one. §4 below is the anchor that pays this, and it
is the **recommended first increment**.

---

## 1. What the conjunction actually demands — the exact restatement

`KeySeparates` is cheap on its own because `DeepenExact.isColAut_of_readKey_eq` is **unconditional and
its hypotheses are very weak**: it needs only two colourings `χa`, `χb` that are `Discrete` with values
`< n`, plus equal reads. It says *nothing* about where they came from — no refinement relation, no
descent, no guard. So:

> **Any map `(adj, χ, v) ↦ ψ` producing a discrete `< n` colouring induces a separating key**
> (`readKey adj (indivOne χ v) ψ`). That is all `keySeparatesAll_rawKey` uses.

And the converse direction is `readKey_transport`: a colour-automorphism sends a witness for `u` to a
witness for `σ u`, so the read's fibres **contain** the orbits. Putting the two together:

> ### The obligation, exactly
> **Produce a discrete colouring `ψ(adj, χ, v)` in polynomial time that is canonical up to
> `Aut(adj, indivOne χ v)`** — i.e. the *read* must be labelling-independent, which is strictly weaker
> than `ψ` itself being equivariant (§2 trap 2) but strictly stronger than any invariant that ties two
> non-automorphic pointed graphs.

`Aut(adj, indivOne χ v)` is the stabiliser of `v` in `Aut(adj, χ)`, so this is *canonical labelling of
the pointed coloured graph*. **This is an exact restatement of canonization ∈ P, not a shortcut.** Per
the standing steer that is the TARGET and not a barrier — but the scoping must not pretend otherwise.

**What the restatement is still worth.** It replaces two coupled carried predicates (`Tinhofer` on
consume, `SolverSeparates`/`AggFaithful` on force) with one, and — §3 — it tells you *which group* you
have to be canonical modulo, which is what turns "one hard problem" into a graded ladder with known
rungs and one open top.

---

## 2. The design triangle — rich / invariant / poly, pick two

Every built or refuted candidate sits at a corner. The refutations are all recorded and measured; this
table is the consolidated view, which no single doc had.

| corner | occupants | why it fails the third clause |
|---|---|---|
| **rich + poly**, not invariant | `KeyComplete.rawKey`, `Deepen.leafOf`, `structReadAt` under an indexed order | the discrete `ψ` is produced by a greedy/index-broken pick, so the read is a function of the labelling. `keySeparatesAll_rawKey` ✓, `KeyEquivariant` ✗ |
| **invariant + poly**, not rich | `Force.lookaheadKey` (cell-size histogram), `refineByFrame` (1 F₂ bit ⟹ ≤ 2 classes/cell), `baseReadWL` (**REFUTED**: 10–16 classes on the rigid multipede, even iterated to a fixpoint), block-level set invariants (DUAL §6 S3: **0 of 8** forced decisions separated), `Hol.holKeyFast` (holonomy signature — invariant + poly, separation never claimed) | 1-WL-plus-a-colour is still 1-WL, and the multipede is *designed* against it |
| **rich + invariant**, not poly | `readMin` (§4, unbuilt), `RigidRefine.readAgg` over `framesUniv` (`keyEquivariant_compKey_readAgg_univ` — ① unconditional, `|frames| = n!`), `Deepen.orbKey` (guard is an `n!` search) | the invariance is bought by aggregating over an exponential family |
| **all three** | — | **the target** |

**Two traps this table encodes (both already paid for; do not re-derive).**
1. **A poly full-order equivariant frame set is TYPE-impossible on a gauged input.**
   `FramesEquivariant` at a gauge colour-automorphism forces the frame set invariant under *free*
   left-multiplication by the gauge group `G`, so `|frames| ≥ |G| = 2^β`. `seedFrames` retired
   (rigid-seal STATUS trap 3).
2. **`ψ` itself cannot be equivariant in general.** `OrdEquivariant` (an equivariant order permutation)
   exists only on **rigid** inputs — a gauge automorphism fixing the chosen order forces `σ = 1`. This
   is why the object of record aggregates rather than picking (rigid-seal trap 2). ⟹ the obligation must
   be phrased on the *read*, as §1 does, never on `ψ`.

---

## 3. ★ The ladder — the live tracks are rungs of ONE program, indexed by the tie-group

This is the pass's main structural finding, and it bears directly on *"only one branch needs to reach
the target"*.

The reason the rich+invariant corner is exponential is always the same: the discrete `ψ` is only
determined up to a group `T` (the **tie-group** — the subgroup of `Aut` the read cannot see the choice
inside), and invariance is bought by enumerating `T`. **A poly key exists exactly when `T` admits a poly
canonical form instead of enumeration.** That is the whole content, and it grades:

| tie-group `T` | canonical form for `T` | status | where |
|---|---|---|---|
| trivial (rigid node) | none needed | ✅ closed | `leafColKey` / R0a, `structRead` = the `ker = 0` anchor |
| `T = Aut`-orbit of the greedy choices (all picks Aut-equivalent) | none needed — **any** pick is canonical up to `Aut` | ✅ closed, and this is what `Tinhofer` MEANS | `orbKey`; measured `Tinhofer` at **1197 / 1361** swept nodes over 10 families |
| `F₂`-gauge (CFI / multipede) | **canonical RREF of the row space**, poly, no enumeration | ✅ the algebra is done | `RigidRREF.rrefCanon_eq_of_span_eq` (RREF is a canonical function of the *subspace*) |
| `Z_{2^k}` | Smith / Howell normal form | ▶ P3-ring, scoped | rigid-seal §8.2 (4), IR §11.13 |
| solvable | per-layer linear systems, layer by layer | ▶ L1–L3 landed, **L4 carried** | `GaugeLayer`; L4 shared with `ForcingModel.bridge` |
| `Γ ≤ G₀^m`, `G₀` bounded | Luks, **citable poly** | ✅ banked | W2 doc §3a Luks sharpening |
| non-solvable | none known | ⛔ **the wall** | W2/W3, claim #3 |

**Consequences for strategy.**
* **The branches are NOT independent lottery tickets.** Track R (`readAgg`/`readAggB`), the W2 gauge
  tower, and the consume-side `Tinhofer` discharge are the same object at different rungs. Progress on
  one does not substitute for another; it *completes a rung*. So "only one branch needs to arrive" is
  true of the *statement* but the branches do not offer independent chances at the same rung.
* **One axis IS genuinely independent and already delivers**: the Luks row is poly *by citation* for
  bounded local `G₀`, which covers every fixed construction plus CFI/Lichter (`Γ₂`). That is a real
  domain on which the poly clause is already met — it is not the wall's domain.
* **Track R's `②` is exactly the top of the F₂ rung**: the 2026-07-26 round-2 probe localised it to *a
  canonical column order on the rigid part with the gauge tied* — i.e. the recover-core, `ForcingModel.bridge`/L4.
  **So the next rung and the next task coincide**, which is the strongest argument for keeping Track R
  as the frontier rather than opening a new key program.

---

## 4. ▶ INCREMENT 1 (recommended first) — `readMin`, the non-vacuity anchor

**Purpose.** Occupy the {equivariant, separating} corner with a *theorem* so `forcePick_record`'s
hypothesis set is provably inhabited and the entire remaining difficulty is provably the **poly** clause
alone. It is **not** progress on the wall — it is brute force restated, and
`Refine.exhaustive_canonizer` already gives an unconditional exponential canonizer. Its value is
vacuity insurance (§0.2) plus a crisp reduction.

**Design.** Index the aggregate by `Equiv.Perm (Fin n)` rather than by descent leaves, so the index set
does not mention `adj` or `χ` at all:

```lean
def colOf (π : Equiv.Perm (Fin n)) : Colouring n := fun x => (π x).val   -- discrete, values < n

noncomputable def readMin : Force.Key n := fun adj χ v =>
  ((Force.kmin? (permList.map (fun π => Deepen.readKey adj (Descend.indivOne χ v) (colOf π)))).getD [],
   <exponential bill>)
```

`Force.kmin?` is the existing lex-min on `List (List Nat)` (it is what `keepMin` uses), so no new order
machinery is needed. The one implementation choice is the enumeration `permList` of `Perm (Fin n)`:
`Finset.univ` + `Finset.image` + a `Finset`-level min mirrors `readAgg` most closely and keeps the
bijection argument verbatim; `Finset.toList` is noncomputable, which is fine here — this key is
`noncomputable` and exponential *by design*, exactly as `orbKey` is.

**Why each clause goes through — all four ingredients verified in source:**

| clause | mechanism |
|---|---|
| `KeyEquivariant` | `transportColouring σ (colOf (π * σ)) = colOf π` (since `transportColouring σ χ = χ ∘ σ.symm`), so `π ↦ π * σ` is a **bijection of the index set**; each term matches by `Deepen.readKey_transport` + `Descend.indivOne_transport`. Min over a reindexed family is equal. Copy the `readEquivariant_readAgg` proof shape (`Finset.image` under a bijection). |
| `KeySeparates` | the minima are attained at some `πu`, `πw`; equal minima ⟹ equal reads ⟹ `isColAut_of_readKey_eq` (whose only hypotheses — discrete, `< n` — hold by construction for `colOf`). **Unconditional**, unlike `AggFaithful`. |
| fibres = orbits exactly | ⊇ from `Force.keyV_aut_invariant` (free from `KeyEquivariant`), ⊆ from separation. So this is "the perfect key" — per the standing steer, the *target*, stated honestly with its exponential bill. |
| cost | billed exponentially and visibly, which is the point — `②` rejects it, `①` does not. |

**⚠ Strictly better as an anchor than the existing exponential object.**
`keyEquivariant_compKey_readAgg_univ` already gives equivariance at `framesUniv`, but its separation is
`AggFaithful` — **carried**. `readMin` gets separation unconditionally from
`isColAut_of_readKey_eq`. So `readMin` closes the vacuity question and `readAgg`-over-`framesUniv` does
not. Estimate ~80 lines, no new machinery.

**Acceptance:** `forcePick_record` instantiated at `readMin` with `hkc` the exponential bound ⟹ an
unconditional `①` + totality + (exponential) `②` canonizer, and a one-line corollary stating that the
open clause is exactly `poly keyCost`.

## ▶ INCREMENT 2 — the de-duplication of §0.1 (small, hygiene)

Bridge lemma + cross-references + one rename. Do it in the same pass as increment 1, since both touch
`KeyComplete`.

## ▶ INCREMENT 3 — the actual research: buy the poly clause one rung at a time

**Do not open a new key program.** The next rung is Track R's `②`, already localised by the round-2
probe to the recover-core; and the `②` bill for the record object (DUAL ledger item 9 / remaining-work
queue 3f) is the measurement instrument that will tell you whether a rung is genuinely poly rather than
poly-by-declaration. Sequence unchanged: **3f (bill the record) → 3g (integration) → Track R P2.**

---

## 5. Viability verdict

* **The conjunction is an exact restatement of poly canonization**, so "is it viable?" is not a question
  about this key — it is the project's question. What the restatement buys is a single carried predicate
  and, via §3, a graded decomposition with **five of seven rungs closed or scoped and one wall**.
* **The two pairwise corners other than the anchor are already occupied by theorems**
  (`rawKey` = separating + poly; `orbKeyG`/`holKeyFast` = equivariant + poly), and increment 1 occupies
  the third. After it, *every* pairwise weakening is a theorem and the triple is the only open object —
  which is the cleanest form the frontier can be put in.
* **The honest risk to watch**: the ladder in §3 could be an *artifact of the cases already attacked*
  rather than a classification — nothing proves the tie-group of an arbitrary residue is a gauge group
  of module type. That is claim #2 (`ir-blindspot-solver.md:1068`, 0 falsifiers) and it is the same
  boundary the whole project sits on, not a new assumption introduced here.
* **What would falsify the frame**: a residue whose tie-group is *not* the automorphism group of a
  recovered algebraic structure — i.e. a node where the read ties a pair for a reason that is neither
  a certified symmetry nor a gauge of a recovered module. That is the W2 probe program's target, and it
  is worth adding this reading of it to that program's falsifier list.
