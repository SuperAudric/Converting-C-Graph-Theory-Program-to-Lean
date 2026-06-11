# Chain descent — the MODULE-ADJOIN plan: the adjusted Phase-2 proof route for the affine residue

> **STATUS (2026-06-11): this is the current point of reference for the seal's open `s(C)` content (G2-B) and
> the adjusted proof plan.** It continues [`chain-descent-self-detection-plan.md`](./chain-descent-self-detection-plan.md)
> §12 (the conservation split + rewiring) and supersedes the *retracted Frobenius separation route* recorded there
> and in [`chain-descent-seal-handoff.md`](./chain-descent-seal-handoff.md). A fresh reader who has read
> `00-START-HERE` → `seal-handoff` → `self-detection-plan` §12 should read this doc to reach the live frontier.
>
> **One rule for reading (project-wide):** treat every summary — this doc included — as a *hypothesis* to confirm
> against the Lean source and `PublicTheoremIndex.md`; the source wins. **Quality bar:** every theorem axiom-clean
> `[propext, Classical.choice, Quot.sound]`, full build green (`bash scripts/build.sh`). **Do not commit** — the user
> commits between messages.
>
> **TL;DR.** The seal's open content reduces, on the affine cyclotomic beachhead, to the single crux
> `PowAffineSeparates` (`CascadeAffine.lean`). The retracted "every twin is a Frobenius image" route died because the
> separability gap `Ĝ⊋G` is the amorphic `S₃`, not just Galois. **This session validated (computationally, on the
> F₁₆ Clebsch and F₂₅ witnesses) that the full `Ĝ` gap is nonetheless entirely *semilinear* (`ΓL₁`)** — the
> non-Galois remainder is `mult-by-α ∈ GL`, not a non-linear mystery. That revives a *corrected* module-adjoin route.
> The route splits into **(b) an easy linear-algebra lemma** (a `ΓL₁` map fixing a spanning base is the identity) and
> **(a) the genuinely-`s(C)` half** ("twins are semilinear"), which is **cyclotomic `s(C) ≤ 2`**.
>
> **§6 RESOLVED (2026-06-11): (a) IS CITABLE and covers both witnesses — so this thread CLOSES the affine slice.**
> Ponomarenko 2020 (arXiv:2006.13592) Thm 1.1: every cyclotomic scheme over a finite field is **2-separable with
> finitely many explicit exceptions** (Table 1); the object is exactly `affineScheme G0pow`. F₁₆ Clebsch `(2,4)` and
> F₂₅ `(5,2)` are **not** exceptions. **Consequence:** half (a) is a *citation, not open math*; the module-adjoin (b)
> is no longer needed to *close* the slice (it is demoted to the "build-instead-of-cite" future, very low priority —
> §6/§8).
>
> **WIRING + FULLY-REDUCED SLICE LANDED (2026-06-11, axiom-clean `[propext, Classical.choice, Quot.sound]`, full build
> green).** `CascadeAffine.lean` now carries: `affinePermFin_eq_one_of_span` (linear kill lemma), `TwinsAreSemilinear`
> (cited `s(C)`-half), `powAffineSeparates_of_twinsAreSemilinear` (reduction), `reachesRigidOrCameron_viaTwinsAreSemilinear`
> (seal capstone, spanning base as hyp), `exists_spanning_base` (basis image), and **`reachesRigidOrCameron_affineSlice`**
> — the seal on `affineScheme (G0pow β)` with the **only** affine-specific input being `hcite : ∀ T, TwinsAreSemilinear`
> (= cited cyclotomic 2-separability) + `d ≤ bound`. **The open counting crux `PowAffineSeparates` and the spanning-base
> hypothesis are both gone.** The genuinely hard residue (non-affine NLS / Davis–Xiang) is unchanged and deferred (§7).

---

## 1. What this session established (the deltas vs the prior handoff)

1. **The "lost" re-targeted approach was recovered and root-caused.** The post-Galois route (2026-06-09 commits
   `049273c` → `583cb11` → `0656843`) was the **intra-cell fusion-closure** attack: it built `intraCellRelations`,
   proved it is a `ClosedSubset` and that properness is free, reducing the converse to *nontriviality* — then found
   the **vacuity boundary** `intraCellRelations_eq_singleton_zero_of_primitive` (on the primitive floor the block
   collapses to `{0}`). **Root cause shared with the Galois fizzle:** every route gave the obstruction *algebraic
   structure* (a Galois subfield; a closed-subset congruence) that **primitivity then forbids**. The amorphic
   fusion is neither — it is a structureless counting coincidence. Git is linear/clean; nothing was lost as a commit.

2. **A group-theoretic bypass was checked and killed as a known vacuity trap.** Re-keying the seal onto the
   *orbit-level* harvest (`coversOrbits_of_realizers`, keyed on `OrbitPartition`) is trivially true (orbit-mates are
   aut-related by definition; seal-handoff §3). The genuine content must stay on the **visible / refinement-computable**
   realizers. Lesson banked: you cannot route around `s(C)` through the group — the content is irreducibly "orbits are
   1-WL-visible at bounded depth."

3. **The poly-vs-quasipoly framing was corrected.** Recovery depth `O(log n)` does **not** force quasipolynomial cost:
   recovered (symmetric) levels are a *single path* (harvest, not fork), so `O(log n)` adds depth, not branching.
   Quasipolynomiality (Babai/Spielman) comes from large branching at each level, which the harvest is designed to
   prevent. So an `O(log n)` `s(C)` bound is compatible with polynomial total cost.

4. **A citation the two prior deep passes missed:** Ponomarenko–Vasil'ev, *Cartan coherent configurations*
   (arXiv:1602.07132). Its **Theorem 3.1** (general, not Cartan-specific) is a *checkable* sufficient condition; see §6.

5. **Three probes built and green** (all in `CatalogueSchemeProbe.cs`); see §5.

6. **The module-adjoin premise was validated** on the concrete residue (F₁₆, F₂₅); see §3–§4.

7. **PDF tooling installed** (persistent, git-invisible): `pdf2txt <file.pdf> [first] [last]` on PATH
   (`~/.local/bin`, user-site PyMuPDF). Future agents: use it, do not reinstall.

---

## 2. The target and where it plugs in (verified against `CascadeAffine.lean`)

The recovery chain on the affine cyclotomic beachhead:

```
reachesRigidOrCameron_viaPowSeparation              -- seal capstone on affineScheme (G0pow β)
  └─ reachesRigidOrCameron_viaAffineIrreducible     -- needs hbound : ∃ bounded T, Discrete(warmRefine from T)
       └─ hbound  ⟸  PowAffineSeparates             -- via discrete_affineScheme_of_twoRoundDiffSeparates
```

The **single open obligation** is `PowAffineSeparates` (`CascadeAffine.lean`):

> `∃ T, T.card ≤ bound ∧ ∀ u u', (∀ ρ b, affineDepth2Count … T u ρ b = affineDepth2Count … T u' ρ b) → u = u'`

i.e. *the depth-2 difference-profile count `affineDepth2Count` is injective in the point, from some bounded base `T`*.
This is a **counting/separation** statement (not "automorphisms are trivial"). Everything above it is landed; closing
`PowAffineSeparates` closes the seal on this witness family (with `hClassify` = G3 cited, `hImprim` landed/earned,
`hne`/`hrank` discharged per instance via `G0pow_irreducible_of_adjoin` / `clebschWitness_irreducible`).

**Landed machinery to build on** (all axiom-clean, `CascadeAffine.lean`):
- `relOfPair_frobPerm_hom` — Frobenius is a configuration automorphism (`frobCoord` normalizes `G0pow β`,
  `frobCoord_conj_sigmaPow`: `σ ↦ σ^p`). The concrete `Ĝ⊋G` gap witness (its Galois part).
- `frobLinear_pow_eq_one_of_adjoin` / `frobPerm_pow_eq_one_of_adjoin` — a Frobenius power fixing a *field-generating*
  set (`Algebra.adjoin = ⊤`) is the identity (fixed-subalgebra argument). **The template to generalize.**
- `adjoin_eq_top_of_orderOf`, `G0pow_irreducible_of_adjoin`, `clebschWitness_irreducible` — the finite-field
  field-generation core + the concrete F₁₆ index-3 witness.

---

## 3. The adjusted proof route — the module-adjoin decomposition

The retracted route was: **TwinsAreFrobenius** ("every twin is a Frobenius image") + Frobenius-fixing-base-trivial ⟹
separation. It died because `TwinsAreFrobenius` is **false**: the gap `Ĝ/G` is the amorphic `S₃`, of which Frobenius
realizes only a `Z₂`.

The corrected route keeps the *shape* but fixes both halves to the full `ΓL₁ = ⟨mult-by-α, Frobenius⟩`:

- **(b) Module-adjoin lemma — "a `ΓL₁` element fixing a spanning base is the identity."** *Easy.* Both generators are
  `F_p`-**linear** (`mult-by-c` is `F_p`-linear; Frobenius `x↦xᵖ` is `F_p`-linear since `aᵖ=a` on `F_p`), so
  `ΓL₁ ⊆ GL_{F_p}(F_q)`. An `F_p`-linear map fixing an `F_p`-spanning set is the identity — plain linear algebra,
  recovery depth `= d = O(log n)`. (Contrast: the landed `frobLinear_pow_eq_one_of_adjoin` needs only field-generation
  — *fewer* points — because Frobenius is *multiplicative*; the `mult` part is not, so the clean unified form for the
  whole gap is the spanning-set/linear one. `mult-by-c` is in fact killed by **one** nonzero fixed point.)

- **(a) "Twins are semilinear" — *every depth-2 profile-twin is realized by a `ΓL₁` point map fixing the base*.** *Hard
  / the real `s(C)` content.* This is the analogue of the retracted `TwinsAreFrobenius`, now to `ΓL` rather than
  Frobenius. The validation (§4) makes its *premise* credible (the gap is exactly `ΓL`), but proving it is the
  WL-faithfulness / `s(C) ≤ 2` bound for cyclotomic schemes — **not** delivered by (b).

**Net:** the module-adjoin replaces the retracted Frobenius-only half with a correct, trivial `ΓL` half, and **sharpens
the open kernel from the counting `PowAffineSeparates` to the structural `TwinsAreSemilinear`** — but does not by itself
close the seal. Whether it *closes* or only *sharpens* depends on §6 (citability of (a)).

---

## 4. The validation (Plan-A premise confirmed on the concrete residue)

`CatalogueSchemeProbe.Probe_ModuleAdjoin_AmorphicGapIsSemilinear` (green) builds the cyclotomic index-3 scheme over
**F₁₆ (Clebsch, n=16)** and **F₂₅ (n=25)**, computes the algebraic-automorphism group `Ĝ` (colour permutations
preserving intersection numbers) and the subgroup realized by semilinear point maps `x ↦ mult(c)∘Frob^j` (verified on
all pairs):

| | `Ĝ` (algebraic gap) | `ΓL`-realised | non-Galois 3-cycle | Galois transposition |
|---|---|---|---|---|
| F₁₆ | full `S₃` (6) | **6 = all of `Ĝ`** | `x ↦ α·x` (mult, **GL**, j=0) | `x ↦ x²` (Frobenius, j=1) |
| F₂₅ | full `S₃` (6) | **6 = all of `Ĝ`** | `x ↦ α·x` (mult, **GL**, j=0) | `x ↦ x⁵` (Frobenius, j=1) |

**Verdict:** the amorphic gap is the full `S₃` *and* entirely **semilinear**. This answers the retraction's doubt:
Frobenius alone is only the `Z₂`, but the non-Galois remainder is `mult-by-α ∈ GL` (not a non-linear amorphic
mystery), so the *full `ΓL` adjoin* covers it. Kill mechanisms decompose cleanly: GL part (`mult`, fixed-point-free ⟹
one individualisation) + Galois part (Frobenius ⟹ field-generating set, the landed lemma).

---

## 5. Probes built this session (all in `CatalogueSchemeProbe.cs`, green)

- **`Probe_Theorem31_DensityBoundary`** — tests Ponomarenko–Vasil'ev Theorem 3.1 over the Hanaki–Miyamoto catalogue.
  Result: **141 schemes satisfy `2c(k−1) < n`; all recover at WL-depth ≤ 2** (confirms `b(X) ≤ 2`). **But narrow:
  only 12/481 primitives satisfy it.** The genuine residue — order-16 #19/#20 (Clebsch), order-25 #16/#17, all
  **rank-4 amorphic** — *violates* the inequality yet recovers; it lies **outside** Theorem 3.1.
- **`Probe_AmorphicResidue_LatinSquare`** — builds Latin-square-type amorphic schemes (GIK classification) from
  randomized non-group Latin squares, n ≤ 100. Result: **Latin-square *graphs* are primitive but rank-3 (depth-1-easy),
  flat WL-depth 2–3, 0 witnesses**; **Latin-square *net* schemes are rank-≥4 but *imprimitive*** (parallel classes =
  blocks ⟹ the handled case). Neither reaches the genuine primitive rank-4 amorphic residue — that zone is
  **negative-Latin-square (NLS) type**, which Latin squares cannot produce (see §7).
- **`Probe_ModuleAdjoin_AmorphicGapIsSemilinear`** — the §4 validation.

Empirical state: **five falsifiers, 0 G2-B witnesses** (Hanaki–Miyamoto catalogue; affine `ΓL(1,2^d)` + non-solvable
`A_n` sweeps; non-affine `PGL(2,p)`-on-pairs; Theorem-3.1 density; non-affine Latin-square). All caveated: **none
reaches the genuine residue zone cheaply** (§7).

---

## 6. The citation lever — Theorem 3.1, and the decisive open check

**Ponomarenko–Vasil'ev (arXiv:1602.07132).** Extracted via `pdf2txt`:
- **Theorem 3.1 (general):** a homogeneous CC with indistinguishing number `c` and max valency `k` satisfying
  **`2c(k−1) < n`** has every one-point extension 1-regular, hence `b(X) ≤ 2`; with **Theorem 2.5** (1-regular
  extension w.r.t. `m−1` points ⟹ `m`-separable) this gives **`base ≤ 2 ∧ s(C) ≤ 2`** (recovery depth ≤ 4).
  `c(X) = max_{r≠1} Σ_s p^r_{s,s*}`; both `c`, `k` are computable from intersection numbers. Proof is *elementary
  connectivity counting* (the inequality forbids small components of the max-valency graph) — plausibly Lean-formalizable.
- **Scope:** the inequality is a *sparsity* condition; the rank-4 amorphic residue is *dense* and **violates** it (the
  probe confirmed). So Theorem 3.1 covers the sparse end, **not** the residue.

**THE DECISIVE NEXT CHECK (Kink resolution — do this before building).** Half (a) of §3 ("twins are semilinear" =
cyclotomic `s(C) ≤ 2`) **may be a citation, not open math**: cyclotomic `s(C) ≤ 2` is recorded as a *known* result
(Evdokimov–Ponomarenko lineage). The question with two parts:
  1. Is cyclotomic `s(C) ≤ 2` citable with extractable hypotheses?
  2. Do those hypotheses cover the **primitive `G0pow β`** instance (the rank-≥3 leak candidate), not merely the
     degenerate/abelian cyclotomic?

Outcomes:
- **Citable & covers `G0pow`** → (a) is a citation; (b)[trivial] + (a)[cited] **closes `reachesRigidOrCameron_viaPowSeparation`
  on the witness** — a real seal slice landed. Frontier then honestly becomes the non-affine NLS residue (§7).
- **Not citable** → (a) is the isolated open kernel; build (b) as a banked clean piece and carry `TwinsAreSemilinear`
  as the sharpened crux (re-key `viaPowSeparation` onto it).

This is a ~20-minute literature check (pdf tooling available) and it gates the whole build.

### 6.1 RESOLUTION (2026-06-11) — cyclotomic `s(C) ≤ 2` IS citable; the affine slice closes

**Ponomarenko, *On the separability of cyclotomic schemes over finite field* (arXiv:2006.13592).** Extracted via
`pdf2txt`:
- **Theorem 1.1:** *with finitely many possible exceptions, every cyclotomic scheme over a finite field is
  2-separable.* The exceptional degrees are **explicit (Table 1):** `p=2: d∈{6,7,8,9,10,11,12,14,15,16,18,20}`;
  `p=3: d∈{4,5,6,8,10}`; `p=5: d∈{4,5,6}`. (Even the exceptions are 3-separable — ref [5].)
- **Object match:** the paper's cyclotomic scheme = relations `{(x,y) : y−x ∈ M_a}`, `M ≤ F×` — *exactly*
  `affineScheme (G0pow ⟨β⟩)`.
- **Both witnesses are NON-exceptions** ⟹ citably 2-separable: F₁₆ Clebsch `(p,d)=(2,4)` (∉ the `p=2` list);
  F₂₅ `(5,2)` (∉ the `p=5` list).
- **Answers question 2 (on-target):** Thm 1.1 covers the general cyclotomic family (incl. the primitive proper-subgroup
  `G0pow`), minus the explicit finite Table-1 set. So the affine cyclotomic is the *citably-closeable* slice (Kink 3
  confirmed: easy/affine end of G2-B; hard core = non-affine NLS, §7).

**Buildability (per the low-priority "build > cite" note).** Thm 1.1's proof: reduce (via ref [5]) 2-separability to
separability of a *fission* of an auxiliary scheme `C(F)`, prove via a **general sufficient condition for separability
(Thm 4.1, §§3–4)** + a **parameter inequality (§5)** + **computer calculations to prune the exceptional cases (§6,
Table 1)**. Verdict: **buildable but heavy** — needs CC-separability theory (no Mathlib substrate) *and* a finite
computer-check; Thm 4.1 would subsume the Cartan Thm 3.1 family. **Cite now; full build = substantial future project,
very low priority.** Axiom hygiene: cite as a theorem-statement **hypothesis** (`CyclotomicTwoSeparable …`), not a fresh
`axiom`.

**The remaining work (the new, bounded kink): the WIRING.** The citation gives *2-separability* (iso-determination by
2-dim intersection numbers); the project's `PowAffineSeparates` is *depth-2 difference-count injectivity from a bounded
base* (a discreteness/base statement). The bridge is the standard equivalence **`m`-separable ⟺ 1-regular `(m−1)`-point
extension** (Cartan Thm 2.5) ⟹ base-discreteness, with the base-number ingredient (cyclotomic base number is small). So
the connection is a **definitional/formalization bridge** matching the literature's 2-separability (or the WL-dim ≤ 3
corollary, Thm 1.3, closer to base-discreteness) to `affineDepth2Count` injectivity — **bounded formalization, not
research**. This is now the actual next implementation step (§8), replacing "build (b)".

---

## 7. Honest scope — the affine slice vs the genuine residue (do NOT confuse them)

- **Affine cyclotomic (the beachhead, this doc's target)** is a *translation* scheme over `(F_q,+)`. It is the
  **easy / likely-citable** end of G2-B. The module-adjoin route addresses *this*.
- **The genuine hard residue is negative-Latin-square (NLS) type** — the *non-affine* Clebsch-family amorphic schemes,
  constructible only via **Davis–Xiang partial-difference-sets in non-elementary-abelian 2-groups** (or PSL(2,q) on
  `A₅/S₄` cosets / classical rank-3/4 geometries). The Latin-square probe proved the cheap constructions cannot reach
  it. This remains **deferred**, gated behind the heavier PDS construction; tackle only after the affine slice is
  resolved and if the non-affine existence question becomes the blocker.
- **A live tension to resolve while doing §6:** memory classifies cyclotomic `s(C) ≤ 2` as the *abelian/affine* family
  ("does not populate the non-abelian-primitive class"), yet the docs wire affine cyclotomic as the G2-B *cascade*
  beachhead. Reconcile: most likely the affine cyclotomic is a *genuine primitive cascade target whose `s(C)` is
  citably small* — the easy slice — with the non-abelian-primitive *hard* core being the non-affine NLS. Confirm this
  framing as part of §6.

**Banked as non-viable (do not re-attempt):** the Galois/Frobenius-only separation (retracted — only `Z₂` of `S₃`);
the closed-subset / intra-cell block route on the primitive floor (vacuity boundary,
`intraCellRelations_eq_singleton_zero_of_primitive`); the orbit-level harvest re-key (vacuity trap); Theorem 3.1's
one-point inequality *for the residue* (it is dense, violates it); the cheap Latin-square construction *for the NLS
residue* (LS-type only — graphs easy, nets imprimitive).

---

## 8. The plan, ordered

1. **Resolve §6 — DONE (2026-06-11, §6.1).** Cyclotomic `s(C) ≤ 2` is citable (Ponomarenko 2020 Thm 1.1) and covers
   both witnesses. Outcome = **CLOSE** (cite, don't build). So (a) is a citation; (b) is demoted.
2. **The wiring — LANDED (2026-06-11, axiom-clean `[propext, Classical.choice, Quot.sound]`, full build green).**
   Bridge scoped first: `discrete_affineScheme_of_twoRoundDiffSeparates`'s `hsep` is *literally* `PowAffineSeparates`'s
   body, so `PowAffineSeparates ⟹ Discrete ⟹ seal` was already wired; the only gap was citation → `PowAffineSeparates`.
   Landed in `CascadeAffine.lean` (end of §CyclicAffine):
   - **`affinePermFin_eq_one_of_span`** (the kill lemma, b) — any `F_p`-linear automorphism fixing a *spanning* base is
     the identity perm. Pure linear algebra; covers all of `ΓL₁`.
   - **`TwinsAreSemilinear`** — the cited `s(C)`-half as a theorem-statement hypothesis (every depth-2 profile-twin from
     `T` is realised by an `F_p`-linear automorphism fixing `T`); justified by Ponomarenko arXiv:2006.13592 Thm 1.1.
   - **`powAffineSeparates_of_twinsAreSemilinear`** — the reduction: `TwinsAreSemilinear` on a *spanning* base ⟹
     `PowAffineSeparates` (a twin's realiser fixes the spanning base ⟹ identity ⟹ `u=u'`).
   - **`reachesRigidOrCameron_viaTwinsAreSemilinear`** — the seal capstone: composes the reduction into
     `reachesRigidOrCameron_viaPowSeparation`, so the seal on `affineScheme (G0pow β)` follows from the cited
     `TwinsAreSemilinear` + a spanning base + (G3, `hne`/`hrank`, `hImprim`). **The raw counting `PowAffineSeparates` is
     gone, replaced by the cited statement.**
2a. **The fully-reduced affine slice — LANDED (2026-06-11, axiom-clean, full build green).** The spanning-base
   hypotheses are now discharged internally:
   - **`exists_spanning_base`** — `∃ T, card ≤ d ∧ affineE.symm '' T` spans `F_p^d` (the standard basis `Pi.basisFun`
     transported through `affineE`; basis image + `Basis.span_eq`).
   - **`reachesRigidOrCameron_affineSlice`** — the bundled capstone: picks that base internally, so the **only**
     affine-specific open input is `hcite : ∀ T, TwinsAreSemilinear …` (the *global* form of cyclotomic 2-separability,
     Ponomarenko Thm 1.1) plus `d ≤ bound`. With {G3 cited, this citation, `hne`/`hrank`, `hImprim`} it yields the seal
     on `affineScheme (G0pow β)` — **no counting crux, no spanning-base hypothesis carried.** That is the affine
     cyclotomic slice fully reduced to the cited 2-separability + G3.
3. **Build (b), the module-adjoin lemma — LANDED (2026-06-11, axiom-clean `[propext, Classical.choice, Quot.sound]`,
   full build green).** `affinePermFin_eq_one_of_span` (`CascadeAffine.lean`, end of §CyclicAffine): *any `F_p`-linear
   automorphism `g₀` whose affine perm (zero translation) fixes a base `T` pointwise, with `affineE.symm '' T` spanning
   `F_p^d`, is the identity perm.* Pure linear algebra (`LinearMap.ext_on` on the span + `LinearEquiv.ext`); covers the
   **whole** `ΓL₁` gap at once (both `mult` and Frobenius are `F_p`-linear), depth `= d = O(log n)`. The first grounded
   piece of the route; companion to the Frobenius-only `frobPerm_pow_eq_one_of_adjoin`. **Use:** the "kill" half — with
   the cited "twins are `ΓL₁`" (a) it gives `PowAffineSeparates` (a spanning base, fixed by a twin's realiser, forces
   the twin trivial). The connecting reduction `powAffineSeparates_of_twinsAreSemilinear` (define `TwinsAreSemilinear`
   + a bounded spanning base exists) is the next increment.
4. **Only then** the non-affine NLS residue (§7) — the Davis–Xiang PDS probe + the relation-algebra generalization of
   the module-adjoin — if it becomes the blocker. This is the genuine remaining open frontier.

---

## 9. Pointers

- Prior handoff (conservation split + rewiring): [`chain-descent-self-detection-plan.md`](./chain-descent-self-detection-plan.md) §12.
- Authoritative seal state + all gaps: [`chain-descent-seal-handoff.md`](./chain-descent-seal-handoff.md).
- The affine model + landed Frobenius/adjoin machinery + the crux: `ChainDescent/CascadeAffine.lean`.
- The seal capstones + the trichotomy/largeness interface: `ChainDescent/Cascade.lean`.
- Probes + the catalogue measurement core: `GraphCanonizationProject.Tests/CatalogueSchemeProbe.cs`.
- Memory topic file (lossy, routes here): `memory/project_cartan_2separability_lead_2026-06-11.md`.
