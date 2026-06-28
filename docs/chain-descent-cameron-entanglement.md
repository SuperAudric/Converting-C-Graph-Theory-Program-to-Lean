# Cameron entanglement — can a rigid graph carry a Cameron symmetry?

> **What this is.** A small, self-contained problem doc for the *Cameron non-existence* target: proving that a
> **rigid** graph cannot carry a **Cameron** (large non-abelian) symmetry — equivalently, that Cameron's symmetry is
> **non-separable** from its combinatorial structure. Written for a reader **new to the project**: §1–§2 define
> everything; §4 is the attack menu (including fresh angles); §5 is the step list. Provenance: the IR-solver doc
> [`chain-descent-ir-blindspot-solver.md`](./chain-descent-ir-blindspot-solver.md) §11.14, the seal's node-4 reduction
> ([`chain-descent-remaining-work.md`](./chain-descent-remaining-work.md) §3a / route §9.9.18).

---

## 1. The claim, precisely

The target is **not** "Cameron graphs don't exist" — they do (Johnson graphs `J(m,t)` are concrete Cameron graphs).
The target is:

> **(No rigid-Cameron.)** A *rigid* graph (trivial automorphism group) cannot carry a hidden Cameron symmetry.
> Equivalently: Cameron's (non-abelian) symmetry is **non-separable** from the structure that makes it hard —
> there is no way to keep the Cameron-hardness while stripping the symmetry to a rigid core.

It splits into two cases, of very different difficulty:
- **(a) Schurian / visible** — the Cameron group sits inside `Aut(G)`. *Trivially impossible* for rigid `G`
  (`Aut(G)` is trivial). No work.
- **(b) Non-schurian / hidden** — `G` is rigid, but its **WL-closure** (the coherent configuration that color
  refinement computes) is a *Cameron-like* scheme whose symmetry is **combinatorial**, not a graph automorphism.
  **This is the whole problem.** (For comparison: the CFI/multipede construction shows the *abelian* analogue of (b)
  is real — a rigid graph whose WL-closure carries a hidden **abelian** gauge. The question is whether the
  **non-abelian** analogue can exist.)

---

## 2. Background a newcomer needs (each in one line)

- **Cameron graph / group.** A primitive graph carrying a *large* automorphism group of **non-abelian** type
  (Johnson `J(m,t)` with `S_m`; the grid/Hamming with `S_m≀S_2`; affine and almost-simple rank-3 families). These are
  **classified** (Cameron's theorem, via the Classification of Finite Simple Groups, "CFSG").
- **The canonizer & "or Cameron".** The project builds a graph canonizer. It consumes symmetry cheaply, but a Cameron's
  symmetry is *too large to consume in a polynomial number of steps*, so the canonizer **flags** it ("or Cameron") —
  an honest "not handled," never a wrong answer. Removing this escape is the prize.
- **Two costs (the key dichotomy).** Canonization hardness has two independent sources:
  **`b(Aut)`** = pins needed to *kill the symmetry* (`≈ log|Aut|`), and **`b_WL`** = pins needed to make refinement
  *discretize* (one color per vertex). Always `b_WL ≥ b(Aut)` (discretizing kills symmetry). The interesting quantity
  is the **gap `b_WL − b(Aut)`** = *structural* hardness beyond symmetry.
- **Cameron vs. the wall, in those terms.** **Cameron** = large `b(Aut)`, **gap ≈ 0** (all its hardness is symmetry;
  kill the symmetry and it discretizes). **The wall ("node 4")** = small `b(Aut)`, **large gap** (structural hardness,
  no symmetry). They are *opposite corners*.
- **Rigid residue.** What the canonizer's Phase 2 / the IR-solver receives after all symmetry is consumed:
  `Aut = ` trivial, so `b(Aut) = 0`. Its *only* possible hardness is the **gap** (structural).
- **Separable symmetry (gauge).** CFI's symmetry is the cycle space `Z₂^β`, an **abelian** group acting linearly; it
  can be turned **off** (→ the rigid "multipede") or **on** (→ symmetric CFI) without changing the hard core. Abelian
  symmetry is *separable*. The conjecture here is that **non-abelian symmetry is not** — see §3.

---

## 3. Why "no rigid-Cameron" is exactly the right target

A rigid graph has `b(Aut) = 0`, so its hardness is *all gap*. If a rigid graph could be "Cameron-hard," its hardness
would have to be Cameron's hardness — but Cameron's hardness **is** its symmetry (`b(Aut)`, gap ≈ 0), which a rigid
graph does not have. So:

> A rigid graph cannot be Cameron-hard. Its only possible hardness is the **structural gap** — which is *the wall*,
> a different object, with **no known witness** (every node-4 falsifier hunt has come back empty).

Proving "no rigid-Cameron" therefore does two things at once:
1. **closes the rigid seal's "or Cameron" escape** — the IR-solver (which only sees rigid residues) provably never
   faces a Cameron; its sole remaining flag cause is the witness-free structural wall;
2. **explains why the *symmetry* seal must keep "or Cameron"** — Cameron is constitutively a `b(Aut)` object, so the
   linear/rigid machinery provably *can't* absorb it; it is handled by **classification** (the cited CFSG result),
   not by the rigid solver.

It does **not** collapse the two seals into one — it proves they are attacking genuinely different objects.

---

## 4. The attack menu (including fresh angles)

The classification gives the strategic shape: **Cameron is a finite list of families**, so "no rigid-Cameron"
decomposes into a *family battery* — for each Cameron family, show it has no rigid (hidden, non-schurian) version.
That makes the problem concrete even though the general statement is GI-adjacent.

- **Route A — Geometric rigidity (most concrete; good first target).** Each Cameron family is a *highly regular
  geometry* (Johnson = `t`-subsets; grid = a product; polar/forms = a classical geometry). Conjecture: **regularity
  this strong forces the automorphisms** — the local incidence rules of the geometry determine the global symmetry, so
  a graph realizing the geometry *cannot* be rigid. **Crux:** a "geometry ⟹ symmetry" lemma per family. **First
  pick: Johnson `J(m,t)`** — show that any graph whose WL-closure is the Johnson scheme has `S_m` in its
  automorphisms (so it isn't rigid). **Why fresh:** attacks the *geometry*, not the group; a newcomer can do Johnson
  by hand.
- **Route B — Non-abelian non-separability (the deep, unifying target).** Prove the only *hidden* (non-schurian)
  symmetry a graph can carry is **abelian** (the cycle-space gauge). Then a non-abelian Cameron can never be hidden in
  a rigid graph — it must be visible, hence killed by rigidity. **Crux:** characterize "hideable symmetry" and show it
  is abelian. **Status:** the conjecture behind §11.14; empirically solid (every gauge construction is abelian), no
  proof. **Why fresh:** it would subsume the family battery in one theorem.
  - **▶ EMPIRICAL SUPPORT (2026-06-28, `GraphCanonizationProject.Tests/NonAbelianCfiProbe.cs`,
    [[project_nonabelian_cfi_witness_2026-06-28]]):** the natural attempt to BUILD a hidden non-abelian gauge — the
    CFI / multipede generalized to an arbitrary finite group Γ (gadget = ordered product `g₁·…·g_d = e`) — is
    **WL-blind to the non-abelian structure.** S₃ ≡ Z₆ and D₄ ≡ Z₈ behave identically in every WL measure
    (`segFused`, `b_WL`, forcing-collapse), on every base, even though the graphs are genuinely non-isomorphic
    (different canonical forms). So WL-hardness depends only on `|Γ|` (Latin-square regularity), not on commutativity:
    a non-abelian gauge built this way collapses, to WL, onto an abelian gauge of the same order. Mechanism: WL only
    counts, and the `product=e` level-set incidence has identical counts for all groups of a given order;
    non-commutativity lives in the conjugacy/commutator structure the local gadget never exposes. **This is a NEGATIVE
    witness hunt = positive evidence for Route B** (with a concrete reason), matching the literature's use of only
    abelian groups for CFI-over-rings. **Caveat:** one construction (single product constraint per gadget); a
    commutator-exposing gadget might make non-abelian WL-visible — the *standard* non-abelian CFI is ruled out, not all
    constructions.
  - **▶ DISCRIMINATOR REFINEMENT (2026-06-28, `Probe_ExtractionDiscriminator`) — WL *depth* is blind, but the recovered
    *structure* is genuinely non-abelian.** Recovering the gadget relation `R_v` from the graph and testing isotopy-to-an-
    abelian-group (via Albert's theorem + relation-graph canonization) gives: `R_v` is the genuine relation of Γ
    (`recovered==Γ` always), and it is abelian-isotopic **iff Γ is abelian** — so S₃/D₄-CFI carry genuinely non-abelian
    structure that **no abelian module fits** (option-2's Smith/ring route flags it). So "rigid ⟹ abelian-linear
    structure" is FALSE: a *rigid* graph (anchored ⟹ `|Aut|=1`) can carry non-abelian STRUCTURE. **The catch (why this is
    not a counterexample to Route B):** that structure is **tame — poly-canonizable** (fixed finite Γ ⟹ a fixed CSP; the
    full canonizer canonized S₃-CFI), and it is non-abelian *structure without symmetry*, not a hidden non-abelian
    *gauge*. So it occupies the structure/non-abelian corner but is NOT the non-poly wall. The genuine-wall candidate is
    a **group-VARYING** non-abelian CFI (the non-abelian analog of Lichter's ring-varying construction) — untested.
    **Practical upshot for the rigid seal:** its "or non-linear" escape / option-2's handled class should read "linear/CSP
    over a fixed finite group (abelian OR non-abelian)," not "linear over an abelian ring" — the non-abelian-but-fixed
    case is poly (coset enumeration / fixed-group CSP) yet outside the Smith-normal-form route as currently specced
    (IR-solver §11.13). See [[project_nonabelian_cfi_witness_2026-06-28]].
  - **▶ GROUP-VARYING CHECK (2026-06-28, `Probe_GroupVaryingNonAbelian`) — the last category is tame.** The non-abelian
    analog of Lichter's ring-varying CFI: across a growing family (dihedral D₃…D₈, orders 6→16, + Heisenberg `H(F₃)`,
    order 27) the extraction recovers the genuine relation at every size, it stays non-abelian, and `b_WL` stays
    non-abelian-blind and tame — **no wall in extraction or WL-depth even as the group grows.** Since dihedral and
    Heisenberg are **solvable**, Babai–Luks string-canonization is poly, so the family is plausibly poly end-to-end. The
    genuine non-poly-wall candidate therefore **narrows to growing NON-SOLVABLE groups** (Aₙ / simple), which the full
    CFI cannot feasibly probe (gadget = `|Γ|^{d-1}` vertices) — so it is now a *theory* question (is CFI over growing
    simple groups super-poly?), with no constructible probe witness. Practical net: the rigid seal's "or non-linear"
    escape covers "linear/CSP over a fixed-or-growing **solvable** group"; only growing non-solvable groups remain a
    theoretical wall candidate.
- **Route C — Gap = 0 for Cameron (the pin-count route).** Prove every Cameron family has **gap `b_WL − b(Aut) = O(1)`**
  (no structural hardness beyond its symmetry). Then a rigid graph carrying a Cameron scheme would have `b(Aut) = 0`
  and `O(1)` gap, hence `b_WL = O(1)` — it discretizes cheaply, so it is *handled, not a wall*. **Crux:** a per-family
  WL-dimension bound (Johnson/grid are known-easy; the classical families are the seal's affine-slice work).
- **Route D — 2-closure (the project's existing route, for context).** A rigid graph's WL-closure has a *small*
  2-closure group; a Cameron scheme needs a *large* one. Skresanov's rank-3 2-closure theory is the lever. **Crux:**
  the 2-closure deficiency `G^(2)/G` for the non-schurian case. *Needs project context; see route §9.9.18.*
- **Route E — Spectral obstruction (speculative).** Cameron families have rigid spectral signatures (eigenvalue
  multiplicities tied to the group's representation theory); rigidity constrains multiplicities differently. Look for a
  family where "Cameron spectrum" and "rigid" are spectrally incompatible. **Why listed:** cheap to probe, may rule out
  families fast even if it doesn't generalize.

---

## 5. The steps required

- **Step 0 — Pin the "entanglement" property to a theorem.** Today "Cameron's symmetry is entangled with the
  decisions" is *framing* (the symmetry can't be cheaply consumed), not a literal statement. Write down the exact
  proposition you want ("no rigid-Cameron," in form (b) of §1) and the exact hypothesis you're allowed (the
  classification? a single family? a separability axiom?). **This is the real first task** — the rest is downstream.
- **Step 1 — Decompose by the classification.** Cameron = {Johnson, grid/Hamming, affine, almost-simple/polar, the
  finite exceptions}. Reduce "no rigid-Cameron" to "no rigid version of family `F`," one per family. (Citing CFSG here
  is fine — it is the one citation the project already allows.)
- **Step 2 — Do Johnson first (Route A).** Prove: a graph whose WL-closure is the Johnson scheme `J(m,t)` has `S_m` in
  its automorphism group ⟹ is not rigid. Concrete, self-contained, validates the whole approach.
- **Step 3 — Sweep the remaining families** by whichever of Routes A/C/E fits each (grid and Hamming are easy; the
  classical/forms families overlap the seal's affine-slice work — reuse it).
- **Step 4 — Attempt the unifying theorem (Route B).** If the family battery succeeds, try to replace it with
  "non-abelian symmetry is non-separable." Optional but it is the clean statement.
- **Step 5 — Discharge into the seal.** Feed "no rigid-Cameron" to the rigid seal to delete its "or Cameron" carry
  (the IR-solver's flag floor collapses to the structural wall); note the symmetry seal keeps its classification-based
  "or Cameron" unchanged.

---

## 6. Honest scope

- **The general statement is hard** — "no rigid-Cameron" in full generality is GI-adjacent. The *value* is the
  **decomposition**: the classification makes it a finite battery, and individual families (Johnson first) are
  tractable by hand.
- **Route B is a conjecture** ("non-abelian symmetry is non-separable / no non-abelian gauge"). Strongly supported
  (every known gauge is abelian; 0 falsifiers across the project's node-4 hunts), unproven.
- **What's already established (use freely):** Cameron is classified (CFSG, cited); `b_WL ≥ b(Aut)`; the abelian
  analogue of the hidden case is *real* (CFI/multipede), so the question is genuinely "abelian yes — non-abelian?".
- **Cleanest disproof of the approach (watch for it):** a *single* rigid graph whose WL-closure is a non-abelian
  Cameron scheme would refute "no rigid-Cameron" outright. None is known; constructing one (or proving you can't) is
  the empirical core.

---

## 7. Pointers

- **Lean formalization of the WL-visibility dichotomy (Route B, in progress):**
  [`chain-descent-wl-visibility.md`](./chain-descent-wl-visibility.md) — proves *why* the standard gadget is WL-blind to
  group structure (coordinate-regularity) and *that* a commutator gadget breaks the blindness. Phase-0 algebraic cores
  landed axiom-clean (`ChainDescent/ScratchWLVisibility.lean`). This is the durable home for the Route-B Lean thread.
- The lead this formalizes: IR-solver doc **§11.14** (the abelian-hiding vs non-abelian-Johnson 2×2; the
  "separable vs. integral" framing).
- The two-pin-count dichotomy: IR-solver doc **§11.1** (`b(Aut)` vs `b_WL`).
- The seal's node-4 reduction (where Cameron is the "or Cameron" escape): **`chain-descent-remaining-work.md` §3a**
  and route-doc **§9.9.18** (the affine/almost-simple/grid trichotomy; Skresanov 2-closure = Route D).
- CFI/multipede (the abelian hidden case that *is* real): IR-solver doc **§11.2–§11.3**.
