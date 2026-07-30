# Handoff — the 2-WL case (written 2026-07-30, after the 1-WL `VT ⟹ Tinhofer` refutation)

You are branching from the point where the previous session moved onto the 1-WL hunt for a VT
non-`Tinhofer` graph. That hunt **succeeded**; everything below is what it taught, filtered for
what matters to the **2-WL** question.

---

## 0. The question, stated precisely

> Start from the exact `Aut(G)`-orbit partition (so `CellsAreOrbits` holds by construction,
> however obtained). Individualize one vertex. Take the **2-WL** closure. Is some cell still not
> a single `Aut(G, χ)`-orbit?

**Status: no counterexample known, AND no evidence either.** Read §2 before believing the first half.

## 1. The necessary condition — and a correction

A 2-WL vertex-level failure **requires a non-schurian one-point extension**: if the extension is
schurian, the diagonal classes of the 2-WL pair colouring *are* the `Aut_v`-orbits, so no cell can
be mixed.

⚠ **Correction to something the previous session said once:** this is **necessary only, NOT
sufficient**. Non-schurity can live entirely off-diagonal while the vertex partition still equals
the orbits. Finding a non-schurian extension is the entry ticket, not the win.

`scratchpad/probe_2wl_vacuity.py` decides both (root schurity, one-point-extension schurity) for
any candidate in one call. **Run it on any candidate BEFORE investing in it.**

## 2. ⛔ THE VACUITY LEDGER — the existing "2-WL always repairs it" evidence is worth ZERO

Measured over 21 objects: **non-schurian ROOT closure 3/21; non-schurian ONE-POINT EXTENSION
0/21.** The sharp case has never occurred, so no sweep so far *could* have found a counterexample.
The 3 non-schurian roots are `net(Z₄)` (2-WL rank 10 vs orbital 14), `net(Z₆)` (10 vs 20), and
**Shrikhande (3 vs 4)** — in all three, individualization *repaired* the deficiency.

★ **Shrikhande is the calibration object.** Non-schurian at the root, schurian one point down.
The phenomenon you must break is exactly: **"point extension repairs coherent-closure deficiency."**
That is a statement about coherent configurations, not about graphs, CFI, or gauge. Nobody has
tried to prove it — so by this project's own standing rule it may well be false.

## 3. Habitats that CANNOT produce a counterexample (proved, don't re-sweep them)

- **Abelian Cayley graphs.** For abelian `G` and inverse-closed `S`, `x ↦ x⁻¹` is an automorphism
  of `Cay(G,S)` **fixing the identity** ⟹ `|Aut_e| ≥ 2`, 1-WL never discretizes, and **no GRR
  exists**. Measured: 3681/3681 had `nondisc == tested`. (This is the recorded `probe_grr_blind`
  trap recurring — it cost the previous session ~40 minutes of compute.)
- **Generalized dicyclic groups** — same exclusion (classical GRR criterion). Measured: Dic2–Dic7,
  1312 graphs, every one with a non-trivial vertex stabiliser.
- **Multipedes / rigid graphs** — already a theorem (`Cascade.recoverableAt_base_iff_discrete`):
  rigid ⟹ orbit partition discrete ⟹ the CAO start is discrete ⟹ vacuous.
- **CFI over base graphs** — CFI is about *distinguishing two graphs*, not orbit recovery inside
  one. Measured: CFI-twisted over prism, K3,3, Q3, cubic8, K5, Petersen (treewidth to 4)
  propagates **even at 1-WL**. Only `CFI[K4]-tw` fails, and that graph is `net(Z₄)` — an
  `Aut(G)`-type accident, not a gauge-parity effect.
- **Group-derived objects generally** (Cayley, Johnson, Kneser, Paley, rook, nets over abelian
  groups) tend to be schurian outright. That is precisely why the 0/21 above happened.

## 4. The search recipe that actually worked at 1-WL (port it to 2-WL)

1. **Lagrange filter.** Orbit sizes divide `|Aut_χ|`, so a cell of size `c` can only be an orbit if
   `c | |Aut_χ|`. ⟹ target **small stabiliser + still-coarse colouring**. The winning witness was
   `|Aut_v| = 2` against a **3-cell**: `3 ∤ 2`, mixed, no computation needed.
2. **Enumerate the stabiliser with a SMALL budget and skip on blow-up.** Big group ⟹ not the sharp
   case. Dropping the budget 30000 → 1500 was a ~15× speedup and is what found the witness; the
   generous-budget runs found nothing in 80 minutes.
3. **Cayley graphs give VT for free** — no transitivity certification needed. (Still verify the
   group: the previous session shipped broken dicyclic/semidirect builders that produced orders
   32/72/288 instead of 4n. Assert `|G|` and check associativity.)
4. **Pre-filter on "closure is non-discrete after one individualization"** — discretizing graphs are
   `Tinhofer` outright and can be skipped instantly.
5. **★ Aim for T2, not T1.** T1 = "`chooseIdK` picks a mixed cell" depends on the colour-id
   convention. **T2 = "EVERY non-singleton cell is mixed at a reachable node"** is
   convention-independent AND kills backtracking selectors too. Structural form:
   > **T2 ⟺ the descent reaches a node whose stabiliser is too small for any of its cells**
   > — extremal case: **trivial stabiliser while the colouring is still non-discrete.**
   Note this node need not be at depth 1: along a legal descent every picked cell is a full orbit,
   so `|Aut_χ|` divides by exactly the cell size each step and shrinks fast.

## 5. The 1-WL result you are building on, and what it does NOT give you

**`VT ⟹ Tinhofer` is REFUTED at 1-WL.** Witness `G = Cay(Z₁₂ ⋊₅ Z₂, {(0,1),(1,1),(2,1),(4,1),(7,1)})`,
vertex `(r,s) ↦ 2r+s`, n = 24, 5-regular. VT; `|Aut| = 48` ⟹ `|Aut_v| = 2`; one individualization ⟹
1-WL cells `[1,1,2,2,3,3,6,6]`; **all six non-singleton cells mixed** (T2). Lean's own
`warmRefineVec` reproduces the partition and `chooseIdK` picks the 3-cell. 20 witnesses total.
Verification: `probe_vt_witness.py`, `VTNotTinhoferProbe.lean`.

⚠⚠ **These are NOT 2-WL candidates — already checked.** On both witnesses, **2-WL recovers the
orbits exactly** (2-WL cells = stabiliser orbits: `[1×12, 2×6]` and `[1×8, 2×8]`), and both
one-point extensions are **schurian**. So the *maximal* 1-WL failure — every cell mixed — is fully
repaired at dimension 2. They are counted in the 0/21 above.

**Take the moral, not the object:** the recipe in §4 found a 1-WL failure of the strongest possible
kind. The same recipe run with the 2-WL closure, over a habitat that is *capable* (§2/§3), is the
live plan.

## 6. Why "2-WL is enough" should not be expected to hold

The `net(Z₄)` repair was **dimension-specific, not structural**. The invariant 1-WL missed was the
`Aut(G)`-type of a group element; 2-WL sees it because the object is built from a *binary*
operation, so the distinguishing structure lands at dimension 2. Nothing there caps the dimension
at 2. This is the tie-group ladder read as a dimension counter (`KEY_scoping`): F₂ · `Z_{2^k}` ·
solvable · bounded-local Γ · non-solvable — and `net(Z_{2^k})` is already a falsifier battery for
the `Z_{2^k}` rung. ⚠ State the GI calibration as calibration only; the standing steer bans
"X ⟹ GI∈P, therefore X impossible".

## 7. Tooling — what is sound and what is not

- ⛔⛔ **`probe_orbit_oracle.orbit_partition` IS BROKEN.** Proved on `multipede[6x5]`: true orbit
  partition has 15 blocks, the oracle returns 11 at the root and 6 when handed the correct
  partition. **It errs by MERGING** ⟹ it produces **false "ok"s, never false counterexamples** ⟹
  every "0 counterexamples" verdict it ever gave (the 498 + 313 VT pins) is unsound. Never use it.
- ✅ Sound machinery, validated against 11 independently known `|Aut|` values
  (`probe_cao_provenance.py`): `probe_cao_cleanroom.all_isos` (complete I-R leaf enumeration, every
  accepted leaf re-verified as a permutation automorphism) and `probe_cao_vtcover.iso_exists`
  (early-exit pairwise). The two agree on orbits.
- **Lean cross-check pattern:** `#eval` on `chooseIdK` / `step`, file placed **outside the package
  root** so it cannot enter any build; no `native_decide`. ⛔ Do NOT hand-reason the colour-id order
  from `indivOne χ v = 2·χv + 1`: the `2χ+1` makes `v` largest, but `sigKey`'s **Cantor-paired**
  tuples reverse the cell order. The previous session got this wrong twice; only `#eval` settles it.
  (Irrelevant if you aim for T2 — another reason to.)

## 8. Process traps that cost real time

- `str.replace`-based file edits **silently no-op'd three times**. Always verify the edit landed.
- Piping a long background command through `tail` **buffers everything** — you see nothing until it
  exits, and nothing at all if it is killed. Write to a log file.
- `pkill -f <script>.py` matches **your own launcher's** command line ⟹ self-kill (exit 144). Kill
  by PID.
- Importing a probe module **re-runs its module-level sweep**. `__main__`-guard everything.
- Voltage/connection-set enumerations blow up combinatorially (one hit 62k covers). Cap and log
  what you skipped.
