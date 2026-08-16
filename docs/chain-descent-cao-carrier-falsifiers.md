# CAO carrier/payload falsifier constructions — the record

> ## ▶▶▶ STATE OF THE QUESTION — self-contained, 2026-08-16. Read only this to know where things stand.
>
> **The goal.** Build a *designed* counterexample to CAO propagation at 2-WL: an object whose 2-WL
> closure, started from the exact orbit partition and with one vertex individualized, has a **mixed
> cell** (a cell meeting two `Aut_v`-orbits). §0 has the hypothesis; get it right before building.
>
> **The object (Construction C, "the ensemble").** One graph. It contains a *copy* for every graph on
> `L` labels — a copy is `L` payload vertices forming a clique. All copies share one **frame**: two
> vertices per label-pair, "edge" and "non-edge"; a copy's payload vertex attaches to whichever
> matches its own graph. Plus gauge/central vertices. Payload orbits = **marked-graph iso classes**.
>
> ### ✅ SETTLED (measured on the real object, or proved)
> * **1-WL: the design programme WORKS.** Construction B is a genuine counterexample (§2, 4 mixed
>   cells); Construction C at rung 1 is a second (§6, 100 mixed cells). Nothing below touches these.
> * **2-WL reads the encoded edge** (§6b, proved + measured): a typed common neighbour is exactly what
>   pair-refinement counts. ⟹ the frame hides the payload **totally at 1-WL, not at all at 2-WL**.
> * **No mixed cell has ever been observed at 2-WL**, in any vertex kind: `L=4`, `N=332` — payload
>   20 = 20, frame 2 = 2, central 11 = 11 (§6e.4d.4).
> * **The reason no measurement can settle the question** (§6e.4a): the single-copy encoding `M` is a
>   **complete** invariant at every reachable `L` (20=20, 90=90, 544=544). Where `M` is complete
>   nothing can be added to it, so every "the ensemble equals `M`" measurement was **forced** and
>   carries no information about large `L`.
>
> ### ⚖️ THE WHOLE QUESTION IS ONE UNDECIDED DISJUNCTION — and both sides are live
> Within a copy, refinement recovers that copy's own graph. Across copies, the pair colour of two
> payload vertices records the **alignment** of their two readings of the shared frame. At large `L`
> the within-copy channel must fail (CFI). **Does the cross-copy channel then supply the orbit?**
>
> | | **(A) it supplies the orbit** | **(B) it supplies nothing the copy lacks** |
> |---|---|---|
> | consequence | `E(L)`-2-WL is complete ⟹ **no mixed cell, ever** ⟹ Construction C dies at rung 2 | the ensemble ≡ the poly-size frame encoding ⟹ a CFI payload **merges** ⟹ counterexample |
> | argued by | §6e.4d — the **Ruler Lemma** plus (LB), (P1), (P2) | §6d/§6e — the **collapse**, and §6d.8's lemma |
> | supporting measurement | the ruler channel demonstrably separates what a copy provably cannot (§6e.4f, `P6`: 3 → 6 cells) | `E ⊑ M` round by round at `L=4`, and the cross-copy aggregate is `M`-determined at `L=4` |
> | ⚠ why that measurement is weak | taken where the within-copy channel was **also** available | taken where `M` is **complete**, so it was forced (above) |
> | status | **NOT PROVED.** ✅ 2026-08-16b: its engine and *both* premises are now **theorems** (§6e.4g items 1–3, Lean); ⛔ what is still missing is the **instantiation** — see the green block below | **NOT PROVED.** §6d.8's lemma is open; ORB, its one clean sufficient condition, is false at large `L` |
>
> ⛔ **Neither side is established, and this doc must not be read as endorsing either.** Earlier
> revisions of §6e.4a/b/d declared (A) proved and Construction C dead; that verdict is **withdrawn**
> — the argument stands as an argument, not as a settled result.
>
> ### ✅✅ 2026-08-16b — **§6e.4g ITEMS 1, 2 AND 3 ARE DISCHARGED IN LEAN.** The disjunction is **still open**, and it is now localized to one step.
> Three new gate-listed modules, all `[propext, Classical.choice, Quot.sound]`, no `sorry`:
> * **item 1** `ChainDescent/RulerLemma.lean` — ★ `ruler` and `phi_eq_iff_orbit`: carrier-generic, no
>   graphs, and with a **non-vacuity witness where `Φ` is strictly finer than the tag**. (A)'s engine
>   is sound; it is no longer in dispute. ⚠ Two corrections to §6e.4d's prose are recorded in the
>   module header (the conclusion is the **orbit**, not the multiset over `Γ`; hypothesis (i) is used
>   in one direction only).
> * **item 2** `ChainDescent/CopyRestrict.lean` — ★★★ **`lb` is (LB) as a theorem, at every `L`, at the
>   real object `Ensemble.eRoot`** — previously paper + `L=4`. It carries two pieces worth naming:
>   `restrict_sig_eq` (*stability restricts to any colour-definable sub-carrier* — carrier-generic, and
>   the genuinely new lemma) and **`encoded_edge_eq` = §6b at the object**, proved via the individualized
>   centre being the unique sort-3 vertex.
> * **item 3** `ChainDescent/CopyProbe.lean` — ★★ `tag_isolates` **(P1)** and `profile_injective`
>   **(P2)**, from (LB) plus discreteness of the *chosen* copy. Corollary **`sameLabelOrbit_of_tag`:
>   `Ensemble.MixedCell` can never be witnessed with a refinement-discrete proper copy on the left.**
>
> ⛔⛔ **The doc's own claim *"1+2+3 ⟹ (A) is a theorem and (B) is refuted"* was TOO STRONG, and doing
> the work is what showed it.** Three things sit between the items and (A), and *all three are about the
> instantiation, not the mathematics*:
> 1. **the coherence chain** (§6e.4d.3's first two arrows): *diagonal colour ⟹ `Φ_E`*. Reachable with
>    the same machinery — `sig_singleton_snd` gives *"a pair colour determines its endpoints' diagonal
>    colours"*, and `sig_restrict` at the frame injection gives *"a pair colour determines the `Align`
>    of the two slot profiles"*. Not written.
> 2. **the instantiation** of `RulerLemma` at the ensemble (`Γ = S_L`, `X` = typed slots, `Ω` = payload
>    vertices, `b` = the slot profile, `y` = the diagonal colour). Equivariance is free from
>    `Ensemble.invG_eRoot`. ⛔ **But `Ensemble`'s slots are ORDERED**, so the ruler's reading is 2-to-1
>    (twins) and `RulerLemma`'s hypothesis (ii) fails as stated. ★ The fix is identified and cheap:
>    weaken `eq_of_align_eq`'s *"`v` injective"* to *"`v` refines `u'`"*, which every reading satisfies
>    because readings are twin-invariant. `hiso` additionally needs `Ω` cut down to **proper symmetric**
>    copies — a model refactor of `Ensemble.lean`, not a mathematical obstacle.
> 3. **existence of a refinement-discrete copy** in `E(L)` — Babai–Erdős–Selkow plus §6e.4d.2's
>    closure argument. Measured (5760/32768 at `L=6`); not formalized, and it is a statement about the
>    payload family, not about the ensemble.
>
> ⟹ ★★★ **What is now machine-checked is that the ruler is isolated and that it works as a ruler.
> What is NOT checked is that the `Align` channel reaches the NON-discrete copies** — and that is
> exactly the sentence (A) asserts and (B) denies. The disagreement has gone from *"is the whole
> argument sound"* to *"does one identified, writable chain of coherence steps go through at the real
> object"*. ⛔ Do not read the three green items as (A).
>
> ### ▶▶ NEXT STEPS — verifiable only. Do not add prose to this file.
> **§6e.4g is the decision procedure**, items 1–3 now done. What remains:
> 4. **For (A):** the three numbered gaps above, in order 1 → 2 → 3. Item 1 is pure bookkeeping with
>    machinery that already exists; item 2 needs the `Ensemble` model moved to unordered proper slots.
> 5. **For (B): prove §6d.8's lemma**, or exhibit an object with a ruler *and* a surviving mixed cell.
>    The falsification search (§6e.4f) is the harness; it found 0 in 1491 objects, with a thin margin.
>    ★ (B) is now the *cheaper* side to attack: one object refutes (A) with no large-`L` argument, and
>    `sameLabelOrbit_of_tag` tells you exactly where it cannot live (any copy the search uses as the
>    ruler is off the table, so the mixed pair must be two non-discrete copies).
>
> ⚠ **Everything below §6e.4d is the RECORD, including several retractions.** It is kept so that
> withdrawn claims are not silently re-inherited (§9 lists them), not because it is a reading path.
> A fresh reader needs: this box → §0 → §7 (the filters) → §6e.4d–g → §8a. Nothing else is required.
>
> ⚠ Companion, not replacement: [`chain-descent-cao-propagation.md`](./chain-descent-cao-propagation.md)
> owns the *question*. Read its §1 (the hypothesis), §3 (the coupling principle) and §14 (the anatomy
> and the arity ladder) before this. ⚠ The research phase is closed
> ([`chain-descent-wind-down.md`](./chain-descent-wind-down.md)); this is a **record**, not a live track.

<details>
<summary><b>Superseded framing kept for provenance — the 2026-08-13 audit box (click to expand)</b></summary>

> **What this was.** Three related *designed* attacks on CAO propagation, raised from outside the
> project (2026-08-12). §6's *"the ensemble is passive"* is **withdrawn** (§6a): the real ensemble's
> 1-WL sees only the degree sequence, so it is far coarser than the two-copy model (**292 / 100** vs
> **538 / 6**), and §6's witness was degree-regular and could not have detected the gap. Then:
> §6b (2-WL reads the encoded edge) and §6d (the `L=4` collapse, every channel) landed on top, and
> §4/§5.1's payload kills were **REINSTATED** — §6a indicts the **`shared`**-frame two-copy model, not
> the `disjoint` one. The conclusion drawn at the time — *"the scheme is blocked on a payload, not on
> tooling"* — is **superseded**: §6e.4a showed the payload question is unreachable by measurement, and
> the live question is now the (A)/(B) disjunction above, not a payload search.

</details>

---

## ▶▶ HANDOFF — start here

**Where it stands, in six sentences.** The CAO-propagation hypothesis starts from the *exact orbit
partition* (§0) — forget that and you will build something that fails at the root instead of at
propagation, which is how Construction A died (§1). A `Q₄` complementary-pair carrier **is** a 1-WL
counterexample (§2, `n = 352`, 4 mixed cells), and the gauge-ensemble Construction C is a second one
at rung 1 (§6, `n = 229,406`, 100 mixed cells) — so at 1-WL the design programme **works**. At 2-WL
no mixed cell has ever been observed, and §6b says why the obvious hiding fails: **an edge encoded as
a typed common neighbour is exactly what 2-WL counts.** Whether the construction is *dead* at 2-WL or
merely *unmeasurable* there turns on one undecided disjunction — does the **cross-copy** channel
supply the orbit (A), or nothing the copy lacks (B)? — stated in the box at the top of this file.
Both sides have an argument, neither has a proof, and **no measurement at any reachable size can
discriminate them** (§6e.4a), which is why §6e.4g lists only theorems and experiments as next steps.

**Reading order — minimal path for a fresh reader.** The top box → §0 (the hypothesis + N1/N2) →
§7 (the filters — cheapest thing in the doc) → **§6e.4d** (the case for (A)) → **§6e.4e** (the case
for (B), and why the two cannot be told apart by measurement) → **§6e.4f** (this session's
experiments) → **§6e.4g** (the decision procedure) → **§8a** (the Lean layer + the trap list).

**Everything else is the record.** §2/§3 (how the constructions are built), §4/§5 (the payload bar —
⚠ now known unreachable by measurement, §6e.4a), §6/§6a–c (the rung-1 result and its audits), §6d/§6e
(the collapse programme and its retractions), §6f (the arity bound and its Lean chain), §6g (a closed
side route), §8 (files), §9 (proved vs measured vs argued, and the retraction list). Read them when
you need provenance for a specific claim, not as a path.

> ### ▶▶▶ FRESH PICKUP — 2026-08-15**d**. THIS BLOCK SUPERSEDES EVERY DATED BOX BELOW IT.
> **Goal of the track:** exhibit a *designed* counterexample to **CAO propagation at 2-WL** (§0 for the
> hypothesis — start from the exact orbit partition, individualize **one vertex**, take the `k`-WL
> closure, ask whether cells are still `Aut_v`-orbits).
>
> ### ⚖️ STATE: **UNDECIDED, between two named positions.** ⛔ An earlier revision of this block said *"Construction C is dead at 2-WL, the question is ANSWERED"*. **That verdict is WITHDRAWN** (2026-08-16). The argument for it stands as an argument; it is not a result.
> **§6e.4d = the case for (A). §6e.4e = the case for (B) and why measurement cannot separate them.
> §6e.4f = this session's experiments. §6e.4g = the decision procedure.** One-screen version:
> * ### ▶▶▶ THE QUESTION: at large `L` the within-copy channel must fail (CFI). Does the **cross-copy** channel then supply the orbit?
>   **(A) yes** ⟹ no mixed cell ever, Construction C dies at rung 2. **(B) no** ⟹ the ensemble ≡ the
>   poly-size frame encoding, a CFI payload merges, and the construction works. ⛔ **Neither proved.**
> * ★★★ **THE RULER LEMMA** — (A)'s engine, carrier-generic, three lines, no graphs in it. If **one**
>   `ω₀` has (i) a tag class equal to its own orbit and (ii) an **injective** reading, then `Φ` decodes
>   the whole orbit of `b_ω`. ▶ **Formalizing this is next step 1**; the lemma itself should not be in
>   dispute once machine-checked, which isolates the disagreement to (LB)/(P1)/(P2).
> * ★★★ **(A)'s repair of §6e.4c's broken step: the probe is CHOSEN, not arbitrary.** Isolating an
>   *arbitrary* `b₀` presupposes the conclusion; isolating a *chosen* refinement-discrete copy is
>   bought by a **LOWER** bound — **(LB)** `col_E` restricted to a copy refines that copy's own bare
>   2-WL. ⚠ **(LB) is (A)'s single load-bearing claim**: proved on paper, measured **64/64** copies at
>   `L=4`, not machine-checked. Attack it first if (A) is wrong.
> * ⚠⚠ **(B) is NOT refuted, and its supporting measurements are not weaker than (A)'s.** `E ⊑ M` holds
>   round by round at `L=4` and the cross-copy aggregate is `M`-determined there. Those are forced,
>   because `M` is already complete at `L=4` — but (A)'s measurements are equally circumstantial: every
>   one was taken where the within-copy channel was *also* available.
> * ★★★ **THE REUSABLE ASSET, and it survives whichever way the disjunction falls — "THE RIGID RULER"
>   DESIGN FILTER.** *If (A) holds, an ensemble containing a rigid refinement-discrete member cannot
>   hide anything its reading channel exposes*, and gauge-transitivity forces the copy set to be all of
>   `{0,1}^S`, so for `L ≥ 6` such members are unavoidable (5760/32768 at `L=6`, measured). ⟹ any
>   successor carrier must state how it escapes that, whether or not (A) is proved.
> * ⛔ **A ruler is NOT a bolt-on device** (§6e.4f, and it is the cleanest limit on (A)): attaching
>   rulers uniformly to a 2-WL-blind graph resolves **nothing** — rook ⊔ Shrikhande stays one cell over
>   two orbits under every uniform attachment tried. Only individualization resolves it, and that uses
>   the orbit knowledge you were after. (A) is therefore **not** a general orbit oracle.
> * ⚠⚠ **What has been measured is the machinery, never the conclusion** — the conclusion is vacuous at
>   reachable `L` (`M` is complete there: 20=20, 90=90, 544=544). ⛔ Still do not write a
>   `probe_cao_washout.py` against the *fixpoint*; there is nothing there for it to see.
>
> ### ✅ WHAT IS MACHINE-CHECKED AND SURVIVES — all of it carrier-generic, none of it tied to Construction C
> | | |
> |---|---|
> | **(ii) the transfer** | `FrameTransfer.merge_of_tuple_merge` — a merge under a bounded-arity tuple colouring is a merge in the encoding's 2-WL closure. §6f **proved at `k = 2`** ⟹ ⛔ the payload search is **off** the critical path |
> | **disjoint unions** | `DisjointUnion.merge_of_blocked` (§6f.4e) — makes the refutation a **single-graph** statement and licenses cross-copy colour comparison. Non-vacuity **merges** |
> | **(α) the `k`-WL bridge** | `TupleCov.stableS_wlT` (§6f.5a α) — the **standard** `k`-WL closure is already `roundTS`-stable ⟹ `roundTS` adds nothing ⟹ **(iii) is quotable in its literature form** (*base treewidth ≥ `k+1` ⟹ the two CFI graphs are `k`-WL indistinguishable*) |
> | **(β) the augmentation price** | `AtomAugment.adequateFor_augment_iff` (§6f.5a β) — adjoining atoms costs **exactly** `Refines (pull b) extra`, an `iff` |
> | **the ensemble as a graph** | `Ensemble.eRoot`, `orbit_not_split` (the free half), `MixedCell` **stated only** |
> ✅ Gate = **132 modules, ~239–264 s**, all axiom-clean. ⚠ Count with `grep -cE '^  ChainDescent' scripts/build.sh`.
>
> ### ⛔⛔ WHAT IS DEAD — DO NOT RESTART ANY OF THESE
> ⚠ **Read this list as conditional where it says so.** Several entries died *because* (A) was
> believed; with (A) withdrawn to "argued", they are suspended rather than buried.
> * **R1** (round-indexed induction) and **R3** (`M⁺ = M + Φ`) — §6e.4a/§6e.4c. R3 additionally
>   re-opens (ii) at a priced cost (§6f.5a β). ⚠⚠ **Both deaths are CONDITIONAL ON (A).** They follow
>   from *"§6d.8's lemma is false"*, which follows from (A). If (A) fails, R1 and R3 are live again —
>   do not treat them as independently refuted.
> * **§6e.0's Phase 0** — *vacuous*, and unfixably so (`M`-2-WL complete at every reachable `L`).
>   ⛔ Do not re-run `probe_cao_lemma_check*` for information.
> * **The payload search** (§6f.4), the **C 2-WL**, `CFI[K5]`-full, the small-3-WL-blind-pair hunt.
> * **§6g's "the bare frame is Tinhofer"** — group individualization is false at size 4.
> * **"Guess from the ensemble's own coarser frame channel"** (my 2026-08-14 suggestion) — refuted by
>   measurement: the ensemble's frame channel is **identical** to `M`'s (§6e.4b).
> * **"The gauge vertices are transparent / outside-the-clique is 1-WL"** — same measurement refutes it;
>   the frame vertices being one **colour** is a 1-WL fact about **vertices**, and 2-WL colours **pairs**.
> * **Induction on `L`** — the statement one would induct is false at every `L`, so there is no true
>   base case to carry up.
>
> ### ✅ WHAT IS UNAFFECTED BY ALL OF THE ABOVE
> **1-WL is a solved success story:** Construction B (§2, `n=352`, 4 mixed cells) is a genuine 1-WL CAO
> counterexample, and Construction C at rung 1 (§6, `n=229,406`, 100 mixed cells) is a second one.
> Every 2026-08-15 negative result is about **rung 2 only**.
>
> ### ▶ IF YOU PICK THIS UP
> Read **§0** (the hypothesis) → **§6e.4d** (the case for (A)) → **§6e.4e** (the case for (B), and the
> symmetry of the evidence) → **§6e.4f** (the experiments) → **§6e.4g** (the decision procedure) →
> **§8a** (the Lean layer + the paid-for trap list).
> ⛔⛔ **Do not add prose to this file.** The disjunction has had three sessions of argument on each
> side and is no closer; only a theorem or an experiment moves it. §6e.4g lists four, all verifiable.
> ⚠ Construction C is **not** closed — that verdict was withdrawn. It is undecided, and which way it
> falls is exactly the (A)/(B) question.

> ### ▶▶ 2026-08-13 REVIEW — the two changes that got it here. Read §6f and the R1 box in §6e.5.
> **1. ★★★ The encoding's WL gain is BOUNDED — by a proof, not a measurement (§6f).** `M(G)` is a
> fixed-dimension FO interpretation of `G`, uniform in `L`, so `M`-2-WL ≼ bare-8-WL (crude; likely 4).
> ⟹ **CFI over a treewidth-9 base is *guaranteed* to merge, and is never computed.** The refutation
> needs **no payload search and no big 2-WL run**: ⛔ `CFI[K5]`-full, the C 2-WL, and the hunt for a
> small 3-WL-blind pair are all **downgraded to constant-pinning** (§6f.4). It also scales to every
> fixed `k`, and it makes §6c's `GI ∈ P` characterization **vacuous** for WL-based propagation.
> **2. ⚠⚠ R1's premise was untested and half of it is FALSE (§6e.5 box).** There is **no** round offset
> with `E^{(r)} = M^{(r+s)}` — measured. But the **one-sided** invariant `M^{(r)} ⊑ E^{(r)}` holds at
> every round with slack, and it is exactly the direction §6d.1 consumes. ⟹ **the refutation never
> needed the collapse to be *exact*.** State R1 one-sided; promote **R3** to a co-equal first target.
> ⟹ **the only thing left on the critical path is (i) = §6e.4.** Everything else is now argued or done.

> ### ▶ IF YOU DO ONE THING
> **Read §6d, then §6e.** The ensemble's 2-WL colouring of a copy **collapses to that copy's own
> `L²`-vertex frame encoding** — measured exactly, on every channel, at `L = 4`. That makes the
> faithful object poly-size (`L=16 → 256` vertices), unblocks every measurement this doc was stuck on,
> and **reinstates** §4's and §5.1's kills (§6a/§3.2c indict the **`shared`**-frame model, not the
> `disjoint` one, which is what those sections measured).
>
> **What is proved vs open, precisely.** Proved for all `L`: frame–frame pairs carry **≤ 12** colours
> (§6d.2a). Open: the **cross-copy averaging** half (§6d.2(b)) — proved at round 1 (§6e.3), validated
> at `L = 4` **and `L = 5`** (§6e.0, which is `M`-only so it runs where the ensemble cannot), and the
> single gap is §6e.4. ⚠ An intermediate verdict called the collapse *"false at 1-WL"*; that was an
> artefact of **not freezing the frame vertices** and is **withdrawn** — with the freeze the model is
> level-uniform (§6d.5).
>
> ⛔ **Direction discipline, and it governs every use:** only a **MERGE** under the `M` model refutes
> anything (§6d.1, machine-checked as `CaoCollapse.merge_of_stable_merge`). Every separation on record
> rules out *that payload* and says nothing about the scheme.

> ### ⛔ WHAT NOT TO DO
> * Do **not** quote §5's admission test as an `iff` — only *fails ⟹ dies* is supported (§5, §9).
> * Do **not** repeat §6's inference *"the ensemble is passive"*. It is **withdrawn** (§6a): the
>   ensemble is far coarser than the model, and the witness pair could not have detected it.
> * ⚠⚠ Do **not** carry §6a/§3.2c's *"the kills are model claims"* as written — **narrowed by §6d.4**.
>   It indicts the **`shared`**-frame two-copy model only; the `disjoint` model is `M(G) ⊔ M(H)` and
>   §6d measures that to reproduce the ensemble. §4/§5.1 are reinstated, modulo §6d.2(b).
> * ⛔ Do **not** treat a **separation** in the `M` model as evidence of anything (§6d.1): the bound
>   direction only carries **merges**. `CaoCollapse.merge_of_stable_merge` is the machine-checked form.
> * ⛔ Do **not** spend effort on a faster 2-WL for a *shared-frame* object, nor on a smaller **copy
>   set** (§3.2d: none is faithful), nor on an *exact poly simulation* of the ensemble (§6c.2: that
>   **is** `GI ∈ P`).
> * Do **not** measure **subdivision** and conclude anything about the construction: `CFI[K4]`
>   survives subdivision and dies under the real all-pairs encoding (§5.1).
> * Do **not** re-derive *"the original two-cube design was broken"* — that was a modelling error of
>   mine, corrected in §3.2a.
> * Do **not** attempt `CFI[K5]`-full in `probe_cao_cfi_frame.py`; it is ~4 h/round (§5.2).
> * Do **not** assume `Aut_v` is the group you compared against — every mixed-cell count here needs
>   a proved **upper** bound on the stabilizer (§2.3, §6), and only T2⁻ is machine-checked (§8).

---

## 0. The hypothesis being attacked — get this right first

From the CAO doc §1, verbatim in force:

> Let `χ` be the **exact `Aut(G)`-orbit partition** (so `CellsAreOrbits` holds by construction,
> *however obtained*). Individualize `v`, take the `k`-WL closure. Is every cell still a single
> `Aut(G, v)`-orbit?

**The start is the orbit partition, not the `k`-WL stable colouring.** Every failed attempt below
failed by forgetting that. It is *not* a vertex-transitivity hypothesis — §2's counterexample design
asks only for `Aut` transitive on the two cells `D` (containing `v`) and `C`, which is CAO restated.

Two necessary conditions follow, and they are the whole design space:

| | condition | why |
|---|---|---|
| **N1** | the automorphism fusing `u, w ∈ C` must **move `v`** | `u, w` share an `Aut_v`-orbit **iff** `(v,u)`, `(v,w)` share an `Aut`-orbital (CAO doc §3). A gadget whose attachment set *determines* `v` can never produce two distinct orbitals. |
| **N2** | the distinguishing relation must be **uniform at the root** | individualization converts a uniform fact into a partition (§14.3). If the split pre-exists, the CAO start hands it to WL for free. |

---

## 1. Construction A — the Q₃ carrier. ⛔ DEAD, and the death is instructive

**Spec.** 3-cube of "positions"; each edge direction `i` replaced by a distinct gadget (a `K_i` joined
to both endpoints) so the frame is rigid. Three copies `A,B,C`; a central vertex `m_v` joined to
`A_v,B_v,C_v`. Individualize `m_0`; residual group = diagonal `S₃`. Carriers attach to a triple
`{x₁,x₂,x₃}`, one corner at each of the three positions adjacent to `0`, with one copy doubled —
e.g. `g₁ = {A1,A2,B3}` vs `g₂ = {A1,B2,A3}`.

**⛔ Why it dies (proof, no computation needed).** If `α ∈ Aut(G)` has `α(g₁)=g₂` then `α` maps
`N(g₁)` to `N(g₂)`, so it fixes the position set `{e₁,e₂,e₃}` setwise, hence fixes their **unique**
common neighbour `0`, hence fixes `m₀`. So `α ∈ Aut_{m₀}`. Dichotomy with no third branch:

* **no such `α`** (the actual build — the gadgets that rigidify the corners also make directions 2 and
  3 permanently inequivalent) ⟹ `g₁,g₂` are different `Aut`-orbits, the CAO start already separates
  them, **nothing is tested**;
* **such an `α` exists** (frame symmetrised) ⟹ it fixes `m₀`, so `g₁,g₂` share an `Aut_{m₀}`-orbit and
  1-WL's merge is **correct**.

⚠⚠ **The conditional is sound; do not over-generalize it.** *"A carrier whose attachment set determines
`v` is dead"* is a theorem. *"Attachment sets must determine `v`"* is **false** — Construction B breaks
exactly that premise. This over-generalization was made and corrected in-session.

**Also fails N2**: "which direction is the odd one out" is a root-level invariant, not a uniform fact.

---

## 2. Construction B — the Q₄ complementary-pair carrier. ✅ **A REAL 1-WL COUNTEREXAMPLE**

### 2.1 The idea that makes it work

In `Q_c`, `p` and its complement `p̄ = p ⊕ 1…1` differ in **every** direction, so the pairing `p ↔ p̄`
is invariant under all direction permutations and is therefore **compatible with a rigid frame**. They
share a distance sphere around the base point only when their weights `w` and `c − w` agree, i.e.

> ### ★ `c` must be EVEN. `Q₄` is minimal — this is impossible in `Q₃`.

At weight 2 in `Q₄` the six positions form three complementary pairs, and the quadruple
`Q₀ = {1100, 0011, 1010, 0101}` is a coset of the Klein group `V = {0000, 1111, 0110, 1001}`.
`Q₀`'s common-distance-2 set is `V` itself — **four** candidates, so the attachment set does **not**
pin `m₀`, and N1 is satisfiable.

### 2.2 Spec (as built and measured)

* positions `F₂⁴`; direction `i` (0–3) replaced by a gadget clique on `i+1` vertices joined to both
  endpoints ⟹ frame rigid, `Aut` on one copy = the 16 translations, acting **regularly**;
* three copies `A,B,C`; central vertex `m_v ~ A_v,B_v,C_v`;
* **carriers**: for each coset `R` of `V`, `R` splits into two complementary pairs; a carrier attaches
  to one corner at each of `R`'s four positions, with one copy **doubled on one whole pair** and the
  other two copies on the other pair. 12 patterns per coset × 4 cosets = **48 carriers**.

`n = 352` — 16 centrals, 48 corners, 240 gadget middles, 48 carriers.

### 2.3 Measured — `scratchpad/probe_cao_hypercube.py`

```
Aut-orbits at the root : centrals [16]  corners [48]  carriers [48]   <- CAO start is coarse
g1, g2 same Aut-orbit  : True
   witness             : translation by 0110, sends m_0000 -> m_0110  (it MOVES the base point)
exact CAO start        : carr 48, centre 16, corner 48, mid 24/48/72/96
after individualizing m_0000:
   corner cells        : 16 x [3]   = exactly the Aut_v-orbits
   carrier cells       : 4 x [12]   each splitting [6,6] under Aut_v
   MIXED CELLS         : 4
g1,g2 same 1-WL cell True | same Aut_v-orbit False
```

with `g₁ = {A1,A1',B2,C2'}`, `g₂ = {B1,C1',A2,A2'}` in the reader's notation
(`1=1100, 1'=0011, 2=1010, 2'=0101`).

**Soundness of the two directions** — neither is a bare computation:

* *same root orbit* is witnessed by an **explicitly verified** automorphism (every generator is checked
  to be an adjacency-preserving bijection before use);
* *different `Aut_{m₀}`-orbits* needs an **upper** bound on the stabilizer, which is a proof: any `α`
  fixing `m₀` preserves the 16 position-cells (measured: those are the cells), gadgets exist only
  within a copy, and the position graph is connected ⟹ the copy permutation is constant ⟹
  `Aut_{m₀}` acts on corners and carriers exactly as the **diagonal `S₃`**;
* the start is the **true** orbit partition (centrals/corners/carriers are each a single orbit
  already; only the middles needed merging, per direction, which is their true orbit);
* the comparison group must include the **gadget-internal clique permutations** — they are in the
  stabilizer, and without them the middles report as spurious mixed cells.

### 2.4 2-WL repairs it exactly — `scratchpad/probe_cao_hypercube_2wl.py`

Reduced model (gadget → edge colour, 112 vertices), calibrated against the 352-vertex verdict first:

```
CALIBRATION 1-WL : corner 16x[3]  carrier 4x[12]  g1,g2 same cell True   (matches n=352)
2-WL (4 rounds)  : corner 16x[3]  carrier 8x[6]   separates g1,g2 True
```

⛔ **Why it cannot be lifted, and why the whole family is capped at 1-WL.** The hidden fact is
**binary** — *the two attachments at `p` and `p̄` lie in the same copy* — and 2-WL is the tool that
reads binary facts. It can read it because same-copy is 2-WL-visible: corners in one cube are joined by
gadget paths, corners in different cubes only through centrals. Raising `c` or `k` changes nothing;
a ternary coincidence is a conjunction of pairwise ones. **To beat 2-WL the copy relation itself would
have to be invisible — which is a CFI gauge**, and that is Construction C.

### 2.5 Standing worth

⚠ **The ledger does not move.** 1-WL CAO propagation was already refuted four times (CAO doc §STATUS:
`net(Z₄)`, Shrikhande n=16, Chang-2, `Cay(Z₁₂⋊₅Z₂)`, plus CFI over a random cubic base). B is the
**fifth**, at `n = 352`. Its value is that it is **designed and parametrized**: it answers a question
the doc never asked — *a 1-WL CAO failure can be built to order, with the mechanism chosen in advance*.

---

## 3. Construction C — the gauge/payload ensemble (the 2-WL attempt)

### 3.1 What it is, in one line

**A CFI construction with a `Z₂⁴` gauge group per slot.** The cubes are the gauge (translation acts
regularly on corners), the payload copies are indexed by gauge choices, the central vertices *are* the
gauge, and individualizing one fixes the gauge globally — which is what turns "which corner" into an
absolute **edge type**. The combinatorial explosion is the gauge orbit, not decoration.

**Spec.** A `K_n` payload (`n = 16` for the Shrikhande/rook attempt). Each of the `C(n,2)` slots owns
cubes; a copy attaches its label-`i` and label-`j` vertices to a corner pair of slot `{i,j}`, and the
corner pair read *after individualization* is the edge type (connected / disconnected). All copies are
present, so **every graph on the label set is carried simultaneously**.

### 3.2 ★ The gauge-invariance condition — check this before building anything

Translating a cube shifts the corner positions at **both** ends of its slot by the same `t`, so the
gauge-invariant of a slot is

```
δ = p ⊕ p'          (positions of the two attached payload vertices)
```

> **The root is one orbit ⟺ `δ_connected = δ_disconnected`, i.e. `1 ⊕ 1' = 2 ⊕ 2'`.**

If they differ, `δ` is a gauge invariant, the two payload copies sit in different `Aut`-orbits at the
root, and **CAO fails at the root** — Construction A's death, one level up. If they are equal, a single
cube's gauge move flips one slot's type, the gauge acts transitively on all colourings, and the root
genuinely is one orbit. Using complementary pairs (`X` and `X'` opposite corners) satisfies it by
construction, since every complementary pair has `δ = 1…1`.

### 3.2a ★ THE GADGET REDUCTION — one cube per slot, and what the doubling was really for

**Reduction (reader, 2026-08-12, verified here).** The two cubes per slot — present so the encoding
is reversible (`1→1'` vs `1'→1`) — halve to **one cube**, by attaching **both** payload endpoints to
**both** corners of the pair. Symmetric in `i, j` by construction.

Verified in two parts.

**(a) The frame algebra still works** (`scratchpad/probe_cao_gadget_check.py`): the `Q₄` gauge is
**transitive on the 8 unordered complementary pairs** (stabilizer `{0000, 1111}`, order 2, so
`16/2 = 8` types), and `δ = p ⊕ p'` is **constant `1111`** across every complementary pair. ⟹ the
root stays one orbit, and ★ **§3.2's `δ` condition becomes AUTOMATIC** — using complementary pairs,
which the `Q₄` parity insight already forced, discharges it. It stops being a design obligation.

**(b) What the doubling was actually load-bearing for** — and it is **not** root symmetry
(`scratchpad/probe_cao_gadget_variants.py`, small ensemble, `L = 4`):

| frame shape | gauge is an aut | transposition is an aut | it fixes `m(0)` | |
|---|---|---|---|---|
| **both-to-both** (one cube) | ✓ | ✓ | ✓ | **PASS** |
| one cube, ordered, `m` holds one corner | ✓ | ✗ | — | **FAIL** |
| two cubes, opposite orientations (the original) | ✓ | ✓ | ✓ | **PASS** |

> ### ★★ The real obligation: `m` must hold exactly ONE corner per cube — that is what makes it a
> gauge choice — and the label transposition must still be an automorphism **fixing `m`**, or
> `Aut_m` loses its transpositions and **T4 fails**.
> The original doubling buys that by letting the transposition **swap the cubes**. Both-to-both buys
> it more cheaply: the transposition then fixes the frame **pointwise**, so it fixes every `m(g)`
> outright. ⟹ the reduction is not a convenience — it makes T4 nearly trivial.

⚠⚠ **A modelling trap, hit here:** the first run reported the two-cube original as **FAIL**. That was
wrong — the transposition there must **swap the cubes**, not swap the ends within a cube, and mapping
ends breaks `m`. Do not re-derive "the original design was broken"; it was the model that was.

### 3.2b ★★ THE GAUGE REDUCES TO **TWO VERTICES** PER SLOT — and that is what rung 1 already is

**Reduction (reader, 2026-08-13).** Drop the `Q_c` cube entirely. A slot owns a **connected pair**
`f(k,0) ~ f(k,1)`; the gauge is the swap, so the gauge group is `(Z₂)^d` with `d = C(L,2)` slots; a
**central** `m(g)`, one per `g ∈ {0,1}^d`, joins `f(k, g_k)` for every `k`; and a copy attaches **both**
endpoints of slot `{i,j}` to the **same** frame vertex `f(k, c_k)`.

> ### ★★★ This is exactly what `probe_cao_ensemble.py` builds. Every measurement in §6, §6a and §6b is therefore a measurement of the **simplified** design, not of a toy rung.

**Nothing the design uses is lost**, and each obligation is discharged more cheaply than before:

| obligation | under the cube | under the pair |
|---|---|---|
| root is one orbit (**T1**) | gauge transitive on copies | same — and ★ `CaoEnsemble.lean`'s `Col = Slot → Bool` is *already* this gauge, so **T1 is machine-checked for the simplified design**, not the cube (`gact_transitive`) |
| one individualization kills the gauge (**T2⁻**) | gauge acts freely | same — `gact_eq_self_iff`, also already proved at `Slot → Bool` |
| the `δ` condition (§3.2) | needs complementary pairs, needs `c` **even** (§2.1) | **vacuous** — a 2-element gauge has one non-trivial element per slot |
| transposition fixes `m` (§3.2a) | needs both-to-both, or two cubes | **automatic** — both endpoints attach to the *same* frame vertex, so a label transposition fixes the frame pointwise |
| `Aut_m` = the label group (**T2⁺**) | `Aut(T(L)) = S_L` | unchanged |

⚠ §2.1's *"`c` must be EVEN"* is a **Construction B carrier** requirement and does not transfer here;
Construction C never needed it. The relaxation the reduction buys — no longer caring whether several
same-orbit vertices are individualized together — is not used by the design either: a single `m(0)`
still rigidifies the whole gauge, and that is precisely `gact_eq_self_iff`.

**Sizing.** `|V| = L·2^d + 2^d + 2d`, `d = C(L,2)`. `L=4 → 332` · `L=6 → 229,406` · `L=16 → 17·2^120`.
⚠ The reduction shrinks the per-copy cost, **not the `2^d` copy count**, which is the binding term —
so it does not by itself put a 16-label payload in reach. What it does buy is §3.2c.

### 3.2c ★★★ WITH THE 2-VERTEX GAUGE THE MODEL GAP IS ONLY TWO CHANNELS — AND ONE OF THEM IS EMPTY

Because a slot's frame vertex is now literally the triangle-frame test's **typed edge vertex**, just
shared, the whole distance between the real object and §4's admission-test model collapses to two
differences: **sharing** and **the centrals**. §6a.1 listed both and measured neither. Both are now
measured — `scratchpad/probe_cao_gauge2_ablate.py`, `L = 4`, at **2-WL**:

```
FULL     all 64 copies + all 64 centrals, m(0) individualized   332 v, 4 rounds, 5344 pair colours
ABLATED  all 64 copies, NO centrals, frame types given          268 v, 4 rounds, 3324 pair colours

channel (ii) centrals : FULL (2992 colours) vs ABLATED (2992) -> IDENTICAL
channel (i)  sharing  : 1936 / 2016 copy pairs -> TWO-COPY model strictly FINER than FULL
                          80 / 2016 copy pairs -> identical
```

> ### ⛔ **The centrals are worth NOTHING at 2-WL.** Their entire contribution to the payload-pair partition is making the frame types absolute. ⟹ **§6a.1's second channel is EMPTY**, and a faithful test object does not need the `2^d` centrals at all — retracting half of §6a.1's caution.
> ### ⛔⛔ **Sharing makes the model DISAGREE at 2-WL, on 96% of copy pairs.**

⚠ **Precision, and it matters — `scratchpad/probe_cao_gauge2_diag.py`.** The 1936 above is the
partition of payload **pairs**. CAO is a statement about the **vertex** partition, and §4/§5.1's kills
are stated as a **separation verdict**, so both were re-measured at those two levels:

| level | two-copy model vs full ensemble, over 2016 copy pairs |
|---|---|
| pair-colour partition | **1936** strictly finer · 80 identical |
| **diagonal (vertex) partition** | **1864 differ** · 152 agree |
| **separation verdict** | 1944 agree · **72 differ** |

★★ The 72 all go the **other way**. At `L = 4` the ensemble has 0 mixed cells, so it separates *every*
non-isomorphic copy pair; and an isomorphism `π : G_c → G_{c'}` always extends to an automorphism of
the two-copy model exchanging the copies (`π` permutes slots, types are absolute), so the model never
separates an isomorphic pair. ⟹ those 72 are pairs the **model FAILS to separate and the ensemble
does**.

> ### ⛔⛔⛔ So the **shared**-frame two-copy model **over-separates on the diagonal AND under-separates on the verdict**. Not stronger, not weaker — **INCOMPARABLE**, measured at the level the kills are stated at.

⚠⚠ **SCOPE, corrected by §6d.** Everything measured in §3.2c and §3.2d uses a **shared** frame
(`build([c,c'], …)` puts one frame under both copies). §6d then found that the ensemble's 2-WL
collapses to a **single-copy** model, and that `M(G) ⊔ M(H)` — a **disjoint** pair — reproduces the
ensemble *exactly* at `L = 4`. ⟹ **this section indicts the `shared` rows of §4.2, not the `disjoint`
rows, and not §5.1.** I originally wrote the conclusion as *"§4 and §5.1 are confirmed model claims"*;
that is too broad and is withdrawn in favour of §6d.4.

★ Together these say the faithful object is **`k` copies + one shared frame + absolute types** — no
centrals. So the question that decides whether the kills can be re-run honestly is *how large must
`k` be*. It was measured immediately, and the answer is the worst one available.

### 3.2d ⛔⛔⛔ THE COPY SET DOES NOT SATURATE — `k = 2^d` IS REQUIRED, AND THAT CLOSES THE TOOLING ROUTE

`scratchpad/probe_cao_gauge2_saturate.py`, `L = 4` (`2^6 = 64` copies). Fix a copy pair, grow the
copy set, and ask when the induced 2-WL partition on that pair's payload pairs **matches the full
ensemble's**. Both ways of growing it were tried — arbitrary subsets, and §3.4's own **gauge-closed**
subsets:

```
A. RANDOM subsets        k =  2  3  4  6  8 12 16 24 32 48 64
   4 / 4 copy pairs           ·  ·  ·  ·  ·  ·  ·  ·  ·  ·  ✓     (matches ONLY at the full 64)

B. GAUGE-CLOSED subsets  |H| =  2   4   8  16  32  64
   3 / 4 copy pairs             ·   ·   ·   ·   ·   ✓
   1 / 4 copy pairs             ·   ·   ·   ·   ✓   ✓            (one index-2 subgroup sufficed)
```

> ### ⛔⛔⛔ There is no small-`k` regime. Faithfulness needs the complete gauge orbit — at best an index-2 subgroup of it, and only sometimes.
> ⟹ a faithful re-test of a **16-label** payload (Shrikhande/rook, `CFI[K4]`) needs `d = C(16,2) = 120`
> and therefore `~2^120` copies. **This is not a constant-factor problem and no implementation fixes
> it.** §5.2's *"get a C 2-WL, it is 2–3 min/round"* addresses the wrong bottleneck: a faster prober
> makes the **unfaithful** model cheaper, not the faithful one reachable.
>
> ⚠⚠ **RE-REVERSED BY §6d — read that before acting on this box.** §6d found the ensemble's 2-WL on a
> copy collapses to a **poly-size** single-copy object, so the faithful test does *not* need `2^d`
> copies after all and **a C 2-WL is worth building**. What survives here is narrower and still true:
> **no restriction of the copy set is faithful**, so a *shared-frame* object cannot be shrunk — the
> escape is that you never needed one.

⚠ **§3.4 is corrected by this.** Its *"you only have to gauge the slots where the two target graphs
differ, so `2^d` copies"* is true as a statement about **preserving the gauge symmetry**, and ladder B
is exactly that construction — but gauge-closure turns out **not** to be the faithfulness criterion.
The two-copy model is *already* gauge-closed (`H = ⟨c ⊕ c'⟩`, order 2) and it is the thing that
over-separates. So §3.4's sizing argument does not license a small test object.

> ### ▶▶ WHAT THIS LEAVES — the route is ANALYTIC, not computational
> §6a derived the ensemble's **1-WL** colouring in closed form (`(degree sequence, own degree)`) and
> settled that level for **all** `L` at once, with no build. The same is now the only available move
> at 2-WL, and ★ the 2-vertex gauge is precisely what makes it plausible: the object is a payload
> clique, one connected pair per slot, and (measured removable) centrals. Two pieces are already in
> hand — **a central is never a common neighbour of two payload vertices** (it touches only frame),
> which is *why* §3.2c's ablation came out empty; and **§6b** fixes what the payload-payload pairs
> see at round 1. What is missing is the payload–frame and frame–frame pair colours at the fixpoint.

### 3.3 What the construction reduces to

`Aut = gauge ⋊ (label symmetries)`; after individualizing `m` the gauge dies and `Aut_m` is the label
group, so **`Aut_m`-orbits of copies = isomorphism classes of graphs on the label set**. Hence

> ### CAO propagation fails at `k`-WL ⟸ encoded-`k`-WL is not a complete isomorphism invariant on graphs over the label set.

Because the ensemble carries every payload, **you never have to choose the payload**: if *any* two
non-isomorphic graphs are fused, CAO fails. Since no fixed WL level is a complete invariant (CFI),
this is the strongest form of the program, and **nothing measured here refutes it.**

### 3.4 Sizing — you do not need `16^240`

The copy set only has to be closed under the gauge, and you only have to gauge the slots where the two
target graphs differ: gauge `d = |E(G) △ E(H)|` slots ⟹ `2^d` copies. For `C6` vs `2C3` (labelled
`12,23,34,45,56,16` vs `12,13,23,45,46,56`) the symmetric difference is `{34,16,13,46}`, so `d = 4` →
**16 copies**, a ~142-vertex test object.

⚠⚠ **But restricting the gauge is exactly the leak the design guards against** — a gauge that touches
only some corners is visible pre-individualization. Preserving *every* symmetry costs `16^{C(n,2)}`
copies and is untestable at any `n`. **The frozen-frame abstraction (§4) is the way out of that bind**,
and it is what the only decisive test used.

---

## 4. ⛔ The Shrikhande/rook payload is DEAD — measured

> ⚠⚠ **This heading changed twice on 2026-08-13; this is the net state.** It was downgraded to
> *"dies in the two-copy model"* by §6a, then **restored** by §6d.4: §6a indicts the **`shared`**-frame
> variant, while §4.2's `disjoint` rows are `M(G) ⊔ M(H)`, which §6d measures to reproduce the
> ensemble. ⚠ Two live caveats remain: the restoration is modulo §6d.2(b), and by §6d.1 a
> **separation** rules out *this payload* without being evidence about the scheme.

### 4.1 The premise, checked — `scratchpad/probe_cao_payload_pair.py`

```
A. 2-WL, plain graphs              : equivalent = True     <- the pair IS 2-WL-blind
B. 2-WL, one vertex individualized : equivalent = False
     Shrikhande extension cells [1, 3, 6, 6]
     rook 4x4   extension cells [1, 6, 9]
```

★ **The payload property that matters is not "2-WL-blind" but "2-WL-blind under the encoding".**
One individualized vertex is enough to separate the bare pair — those are §14.1's numbers.
Construction C individualizes the **gauge**, not a payload vertex, so B does not by itself kill it;
it sets the bar: **no payload vertex and no payload label may become pinned.**
⚠ The subdivided cases (C/D) in that probe were **never run** — the job was killed. Do not cite them.

### 4.2 The triangle-frame test — `scratchpad/probe_cao_triangle_frame.py`

`K16` + a frame vertex on **every** pair, coloured **only** by edge type (never given an identity of
its own — the faithful abstraction of the shared, ensemble-symmetric frame). 272 vertices, no component
marker, so separation has to be earned.

| model | frame constraint | control (S vs S) | Shrikhande vs rook |
|---|---|---|---|
| disjoint | none | not separated | **separated** (5 rounds, 217 colours) |
| disjoint | frame-frame pairs frozen, orbit-level | not separated | **separated** (3 rounds) |
| disjoint | frame-frame frozen, **minimal** | not separated | **separated** (5 rounds, 75 colours) |
| shared frame | none | not separated | **separated** (5 rounds, 1408 colours) |
| shared frame | frozen, orbit-level | not separated | **separated** (4 rounds, 352 colours) |
| shared frame | frozen, **minimal** | not separated | **separated** (5 rounds, 246 colours) |

★ The **minimal** rows are the load-bearing ones: there the frame-frame pairs know only their two
types — no same-cube, no share-a-label — which is strictly **coarser** than the `Aut_m`-orbit partition
of those pairs, so that model hands 2-WL strictly *less* than the real object can. It still separates.

⚠ The orbit-level freeze produced *more* colours than no freeze (16398 vs 217) because its atom is
finer at round 0 (it hands over "share a label" immediately). It is therefore neither uniformly
stronger nor weaker; the **minimal** rows are the ones to quote.

### 4.3 The mechanism, and it is not a modelling artefact

> ### ★★ 2-WL cannot distinguish Shrikhande from rook 4×4, but it CAN distinguish their frame-encoded versions.
> ⚠ "Triangle-extended" throughout §4 means the **full** encoding — a frame vertex on *every* pair,
> clique payload. It does **not** mean subdivision, and §5.1 shows the two are not interchangeable.

Promoting edges to vertices is what does it: a **pair** of frame vertices is a pair of edges, hence up
to **four** payload vertices, so 2-WL on the extension carries a 4-vertex window on the payload.
Shrikhande and rook differ exactly at four vertices — measured:

```
K4 count   Shrikhande 0    rook 4x4 8   (4 rows + 4 columns)
```

⛔ **The skip-recolouring rule cannot repair this.** That rule constrains the frame's *vertex* cells;
the information lives in *pair* colours. Frame-frame pairs were frozen completely and it still
separated, so the channel is the **payload-frame** pairs — which cannot be frozen without deleting the
encoding itself, since they are what carries the edge type.

---

## 5. ★★★ THE PAYLOAD ADMISSION TEST — what the frame hides, and what it cannot

**The design intent** (reader, and it is the right frame for the whole scheme): the edge vertices are
built to obscure as much as possible of the fact that they *are* edges. Their 1-WL content is forced
static; their 2-WL+ content is still computed, but the only place it can say anything is **inside the
payload's own edge set** — stepping outside lands either in the full ensemble (every graph present, so
symmetric by construction) or in the cube (symmetric by construction). So the extra strength available
to 2-WL is exactly *2-WL on the encoded payload*. Hence:

> ### ▶ A candidate payload pair must be 2-WL-resistant **after the FULL frame encoding**, not before.
> **"Full" is load-bearing and is not edge-bisection.** The encoding is: payload copy = a **clique**,
> a **typed frame vertex on every pair** (edges *and* non-edges), adjacency carried only by the types.
> ⛔⛔ **Subdivision is NOT a proxy for it** — `CFI[K4]` survives subdivision and dies under the full
> encoding (§5.1). The criterion was first phrased as *"still 2-WL-resistant after edge-bisection"*;
> that phrasing is what motivated the test, but the measurement showed the two encodings disagree, so
> **only the full form is the criterion.**
> ⚠ **Stated as a NECESSARY condition, and only that direction is supported.** *Fails the test ⟹
> dies* is what §4.2/§4.3 and §5.1 measure, and it is the direction that makes it a useful filter —
> apply it to any candidate **before** building anything around it. **The converse (*passes ⟹
> survives*) is a design conjecture, not a theorem**: it assumes the ensemble contributes nothing (§6),
> and nothing here bounds what the encoded closure can compute. Do not quote this as an `iff`.

**▶ The measured calibration is §5.2's table — read it there, not here.** Two facts about it belong
with the test itself:

⚠⚠ **The cost is NOT a constant — an earlier "the encoding hands WL exactly one extra level" is
RETRACTED.** At `k = 1` the encoding buys nothing: 1-WL's state is a single vertex and its aggregation
is a multiset, so it can see an edge but cannot correlate two of them. At `k = 2` the state is a pair
of frame vertices = four payload vertices, and that is where the gain appears. The cost scales with `k`
because a `k`-tuple of frame vertices spans up to `2k` payload vertices.

⚠ **Every measured gain is a lower bound only.** A pair that falls to `(k+1)`-WL bare cannot exhibit
a gain larger than one level however strong the encoding is, and both rung-2 pairs on record
(Shrikhande/rook, `CFI[K4]`) are exactly that. **Nothing measured bounds the cost above.** Budget
generously: *"a payload that beats 4-WL to beat 2-WL"* is a safe floor, not a target.

**⛔⛔ THE ASSUMPTION INSIDE THE ADMISSION TEST HAS FAILED ITS AUDIT — §6a, 2026-08-13.** The test
assumes the two-copy private-frame model stands in for the ensemble. It does not: at 1-WL the model
gives **538 cells / 6 mixed** where the ensemble gives **292 / 100**, and at 2-WL the two are
**incomparable** (each has a channel the other lacks — §6a.1). §6's *"measured TRUE at rung 1"* is
withdrawn; its witness `C6`/`2C3` is 2-regular and so could not have detected the disagreement.
⚠⚠ **NARROWED THE SAME DAY BY §6d — read that before acting on this paragraph.** The audit indicts
the **`shared`**-frame two-copy model; the `disjoint` model is `M(G) ⊔ M(H)`, and §6d measures *that*
to reproduce the ensemble exactly. So §5.1's rows (which are `disjoint`) stand, modulo §6d.2(b).
⛔ What does **not** survive in any model is the *direction*: a **separation** under the test proves
nothing about the ensemble; only a **merge** does (§6d.1). The model-free clause is §6b's weaker one:
*a payload pair separated by **bare** 2-WL is dead.*

### 5.1 ⛔ CFI PAYLOADS — `CFI[K4]` TESTED AND DEAD (⚠ direction: §6d.1)

`scratchpad/probe_cao_cfi_frame.py`. Both CFI pairs are checked 2-WL-blind **bare** first, so the
test is not vacuous: `CFI[K4]` (`n = 28`) and `CFI[K5]` (`n = 60`), plain vs twisted, **equivalent =
True**. `CFI[K4]` is the cheapest pair that is 2-WL-blind at all (base treewidth 3 > 2), which is why
it was tried first — ⚠ **and it does not survive; see the verdict below.** An earlier version of this
section read *"`CFI[K4]` already suffices, so the payload costs `n = 28`"* — **that is REFUTED**, and
the surviving content of it is only that `K4` is where to *start* testing, not where to stop.

| payload | encoding | union `|V|` | control | 2-WL separates? |
|---|---|---|---|---|
| `CFI[K4]` | subdivision (edges only) | 152 | clean | ⭕ **No — survives** |
| `CFI[K5]` | subdivision (edges only) | 440 | clean | ⭕ **No — survives** |
| `CFI[K4]` | full, ⚠ **non-faithful variant** (see below) | 812 | clean | ⛔ Yes — separates, diverging at **round 2** |
| **`CFI[K4]`** | **full, faithful** (clique payload) | **812** | **clean** | ⛔⛔ **YES — SEPARATES**, diverging at **round 3**, 1848 colours vs the control's 567 |
| `CFI[K5]` | full | 3660 | — | ⛔ out of reach (`n³` time, `n²` signatures) |

> ### ⛔⛔ VERDICT: `CFI[K4]` FAILS the payload admission test.
> The full all-pairs frame cracks a pair that is 2-WL-blind bare, so **encoded-2-WL ≥ bare-3-WL** on
> this pair, and subdivision was indeed the weak encoding: the same pair survives it (row 1) and dies
> here. ⚠ An intermediate 2026-08-13 verdict downgraded this to *"a statement about the model"*;
> **§6d narrowed that** — the encoding used here is `disjoint`, which §6d measures to reproduce the
> ensemble. It stands, modulo §6d.2(b). ⛔ But it is a **separation**, so by §6d.1 it only rules this
> payload out; it is not evidence about the scheme.

**✅ The premise of this section is now reproducible** — `scratchpad/probe_cao_cfi_bare.py`. It was
asserted here and measured only ad hoc, which left the whole section unfalsifiable: if the pair were
not 2-WL-blind bare, the frame separating it would mean nothing. Measured:
`CFI[K4]` `n=28` stable after 3 rounds at 14 pair colours, `CFI[K5]` `n=60` after 3 rounds at 19 —
**both plain ~ twisted equivalent = True**.

⚠⚠ **THE FAITHFULNESS DEFECT IN ROW 3 — found after that run, kept only as provenance.** It retained
the payload's **own edges** alongside the typed frame vertices; Construction C makes the copy a
**complete** graph with adjacency living *only* in the types (as `probe_cao_triangle_frame.py` does).
So it handed 2-WL the adjacency **twice** — atomically at round 0 *and* through the frame. Fixed in
`encode`; row 4 is the verdict. ★ **The two rows agree and the fix behaved exactly as predicted**: the
faithful model diverges one round *later* (3 vs 2) and reaches the same 1848 colours, which is what
removing a duplicated round-0 signal should do. Raw output kept at `scratchpad/cfi_frame_unfaithful.out`.

### 5.2 ▶ WHERE THE CALIBRATION NOW STANDS — and the one measurement that would settle it

| pair | bare WL dimension | encoded, tested at | encoding | result |
|---|---|---|---|---|
| `C6` / `2C3` | 2 (1-WL blind) | 1-WL | ⚠ full **+ payload edges** | survives ⟹ **gain 0** |
| Shrikhande / rook | 3 (2-WL blind) | 2-WL | full | separates ⟹ **gain ≥ 1** |
| `CFI[K4]` | 3 (2-WL blind) | 2-WL | subdivision | survives — ⚠ weak encoding, not comparable |
| `CFI[K4]` | 3 (2-WL blind) | 2-WL | **full** | separates ⟹ **gain ≥ 1** |
| `CFI[K5]` | 4 (3-WL blind) | 2-WL | subdivision | survives — ⚠ weak encoding, not comparable |
| **`CFI[K5]`** | **4 (3-WL blind)** | **2-WL** | **full** | **▶ NOT RUN — the decisive cell** |

Every row has a same-pair-against-itself control that came out unseparated, so no row is a machinery
artefact. The `full` encoding is the construction's own (**clique** payload, a typed frame vertex on
every pair); `subdivision` is edges-only and is kept only for the contrast in §5.1.

⚠ **The `C6`/`2C3` row used the same non-faithful variant as §5.1's row 3** (frame on every pair, but
the payload keeping its own edges instead of being a clique). **Its conclusion is safe anyway, and
only because it is a survival**: that model is strictly *stronger* than the construction's, so failing
to separate there means failing to separate under the faithful encoding a fortiori. ⛔ The same
reasoning does **not** rescue a separation — which is exactly why §5.1's row 3 had to be re-run and
row 4 is the verdict. **If you re-derive the rung-1 row, use the clique payload.**

> ### ⚠⚠ SUPERSEDED BY §6f — **the gain IS bounded above**, by an interpretation argument and with no
> measurement: `M`-2-WL ≼ bare-8-WL, uniformly in `L`. The paragraph below is kept as the record of
> why `CFI[K5]`-full was once "the decisive cell"; it is now **constant-pinning, not decisive**, and
> §6f.4 says do not build tooling for it.

Both rung-2 points give `≥ 1` and **neither bounds the gain above**, so the two live readings are
still open: *"costs exactly one level"* (⟹ `CFI[K5]` is the payload, and the programme is sound but
huge) versus the **doubling** reading, *encoded-`k`-WL ≈ bare-`2k`-WL* (⟹ `CFI[K5]` dies too and the
payload must be 4-WL-blind, i.e. CFI over a treewidth-5 base). A 3-WL-blind pair tested at encoded
2-WL separates them, and `CFI[K5]` full at `n = 3660` is the only instance in hand.

**▶ To make that run possible**, one of: (a) a C implementation of the counting-signature 2-WL —
`n³ ≈ 4.9×10^10` simple ops per round is ~2–3 min/round in C against ~4 h in Python; (b) a
**smaller 3-WL-blind pair** than `CFI[K5]`'s 60 vertices, which would shrink `C(n,2)` quadratically
and is the higher-leverage search; (c) an algorithmic 2-WL (partition-refinement rather than
recolour-everything). ⛔ Do **not** attempt it in the current Python prober.

⚠⚠ **The two ⭕ rows are NOT the admission test being passed.** They use **subdivision**; Construction
C types **every pair**, edges and non-edges alike — that is the `full` row, and the same `CFI[K4]`
that survives subdivision **dies** there. ⟹ **subdivision is the weak encoding, and measuring it
answers a different question.** Keep the rows only as the contrast that establishes it.

---

## 6. THE RUNG-1 ENSEMBLE — RAN 2026-08-12. ⚠ Its verdict is WITHDRAWN by §6a

**The worry.** With every colouring present, WL gets the whole **Hamming structure on colouring
space** as a reference frame: two copies differing in a single slot agree at all the others, and that
relation is WL-visible. §3.3's reduction and §5's admission test both silently assume this contributes
nothing. It is the only unproved step in the scheme, so it was measured.

**Object** — `scratchpad/probe_cao_ensemble.py`, Construction C at rung 1 with **nothing restricted**:
6 labels, 15 slots, gauge `Z₂` per slot, **all `2^15` copies and all `2^15` central vertices**.
`|V| = 229,406`, `|E| = 1,966,095`.

```
CAO start cells : payload 196608 | frame 30 | centrals 32767 | m(0) individualized
1-WL            : stabilized in 4 rounds -> 292 payload cells
Aut_v = S_6     : 544 true orbits on the payload
MIXED CELLS     : 100        (orbits fused per cell, top 10: 9 9 8 8 8 8 7 7 7 7)
C6 copy cells [218] | 2C3 copy cells [218]
   share a 1-WL cell: True   |   share an Aut_v-orbit: False
```

> ### ⛔⛔ VERDICT WITHDRAWN 2026-08-13 — see §6a.
> It read: *"the full ensemble gives 1-WL **nothing** beyond the two-copy model"*, inferred from the
> two landing in the same cell 218. The inference is **void**: the ensemble gives 1-WL not *the same
> as* but **far less than** the two-copy model, and the witness pair is degree-regular so it could not
> have told the two apart. The **numbers above are correct and reproduce**; only the inference drawn
> from them is withdrawn.

★★ **It is still a second designed 1-WL CAO-propagation counterexample — Construction C's machinery
working end to end** — with 100 mixed cells rather than 4. ⚠ But §6a shows the payload was *not*
effectively chosen: at 1-WL this object cannot see a payload at all, so any two 6-vertex graphs with
a common degree sequence and different iso type would have served equally.

**Both group facts are proved, not assumed, and the orbit count is independently cross-checked** —
this part is untouched by §6a, and without it the 100 is unfalsifiable. The CAO start is exactly
three cells because the gauge `(Z₂)^15` and the label group `S₆` are jointly transitive on each kind
and the kinds cannot merge (degrees 10 / ~49k / 15); `Aut_{m(0)} = S₆` **exactly**, because a
stabilizing `α` preserves `m(0)`'s neighbourhood hence types, "two slots share a label" is recoverable
(disjoint slots have no common payload neighbour), `Aut(T(6)) = S₆`, and the slot permutation then
determines the action on every copy. **Burnside cross-check** of the union-find: `156` iso classes of
6-vertex graphs (known value) and `544` orbits on (graph, marked vertex) — both match exactly, and
`544` is independently reproduced by `probe_cao_ensemble_audit.py`.

---

## 6a. ⛔⛔ THE TWO-COPY MODEL IS UNFAITHFUL — AUDITED 2026-08-13

`scratchpad/probe_cao_ensemble_audit.py`, `probe_cao_ensemble_exact.py`.

**The finding, in one line.** The rung-1 ensemble's 1-WL payload partition is **exactly**

```
colour(c, i)  =  (degree sequence of G_c,  deg_{G_c}(i))
```

— verified **elementwise** against the real 229,406-vertex object, not inferred from matching counts.
It reproduces all three of §6's numbers: **292** cells, **544** orbits, **100** mixed.

**Why, structurally — and the reason is level-independent, not an artefact of rung 1.** The frame is
**shared**: 30 frame vertices carry all `2^15` copies. `S₆` is transitive on slots and `m(0)` marks
type 0, so a frame **vertex** can hold exactly **two** colours, for ever. A payload vertex `p(c,i)`
sees five clique neighbours — *all* of them, so adjacency is invisible there — plus one frame
neighbour per slot contributing only a **count of type-0**, which is `deg(i)`. Iterating adds the
multiset of the other five colours. That is the whole fixpoint.

**What that does to the two-copy model.** The admission test (§5) is calibrated on
`probe_cao_triangle_frame.py`'s `disjoint` shape, where each copy owns a **private** frame vertex per
pair — and those *do* accumulate copy-specific data. Same question, same rung, measured:

| model | payload cells | mixed cells | vs the 544 true orbits |
|---|---|---|---|
| the **real ensemble** (shared frame, all `2^15` copies) | **292** | **100** | far coarser |
| the **two-copy `disjoint` model** (private frame) | **538** | **6** | nearly exact |

> ### ⛔ The two-copy model separates ~94 orbit-fusions the real construction does not.
> It is not a conservative abstraction of the ensemble; it is a **much stronger object**.

**⚠⚠ And §6's witness could not have detected this.** `C6` and `2C3` are both **2-regular**, so they
are identical under the weakest invariant there is. A validation whose witness is degree-blind cannot
distinguish *"the ensemble equals the model"* from *"the ensemble sees only degrees"* — and it was
the second. **A single agreeing data point is not a validation of an abstraction; compare the
partitions.**

### 6a.1 At 2-WL the two are INCOMPARABLE — so neither direction transfers

⚠ Do **not** patch this by saying *"the model is stronger, so its survivals are sound"*. That rule
(§8(c)) applies to a coarser **colouring of the same graph**; the ensemble and the two-copy model are
**different graphs**, and WL power is not monotone across that. At 2-WL each has a channel the other
lacks:

| channel | two-copy model | real ensemble |
|---|---|---|
| frame–frame pairs = a 4-payload-vertex window (§4.3's stated mechanism) | **present**, copy-specific | **absent** — a frame pair is shared by *every* copy, so it cannot carry copy-specific data |
| the `2^{C(n,2)}` **central** vertices | **absent entirely** — no 2-copy model has them | ⛔ **MEASURED EMPTY 2026-08-13 (§3.2c)** — ablating every central leaves the payload-pair partition **identical**. A central touches only frame, so it is *never* a common neighbour of two payload vertices; its whole effect is making the types absolute. ⚠ This row originally read "real at 2-WL and still unmeasured" — **retracted** |

⟹ of the two channels, **one is empty and one is real**: sharing, measured to make the shared-frame
two-copy model disagree with the ensemble on **1936 / 2016** copy pairs (§3.2c).
⚠⚠ **This section originally concluded "so §4 and §5.1 are confirmed model claims". That is
WITHDRAWN by §6d.4**: those sections use the **`disjoint`** model, which is `M(G) ⊔ M(H)` and *does*
reproduce the ensemble. What this section establishes is that the **`shared`** two-copy variant is
not the construction — a narrower and still useful fact, since §4.2 has `shared` rows.

### 6a.2 ⚠ §4.3's stated mechanism does not survive its own evidence

§4.3 blames the separation on *"a pair of frame vertices = a pair of edges = four payload vertices"*.
Two facts already in this doc contradict that being the channel:

* **subdivision** also makes pairs of frame vertices span four payload vertices, yet `CFI[K4]`
  **survives** subdivision and dies under `full` (§5.1);
* the **minimal-freeze** rows (§4.2) kill the frame–frame channel outright and **still separate**.

So the 4-subset window is not the mechanism, or not the only one. §9 already flagged this as *"not
isolated by ablation"* — it is now actively **counter-indicated**, and the honest reading is that the
surviving channel is **payload–frame** pairs (a 3-subset window `{x, i, j}`), which is also the one
channel that *does* survive frame-sharing.

---

## 6b. ★★★ WHAT DOES TRANSFER: 2-WL READS THE ENCODED EDGE — proved, and measured on the real object

This is the one 2-WL statement in the doc that needs no model.

> ### ★★★ In the ensemble, `p(c,i)` and `p(c,j)` have `f({i,j}, c_{ij})` as a **common neighbour**, and after `m(0)` is individualized that vertex's type is **absolute**. An edge encoded as a typed common neighbour is exactly what 2-WL counts. ⟹ 2-WL recovers the adjacency of **every** copy at round 1, however shared and however symmetric the frame is.

**Measured — `scratchpad/probe_cao_ensemble_2wl.py`, and it is the first 2-WL measurement anywhere in
this doc on the real shared-frame, full-gauge object** (`L = 4`, `n = 332`: 256 payload, 12 frame,
64 central; the `L = 6` object is 229k and out of reach at 2-WL):

```
round 1: 27 -> 82   round 2: 82 -> 3614   round 3: 3614 -> 5344   round 4: stable
payload-pair colours on type-1 slots 20, on type-0 slots 20, overlap 0
==> 2-WL RECOVERS every copy's adjacency: True
payload vertex cells 20 | true Aut_m = S_4 orbits 20 | MIXED CELLS 0
```

**Consequences, and they are the load-bearing ones:**

1. **`encoded-2-WL ≥ bare-2-WL`, unconditionally and in the real object.** The design intent — *"the
   edge vertices obscure that they are edges"* — **fails at 2-WL by construction**. It succeeds
   completely at 1-WL (§6a: the payload is invisible), and that gap is exactly why the programme
   works at rung 1 and stalls at rung 2.
2. **§5's admission test keeps its necessary direction without the model.** *A payload pair that
   `bare-2-WL` separates is dead* is now a theorem, not a measurement in an unfaithful abstraction.
   ⚠ It is the *weaker* necessary condition than §5's; the stronger form (2-WL-resistant after the
   full encoding) still rests on the two-copy model and inherits §6a.
3. ⚠ **It does not kill the programme.** The payload pairs of interest are 2-WL-blind *bare*, so
   clause 1 does not touch them. What it removes is any hope that the frame *hides* a payload from
   2-WL — the payload must carry the whole burden itself.
4. ▶ It is the natural next **Lean** target: it needs a refiner in the Lean layer (T3's dependency)
   and it is a statement about one round, not a fixpoint.

**▶ What §6 + §6a + §6b leave.** Rung 2 is **not** settled either way, and the reason has changed.
It is *not* that the frame leaks and the ensemble does not (§6's reading — withdrawn). It is that
**at 1-WL the frame hides the payload completely** (§6a) and **at 2-WL it hides nothing at all**
(§6b), so the entire question is whether a payload can carry the burden alone, against an encoding
whose extra strength over bare 2-WL is **still unmeasured on the real object**. Every number bearing
on that extra strength (§4, §5.1, §5.2) comes from an abstraction now known to disagree with the
ensemble. ⟹ the binding constraint is **tooling that can run 2-WL on a shared-frame object**, not a
bigger payload.

---

## 6c. ★★★ THE ENSEMBLE AS A REDUCTION — *"does poly-time CAO propagation give `GI ∈ P`?"*

**Raised by the reader 2026-08-13.** ⚠ This is **not** the banned *"X ⟹ `GI∈P`, therefore X is
impossible"* argument (steers-archive), and it must not be turned into one. It asks a narrower and
legitimate question — what a CAO-propagation algorithm would *cost* — and its useful form turns out
to be the contrapositive, which refutes via a **theorem** (bounded-dimension WL is incomplete), never
via the unprovability of `GI ∈ P`.

### 6c.1 The move that makes it work: the ensemble needs NO orbit oracle

The standing objection to any "CAO gives you canonization" argument is that **reaching** a CAO
colouring needs the orbit partition, and orbit partition is poly-time equivalent to GI (Mathon). The
ensemble sidesteps it, and this is the argument's real idea:

> ### ★★★ `E(L)`'s root orbit partition is **known by construction, not computed** — §6's proof: the gauge `(Z₂)^d` and the label group `S_L` are jointly transitive on each kind, and the three kinds cannot merge on degrees. Three cells, for free, for every `L`.

Two further facts are also proved rather than computed: `Aut_{m(0)} = S_L` **exactly** (§6, via
`Aut(T(L)) = S_L`), and therefore the `Aut_{m(0)}`-orbits on payload vertices are exactly the
isomorphism classes of **(graph, marked vertex)** on `L` labels.

★ Note also that `E(L)` is **universal**: it depends only on `L`, never on the input graph. The input
merely *selects a copy*. So "Step 1" is not a computation at all.

### 6c.2 What the reduction actually establishes

Assume `k`-WL CAO propagation. Individualize `m(0)`; by hypothesis the `k`-WL cells are the
`Aut_{m(0)}`-orbits. Then:

* restricted to one copy `c`, the cells **are the `Aut(G_c)`-orbit partition** of the payload graph;
* across copies, `G_c ≅ G_{c'}` iff their copies share cells.

⟹ *if* "which cell is `p(c,i)` in" is computable in `poly(L)`, then `GI ∈ P`.

**▶ Step 3 of the reader's version is redundant.** It routes through *"the payload is now CAO, hence
Tinhofer, hence canonized by W1"*. But the orbit partition alone already gives `GI ∈ P`, so the
Tinhofer leg and its dependency on `canonizes_on_tinhofer` can be dropped. Shorter argument, one
fewer thing to prove.

> ### ⛔ **Step 2 is not a lemma — under the hypothesis it IS the conclusion.**
> A poly-time simulation of the ensemble's `k`-WL closure computes iso classes, and conversely
> `GI ∈ P` computes them. So what the argument proves is a **characterization**, not an implication:
> ```
> k-WL CAO propagation  ⟹  ( GI ∈ P  ⟺  E(L)'s k-WL closure is poly-simulable )
> ```
> ⟹ **no amount of cleverness discharges Step 2 short of solving GI**, and the simulation route can
> never be a stepping stone: any success at it *is* the whole prize.

⛔ **And the object named for Step 2 — the triangle frame — is measured to be the wrong one** (§3.2c:
incomparable on both the diagonal and the verdict; §3.2d: no copy subset saturates). A faithful
extraction must be **analytic**, not a smaller build.

### 6c.3 ★★★ THE CONTRAPOSITIVE IS THE USABLE FORM — and it is a proof strategy, not a hope

Do not chase an exact poly-time simulation. Prove an **upper bound**:

> ### ▶ `E(L)`'s `k`-WL closure on the payload `≤` some invariant already KNOWN to be incomplete.

Then the closure is not a complete isomorphism invariant, so its cells are strictly coarser than the
`Aut_{m(0)}`-orbits, so **`k`-WL CAO propagation is FALSE** — with an explicit counterexample family
and **no large computation at all**. The natural bound to aim at is `≤ bare-m-WL` for a fixed `m`,
because CFI over a base of treewidth `m+1` then supplies the witness, and CFI's incompleteness is a
**theorem**, not an open problem. ⟹ the GI-hardness observation in §6c.2 is *not* load-bearing here;
it only explains why Step 2 cannot be a stepping stone.

> ### ★★ THIS TEMPLATE HAS ALREADY BEEN EXECUTED ONCE — at 1-WL, by §6a.
> The closed form there is `(degree sequence, own degree)`, which is **weaker than bare 1-WL**. Degree
> sequence is not a complete invariant (`C6` / `2C3`), so 1-WL CAO propagation fails — for **all `L`**,
> by proof, with the witness handed to you. §6's 100 mixed cells were a *measurement* of the same
> fact; the closed form is what makes it a theorem. **The template works; only the level is open.**

**▶ So the top outstanding item (§9 A.1) is retargeted.** It asked for the *exact* 2-WL closed form. The weaker
**upper bound** suffices and is far more tractable, and §6b already supplies the matching lower bound
`ensemble-2-WL ≥ bare-2-WL`. The open interval is `2 ≤ m ≤ ?`, and **any finite `m` refutes 2-WL CAO
propagation.**

⚠⚠ **The honest risk: the upper bound may not exist.** With every copy present, a cross-copy pair
gives copy `c` access to the multiset over *all* graphs `H` of an invariant of `(G_c, H)`. Nothing
yet bounds that by a fixed WL dimension. If it is unbounded, this strategy stalls at exactly the wall
the rest of the programme is stuck on — it is a better-shaped attack, not a guaranteed one.

### 6c.4 ⛔ The `d`-reduction by restricting to constant-edge-count copies is NOT available

The reader's accompanying suggestion — consider only the `48`-edge copies, cutting `2^120` to
`C(120,48)` — **breaks §6c.1's key move**, and provably so within this frame design:

> A gauge orbit is a coset `c ⊕ H` for a subspace `H ≤ (Z₂)^d` (the gauge acts on the frame only by
> swapping `f(k,0) ↔ f(k,1)`, so every gauge is such a subspace). Weight preservation demands
> `|c ⊕ h| = |c|` for all `c`, which forces `h = 0`. ⟹ **a weight-preserving gauge is trivial.**

So a constant-edge-count copy set is not a gauge orbit; the root is then no longer one orbit by
construction, the orbit partition stops being free, and Step 1's whole advantage is lost. Restricting
the copy set is not a sizing optimization here — it is the thing the design is built to avoid (§3.4),
and §3.2d already measured that no restriction of the copy set is faithful anyway.

---

## 6d. ★★★ ITEM 1, FIRST RESULT — THE ENSEMBLE'S 2-WL COLLAPSES TO A **SINGLE-COPY, POLY-SIZE** OBJECT

`scratchpad/probe_cao_bound_single.py`, 2026-08-13.

### 6d.1 The method — why a *guess* can prove an upper bound

WL's stable colouring is the **coarsest** stable partition refining the atoms. So to prove
*"ensemble-`k`-WL is coarser than `X`"* it suffices to **exhibit any stable partition refining the
atoms whose payload part is `X`** — nothing has to be computed on the big object. That converts the top outstanding item (§9 A.1)
from *"simulate an exponential graph"* into *"guess a closed form and verify stability"*, which is
checkable symbolically. ★ Note the direction this buys: **a MERGE in the bound implies a merge in the
ensemble** (hence a mixed cell, hence a refutation); a *separation* in the bound implies nothing.

### 6d.2 Two structural facts, one proved and one conjectural

**(a) ✅ PROVED AND MEASURED — frame–frame pairs carry at most 12 colours, for every `L`.** WL is
always coarser than the orbit partition, and `S_L`'s orbits on ordered slot-pairs are classified by
`(t, t', |k ∩ k'|)`, `|k ∩ k'| ∈ {0,1,2}`. Measured at `L = 4`: the ensemble's frame–frame colouring
is **exactly** those 12 classes. ⟹ the frame is a **fixed, tiny, copy-independent** object that
cannot accumulate payload data at any round, at any `L`.

**(b) ⚠ CONJECTURAL — the cross-copy channel averages away.** At round 1 the colour of
`(p(c,i), p(c',l))` depends only on `δ = c ⊕ c'` (agreement at slot `{i,l}`, or `dist_i(c,c')` when
`i = l`). Summing over all `c' = c ⊕ δ` is then a sum over all `δ`, independent of `c` — the same
averaging that collapsed 1-WL to the degree sequence (§6a).

### 6d.3 The measurement — the collapse is EXACT at `L = 4`, on every channel

Define the single-copy model `M(c)`: `c`'s payload as a clique, plus the `2d` frame vertices with
`p(i) ~ f(k, c_k)` and `f(k,0) ~ f(k,1)`. **`|M| = L + 2d = L²`.**

```
ensemble (332 v, 4 rounds, 5344 pair colours)   vs   M(c)  (16 v)      [all 64 copies, L=4]
  payload-payload  60 colours vs 60   IDENTICAL: True
  diagonal         20 cells   vs 20   IDENTICAL: True      (= the 20 Aut_m-orbits)
  payload-frame   160 colours vs 160  IDENTICAL: True
  (identical whether or not M's frame-frame pairs are frozen at their 12 orbit classes)
```

> ### ★★★ `ensemble-2-WL` on a copy `=` `2-WL` on that copy's own `L²`-vertex frame encoding. For `L = 16` that is **256 vertices**; for `L = 28`, **784**.

### 6d.4 ⚠⚠ WHAT THIS REVERSES — read this before quoting §6a against §4 or §5.1

In a **single-copy** model the unused frame vertex `f(k, 1-c_k)` has degree 1, so `M(c)` is exactly
the **`full` frame encoding of `G_c`** (clique payload + one typed frame vertex per pair) plus an
inert pendant per slot. Therefore `M(G) ⊔ M(H)` **is** §4.2's `disjoint` model and §5.1's `full`
encoding — the objects those sections actually measured.

> ### ⟹ If (b) holds, §4's and §5.1's kills are **REINSTATED**, and §6a's *"these are model claims"* applies to the **`shared`** variant only.
> §3.2c measured a **shared**-frame two-copy object (`build([c,c'], …)` puts one frame under both
> copies) and found it incomparable to the ensemble. That verdict stands — but it indicts the
> `shared` rows, **not** the `disjoint` ones. ⚠ I stated the caution too broadly; this narrows it.

### 6d.5 ✅ THE LEVEL-UNIFORMITY WORRY IS RESOLVED — **FREEZE THE FRAME VERTICES**

⚠ This paragraph originally recorded a tension: at **1-WL** the `disjoint` model *disagrees* with the
ensemble (§6a: **538 / 6** vs **292 / 100**), so the collapse looked **not level-uniform** — false at
`k = 1`, true at `k = 2`. **It was an artefact of not freezing.**

**The reader's argument (2026-08-13), which supplies the rule.** A frame vertex may split into its two
individualization orbits and then **never refine again**: for every within-copy path that would
distinguish two frame vertices, *every alternative exists across the other copies*, so the multiset
balances. Stepping off a payload vertex onto the frame reaches every other graph at once, so nothing
distinguishing comes back — the escape channel is uniform **by construction**, at every `k`.

**Measured — `scratchpad/probe_cao_bound_freeze.py`, `L = 6`, 1-WL, against §6a's true partition:**

```
single-copy model, frame FROZEN  :  292 cells   identical to the ensemble: True
single-copy model, frame unfrozen:  538 cells   identical to the ensemble: False
```

> ### ★★★ The faithful model is level-uniform: **one copy + the frame, frame vertices frozen at their two orbit colours** (and frame–frame *pairs* frozen at the 12 classes of §6d.2(a) for `k = 2`).
> The freeze is **necessary at 1-WL** and **redundant at 2-WL** (`L = 4`, measured both ways). ⟹ §6d's
> collapse holds at `k = 1` *and* `k = 2`, and the "not level-uniform" caveat is **withdrawn**.

### 6d.6 ▶ THE OPERATIONAL RECIPE, and what is still conjectural

```
M_frozen(G), G a payload graph on L labels, d = C(L,2):
   K_L payload  +  2d frame vertices;  f(k,0) ~ f(k,1);  p(i) ~ f(k, G_k) for every slot k ∋ i
   frame VERTEX colours frozen at t;  frame-frame PAIR colours frozen at (t, t', |k ∩ k'|)
   |M| = L + 2d = L².   Shrikhande/rook 256 · CFI[K4] 784 · CFI[K5] 3540.
Compare two payloads with a SHARED intern table and LOCKSTEP rounds (≡ the disjoint union, but at
n = |M| rather than 2|M| — an 8x saving in the n³ loop).  ⚠ different round counts are not comparable.
```

**First run of the recipe — `scratchpad/probe_cao_mfrozen.py`, `L = 16`, 256 vertices per side:**

```
Shrikhande  84 pair colours    rook4x4  (separates)    control (Shrikhande vs itself): NOT separated
==> M_frozen 2-WL separates Shrikhande from rook 4x4: True
```

⟹ §4's kill **survives the move to the faithful object**. ⚠ Under §6d.1's direction rule this is a
*separation*, so it does not refute anything by itself — it says only that this payload cannot be the
counterexample. The refutation route still needs a payload that **merges**.

### 6d.7 ★★★ THE CLOSED FORM IS COMPLETE — every channel expressed in `M`-data

`scratchpad/probe_cao_crosscopy.py`, `L = 4`, against the ensemble's stable colouring.

⚠⚠ **First, a retraction of my own mechanism.** §6d.2(b) said *"at round 1 cross-copy colours depend
only on `δ = c ⊕ c'`"*. **That is false.** The round-1 frame contribution counts slots `k ∋ i, k ∌ l`
with `c_k = t`, which is `deg_{G_c}(i)` — **absolute** copy data, already at round 1. The reader's
uniformity argument does not use that claim, which is why it survives its failure.

**The reader's uniformity argument (2026-08-13), which is the right one.** For a pebbled pair, split
`z` by copy. The copies holding pebbles (at most `k`) are handled explicitly; *all other copies
together* give `[global count] − [copy c] − [copy c']`. The global count is a constant of `E(L)`, and
each correction is fixed by that vertex's own `M`-colour — because in a **stable** colouring
`col_M(i,i)` already determines `{(col_M(i,m), col_M(m,m)) : m}`, i.e. the copy's whole colour profile.
*Uniform minus a uniform selection of `≤ k` is uniform*, for any `k`.

**Measured, and the shape is not what either of us first guessed:**

```
cross-copy pair colours in the ensemble: 2932   (over 64512 ordered cross pairs)
  A  determined by the pair of M-diagonal colours alone        : False   (398 classes)
  B  ... plus δ = c ⊕ c'                                       : False   (8030 classes)
  C  ... plus the slot-alignment MULTISET (below)              : TRUE    (2932 classes = exact)
  ==> the cross-copy contribution to the DIAGONAL is determined by M-col(c,i): TRUE  (20 values)
```

> ### ★★★ The individual cross-copy colours are RICH — 2932 of them, not a function of the `M`-diagonals even with `δ`. Their **aggregate over all other copies** is nonetheless exactly a function of `M-col(c,i)`. That is "uniform on the return": the summands are complicated, the sum is not.

⟹ **the collapse cannot be proved by claiming cross-copy colours are simple — only their aggregate is.**

**The closed form, complete and exact at `L = 4`:**

| channel | closed form |
|---|---|
| diagonal · within-copy pairs · payload–frame | `M(c)`'s own colouring (§6d.3) |
| frame–frame | the 12 classes `(t, t', |k ∩ k'|)` — **proved, all `L`** (§6d.2a) |
| **cross-copy pairs** | `(M-col(c,i), M-col(c',l), multiset over (k,t) of (M(c)-col(i, f(k,t)), M(c')-col(f(k,t), l)))` — **bijective**, 2932 = 2932 |

⚠ **A vacuity trap hit and caught here.** The same hypothesis with an *ordered tuple* over slots
instead of a multiset reported `True` with **64512 classes over 64512 pairs** — an **injective** key,
so "determines the colour" was vacuously true. The class count is what exposes it. WL aggregates over
`z` and yields a multiset, so the multiset is also the faithful form. ★ Always check the witness is
not degenerate (standing project steer).

### 6d.8 ▶ WHAT ITEM 1 HAS BEEN REDUCED TO

Everything is now `M`-data, so the residual obligation is a self-contained combinatorial lemma with
no WL, no graph and no ensemble in it:

> ### ▶ **LEMMA (open).** For fixed `(c,i)`, the multiset over all `(c',l)` of `(M-col(c',l), the slot-alignment multiset of a(c,i) against b(c',l))` is determined by `M-col(c,i)`.
> where `a(c,i)` is the vector `(k,t) ↦ M(c)-col(i, f(k,t))` and likewise `b(c',l)`.

★ It looks provable: the distribution of `b(c',l)` over all `c'` is **`S_L`-invariant and independent
of `c`**, while `a(c,i)` is held fixed — so the sum should factor through `a`'s `S_L`-orbit, which
stability ties to `M-col(c,i)`. **Measured true at `L = 4` (20 values).** ⛔ Until it is proved, do not
restate §4/§5.1 as unconditional.

### 6d.9 ▶ What follows immediately

⚠⚠ **This whole list is written under §5.2's belief that the encoding's gain is unbounded above.
§6f bounds it** — so bullets 1 and 2 are **downgraded to constant-pinning**. Read §6f before acting
on them.

* **`CFI[K5]` is again THE measurement**, and now against the *right* object rather than a proxy.
  ⚠ **Size, stated in the new units:** `|M_frozen| = L + 2·C(L,2) = 3540` per side at `L = 60`, *not*
  §5.1's `3660` — that figure was the two-copy **union** under the old encoding. ⚠ This
  **re-reverses** §3.2d's *"a faster 2-WL addresses the wrong bottleneck"*: under the collapse the
  faithful object **is** poly-size, so a C implementation is worth building after all.
* The refutation route (§6c.3) needs a **merge**, so the target is a payload that `M`-2-WL fails to
  separate. `Shrikhande`/`rook` and `CFI[K4]` both separate under `M` (§4.2, §5.1), so neither
  refutes; a 3-WL-blind pair is the next candidate.
* ▶ **The proof obligation is now sharp**: prove (b), i.e. that the partition built from `M` is stable
  in `E(L)`. (a) is done.

---

## 6e. ▶▶ PROOF PLAN FOR §6d.8's LEMMA — two steps done, one gap, four candidate resolutions

**Notation.** `S` = the `d = C(L,2)` slots. A copy is `c ∈ {0,1}^S`. In the stable colouring of
`M(c)`: `μ_c(i,j)` = payload-pair colours, `a(c,i) = ((k,t) ↦ M(c)\text{-col}(p(i), f(k,t)))` = the
**slot profile** of `i`, and `Align(a,b) = {{ (a_{k,t}, b_{k,t}) : (k,t) }}` = their contingency
table over slots.

> ### TARGET. For all `(c,i)`, `Φ(c,i) := {{ (μ_{c'}(l,l), Align(a(c,i), b(c',l))) : (c',l) }}` is determined by `μ_c(i,i)`.

### 6e.0 ⛔⛔ PHASE 0 — ~~validated beyond the ensemble's reach~~ **VACUOUS, see §6e.4a**

★ The lemma mentions **only `M`-data** — no ensemble, no `2^d`-vertex graph. So it is testable where
the ensemble is not. `scratchpad/probe_cao_lemma_check.py`:

```
L=4:  20 mu-classes, 0 violations   (calibration — matches the L=4 ensemble ground truth)
L=5:  90 mu-classes, 0 violations   ★ the L=5 ensemble is 6164 vertices at 2-WL, unreachable
```

⟹ the §6d collapse now has support at an `L` the direct method could never test. ⚠ Representative
sampling (3 per class), so this is evidence, not proof.

### 6e.1 ✅ STEP 1 — reduce to a pushforward. This is the step that makes the lemma tractable

Let `D := {{ (μ_{c'}(l,l), b(c',l)) : (c',l) ∈ {0,1}^S × [L] }}`. **`D` does not depend on `(c,i)`.**
Then

```
Φ(c,i)  =  pushforward of D under  (y, b) ↦ (y, Align(a(c,i), b))
```

⟹ `Φ(c,i)` depends on `(c,i)` **only through the single vector `a(c,i)`**, and the whole question is
*which features of `a` the fixed distribution `D` can resolve*. ★ This disposes of the "profile of
`(G_c,i)` against all graphs" worry that §6d.7 raised: there is no unbounded object — one fixed
distribution, probed by one vector.

### 6e.2 ✅ STEP 2 — `D` is `S_L`-invariant (free), and ⚠ why that alone must NOT suffice

`M` is built equivariantly, so `b(πc', πl)_{πk} = b(c',l)_k` and `(c',l) ↦ (πc', πl)` permutes the
index set. Hence `Φ(c,i)` depends only on the `S_L`-**orbit** of `a(c,i)`.

> ### ⚠⚠ A TRAP: do not try to finish from here. Finishing from `S_L`-invariance alone would require `μ_c(i,i)` to determine the `S_L`-orbit of `a(c,i)` — i.e. *`M` is a complete isomorphism invariant*, which is exactly what must not be true (it would make the whole programme vacuous, §6c.2). **The proof must use something strictly finer than the group action.**

### 6e.3 ✅ STEP 3 — the base case is provable, and it identifies that "something finer"

At **round 1**, `b(c',l)_k = ([l ∈ k], c'_k)`. As `c'` ranges over **all** of `{0,1}^S`, the bits
`(c'_k)_k` are i.i.d. uniform, hence **fully exchangeable across slots** — not merely
`S_L`-exchangeable. ★ *This is where "every copy is present" does its work, and it is the formal
content of the reader's uniformity argument.* `Align(a,b)` then splits into

| ingredient | what it needs from `a` | why `μ_c(i,i)` determines it |
|---|---|---|
| the `c'`-bit counts | only the **sizes** of the `a`-classes | the multiset `{{a(c,i)_k : k}}` **is** the diagonal's refinement aggregated over frame `z` in `M(c)` |
| the `[l ∈ k]` counts | the incidences `n_{l,A} = #{k ∋ l : k ∈ A}` | `μ_c(i,l)` determines `n_{l,·}` (frame-aggregation in `M(c)`), and the multiset over `l` of `μ_c(i,l)` is the diagonal's refinement aggregated over payload `z` |

∎ base case.

### 6e.4 ⛔ THE GAP — the induction step

At the **fixpoint**, `b(c',l)_k` is the stable `M(c')` colour, which depends on **all** of `c'`, not
just `c'_k`. So the slot-vector `b` is not a product measure, the full exchangeability of §6e.3 fails,
and only §6e.2's `S_L`-invariance survives — which §6e.2 shows is insufficient by itself.

**That is the entire remaining obligation.** Everything else above is done.

### 6e.4a ⚠⚠ 2026-08-15 — **PHASE 0 WAS VACUOUS** (stands); ~~the lemma is false~~ **DOWNGRADED — read §6e.4c first**

> ### ⚠⚠ 2026-08-15c: *"the LEMMA IS FALSE"* is **DOWNGRADED to NOT ESTABLISHED** — the `LEMMA ⟹ ORB`
> direction needs an isolation step that presupposes its own conclusion (§6e.4c). `ORB ⟹ LEMMA` and
> **ORB ⟺ `M`-complete** (hence ORB false at large `L`) both **stand**, as does the vacuity finding.

**This supersedes §6e.4's diagnosis, §6e.0's validation, and §6e.5's R1/R3.** §6e.4 blames the gap on
cross-copy exchangeability failing at the fixpoint. That was a red herring: the obligation dies for a
much simpler reason, and it dies at every `L` a prober can never reach while holding trivially at
every `L` one can.

> ### THE REDUCTION. §6e.1 + §6e.2 already give `Φ(c,i) = F(a(c,i))` with `F` **`S_L`-invariant**. So `Φ` is a function of the `S_L`-**orbit** of `a(c,i)`, and the LEMMA follows at once from
> ### **ORB.** *`μ_c(i,i)` determines the `S_L`-orbit of `a(c,i)`.*
> No sum over copies, no product measure — §6e.4's whole difficulty evaporates. And ORB is *equivalent*
> to the lemma whenever some `b(c',l)` is **injective on typed slots**, because then `Align(a, b(c',l))`
> simply reads `a(c,i)` off in `b`'s labelling. ✅ Injective profiles are abundant:
> **96/256 at `L=4`, 1920/5120 at `L=5`** (`scratchpad/probe_cao_orb.py`).

> ### ⛔ AND ORB IS EXACTLY *"`M`-2-WL IS COMPLETE"*. §6e.2's TRAP BOX IS **RIGHT**.
> **Mechanism, and it is one line.** In `M(c)` the payload is a **clique**. So for *any* slot `k`, the
> pair `(p(i), f(k,t))` has common payload neighbours `{j ∈ k}` when `c_k = t` (two of them, or one if
> `i ∈ k`) and **none** otherwise. ⟹ **one** refinement round makes that pair's colour see `c_k` — for
> **every** slot, including the slots that do not contain `i`. ⟹ `a(c,i)` reads off the whole of `c`.
> ✅ Measured at `L=5`: `a(c,i)` determines `c` with **0 collisions**, and the profiles have
> **90 `S_L`-orbits = 90 marked-graph iso classes = 90 `μ`-classes** (`probe_cao_orb_mech.py`).
> ⟹ the orbit of `a(c,i)` **is** the iso class of `(G,i)`, so ORB ⟺ `μ` is complete.

```
  LEMMA  +  injectivity   ==>  ORB  ==>  `M`-2-WL is a COMPLETE invariant of (graph, marked vertex)
  but    `M`-2-WL  <=  arity-6 WL on G          -- §6f, MACHINE-CHECKED at k = 2
  and    CFI over a treewidth->=7 base is 6-WL-blind, non-isomorphic   -- literature, (iii)
  ============================================================================================
  ==>  `M`-2-WL is INCOMPLETE for large L   ==>   **§6d.8's LEMMA IS FALSE.**
```

⚠ **This refutes via a THEOREM (bounded-WL incompleteness), never via `GI ∈ P`** — the banned argument
is not used, and must not be substituted for §6f here even though it looks shorter.

> ### ⛔⛔ §6e.0's PHASE 0 IS VACUOUS, AND NO REACHABLE `L` CAN FIX IT
> The lemma is **true** at every `L` where `M`-2-WL is complete — and it is complete at *every rung
> ever tested*: `μ`-classes vs marked-graph iso classes (Burnside) come out
> **`L=4`: 20 = 20 · `L=5`: 90 = 90 · `L=6`: 544 = 544** (`probe_cao_vacuity.py`, and the `L=6`
> `μ`-count from the numpy port). ⟹ §6e.0's *"support at an `L` the direct method could never test"*
> tests **nothing**. ⚠⚠ And it is unfixable by climbing: `M`-2-WL is at least bare 2-WL, so
> incompleteness needs `L` in the tens at minimum, where `2^{C(L,2)}` copies is beyond any prober
> for ever. ⛔ **Do not run `probe_cao_lemma_check*` at a larger `L` expecting information.**

> ### ⛔⛔ R3 IS NOT MERELY *"UNPAYABLE-LOOKING"* (§6f.5a β) — IT IS **PROVABLY VACUOUS**
> `M⁺ = M + Φ` is a **complete isomorphism invariant**: `Φ` determines the `S_L`-orbit of `a(c,i)`
> (given injectivity), and that orbit *is* the iso class of `(G,i)`. ⟹ bounding the ensemble above by
> `M⁺` bounds it by a complete invariant, which refutes nothing. (β) is upgraded from suspicion to
> proof, and §6e.5's R3 proviso is **violated**.

> ### ▶▶ WHAT ACTUALLY WENT WRONG — the design lesson, and it points at the alternative
> The defect is **not** averaging, exchangeability, or product measures. It is that the guess
> **exposes the whole slot-profile VECTOR `a(c,i)` across copies**, and *a vector of coarse colours is
> a complete invariant even when every entry is coarse*. The `Align` channel with an injective `b`
> reads it straight off.
> ⟹ ★ **Any surviving guess must aggregate the slot profile into a BOUNDED summary before it crosses
> copies.** ★★ And there is a positive lead already on record: **§6a measured the ensemble at 1-WL to
> be far COARSER than the model.** So `col_E(p(c,i), f(k,t))` is plausibly far coarser than
> `a(c,i)_{(k,t)}`, and the injectivity that kills the lemma may be an artefact of building the guess
> out of **`M`-colours instead of the ensemble's own frame colours**. ▶ That is the alternative path:
> guess from the ensemble's frame channel, not from `M`'s.

⚠ **What this does NOT show.** It does **not** show (i) is false. `wl_E ⊑ M`-2-WL may still hold; what
is refuted is the *stable-guess proof route* to it, and its designated repair. (i) keeps its status as
the one open mathematical obligation — it simply no longer has a plan.

### 6e.4b ⚠⚠ 2026-08-15 — ~~(i) IS FALSE, CONSTRUCTION C REFUTED AT 2-WL~~ **RETRACTED SAME DAY. Read §6e.4c.**

> ### ⛔⛔ RETRACTION, 2026-08-15c — the headline of this section was WRONG and is withdrawn.
> The measurements below are sound and stand. The **inference** from them — that the ensemble's 2-WL
> is a complete invariant, hence no mixed cells, hence (i) false — **is not established**: see §6e.4c
> for the exact broken step. ⚠ The one measurement that bears on it points the OTHER way:
> **ensemble payload cells = 20 = `M`'s μ-classes = 20** at `L=4`, i.e. the cross-copy channel added
> **nothing**, which is (i) holding with equality. ⛔ Do not quote this section's title.

### 6e.4b (measurements, which stand) — THE FRAME IS NOT 1-WL-BLIND AT THE PAIR LEVEL

§6e.4a killed the *proof route*. This kills the **construction**. Both proposed rescues — *"guess from
the ensemble's own coarser frame channel"* (mine, 2026-08-14) and *"the gauge vertices see every
colour in equal proportions, so paths through them carry no more than their endpoints"* (reader,
2026-08-15) — rest on the same hope, and it is **measurably false**.

> ### THE MEASUREMENT — `scratchpad/probe_cao_ensemble_frame.py`, the real ensemble, `L=4`, `N=332`
> The ensemble's frame channel is not coarser than `M`'s. **It is identical.**
> ```
>   aE(c,i) determines the copy c          TRUE, 0 collisions      (M: same)
>   aE injective on all 12 typed slots     96 / 256                (M: 96 / 256, identical)
>   S_L-orbits of aE                       20  =  ensemble payload cells 20  =  M's mu-classes 20
> ```
> ⚠ Sharing the frame is **irrelevant** to the mechanism, because the mechanism never leaves one copy:
> `p(c,i) ~ p(c,j)` (payload of a copy) and `p(c,j) ~ f(k,t)` iff `c_k = t`, so the pair
> `(p(c,i), f(k,t))` counts common neighbours `{j ∈ k}` exactly when `c_k = t`. ⟹ *"the ensemble is far
> coarser than the model"* is a **1-WL** fact (§6a) and does **not** survive to 2-WL.

```
  aE(c,i) sees [c_k = t] at every slot          ==> aE(c,i) determines c
  some aE(c',l) is injective on typed slots     (96/256 at L=4)
  col_E(p(c,i), p(c',l))  refines  Align(aE(c,i), aE(c',l))     -- the frame terms of its signature
  the DIAGONAL colour of p(c,i) refines the multiset of those over all payload z
  ==============================================================================================
  ==> the ensemble's 2-WL diagonal colour determines the S_L-orbit of aE(c,i)
      = the ISO CLASS of (G_c, i)
  ==> ENSEMBLE 2-WL IS A COMPLETE INVARIANT OF THE MARKED PAYLOAD GRAPH, AT EVERY L
  ==> NO MIXED CELLS, EVER.  (i) IS FALSE, AND CONSTRUCTION C DIES AT RUNG 2.
```

✅ Independently confirmed at `L=4`: **20 payload cells = 20 orbits** — complete, and matching §6b's
measured *"0 mixed cells, 20 cells = 20 orbits"*, which is now **explained rather than merely observed**.
⚠ No complexity contradiction: the ensemble has `L·2^{C(L,2)}` vertices, so this is an exponential-time
isomorphism test. ⚠ One link is genericity, not proof: *some* `aE(c',l)` injective. Measured at `L=4`;
a rigid copy supplies it, but that is not written out.

> ### ⛔ AND THE OBVIOUS DESIGN FIX DOES NOT WORK — the payload clique is **not** the culprit
> The clique is what makes the one-round argument work, so dropping it is the natural repair.
> Measured (`probe_cao_noclique.py`, `probe_cao_noclique_mech.py`) with the payload an **independent
> set** instead: **identical figures at `L=4` (0 collisions, 96/256, 20 orbits = 20 `μ`-classes) and
> at `L=5` (0 collisions, 1920/5120, 90 = 90).** The information simply takes the longer route
> `p(i) → f(k',c_{k'}) → p(j) → f(k,c_k)` and arrives a round or two later. ⟹ this is **structural to
> the frame encoding**, not a removable detail.

> ### ⛔ THE INDUCTION-ON-`L` IDEA IS BLOCKED FOR THE SAME REASON
> *"the equivalence is calculable for small `L` and the growth is pure addition of vertices and their
> edges"* (reader) is a sound instinct — but the statement one would induct (`E(L)`-2-WL bounded by an
> incomplete invariant) is **false at every `L`**, not merely unproved at large `L`. There is nothing
> true to carry up.

> ### ▶▶ WHAT SURVIVES, AND WHAT THIS MEANS FOR THE TRACK
> * **Unaffected:** Construction B (§2) is still a genuine **1-WL** CAO counterexample, and
>   Construction C at rung 1 (§6, 100 mixed cells) still stands. The 1-WL design programme works.
> * **Dead:** Construction C at 2-WL, (i), R1, R3, and the `M`-collapse. ⛔ Do not restart any of them.
> * ★★ **The general lesson, and it is the strong form of §6b.** §6b said the frame *"hides the payload
>   completely at 1-WL and not at all at 2-WL"*. The true statement is worse: at 2-WL the frame hands
>   over the **entire marked-graph isomorphism class**. Any future carrier must not let a payload
>   vertex read its own graph off the frame — which every all-pairs slot encoding does.
> * ⟹ **2-WL CAO propagation is back to OPEN with no live construction**, and §6f/§6f.5a's machinery
>   (the transfer, `DisjointUnion`, `TupleCov`, `AtomAugment`) is what survives, all of it carrier-generic.

### 6e.4c ⚠⚠ 2026-08-15c — **THE BROKEN STEP, AND WHAT THE QUESTION REALLY REDUCES TO**

> ### ▶▶ **STILL OPEN — this section states the question that §6e.4d–g are about.** The diagnosis here
> is **correct and stands**: the retracted argument really did presuppose its conclusion. §6e.4d
> answers the *scope* objection — the probe can be **chosen**, and isolating a chosen generic copy is
> bought by a lower bound rather than by completeness — but that is **position (A)**, argued, not
> established (§6e.4e states (B), which is not refuted).
> ⚠ Read this section anyway: its statement of *what* the question is, and the `ORB ⟺ M`-complete
> equivalence, are what make §6e.4d's consequences follow *if* (A) holds.
> ⛔ A 2026-08-15d revision of this box read *"ANSWERED — the answer is YES and Construction C dies"*.
> **Withdrawn 2026-08-16.**

Raised by the reader against §6e.4b, and the objection is **half right — the better half**.

> ### ⛔ THE BROKEN STEP — an isolation that presupposes what it proves
> §6e.4a and §6e.4b both run: *`Φ` contains the alignments against a rigid injective profile `b₀`;
> those spell out `a ∘ π` for every `π`, which is the orbit of `a`.* ⚠ To read them out one must
> **isolate** the entries coming from `b₀`'s orbit, and the only handle for that is their colour —
> which presupposes the colouring already separates those copies, i.e. part of the conclusion. Not
> viciously circular (rigid copies plausibly separate early and bootstrap) but **not established**.
> ⟹ **RETRACT both:** §6e.4b's *"(i) is false / Construction C refuted at 2-WL"*, and §6e.4a's
> *"the LEMMA IS FALSE"*. `ORB ⟹ LEMMA` is solid (§6e.1+§6e.2); only the **converse** is gapped.

> ### ⚠ AND THE READER'S PREMISE IS ALSO WRONG, MEASURABLY — do not adopt it either
> *"What a payload vertex sees outside its clique does not differ from 1-WL — the gauge vertices
> staying one colour showcases it."* The frame vertices being one **colour** is a statement about
> **vertices**, i.e. 1-WL. 2-WL colours **pairs**, and `(p(c,i), f(k,t))` has common neighbours
> `{j ∈ k}` exactly when `c_k = t`, so one round separates it. ✅ Measured on the real ensemble
> (`L=4`, `N=332`): `aE(c,i)` **determines `c`**, 0 collisions, 96/256 injective. That is §6b in
> strong form. ⟹ the outward channel is *not* 1-WL-blind; what is unproved is only whether a
> **cross-copy** pair can use it to learn anything a within-copy pair does not already have.

> ### ▶▶▶ WHAT SURVIVES, AND IT IS SHARP — the whole thing now rests on ONE question
> ### **Does `Φ(c,i)` determine the `S_L`-orbit of `a(c,i)`?**
> * **Reader's position: NO** — the uniform distribution over all copies washes the alignment out, so
>   a cross-copy pair reduces to the disjoint (triangle-frame) case, which needs no exponential object.
> * **§6e.4a/b's position: YES**, via the isolation step above — **not established**.
>
> ★★ **What IS established, and it is what makes the question sharp.** `a(c,i)` determines `c`
> (§6e.4a's clique/common-neighbour mechanism, measured), so the **orbit of `a` IS the marked-graph
> iso class**. Hence **ORB ⟺ `M`-2-WL is complete**, and therefore **ORB is FALSE for large `L`**
> (§6f + CFI). ORB was the one clean sufficient condition for §6d.8's lemma. ⟹ **the lemma can only
> hold if `Φ` is STRICTLY COARSER than `a`'s orbit** — which is exactly the reader's washout claim,
> now promoted from intuition to *the precise statement that must be proved*.
> ⚠ ⛔ **Not testable by climbing `L`:** at every reachable `L`, `μ` is complete (§6e.4a), so `Φ` and
> the orbit trivially agree. The question is analytic.

⚠ **Unaffected by this retraction:** §6e.4a's vacuity finding (`M`-2-WL complete at `L=4/5/6` —
20=20, 90=90, 544=544) and §6e.4b's frame-channel measurements. Both are direct measurements and
neither depends on the isolation step.

### 6e.4d ★★★ 2026-08-15d — **THE CASE FOR (A):** `Φ(c,i)` determines the `S_L`-orbit of `a(c,i)`

> ### ⚠⚠ STATUS, corrected 2026-08-16. This section was originally titled *"THE QUESTION IS ANSWERED: YES"* and concluded that Construction C is dead. **That verdict is WITHDRAWN.**
> What follows is a **proof sketch whose premises are measured only at `L = 4`**, not a settled
> result. It is (A) in the top box's disjunction; (B) is stated in §6e.4e and is **not refuted**.
> The mathematics below is unchanged and still believed by its author — what changed is the label on
> it. ⚠ Read §6e.4e immediately after; reading this section alone will leave you over-confident.

> ### ▶▶▶ **(A): `Φ(c,i)` determines the `S_L`-orbit of `a(c,i)`.**
> The retracted argument tried to isolate an **arbitrary** rigid injective `b₀` inside its tag class,
> and §6e.4c is right that this presupposes the conclusion. But nothing forces the probe to be
> arbitrary. **The probe is chosen**, and isolating one *chosen* copy is bought by a **LOWER bound**
> on the colouring — which is available unconditionally — not by the completeness the conclusion is
> about. That is the whole repair, and it is one sentence long.

**THE THEOREM (carrier-generic; no graphs, no WL, no ensemble in it).** Let `Γ` be a finite group
acting on a finite set `X`. Let `Ω` be a finite `Γ`-set carrying **equivariant profiles**
`b : Ω → C^X` (`b_{γω} = b_ω ∘ γ⁻¹`) and a **`Γ`-invariant tag** `y : Ω → Y`. Put

```
    Φ(ω)  =  {{ ( y(ω'), Align(b_ω, b_{ω'}) ) : ω' ∈ Ω }},     Align(u,v) = {{ (u x, v x) : x ∈ X }}.
```

> #### **RULER LEMMA.** If some `ω₀ ∈ Ω` satisfies
> #### (i) `y⁻¹(y(ω₀)) = Γ·ω₀` — *the tag isolates `ω₀`'s orbit*, and
> #### (ii) `b_{ω₀} : X → C` is **injective** — *the ruler's marks are all distinct*,
> #### then `Φ(ω)` determines the multiset `{{ b_ω ∘ γ : γ ∈ Γ }}`, hence the `Γ`-orbit of `b_ω`.

*Proof.* By (i) the sub-multiset of `Φ(ω)` at tag `y(ω₀)` runs over `ω' ∈ Γ·ω₀` and nothing else.
Write `ω' = γω₀`; then `b_{ω'} = b_{ω₀}∘γ⁻¹` and `Align(u, v∘γ⁻¹) = Align(u∘γ, v)`, so the block is
`{{ Align(b_ω∘γ, b_{ω₀}) : γ ∈ Γ }}`. By (ii) the labels `b_{ω₀}(x)` are pairwise distinct, so the
contingency table `{{ (b_ω(γx), b_{ω₀}(x)) : x }}` **is the graph of the function** `b_ω∘γ` written in
`b_{ω₀}`'s labelling. Each entry therefore decodes to `b_ω∘γ`, and the block decodes to the orbit. ∎

★ **Note what the proof does *not* need:** it never separates the members of `Γ·ω₀` from each other,
and it says nothing about any other tag class. The mixed classes that make the invariant incomplete
are simply **not used**.

#### 6e.4d.1 Where the two hypotheses come from — and why they are not the conclusion in disguise

Both are supplied by **one generic copy**, and the fact that supplies them is a *lower* bound:

> ### ▶ **(LB) `col_E` restricted to a copy refines that copy's own bare 2-WL.** Proof: within-copy payload pairs are adjacent (the payload is a clique) and cross-copy ones are not, so *"z is in the same copy as u"* is determined by `col_E(u,z)`; hence `E`-stability restricts to within-copy stability, and by §6b the within-copy pair colours already see the encoded adjacency. A stable colouring refining the atoms refines the 2-WL closure. ∎ ⚠ Level-independent, and independent of the collapse (i).

> ### ✅✅ **2026-08-16b — (LB) IS NOW A THEOREM**, at every `L`, at the real object:
> `ChainDescent/CopyRestrict.lean`, **`lb : Refines (eCopy L c) (wl2G (hInit c))`** for every
> `SymCopy` copy `c`. The proof is the paragraph above, in three parts: `restrict_sig_eq` (*stability
> restricts to a colour-definable sub-carrier* — carrier-generic, and the part that was actually
> load-bearing), `centre_readout` + `frame_type_eq` (the individualized `m(base)` is the **unique**
> sort-3 vertex, so any pair colour reads a frame vertex's type), and `encoded_edge_eq` = **§6b at the
> object**. ⚠ `SymCopy` is forced by `Ensemble`'s ordered-slot model, not by the mathematics.

✅ **(LB) was also MEASURED before that** — `probe_cao_ruler`/`probe_cao_lowerbound.py`, real
ensemble `L=4`, **all 64 copies**: the ensemble's within-copy vertex colouring refines the copy's bare
1-WL (64/64) and its bare 2-WL diagonal (64/64); the within-copy **pair** colouring refines the copy's
bare 2-WL pair colouring (64/64); sanity, it refines the copy's `Aut`-orbits (64/64).
★★ **(LB) is the ONLY structural claim (P1) and (P2) need, and it is a LOWER bound** — so it cannot be
weakened by the ensemble being larger, more symmetric, or coarser anywhere else. ▶ **This is the thing
to attack if §6e.4d is wrong.**

Now pick `H` with a **discrete bare 1-WL colouring** (equivalently: `H` is identified by colour
refinement). Then the copy's within-copy colouring is discrete, and:

* **(P1) the tag isolates `(H,j)`.** `col_E(p(H,j))` determines `{{ (col_E(p(H,j),z), col_E(z,z)) }}`;
  restricted to within-copy `z` these `L−1` pair colours are **distinct**, so they *label* the copy's
  vertices. Stability then upgrades each such label to a whole column — `col_E(p(H,j),p(H,u))`
  determines `{{ (col(p(H,j),z), col(z,p(H,u))) }}`, i.e. the map `w ↦ col(p(H,w),p(H,u))` in that
  labelling — so the diagonal colour determines the **entire within-copy pair-colour matrix in a
  canonical labelling**, hence (by §6b, pair colour ⟹ encoded adjacency) the marked graph `(H,j)` up
  to isomorphism. No non-isomorphic marked copy can share the tag. ∎
* **(P2) `aE(H,j)` is injective on typed slots.** For `t = H_k` the pair `(p(H,j), f(k,t))` has common
  payload neighbours exactly `k` (§6e.4a's clique mechanism), and those carry **distinct** labels, so
  the pair colour determines `k`; for `t ≠ H_k` the frame partner `f(k,H_k)` (frame–frame class
  `|k∩k'| = 2`) carries `k` across. The frozen types separate `t`. ⟹ all `2·C(L,2)` values distinct. ∎

> ### ⚠⚠ **THE NON-CIRCULARITY, stated so it travels.** (P1) is proved from a **lower** bound
> (`col_E ⊒ within-copy bare 2-WL`) applied to a graph that is discrete *under that lower bound*. It
> never assumes the colouring separates the copies the conclusion is about — those are CFI-like and
> are never used as probes. §6e.4c's objection is correct against an *arbitrary* `b₀` and simply does
> not apply to a *chosen* one.

#### 6e.4d.2 ⛔ THE ESCAPE ROUTE IS CLOSED — the construction cannot omit its rulers

The obvious repair is to build the ensemble out of copies that are all symmetric. **It is not
available.** `E(L)`'s root must be a single orbit, and the only thing acting transitively on copies is
the gauge `(Z₂)^d`, whose orbits are cosets `c ⊕ H`; transitivity forces `H = (Z₂)^d`, i.e. the copy
set is **all** of `{0,1}^S` (this is §3.2d's non-saturation and §6c.4's *"a weight-preserving gauge is
trivial"*, read in the other direction). For `L ≥ 6` that set **necessarily contains 1-WL-discrete
graphs** — measured: **5760 of the 32768** copies at `L=6`, and 35 %–78 % of random copies at
`L = 7,8,9` (rising, as Babai–Erdős–Selkow predicts). ⟹ *every* instance of Construction C carries
its own rulers, at every `L` where the construction is interesting.

#### 6e.4d.3 ▶▶ WHAT (A) WOULD FORCE — ⚠ conditional on (LB), (P1), (P2), none machine-checked

```
 col_E(p(c,i))  ==> {{ (y(c',l), col_E(p(c,i),p(c',l))) }}        [stability; pair colour fixes fibres]
                ==> {{ (y(c',l), Align(aE(c,i), aE(c',l))) }} = Phi_E(c,i)   [stability, frame z]
                ==> {{ aE(c,i) o pi : pi in S_L }}                [RULER LEMMA, omega0 = (H,j)]
                ==> the S_L-orbit of (c,i)                        [aE(c,i) determines c, and i]
 ================================================================================================
 ==> E(L)'s 2-WL colouring is a COMPLETE invariant of the marked payload graph, at every L
 ==> NO MIXED CELLS.  Construction C would die at rung 2.
```

⚠⚠ **Read the chain as a conditional.** Every arrow is a coherence step and is safe; the load is
carried entirely by the three premises feeding the third arrow. **The chain is only as good as (LB),
and (LB) is measured at `L = 4` and proved on paper.** §6e.4g items 1–3 are exactly the job of turning
this from a sketch into a theorem. Until then this block states what (A) *would* force, not what is.

> ### ⚠ THE STANDING STEER, CHECKED — *"the CAO start is the ORBIT PARTITION, not the WL colouring"*
> The probes here start from the plain atoms; the hypothesis starts from the exact orbit partition
> (§0). **The direction is safe, and it is the good one.** The orbit-partition start is *finer*, so its
> closure is sandwiched: `atom-closure ⊑ CAO-closure ⊑ orbit partition` — the right-hand `⊑` because WL
> colours are `Aut`-invariant (`CaoTarget.inv2_wl2`). The measurements give `atom-closure = orbits`,
> which pins the middle term. ⟹ **cells = orbits either way.** The Ruler Lemma argument likewise uses
> only a **lower** bound on the colouring, which a finer start preserves. ★ This is the steer that
> killed Construction A; it costs one paragraph to check, and it does not bite here.

1. **Construction C would be refuted at 2-WL**, and the argument **does not use the collapse (i)** as
   an input. ⚠⚠ It does, however, **contradict** (i): if `E(L)`-2-WL is complete and `M`-2-WL is not
   (§6f's bounded arity + CFI), then `E` is *strictly finer* than `M`, which is the negation of the
   collapse. ⟹ **(A) and (B) are directly contradictory, not independent — exactly one is right**,
   which is why §6e.4g's items settle both at once. ⚠ Note the dependency: *(i) is false* additionally
   inherits §6f + (iii), which are argued and literature; *(A)* itself needs only §6e.4d.1.
2. ⛔ **§6d.8's LEMMA would be FALSE at large `L`** — §6e.4a's conclusion, with the isolation step
   repaired. (`LEMMA` + `Φ ⟹ orbit` would give ORB, and ORB ⟺ `M`-2-WL complete, false by
   §6f + CFI.) ⟹ **R1 would have nothing true to induct, and R3's `M⁺` would be a complete
   invariant.** ⚠⚠ **This is conditional on (A).** If (A) fails, R1 and R3 are live again — the
   handoff's *"what is dead"* list flags this.
3. ★★★ **The general design filter — THE RIGID RULER.** ⚠ Conditional on (A) like everything else
   here, but it is the part worth carrying into a successor carrier either way, because a design that
   survives it is strictly safer.
   > **An ensemble that contains a rigid, refinement-discrete member cannot hide anything from 2-WL
   > that its reading channel exposes.** One such member is enough: its own colour names it, and its
   > injective reading turns the `Align` channel into a *ruler* against which every other member is
   > read off. ⟹ *"hide the payload among all its relabellings"* is self-defeating, because a family
   > closed enough to be one orbit is large enough to contain a ruler.
   ⚠ This is the strong form of §6b: not merely *"a payload vertex must not read its own graph off the
   frame"*, but *"no member may be individually identifiable"* — and gauge-transitivity makes that
   unachievable. ⛔ **But see §6e.4f #5**: the ruler is **not** a bolt-on device, so this filter binds
   only on carriers whose members read a **shared frame**. It says nothing about other designs.

#### 6e.4d.4 ▶ THE MEASUREMENTS — and how the vacuity trap was avoided

⚠ The conclusion itself is **untestable at reachable `L`** (§6e.4c): `μ` is complete there, so every
tag isolates and *"`Φ` determines the orbit"* comes out true for a reason that has nothing to do with
large `L`. So what was measured is the **proof**, not the conclusion — hypotheses, mechanism, and the
decode — plus one genuinely non-vacuous surrogate.

| what | probe | result |
|---|---|---|
| the decode **runs**: extract the ruler's tag block from `Φ`, decode each entry, compare with the true orbit | `probe_cao_ruler.py` | `L=4`: **20/20** orbit reps recovered exactly · `L=5`: **90/90**. Rulers: **96/256**, **1920/5120** |
| (P1)+(P2) **past the ensemble's reach** — single-copy properties, so no `2^{C(L,2)}` object needed | `probe_cao_ruler_exists.py` | `L = 6,7,8,9`: every 1-WL-discrete copy tested is payload-discrete **and** has all `L` marked profiles injective (40/40, 20/20, 20/20, 20/20) |
| rulers **cannot be omitted** | same | 1-WL-discrete copies: **5760/32768** at `L=6`; 70/200, 109/200, 156/200 random at `L=7,8,9` |
| **cells vs orbits for EVERY kind** of the real ensemble — the record only ever counted payload | `probe_cao_kind_census.py` | `L=4`, `N=332`: payload **20 = 20**, frame **2 = 2**, central **11 = 11**, **0 mixed cells anywhere** |
| (P1)+(P2) and the decode **on the real ensemble**, not on `M(H)` | same | `L=4`: (P1) 256/256, (P2) 96/256, **96 rulers**, block size **24 = \|S₄\|**, **20/20** orbit reps recovered |
| the **surrogate**: make the tag genuinely incomplete by capping the rounds, then ask whether `Align` washes out | `probe_cao_phi_isolate.py` | see below |

> ### ★★ THE SURROGATE, and it is the one non-vacuous test of *washout itself*
> Run `M`'s 2-WL for exactly `r` rounds (lockstep across all copies, globally interned). This keeps
> every structural feature of the question — equivariance, all copies present, the same `X`, the same
> `Align` channel — while making the tag `y^{(r)}` **genuinely incomplete**. The reader's washout
> claim is level- and round-independent, so it predicts `Φ ≈ y` at every `r`. Measured:
> ```
>   L=4  r  y-cls Phi-cls orbits     L=5  r  y-cls Phi-cls orbits     L=6  r  y-cls Phi-cls orbits
>        0      1       4     20          0      1       5     90          0      1       6    544
>        1      4      20     20          1      5      90     90          1      6     544    544
>        2     20      20     20          2     90      90     90                 (fixpoint: 544)
> ```
> At `r = 1` the tag has **4 / 5 / 6** classes and `Φ` already has **all 20 / 90 / 544**.
> ⟹ **washout is false by measurement**, in exactly the regime — incomplete tag — where the question
> is live. ★★ **`L = 6` is the sharp row**: it is the first `L` with genuine 1-WL twins (`C₆`/`2C₃`,
> prism/`K₃,₃`), the tag is down to **6** classes, and `Φ` still separates **every one of the 544**
> marked-graph iso classes.
> ⚠⚠ **And this happens with NO RULER PRESENT** (`iso+inj = 0` at `r ≤ 1`). ⟹ the Ruler Lemma is
> **sufficient, not necessary** — the `Align` channel against the full family is stronger than the
> lemma needs. ★ Read the lemma as *the part of that strength that can be **proved** at large `L`*,
> where no measurement reaches; do **not** read it as a characterization.

⚠ **A trap paid for here, do not re-derive it.** At `L = 4,5` the fixpoint satisfies
*profile injective ⟺ `Aut(G_c)_i = 1`* exactly. ⛔ **Do not adopt the `⟸` direction as the ruler
criterion**: it says individualization + refinement always discretizes, which is precisely what CFI
graphs refute at large `L`. The honest hypothesis is **discreteness of the copy's own colouring**,
which is what (P1)/(P2) use and what `probe_cao_ruler_exists.py` measures.

#### 6e.4d.5 ⚠ WHAT IS PROVED, ARGUED, AND PINNED — read before quoting

> ### ⛔ TOP-LINE, **corrected 2026-08-16b**: the Ruler Lemma, (LB), (P1) and (P2) **are now
> machine-checked** (`RulerLemma.lean`, `CopyRestrict.lean`, `CopyProbe.lean`) — but the section's
> **conclusion is still not established**, because the *instantiation* of the lemma at the ensemble is
> not written and one of its two hypotheses fails as stated in the ordered-slot model. See the top
> box's green block for the exact remaining gaps, §6e.4e for the competing position, §6e.4g for what is
> left to do. ⛔ The list below is accurate about each step; it does not license the original verdict.

* **Proved (paper-level, not yet Lean):** the Ruler Lemma (§6e.4d, three lines, carrier-generic and a
  natural Lean target); *`col_E` restricted to a copy is finer than that copy's bare 2-WL*; (P1) and
  (P2) from within-copy discreteness. ⚠ Write that middle one in words — `Refines`/`⊑` is ambiguous in
  this project (`PartitionClosure.Refines` vs `Refine`'s `Colouring`-typed one).
* **Measured:** the decode in `M` at `L=4,5` **and in the real ensemble at `L=4`** (96 rulers, block
  `= |S₄| = 24`, 20/20 reps recovered); (P1)/(P2) at `L=6..9` in the **single-copy** object `M(H)`
  (the ensemble is unreachable past `L=4`); the kind census at `L=4`; the surrogate.
* **Pinned, inherited:** `Aut_{m(0)}(E) = S_L` (§3.2b); *"`a` determines `c`"* (§6e.4a, argued
  structurally + measured); §6f's arity bound and (iii)'s CFI literature, which are what make ORB
  false and hence make the LEMMA's falsity follow.
* ⚠ **The one soft joint:** the ensemble-side (P1)/(P2) are *proved* in §6e.4d.1 and *measured at
  `L = 4`*, but the `L = 6..9` confirmations are in the single-copy object. If a future reversal
  comes, it comes from there — so it is §6e.4d.1's paragraph, not a citation, that must be attacked.
  ⚠ Note the argument does **not** route through the collapse (i), so (i)'s status cannot affect it.

> ### ▶ WHAT WOULD FALSIFY §6e.4d
> ⚠⚠ **CORRECTION (reader, and it is right).** A first draft offered *"exhibit a copy whose within-copy
> `E`-colouring is coarser than that copy's own refinement"* as the falsifier. **That is circular and
> useless as a test:** the copy's own refinement already refines its `Aut`-orbits, so any such
> coarseness *is* a mixed cell — i.e. the falsifier asks for the counterexample the whole track is
> looking for. Withdrawn. The usable attacks are the ones that can fail *without* being the
> counterexample:
> 1. **Break (P2).** Exhibit a refinement-discrete copy whose reading of the frame is **not** injective
>    at some `L`. Then the block decodes to less than a function and the argument stops — with the
>    conclusion still undecided. `probe_cao_ruler_exists.py` tests exactly this (`L = 6..9`, all pass).
> 2. **Break the coherence step.** Show that a cross-copy pair colour does *not* determine the
>    alignment of the two readings — i.e. that restricting the WL sum to the frame fibre is not
>    available. This is the one step that is pure bookkeeping, so it is the cheapest to check and the
>    most damaging if wrong.
> 3. **Break the Ruler Lemma itself.** Exhibit any group, any equivariant family, any invariant tag
>    with an isolated injective member, where `Φ` fails to determine the orbit. The proof is three
>    lines, so this should be impossible — which is precisely why it is the right thing to attack.
> ⛔ **What would NOT falsify it:** any measurement at reachable `L` of the *conclusion* (vacuous), and
> anything about the collapse (i), which the argument does not use as an input.

### 6e.4e ⚖️ 2026-08-16 — **THE CASE FOR (B)**, stated at full strength, and why the evidence is SYMMETRIC

> ### ▶▶ **(B): the cross-copy channel supplies nothing the within-copy channel cannot.**
> The ensemble's family is closed under `S_L`, so everything computable from it is `S_L`-invariant.
> (B) says the uniform average over all copies **washes the alignment out**: a cross-copy pair reduces
> to the disjoint (triangle-frame) case, the exponential object buys nothing over the poly-size
> encoding, and the collapse (i) holds with equality. ⟹ a CFI payload **merges** at large `L`, giving
> the mixed cell, and Construction C works.

**What supports (B).**
* `M^{(r)} ⊑ E^{(r)}` **at every round** at `L = 4` (§6e.5's R1 box) — the ensemble is *coarser* than
  the single-copy encoding at every round measured, which is the direction (B) predicts.
* The cross-copy aggregate is exactly `M`-determined at `L = 4` (§6d.7), on every channel (§6d.3).
* Ensemble payload cells = `M`'s `μ`-classes = 20 at `L = 4` (§6e.4b) — the cross-copy channel added
  **nothing** there.

> ### ⚠⚠ AND NOW THE PART THAT MATTERS: **BOTH SIDES' MEASUREMENTS ARE CIRCUMSTANTIAL, FOR THE SAME REASON**
> * **(B)'s are forced.** `M` is a **complete** invariant at every reachable `L`. Nothing can be added
>   to a complete invariant, so "the ensemble equals `M`" had to come out true regardless of the
>   cross-copy channel's strength. The measurement had no power.
> * **(A)'s are equally circumstantial.** Every ruler measurement — the decode at `L=4,5`, (P1)/(P2)
>   at `L=6..9`, the kind census — was taken where the **within-copy channel already sufficed**. None
>   of them shows the ruler channel doing work that was *necessary*.
> ⟹ **the two positions are observationally equivalent at every size we can compute.** This is not a
> rhetorical concession; it is why §6e.4g admits only theorems and experiments.

> ### ⚠⚠⚠ THE SHARPEST POINT IN (B)'s FAVOUR — TWO DIFFERENT FAILURE MODES, AND ONLY ONE HAS BEEN TESTED
> The one measurement where the ruler channel provably supplied something the within-copy channel
> could not is §6e.4f's `P6` ablation. But there the within-copy channel fails because the copy has a
> genuine **automorphism** (reversal), not because 2-WL is **blind**. At large `L` the failure mode is
> WL-blindness. The Ruler Lemma does not distinguish the two — it only needs the readings to differ —
> but **empirically the ruler has only ever been seen to defeat the symmetry mode.** ⟹ *"it beats
> automorphisms, therefore it beats WL-blindness"* is an extrapolation, and it is (A)'s weakest joint
> alongside (LB). ⛔ Do not quote §6e.4f's `P6` result as evidence about CFI.

### 6e.4f ▶ 2026-08-16 — THE SESSION'S EXPERIMENTS, and exactly what each does and does not show

All reader-designed except the last two. ⚠ Each row says what it **cannot** show; that column is the
point of the table.

| # | experiment | result | ⚠ does NOT show |
|---|---|---|---|
| 1 | **The `C6` construction** (reader): 15 gauges, 6 rotated copies of the smallest asymmetric graph as rulers, 6 rotated copies of a payload. `probe_cao_c6_ensemble.py` | 102 vertices (not 152). cells = orbits in every variant; with `P6` the rotations act **freely**, so `Aut_v = 1` and one individualization **discretizes all 102** | anything about large `L` — six labels admits no 2-WL-hard pair |
| 2 | **Ruler ablation** on that object, from the plain colouring. `probe_cao_c6_ablate.py` | shared frame **+ ruler** → **6** payload cells; ruler deleted → 3; private frames → 3; private frames + ruler → 3. The ruler supplied *which end of its own path a vertex sits at* — invisible to any within-copy refinement | that the channel survives **WL-blindness** — see §6e.4e's box |
| 3 | **Mirrored-ruler repair** (reader): close the ruler set under `D₆` instead of `Z₆` | `\|Aut\|` 6 → 12, cells **6 → 3** = orbits, positions `[0,5][1,4][2,3]`. Symmetrising **merges orbits**; it does not hide information | that symmetrising can *create* a mixed cell — it moves the target |
| 4 | **Full `S_L` closure** — every relabelling of every base graph present. `probe_cao_fullclosure.py` | `P5` 3=3 · chair 4=4 · `P5`+chair+`C5` **8=8** · `C6`+`2C3` 2=2 · prism+`K₃,₃` 2=2, all mixed = 0 | ⚠ **"preserves all symmetries ⟹ detects none" is false as stated** — closure kills *labellings*, and `S_L` is not transitive on marked graphs. But none of these objects has a 2-WL-hard pair |
| 5 | **Is a ruler a bolt-on device?** (reader) `X` = rook(4,4) ⊔ Shrikhande — 32 vertices, 2 orbits, **1 cell**, a genuine 2-WL mixed cell with no CFI needed. `probe_cao_ruler_bolt_on.py` | ⛔ **NO.** private ruler on every vertex → still 1 cell; one shared ruler → 1; rulers + hub → 1. Only attaching to **one** vertex resolves it, and that is individualization | ★ this is the cleanest **limit** on (A): the ruler is not a general orbit oracle. Its power needs members with **readings of a shared frame**, and manufacturing those from an arbitrary graph costs exponential size |
| 6 | **Falsification search** for the conditional *ruler ⟹ no mixed cell*. Exhaustive over `S_4`-closed families, round by round. `probe_cao_ruler_falsify.py` | 1491 objects; **1487 have a mixed cell at some round** (the search had teeth); mixed at `r=0`: 1487, `r=1`: 1450, `r=2`: 0. **0 falsifiers** | ⚠ **thin margin**: rulers first appear at `r=2` and mixed cells vanish at `r=2`, so the two coincide. *"Both happen once the colouring is fine enough"* is **not excluded** |
| 7 | **(LB) measured**, real ensemble `L=4`. `probe_cao_lowerbound.py` | all **64/64** copies: the ensemble's within-copy vertex colouring refines the copy's bare 1-WL and 2-WL, and its within-copy **pair** colouring refines the copy's bare 2-WL | that (LB) holds at large `L` — it is proved on paper, measured only here |

### 6e.4g ▶▶▶ THE DECISION PROCEDURE — the only next steps. ⛔ No more prose on this question.

Three sessions of argument have not moved the disjunction. Each item below settles it one way or the
other and each is a **theorem or an experiment**.

| # | item | settles | status |
|---|---|---|---|
| **1** | ★ **Formalize the Ruler Lemma** — `Γ` acting on `X`, equivariant `b : Ω → C^X`, invariant tag `y`, one `ω₀` with `y⁻¹(y ω₀) = Γ·ω₀` and `b_{ω₀}` injective ⟹ `Φ` determines the `Γ`-orbit of `b_ω` | whether (A)'s **engine** is sound | ✅ **DONE 2026-08-16b** — `RulerLemma.ruler`, `phi_eq_iff_orbit`, plus a non-vacuity witness (`Φ` strictly finer than the tag) |
| **2** | ★★ **Formalize (LB)** — the ensemble's colouring restricted to a copy refines that copy's own 2-WL closure | (A)'s **single load-bearing structural claim** | ✅ **DONE 2026-08-16b** — `CopyRestrict.lb`, every `L`, real object; carries `restrict_sig_eq` and **§6b** (`encoded_edge_eq`) |
| **3** | **Formalize (P1)/(P2)** for the ensemble from (LB) + refinement-discreteness of a chosen copy | ~~1+2+3 ⟹ (A)~~ ⛔ **that claim was too strong** | ✅ **DONE 2026-08-16b** — `CopyProbe.tag_isolates`, `profile_injective`, `transfer`; ★ corollary `sameLabelOrbit_of_tag` |
| **4a** | ▶▶ **The coherence chain** (§6e.4d.3's arrows 1–2): *diagonal colour ⟹ `Φ_E`*. Machinery exists — `CopyProbe.sig_singleton_snd` for *"a pair colour determines endpoint diagonal colours"*, `CopyRestrict.sig_restrict` at the frame injection for *"a pair colour determines `Align`"* | pure bookkeeping; do it first | ▶ **NOT WRITTEN** |
| **4b** | ▶▶ **Instantiate `RulerLemma` at the ensemble.** Equivariance is free (`Ensemble.invG_eRoot`). ⛔ Blocked on the **ordered-slot** model: the ruler's reading is 2-to-1 on twins, so hypothesis (ii) fails. ★ Fix: weaken `eq_of_align_eq`'s *"`v` injective"* to *"`v` refines `u'`"* (every reading is twin-invariant), and cut `Ω` down to **proper symmetric** copies | **(A) directly**, given 4a and 4c | ▶ **NOT WRITTEN** — needs an `Ensemble.lean` model refactor |
| **4c** | **Existence of a refinement-discrete copy** in `E(L)` (Babai–Erdős–Selkow + §6e.4d.2) | (A)'s remaining input | ▶ measured only (5760/32768 at `L=6`) |
| **5** | **For (B):** either prove §6d.8's lemma (the cross-copy aggregate is `M`-determined at the fixpoint), or **exhibit an object with a ruler AND a surviving mixed cell**. The harness exists (`probe_cao_ruler_falsify.py`); extend it to `L=5`, more rounds, and to carriers that are not the frame encoding | **(B) directly.** One such object refutes (A) without any large-`L` argument | ▶ open. ★ `sameLabelOrbit_of_tag` narrows the search: **both** members of the mixed pair must be non-discrete |

> ### ⚠ WHAT WOULD *NOT* SETTLE IT — each of these has already been tried this session
> * Any measurement of the **conclusion** at reachable `L` — vacuous, `M` is complete there.
> * Any measurement of a fully-symmetrised small object — settled (§6e.4f #4), and it does not reach
>   the WL-blind regime.
> * Any further **argument** from either side about washout. Both have been stated at full strength;
>   they are observationally equivalent (§6e.4e).

### 6e.5 ▶ FOUR CANDIDATE RESOLUTIONS, best first

> #### ⛔⛔⛔ 2026-08-15 — R1 AND R3 ARE BOTH DEAD. §6e.4a refutes the lemma outright and proves `M⁺` complete. Kept as a record of the plan, not as work to do.

**R1 — round-indexed induction (most likely to work).** Prove the collapse and the lemma together by
induction on the WL round `r`: `b^{(r)}(c',l)_k` is determined by round-`(r−1)` data, and the
induction hypothesis supplies its `M`-form. §6e.3 is the base case. **Obligation:** find the right
round-indexed invariant — a statement of the shape *"the round-`r` slot profile is a function of
(round-`(r−1)` data local to `k`) and (`μ`-determined globals)"*.

> #### ⚠⚠ R1's PREMISE WAS UNTESTED, AND HALF OF IT IS FALSE — `scratchpad/probe_cao_roundmatch.py`, `L = 4`, 2026-08-13
> Every earlier measurement (§6d.3) compares only **fixpoints**: the prober runs `M` for 12 rounds and
> the ensemble to stability. R1 needs a *round-wise* correspondence, and that had never been looked at.
> Measured, as a refinement relation on payload pairs at every `(r_E, r_M)`:
> ```
>            M0       M1       M2       M3+          E colours: e0,e1 = 2   e2 = 52   e3,e4 = 60
>   e0     IDENT   M-fine   M-fine   M-fine         M colours: m0 = 2  m1 = 24  m2+ = 60 (fixpoint)
>   e1     IDENT   M-fine   M-fine   M-fine
>   e2    E-fine   E-fine   M-fine   M-fine
>   e3    E-fine   E-fine    IDENT    IDENT
>   e4    E-fine   E-fine    IDENT    IDENT
> ```
> **⛔ There is no INTEGER offset `s` with `E^{(r)} = M^{(r+s)}`.** `s = −1` matches `e1 = m0` and
> `e3 = m2` but fails at `e2`, which sits **strictly between** `m1` and `m2`. So R1 must **not** be
> stated as a round-indexed *equality* — that statement is false, and an induction carrying it cannot
> close.
>
> ⚠ **Read this as a DELAY, not a divergence** (reader, 2026-08-13, and it is the better reading). The
> ensemble is running the same refinement one step behind and *half a step out of phase* — `e2` lands
> between two `M` rounds rather than off to the side, which is exactly what a construction that must
> first earn the frame types (§6b) before it can use them would produce. Nothing here says the two
> objects compute different things; it says the schedules do not line up on integers. ⟹ the correction
> to R1 is about the **shape of the invariant**, not about whether the collapse is real.
>
> **✅ But the one-sided invariant holds at every round, with slack:**
> > ### ▶ `M^{(r)}` **refines** `E^{(r)}`, for every `r` (`IDENT` or `M-fine` on the whole upper triangle `r_M ≥ r_E`).
> ★ Two things follow, and they change what R1 should carry. **(1)** The chains are **nested, never
> `INCOMPARABLE`** — the two refinement schedules interleave monotonically rather than diverging, which
> is the good case. **(2)** The surviving direction is *exactly* the one §6d.1 consumes: `M` finer than
> `E` is what turns an `M`-merge into an `E`-merge. ⟹ **the refutation never needed the collapse to be
> exact.** §6d.8's lemma states an equality; only `⊑` is load-bearing, `M` reaches its fixpoint a round
> **before** the ensemble, and that slack is what an induction gets to spend.
>
> ⚠ Honest limit: this does not shrink the *analytic* obligation much — proving `M^{(r+1)} ⊑ E^{(r+1)}`
> still requires the cross-copy aggregate to be `M`-determined, which is §6d.8. What it changes is the
> **shape** R1 carries (one-sided, not equality) and it promotes **R3** from fallback to co-equal
> first target: any *finer* stable `s` between `M` and `WL_E` also carries merges, so over-approximating
> the cross-copy channel is legitimate from the start rather than a concession after failure.

**R2 — finite-range dependence.** Show `b(c',l)_k` depends on `c'` only through slots within bounded
distance of `k` (share a label, or share a label with a label of `k`). Then `b` is a finite-range
field over i.i.d. bits and exchangeability is replaced by a local-independence argument.
⚠ Probably false at the fixpoint (WL colours are global), but plausible for a bounded number of
rounds — so it composes with R1 rather than replacing it.

> #### ⛔⛔ 2026-08-14 — READ §6f.5a(β) BEFORE ACTING ON R3. Adjoining `Φ` **re-opens (ii)**, at an exactly-known price (`AtomAugment.adequateFor_augment_iff`), and `Φ` is at least an orbit computation, so the price looks unpayable. ▶ The surviving form is the **reframe**: adjoin only tuple-determined data; ceiling = `pull (bOf s)`.

**R3 — ⭐ the workaround that keeps the payoff even if the collapse is false.** We never needed the
*exact* collapse; §6c.3 needs an **upper bound by something incomplete**. Define `M⁺ = M` with `Φ`
adjoined as an extra colour coordinate, close under refinement, and show the closure terminates with
a bounded description. Then `ensemble ⊑ M⁺`, and the refutation route survives **provided `M⁺` is
still not a complete invariant**. ★ This turns a failed proof into a weaker but usable one, and it
should be kept in reserve from the start.

**R4 — the logical route.** A 2-WL colour is a `C³` (three-variable counting logic) type. Show
`Φ(c,i)` is `C³`-definable over `M(c)`, hence determined by `μ_c(i,i)`. The sum over all `c'` is a sum
over a *fixed, uniformly described* family — precisely the reader's uniformity — and the technical
content is that aggregating against a uniformly described family of 2-WL structures stays inside 2-WL.
**Cleanest if it works**; the work is in making "uniformly described" expressible.

### 6e.6 ▶ WHAT WOULD FALSIFY THE APPROACH

A single pair `(c,i)`, `(e,m)` with `μ_c(i,i) = μ_e(m,m)` but `Φ(c,i) ≠ Φ(e,m)`. `probe_cao_lemma_check.py`
searches for exactly that and is cheap at `L = 5`; ★ **`L = 6` is the next rung and is the highest-value
run in the plan** (`2^15` copies × a 36-vertex `M`), because it is still `M`-only. A failure there would
make **R3 mandatory** and would localize which feature of `a` beyond §6e.3's (i)/(ii) the fixed
distribution `D` resolves.

---

## 6f. ★★★ THE ENCODING'S WL GAIN IS **BOUNDED BY A PROOF** — so the payload search is not needed

**Raised and argued 2026-08-13, reviewing §5.2.** ⚠ *Argued, not machine-checked and not yet written
out in full* — see the caveats at the end. But it is the single largest change to what should be done
next, so it is stated before it is polished.

### 6f.1 The gap it closes

§5.2 records two live readings of how much the frame encoding gains over bare WL — *"exactly one
level"* vs *"doubling"* — and says **"neither bounds the gain above"**, which is why `CFI[K5]`-full was
"the decisive cell" and why §6d.9 concluded a C 2-WL was finally worth building. **The gain is bounded
above, and the bound needs no measurement at all.**

### 6f.2 `M(G)` is a fixed-dimension interpretation of `G`

`M(G)` (§6d.6) is: the payload as `K_L`, plus two frame vertices per slot, `f(k,0) ~ f(k,1)`, with
`p(i) ~ f(k, G_k)` for `k ∋ i`, frame vertices coloured by `t`. Code its universe inside tuples over
`G`'s:

```
   p(i)          <-  (i, i, 0)
   f({a,b}, τ)   <-  (a, b, τ)      modulo the definable involution (a,b,τ) ~ (b,a,τ)
   adjacency, and the colour τ, are FO-definable from G's edge relation:
       (i,i,0) ~ (a,b,τ)   iff   (i = a ∨ i = b) ∧ ( τ = 1 ↔ E(a,b) )
       (a,b,τ) ~ (a,b,1−τ) ;   (i,i,0) ~ (j,j,0) for i ≠ j
```

So `M(·)` is a **3-dimensional FO interpretation, uniform in `L`** (the formulas do not mention `L`),
into `G` expanded by two constants, with every quotient class of **constant size 2** — which is the
technical point that makes the counting translation go through. By the standard interpretation lemma
for counting logic (a `C^m` formula over the interpreted structure pulls back to a `C^{d·m}` formula
over the base), and `k`-WL ≡ `C^{k+1}`:

> ### ▶ **`2`-WL on `M(G)`** is refined by **`8`-WL on `G`** — and generally **`k`-WL on `M(G)` ≼ `(3k+2)`-WL on `G`**, for a constant that does **not** depend on `L`.

⚠ `8` is a deliberately crude constant (`C³ → C⁹`). Counting the coordinates that actually occur —
payload pairs are 2-tuples, payload–frame pairs are 3-tuples, frame–frame pairs are **frozen** and
carry nothing, and one update step adds ≤ 2 — suggests `4`-WL suffices. **The constant does not
matter; only that it is finite and uniform in `L`.** Freezing only coarsens, so the bound covers
`M_frozen` a fortiori.

### 6f.3 What it buys — §6c.3's template, executed at rung 2, with no computation

§6c.3 asks for *"`E(L)`'s `k`-WL closure on the payload `≤` some invariant already KNOWN to be
incomplete"*, and names bare-`m`-WL as the natural target because CFI over a base of treewidth `m+1`
then supplies the witness **by a theorem**. Composing:

```
  (i)  ensemble-2-WL  ⊒  M_frozen-2-WL          -- §6d.8's lemma, ONE-SIDED (§6e.5 R1 box).  ⛔ OPEN
  (ii) M_frozen-2-WL  ≼  6-WL on the payload    -- §6f.2, TIGHTENED by §6f.5a(γ).      ✅ PROVED k=2
  ---------------------------------------------------------------------------------------------
  take X of treewidth >= 7 (K8).   CFI(X,0), CFI(X,1) are 6-WL-equivalent  [CFI, literature]
  => their M's are 2-WL-equivalent => equal colour MULTISETS => some i in one, l in the other
     share a colour;  CFI(X,0) not iso CFI(X,1) => p(c,i), p(c',l) lie in DIFFERENT Aut_{m(0)}-orbits
  => a MIXED CELL  =>  2-WL CAO PROPAGATION IS FALSE.
```

> ### ★★★ The refutation needs **no merging payload to be found, and no large 2-WL run**. `CFI[K₈]` is *guaranteed* to merge by the two bounds; it is never computed. The only open input is (i).
> ⚠⚠ **2026-08-15: (i) is not merely open — it has NO PROOF ROUTE (§6e.4c).** The constants here are
> §6f.5a(γ)'s (`2k+2`, so `6`/`K₈`), **not** §6f.2's crude `3k+2` (`8`/`K₁₀`), which the Lean superseded.

★ And it **scales**: `k`-WL on `M` ≼ `(3k+2)`-WL, so CFI over a base of treewidth `3k+3` refutes level
`k` — provided the collapse holds at level `k` (§6d.5 makes it level-uniform at `k = 1, 2`; higher is
untested). ⟹ the construction is aimed at *every* fixed WL level, not just rung 2.

### 6f.4 ⚠⚠ WHAT THIS SUPERSEDES — and one thing it makes vacuous

* §5.2's *"neither bounds the gain above"* and its two live readings — **superseded**; the gain is
  bounded by a constant, so the *"doubling"* reading is no longer a threat to the programme, it merely
  moves which CFI base is needed.
* §5.2's *"the one measurement that would settle it"* (`CFI[K5]`-full) and §6d.9's *"a C 2-WL is worth
  building after all"* — **downgraded from decisive to constant-pinning.** They would tell us whether
  the true constant is 3, 4 or 8; they are no longer on the critical path. ⛔ Do not build the C 2-WL
  or hunt for a small 3-WL-blind pair (outstanding B.3) as if the refutation depended on it.
* ⚠ **It makes §6c's `GI ∈ P` characterization vacuous at every fixed `k`** — if 2-WL CAO propagation
  is *false*, then *"2-WL CAO propagation ⟹ `GI ∈ P`"* has a false antecedent. §6c keeps its value
  only for **non-WL** propagation algorithms, which is where the reader's original question lives.
  ⟹ these are two exits from the same door, and the refutation exit **strictly dominates** for the
  purpose of settling the WL levels. Both need (i).

### 6f.4a ✅ THE LEAN SKELETON IS BUILT — `ChainDescent/FrameEncoding.lean`, 2026-08-13

The formalization is scoped in three inputs, and only the middle one is ours to prove:

```
  (i)   ensemble-2-WL  ⊒  M-2-WL        -- §6e.4.  OPEN mathematically  => a named hypothesis
  (ii)  M-2-WL  ≼  bounded-WL on G      -- §6f.    OURS                 => the Lean target
  (iii) CFI over high treewidth is bounded-WL-blind   -- literature, a pebble-game argument over
        arbitrary-treewidth bases; a formalization project in its own right => a named hypothesis
```

**Landed** (axiom-clean, no `sorry`, no custom axiom, gate-listed):

| | |
|---|---|
| §1 | the 2-WL round at a **generic finite carrier** (`roundG`, `isRound_roundG`, `wl2G`, `refines_wl2G_of_stable`) — `CaoTarget.round2` is the `Fin n` case, and the encoding's carrier is a sum type |
| §2 | `MVert`, `mAdj`, `mInit` — the §6d.6 object |
| §3 | the coding `MVert L → TCode L` (**injective**, proved) and `Adequate` |
| §4 | ★★★ `refines_wl2G_of_adequate` and **`merge_of_adequate`** — the transfer bound, and the only consumer form, so the direction cannot be got backwards |
| §5 | a non-vacuity witness, ⚠ **flagged degenerate** |

**Three modelling decisions, each of which shrank the build and each of which is recorded at source:**
* **Unfrozen.** §6d.6 freezes frame–frame pairs; the Lean file uses the **plain** round. Stability
  against it is strictly *stronger*, and the unfrozen closure refines the frozen one, so the frozen
  conclusion follows by transitivity. ★ It also makes pin (i) **weaker**, hence safer to carry.
* **Ordered slots.** Two twin frame vertices per unordered slot. Twins separate nothing, and it buys
  free `Fintype`/`DecidableEq` instead of an index bijection into `Fin N`.
* **Types atomic.** `mInit` hands each frame vertex its type; in the ensemble it is *earned* (§6b).
  This makes the guess's target **finer**, hence pin (i) **stronger** — the honest direction.

### 6f.4b ✅ INCREMENT 2, PART ONE — `ChainDescent/TupleWL.lean`: **the block lemma is PROVED**

`k`-WL on tuples (`Tup k L := Fin k → Fin L`), landed axiom-clean and gate-listed:
`encList`/`encVec` with **injectivity at fixed arity** (what lets a colour *vector* be a `rankOf`
key) · `tupSig`/`tupKey`/**`roundT`**/**`isRound_roundT`** ⟹ FT1's whole closure theory now applies at
**every** arity, not just 2 · `wlT`, `refines_wlT_of_stable`, `stable_iff_tupSig`.

> ### ★★★ THE BLOCK LEMMA — `subst2_of_stable` / `substJoin_of_stable`
> `k`-WL stability is about replacing **one** coordinate; `Adequate.blocks` needs **two** (a frame
> vertex costs two fresh labels). They are not the same statement, and the gap closes by **nesting**:
> the inner multiset **factors through `s`** (stability at `j`), so the outer sum is the image of a
> *one*-coordinate substitution multiset under a fixed map — and that is determined by `s x` by
> stability at `i`.
> ⟹ **each extra coordinate costs one nesting, `j` coordinates cost `j`** — which is *exactly* §6f's
> dimension count, now stated and proved with **no logic and no interpretation lemma**. This is the
> mathematical content of *"the encoding's WL gain is bounded"*.

### 6f.4c ✅ INCREMENT 2, PART TWO — COVARIANCE, and the two assembly-ready forms

`blocks`'s summand is a **pair** `(b (P₁, Z), b (Z, P₂))` — two different *reindexings* of one
combined six-label tuple — so the block lemma alone does not close it. Landed:

> ### ⛔ A DEAD ROUTE, RECORDED SO IT IS NOT RE-WALKED: covariance does **not** follow from `roundT`-stability.
> For a **permutation** `σ` it would: `(x ∘ σ)[i := v] = (x[σ i := v]) ∘ σ`, so the signature
> transports. For a **collapse** (`σ` non-injective — dropping and repeating coordinates, which is what
> padding needs) it fails: `(x ∘ σ)[i := v]` is not a reindexing of any update of `x`. The natural
> rescue — identify `v = x i` inside the signature by its colour — also fails, because a tuple whose
> `i`-th coordinate differs from all others has the **same equality pattern** as one with a *fresh*
> value there. ⟹ no amount of stability gives it.

▶ **The fix is to put it in the round.** `roundTS` records, beside the signature, the colours of
**every** reindexing `x ∘ σ`. It is a genuine refinement round (`isRound_roundTS`), it still yields
`SigDet` so §3's block lemma applies verbatim, and its stable colourings are covariant by construction
(`cov_of_stableS`). ⚠ It is *finer* than `roundT`, so the bound is **weaker** — the safe direction for
an upper bound — and it is still **bounded-arity**, so §6f.3's CFI input is unaffected in kind.

**The two shapes the encoding's two sums consume, both proved:**

| | |
|---|---|
| `exists_factor_cov` | covariance as a **function** of the colour (an implication cannot be mapped over a multiset) |
| **`substPair1_of_stableS`** | ONE fresh label, paired reindexings — the **payload** sum of `pairSigG_split` |
| **`substPair2_of_stableS`** | TWO fresh labels, paired reindexings — the **frame** sum; block lemma and covariance combined |

### 6f.4d ✅ INCREMENT 2, PART THREE — `Adequate` IS DISCHARGED. `ChainDescent/FrameTransfer.lean`

The plumbing closed, and the prediction *"no further ingredient is missing"* held. Gate = **129
modules, 254 s**, axiom-clean. `mk6` + the four reindexings `σA1 σA2 σB1 σB2` (each `funext i;
fin_cases i <;> rfl`) · `update4`/`update5` · `dec`/`tup6`/**`bOf`** · `payload_sum` and `frame_sum`
putting the two halves of `pairSigG_split` into `TupleWL` §5's shapes · **`blocks_bOf`** ·
**`adequate_bOf`** · **`merge_of_tuple_merge`**.

> ### ★★★ `merge_of_tuple_merge` — §6f's BOUND, MACHINE-CHECKED
> A merge under a **bounded-arity** (`k = 6`) tuple colouring is a merge in the **encoding's 2-WL
> closure**. `Adequate.blocks` — the clause §6f.4a opened — is now a **theorem**, from `roundTS`
> stability alone. ⟹ §6f goes from *argued* to **proved at `k = 2`**, and it never needed the `C^m`
> interpretation lemma.

⚠ **One side condition remains a hypothesis, honestly:** `adequate_bOf`'s `refinesAtoms` — that the
tuple colouring is fine enough to see `E`'s adjacency. It is discharged by closing an `E`-dependent
start colouring under `roundTS`, which is mechanical but not written.

> ### ⛔⛔ WHAT THIS IS **NOT** — read before quoting it
> It is the **transfer**, at `k = 2`. It is **not** a counterexample to CAO propagation, and five
> things stand between the two:
> 1. ⛔ **(i) the collapse is open mathematically** (§6e.4) — nothing yet links `M(E)` to `E(L)`.
> 2. ⛔ **(iii) CFI's WL-blindness is not formalized** — a pebble-game argument over arbitrary-treewidth
>    bases; a named hypothesis and a project of its own.
> 3. ✅ ~~the ensemble has no Lean object~~ **CLOSED 2026-08-14 — `ChainDescent/Ensemble.lean`**
>    (gate **129 modules**, axiom-clean): `eAdj`/`eInit`/**`eRoot`** with `m(base)` individualized, a
>    **generic `InvG` layer** for `roundG`/`wl2G`, the label action as an `Equiv`, `eact_base` (T4 at the
>    graph), and ⟹ ★ **`orbit_not_split`** — the free half, an orbit is never split. ⛔ **`MixedCell`**
>    is **stated, not proved**; `not_labelPropagates_of_mixed` is the bridge. ⟹ the target sentence is
>    now **expressible**. ⚠ Against **label** orbits (T2⁺ unproved) and ⚠ ordered slots ⟹ twin frame
>    vertices, so ⛔ never quote `Aut = ` the label group from it.
> 4. ⛔ **T2⁺ unproved** — only `Aut_{m(0)} ⊇ S_L` is machine-checked; *different orbits* needs the
>    "exactly" direction, plus root-is-CAO (§6c.1, argued).
> 5. ⛔ **"any `k`-WL" is not what this gives** — `TupleWL` is generic in `k`, but `FrameEncoding` is
>    2-WL-specific (`roundG` is the pair round) and the collapse is level-uniform only at `k = 1, 2`
>    (measured). Arbitrary `k` needs the encoding side re-run at arity `≈ 3k + 2`.

> ### ⛔ WHAT IS NOT PROVED, AND IT IS THE POINT: `Adequate.blocks`
> *The multiset over `z : MVert L` of the two half-colours is determined by the pair's own colour.*
> That **is** §6f.2's obligation, named. `pairSigG_split` (proved) decomposes that sum into a sum over
> one fresh label and a sum over two labels plus a bit — which is literally where §6f's dimension count
> comes from. ▶ **Increment 2 = a tuple-WL layer + the "multiset over `j` fresh coordinates" lemma,
> discharging `blocks` for a `k`-WL `b`.** ⚠ The witness in §5 is the *discrete* bound: it proves the
> skeleton is not vacuous and **nothing more**, since a discrete bound merges nothing.

### 6f.4e ✅ 2026-08-14 REVIEW — THE CROSS-GRAPH JOINT IS CLOSED. `ChainDescent/DisjointUnion.lean`

A review of the §6f.3 composition found **four joints that were not on the four-gap list**. This one
was real and is now closed; the others are recorded in §6f.5a.

> ### ⛔ THE DEFECT — `merge_of_tuple_merge` is SINGLE-GRAPH, the template consumes a CROSS-GRAPH merge
> `FrameTransfer.merge_of_tuple_merge` fixes one `E` and merges two vertices of `M(E)`. §6f.3 instead
> wants `x ∈ M(CFI(X,0))`, `y ∈ M(CFI(X,1))`. Worse, its premise compares `rankOf` colours produced by
> **two separate runs** — colours that are not comparable at all. Every `M`-model statement in this doc
> that writes *"`M`-col`(c,i)` = `M`-col`(c',l)`"* quietly assumes a common structure.

★ **The fix is not a patch — the two halves are one fact.** WL-additivity on a disjoint union turns
*"`A`, `B` are `m`-WL-equivalent but non-isomorphic"* into *"the **single** graph `A ⊔ B` has a `k`-WL
cell meeting two `Aut`-orbits"*: no automorphism crosses non-isomorphic components, while WL does not
separate them. ⟹ the single-carrier shape `merge_of_tuple_merge` already has **is** the right shape,
and the cross-copy comparability that the `M` model rests on is licensed at the same time.

**Landed** (gate **130 modules, 236 s**, axiom-clean, no `sorry`, no custom axiom):

| | |
|---|---|
| §1–2 | `dAdj`/`dInit` (⚠ **side-blind** atoms — tagging the sides would forbid the merge by fiat) · `side` · the split `pairSigG = sigL + sigR` |
| §3 | **`Blocked A B u κ`** — intra pairs carry their own side's run, **cross** pairs carry *only* the two endpoint diagonal colours through `κ`, cross never confused with intra (`sep`), `endFst`/`endSnd`, own-side signatures agree **across the two sides** (`sideDet`), and ★ **`diagEq`** |
| §5 | `ownP_eq`/`ownQ_eq` — the two `exists_factor` steps that make the sides comparable |
| §6 | ★★★ **`stable_of_blocked`** — case A (both intra) needs `sideDet` + `κ` + `diagEq`; case B (both cross) needs `ownP_eq`/`ownQ_eq`; `sep` forbids the mixed case |
| §7 | **`refines_wl2G_of_blocked`**, and the consumer **`merge_of_blocked`** |
| §8 | ★ non-vacuity, and it **merges**: `wl2G_double_merge` — 2-WL cannot separate the two copies of `A ⊔ A`, *even when each side's own colouring is discrete* |

★ **`diagEq` is where *"the two sides are WL-equivalent"* enters**, and it is used in exactly one case
(A2). ★ The `A ⊔ A` witness is deliberately not a CAO statement — the copies *are* one orbit there;
it exists so `Blocked` is inhabited by something that actually fires `merge_of_blocked`, not by a
discrete bound that merges nothing (the `FrameEncoding` §5 trap).

⚠ It does **not** supply a `Blocked` witness for a CFI pair — that is input (iii), literature.

### 6f.5a ⚠⚠ THREE JOINTS THE FOUR-GAP LIST DOES NOT NAME — found 2026-08-14, two still open

> #### ✅✅ (α) — **CLOSED 2026-08-14**, and the dead route it rested on is RETRACTED. `ChainDescent/TupleCov.lean`
> §6f.4c correctly put covariance **into the round**, because it does not follow from `roundT`-stability
> (the dead-route box). ⟹ `roundTS` is *finer* than `roundT` — the safe direction for an upper bound,
> but the CFI theorem says CFI over treewidth `> m` bases is indistinguishable by **standard `m`-WL**,
> and nothing on record puts `roundTS` at arity `m` below that. §6f.4c's *"bounded-arity, so the CFI
> input is unaffected **in kind**"* is carrying real weight.
> ⛔ **The planned fix — restate (iii) in pebble-game / `C^{m+1}` form — was NOT needed, and would
> not have been enough.** It gets the input in the door but leaves the relation to standard `k`-WL to
> be drawn back out, which is the actual claim. ★ **A better answer was available and is now proved.**
>
> ### ★★★ THE DEAD ROUTE WAS NOT DEAD. §6f.4c rejects *"identify `v = x i` in the signature by its colour"* because a coordinate distinct from all others has the same equality pattern as a fresh value. **True for `v = x i` — but a COLLAPSE NEVER NEEDS THAT CASE.** A collapse writes into a coordinate it does not read from, and `x[i := x j]` with `i ≠ j` has coordinates `i` and `j` **equal**, which the equality pattern *does* see.
>
> **Landed** (gate **131 modules, 239 s**, axiom-clean):
>
> | | |
> |---|---|
> | §1 | `Cov`/`CovPerm` · ★ **`stableS_iff`** — `roundTS`-stability **is** `roundT`-stability **plus** `Cov`, nothing else. This is what prices §6f.4c's move |
> | §2 | ★★★ **`subst_of_stable`** — from `roundT`-stability alone plus one equality marker, the colour of `x` determines the colour of every `x[m := x j]`. One-element extraction: exactly one `v` marks coordinate `i` against `j` |
> | §3 | `covPerm_roundT`/**`covPerm_wlT`** — permutations, by induction **on the rounds** (⚠ not available from stability; that asymmetry is why the two halves need different proofs) |
> | §4 | **`cov_idem_of_stable`** — idempotent reindexes, by iterated substitution along `part ρ S`. ★ Idempotence is the right target because `ρ` fixes `im ρ` pointwise, so a write never clobbers a position a later step reads |
> | §5 | **`exists_perm_comp_idem`** — every `σ` factors as `π ∘ ρ`, `ρ = (section of σ) ∘ σ` idempotent, `π` from `Equiv.extendSubtype` |
> | §6 | ★★★ **`stableS_wlT`** — the **standard `k`-WL closure is already `roundTS`-stable** |
>
> ⟹ ⛔⛔ **`roundTS` adds NOTHING over standard `k`-WL on a closure**, so §6f.4c's round was a sound
> but **unnecessary** detour, and (iii) may be stated in its literature form:
> *base treewidth `≥ k+1` ⟹ the two CFI graphs are `k`-WL indistinguishable* — confirmed against the
> literature 2026-08-14. With arity 6 that is treewidth ≥ 7, i.e. **`K₈`**, matching (γ).
> ▶ **Residual, both instantiation not mathematics:** `CovPerm` of the start colouring, and
> `SeesEqAll` of the closure — both free for the atomic type of a tuple, but not yet written for the
> start `FrameTransfer` uses. ⛔ It does **not** formalize (iii); that is still literature.

> #### ✅ (β) — **PRICED 2026-08-14, and the price is bad for R3 as written.** `ChainDescent/AtomAugment.lean`
> §6e.5 promotes R3 (`M⁺ = M + Φ`) to a co-equal first target with one proviso — *"provided `M⁺` is
> still not a complete invariant"*. **There is a second cost, and it is now machine-checked.**
>
> ### ★★★ `AtomAugment.adequateFor_augment_iff` — THE PRICE, AND IT IS AN `iff`
> Augmenting the encoding's atoms by `extra` costs **exactly** `Refines (pull b) extra`: the adjoined
> data must itself be determined by the bounded-arity bound. Nothing less suffices, nothing more is
> needed. ★ The reason it is computable at all is structural — `Adequate`'s `blocks` clause is
> **start-colouring-free**, so the *entire* start-dependence of the transfer is the one `refinesAtoms`
> clause. ⟹ **R3 buys (i) with currency drawn from (ii)**; §6e.5 treats them as independent.
>
> ### ⛔⛔ AND FOR `Φ` SPECIFICALLY THE PRICE LOOKS UNPAYABLE
> `Φ(c,i)` depends only on the **`S_L`-orbit** of the slot profile `a(c,i)` (§6e.2), and at the
> fixpoint `a(c,i)` decorates each typed slot with an `M(c)`-2-WL colour. So `Φ` is at least as strong
> as *the isomorphism type of a WL-colour-decorated structure* — an **orbit** computation, not a WL
> computation. ⟹ this is not *"unmeasured"*; it is on the wrong side of the line, and §6e.2's own trap
> box says why it had better be. ⚠ Not a proof that `Φ` fails `Refines (pull b) Φ` — that is now a
> stated, checkable obligation rather than a silence.
>
> ### ▶▶ THE REFRAME — RUN R3 IN THE OTHER DIRECTION
> Instead of *adjoin `Φ`, then hope it is bounded*, adjoin only data that is **tuple-determined by
> construction**; then (ii) is free and the whole obligation stays on (i), where it belongs.
> `AtomAugment.adequateFor_augment_self` is the ceiling for that: **the strongest augmentation this
> route can carry is `pull (bOf s)` itself.** ⟹ the precise sense in which R3 cannot over-approximate
> the cross-copy channel for free. ⚠ `merge_of_tuple_merge_aug` is the augmented consumer, with `hex`
> — the whole of (β) — visible as a hypothesis.

> #### ▶ (γ) THE CONSTANT IS `2k+2`, NOT `3k+2` — the Lean already beat the interpretation lemma.
> §6f.2 reads `3k+2` off a 3-dimensional interpretation, but the third coordinate is a **`Bool`** — a
> bounded decoration, not a label. The Lean count is the honest one: a coded `M`-vertex spends **2**
> labels and a fresh `z` spends **≤ 2**, so arity `2k+2`; `k = 2 → 6`, which is exactly `FrameTransfer`'s
> `mk6`. ⟹ **`2`-WL on `M` ≼ arity-`6` WL on `G`**, and the CFI base needs treewidth **≥ 7** (`K₈`),
> not 9 (`K₁₀`). Both are crude so nothing downstream breaks — but ⛔ stop quoting the numeral `8` and
> `K₁₀` as if the interpretation lemma were the source, and §6f.5 caveat 2's *"the tightening is
> unexamined"* is **superseded**: the Lean tightened it.

### 6f.5 ⚠ Caveats, stated so they travel

1. **Argued, not proved.** The interpretation lemma for `C^m` under `d`-dimensional quotient
   interpretations is standard, but it is cited here from memory and has **not** been written out
   against this specific interpretation. ▶ Pin it before quoting the numeral. ★ §6f.4a's Lean route
   **bypasses the logic entirely** — it asks for `Adequate.blocks` directly, by the same
   stable-guess method as §6d.1, so the citation is a sanity check on the constant rather than a
   dependency of the proof.
2. **The constant is crude** and the tightening is unexamined (§6f.2).
3. ⚠ It is consistent with everything measured: `M`-2-WL separates Shrikhande/rook and `CFI[K4]`
   (both need ≥ 3-WL bare), which sits inside `≤ 8`. It predicts `M`-2-WL **fails** on a CFI pair over
   a large enough base — ★ and *that* is a falsifiable prediction the constant-pinning runs would test.
4. ⛔ It does **not** touch (i). The whole programme still rests on §6e.4.

---

## 6g. ★★★ THE OPPOSITE-SIDE ATTACK — *"the bare frame is Tinhofer anyway"*. ✅ HALF TRUE, AND THE OTHER HALF IS THE WHOLE PROBLEM

**Raised by the reader 2026-08-13**, independently of whether CAO propagates: the frame's own
structure — `L` payload vertices plus one vertex per slot, incidence only; this is the subdivision of
`K_L`, whose slot part is the triangular graph `T(L) = J(L,2)` — should be **Tinhofer**, because every
individualization set produces a CAO residue. Individualizing a payload vertex splits by distance and
no further; individualizing a slot vertex acts like individualizing its two endpoints *to a common
colour*. Measured — `scratchpad/probe_cao_frame_tinhofer.py`, orbits by brute force over `S_L`, so
nothing here is heuristic.

### 6g.1 ✅ (A) THE BARE FRAME, POINTWISE — holds everywhere tested

```
L=4: 176 individualization sets, |S| <= 3   FAILURES 0
L=5: 576 individualization sets, |S| <= 3   FAILURES 0
L=6: 232 individualization sets, |S| <= 2   FAILURES 0
```

★ **And there is a reason, which is the right way to state the claim.** Pointwise individualization
can only ever induce a **partition of the labels**, whose setwise stabilizer is a **Young subgroup**
`S_{B₁} × … × S_{B_r}`. A Young subgroup's orbits are: the blocks (on payload) and the *unordered
pairs of blocks* (on slots) — which is **exactly** what 1-WL computes, since a slot vertex's entire
1-WL view is the pair of its endpoints' colours. ⟹ (A) is a statement about Young subgroups, and that
is what makes it true. ⚠ Evidence to `|S| ≤ 3`, not proof.

> ### ⚠ CORRECTION — *"within an orbit every ordering is a valid automorphism"* is FALSE on slot cells
> It holds on **payload** cells (a block's full `S_{B}` acts). It fails on **slot** cells: the cell of
> pairs of free labels has size `C(m,2)` and carries only the induced `S_m`-action, not the full
> symmetric group (`L = 6`, no individualization: 15 slots, `|Aut| = 720 ≪ 15!`). ⟹ the *"orbit of
> size 5 has 5! identical outputs"* property is **not** what makes (A) work — the Young-subgroup
> structure is. Do not lean on it.

### 6g.2 ⛔⛔⛔ (B) GROUP INDIVIDUALIZATION — NOT "unproven at 3+". **FALSE AT 4**, AND IT IS THE WHOLE PROBLEM

> ### ★★★ THE OBSERVATION THAT SETTLES IT: **a set of slots given one shared colour IS a graph.**
> `T` = a set of slot vertices `=` `E(H)` for a graph `H` on the labels, and the stabilizer of `T` in
> `S_L` is exactly **`Aut(H)`**. ⟹ *"Tinhofer under group individualization"* **is** *"1-WL reaches
> `Aut(H)`-orbits for every graph `H`"* — i.e. **every graph is 1-WL-amenable**, which is false.
> Group individualization of slots **is the payload encoding**. The opposite-side attack lands on the
> same wall, and it lands there in one line.

Swept exhaustively (every slot-set, orbits by brute force):

```
L=4:    64 slot-sets   FAILURES 0
L=5:  1024 slot-sets   FAILURES 0          <- so a counterexample needs L >= 6
L=6: 16384 slot-sets   FAILURES 1140       ★ smallest failing GROUP SIZE = 4
     witness  T = {04, 05, 12, 13}  =  H = K_{1,2} ⊔ K_{1,2}  (two "cherries")
```

★★ **The size-4 failure is on the SLOT cells, not the payload** — which is why it was not anticipated.
On `H` itself 1-WL is perfectly correct (centres degree 2, leaves degree 1 = the two orbits). On the
**frame**, the slot vertices `{2,3}` and `{4,5}` (two leaves of the *same* cherry) and `{2,4}` (leaves
of *different* cherries) all present 1-WL with the same view — `(¬T, {leaf, leaf})` — and never
diverge. *Same-cherry vs different-cherry is a **pairwise coincidence**, and §7's filter 6 says 1-WL
cannot read one.* ⟹ **the claim survives group sizes 1, 2 and 3, and dies at 4.**

**The second, starker failure mode — and it is the CAO-relevant one:**

```
L=7, T = E(C3 ⊔ C4), |T| = 7:  |Aut| = 48,  1-WL 3 cells vs 6 orbits  -> Tinhofer FALSE
                                ★ PAYLOAD: 1 cell vs 2 orbits  = a MIXED CELL
control  T = E(C3 ⊔ C3), L = 6:  1-WL 3 cells vs 3 orbits      -> Tinhofer TRUE  (Aut transitive)
```

⟹ at `|T| = 4` the frame fails on slots; at `|T| = 7` it fails **on the payload**, which is the
falsifier shape itself. `C3 ⊔ C4` is §5.2's own rung-1 witness, arrived at from the opposite direction.

### 6g.3 ▶ WHAT THIS IS WORTH — it is not only a negative

1. ⛔ **The route does not reach the payload.** The literature's Tinhofer/IR definition individualizes
   **pointwise**, so (A) is the literature statement and (B) is a strictly stronger property the
   payload needs. (B) is equivalent to `GI`-completeness of 1-WL amenability, so it cannot be patched.
2. ★★ **But (A) is exactly the theorem *"the frame is inert"***, which this doc has been asserting
   informally. It is the **1-WL analogue of §6d.2(a)**'s `≤ 12` frame bound at 2-WL, and it is
   stronger in kind: not just that the frame carries few colours, but that its skeleton is
   **IR-solvable at every individualization set**. ⟹ **100% of the hardness is in the payload
   colouring**, now from two independent directions (§6b at 2-WL, §6g at 1-WL).
3. ✅ **The reader's spine-fact step is already machine-checked** — *"the individualization set matters,
   not the order, so piecewise = all at once"* is `PartitionClosure.closure_meet_comm` /
   `reached_partition_order_free` (FT1). Nothing to prove there.
4. ▶ **(A) is a plausible Lean target** (Young subgroup ⟹ orbits = blocks and unordered pairs of
   blocks = the 1-WL slot colour), and it would discharge item 2 as a theorem. ⚠ Lower priority than
   §6f's `Adequate.blocks`, because (A) bounds the *easy* half.

---

## 7. Reusable filters extracted (apply before building)

1. **N1 / N2** (§0) — the fusing automorphism must move `v`; the distinguishing relation must be
   uniform at the root.
2. **The attachment-set test** (§1) — if the carrier's attachment set determines `v`, it is dead.
   ⚠ Conditional only; `Q₄` complementary pairs break its premise.
3. **The parity test** (§2.1) — complementary-pair carriers need `c` **even**.
4. **The `δ` test** (§3.2) — `1 ⊕ 1' = 2 ⊕ 2'` or the root is not CAO. ✅ **Discharged automatically**
   by complementary-pair corners (§3.2a); keep the test only for non-complementary designs.
4b. **The transposition-fixes-`m` test** (§3.2a) — for any frame shape, check that a label
   transposition is an automorphism *and* fixes the individualized central vertex. It is the cheapest
   way to catch a frame that silently loses T4, and it is what separates the three shapes.
5. **The payload admission test** (§5) — 2-WL-resistant *after the **full** frame encoding* (clique
   payload + typed frame vertex on **every** pair), not before, and ⛔ **not** after mere subdivision.
   ⚠ **Necessary only**, and ⚠⚠ **measured in a model that failed its audit (§6a)** — treat a failure
   here as a reason to look harder, not as a kill. The clause that is model-free is 5′.
5′. **The typed-common-neighbour test** (§6b) — ★ *if bare 2-WL separates the pair, it is dead*, and
   this one is a **theorem about the real object**: an edge encoded as a typed common neighbour is
   exactly what 2-WL counts, so no amount of frame-sharing or gauge symmetry hides it.
6. **The binary-coincidence test** (§2.4) — if the hidden fact is a pairwise coincidence, 2-WL reads it.
   ★ **And 1-WL does not** — §6g.2's group-size-4 failure is exactly this: a slot vertex's whole 1-WL
   view is its two endpoints' colours, so *"do these two leaves share a centre"* is invisible to it.
7. ★ **The partition-comparison rule** (§6a) — when validating an abstraction against the object,
   **compare the whole partitions, not one witness pair**. §6 validated on `C6`/`2C3`, which are
   2-regular and therefore agree under *every* candidate invariant; the abstraction was off by
   538 vs 292 cells and the test could not see it.

---

## 8. Files and reproduction

| file | what it does | runtime |
|---|---|---|
| `scratchpad/probe_cao_hypercube.py` | Construction B at `n = 352`; verified generators, true CAO start, mixed-cell verdict | < 1 s |
| `scratchpad/probe_cao_hypercube_2wl.py` | reduced 112-vertex model; 1-WL calibration + the 2-WL repair | ~5 s |
| `scratchpad/probe_cao_payload_pair.py` | Shrikhande/rook: 2-WL plain vs one-point extension (⚠ cases C/D never ran) | ~1 s for A/B |
| `scratchpad/probe_cao_triangle_frame.py` | the triangle-frame kill, 6 variants + controls; args `<disjoint\|shared> <none\|orbit\|minimal>`. ⚠ `freeze` was **not wired to argv** until 2026-08-13, so only the two `none` rows of §4.2 were reproducible from the committed file | ~1–3 min |
| `scratchpad/probe_cao_ensemble.py` | §6 — Construction C at rung 1, full symmetry, `n = 229406`; 100 mixed cells | ~2 min |
| `scratchpad/probe_cao_ensemble_audit.py` | **§6a** — the ensemble's 1-WL = (degree sequence, own degree); the 538/6 vs 292/100 comparison against the two-copy model | ~3 min |
| `scratchpad/probe_cao_ensemble_exact.py` | **§6a** — the same claim **elementwise** against the real 229406-vertex object, not by matching counts | ~2 min |
| `scratchpad/probe_cao_ensemble_2wl.py` | **§6b** — 2-WL on the REAL shared-frame ensemble, `L=4`, `n=332`; adjacency recovered, 0 mixed cells. The only 2-WL run in this doc on the real object | ~2 min |
| `scratchpad/probe_cao_cfi_bare.py` | **§5.1's premise** — `CFI[K4]`/`CFI[K5]` are 2-WL-blind bare. Was asserted but never checked in | ~1 min |
| `scratchpad/probe_cao_gauge2_ablate.py` | **§3.2c** — ablates the two channels at 2-WL: centrals **empty**, sharing over-separates on 1936/2016 copy pairs | ~5 min |
| `scratchpad/probe_cao_gauge2_saturate.py` | **§3.2d** — the copy set does **not** saturate; random *and* gauge-closed ladders. ⚠ its `coset` needs GF(2)-**independent** generators or the `2^j` labels silently lie | ~20 min |
| `scratchpad/probe_cao_gauge2_diag.py` | **§3.2c precision** — diagonal partition and separation verdict, not just pair colours | ~5 min |
| `scratchpad/probe_cao_bound_single.py` | **§6d** — the single-copy collapse: frame–frame = 12 classes, and `M(c)` reproduces the ensemble on payload-payload, diagonal and payload-frame | ~5 min |
| `scratchpad/probe_cao_bound_freeze.py` | **§6d.5** — the freeze rule: frozen single-copy = the ensemble at 1-WL (292, elementwise), unfrozen = 538 | ~2 min |
| `scratchpad/probe_cao_mfrozen.py` | **§6d.6 — THE FAITHFUL TEST, and the tool to reach for.** `M_frozen(G)` for any payload; args `sr` or `<m>` for `CFI[K_m]`. Shrikhande/rook at 256 v | ~5 min (`sr`) |
| `scratchpad/probe_cao_crosscopy.py` | **§6d.7** — cross-copy colours are rich but their aggregate is `M`-determined; the exact closed form. ⚠ its hypothesis C **must** use a multiset, not an ordered tuple (injective key ⟹ vacuous) | ~5 min |
| `scratchpad/probe_cao_lemma_check.py` | **§6e.0 — PHASE 0 of the proof plan.** `M`-only, so it runs where the ensemble cannot; args `<L> <reps>`. `L=4` calibrates, `L=5` passes, ▶ `L=6` is the next rung | `L=5` ~10 min |
| `scratchpad/probe_cao_frame_tinhofer.py` | **§6g** — is the bare frame Tinhofer? (A) pointwise: 0 failures; (B) **group** individualization of a slot set: ⛔ **fails at group size 4** (`L=6`, `T = E(K_{1,2} ⊔ K_{1,2})`), on the **slot** cells. Orbits by brute force over `S_L`, so no heuristic. Args `all|A|B` | ~15 min |
| `scratchpad/probe_cao_roundmatch.py` | **§6e.5's R1 box** — the ensemble/`M` correspondence **round by round**, which every earlier probe compared only at the fixpoint. ⛔ found: no round offset exists; ✅ the one-sided `M^{(r)} ⊑ E^{(r)}` holds throughout. Args `<L> <E-rounds> <M-rounds>` — ⚠ **`argv[1]` is `L`**, consumed by `probe_cao_gauge2_ablate` on import (I lost a run to `L=5`, a 6164-vertex ensemble) | `L=4` ~3 min |
| `scratchpad/probe_cao_gadget_check.py` | §3.2a(a) — gauge transitive on the 8 complementary pairs; `δ` constant | < 1 s |
| `scratchpad/probe_cao_gadget_variants.py` | §3.2a(b) — the three frame shapes vs the transposition-fixes-`m` test | < 5 s |
| `scratchpad/probe_cao_cfi_frame.py` | §5.1 — CFI payloads through the frame; args `<m> <sub\|full>`. Outputs kept: `cfi_frame_full.out` (faithful), `cfi_frame_unfaithful.out` (row 3, provenance) | 152/440 fast; 812 ~1 h |

**Lean — `ChainDescent/CaoCollapse.lean` (NEW 2026-08-13), the footing for §6d/§6e.** ★ The method of
§6d.1 was **already machine-checked** before this: `CaoTarget.refines_wl2_of_stable` (from FT1's
`PartitionClosure.refines_wl_of_stable`) says `wl2` is the **coarsest** stable refinement of the
atoms, and `CaoTarget.inv2_wl2` gives that WL colours are automorphism-invariant — i.e. *"WL is
coarser than the orbit partition"*, §6d.2(a)'s first half, done. `CaoCollapse` adds:

| | |
|---|---|
| `rootPair_upperBound_of_stable`, `ext_upperBound_of_stable` | §6d.1's method in the shape the collapse cites, at the root closure and after individualization |
| `merge_of_stable_merge` | ★ the **usable direction** isolated — a merge in the guess forces a merge in the closure — so a refutation argument cannot silently use the other one |
| `rounds_upperBound_of_stable` | the **round-indexed** form, which is the skeleton **R1** (§6e.5) consumes |
| `Slot`, `mapSlot`, `frameClass`, `frameClass_mapSlot`, `frameClass_overlap_le` | the frame layer; **invariance proved** and the **`≤ 12`** bound proved, uniformly in `L` |
| `FrameClassComplete`, `frameClass_eq_orbit_of_complete` | ⛔ the completeness half of §6d.2(a) **pinned as a `Prop`, not proved**, with its consumer recorded so proving the pin discharges it |

All declarations `[propext, Classical.choice, Quot.sound]` or a subset; no `sorry`, no custom axiom,
no `native_decide`. ▶ The pin's route is identified: `Equiv.extendSubtype` (Mathlib
`Logic/Equiv/Fintype.lean`) plus a three-case construction on `|k ∩ k'| ∈ {0,1,2}`, needing `4 ≤ L`.

✅ **BOTH CAO MODULES ARE NOW GATE-LISTED** — `CaoEnsemble` and `CaoCollapse` added to
`scripts/build.sh`'s `MODULES`; the gate passes. That discharges the doc's standing *"not gate-listed"*
caveat and outstanding item 6.

> ### ▶ 2026-08-15 PROBES ADDED (all in `scratchpad/`)
> * `probe_cao_lemma_check_np.py` — numpy port of `probe_cao_lemma_check.py`. `L=5` in **4 s** vs hours;
>   `L=4`→20/0 and `L=5`→90/0 reproduce the original exactly (validate on those before trusting it).
>   Args `<L> <REPS> <CHUNK>`. Frame frozen, colours interned **globally** across copies, `Φ` compared
>   by lexsort + sha256. ⛔ Its verdict is **vacuous at every reachable `L`** (§6e.4a).
> * `probe_cao_orb.py` — (A) ORB by brute force over `S_L`; (B) how many `b(c',l)` are injective on
>   typed slots (which is what makes LEMMA ⟹ ORB live). Imports the port; arg `<L>`.
> * `probe_cao_orb_mech.py` — the mechanism: does `a(c,i)` determine `c`, and how many `S_L`-orbits do
>   the profiles have. **This is the file that refutes the lemma.**
> * `probe_cao_ensemble_frame.py` — 2-WL on the **REAL ensemble** (`L=4`, `N=332`) with `m(base)`
>   individualized; extracts the ensemble slot profile `aE(c,i)` and answers: does it determine `c`,
>   how many are injective, how many `S_L`-orbits vs payload cells. ★ **This is the file that refutes
>   both "the ensemble's frame channel is coarser" and "outside-the-clique is 1-WL".** ~25 s.
> * `probe_cao_noclique.py` / `probe_cao_noclique_mech.py` — the same mechanism test with the payload
>   an **independent set** instead of a clique (`CLIQUE = False`, `ROUNDS = 20`). Answer: identical
>   figures ⟹ the clique is **not** the culprit.
> * `probe_cao_vacuity.py` — `μ`-classes vs marked-graph iso classes. ⚠⚠ **Trap paid for:** the
>   canonical form must send the marked vertex to `p[i]` *with the graph relabelled the same way* — the
>   first version applied `p` to the graph and `p` to the vertex inconsistently and reported 38/243
>   instead of 20/90, which would have inverted the conclusion.
> ⚠⚠ `pkill -f <probe name>` **kills the launching shell too** (its command line contains the string) —
> same trap as the gate's `pkill -f 'lake build'`. Kill by PID.
> ⚠ `numpy` is not installed system-wide and `venv` creation fails here; use
> `python3 -m pip install --break-system-packages numpy` (already done, numpy 2.4.6).
> ⛔ **There is no `probe_cao_washout.py` and there should not be.** The one live question (§6e.4c) is
> **vacuous at every reachable `L`**, because `μ` is complete there — a probe would return "holds" and
> mean nothing, exactly as Phase 0 did.
> ⚠ **2026-08-15d amends this, and the amendment is the interesting part.** The steer is right about
> the *fixpoint*: a probe asking *"does `Φ` determine the orbit?"* at the fixpoint returns TRUE for a
> reason that has nothing to do with large `L`. It is wrong as a blanket ban, because the vacuity has
> a **removable cause** — the tag being complete. Cap the rounds and the tag is genuinely incomplete
> while every structural feature of the question survives. See `probe_cao_phi_isolate.py` below.
> ★ **The generalizable move: when a question is vacuous because some input is too strong, weaken that
> input rather than climbing `L`.**

> ### ▶ 2026-08-15**d** PROBES ADDED — §6e.4d, the Ruler Lemma
> * `probe_cao_ruler.py` — ★ **the constructive check of the theorem's PROOF, not its conclusion.**
>   Counts rulers ((i) tag isolates + (ii) profile injective), then actually **decodes** the ruler's
>   tag block of `Φ` and compares the recovered multiset with the true `S_L`-orbit. `L=4`: 96 rulers,
>   **20/20** reps decoded; `L=5`: 1920 rulers, **90/90**. Imports `probe_cao_lemma_check_np`; arg `<L>`.
>   ⚠ Also reports *profile injective ⟺ `Aut(G_c)_i = 1`* — **true at `L=4,5`, and do NOT adopt it**:
>   its `⟸` half is *"individualization + refinement always discretizes"*, which is what CFI refutes.
> * `probe_cao_ruler_exists.py` — ★★ **the hypotheses at `L = 6,7,8,9`, i.e. past the ensemble for
>   ever**, because (P1)/(P2) are **single-copy** properties: no `2^{C(L,2)}` object, no global
>   interning. Every 1-WL-discrete copy tested is payload-discrete and has all `L` profiles injective;
>   1-WL-discrete copies are abundant (5760/32768 at `L=6`). Args `<Lmax> <samples>`; ~22 s.
>   ⚠ **Trap paid for:** *"the `M(H)` colouring is discrete"* is the WRONG test — frame–frame pairs are
>   **frozen** by design (§6d.5), so the frame diagonal holds 2 colours for ever and global
>   discreteness is unreachable by construction. Test **within-payload** discreteness, which is all
>   (P1)/(P2) use.
> * `probe_cao_phi_isolate.py` — ★★★ **the non-vacuous surrogate.** Runs `M`'s 2-WL for exactly `r`
>   rounds (lockstep, globally interned) so the tag is genuinely INCOMPLETE, then reports
>   #orbits / #tag-classes / #`Φ`-classes / #rulers per `r`. `L=4,5`: at `r=1` the tag has 4 resp. 5
>   classes and `Φ` already has **all 20 / all 90**; `L=6` at `r=1`: tag **6** classes, `Φ` **all 544**
>   ⟹ **washout is false by measurement.** Args
>   `<L> <rmax> <chunk>`. ⚠ `L=6` needs `rmax=1` — going to the fixpoint OOMs at 7 GB in round 2's
>   interning, and the fixpoint row (544 = 544) is already in `lemma_L6.log`. ⚠ `Φ` rows are folded to
>   `uint64` by a random linear hash before sorting
>   (structured-array lexsort is ~50× slower and `L=6` needs 550 passes); a collision could only
>   **merge** `Φ`-classes, i.e. only ever argue *against* the hypothesis under test — check the
>   direction before reusing this trick anywhere it could argue *for* one.
> ### ▶ 2026-08-16 PROBES — the session that withdrew §6e.4d's verdict (§6e.4e–g)
> ⚠ Five of these are **reader-designed**, and each was built to attack the ruler argument. They are
> the falsification harness; keep them together.
> * `probe_cao_lowerbound.py` — ★★ **(LB) measured**, the one load-bearing structural claim: real
>   ensemble `L=4`, all **64/64** copies, the within-copy vertex *and* pair colourings refine the
>   copy's own bare 1-WL/2-WL. ~30 s. ▶ §6e.4g item 2 is to formalize exactly this.
> * `probe_cao_c6_ensemble.py` — the reader's `C6` construction (102 vertices, 15 gauges, rotated
>   ruler + payload copies), with **exact** automorphisms via VF2 and the CAO start (orbit partition).
>   Args = payload names. ⚠ `networkx` is needed and was installed for this (`--break-system-packages`).
> * `probe_cao_c6_ablate.py` — ★★ the ruler ablation: shared frame ± ruler vs private frames ± ruler.
>   **6 / 3 / 3 / 3 payload cells** — the only measurement on record where the cross-copy channel
>   supplies something no within-copy refinement can. ⚠ Its within-copy failure is an **automorphism**,
>   not WL-blindness (§6e.4e) — do not quote it as evidence about CFI.
> * `probe_cao_fullclosure.py` — ★ full `S_L` closure (every relabelling of every base graph).
>   `P5`+chair+`C5` → **8 cells = 8 orbits**. ⚠ Uses an O(n²)-memory hashed WL round; the naive round
>   materializes an `n² × (n+1)` array (1.9 GB at n = 620).
> * `probe_cao_ruler_bolt_on.py` — ★★★ **the cleanest limit on (A)**: rook(4,4) ⊔ Shrikhande, a real
>   32-vertex 2-WL mixed cell, and **no uniform ruler attachment resolves it**. A ruler is not a
>   bolt-on device. Run this before claiming the argument generalizes to anything.
> * `probe_cao_ruler_falsify.py` — ★★ the falsification harness for *ruler ⟹ no mixed cell*, exhaustive
>   over `S_4`-closed families with capped rounds. 1491 objects, 1487 with mixed cells, **0
>   falsifiers**, thin margin. ▶ §6e.4g item 4 is to extend it (`L=5`, more rounds, other carriers).
>   ⚠⚠ **Two performance traps paid for here:** a `C × C` random-hash table is `O(C²)` and `C` grows
>   every round (~5000 by the fixpoint at n = 268) — use two `O(C)` tables and multiply; and
>   ⛔ **`pkill -f <probe name>` kills the launching shell too** (the doc's standing trap) — it ate a
>   `sed` and two runs this session. Kill by PID.
> * `probe_cao_kind_census.py` — ★ cells vs orbits for **every vertex kind** of the real ensemble, not
>   just payload, which is all the record ever counted. `L=4`, `N=332`: payload 20=20, frame 2=2,
>   **central 11=11**, 0 mixed cells anywhere. Imports `probe_cao_ensemble_frame`; ~31 s.
>   ★ The central layer was worth checking on its own: `m(g)` touches only the frame, so the clique
>   mechanism does not run inside a copy and central–central pairs see only `#{k : g_k = h_k}`, whose
>   distribution over all `h` is `g`-independent. It is nonetheless complete — via the same ruler.

### 8a. ▶▶ THE LEAN LAYER — all **fourteen** modules, and exactly what each one owes

**All are gate-listed in `scripts/build.sh`; the gate is 135 modules, ~280–360 s, and passes.**
⚠ **Count modules with `grep -c '✔ ChainDescent'`, not `grep -c '✔'`** — the latter also matches the
*"serial build complete"* line, which is why earlier numbers in this doc's history ran one high. Every
declaration is `[propext, Classical.choice, Quot.sound]` or a subset — no `sorry`, no custom axiom, no
`native_decide`.

| module | what it owns | ⛔ what it still owes |
|---|---|---|
| `CaoTarget` (FT2) | `round2`, **`wl2`** (the 2-WL closure as a function), `refines_wl2_of_stable` (§6d.1's method), `inv2_wl2`, `Propagates`/`Separates` | — |
| `CaoFast` | `wl2Fast`, the **runnable** closure | — |
| `CaoEnsemble` | the **index** layer: `gact_transitive` = T1, `gact_eq_self_iff` + `lact_base` = T2⁻ | no graph — superseded for that by `Ensemble` below |
| `CaoCollapse` | §6d.1 at `rootPair`/`ext`, ★ **`merge_of_stable_merge`** (the usable direction), the round-indexed form, the frame layer with invariance + **`≤ 12` proved** | ⛔ **`FrameClassComplete`** — pinned `Prop`. Route: Mathlib `Equiv.extendSubtype` + three cases on `|k ∩ k'| ∈ {0,1,2}`, needs `4 ≤ L` |
| `FrameEncoding` | the **generic-carrier** 2-WL round (`roundG`/`isRound_roundG`/`wl2G`/`refines_wl2G_of_stable`), `MVert`/`mAdj`/`mInit`, the injective `code`, `Adequate`, `pairSigG_split`, ★ **`merge_of_adequate`** | ⚠ non-vacuity witness is **degenerate** (discrete `b` merges nothing) |
| `TupleWL` | `k`-WL at **every** arity (`roundT`/`isRound_roundT`/`wlT`), ★★★ **the block lemma** (`subst2_of_stable`/`substJoin_of_sigDet`), the **substitution-closed** round `roundTS` + `cov_of_stableS`, and the two assembly shapes `substPair1/2_of_stableS` | ⚠ §4–§5 are `noncomputable` (via `Finset.toList`) — proof-side only |
| `FrameTransfer` | `mk6`, the four reindexings, `bOf`, `payload_sum`/`frame_sum`, ★★★ **`blocks_bOf`** ⟹ **`adequate_bOf`** ⟹ **`merge_of_tuple_merge`** — §6f's bound, **proved at `k = 2`** | ⚠ `refinesAtoms` is a side **hypothesis** (mechanical: close an `E`-dependent start colouring under `roundTS`) |
| `Ensemble` | ★ **the ensemble AS A GRAPH**: `eAdj`/`eInit`/**`eRoot`**, a **generic `InvG`** layer for `roundG`/`wl2G`, the label action `eact` (+`eact_base` = T4 at the graph), `invG_eRoot`, ★ **`orbit_not_split`** (the free half), ⛔ **`MixedCell`** + `not_labelPropagates_of_mixed` | ⛔ `MixedCell` **stated, not proved** · ⚠ against **label** orbits (T2⁺ unproved) · ⚠ ordered slots ⟹ twin frame vertices, so **never** claim `Aut = ` the label group from it |

| `DisjointUnion` | ★ 2-WL on `A ⊔ B`: side-blind `dInit`, the `sigL`/`sigR` split, **`Blocked`** (cross pairs carry only the two endpoint diagonal colours; ★ `diagEq` is where *"the two sides are WL-equivalent"* enters, used in exactly one case), `stable_of_blocked`, ★★★ **`merge_of_blocked`**, and a non-vacuity witness that **merges** (`wl2G_double_merge`) | — ⚠ supplies no `Blocked` witness for a CFI pair; that is (iii) |
| `TupleCov` | ★★★ **`stableS_iff`** (`roundTS`-stability **=** `roundT`-stability **+** `Cov`, nothing else) · **`subst_of_stable`** (the extraction lemma, from stability alone) · `covPerm_wlT` (permutations, by induction **on the rounds**) · `cov_idem_of_stable` · `exists_perm_comp_idem` (σ = π∘ρ) ⟹ ★★★ **`stableS_wlT`** | ⚠ two side conditions are **instantiation, not mathematics**: `CovPerm` of the start colouring and `SeesEqAll` of the closure — both free for the atomic type, neither written for the start `FrameTransfer` uses |
| ★ `RulerLemma` (item 1) | **carrier-generic**, no graphs: `Align`, `Phi`, `Equivariant`, `Invariant`, `map_univ_smul`, ★ **`eq_of_align_eq`** (the decode), `align_smul`, ★★★ **`ruler`**, `phi_smul`, `phi_eq_iff_orbit`; `Witness` = a non-vacuity instance where `Φ` is **strictly finer** than the tag | ⚠ `ruler`'s (ii) is *"`b ω₀` injective"* — **too strong for the ordered-slot ensemble**; the identified fix is *"`b ω₀` refines the other reading"* |
| ★★★ `CopyRestrict` (item 2) | ★★★ **`restrict_sig_eq`** (stability restricts to a colour-definable sub-carrier — carrier-generic), `sig_restrict`/`sig_singleton`, `exists_copy_pred`, `centre_readout`, `frame_type_eq`, ★ **`encoded_edge_eq` = §6b at the object**, `eCopy_stable`, ★★★ **`lb` = (LB)**, `eCopy_injective_of_discrete` | ⚠ `SymCopy` is carried wherever the encoded edge is pinned — an ordered-slot artifact |
| ★★ `CopyProbe` (item 3) | `sig_singleton_snd`, `frame_type_eq'`, `frame_partner`, ★★★ **`transfer`** (a discrete copy is a coordinate system), ★ **`profile_injective` = (P2)**, ★★ **`tag_isolates` = (P1)**, ★ **`sameLabelOrbit_of_tag`** (no mixed cell touches a discrete proper copy) | ⛔ owes the **coherence chain** (§6e.4g item 4a) and the **instantiation** (4b); `hd` (the copy's restriction is injective) is a hypothesis, discharged by `lb` + the copy's own discreteness |
| `AtomAugment` | ★★★ **`adequateFor_augment_iff`** — augmenting the atoms costs **exactly** `Refines (pull b) extra` (an `iff`; it works because `Adequate.blocks` is **start-colouring-free**) · `merge_of_tuple_merge_aug` (the augmented consumer, with the cost visible as `hex`) · ★ **`adequateFor_augment_self`** = the ceiling | — |

⛔ **NOT in the Lean layer, and each is a real gap:** ★★ **(A)'s coherence chain and instantiation**
(§6e.4g items 4a/4b — the two things standing between `RulerLemma`+`CopyRestrict`+`CopyProbe` and (A);
4a is bookkeeping, 4b needs `Ensemble.lean` moved to unordered proper slots) · the **collapse**
(§6e.4 — ⚠⚠ and as of 2026-08-15 it has **no proof route at all**, §6e.4c; do not start Lean work on
it before the washout question is settled on paper) · **CFI's WL-blindness** (literature; ✅ now quotable in its *standard*
`k`-WL form thanks to `TupleCov`) · **T2⁺** (`Aut_{m(base)}` is *exactly* the label group; needs
`Aut(T(n)) = Sym n`) · **T3** (the frame's cells are the position classes) · the **triangle frame**
`TF(E)` (§6g, queued — ★ **and it is the natural object if the reader's washout reading is right**,
since it is poly-size where the ensemble is exponential).

▶ **The mechanical Lean items still owed, cheapest first:** ★ §6e.4g **4a** (the coherence chain) ·
`FrameTransfer.refinesAtoms` · `TupleCov`'s two side conditions · `CaoCollapse.FrameClassComplete` ·
§6e.4g **4b** (unordered-slot `Ensemble`, then the instantiation) · **T2⁺** · `TF(E)`.
⚠ `PublicTheoremIndex.md` has **no rows for any of the fourteen** — regen is
`scripts/GenerateTheoremIndexes.py rewrite --with-line-numbers`, ⚠⚠ it recomputes the **Notes**
column and can resurrect **phantom rows**, so verify *unmatched deletions = 0*. Deliberately not run.

⚠⚠ **LEAN TRAPS PAID FOR IN THIS FAMILY — do not re-pay them.**
`Refines` is **ambiguous** (`Refine` exports a `Colouring`-typed one) ⟹ write `PartitionClosure.Refines` ·
`omit [..] in` goes **BEFORE** the docstring, never between docstring and theorem ·
`obtain ⟨..⟩ := ⟨h.1, ..⟩` with no expected type fails — let `simp [Nat.pair_eq_pair]` build the nested
conjunction and destructure that (⚠ it nests: `h.1.1`, not `h.1`) ·
`Multiset.product` and `Multiset.bind` will **not** `rw` — get the product decomposition by **`rfl`** and
unfold `bind` with **`unfold`**; `Multiset.map_join`, `Multiset.bind_assoc` and `Multiset.map_bind` all
exist and are the right bridges ·
build a group action from **`Equiv` combinators** (`arrowCongr`/`prodCongr`/`sumCongr`), never as a raw
function — the direct definition's inverse laws do not close by `rfl` ·
use `Prod.map_fst`/`Prod.map_snd`, not `Prod.map_apply` ·
**`ne_eq`** must be in the simp set before `Equiv.apply_eq_iff_eq` fires inside `decide` ·
write adjacency as `decide (… ∧ …)`, not `==`/`!=`, or the `Bool` goals will not simp ·
`k.2 ▸ …` gives "failed to compute motive" — use `have h … ; rwa [k.2] at h`.

⛔ **Traps hit while producing this — do not repeat.** (a) and (b) are already in the CAO doc §9.
(a) `pkill -f probe_...` **matches your own launcher** ⟹ self-kill, exit 144; kill by PID.
(b) A 1-WL stop condition of the form `len({(old,new)}) == len(set(new))` is **always true** (the new
colouring always refines the old), so the loop returns after one round; compare
`len(set(new)) == len(set(old))` instead. This produced a wrong `[3,45]` corner split before it was
caught.
(d) ⚠⚠ **2026-08-15 Lean traps.** `wl_stable`, **not** `stable_wl` · `have e : _ ≃ _ := {..}` in
tactic mode **forgets the body** ⟹ use `let`, or the later `rfl` will not close · `rw [sect_spec]`
fails with a metavariable pattern ⟹ use `congrArg` · state helper lemmas with **explicit** vertex
arguments: an implicit `{p}` cannot unify against `p.1`/`p.2` · `cases h : side v` **substitutes into
the goal**, so close those branches with `rfl`, not `exact h` · `(univ : Finset (α ⊕ β)).val =
univ.val.map inl + univ.val.map inr` holds **by `rfl`** · `rw`'s trailing `rfl` will not reduce
`fold (Sum.inr a)` — add `simp only [fold_inl, fold_inr]`.
(e) ⚠⚠ **THE MODEL-FAITHFULNESS TRAP, and it cost a whole 812-vertex run.** In the `full` encoding the
payload copy must be a **clique** with adjacency carried *only* by the frame types. Keeping the
payload's own edges as well hands 2-WL the adjacency **twice** — atomically at round 0 *and* through
the frame. It is a *stronger* model than the object, so **survivals under it are still sound but
separations are not**. Check which side of that asymmetry your result is on before quoting it.
(d) ⚠ Two modelling errors of the same family, both caught only by cross-checks: the `Aut_v`
comparison group must include the **gadget-internal clique permutations** (§2.3) or middles report as
spurious mixed cells; and a relabelling of the two-cube frame must **swap the cubes**, not the ends
(§3.2a), or the original design reads as broken.

(e) ⚠⚠ **1-WL colours are only comparable ACROSS COMPONENTS if every component is refined for the
SAME number of rounds.** Refining a disjoint union component-by-component with a shared intern table
is legitimate — but stopping each component at *its own* fixpoint returns colours from different
rounds, which are different namespaces. That bug made §6a's control read **520** instead of **538**
on its first run, and it is silent: the numbers look plausible and the partition looks well-formed.
Run a fixed `≥ n` rounds instead.
(f) ⚠⚠ **Validating an abstraction on one witness pair is not validating it** — §7's filter 7, and it
is what let §6's wrong inference stand for a day.

⚠ **Run the big 2-WL jobs one at a time.** Concurrent 812- and 128-vertex runs thrashed memory badly
enough to stall a *32*-vertex job past 120 s — which looked like a hang in the small job, not the big
one. 2-WL here is `n³` time with `n²` signatures; the counting signature in `probe_cao_cfi_frame.py`
is what makes `n = 812` fit at all.

---

## 9. Provenance

**Measured — on the REAL object.** §2.3, §2.4, §3.2a, §6's three numbers, **§6a** (elementwise, at
`n = 229406`), **§6b** (`L = 4`, `n = 332`), **§3.2c** and **§3.2d** (`L = 4`, at 2-WL, every copy
present). ⚠ §3.2c/§3.2d are measured at `L = 4` only; the *mechanisms* they isolate (a central is
never a common neighbour of two payload vertices; the copy set does not saturate) are stated for
general `L` but proved only for the first.

**Measured — in the `M`-model, which §6d measures to reproduce the ensemble (at `L = 4`).** §4.2's
**`disjoint`** rows, §4.3's `K4` counts, §5.1 (all rows), §5.2's table. Every separation has a
same-object control that came out unseparated. ⚠ Each inherits §6d.2(b), and each is a *separation*,
so by §6d.1 none is evidence about the scheme — only about that payload.

**Measured in a model now known NOT to be the construction.** §4.2's **`shared`** rows, and §3.2c/§3.2d
(which use a shared frame by construction — that is what they were measuring).

**Proved, not measured.** §1's dichotomy · §2.3's and §6's `Aut_v` **upper** bounds (without these the
mixed-cell counts are unfalsifiable) · §2.1's parity requirement · §3.2's `δ` condition · §3.3's
reduction · **§6b's typed-common-neighbour argument**, which is the only 2-WL claim here that is both
proved and about the real object.

**Cross-checked.** §6's 544 orbits, by Burnside, together with the known 156 iso classes — and
independently re-derived in `probe_cao_ensemble_audit.py`. §6's 292/100 re-derived from a closed
formula and then compared **elementwise**.

**Machine-checked.** T1 and T2⁻ in `ChainDescent/CaoEnsemble.lean`; §6d.1's method, its
merge-direction corollary, the round-indexed form, and the frame layer's invariance + `≤ 12` bound in
`ChainDescent/CaoCollapse.lean`; **§6f's transfer skeleton** — the generic-carrier 2-WL round, the
encoding, the injective coding, and `merge_of_adequate` — in `ChainDescent/FrameEncoding.lean`
(all 2026-08-13). All axiom-clean, no `sorry`, no custom axiom.
✅ **2026-08-14/15 additions, all axiom-clean:** `DisjointUnion` (2-WL on `A ⊔ B`, §6f.4e) ·
`TupleCov` (the standard-`k`-WL bridge, §6f.5a α) · `AtomAugment` (the augmentation price, §6f.5a β).
✅ **All eleven CAO modules are gate-listed and the gate passes (132 modules, ~239–264 s)** — the earlier
*"not gate-listed"* caveat is discharged. **§8a is the authoritative per-module table**: what each owns
and what it owes. ⛔ Pinned, **not** theorems: `CaoCollapse.FrameClassComplete`,
`Ensemble.MixedCell`; and `FrameTransfer.adequate_bOf`'s `refinesAtoms` is a side hypothesis.

**Measured — round by round rather than at the fixpoint.** §6e.5's R1 box (`L = 4`, `n = 332`,
`probe_cao_roundmatch.py`): no round offset aligns `E` and `M`; the one-sided `M^{(r)} ⊑ E^{(r)}`
holds at every round, and the two chains are never `INCOMPARABLE`.

**Argued, not established — ▶ and §6f is the one that matters.** §6f's interpretation bound
(`M`-2-WL ≼ bare-8-WL, uniform in `L`): the interpretation is written out, the counting-translation
lemma it invokes is cited from memory and **not** verified against it (§6f.5). It is consistent with
every measurement on record and makes a falsifiable prediction. ⛔ Do not quote the numeral `8` as
established. Also: §5's admission test — ⚠ **necessary direction only**, and ⚠⚠ its
ensemble assumption is now **refuted at rung 1** (§6a), not merely unmeasured at rung 2. §4.3's
4-vertex-window mechanism is **counter-indicated** by two facts already in the doc (§6a.2).

**Measured 2026-08-15 — and these three are what the current state rests on.**
* **`M`-2-WL is a COMPLETE invariant of (graph, marked vertex) at every reachable `L`** — `μ`-classes
  vs Burnside iso-class counts: `L=4` 20 = 20, `L=5` 90 = 90, `L=6` 544 = 544. ⟹ §6e.0's Phase 0 is
  **vacuous**, and unfixably so.
* **`a(c,i)` determines `c`** (0 collisions at `L=5`), and the profiles have exactly as many
  `S_L`-orbits as there are marked-graph iso classes ⟹ **the orbit of `a` IS the iso class** ⟹
  **ORB ⟺ `M`-complete ⟹ ORB is false at large `L`**. Mechanism: the payload clique gives
  `(p(i), f(k,t))` common neighbours `{j ∈ k}` exactly when `c_k = t`, in one round, at every slot.
  ⚠ Dropping the clique changes **nothing** (identical figures) — the information reroutes.
* **On the REAL ensemble (`L=4`, `N=332`): `aE(c,i)` determines `c`, 96/256 injective, 20 `S_L`-orbits
  = 20 payload cells = `M`'s 20 `μ`-classes.** ⟹ the ensemble's frame channel is **identical** to
  `M`'s (killing *"guess from the ensemble's coarser channel"*), and simultaneously the cross-copy
  channel added **nothing** at `L=4` (which is (i) holding with equality).

**⛔⛔ RETRACTED 2026-08-15c, same day as claimed — do not re-inherit either.**
*"§6d.8's LEMMA IS FALSE"* and *"(i) is false / Construction C is refuted at 2-WL"*. Both ran through
an **isolation** step (identify, inside `Φ`, the entries coming from a rigid injective profile's orbit)
whose only handle is colour — which presupposes the colouring already separates those copies, i.e.
part of the conclusion. ⚠ `ORB ⟹ LEMMA` is **solid** (§6e.1+§6e.2); only the **converse** is gapped.
⚠ The retraction does **not** touch the three measurements above.

**⚠⚠ 2026-08-16 — THE PARAGRAPH BELOW OVERSTATES ITS CASE AND IS DOWNGRADED.** *"Re-established with
a sound proof"* should read *"argued, with the isolation step repaired"*: (LB)/(P1)/(P2) are proved on
paper and measured at `L = 4` only, and the competing position (B) is **not refuted** (§6e.4e). The
measurements listed are accurate and stand; the verdict language does not. ⛔ Do not quote *"and
Construction C is refuted with them"*.

**~~✅~~ 2026-08-15d — THE RETRACTION IS *RESOLVED*, NOT REVERSED (§6e.4d).** The isolation step is
repaired by **choosing** the probe: a generic (1-WL-discrete) copy is isolated by a **lower** bound on
the colouring, and the CFI-like copies the conclusion concerns are never used as probes. ⟹ *"`Φ`
determines the orbit"* and *"§6d.8's LEMMA is false at large `L`"* are **re-established with a sound
proof**, and *"Construction C is refuted at 2-WL"* with them — this time without routing through the
collapse (i) at all. Newly measured, and none of it vacuous:
* **The decode runs**: `probe_cao_ruler.py` `L=4` 20/20, `L=5` 90/90; on the **real ensemble**
  (`probe_cao_kind_census.py`, `L=4`) 96 rulers, block size 24 = `|S₄|`, 20/20 reps recovered.
* **(P1)+(P2) at `L = 6,7,8,9`** (`probe_cao_ruler_exists.py`) — single-copy properties, so past the
  ensemble for ever. 1-WL-discrete copies are abundant (**5760/32768** at `L=6`) and every one tested
  is payload-discrete with all `L` profiles injective.
* **Cells vs orbits for EVERY vertex kind** (`probe_cao_kind_census.py`, `L=4`, `N=332`): payload
  20=20, frame 2=2, **central 11=11** — the central layer had never been counted, and a CAO
  counterexample needs only one mixed cell **anywhere**.
* **Washout refuted by measurement** in a bounded-round surrogate (`probe_cao_phi_isolate.py`) where
  the tag is genuinely incomplete: at `r=1`, tag **4 / 5 / 6** classes and `Φ` **all 20 / 90 / 544**
  for `L = 4 / 5 / 6`. ★ `L=6` is the sharp row — first `L` with real 1-WL twins — and it separates
  all 544 with **no ruler present**, so the `Align` channel is stronger than the Ruler Lemma needs.

**Superseded, listed so the retractions are not silently re-inherited.**
*"The encoding hands WL exactly one extra level"* (→ not constant, §5) · *"a carrier's attachment set
must determine `v`"* (→ false, §1) · *"`CFI[K4]` suffices as a payload"* (→ refuted, §5.1) ·
*"the two-cube original fails the transposition test"* (→ my modelling error, §3.2a) · the `iff` form
of the admission test (→ necessary only, §5) · *"rung 2 is purely a budget question"* (→ §6) ·
⛔⛔ **2026-08-13:** *"the ensemble is passive / contributes nothing beyond the two-copy model"*
(→ §6a — it is far **coarser**, and the witness was degree-blind) · *"the Shrikhande/rook and
`CFI[K4]` payloads are DEAD"* (→ §4, §5.1 — dead **in the model**; not established for Construction C)
· *"rung 2 is a payload question, not a scaffolding question"* (→ §6a — the scaffolding is exactly
what is unresolved).

> ### ▶▶ OUTSTANDING — the handoff list, rewritten clean 2026-08-14
> *(supersedes the 08-13 list: §6f's Lean chain is now DONE, so items 4a/4c changed and §8a carries the
> per-module state. Read §8a before touching Lean.)*
>
> ### ✅ 2026-08-14 — CLOSED: the cross-graph joint (§6f.4e, `DisjointUnion.lean`, gate 130 modules).
> ### ✅ 2026-08-14 — CLOSED: §6f.5a's (α) — `TupleCov.stableS_wlT`, the standard `k`-WL closure is already `roundTS`-stable ⟹ (iii) is quotable in its literature form. ✅ ALSO PRICED: (β) — `AtomAugment.adequateFor_augment_iff`, an `iff`; R3-as-written looks unpayable, the reframe survives. (γ) the constant is `2k+2` ⟹ `K₈` not `K₁₀` (resolved).
>
> ### ⚖️ 2026-08-16 — THE FOUR-GAP LIST BELOW IS **STILL LIVE**, and gap (i) is now the (A)/(B) disjunction
> ⛔ A 2026-08-15d revision of this box said the list was *"about a dead construction"* because §6e.4d
> closed Construction C. **That is withdrawn.** Gap **(i)** — the collapse — is exactly the undecided
> disjunction in the top box: (B) is (i) holding, (A) is (i) failing at large `L`. It is neither
> resolved nor bypassed.
> ▶ **The four items that would settle it are §6e.4g**, and item 1 (formalize the Ruler Lemma) is the
> cheapest thing in this file. **(iii)**, **T2⁺**, **"any `k`"** and the carrier-generic Lean assets
> remain as listed — they are about the `(i)∘(ii)∘(iii)` *template*, which outlives any one carrier.
>
> ### ⛔⛔ THE FOUR GAPS BETWEEN HERE AND A COUNTEREXAMPLE — memorize these before quoting anything
> **(i) the collapse (§6e.4) — the ONLY mathematics, and as of 2026-08-15 it has NO PLAN: R1 and R3
> are both dead and the whole thing reduces to one analytic question (§6e.4c)** · **(iii) CFI's
> WL-blindness — literature; ✅ now quotable in its *standard* `k`-WL form (`TupleCov`), but still not
> formalized** · **T2⁺** — so `Ensemble`'s target is stated against *label* orbits · **"any `k`"** —
> `FrameEncoding` is 2-WL-specific and the collapse is level-uniform only at `k = 1, 2` (measured);
> arbitrary `k` needs the encoding side re-run at arity **`2k + 2`** (§6f.5a γ — *not* `3k+2`).
> ⟹ ⛔ **nothing in this doc refutes CAO propagation.** What is proved is the **transfer** at `k = 2`,
> plus the three carrier-generic supports (`DisjointUnion`, `TupleCov`, `AtomAugment`).
>
> **A. The one open obligation — ⛔⛔ AND AS OF 2026-08-15 IT HAS NO PLAN. Read §6e.4a first: the
> lemma below is FALSE, Phase 0 is VACUOUS, and R1/R3 are both dead. Item 2 is WITHDRAWN.**
> 1. ⛔ ~~**Close §6e.4**~~ — now in its **one-sided** form: `M^{(r)} ⊑ E^{(r)}`, *not* the equality of
>    §6d.8 (§6e.5's R1 box: no round offset exists, and only `⊑` is load-bearing). §6e is the plan:
>    Step 1 (pushforward) and Step 3 (round-1 base case) are **done**; §6d.2(a) is **proved for all
>    `L`**; Phase 0 validates at `L = 4` and `L = 5`. The gap: at the fixpoint `b(c',l)` is not a
>    product measure, so full slot-exchangeability fails. ▶ **R1 and R3 are now co-equal first
>    targets** — R3 (a *finer* stable `s` between `M` and `WL_E`, e.g. `M⁺ = M + Φ`) still carries
>    merges, so over-approximating the cross-copy channel is legitimate from the start, not a
>    concession after R1 fails. ⚠ **R4** (`C³`) is aimed at the propagation statement itself; note it
>    is now **adjacent to §6f**, which uses the same interpretation machinery on `M` — if §6f's lemma
>    is written out properly, R4 inherits the tooling.
> 1a. ▶ **Pin §6f's interpretation lemma** (§6f.5 caveat 1) — cheap, purely bibliographic/write-out,
>    and it is what licenses skipping the entire payload search. Do this **before** quoting the `8`.
> 2. ⛔ ~~**`probe_cao_lemma_check.py` at `L = 6`**~~ **DONE AND WITHDRAWN 2026-08-15.** Ported to numpy
>    (`probe_cao_lemma_check_np.py`, `L=5` in 4 s where the original was hours; `L=4`/`L=5` reproduce
>    20/0 and 90/0 exactly). `L=6` builds in 353 s and gives **544 `μ`-classes = 544 iso classes** —
>    i.e. **vacuous**, like every other reachable `L` (§6e.4a). ⛔ Do not re-run it for information.
>    ⚠ Budget it: `2^15` copies × a 36-vertex `M` is **hours in pure Python** — a previous background
>    attempt was killed unfinished. Vectorize (numpy, batched over copies) or do not start it.
>
> **B. ⛔ THE PAYLOAD SEARCH IS OFF THE CRITICAL PATH — §6f.**
> 3. ⛔ **Do NOT** build a C 2-WL, run `CFI[K5]`-full, or hunt for a small 3-WL-blind pair *as if the
>    refutation depended on it*. §6f bounds `M`-2-WL by bare-8-WL uniformly in `L`, so CFI over a
>    treewidth-9 base is **guaranteed** to merge without ever being computed. These runs now only pin
>    the constant (is it 3, 4 or 8?) and test §6f.5's falsifiable prediction — worth doing eventually,
>    worth **nothing** on the critical path. ⚠ Direction discipline (§6d.1) still governs: only a
>    **merge** refutes.
>
> **C. Lean — ▶ read §8a first; it is the per-module state and the trap list.**
> 4. ▶ **T2⁺** (`Aut_{m(base)}` is *exactly* the label group; `Aut(T(n)) = Sym n` is the content) —
>    ★ **now the highest-value Lean item.** `Ensemble.lean` exists, so this is what upgrades
>    `MixedCell`/`orbit_not_split` from **label** orbits to real `Aut`-orbits and makes every
>    mixed-cell count in this doc unconditional. ⚠ Mind the ordered-slot twins (§8a). Then **T3**.
> 4a′. ▶ **Discharge `FrameTransfer`'s `refinesAtoms`** — mechanical: close an `E`-dependent start
>    colouring under `roundTS` and show the pullback refines `mInit E`. Removes the last side
>    hypothesis from the §6f chain.
> 4b′. ▶ **Prove `CaoCollapse.FrameClassComplete`** — completeness half of §6d.2(a). Route: Mathlib
>    `Equiv.extendSubtype` + three cases on `|k ∩ k'| ∈ {0,1,2}`, needs `4 ≤ L`.
> 4c. ▶ **Build the triangle frame `TF(E)`** (reader's suggestion, §6g): the bare frame with a **pendant**
>    on each edge-slot in place of a colour, so it is a plain uncoloured graph. ⚠⚠ **Frame it honestly:**
>    its WL dimension is **inherited** from the payload — bounded above by §6f's argument and below by
>    §6b's, both within a constant — so it **transports** hardness rather than creating it, and it needs
>    a high-WL payload family as input (the same unformalized literature input). ★ Its value is as the
>    **poly-size** object that grounds §6g, not as a new hardness source. ⚠ With ordered slots the slot
>    vertices are twins; use `Sym2`-style unordered slots if an `Aut ≅ Aut(H)` claim is wanted.
> 4d. ▶ **§6g's (A) in Lean — *"the frame is inert"***, the 1-WL analogue of §6d.2(a). Statement:
>    a pointwise individualization induces a label partition, its stabilizer is a **Young subgroup**,
>    and a Young subgroup's orbits (blocks on payload, *unordered pairs of blocks* on slots) are
>    exactly the 1-WL cells. ⚠ **Lower priority than 4a** — it bounds the *easy* half; §6g.2 shows the
>    payload half is unreachable this way. Logged so the measured result does not rot.
> 5. ★★ **§6b in Lean** — the one 2-WL statement that is both proved and about the real object, and a
>    **single-round** claim rather than a fixpoint. It forces the refiner into the Lean layer that T3
>    needs anyway, so it is a better next target than T2⁺.
> 6. **T2⁺** (`Aut_m` is *exactly* the label group; `Aut(T(n)) = Sym n` is the content) — makes every
>    mixed-cell count here unconditional. Then **T3** (frame cells = position classes).
> 7. ⚠ **`PublicTheoremIndex.md` is stale for the whole CAO family** — `CaoTarget`, `CaoFast`,
>    `CaoEnsemble`, `CaoCollapse`, `FrameEncoding`, `TupleWL`, `FrameTransfer` and `Ensemble` have
>    **no rows** — the whole family. This predates the 08-13/08-14 work (`CaoTarget`/`CaoFast` landed 08-11). Regen is `scripts/GenerateTheoremIndexes.py rewrite
>    --with-line-numbers` per `scripts/theorem-index-maintenance.md`; ⚠⚠ it recomputes the **Notes**
>    column and can resurrect **phantom rows**, so verify *unmatched deletions = 0*. Deliberately
>    **not** run unverified at handoff.
> 4a. ▶▶ **INCREMENT 2 — discharge `FrameEncoding.Adequate.blocks`.** ★ Still the single most
>    valuable Lean target: it converts §6f from *argued* to *proved*.
>    ✅ **(a) the `k`-WL tuple layer and (b) the BLOCK LEMMA are DONE** — `ChainDescent/TupleWL.lean`
>    (§6f.4b), gate-listed and axiom-clean.
>    ✅ **(c) covariance and (d) the assembly are DONE TOO** — §6f.4c/§6f.4d. `Adequate.blocks` is a
>    **theorem**; §6f is proved at `k = 2`. ▶ What is left on THIS item is only `refinesAtoms`
>    (mechanical: close an `E`-dependent start colouring under `roundTS`).
> 4c. ▶▶ **CONSTRUCT `E(L)` AS A GRAPH IN LEAN** — now the cheapest step with the largest effect: it is
>    what makes *"the ensemble has a mixed cell"* expressible at all (§6f.4d caveat 3). Then **T2⁺**
>    (caveat 4). ⛔ Neither closes (i) or (iii).
> 8. ✅ ~~Gate-list the CAO modules.~~ **DONE** — all seven are in `scripts/build.sh`; gate = **132 modules, ~239–264 s**, passing.
