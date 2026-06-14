# Chain descent — the GENERAL-CC SEPARABILITY build (the unconditional seal's last piece)

> **This document is the exclusive, durable home for the one remaining piece of the unconditional seal: the
> general coherent-configuration (CC) separability theory.** It is aimed to be self-contained — a fresh reader
> should need nothing else to begin or continue, however still seek it out if something else is needed.
> Everything the build consumes, the math it formalises, the plan, the ruled-out routes, and the running log 
> live here. Cross-references to other docs are for provenance or if more clarification is needed than provided
> in here.

---

## STATUS (read first)

**Goal.** A polynomial-time graph canonizer / the unconditional oracle-capability seal `reachesRigidOrCameron`,
currently conditional `modulo {G3 cited + G2-B open}` (every capstone *also* carries `hImprim`/G2-A — a separate
deferred Lean-infra piece, §7). **Closing G2-B is the open mathematical content; this build is the one known route.**

**G2-B is NOT "GI ∈ P, give up" — read §1A before concluding any piece is hopeless.** Every unbounded-WL family is
carved into a separate seal leg (CFI→hImprim, abelian→leg B, large/hidden-Johnson→Cameron — *why* the last leg is "or
Cameron"); the residue (primitive, small, non-abelian, non-Cameron) is the **tame remainder** — 0 empirical witnesses,
the ℤ₄² bullseye recovers at WL-depth 2. §1A has the carve-out, the closure angle, and the off-track falsifier.

**Quality bar (non-negotiable).** Every theorem axiom-clean `[propext, Classical.choice, Quot.sound]`; full build green
(`bash scripts/build.sh`, serial ~60–120 s); **no `sorry`, no fresh `axiom`** (cited results are theorem-statement
hypotheses, the G3 pattern); **do not commit** (the user commits between messages).

### Landed (all axiom-clean — decls in §9, history in the changelog + §8)
- **The whole consumer chain to the seal is built.** (C) the group base is FREE (`exists_greedy_base_le_log` + the
  "small" antecedent); the gate / sink / `b(X)`-tail; the general-CC substrate (`CoherentConfig`, the point-extension
  *construction* `pointExtension`, general `AlgIso`/`Separable`/`SeparablePointed`); the pointed transport; and **three
  seal checkpoints** — `…viaExtensionSeparability` (cites Thm 4.1), the citation-free `…viaDominatorClosure` (δ′ at
  scheme level), and `…viaExtensionDominatorClosure` (δ′ on the extension, the `n ≥ 25` path).
- **The δ′ forced-triangle engine — on the scheme AND lifted to the extension `X_T`** (`CoherentConfig.lean §CC.10`):
  the criterion, the rank engine, **`Sharp (pointExtension X T)` PROVED**, and the wiring to the seal carrying exactly
  {G3 + hImprim + `hclo`-on-`X_T` + `hcatch`}.
- **Real discharges (non-vacuity, not the family theorem):** the `g = -1` odd-char family (`…viaG0powNeg`, `hclo`
  PROVED not carried) and the concrete ℤ₄² Clebsch closure (`b(X) ≤ 2`, `AssociationScheme`-level).
- **The CC sparse substrate — A1 ported through §S.9 (`CoherentConfig.lean §CC.11`–`§CC.16`, all axiom-clean):** `c(X)`+its
  geometric lemma `indistinguishingNumberOf_eq_card`, `k(X)`, `SparseSeparable` (`§CC.11`); the (19) estimate `sum_pu_le` +
  transpose bridge (`§CC.12`); the (20) identity `pu_eq_sum` (`§CC.13`); the transpose-aware triangle identity
  `valency_mul_interNum` = `n_k·c^k_{i,j}=n_i·c^i_{k,j*}` (`§CC.14`); the §S.4 smax/sα graph layer + `saAdj_symm` (`§CC.15`); the
  §S.5 summation identity `sum_interNum_eq_outDeg` + the §S.9 Lemma-3.5(1) `n_u>n_v` half `valency_le_pu_of_valency_lt` (`§CC.16`);
  the **fiber-size identity** `fiberSize_mul_valency` + within-fiber `smaxAdj_symm_of_sameFiber` + reusable `outDeg_eq_interNum` (`§CC.17`).
  **★ A1 IS ESSENTIALLY DONE (`§CC.18`, the abundance discharge):** `basePinsAll_of_card_gt` (`(k−1)·c < |T| ⟹` every `γ∉T` pinned by
  two base points, via an indistinguishing-number union bound) / `dominatorReachable_of_card_gt` (`⟹ ∀v DominatorReachable T v`) /
  `allSingletonFiber_of_card_gt` (the A1 capstone: `(k(X_T)−1)·c(X_T) < |T| ⟹ X_T complete`). **The scout paid off — §S.10–§S.16 are
  UNNECESSARY:** the δ′ engine accepts *any* bounded base, so PV's sharp `b≤2` is overkill; a crude `b ≤ (k−1)c+1` falls out of ONE
  counting lemma, cross-fiber automatic (no smax). §CC.15–§CC.17 (smax/fiber-size) are landed infra, off the critical path; the
  §S.10–§S.16 sα port is abandoned. A1 now reduces `hclo` to a single `O(1)` threshold `(k(X_T)−1)·c(X_T) < |T|` — the crisp A2 interface.

### The open frontier — ONE quantity: `c(X_T)` (live work: `chain-descent-cxt-scoping.md`)
A bounded-base δ′ pinning rank / forced-triangle closure for the residue family **on the extension `X_T`**
(`hclo : ∀ v, (pointExtension …).DominatorReachable T v`). Everything reduces to it: §1B — the general (A)+(B) *domination*
condition IS this quantity; the `n ≥ 25` **`hcatch`** is *equivalent to it* at a complete extension (the `hcatch` finding)
— so `c(X_T)` subsumes `hcatch`. **Scoped + probed + drafted in `chain-descent-cxt-scoping.md` (M1/M2/M3, 2026-06-13):**
- **M1 (probe):** `c(X_T)` **and** `k(X_T)` collapse to `O(1)` after `O(1)` points, uniformly across a diverse family
  (rank 3/4, cyclotomic/amorphic, char 2/odd, n=10–41) — **no falsifier**; so the sparse bound `2c(k−1)<n` holds on the
  extension. This is the evidence the target is true.
- **DECISION:** supply `c(X_T)` as a GENERAL theorem, not a family ladder (G2-B = infinitely many families). The route is
  **δ′ Option A — citation-free:** apply the (project-landed) sparse theorem to `X_T`. cite-Thm-4.1 is the fallback.
- **M2 (deep-research):** **build over cite is confirmed** — the sparse theorem is homogeneous-only (Q1) and the crux
  is open (Q2); citable results are group-side only (Q3). **Calibration (Q4): polynomial canonisation is citable for the
  rank-3/4 residue (Babai/Kivva); only sub-exponential in unbounded rank — and the residue IS rank 3–4.**

**NEXT (the handoff target, detail in `cxt-scoping.md` §6):** **A1 is LANDED (§CC.11–§CC.18, all axiom-clean, 2026-06-14)** — the
abundance discharge `allSingletonFiber_of_card_gt` (§CC.18) closes A1 via ONE counting lemma, skipping §S.10–§S.16 (the δ′ engine
accepts any bounded base, so the crude `b ≤ (k−1)c+1` suffices). **A1 now reduces `hclo` to the single `O(1)` threshold
`(k(X_T)−1)·c(X_T) < |T|`. Next = A2:** prove the residue meets it — `c(X_T), k(X_T) = O(1)` after `O(1)` individualizations
(M1-evidenced, M2-confirmed not citable, char-2 load-bearing). Then `allSingletonFiber_of_card_gt` + the landed seal wiring
(`reachesRigidOrCameron_viaExtensionDominatorClosure`) closes the seal `modulo {G3}`; then (deferred, §7) `SchurianScheme`→seal
wiring + the hImprim `G₀Irreducible → IsPrimitive` bridge.

**Orientation:** §1A why-not-GI∈P · §1B the `c(X_T)` reduction · §5.1 the build map · §5.2 the open problem + planning
insights · §7 do-not-re-walk · §8 condensed timeline + the changelog for full history.

## 0. How to work in this build

- **One rule:** treat every summary — this doc included — as a *hypothesis* to confirm against the Lean source and
  the primary papers. The source wins.
- **Build:** `bash scripts/build.sh` (serial, ~60–120 s; parallel `lake build` thrashes swap — don't). Add new
  modules to `scripts/build.sh` `MODULES=(…)` in topological order. Verify axioms with
  `lake env lean /tmp/check.lean` containing `#print axioms <decl>` (run from `GraphCanonizationProofs/`).
- **Papers / extraction:** the two load-bearing extracts are **version-controlled in
  [`docs/papers/`](./papers/README.md)** (2026-06-12; `/tmp` copies do not survive a reboot):
  `docs/papers/p4paper-arxiv-2006.13592.txt` (the Thm-4.1 paper) and `docs/papers/cartan-arxiv-1602.07132.txt`
  (Cartan/Thm 3.1). Both cleaned + greppable. For anything else: `pdf2txt <file.pdf> [first] [last]` is on PATH
  (`~/.local/bin`, user-site PyMuPDF); arXiv ids are stable, re-fetch with
  `curl -sL https://arxiv.org/pdf/<id> -o /tmp/x.pdf`.
- **GOTCHA — `grep`/`rg` find NOTHING on a *fresh* `pdf2txt` extraction. Run the cleaner first.** The cause is **NUL
  bytes** in the pdf2txt output: `grep` treats any file containing a NUL as *binary* and silently refuses to print
  matches (`LC_ALL=C grep` fails for the same reason — it is NOT a locale problem; the `setlocale: LC_ALL` warnings are
  noise). Secondary: pdf2txt uses ligatures *inside words* — "conﬁguration" (ﬁ), "diﬀerent" (ﬀ) — so even after NUL
  stripping `grep configuration` would miss them. **FIX (do this on every new extraction):**
  `python3 scripts/clean-extracted-text.py /tmp/x.txt` — strips NUL + NFKC-normalizes ligatures to ASCII, in place.
  Then plain `grep`/`rg` works (math symbols like `←` are preserved for reading; they don't break grep). The two
  papers above are already cleaned; `python` (`open(...,encoding='utf-8',errors='replace').read()`) also always works
  as a fallback.
- **Index:** after landing decls, regen `PublicTheoremIndex.md` via
  `python3 scripts/GenerateTheoremIndexes.py rewrite --with-line-numbers` then hand-fill Descriptions and delete
  stale rows by hand. (New `private` decls land in `PrivateTheoremIndex.md`; fill those too.)
- **Probes (C#, the empirical bed):** the project's discipline is *probe before Lean* — extract the concrete
  construction (matrices, ranks, witnesses) with a C# probe, then formalize. Probes live in
  `GraphCanonizationProject.Tests/` (self-contained, touch no production code); run one with
  `dotnet test GraphCanonizationProject.Tests/ --filter "FullyQualifiedName~<ProbeName>" --logger "console;verbosity=detailed"`
  (from the repo root). Key ones for this build: `Theorem41ConditionsProbe` —
  `Probe_DumpClebschMatrix` (dumps the ℤ₄² Clebsch colour matrix + dominator rank/pinners as Lean literals — the
  source of `ClebschConcrete.lean`'s data), `Probe_ExtractPinningRank` (the rainbow-rigidity construction extraction),
  `Probe_CatchUpGate_BasesAndDominators` (closure completes from every minimal base). To target a *different*
  residue, copy the dump/extract pattern.
- **`decide`-in-Lean limits (hard-won, see ClebschConcrete + §7):** plain `decide` only (NEVER `native_decide` — it
  adds `ofReduceBool`, breaking the axiom bar); it has **no `Decidable (p → q → r)`** for nested implications (single
  `p → q` is fine) — key a `decide`-fed lemma on a Nat-equality (e.g. `interNum = 1`), not a `relOfPair`-uniqueness
  `∀u, … → … → u = γ`; `∃!` has no synthesizable `Decidable` (give the term); **split big `decide`s with `fin_cases`**
  to bound kernel memory (a monolithic 16k-case coherence `decide` OOM-killed the box). `relOfPair` is
  `noncomputable`, so bridge it to a computable colour function before `decide`.

---

## 1. Why this doc exists — the reduced problem

The seal canonizes by descending the individualization–refinement tree, asking an oracle to sort each cell into
orbits. Its open content (G2-B) reduces to: **a primitive, small, non-abelian residual scheme `recovers`** — i.e.
individualizing a *bounded* base discretizes it. In the project's terms the seal consumes

> **`SeparatesAtBoundedBase S bound`** := `∃ S₀, |S₀| ≤ bound ∧ Discrete (warmRefine (schemeAdj S) … (individualizedColouring n S₀))`.

This *is* the **base number** `b(X) ≤ bound` (the WL-with-`S₀`-individualized point extension is complete).

The **seal-bridge gate** (worked across prior sessions; provenance: `chain-descent-module-adjoin-plan.md §9`)
established that this consumer factors into a 3-part chain, and located exactly what is open:

```
   reachesRigidOrCameron                              (the seal; conditional modulo {G3 + G2-B})
        ⟸  SeparatesAtBoundedBase S bound            ( = b(X) ≤ bound ; discharges the G2-B crux hCrux)
             ⟸  (A) Separable (orbitalScheme H)       [s(X)=1, the algebraic-iso notion — Ponomarenko Thm 4.1]
              ∧  (B) Separable ⟹ CellsAreOrbits at T  [the transport: algebraic separability ⟹ WL recovers orbits]
              ∧  (C) a bounded group base  IsBase T    [ = b(G) ≤ bound ]                       ◀── FREE, see §2
```

**The three findings that reduced it to (A)+(B):**
1. **(C) is free.** `exists_greedy_base_le_log` (landed) proves `b(G) ≤ log₂|Aut(X)|` unconditionally; the seal's
   *existing* "small" antecedent (`¬IsLargeSchemeViaAut` = `|Aut| ≤ poly(n)`) makes it `O(log n)`. Wired:
   `separatesAtBoundedBase_of_separable_of_small`. So (C) needs no math, citation, or probe.
2. **(A) and (B) are coupled — both need general-CC separability.** `Separable X` (§S.17) is *relation-level on the
   homogeneous X*; the transport (B) needs separability of the *point extension* `X_T`, a multi-fiber **general CC**
   the project's homogeneous `AssociationScheme`/`AlgIso` **cannot even express**. So you cannot do (B) "cheaply
   first" — it requires the same substrate that proves (A). They are one build.
3. **Separability is the right and only handle.** The block / scheme-congruence route to G2-B is *provably dead* on
   the primitive floor (`intraCellRelations_eq_singleton_zero_of_primitive`: a primitive scheme forces the intra-cell
   block to `{0}`); the gap is a *non-congruence amorphic WL-fusion* (the Clebsch `S₃`) no closed-subset captures.
   The forward/counting = separability route is the only one left. Ponomarenko Thm 4.1 is its general theorem.

**So: build the general-CC separability substrate, prove (A) and (B) for the residue, and the seal closes
(modulo the cited G3 only).** That is this document.

---

## 1A. Why the crux is NOT "GI ∈ P, give up" — the carve-out (read before pattern-matching to hopelessness)

It is easy to glance at the crux — *"a primitive small scheme recovers at a bounded base"* — and conclude
"bounded base = bounded WL-dimension = **GI ∈ P**, therefore hopeless, just isolate it." **That inference is
wrong, and it has already misled an onboarding pass. The reasoning is recorded here so it does not recur.**

**The scare, step by step (every step true):** (1) bounded base ⟺ bounded WL-dimension, and bounded WL-dim
canonizes in poly time; (2) WL-dimension is unbounded in general (CFI); (3) ∴ "prove bounded base" *smells like*
"prove GI ∈ P."

**The error is in step (3):** it conflates *bounded base for **the residue*** with *bounded base for **all
schemes***. Only the latter is GI ∈ P. The residue has already had **every known source of unbounded WL carved
out by a separate leg of the seal:**

| Unbounded-WL family | Carved out by |
|---|---|
| CFI / gauge twists | imprimitive gadget structure → **hImprim** (G2-A), or simply not primitive |
| abelian Cayley / circulants (unbounded WL — Wu–Ren–Ponomarenko 2025) | abelian → **leg B** (`AbelianConsumed`) |
| Johnson / Hamming / product action / large almost-simple | *large* → **Cameron** (G3) |
| **hidden Johnson (the genuine wall)** | **Cameron** — this is *precisely why* the seal's last leg is *"or Cameron"* |

After all four carves the residue is **primitive, small, non-abelian, non-Cameron** — and **no known
unbounded-WL scheme lives there**: seven empirical falsifiers returned **0 witnesses**, and the on-target ℤ₄²
amorphic-NLS bullseye *recovers* (WL-depth 2). So the crux is **not GI ∈ P; it is the tame remainder left
after the hardness was quarantined into Cameron.**

**Isolation is the method, applied recursively.** Each row above was *itself* once an "apparent GI ∈ P" that
was dissolved by identifying and walling a sub-case. The crux is the **last** such residue, and the same move
is expected to close it. It is hard *open* math, **not** a proven impossibility — and it was deemed the
*most likely* route to the unconditional seal, which is incompatible with treating it as unclosable.

**The closure angle (what is actually owed).** The route is **separability**: primitive-small-non-Cameron ⟹
bounded `s(C)` ⟹ recovery. This reduces to *"the residue's point extension satisfies Ponomarenko Thm 4.1's
conditions (domination + couple-extensions),"* which the C# probe has already **verified holds** on the
extension (`Theorem41ConditionsProbe`; bare dense `X` fails, the one-point extension `X_α` passes at every µ).
The structural reason to expect it in general is **Cameron's dichotomy** (a primitive group is either
large/classifiable or small/restricted): the *smallness* hypothesis together with *non-Cameron* forces the
bounded-structure regime, where domination holds by counting and separability converts it to recovery. The δ′
forced-triangle closure is the citation-free form of the same content.

**What would mean we are OFF track (the honest falsifier).** A primitive, small, non-abelian, **non-Cameron**
scheme with *unbounded* base — a genuine G2-B witness. That would show the hardness is *not* fully captured by
Cameron, i.e. *"or Cameron"* is the wrong carve and the seal is **false** (a statement change — itself a real
result). The 0-witness record is the standing evidence we are *on* track; equally, Thm 4.1's conditions
*failing* on the residue would be a warning — but the probe shows they hold.

**Discipline that prevents the misperception.** Before invoking "GI ∈ P" about any recovery claim, ask
**"what is still IN the residue?"** If the hard families are already carved into other legs, the claim is about
the tame remainder and GI ∈ P does not apply. The scare comes from forgetting the carve, not from the math.

---

## 1B. Does Cameron's dichotomy actually deliver domination? — the option-1 derivation (2026-06-13)

> **The load-bearing question §1A leaves asserted:** *"primitive + small + non-Cameron ⟹ Thm 4.1 domination,
> because Cameron's dichotomy forces the bounded-structure regime."* This section works it out against the paper
> (Ponomarenko §§4–5) rather than asserting it. **Verdict: Cameron's dichotomy does NOT deliver domination by
> itself — it delivers an *order* bound; domination is a *sparsity* property the dichotomy does not control. The
> two meet at one concrete open quantity, and that quantity is exactly the δ′ route's content. So the general
> route is not a shortcut around δ′ — it IS δ′, and this pins the single lemma both need.**

**What domination actually is (paper §5, made precise).** Thm 4.1 condition (i) — *every `Δ`, `|Δ|≤4`, has a `λ`
with `Δ ← λ`* — is delivered by the paper through ONE sufficient bound, the **parameter inequality (32)**:
`n > 3·c·(k−1)·k`, where `k = maxValency(X)` and `c = indistinguishingNumber(X)`. The mechanism (Lemma 5.2): the
set `Λ(α)` of points that *fail* to dominate `α` has `|Λ(α)| ≤ ½·c·k(k−1)` — because a non-dominator `λ` (with
`cʳₛₜ ≥ 2`) forces a same-`λ`-relation twin `β` in the `k`-bounded sphere `μs`, and double-counting the triples
`(α,β,λ)` against `|c(α,β)| ≤ c` and the `≤ k(k−1)` sphere-pairs caps `|Λ(α)|`. Union over `|Δ|≤4` (really ≤6)
points stays `< n` exactly when (32) holds, leaving a dominator outside it. **Domination is governed by `c` and
`k` — the local sparsity parameters — not by `|Aut|`.**

**What Cameron's dichotomy controls — and what it does not.** The cited classification (G3) is about *order /
largeness*: a primitive, rank-≥3, **large** CC is a Cameron scheme. Its contrapositive — *non-Cameron + primitive
⟹ not large ⟹ `|Aut|` bounded* — is the ONLY thing the dichotomy hands us, and it is an **order** fact. It says
nothing directly about `c` or `k`. So "Cameron's dichotomy ⟹ domination" is a non-sequitur as stated: the
dichotomy bounds `|Aut|`, (32) needs `c·k²`.

**Why the gap is real and not bridgeable for free.** On the *bare* residue, (32) FAILS (it is dense: `k ≈ n/4`,
`c` large — `3ck² ≫ n`), which is exactly what the probe saw (`X` undominated, §3.6). Domination only switches on
after individualizing points (the probe: `X_α`/`X_T` dominated). The orbit–stabiliser bound makes the `k` half of
the switch-on *free*: the relations of `X_T` from a point are `Aut_T`-orbits, so
**`maxValency(X_T) ≤ |Aut_T|`**, and the greedy base (landed `exists_greedy_base_le_log`) shrinks `|Aut_T|`
geometrically — each genuine individualisation at least halves it. So `k(X_T)` is driven down by base
individualisation with no new math. **But the `c` half is NOT free:** the crude bound `c ≤ n` forces (32) only at
`|Aut_T| < 1` = a *full* base (where `X_T` is already discrete and the statement is vacuous). To get domination at
**base + O(1)** rather than needing more, you must bound the **post-base indistinguishing number `c(X_T)`** — how
many points fail to separate a pair after individualising the base. *That* is the open quantity, and Cameron's
dichotomy says nothing about it.

**Where this lands — the convergence.** The post-base indistinguishing number being `O(1)` is precisely
*"forced (`c=1`) triangles are abundant after base-individualisation"* — which is the δ′ route's
`DominatorReachable`-closure content, and exactly the **rainbow-rigidity** the probe extracted (rank-4 rainbow
triangles are rigid ⟹ `c=1`; §8 2026-06-13). Domination's `Λ(α)` (Lemma 5.2) is the *same forced-triangle
calculus* (`cʳₛₜ=1`) the project calls `saAdj`/`determined_of_forcedTriangle` (build doc §3.4). So:

| Ingredient | Status |
|---|---|
| non-Cameron + primitive ⟹ `|Aut|` bounded (order) | **free** — Cameron's dichotomy (G3, cited) |
| `maxValency(X_T) ≤ |Aut_T|`, shrinks geometrically along a base | **free** — orbit–stabiliser + greedy base (landed) |
| `indistinguishingNumber(X_T) = O(1)` after a base (the `c` half) | **OPEN** — *the* single quantity; = δ′ forced-triangle abundance / rainbow-rigidity |

**Conclusion (actionable).** (1) Option 1, literally "Cameron's dichotomy ⟹ domination," is **false as a free
implication** — the dichotomy is an order bound; domination needs a `c·k²` sparsity bound it does not supply.
(2) The route is *not vacuous either*: it reduces — cleanly, via orbit–stabiliser — to **one** open quantity, the
post-base indistinguishing number `c(X_T)`. (3) That quantity is **identical** to the δ′ route's "forced-triangle
closure exhausts Ω from a base," so the general route and the recent δ′ work are the *same open content*, and the
δ′ (constructive, citation-free) formulation is the better target — the general framing does not buy a shortcut,
it confirms δ′ is correctly aimed and supplies the parameter (`c(X_T)`) to bound. (4) **Calibration caveat
(still open, flagged §8 2026-06-12):** "small" at the Babai/Sun–Wilmes threshold is *sub-exponential*
(`≈exp(n^{1/3})`), not poly; under that threshold `|Aut_T|` — and hence the number of individualisations to drive
`k` down — is `n^{O(1)}`-scale, so a *polynomial* (not merely "bounded") base needs `|Aut|` genuinely
poly-bounded. Pin which `IsLarge` the seal instantiates before claiming *polynomial* canonisation from this route.

---

## 2. The exact target (in Lean terms) — what "done" means

> This section gives the **separability ((A)+(B)) consumer chain** to the seal — one of the three checkpoints. The
> full chain incl. the now-primary **δ′-on-`X_T`** path is the build map in §5.1; the open input either way is `c(X_T)` (§5.2).

The (A)+(B) route delivers two theorems for the residue family `S = orbitalScheme H` (a `SchurianScheme n`):

- **(A)** `S.toAssociationScheme.Separable`  — the §S.17 predicate (or its general-CC strengthening in `CoherentConfig.lean`).
- **(B)** `∀ T, SeparabilityTransports S T`  — i.e. `S.toAssociationScheme.Separable → TwinsRealizedByResidualAut S T`.

These compose, through **already-landed, axiom-clean** decls, straight to the seal:

| Landed decl (file) | Role |
|---|---|
| `separatesAtBoundedBase_of_separable_of_small` (`CascadeAffine.lean §S-gate`) | `(A) ∧ (B at every base) ∧ (small bound) ⟹ SeparatesAtBoundedBase` — picks the group base internally (C free) |
| `separatesAtBoundedBase_of_separable` (`CascadeAffine.lean §S-gate`) | `(A) ∧ (B at T) ∧ IsBase T ∧ |T|≤bound ⟹ SeparatesAtBoundedBase` |
| `separatesAtBoundedBase_of_twinsRealized` (`Cascade.lean`) | the sink: `TwinsRealizedByResidualAut T ∧ IsBase T ⟹ SeparatesAtBoundedBase` |
| `twinsRealizedByResidualAut_iff_cellsAreOrbits` (`Cascade.lean`) | `TwinsRealizedByResidualAut S T ↔ CellsAreOrbits (schemeAdj …) T` (the sink *is* recovery) |
| `SeparabilityTransports` / `TwinsRealizedByResidualAut` (`CascadeAffine.lean` / `Cascade.lean`) | the two obligation predicates |
| `exists_greedy_base_le_log` (`Cascade.lean`) | `b(G) ≤ log₂|Aut|` — discharges (C) |
| `PersistentTwinYieldsBlock` (`Cascade.lean:4504`) | `¬SeparatesAtBoundedBase → IsLarge ∨ ∃ block`; **proving `SeparatesAtBoundedBase` discharges it vacuously** |
| `reachesRigidOrCameron_viaPersistentTwinBlock` (`Cascade.lean:4543`) | the seal capstone consuming `hCrux : PersistentTwinYieldsBlock` (+ G3 `hClassify`, landed `hImprim`, `hne`/`hrank`) |

So the **final assembly** is: prove (A)+(B) for `orbitalScheme H` ⟹ `SeparatesAtBoundedBase S bound` (via
`separatesAtBoundedBase_of_separable_of_small`, with `bound` = the poly "small" bound) ⟹ `PersistentTwinYieldsBlock`
holds (its `¬SeparatesAtBoundedBase` antecedent is false) ⟹ feed `reachesRigidOrCameron_viaPersistentTwinBlock`.
**The seal is then unconditional modulo G3 (the cited primitive-CC classification) alone.**

**The §S.17 objects already built** (homogeneous, `Separability.lean`; the general-CC versions in `CoherentConfig.lean`
extend these — keep names parallel):
```lean
structure AlgIso (X Y : AssociationScheme n) where
  relEquiv : Fin (X.rank + 1) ≃ Fin (Y.rank + 1)
  map_zero : relEquiv 0 = 0
  pres_intersection : ∀ r s t, X.intersectionNumber r s t = Y.intersectionNumber (relEquiv r) (relEquiv s) (relEquiv t)
def AlgIso.InducedBy (φ : AlgIso X Y) (f : Equiv.Perm (Fin n)) : Prop := ∀ r v w, X.rel r v w = Y.rel (φ.relEquiv r) (f v) (f w)
def Separable (X : AssociationScheme n) : Prop := ∀ (Y) (φ : AlgIso X Y), ∃ f, φ.InducedBy f
def SeparableParam (X : AssociationScheme n) : Prop := 3 * X.indistinguishingNumber * (X.maxValency - 1) * X.maxValency < n  -- Thm 5.1
```
Note `Separable` here quantifies `Y` over *homogeneous `AssociationScheme n`*, whereas Thm 4.1 quantifies over *general
CCs*. **This soundness gate is RESOLVED (2026-06-12): the general-CC `CoherentConfig.Separable`/`SeparablePointed`
quantify the partner over all `CoherentConfig n` (the widening), so the transport (B) consumes separability against the
*extension* alg-isos it actually needs.** (The concern, kept for the record: the homogeneous form is the *weaker*
predicate, omitting exactly the extension partners (B) uses — so the build targets the widened predicate, not §S.17.)

---

## 3. The mathematics (self-contained)

All from Ponomarenko, *On the separability of cyclotomic schemes over finite field*, **arXiv:2006.13592**
(`docs/papers/p4paper-arxiv-2006.13592.txt`), and Ponomarenko–Vasil'ev, *Cartan coherent configurations*,
**arXiv:1602.07132** (`docs/papers/cartan-arxiv-1602.07132.txt`); foundations in Evdokimov–Ponomarenko, *Separability number and Schurity number of coherent
configurations*, EJC 2000 (their ref **[4]**). Statements below are quoted/paraphrased faithfully; verify against
the source before relying on a subtlety.

### 3.1 Coherent configurations (general, multi-fiber)
A **coherent configuration (CC)** `X = (Ω, S)`: a partition `S` of `Ω×Ω` into *basis relations* such that (a) the
diagonal `1Ω` is a union of elements of `S` (the *reflexive* ones, whose union of supports gives the **fibers** =
a partition of `Ω`), (b) `S` is closed under transpose `r ↦ r*`, and (c) for `r,s,t ∈ S` the **intersection number**
`c^t_{rs} = |{z : (x,z)∈r, (z,y)∈s}|` is constant over `(x,y)∈t`. **Homogeneous** = one fiber (`1Ω ∈ S`); this is the
project's `AssociationScheme`. The point extension below is *not* homogeneous even when `X` is — it has the
individualized points as singleton fibers. **This multi-fiber generality is the substrate the project lacks.**

### 3.2 Point extension, base, base number (Cartan §2.2)
The **point extension** `X_{α,β,…}` is the smallest CC `≥ X` having `{α},{β},…` as fibers — equivalently the
WL-refinement of `X`'s coloured graph with `α,β,…` individualized. A set is a **base** if its extension is
*complete* (all singleton fibers); `b(X)` = min base size. `b(X) ≤ bound ⟺ SeparatesAtBoundedBase S bound`. For
schurian `X = Inv(G)`: `b(G) ≤ b(X)` (inequality (2)), and `b(G)` can be ≪ `b(X)` — the gap is the recovery/`s(X)`
content.

### 3.3 Algebraic isomorphism, separability, m-extension (the heart)
An **algebraic isomorphism** `φ : X → X'` is a bijection `S → S'` preserving all intersection numbers:
`c^t_{rs} = c^{φt}_{φr,φs}`. `φ` is **induced** by `f : Ω → Ω'` if `f` is an honest isomorphism realising it. `X`
is **separable** (`s(X) = 1`) if *every* algebraic isomorphism out of `X` is induced. (Quote, p4paper §2:
"`X` is called separable if … `Iso(X,X',φ)` is nonempty.")

The **m-extension** of `X` (p4paper §2): "the minimal fission of the tensor `m`-power of `X` for which
`Diag(Ωᵐ)` is the union of reflexive basis relations." Its intersection numbers are the **m-dimensional
intersection numbers** of `X` (`m=1` = usual). `X` is **m-separable** if determined up to iso by its m-dim
intersection numbers (`s(X) ≤ m`).

### 3.4 The forced-triangle (`c=1`) calculus — ALREADY IN THE PROJECT
p4paper §2.6: `x ←r y` means `c^y_{xr} = 1`; `x ↔r y` means `x ←r y` or `y ←r* x`. **Lemma 2.7(a):** if `x ←r y`
then for any `µ` and `β ∈ µy` there is a *unique* `α ∈ µx` with `r(α,β) = r`. **This is exactly the project's
`saAdj` forced-triangle / `valency_mul_intersectionNumber` / `transport` machinery from the landed PV Thm 3.1** —
see §4. Thm 4.1's whole proof is built on this calculus; **expect heavy reuse of the PV Thm 3.1 substrate.**

### 3.5 The theorems
- **Theorem 4.1 (the build target — general sufficient condition).** Let `X = (Ω,S)` be a CC, `µ ∈ Ω`. Assume
  (i) for every `Δ ⊆ Ω, |Δ| ≤ 4`, there is `λ ∈ Ω` with `Δ ← λ` (domination), and (ii) for all `α,β,γ ∈ Ω` there is
  `m ∈ S` with `µm ≠ ∅` and the *couple* `Qµ(α,β,γ)` has an `m`-extension. **Then** every algebraic isomorphism
  `φ : X → X'` is induced by an `f` taking `µ` to any given valid `µ'`; **in particular `X` is separable.** (Proof:
  p4paper §§3–4, built on the `c=1` calculus.) The conclusion is the **pointed** form — `f` is controllable on `µ` —
  which is *stronger* than bare `Separable` and is likely what the transport (B) needs.
- **Lemma 2.6 (the key reduction, from EP [4, Thm 4.6(1)]).** *If a **one-point extension** of `X` is separable,
  then `X` is 2-separable.* This is the lever from extension-separability to 2-separability — central to both the
  transport (B) and the lighter route to (A) (§5.3).
- **Theorem 2.5 (Cartan, base ⟹ separability).** A CC admitting a **1-regular** extension w.r.t. `m−1` points is
  `m`-separable. (Direction: extension/base ⟹ separability. The seal needs the *other* direction, base from
  separability — supplied by the transport (B), not by Thm 2.5. **But note (2026-06-12):** Thm 2.5's *premise* —
  1-regularity of the extension — feeds the seal *directly* through the landed B1–B5 bridge, no transport needed;
  that is the δ′ route, §5.3.)
- **Theorem 1.1 / 1.2 (the cyclotomic instance, already cited).** Every cyclotomic scheme over a finite field is
  2-separable with finitely many exceptions (`(p,d)` table: `p=2, 2≤d≤20`; `p=3, 2≤d≤10`; `p=5, 2≤d≤6`, minus a
  short list). This is the **affine slice**, already closed in Lean by *citation* (`TwinsAreSemilinear` /
  `reachesRigidOrCameron_affineSlice`). The general build *removes* this citation dependency and covers the
  *non-affine* residue too.

### 3.6 Why the residue needs the general theorem (not the sparse one already done)
The project already formalised **PV Cartan Thm 3.1** (the *sparse* sufficient condition `2c(k−1) < n ⟹` one-point
extension 1-regular `⟹ b(X) ≤ 2 ∧ 2-separable`) — see §4. The **dense amorphic residue violates `2c(k−1) < n`**
(it is dense: many equal-valency relations). Thm 5.1's parameter form `n > 3c(k−1)k` is *stricter* still, so no
parameter route reaches the residue. The dense power is **only** the m-extension route (apply the sufficient
condition to the 2-extension ⟹ 2-separability, as p4paper Thm 1.2 does via Lemma 2.6). Hence the `Ωᵐ` substrate.

---

## 4. What the project HAS vs LACKS

### HAS (build on these — decl names are load-bearing)
- **Homogeneous CC substrate** (`Scheme.lean`): `AssociationScheme n` (single-fiber, `rank`, `rel`,
  `intersectionNumber` + axioms), `ClosedSubset`, `IsPrimitive`, `schemeEquiv`, `orbitalScheme` (the residue
  constructor: `orbitalScheme H` for `H ≤ Perm Ω` is a `SchurianScheme`).
- **The §S.17 homogeneous separability layer** (`Separability.lean`): `AlgIso`, `AlgIso.InducedBy`, `Separable`,
  `SeparableParam`, `idAlgIso`. These are the `m=1`, single-fiber case of what Stage 1 generalises.
- **The landed PV Thm 3.1 substrate** (`Separability.lean §S.1–§S.16` + `CascadeAffine.lean §S-bridge/§S-stab`) —
  *this is the `c=1` forced-triangle calculus Thm 4.1 reuses*: `valency`, `maxValency`, `indistinguishingNumber`,
  `Smax`/`smaxAdj`, `saAdj` (the `c=1` local-rigidity relation) + `saAdj_symm`, `valency_mul_intersectionNumber`
  (triangle identity, = p4paper (4)), `transport`/`transport_step` (the `c=1` path-transport = Lemma 2.7-style),
  `saComp`/`compsOf` (components), `separatesAtBoundedBase_of_sparseSeparable` (the full sparse theorem), and the
  **warmRefine↔extension bridge** `relOfPair_eq_of_warmRefine_determined` (B1), `determined_of_saAdj` (B3),
  `discrete_of_connectivity` (B4), `separatesAtBoundedBase_of_connectivity` (B5) + the stabilization lemma
  `warmRefine_refineStep_samePartition`. **This is the template for the warmRefine↔CC-model bridge Stage 2 needs.**
- **The seal-bridge gate + sink + (C)** (the §2 table): the consumers (A)/(B) feed.

### LACKS — now essentially ALL LANDED (the ledger, collapsed 2026-06-13)
Everything the build set out to create is built and axiom-clean (decls in §9; the blow-by-blow is the changelog):
the general `CoherentConfig` type + coercion, the point-extension **construction** `pointExtension` (universal
property discharged), general `AlgIso`/`Separable`/`SeparablePointed`, the cited `Theorem41Statement`, the pointed
transport, the δ′ engine on the extension, and the wiring to the seal. The `Ωᵐ` m-extension / Lemma 2.6 tower turned
out **unneeded** (the pointed transport consumes `SeparablePointed` of the extension directly). **The one remaining
LACK is the open mathematics:** `hclo` — the `c(X_T)` bound (§5.2), supplied either by *proving* Thm 4.1's conditions
on the extension or by *citing* Thm 4.1 (the decision, STATUS).

### Mathlib
HAS: modules, `Basis`, `Submodule.span`, finite groups, `MonoidHom`, `Equiv.Perm`, `Finset`/`Fintype` combinatorics.
LACKS: **all** coherent-configuration / association-scheme / S-ring / separability theory. None of §3 exists in
Mathlib. `Scheme.lean` is the only CC substrate.

---

## 5. The build map + the open problem

### 5.1 The dependency chain — every link LANDED except the last (decls in §9)

```
seal  reachesRigidOrCameron
  ⟸ checkpoint  …viaExtensionDominatorClosure (δ′ on X_T)  |  …viaDominatorClosure (δ′ scheme)  |  …viaExtensionSeparability (Thm 4.1)
       ⟸ SeparatesAtBoundedBase   ⟸   Discrete (warmRefine … T)
            ⟸ discrete_warmRefine_of_extensionComplete            [E complete + hcatch]
                 ⟸ allSingletonFiber_of_dominatorClosure_pointExtension   [Sharp PROVED + T-singletons free]
                      ⟸  hclo : ∀ v, (pointExtension X T).DominatorReachable T v      ◀══ THE OPEN LINK ( = c(X_T) )
  +  (C) base FREE (exists_greedy_base_le_log)    +  hImprim (carried, §7)    +  G3 (cited)
```

Everything above the open link is axiom-clean and landed (the substrate `CoherentConfig.lean`, the δ′ engine `§CC.10`,
the wiring `CascadeAffine.lean §S-gate2`). **The sole open input is `hclo` — the `c(X_T)` content of §5.2.** Note the
`n ≥ 25` path re-incurs `hcatch` (`WarmTwinsAreFiberTwins`), which at a complete extension *equals* the 1-WL discreteness
(so it is part of `c(X_T)`, not a separate cheap step — the 2026-06-13 `hcatch` finding); it is *free* only where the
scheme-level δ′ already closes (n=16, `warmTwinsAreFiberTwins_of_dominatorClosure`).

### 5.2 The open problem: `c(X_T)` — a bounded-base forced-triangle closure on `X_T`

> **Scoped in depth in [`chain-descent-cxt-scoping.md`](./chain-descent-cxt-scoping.md)** (2026-06-13): the precise
> target, why both routes converge on `c(X_T)`, why it is *not* free-citable (it is the `s(X)` content; group base-size
> theory bounds `b(G)≤b(X)` only), the **central probe-first question** (is the `X_T`-level forced-triangle mechanism
> uniform across the family, or family-dependent? — this chooses Route δ′ vs cite-Thm-4.1), milestones M1–M4, and honest
> endpoints/risks. The immediate next action is **M1** (probe `c(X_T)` + extract the `X_T` mechanism across a diverse
> residue family). The insights below are the standing planning notes it builds on.

**Target:** for the residue family, exhibit a bounded base `T` and prove `∀ v, (pointExtension X T).DominatorReachable T v`
— equivalently a well-founded **pinning rank** (the iteration engine `dominatorReachable_of_rank` turns "exhibit a rank
whose every positive level is forced-triangle-pinned by two lower-rank points" into the closure). **Per the STATUS
decision this is ONE general theorem, not a family ladder** — supply it by citing Thm 4.1 (the conditions are
probe-confirmed on the extension: `X_α` passes domination + couple-extension at every non-singleton fiber) or by a
general δ′ closure argument. Planning insights (worked by hand; **verify before relying**):

- **Forced-triangle criterion, group-theoretic form.** On a schurian scheme, `γ` is pinned by `α,β` iff
  `Stab(α)·γ ∩ Stab(β)·γ = {γ}` (`dominatorReachable_step_of_stab`); a base has `⋂ Stab(t) = 1`, so the closure question
  is whether pairwise stabiliser-orbit intersections propagate reachability from `T` to all of Ω. The closure is
  `Aut(S)`-equivariant (`dominatorReachable_univ_image`) — prove at ONE representative base per orbit.
- **Affine/cyclic reduction.** For `affineScheme (G0pow β)` (`H := ⟨β⟩ ≤ F_q^×`), pinning ⟺ `∀ h ∈ H, (r + 1 − r·h) ∈ H → h = 1`,
  `r := (γ−α)/(β−γ)` — the known-open cyclotomic `s(C)` arithmetic (`dominatorReachable_G0pow_ratio_step` is the Lean form).
  One-round-from-a-2-base works **iff `|H| ≤ 2`**; larger `H` needs iteration.
- **Char-2 midpoint obstruction.** In characteristic 2 the midpoint triangles (`r = 1`) NEVER pin (`2−h = h ∈ H` always),
  so a char-2 residue (ℤ₂⁴ / `F_16`) needs non-midpoint bases — why those sit at WL-depth ≥ 2.
- **Scope.** The **affine** cyclotomic slice is already citation-closed (`reachesRigidOrCameron_affineSlice`), so affine
  δ′ only *removes a citation*; the genuinely new coverage is the **non-affine** residue (ℤ₄² amorphic-NLS = `orbitalScheme`),
  reached by the general/schurian step builders. Rainbow-rigidity (`c=1` for distinct colours) is an **order-16 artifact**
  (probe: gone by n=25) — do not formalise a parametric rainbow family; the `n ≥ 25` closure lives in `X_T`'s finer colours.
- **Realistic endpoint.** A clean *sufficient condition* on the stabiliser-orbit structure (or cited Thm 4.1) carried into
  a per-family capstone — not necessarily a from-scratch full closure.

### 5.3 Route options (decided — full ruled-out list in §7)
Route **β** (cite/prove Thm 4.1 via the extension) and Route **δ′** (the forced-triangle closure) reduce to the *same*
`c(X_T)` (§1B): δ′ is the citation-free Lean vehicle, (A)+(B) the uniform-coverage citation. Route **γ** (the parameter
bound `n > 3c(k−1)k`) is RULED OUT (the dense residue violates it, §7). Route **α** (the full `Ωᵐ` Thm 4.1 tower) only if
a stage forces `m > 2` — not needed so far.

## 6. Recommendation + honest scope

The substrate routes (α full-`Ωᵐ`, β 2-extension, δ/δ′ forced-triangle) have **collapsed to one open quantity** as the
build matured — see §5.3 for the decided route map and §7 for what is ruled out. In short: **δ′ on `X_T` is the
citation-free Lean vehicle; cited Thm 4.1 ((A)+(B)) is the uniform-coverage alternative; both reduce to `c(X_T)` (§1B).**

**Honest scope (unchanged since creation):** this is research-scale, multi-session, and *may not close* — the residue
could be unbounded-`s`, in which case a counterexample is a *statement change* (the seal is false — itself a real
result). The standing evidence that closure is the likely outcome: **seven empirical falsifiers returned 0 G2-B
witnesses**, including the on-target ℤ₄² bullseye (recovers at WL-depth 2). The risk is proof-effort, not falsification.

---

## 7. Decision log — ruled out / do not re-walk

- **Block / scheme-congruence route to G2-B is DEAD on the primitive floor.**
  `intraCellRelations_eq_singleton_zero_of_primitive`: a primitive scheme forces the intra-cell block to `{0}`. The
  gap is a non-congruence amorphic WL-fusion (Clebsch `S₃`). Only the forward/separability route survives. (This is
  *why* this build exists.)
- **(C) the group base is not an obstacle** — `exists_greedy_base_le_log` + "small". Do not re-survey it.
- **The transport (B) is NOT a cheap pre-substrate de-risk** — it needs extension-separability (general CC), coupled
  to (A). Do not look for a homogeneous-only proof of `Separable ⟹ CellsAreOrbits`; it does not exist (the twin lives
  in the multi-fiber extension).
- **Thm 5.1 parameter route (γ) is ruled out** (stricter than the done sparse Thm 3.1; residue is denser).
- **`decide`-checking a hard-coded `SchurianScheme` is INFEASIBLE — do not attempt.** Promoting the concrete
  `clebschZ4Scheme` (`AssociationScheme`, `decide`-checked) to a `SchurianScheme` (to feed the *seal* capstone, not
  just `Discrete`) requires the `schurian` axiom `∀ i v w v' w', rel i v w → rel i v' w' → ∃ π ∈ auts, π v=v' ∧ π w=w'`
  — `∃`-over-auts `∀`-over-pairs ≈ `4·16⁴·32` ≈ 8M kernel checks, ~32× the coherence `decide` that was already
  borderline-OOM. Splitting helps a constant factor, not enough. And `orbitalScheme` (schurian by construction) is
  `noncomputable`, so it cannot be `decide`d either. Net: the concrete witness stays at `AssociationScheme`/`Discrete`
  level; feeding the seal for a concrete non-affine residue needs a *non-`decide`* schurity argument (research effort,
  not mechanical). Recorded 2026-06-13.
- **The orbit-level harvest re-key is a vacuity trap** (`coversOrbits_of_realizers` keyed on `OrbitPartition` is
  trivially true — orbit-mates are aut-related by definition). Keep all recovery content on *visible* (warmRefine)
  realizers. The sink `TwinsRealizedByResidualAut` is correctly keyed (≡ `CellsAreOrbits`).
- **Do not anchor on group non-commutativity** (`not_comm_of_orbit_disagree` is the ¬leg-B / *consumption* statement,
  a different thing). C₇/`D₇` is non-abelian yet recovers via its metric structure — separability, not commutativity,
  is the content. Symmetric schemes have commutative Bose–Mesner algebras regardless of the group.
- **The affine slice is already closed by citation** (`reachesRigidOrCameron_affineSlice` via cyclotomic
  2-separability, Thm 1.1). This build *removes* that citation and covers the non-affine residue — do not re-do the
  affine slice; do reuse its template (`powAffineSeparates_of_twinsAreSemilinear` = the transport at the affine
  instance, with the realiser the explicit linear `affinePermFin`).
- **Custom-axiom-free invariant:** cited classifications (G3 `PrimitiveCCClassification`, any EP/Ponomarenko theorem
  you choose to *cite* rather than *prove*, e.g. Lemma 2.6 if you carry it) must be theorem-statement **hypotheses**,
  never fresh `axiom`s. Decide per lemma: prove it, or carry it as a named hypothesis on the final theorem.

---

## 8. Increment log — condensed milestone timeline

> **Full per-increment detail is in the sibling [`chain-descent-general-cc-separability-changelog.md`](./chain-descent-general-cc-separability-changelog.md)
> — if a full entry is needed, append new entries THERE** (newest at bottom, full format). This is the one-line-per-milestone arc; the
> STATUS block at the top is the authoritative current state, this is the path that reached it.

- **2026-06-11** — doc + plan created (inputs: gate / sink / (C)-discharge / PV-Thm-3.1 substrate / §S.17 separability).
- **2026-06-12** — two onboarding review passes (plan survived); papers version-controlled to `docs/papers/`.
- **2026-06-12** — Stage-3 gate ran: Thm 4.1's hypotheses HOLD on the residue's one-point extension (Route β viable).
- **2026-06-12** — Stage 0 decided (Option H, colour-function CC) + Stage-1 skeleton landed (`CoherentConfig.lean`):
  `CoherentConfig`, general `AlgIso`/`Separable`/`SeparablePointed`, `Theorem41Statement` (cited carry), `IsPointExtension`.
- **2026-06-12** — Stage-2.1 direction check: naive twin⟹alg-iso REFUTED at arbitrary `T`; cells=fibers only at `|T|≥2` (bases).
- **2026-06-12** — Stage 1.2 LANDED (`§CC.8`): the point-extension *construction* `pointExtension X T` + universal property.
- **2026-06-12** — Stage 2 transport LANDED modulo the catch-up + the citation checkpoint `…viaExtensionSeparability` (`§CC.9`/`§S-gate2`).
- **2026-06-12** — catch-up probe-gate GREEN at every minimal base; `b(X)=b(G)`; the `c=1` dominator closure discretizes at scheme level.
- **2026-06-12** — the **δ′ dominator-closure engine** LANDED, citation-free (`§S-bridge-δ`/`§S-gate2`): checkpoint `…viaDominatorClosure` {G3+hImprim+`hclo`}.
- **2026-06-12/13** — Stage-3 δ′ toolkit: forced-triangle criterion (affine / general / schurian `Stab·γ∩Stab·γ={γ}`), closure equivariance,
  the iteration engine `dominatorReachable_of_rank`, the `F_q`-power + ratio step builders (char-2-midpoint obstruction explicit).
- **2026-06-13** — first END-TO-END family closures: `…viaG0powNeg` (`g=-1` odd char, `hclo` PROVED not carried) + subfield `H=K^×` (multi-round, but IMPRIMITIVE).
- **2026-06-13** — §1B derivation: Cameron's dichotomy delivers ORDER not domination; the open quantity is the post-base `c(X_T)` = the δ′ content.
- **2026-06-13** — probe extracted the non-affine closure construction (rainbow-triangle rigidity, depth 3) ⟹ the **concrete ℤ₄² Clebsch δ′ closure** in Lean (`ClebschConcrete.lean`, `b(X)≤2`, `AssociationScheme`-level).
- **2026-06-13** — rainbow-rigid family lemma LANDED, then **probe-REFUTED as parametric**: rainbow-rigidity + scheme-level δ′ are **order-16 artifacts** (Z5²/n=25 needs `X_T`'s finer colours).
- **2026-06-13** — the **δ′ engine LIFTED to the general CC** (`§CC.10`), running on `X_T = pointExtension`; carried `Sharp` the lone hypothesis.
- **2026-06-13** — **`Sharp (pointExtension X T)` PROVED** (`sharp_pointExtension`, `§CC.10`) + `allSingletonFiber_of_dominatorClosure_pointExtension` (carries only `hclo`).
- **2026-06-13** — **DECISION:** δ′ family-by-family DRIES UP (G2-B = infinitely many families) ⟹ the input must be GENERAL (cite Thm 4.1 / (A)+(B), per the affine-slice precedent).
- **2026-06-13** — **the wiring to the seal LANDED** (`§S-gate2`): `…viaExtensionDominatorClosure` carries {G3+hImprim+`hclo`-on-`X_T`+`hcatch`}; probe: 1-WL base = 2-WL `b(X)` on every residue (no dimWL-exchange citation).
- **2026-06-13** — `hcatch` analysis: at a complete extension `WarmTwinsAreFiberTwins ↔ Discrete(warmRefine)`, so the `n≥25` `hcatch` IS the 1-WL discreteness (= `c(X_T)` content), free only where scheme-level δ′ closes.

## 9. Quick reference — decl/source index

**Seal connection (landed, consume these):** `reachesRigidOrCameron_viaPersistentTwinBlock` (`Cascade.lean:4543`),
`PersistentTwinYieldsBlock` (`Cascade.lean:4504`), `SeparatesAtBoundedBase` (`Cascade.lean:4437`),
`separatesAtBoundedBase_of_separable_of_small` / `separatesAtBoundedBase_of_separable` / `SeparabilityTransports`
(`CascadeAffine.lean §S-gate`), `separatesAtBoundedBase_of_twinsRealized` / `TwinsRealizedByResidualAut` /
`twinsRealizedByResidualAut_iff_cellsAreOrbits` (`Cascade.lean`, by `SeparatesAtBoundedBase`),
`exists_greedy_base_le_log` (`Cascade.lean:916`), `CellsAreOrbits` (`CascadeOracle.lean:268`), `IsBase`
(`Cascade.lean:70`), `orbitPartition_iff_residualAut` (`Cascade.lean:477`), `orbitalScheme` (`Scheme.lean`).

**Homogeneous separability (extend these):** `AlgIso` / `Separable` / `SeparableParam` / `idAlgIso`
(`Separability.lean §S.17`).

**General-CC substrate (LANDED 2026-06-12, build on these):** `CoherentConfig` / `interNum` / `transposeRel` /
`relOf_diag_left_eq` (derived fiber coherence) / `AssociationScheme.toCoherentConfig` / general `AlgIso` /
`Separable` / `SeparablePointed` / `Dominates` / `DominationCondition` / `IsCoupleExtension` /
`CoupleExtensionCondition` / `Theorem41Hypotheses` / **`Theorem41Statement`** (the cited carry) / `Refines` /
`SingletonFiber` / `IsPointExtension` / `ExtensionSeparable` / `discreteCC` (`CoherentConfig.lean`).
**The §CC.8 construction (LANDED 2026-06-12):** `extFlag` / `extInitSetoid` / `pairCount` / `pairStep` /
`pairIter` (+ `_zero`/`_succ`/`_le_init`/`_swap`) / `numClasses` (+ `_le_of_le`/`le_of_numClasses_le`/`_le_sq`/
`_growth`) / `exists_pairIter_fixed` / `stableSetoid` / `pairStep_stableSetoid` / `stableSetoid_pairCount` /
`pairCount_swap` / `pairCount_eq_of_zrel` (the counting heart) / `zrel_le_pairIter` / `stableEquiv`(`_eq_iff`) /
**`pointExtension`** / `pointExtension_relOf_eq_iff` / **`isPointExtension_pointExtension`** /
**`exists_isPointExtension`** / `isPointExtension_unique` (`CoherentConfig.lean §CC.8`).
**The Stage-2 transport (LANDED 2026-06-12, modulo the catch-up):** `SeparablePointed.exists_aut_of_fiber_eq` /
`IsPointExtension.aut_fixes` / `Refines.aut_descends` / **`fiberTwin_realized_of_separablePointed`** /
`extension_complete_of_separablePointed` (`CoherentConfig.lean §CC.9`); **`WarmTwinsAreFiberTwins`** (the
isolated catch-up) / `isSchemeAut_of_relOfPair_eq` / **`twinsRealized_of_extensionPointed`** /
`separatesAtBoundedBase_of_extensionPointed`(`_of_small`) /
**`reachesRigidOrCameron_viaExtensionSeparability`** (the citation checkpoint) (`CascadeAffine.lean §S-gate2`).
**The δ′ engine on the general CC (LANDED 2026-06-13, `CoherentConfig.lean §CC.10` — the δ′ closure on the
extension `X_T`, for the n≥25 residue the scheme-level engine can't reach):** the forced-triangle criterion
both directions **`CoherentConfig.interNum_eq_one_of_forcedUnique`** / **`forcedUnique_of_interNum_eq_one`** /
the inductive closure **`CoherentConfig.DominatorReachable`** / step builder
**`dominatorReachable_step_of_unique`** / the rank engine **`dominatorReachable_of_rank`** / the
refinement hypothesis **`Sharp`** — **now PROVED for the extension (2026-06-13): `sharp_pointExtension`**
(via the `a`-isolating count + `stableSetoid_pairCount` fixpoint coherence) / the propagation
**`singletonFiber_of_dominatorReachable`** / the discreteness payoff
**`allSingletonFiber_of_dominatorClosure`** (closure + `Sharp` + `T`-singletons ⟹ `X` discrete = `T` a base)
and its unconditional-on-`X_T` corollary **`allSingletonFiber_of_dominatorClosure_pointExtension`**
(carries **only `hclo`** — `Sharp` and `T`-singletons both discharged for `pointExtension X T`).
**The wiring to the seal (LANDED 2026-06-13, `CascadeAffine.lean §S-gate2` — the δ′-on-`X_T` path reaches
`reachesRigidOrCameron`):** **`discrete_warmRefine_of_extensionComplete`** (complete `E` + catch-up ⟹ `warmRefine`
discrete) / **`separatesAtBoundedBase_of_extensionDominatorClosure`** (`hclo`-on-`X_T` + `hcatch` + bound ⟹ the seal
consumer; `Sharp` discharged internally) / the capstone **`reachesRigidOrCameron_viaExtensionDominatorClosure`**
(carries {G3 + `hImprim` + `hclo`-on-`X_T` + `hcatch`} — the citation-free `n ≥ 25` checkpoint).
**The catch-up analysis:** **`warmTwinsAreFiberTwins_of_warmDiscrete`** (warm-discrete ⟹ `hcatch`; with the bridge ⟹
`hcatch ↔ warmRefine-discrete` at a complete `E` — so `n ≥ 25` `hcatch` ≡ the 1-WL discreteness = open content, NOT
plumbing) / **`warmTwinsAreFiberTwins_of_dominatorClosure`** (`hcatch` free where the scheme-level δ′ closes — n=16
non-vacuity; does not extend to `n ≥ 25`).
**The CC sparse substrate — A1 incr 1–2 (LANDED 2026-06-13, `CoherentConfig.lean §CC.11`; the citation-free `c(X_T)`
route, live work in `chain-descent-cxt-scoping.md`):** the indistinguishing number **`indistinguishingNumberOf`** /
**`indistinguishingNumberOf_eq_card`** (the geometric form `c(r)=|{γ:relOf γ α=relOf γ β}|`) / `IsReflexive` /
**`indistinguishingNumber`** (`c(X)`) / `indistinguishingNumberOf_le`; the valency **`sourceFiber`** / **`valency`** /
**`valency_eq_card`** / **`maxValency`** (`k(X)`) / `valency_le_maxValency`; and **`SparseSeparable`** (`2c(k−1)<n`).
**A1 incr 3–7 — the §S.4–§S.9 substrate (LANDED 2026-06-14, `CoherentConfig.lean §CC.12`–`§CC.16`, axiom-clean):**
the CC pair-count **`pu`**/**`pu_eq`**, the transpose bridge **`relOf_right_eq_iff_left`** (CC substitute for `relOfPair_symm`),
**`not_isReflexive_relOf_of_ne`**, **`card_relNeighbors_le_maxValency`** (`A.card ≤ k(X)` for non-reflexive `u`, replacing
homogeneity's exact `= k`), **`sum_pu_le`** (`Σ_δ pᵤ(δ) ≤ k(k−1)·c`, §S.6), **`pu_eq_sum`** (`pᵤ(δ) = Σ_w c^v_{uw}(c^v_{uw}−1)`,
§S.7), **`outDeg_mul_interNum`**/**`valency_mul_interNum`** (the triangle identity `n_k·c^k_{i,j} = n_i·c^i_{k,j*}`, §S.8 —
transpose-aware: `j* = transposeRel j`, the first §S statement M2-Q1 changes), the §S.4 graph layer
`InSmax`/`smaxAdj`/`SmaxConnected`/`saAdj`/`SaConnected` + **`saAdj_symm`** (`§CC.15`; forced-triangle relation symmetric —
`s*` lands on `relOf γ β`), and §S.5 `sum_interNum_eq_outDeg` + §S.9 `valency_le_pu_of_valency_lt` (`§CC.16`, the `n_u>n_v`
half of Lemma 3.5(1), carrying the source witness `relOf α β₀ = u`). Direct ports of `Separability.lean §S.4–§S.9`.
**A1 incr 8 — §CC.17 (LANDED 2026-06-14, axiom-clean):** **`fiberSet`** / **`outDeg_eq_interNum`** (`#{w:relOf u w=r} =
c^{relOf u u}_{r,r*}`, generalises `valency_eq_card`) / **`fiberSize_mul_valency`** (`|F_src(r)|·n_r = |F_tgt(r)|·n_{r*}`, the
class double-count) / **`smaxAdj_symm_of_sameFiber`** (within-fiber smax symmetry). Resolved the route fork: `smaxAdj` symmetric
only intra-fiber ⟹ global `SmaxConnected` FALSE on the multi-fiber CC. (Landed infra; off the critical path after §CC.18.)
**★ A1 incr 9 — §CC.18 (LANDED 2026-06-14, axiom-clean — A1 ESSENTIALLY DONE):** **`dominatorReachable_of_basePinsAll`** (CC mirror)
/ **`basePinsAll_of_card_gt`** (`(k−1)·c < |T| ⟹` every `γ∉T` pinned by two base points; indistinguishing-number union bound) /
**`dominatorReachable_of_card_gt`** (`⟹ ∀v DominatorReachable T v`) / **`allSingletonFiber_of_card_gt`** (capstone: `(k(X_T)−1)·c(X_T)
< |T| ⟹ X_T complete`). **The abundance route — ONE counting lemma, skips §S.10–§S.16** (the δ′ engine takes any bounded base, so
crude `b ≤ (k−1)c+1` ≫ enough; cross-fiber automatic, no smax). The §S.10–§S.16 sα port is abandoned as unnecessary.
**A2 Phase 0 — §CC.19 (LANDED 2026-06-14, axiom-clean — the monotonicity/padding bridge):** **`indistinguishingNumber_mono`** /
**`maxValency_mono`** (`Refines Y Z ⟹ c(Y) ≤ c(Z)`, `k(Y) ≤ k(Z)`) / **`refines_pointExtension_of_subset`** (`T₀ ⊆ T ⟹ X_T`
refines `X_{T₀}`) / **`allSingletonFiber_of_card_gt_subset`** (padding capstone: `T₀ ⊆ T ∧ (k(X_{T₀})−1)·c(X_{T₀}) < |T| ⟹ X_T`
complete). Reduces A2 to the crisp **"bound `c(X_{T₀}), k(X_{T₀}) = O(1)` at one `O(1)` base"**.
**OPEN (the rest) = A2 core:** bound `c(X_{T₀}), k(X_{T₀}) = O(1)` for the residue (rank 3–4, bounded WL-dim). Attack: Phase 2
deep-research (cite-vs-prove, RUNNING), Phase 1 probe, Phase 3 prove/carry; then §CC.19 + seal wiring closes `hclo`.
**The δ′ dominator-closure engine (LANDED 2026-06-12, CITATION-FREE — the lighter seal path):**
**`determined_of_forcedTriangle`** (B3′, smax-free) (`CascadeAffine.lean §S-bridge`) / **`DominatorReachable`** /
`determinedAt_of_dominatorReachable` / **`discrete_of_dominatorClosure`** /
**`separatesAtBoundedBase_of_dominatorClosure`** (`CascadeAffine.lean §S-bridge-δ`) /
**`reachesRigidOrCameron_viaDominatorClosure`** (the citation-free checkpoint, carries only
{G3 + `hImprim` + `hclo : ∀ v, DominatorReachable S T v`}) (`CascadeAffine.lean §S-gate2`).
**Stage 3 substrate — the affine forced-triangle criterion (LANDED 2026-06-12, the δ′ family argument runs on
these):** the general (any-scheme) criterion **`interNum_eq_one_of_forcedUnique`** (`c=1` ⟺ filter `={γ}`) /
**`dominatorReachable_step_of_unique`** (the general step builder, subsumes the affine one + non-affine residues) /
**`dominatorReachable_step_of_stab`** (the schurian `Stab(α)·γ ∩ Stab(β)·γ = {γ}` reading — the closure's geometric
handle); the affine specialisation **`affineScheme_interNum_eq_one_of_unique`** (orbit-of-difference uniqueness) /
**`dominatorReachable_affine_step`** (`CascadeAffine.lean §S-stage3`); the closure-equivariance reduction
**`dominatorReachable_map`** / **`dominatorReachable_univ_image`** (complete closure transports across `Aut(S)`-images
of the base — prove at one representative); the **iteration engine `dominatorReachable_of_rank`** (a well-founded
pinning rank ⟹ `∀ v, DominatorReachable S T v` — the brick turning the step builders into a global closure) and the
**one-round criterion `dominatorReachable_of_basePinsAll`** (every non-base point pinned by two base points ⟹ closure);
the **rainbow-rigid family lemma (2026-06-13, the §1B `c(X_T)` content operationalised)** —
**`dominatorReachable_of_rank_interNum`** (the general public `interNum`-keyed rank engine, `ClebschConcrete`'s private
`domReach_of_rank_pin` lifted) / **`RainbowRigid`** (rainbow triangle ⟹ `c=1`, the small-`c(X_T)` hypothesis) /
**`interNum_eq_one_of_rainbow`** (rigidity ⟹ pinning) / **`dominatorReachable_of_rainbowRank`** (a `RainbowRigid`
scheme with a rainbow rank closes — lifts `clebschZ4_closure` to the rainbow-rigid family) + the non-vacuity witness
**`clebschZ4_rainbowRigid`** (`ClebschConcrete.lean`, `decide`)
(`CascadeAffine.lean §S-bridge-δ`); the **cyclotomic arithmetic reduction** **`fieldOf`** (point→`F_q`) /
**`fieldOf_injective`** /
**`G0pow_orbit_iff`** (a `G0pow g`-orbit relation ⟺ multiplication by `g^k` through the field iso) /
**`dominatorReachable_G0pow_step`** (the forced-triangle step builder with `huniq` in pure `F_q` powers) /
**`dominatorReachable_G0pow_ratio_step`** (the ratio form `(r+1−r·h)∈⟨g⟩→h=1`, `r=(c−a)/(b−c)` — divides out the
field differences, exposes the char-2-midpoint obstruction); **the FIRST family closure** —
**`dominatorReachable_G0pow_neg`** (`g=-1`, odd char: any 2-base closes in one round) and the seal capstone
**`reachesRigidOrCameron_viaG0powNeg`** (the seal on the `g=-1` family with `hclo` PROVED, not carried — only
{G3+hne+hrank+hImprim} remain); the **multi-round subfield closure** —
**`dominatorReachable_G0pow_subfield_step`** (size-free `r∉K ⟹ pinned`) / **`dominatorReachable_G0pow_subfield`**
(the `H=K^×` family closes in 2 rounds; **imprimitive — validates the engine, not the primitive residue**) +
private `ratio_not_mem_num_out`/`_denom_out`
(`CascadeAffine.lean §S-stage3-δ`). Open (the genuine `s(C)` core): the **pinning-rank witness** for the
**primitive irreducible** larger `H` (no subfield shortcut), char-2 (Clebsch), and the **non-affine** residue
(new-coverage target) — define `rank` and verify per-level pinning via the general/schurian/`F_q`-power builders.

**The concrete non-affine closure (LANDED 2026-06-13, `ChainDescent/ClebschConcrete.lean` — the FIRST non-affine
δ′ closure in Lean):** **`clebschZ4Scheme`** (the ℤ₄² amorphic-NLS Clebsch scheme as a hard-coded
`AssociationScheme 16`, axioms by `decide`) / **`clebschZ4_closure`** (`∀ v, DominatorReachable clebschZ4Scheme
{0,1} v` — the `hclo` discharged for the real non-affine bullseye) / **`clebschZ4_discrete`** (`b(X) ≤ 2`); built
on `clebschZ4ColF` (the colour matrix) / `clebschZ4_relOfPair` (the bridge) / `clebschZ4Rank` + `clebschZ4Pin` (the
probe rank/pinners) / private `domReach_of_rank_pin` (the `interNum`-keyed rank engine). Axiom-clean, no
`native_decide`. Scope: parameter-scoped to Clebsch `(16,5,0,2)`, `AssociationScheme`-level (does not feed the seal
capstone — needs `SchurianScheme`).

**PV Thm 3.1 `c=1` substrate (reuse heavily):** `saAdj` / `saAdj_symm` / `valency_mul_intersectionNumber` /
`transport` / `transport_step` / `saComp` / `compsOf` / `separatesAtBoundedBase_of_sparseSeparable`
(`Separability.lean §S.1–S.16`); the warmRefine bridge `relOfPair_eq_of_warmRefine_determined` /
`determined_of_saAdj` / `discrete_of_connectivity` / `separatesAtBoundedBase_of_connectivity` /
`warmRefine_refineStep_samePartition` (`CascadeAffine.lean §S-bridge/§S-stab`).

**Papers:** Ponomarenko, arXiv:2006.13592 (**`docs/papers/p4paper-arxiv-2006.13592.txt`**, version-controlled) —
**Thm 4.1** (§4, the target; statement at line ~552 in the extract), **Lemma 2.6** (one-pt ext separable ⟹
2-separable, line ~299), **m-extension** (§2), Thm 1.1/1.2 (cyclotomic). Ponomarenko–Vasil'ev, arXiv:1602.07132
(**`docs/papers/cartan-arxiv-1602.07132.txt`**, version-controlled) — **Thm 2.5** (1-regular `(m−1)`-ext ⟹
`m`-separable, line ~388), base defs (§2.2), **Thm 3.1** (the sparse condition, already formalised). Chen–Ponomarenko,
*Coherent Configurations* (the monograph, p4paper ref **[3]**) — the `b(X) ↔ s(C) ↔ dimWL` theory incl.
`dimWL(X) ≤ dimWL(X_α) + 1` (§4.2; the transport lead, Stage 2.2(c)). Evdokimov–Ponomarenko,
*Separability number and Schurity number of coherent configurations*, EJC 2000 (ref **[4]**) — `s(X)`/`t(X)`
foundations, Thm 4.6(1) (source of Lemma 2.6). Extraction: `pdf2txt`, then **`scripts/clean-extracted-text.py`** or
grep finds nothing (NUL bytes; §0 gotcha). The two papers above are committed cleaned (`docs/papers/README.md`).

**Provenance (do not need to read, but for the curious):** the seal-bridge gate / transport / (C) findings are in
`chain-descent-module-adjoin-plan.md §9`; the seal state in `chain-descent-seal-handoff.md`; the project overview in
`docs/00-START-HERE.md`.
