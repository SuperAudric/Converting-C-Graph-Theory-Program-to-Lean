# Chain descent — Tier 3 paper plan (decomposability)

A paper-first plan for Tier 3 of the orbit-recovery program: every
obstruction the chain-descent oracle produces decomposes as
`(cascade-class residue) ⋊ (Z_2^d abelian residue)`. Equivalently
(dually), the cascade + linear oracles together resolve every
obstruction without a non-abelian residual.

This is a **planning doc, not a paper**. It scopes the theorem-target,
breaks it into sub-claims, names the risks, records a sibling framing
(§8) that may complement the main attack, and identifies what would
have to land in Lean once the paper is rigorous.

> ⚠ **Equivalence to GI ∈ P.** The Tier-3 statement as written is
> equivalent in strength to graph isomorphism being in P. The matroid
> memo ([`chain-descent-matroid.md`](./Archive/ChainDescent/chain-descent-matroid.md) §8.4)
> and the calculator's construction question
> ([`chain-descent-calculator.md`](./chain-descent-calculator.md) §7)
> both make this explicit. This plan does not claim to close that gap;
> it claims to *target* it through a clean inductive scaffolding —
> Tier 1 (orbit-recovery for CFI) + Tier 2 (orbit-recovery for schurian
> schemes) as base cases, plus a composition theorem (§7) that handles
> the layered interaction. A successful Tier 3 proof would resolve GI;
> a clean Tier-3 *counterexample* — a graph the layered oracle cannot
> peel — would be the first known hidden-Johnson graph.

For broader context:
[`chain-descent-strategy.md`](./chain-descent-strategy.md) (algorithm),
[`chain-descent-calculator.md`](./chain-descent-calculator.md)
(oracle / cost model),
[`chain-descent-orbit-recovery.md`](./chain-descent-orbit-recovery.md)
(Tier 1 + Tier 2),
[`chain-descent-hidden-johnson.md`](./chain-descent-hidden-johnson.md)
(visible Johnson killed).

---

## 1. Headline

> **Theorem 3 (Tier-3 decomposability, target).** Let `G` be a connected
> graph and let `Aut_desc(G)` be the residual symmetry that arises at
> any node of the chain descent on `G`. Then `Aut_desc(G)` admits a
> normal-form decomposition
>
> `Aut_desc(G) ≅ N ⋊ Q`,
>
> where:
>
> - `N` is an elementary-abelian 2-group (the abelian residue, handled
>   by the linear oracle of
>   [`chain-descent-calculator.md`](./chain-descent-calculator.md) §6);
> - `Q` is in the cascade class (handled by Tier 1 + Tier 2 of
>   [`chain-descent-orbit-recovery.md`](./chain-descent-orbit-recovery.md)
>   plus its eventual Tier-3a extension to nested constructions).
>
> Moreover, the decomposition is *constructively obtained* by the
> layered oracle in polynomial time, without exploring more than one
> branch per genuine decision.

The corollary is the polynomial-or-flag bound for the chain-descent
canonizer:

> **Corollary 3.** Under Theorem 3, the chain-descent canonizer is
> polynomial-time on every connected graph. Equivalently, GI ∈ P.

The contrapositive — what a Tier-3 counterexample would deliver:

> **Anti-corollary (counterexample form).** A connected graph `G` whose
> `Aut_desc(G)` does *not* admit the decomposition above is a witness
> to the construction question of
> [`chain-descent-calculator.md`](./chain-descent-calculator.md) §7 —
> the first known graph family on which chain descent's flagged region
> exceeds the abelian / cascading union.

---

## 2. Background and motivation

The chain-descent canonizer reduces canonization to one operation per
descent node (the **oracle**, [calculator §1](./chain-descent-calculator.md)),
and pins all its remaining difficulty to one structural theorem (**T-C**,
[calculator §4](./chain-descent-calculator.md)): polynomial work per node.

T-C splits into two cases by the cell shape:

- **True-symmetry cells** (the cell is one orbit). Handled by the
  cascade oracle ([calculator §5](./chain-descent-calculator.md)),
  whose correctness reduces to orbit recovery — settled for CFI
  graphs (Tier 1) and schurian scheme graphs (Tier 2) in
  [`chain-descent-orbit-recovery.md`](./chain-descent-orbit-recovery.md).
- **False-symmetry cells** (the cell splits into ≥ 2 orbits, a
  *genuine decision*). Handled by the linear oracle
  ([calculator §6](./chain-descent-calculator.md),
  [linear-oracle.md](./chain-descent-linear-oracle.md)) when the
  decision's residual symmetry is `Z_2` (a unique candidate twist).
  **Built and validated 2026-05-28** — collapses every all-singleton
  footprint, correctness-preserving through CFI(K7). Measured to be
  *starved* by the a-posteriori cascade oracle (see "remaining gap"
  below), not weak.

The remaining gap, on either side:

- **Within Tier 1+2:** orbit recovery is settled for individual
  classes (CFI, schurian schemes), but not yet for arbitrary
  cascade-class graphs (Tier 3 of orbit recovery, conjectural). The
  *a-priori* cascade oracle — certify one rep per orbit before
  branching — is **built** (C#, 2026-05-28); it eliminated the
  linear-oracle starvation, collapsing every measured CFI base
  (K4…K7) to a single path, maxRecDepth ≈ tw(H)
  ([cascade-oracle §10](./chain-descent-cascade-oracle.md),
  [calculator §9 item 4](./chain-descent-calculator.md)). The binding
  constraint is now the *Lean discharge of its contract* and
  general-class (Tier-3) completeness, not the implementation.
- **Within the linear oracle:** the abelian case is built (all-
  singleton footprints); the *non-abelian* case (the genuine wall,
  hidden Johnson) is open.
- **Between them:** even if both oracles work on their respective
  case classes, a layered graph (Tier-1-cascade composed with
  abelian residue) needs the two oracles to compose cleanly. This is
  the **composition theorem** (§7 below).

Tier 3 of this doc is the *combined* theorem: cascade + linear
together resolve every obstruction, and the layered composition is
sound.

### 2.1 Why decomposability is the natural attack

The calculator's construction question ([§7](./chain-descent-calculator.md))
is already phrased as decomposability:

> Target: prove every obstruction the descent produces decomposes as
> `(resistant-abelian) ⋊ (cascading)` — or find a counterexample.

The matroid memo independently arrived at the same shape ([§8.4](./Archive/ChainDescent/chain-descent-matroid.md)):

> Tier-2 detection (if it exists at all) lives at a different layer —
> either the linear oracle (which makes the structure F_2-explicit) or
> one of the other attack routes.

The "different layer" is precisely the layered oracle structure of
this plan. The hidden-Johnson near-theorem
([`chain-descent-hidden-johnson.md`](./chain-descent-hidden-johnson.md)
§6) sharpens this further: any genuine wall *must* be encoded — naive
hidden Johnsons (visible group acting on visible vertices) are killed
by Pieces A + B.

All four prior workstreams converge on the same shape:

| Source | Form of the Tier-3 claim |
|---|---|
| Calculator §7 | "every obstruction decomposes as (resistant-abelian) ⋊ (cascading)" |
| Matroid §8.4 | "Tier-2 detection lives at the linear oracle / orbit-recovery layer" |
| Hidden-Johnson §6 | "any genuine hidden Johnson must be encoded, not naive" |
| Orbit-recovery §4 | "Tier 3 = cascade class, conjectural" |

This plan reframes the four as a single layered-oracle composition
theorem with three sub-claims (§5–§7).

---

## 3. Setup and notation

**Layered oracle.** Two oracles wired in sequence at every descent
node:

1. **Cascade oracle** — for true-symmetry cells. Returns a single
   representative if the cell is one orbit (certified via orbit
   recovery: Tier 1, Tier 2, or future Tier 3a — see §10).
2. **Linear oracle** — for genuine decisions. Reads a candidate twist
   `t` off one branch's reverse-symmetric propagation pattern, verifies
   `t` edge-by-edge, and uses it to prune the mirror branches. Returns
   one representative per *coupled component* of decisions.

A **layered run** of the descent calls the cascade oracle first; if it
defers (cell is not one orbit), the linear oracle takes over for the
genuine-decision cell.

**Coupled component.** A maximal set of cells whose order labels swap
together under a single genuine decision's two directions
([strategy §12](./chain-descent-strategy.md)). The reverse-symmetric
propagation argument (`warm_6_2`, proved) makes this well-defined.

**Commit set.** The set of pair-guesses committed up to a given
descent node. The propagation closure of a commit set is the substrate
underlying the linear oracle's twist-discovery
([matroid §2](./Archive/ChainDescent/chain-descent-matroid.md)).

**Residual symmetry at a node.** `Aut_desc(G)` is the subgroup of
`Aut(G)` consistent with the descent path so far. It shrinks as the
descent commits more pair-guesses; the cascade oracle and linear oracle
quotient it down level by level.

**Cascade class.** Graphs for which 1-WL refinement, after polynomial-
many fresh-colour individualizations chosen by the canonical chain-
descent picker, recovers `Aut_S`-orbits. Tier 1 (CFI) and Tier 2
(schurian schemes) are the two settled subclasses; Tier 3a (nested
constructions) is the natural extension; the *general* cascade class
is Tier 3-conjectural.

**Abelian residue.** A descent commit set is **abelian** if every
coupled component admits a unique candidate twist (the linear oracle's
boundary, [calculator §6](./chain-descent-calculator.md)). Then the
twists generate a `Z_2^d` subgroup of `Aut(G)`.

---

## 4. The three sub-claims

Theorem 3 splits into three sub-claims, each independently scopable:

| § | Sub-claim | Difficulty | Risk |
|---|---|---|---|
| 5 | **Abelian-stripping.** Every commit set produces either a unique candidate twist per coupled component, or a non-abelian residual (the wall). | Tractable — refines calculator §6's specification | Low — mostly bookkeeping over linear oracle's existing spec |
| 6 | **Residual cascade.** After the abelian layer is stripped, the residual graph (the quotient by the discovered `Z_2^d`) is in the cascade class. | Hard — the load-bearing claim | High — this is where a counterexample would land |
| 7 | **Layered composition.** The cascade and abelian oracles compose soundly under any call order, because the cascade oracle's failure mode is a polynomial-time *degenerate* output (every vertex its own orbit) rather than a flag, so the algorithm can alternate freely. | Low — reduces to cascade oracle's polynomial graceful degradation | Low — the alternation is incidental, not load-bearing |

Sub-claim 2 is the genuine open content. Sub-claims 1 and 3 are
finite-effort consolidation of existing pieces.

---

## 5. Sub-claim 1 — Abelian-stripping

**Statement.** For every commit set `S` at a descent node of `G`, and
every coupled component `K` produced by extending `S` with one further
guess, exactly one of:

- **(a)** `K` admits a unique candidate twist `t_K : V(G) → V(G)`
  reading off the reverse-symmetric pattern of one branch's
  propagation. Then `t_K ∈ Aut(G)` is verifiable in polynomial time;
  iterated over coupled components, the discovered twists generate a
  `Z_2^d` subgroup `N ≤ Aut_desc(G)`.
- **(b)** `K` admits ≥ 2 candidate twists. Then `K` carries a
  non-abelian residual on its cell, and the descent flags.

**Proof shape.** This is the formal version of calculator §6's
boundary statement. The content already exists in spec form; the work
is to (i) make "unique candidate twist" a precise local condition on
the propagation pattern, (ii) state the polynomial-time verifiability
bound (edge-by-edge check, `O(n^2)` per twist), (iii) argue that
distinct coupled components contribute independent `Z_2` generators
(uses `warm_6_2`'s direction-symmetry).

**Lean cost.** Most of the machinery is in place: `warm_6_2`,
`warmRefine_agree_off'`, the descent spine. New content is the
predicate `UniqueCandidateTwist S K t` and the discovery procedure as a
total function under the unique-candidate hypothesis. Estimated 1-2k
lines once paper-rigorous.

**Risk.** Low. The uniqueness boundary is the same one calculator §6
already names; this sub-claim just makes it a theorem rather than a
spec. The main hazard is bookkeeping: delineating each coupled
component cleanly from the refinement footprint (the parent↔child
partition diff — *not* TC provenance, which is inert for the
within-cell cascade; see
[`chain-descent-linear-oracle.md`](./chain-descent-linear-oracle.md) §3).

---

## 6. Sub-claim 2 — Residual cascade

**Statement.** Let `N ≤ Aut_desc(G)` be the abelian layer discovered by
sub-claim 1 across all commit sets reachable from the root. Let `G/N`
be the quotient graph (vertices = `N`-orbits, edges induced by `G`'s
edge set). Then `G/N` is in the cascade class — orbit recovery on
`G/N` happens at polynomial depth.

**Why this is the load-bearing claim.** This is the assertion that
"after stripping the abelian gauge, what's left is something the
cascade oracle can handle." It rules out the hidden-Johnson
construction question: a graph whose quotient by every discoverable
abelian layer is itself non-cascade.

**Proof shape (target).** Three potential routes, each open:

1. **Direct route.** Show `G/N` always falls into Tier 1, Tier 2, or a
   nested combination (Tier 3a). This needs a *structural*
   characterization of `G/N` — what kinds of graphs can arise from
   abelian-quotient of an arbitrary connected graph? Possibly tractable
   for `N = Z_2^d` because the quotient has a specific shape (the
   "double-cover-quotient" structure of CFI-like constructions).
2. **Inductive route on construction depth.** If `G` is `L`-constructible
   for some construction language `L` of polynomial depth, induct: each
   `L`-layer adds either a cascade-detectable layer (handled by Tier
   1+2) or an abelian-detectable layer (handled by §5). Requires a
   constructive characterization of all connected graphs in `L` — see
   §8 for the visibility framing that targets exactly this.
3. **Dual / counterexample route.** Search for a hidden Johnson by
   parametrically constructing candidate graphs from known
   non-abelian-simple actions on encoded vertex sets. Either find a
   `G/N` outside the cascade class (counterexample, refutes Theorem 3)
   or accumulate evidence that none exists.

**Risk.** High. This is the calc-§7 / matroid-§8.4 / hidden-Johnson-§6
content — the genuine open mathematics. The decomposability framing
does not bypass it; it scopes it.

**Where the risk concentrates.** The hard case is graphs `G` where:

- 1-WL fails to recover orbits even after `n` individualizations
  (rules out Tier 1+2),
- the linear oracle discovers no twist (rules out §5 falling into
  case (a)), and
- the residual `G/N = G` (the abelian layer is trivial).

Such a `G` would have its full `Aut_desc(G)` outside both the
abelian-detectable and cascade-detectable classes — the hidden Johnson.
Babai's framework constructs such obstructions implicitly via Local
Certificates; sub-claim 2 says no graph-isomorphism instance produces
them.

---

## 7. Sub-claim 3 — Layered composition

**Statement.** The cascade and linear oracles compose soundly under
any call order. Specifically: the cascade oracle's failure mode is a
polynomial-time *degenerate* output (return every target-cell vertex
as its own orbit — sound but loose), not a flag. So the descent can
freely alternate cascade-then-linear-then-cascade-…, terminating
either when the cascade oracle returns a non-degenerate answer (true
symmetry detected and pruned) or when both oracles produce no progress
(flag).

**Why composition is automatic, not load-bearing.** The earlier draft
of this sub-claim treated composition as a "clean interleaving"
guarantee requiring its own spine-commutation proof. That was
over-engineered. The cascade oracle's spec
([calculator §5](./chain-descent-calculator.md)) already permits
"return all target-cell vertices" as a safe degenerate output — the
harness then proceeds as budget-bounded IR search, which is correct,
just slow. So the layered algorithm needs no claim about *whether*
cascade-then-linear and linear-then-cascade produce equivalent
outputs; both orderings are individually sound, and the algorithm
picks whichever oracle has progress to report next.

**The sub-claim reduces to:**

1. **Cascade oracle terminates polynomially in failure**, returning a
   sound degenerate output. Already true of the shipped
   `CascadeOracle.cs` ([calculator §5, Phase-1 status](./chain-descent-calculator.md)) —
   it certifies nothing a priori and returns every target-cell vertex,
   the textbook degenerate output.
2. **Linear oracle terminates polynomially**, either returning a
   verified twist (one branch's pattern → candidate → edge-check) or
   reporting "no unique candidate" (flag).
3. **The two failure modes are disjoint** at any node: if cascade
   returns non-degenerate, linear is not called; if linear returns a
   twist, the cascade oracle re-runs on the next level's cell with
   `N`-quotiented inputs. So sequential calls always make progress or
   honestly flag.

**Conjecturally stronger but not required.** It is likely *also* true
that the alternation pattern is *guaranteed* in a specific sense — the
spine machinery ([strategy §12](./chain-descent-strategy.md)) gives a
direction-blind partition, so cascade calls before vs. after a linear
commit see the same cells. If proved, this would imply the two
orderings always *agree* on output, not just both *succeed*. Worth
recording as a sub-conjecture:

> **Sub-conjecture 3' (commutation, optional).** For any descent node,
> running cascade-then-linear and linear-then-cascade produces the
> same residual symmetry.

This is not needed for the algorithm's correctness or polynomial-or-
flag bound; it is a structural fact about the layered oracle's call
graph and may have independent value (e.g. for the linear oracle's
coupled-component delineation).

**Risk.** Low. (1) holds in the shipped code; (2) is part of the
linear oracle's spec; (3) follows from (1) + (2) by case analysis on
which oracle returned non-degenerate at the current node. The optional
sub-conjecture 3' adds zero risk to the main result.

---

## 8. Alternate framing — visibility / no-hidden-symmetry

**The framing.** A symmetry cannot hide itself. Every support
structure (encoding gadget) layers over existing pieces, leaving at
least one visible piece. So a graph's non-trivial automorphisms must
trace, by induction on construction, back to either an atomic
symmetric primitive or a visible attachment of a constructed layer.

**Equivalence to GI ∈ P.** As [calculator §7](./chain-descent-calculator.md)
warns: "the descent detects every automorphism, so nothing can be
hidden" — assuming this is the conclusion, not the hypothesis. The
visibility framing is equivalent in strength to GI ∈ P, just like the
decomposability framing of §1.

**Why include it.** The two framings have different shapes, and a
proof attempt on one can illuminate gaps in the other. Specifically:

- **Decomposability (§1–§7)** is *post hoc*: given a graph, decompose
  its automorphism group.
- **Visibility (§8)** is *constructive*: given a construction
  language, induct on construction.

The complementary use the user proposes:

> If at some point we are able to define what causes a cascade layer
> or what causes a hidden symmetry, then this gives us a way to
> invert the question and say "This does not provide a way to form a
> hidden Johnson, so there must be none."

This is the **inversion strategy**. Decomposability (§6) asks "does
every `G` admit the decomposition?"; visibility inverts: "does any
construction or hiding mechanism produce a non-decomposable `G`?"

Two concrete inversion routes are available, listed in order of how
naturally they extend the existing project:

- **§8.1 — Cascade-theorem self-undermining** (the user's preferred
  route). Cascade theorems characterize what *enables* a symmetry to
  be obscured. If every hiding mechanism requires structure that is
  itself detected by the same cascade theorems, hiding bootstraps
  into self-detection.
- **§8.2 — Construction-language enumeration** (the catalogue route).
  Pick a construction language `L`; show every `L`-construction either
  cascades or produces only abelian residue; conclude no `L`-graph is
  hidden-Johnson.

The user's preferred route (§8.1) does not require defining a
construction language — it operates at the cascade-theorem level and
self-bootstraps. The catalogue route (§8.2) is straightforward but
risks being unboundedly large.

### 8.1 Cascade-theorem self-undermining inversion

**The shape of the argument.** Suppose the cascade analysis (Tier 1,
Tier 2, and any successors) produces theorems of the form:

> *Obscuring theorem.* A symmetry `H ≤ Aut(G)` can be hidden from
> 1-WL only in the presence of structure `S(H)` — typically a higher-
> order symmetry, a coupled-component pattern, or a particular
> construction constraint.

Then the inversion: to hide a hidden Johnson `J ≤ Aut(G)`, the graph
must carry the obscuring structure `S(J)`. But `S(J)` is itself a
detectable structure — by the *same* cascade theorems, applied at the
level of `S(J)` rather than `J`. So detecting `S(J)` exposes `J`. The
hiding mechanism is self-undermining: it cannot conceal both `J` and
`S(J)` simultaneously.

**Why this might work where matroid detection didn't.** The matroid
memo ([§7](./Archive/ChainDescent/chain-descent-matroid.md)) tried to detect Tier-2
structure by binary-vs-non-binary classification of a *single closure
operator*. That failed because the closure operator was not a
matroid. The self-undermining argument doesn't classify a fixed
operator — it bootstraps off the existence of cascade theorems
themselves, regardless of whether they describe a matroid. As long
as the theorems describe *some* structure `S(H)` that's needed for
hiding, the inversion runs.

**Sketch of the cascade theorems that would enable this.** None of
these are proved; they are the *shape* of theorems Tier 1/2/3a work
is likely to produce as it deepens:

- **(O1)** "A non-abelian simple group `H ≤ Aut(G)` is obscured from
  1-WL only if `G` contains a coupled-component cluster of cycle
  rank `≥ |H|`." *(Plausible from Tier-1 CFI cycle-space theory.)*
- **(O2)** "An `A_k` action is obscured only if the obscuring layer
  itself supports an `S_m` permutation for some `m ≥ k`." *(Plausible
  from the orbital-structure argument of Pieces A+B.)*
- **(O3)** "Hiding `k`-set structure requires the host graph to
  realize a coherent algebra of rank `≥ k`." *(Plausible from
  Tier-2 scheme theory.)*

Any single theorem of this shape, *combined with the observation that
the obscuring structure is itself in the cascade class*, gives the
inversion. The §8.1 attack does not require knowing the obscuring
structure's specific form — it requires showing that *whatever it is*,
it must itself be cascade-detectable.

**Concrete sub-target.** A theorem-shape worth aiming for, in
decreasing strength:

> **(O*) Self-detection lemma.** For every non-abelian-simple
> `H ≤ Aut(G)`, the obscuring structure `S(H)` is itself a schurian
> association scheme on the obscured vertex set. By Tier 2, 1-WL
> recovers `S(H)`-classes at depth 1; by reading `S(H)` off the
> 1-WL output, `H` is reconstructed.

If (O*) holds, hidden Johnsons are ruled out by Tier-2 detection of
the obscuring scheme — *without* defining a construction language and
*without* solving sub-claim 2 directly. This is the cleanest version
of the user's "dual route."

**Why we don't have (O*) yet.** Tier-2 covers *visible* scheme graphs,
not arbitrary obscuring schemes. (O*) would require showing that the
obscuring structure is *itself* visible as a scheme on the obscured
vertex set — a meta-statement about Tier-2's applicability. Currently
the project has the components (Tier-2 detection mechanism, scheme
theory) but not the bridge.

**The route's value, even partially.** Even a *weaker* (O1)- or
(O2)-shaped theorem narrows the search for hidden-Johnson
counterexamples to graphs satisfying the obscuring-structure
constraint. This is publishable independently — "any hidden Johnson
must have such-and-such structural fingerprint" is a contribution
even without closing the construction question.

**Operational form.** (O\*) / "residue is rigid" is realized as an
*algorithm* by the deferred-decision workflow
([`chain-descent-deferred-decisions.md`](./chain-descent-deferred-decisions.md)):
consume all symmetry first (deferring real decisions), and the clean
two-phase form — polynomial oracle phase + oracle-free rigid residue —
holds *iff* all symmetry is unconditional, which is exactly (O\*). That
doc reframes the open content as the sharper sub-question "which
symmetry is conditional on a non-symmetric choice?"

### 8.2 Construction language scoping

This is the secondary inversion route — a fallback if the §8.1
self-undermining argument doesn't produce a clean theorem. The
catalogue route requires defining a construction language `L` and
proving each operator preserves decomposability. **Risk:** `L` may not
be of tractable size — if "every known graph type" demands its own
theorem, the catalogue degenerates into an enumeration without closing
the open case. The route is most attractive when `L` is small (a few
operators) and each operator's contribution is structurally
characterizable.

Concrete candidates, in increasing scope:

- **`L_CFI` — iterated CFI only.** Atomic: any base graph `H` with
  `tw(H) ≤ k` for fixed `k`. Operator: `CFI`. Bounded depth.
  *Visibility for `L_CFI` is Tier 3a (§10).*
- **`L_scheme` — iterated schemes.** Atomic: any vertex-transitive
  schurian scheme. Operators: scheme products, blow-ups.
  *Visibility for `L_scheme` extends Tier 2 to nested schemes.*
- **`L_layered` — `L_CFI` + `L_scheme` + abelian products.**
  *Visibility for `L_layered` is the natural target for sub-claim 2.*
- **`L_full` — every connected graph is in `L`.**
  *Visibility for `L_full` is full GI ∈ P.*

`L_layered` is the right target for the Tier-3 paper: it covers every
known hidden-Johnson candidate construction (because every known
candidate is layered) without claiming universality. A Tier-3 paper
proving visibility for `L_layered` would:

- formally close the calculator §7 construction question for layered
  graphs (Babai's quasipolynomial bound becomes polynomial in this
  case);
- give a constructive Tier-3 oracle that recurses through layers;
- leave `L_full` as the residual open problem (any graph not in
  `L_layered` would be a counterexample, and would not match any
  known construction).

### 8.3 Where decomposability and visibility meet

The two framings agree on the following equivalence:

> Decomposability holds for the class of `L`-constructible graphs
> **if and only if** visibility holds for `L`.

The "only if" direction is immediate: if every `L`-constructible graph
decomposes, then by induction on `L`-construction, every layer's
contribution is detectable, hence visible.

The "if" direction is the inversion: visibility for `L` means each
`L`-layer's symmetry contribution has a constructive witness, which is
exactly the layered oracle's input.

So the two framings are duals at the class level. The choice between
them is about *which direction the inductive argument runs*:

- **Decomposability inducts on the obstruction structure.** Bottom-up
  from `Aut(G)` to layers.
- **Visibility inducts on the construction structure.** Top-down from
  primitives to the constructed graph.

The recommended use in this Tier-3 plan is to **lead with
decomposability** (§1–§7) and use visibility (§8) **as a fallback** when
a decomposability sub-claim resists direct attack — particularly
sub-claim 2, which is the only one with genuine open content.

---

## 9. Risks and counterexample value

### 9.1 Where each sub-claim could fail

| Sub-claim | Failure mode | What the failure tells us |
|---|---|---|
| §5 (abelian-stripping) | A coupled component admits ≥ 2 candidate twists yet linear oracle returns one. | Spec bug in calculator §6 — fixable. |
| §6 (residual cascade) | A `G/N` outside the cascade class. | Genuine hidden Johnson — refutes Theorem 3, publishable counterexample. |
| §7 (layered composition) | Cascade oracle creates cells that the linear oracle was about to discover. | Composition bug — fixable by re-ordering or by sharpening the spine commutation lemma. |

Only §6 carries open mathematical risk. §5 and §7 are engineering /
proof bookkeeping.

### 9.2 The value of a counterexample

A counterexample to sub-claim 2 — a graph whose every layered
quotient remains non-cascade — would be the first explicit
hidden-Johnson construction. This would:

- close the construction question of calculator §7 in the *negative*
  direction;
- be a graph-family contribution alongside Cai-Fürer-Immerman's CFI
  family (which solved the "lower bound for k-WL" problem);
- delimit precisely where Babai's quasipolynomial bound is necessary.

The counterexample search is itself a research program. If decomposability
proves elusive, swapping to a focused counterexample search (via §8's
inversion strategy) is the productive move.

---

## 10. Relationship to existing work

### 10.1 Building blocks

| Piece | Status | Role in Tier 3 |
|---|---|---|
| Tier 1 (CFI cascade) | Proved, axiom-free in Lean for OddDegree | Base case for §6 (CFI residues are cascade-class) |
| Tier 2 (schurian schemes) | Proved for rank ≤ 2 + |J| ≤ 1 in Lean; paper-rigorous in general | Base case for §6 (scheme residues are cascade-class) |
| Linear oracle (calc §6) | Built + validated through CFI(K7) 2026-05-28 | The abelian-stripping mechanism of §5 |
| A-priori cascade oracle (calc §5) | Built 2026-05-28 — eliminated linear-oracle starvation; CFI(K4…K7) collapse to a single path. Binding constraint is now the Lean discharge + Tier-3 completeness | Feeds clean footprints to the linear oracle; path to polynomial CFI |
| Construction question (calc §7) | Open | Dual form of Theorem 3 |
| Hidden-Johnson Pieces A+B | Proved | Rules out naive (visible-action) counterexamples to §6 |
| `warm_6_2`, descent spine | Proved | Composition machinery for §7 |
| Matroid framework | Closed (not a matroid) | Negative result; informs §8.3's class-level equivalence |

### 10.2 Tier 3a as a stepping stone

Tier 3a is a natural sub-target that doesn't require resolving the
full Tier-3 difficulty. Plan written as
[`chain-descent-tier3a-cascade-composition.md`](./chain-descent-tier3a-cascade-composition.md);
the headline:

- **Theorem 3a (cascade composition).** If `Aut(G)` admits a normal
  chain `H_0 ⊵ … ⊵ H_k = {1}` where each successive quotient is in a
  known cascade class with depth bound `f_i`, then `G`'s cascade
  depth is at most `Σ f_i`.

This is a strict generalization of Tier 1 (CFI, `k = 1`) and Tier 2
(scheme, `k = 1`, `f = 1`) to compositions — CFI∘CFI, CFI∘Scheme,
Scheme∘CFI (where well-defined), Scheme∘Scheme, and iterated
combinations. The proof is monotonicity of 1-WL in the
individualization set (`warmRefine_refines`, proved) plus induction
on chain length. Estimated paper effort: small (the inductive step is
routine); Lean effort: ~1500-3000 lines of composition framework
on top of existing Tier 1 + Tier 2.

Tier 3a is **paper-tractable** and **forward-compatible** — any
future cascade class (Hamming, distance-regular extensions, higher-
rank schemes) automatically slots in as a one-layer instance without
re-proving composition. Recommended first concrete deliverable while
the main Tier-3 plan matures.

### 10.3 Babai connection

Babai's algorithm achieves quasipolynomial GI via a recursive
"Local Certificates" framework that conceptually matches the
visibility / decomposability shape: discover automorphism witnesses
locally, recurse on the residue. The bound is `2^O(log³n)` rather
than polynomial because the recursion depth is `O(log n)` and each
level has `O(log² n)` candidates.

Tier 3's polynomial bound (if proved) would require the recursion
depth to be `O(log n)` and the per-level work to be `O(poly(log n))`,
*or* a different attack that bypasses the local-certificate
combinatorics entirely. The decomposability framing offers the second
route: by reducing to two oracle calls per layer (cascade + linear),
the per-layer work is polynomial, and the layer count is bounded by
the construction depth.

If `L_layered`-construction depth is polynomial in `n` for every
graph (the visibility conjecture for `L_layered`), then Tier 3
delivers polynomial-time GI. If not, Tier 3 delivers polynomial-time
GI on the `L_layered` class and Babai's quasipolynomial bound remains
the best general result.

---

## 11. Lean path

**Paper-first, then Lean.** The paper draft of Theorem 3 should be
complete and reviewed before any Lean work begins. Reason: sub-claim 2
has high mathematical risk, and Lean effort spent on a wrong proof
sketch is wasted.

**Lean order, once paper-rigorous:**

1. **Sub-claim 1 (abelian-stripping)** is the natural first Lean
   target — uses existing infrastructure (`warm_6_2`, descent spine)
   and produces concrete generators. Estimated 1-2k lines.
2. **Tier 3a (CFI-tower cascade)** can land in parallel as a
   strengthening of Tier 1's `theorem_1_HOR_cfi_oddDeg`. Reuses CFI
   infrastructure (`ChainDescent/CFI.lean`). Estimated 1-2k lines.
3. **Sub-claim 3 (composition)** depends on §1's linear-oracle
   formal object existing. Estimated 500-1000 lines once §1 lands.
4. **Sub-claim 2 (residual cascade)** — only after paper-rigorous.
   Estimated 3-5k lines plus whatever scheme-class infrastructure
   the paper proof requires (likely several hundred lines of new
   association-scheme / quotient machinery).

**Total Lean budget for full Tier 3:** ~6-10k lines on top of the
existing ~7k lines of Tier 1+2 + ChainDescent foundations. This is a
multi-month project even after the paper is settled.

---

## 12. What's settled, what's next, and what's risky

### 12.1 Settled (going into Tier 3)

- Tier 1 (CFI cascade): axiom-free in Lean for OddDegree, paper-rigorous
  in general.
- Tier 2 (schurian schemes): proved in Lean for `rank ≤ 2 ∧ |J| ≤ 1`,
  paper-rigorous in general.
- `warm_6_2`, descent spine, propagation substrate: proved in Lean.
- Hidden-Johnson Pieces A+B: proved (naive hidden Johnson ruled out).
- Matroid framework on commit-set closures: closed (not a matroid).
- The construction question (calc §7) and the visibility framing (§8)
  are dual statements of the same Tier-3 difficulty.

### 12.2 Next (paper-first plan order)

1. **Sub-claim 1 paper draft.** Formal statement of the unique-twist
   boundary, linked to calculator §6's spec. Tractable; primarily
   bookkeeping.
2. **Tier 3a paper draft.** CFI-tower cascade. Independent of sub-claim
   6; doable now.
3. **Sub-claim 3 paper draft.** Composition theorem. Reduces to existing
   lemmas + a new commutation statement.
4. **Sub-claim 2 paper draft (the hard one).** Attempt direct route
   (§6 route 1) first; pivot to inductive (§6 route 2) if it resists;
   pivot to counterexample search (§6 route 3) if both resist.
5. **§8 visibility framing** as a parallel scratchpad — record any
   inversion arguments that suggest counterexamples, and use them to
   stress-test the decomposability route.
6. **Lean phase** — only after the paper is rigorous and reviewed.

### 12.3 Risky

- **Sub-claim 2** is the only sub-claim with genuine open content.
  Its three potential routes (direct / inductive / counterexample)
  are all unscoped.
- **The construction language `L_layered`** is not yet rigorously
  defined. Operator catalogue and closure under composition both need
  paper-rigorous treatment.
- **GI ∈ P equivalence** means a successful Tier 3 proof is a major
  result; a failed Tier 3 attempt could still yield Tier 3a (CFI
  tower) and the composition theorem as standalone contributions.

---

## 13. Cross-references

- [`chain-descent-simplified-overview.md`](./chain-descent-simplified-overview.md) —
  gentle intro to the project.
- [`chain-descent-strategy.md`](./chain-descent-strategy.md) §15 —
  algorithm-level gaps including the flagged-region scope.
- [`chain-descent-calculator.md`](./chain-descent-calculator.md) §6 —
  linear oracle (sub-claim 1's mechanism); §7 — construction question
  (Theorem 3's dual).
- [`chain-descent-orbit-recovery.md`](./chain-descent-orbit-recovery.md) —
  Tier 1 (CFI) and Tier 2 (schemes) base cases for sub-claim 2.
- [`chain-descent-hidden-johnson.md`](./chain-descent-hidden-johnson.md) §6 —
  naive hidden Johnson killed; encoded case is sub-claim 2's open
  content.
- [`chain-descent-matroid.md`](./Archive/ChainDescent/chain-descent-matroid.md) §7, §8.4 —
  intended Tier-2 detector (failed) and the verdict that detection
  must live at the layered-oracle level.
- [`chain-descent-tier2-decomposition-experiment.md`](./Archive/ChainDescent/chain-descent-tier2-decomposition-experiment.md) —
  empirical confirmation that CFI ladder is Tier 1; baseline data for
  Tier 3a.
- [`chain-descent-tier3a-cascade-composition.md`](./chain-descent-tier3a-cascade-composition.md) —
  the Tier 3a paper plan (Theorem 3a, cascade composition).
