# Theorem-index maintenance

How to regenerate the four theorem-index files (`PublicTheoremIndex.md`,
`PrivateTheoremIndex.md`, and their `Archive/` counterparts) — both the routine
mechanical refresh and the heavier **description-rewrite + privatization** pass.

The generator is [`GenerateTheoremIndexes.py`](./GenerateTheoremIndexes.py); read its
module docstring for the column model. This file documents the *human/agent* process
on top of it — written after the 2026-05-31 full rewrite so it can be redone, most
likely for just a handful of entries.

---

## 0. The two columns, and who owns them

| Column | Owner | How |
|--------|-------|-----|
| **Name** | script | from source (qualified, displayed `ChainDescent.`-stripped) |
| **Line** | script | `--with-line-numbers`; header+body source range |
| **Notes** | script | computed: infra-kind + `noncomputable` + `@[…]` tags (`private` omitted) |
| **Description** | **human/agent** | hand-written, preserved across regens; bulk-applied via `--descriptions` |

Public-vs-private split is driven entirely by the `private` keyword in the Lean source
(the script routes the row to the matching index file).

Prose between tables (per-file blurbs, `### …` sub-headers, the Legend, the intro note)
is **passed through verbatim** and never moved between files — edit it directly in the
markdown; the script won't touch it.

---

## 1. Routine refresh (after any source edit)

```bash
python3 scripts/GenerateTheoremIndexes.py rewrite --with-line-numbers
```

Refreshes Line + Notes, discovers new decls (adds rows, creating `## <path>` sections as
needed), and migrates rows between public/private/active/archive as their source status
changes. Existing Descriptions are preserved. Then sanity-check:

- The run prints "N tracked row(s) with no matching source decl". A small stable set of
  anonymous-instance rows (`Decidable (…)`, `Fintype …`) is expected and kept verbatim.
  Anything else is a stale row to delete by hand or a resolution bug.
- The run also prints "N newly added row(s)" with each new row's **location in the index file**
  (`PublicTheoremIndex.md:<line>  <qualified-name>`). Line + Notes are already filled; only the
  Description is owed — jump to each location and write it (or supply them via `--descriptions`,
  §2). The locations are exact for the file as just written.
- `git diff` should be row-level only (no prose +/- lines).

---

## 2. Editing a *few* descriptions (the common case)

Two equivalent options:

- **Direct:** edit the Description cell in the index markdown. It is preserved on the next
  `rewrite`. Simplest for one or two rows.
- **Via JSON** (keeps source-of-truth in one place): add entries to a JSON map and apply:
  ```bash
  echo '{"ChainDescent.foo_lemma": "§X What it achieves …"}' > /tmp/d.json
  python3 scripts/GenerateTheoremIndexes.py rewrite --with-line-numbers --descriptions /tmp/d.json
  ```
  Keys may be the qualified name (`ChainDescent.OrbitPartition.refl`), the display name
  (`OrbitPartition.refl`), or the bare last segment (`foo_lemma`) — most specific wins.
  **Use the qualified or display form for any name that collides** across namespaces/files
  (e.g. `some_isAut`, `refl`/`symm`/`trans`, `adj_symm`), or the bare key will hit the wrong
  one. The override also rewrites single-decl conceptual rows (e.g. `AutGroup adj`); combined
  `a / b` rows are left verbatim — edit those by hand.

### Description style (enforce this)
- What the declaration **achieves / why a consumer would use it** — *not* how it is proved.
  Never restate the definition as "X, by using lemmaA on lemmaB".
- ≤ 2 sentences, ideally 1 short. Near-self-explanatory name → very short is fine.
- **Prefix** with a marker that links to documentation when it adds value: the source `§…`
  section marker and/or a **bold conceptual anchor** (`**Key theorem.**`, `**Support
  backbone.**`, …). Don't invent markers absent from the source/docs.
- Backticks for Lean identifiers/expressions; use project vocabulary (Aut_S-orbit, 1-WL cell,
  individualized set, twist, …).
- Examples (good): `relOfPair` → "§1.1 The unique relation index `i : Fin (S.rank + 1)` for
  which `rel i v w = true`."; `complete_of_cellComplete_recoverable` → "**Key theorem.** At an
  orbit-recoverable node, certifying every same-cell pair already certifies every orbit …".

---

## 3. Making a declaration `private`

Criterion (conservative, err toward public): privatize a decl **only if** it is referenced
in **no other file** AND is a genuine internal helper — *not* a headline/"Key" theorem, a
contract/interface type or `Prop` predicate, a named result the docs refer to, a `@[simp]`
lemma, or a demonstrative example/refutation.

```bash
# 1. Add `private` before the decl keyword in the .lean source (after @[…]/before noncomputable).
# 2. Build-verify — a wrongly-privatized (externally-used) decl breaks here, naming itself:
bash scripts/build.sh        # serial, ~60 s in RAM; see its header for why not `lake build`
# 3. Regenerate; the decl migrates to PrivateTheoremIndex.md automatically:
python3 scripts/GenerateTheoremIndexes.py rewrite --with-line-numbers --descriptions /tmp/d.json
```
A `private` decl does not need a doc-comment noting *why* it's private; if it turns out to be
needed elsewhere, just remove `private` (always builds) and regen.

---

## 4. Full redo (all descriptions + privatization) — the 2026-05-31 pass

Done with one subagent per file (big files chunked ~60 decls each), in batches small→large
so style is validated before the large files. Pipeline:

**4.1 Cross-file usage map** (gates privatization — compute centrally; do NOT let agents grep,
the shell is zsh and unquoted `$arr` does not word-split):
```python
# parse each active file with gen.parse_lean_file; for each decl, word-boundary-search its
# bare name in every OTHER active file → external = any hit. Emit {qualified: {file,line,kind,external}}.
```
A name appearing in another file (even a comment) is treated as external ⇒ stays public
(safe over-approximation). Collisions (`refl`, `some_isAut`) are conservatively "external".

**4.2 Per-file (chunk) decl lists**: `qualified-name  kind  Lline  ext-status`, one file per agent.

**4.3 Spawn a subagent per chunk** with the prompt template in §5. It returns
`{qualified: {description, private}}`.

**4.4 Merge + validate**: union the JSONs; assert each chunk's keys exactly match its decl
list (no missing/extra). Build `all_desc.json = {qualified: description}` and a private list.

**4.5 Privatize** the flagged decls in source (§3 mechanism, applied in bulk: insert
`private ` before the keyword, skipping any already-private), then `bash scripts/build.sh`.

**4.6 Apply**: `rewrite --with-line-numbers --descriptions all_desc.json`. Verify idempotent
(run twice → no diff), public prose preserved, private index populated.

**4.7 Headers/legend**: edit the four preambles by hand if the column semantics changed
(they are prose, preserved by the script). Keep `default_preamble` in the script in sync.

Residuals from the 2026-05-31 pass: combined `a / b` conceptual rows kept their prior
descriptions; the Archive indexes were active-only for descriptions (their Notes/Lines still
refresh on every regen).

---

## 5. Subagent prompt template (§4.3)

Fill in `<FILE>`, `<CHUNK-FILE>`, `<LINE-RANGE>`, `<FILE-CONTEXT>`.

```
You are writing one-line index descriptions for a chunk of Lean declarations in a
graph-canonization proof project, and judging which should be `private`.

## Your chunk
- Decl list: run `cat <CHUNK-FILE>` — TAB-separated `qualified-name  kind  Lline  ext-status`.
  Produce output for EXACTLY these decls.
- Source: `<FILE>`, lines ~<LINE-RANGE> (read that region — statements, `/-! ## §… -/`
  section headers, doc-comments).
- Current index descriptions to TIGHTEN/improve: the matching `## <FILE>` section of
  GraphCanonizationProofs/PublicTheoremIndex.md.
- File context: <FILE-CONTEXT>.

## Description style (match exactly)
- Tells a FUTURE CONSUMER what the item ACHIEVES / why they'd use it — NOT how it's proved
  internally. Never "X, by using lemmaA on lemmaB".
- ≤2 sentences, ideally 1 short. Near-self-explanatory name → very short is fine.
- Prefix with markers that connect to documentation when they add value: the source `§…`
  marker and/or a bold conceptual anchor (**Key theorem.**, **Support backbone.**, …).
  Don't invent markers absent from the source.
- No Notes value (auto-computed). Backticks for Lean identifiers.
Calibration examples:
- `relOfPair`: "§1.1 The unique relation index `i : Fin (S.rank + 1)` for which `rel i v w = true`."
- `complete_of_cellComplete_recoverable`: "**Key theorem.** At an orbit-recoverable node,
  certifying every same-cell pair already certifies every orbit — reducing orbit-completeness
  to a polynomial check."

## Privatization
For each `zero-ext` decl (referenced in NO other file), set `private`:
- `private: true` ONLY if a genuine internal helper / stepping-stone, unlikely to EVER be
  cited outside this file, and not demonstrative in itself.
- `private: false` (keep public) for headline/"Key" theorems, contract/interface types or
  `Prop` predicates, core vocabulary, `@[simp]` lemmas, and demonstrative results/examples.
  ERR TOWARD PUBLIC.
- `EXT` decls → always `private: false`.

## Output
Return ONLY one fenced ```json block: keys = EXACT qualified names from the chunk file,
values = `{"description": "<text>", "private": <true|false>}`. Every decl, no extras, no
prose outside the block.
```

---

## 6. Gotchas

- **zsh word-splitting**: `grep PATTERN $files` with an unquoted space-string passes one bad
  arg. Use a zsh array `files=(a b c)` then `grep PATTERN $files`.
- **Name collisions**: the parser keys by qualified name; rows resolve by suffix + section
  path + Line-hint. A bare-name display row for a colliding name relies on the Line-hint to
  pick the right decl — keep the index Line column current.
- **Combined `a / b` rows** are kept verbatim by `--descriptions`; rewrite them by hand.
- **Build time is RAM-bound** — use `scripts/build.sh` (serial), not `lake build` (parallel
  → swap thrash on this box). See that script's header.
