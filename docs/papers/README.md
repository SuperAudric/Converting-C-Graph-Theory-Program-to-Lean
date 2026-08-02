# docs/papers — version-controlled paper extracts

Cleaned plain-text extractions of the papers the general-CC separability build
(`docs/chain-descent-general-cc-separability.md`) consumes. These are the durable copies —
`/tmp` extracts do not survive a reboot, and a session without network cannot re-fetch.

| File | Paper | Used for |
|---|---|---|
| `p4paper-arxiv-2006.13592.txt` | Ponomarenko, *On the separability of cyclotomic schemes over finite field*, arXiv:2006.13592 | **Thm 4.1** (the general sufficient condition, §4), **Lemma 2.6** (one-pt-extension separable ⟹ 2-separable), the m-extension (§2), Thm 1.1/1.2 (cyclotomic, the cited affine slice) |
| `cartan-arxiv-1602.07132.txt` | Ponomarenko–Vasil'ev, *Cartan coherent configurations*, arXiv:1602.07132 | **Thm 3.1** (the sparse condition — already formalised, `Separability.lean`), **Thm 2.5** (1-regular `(m−1)`-point extension ⟹ `m`-separable), base defs (§2.2) |

Both files have already been run through `python3 scripts/clean-extracted-text.py`
(NUL bytes stripped, ligatures NFKC-normalised) — plain `grep`/`rg` works on them.

**For a fresh extraction** of any other paper: `curl -sL https://arxiv.org/pdf/<id> -o /tmp/x.pdf`,
`pdf2txt /tmp/x.pdf`, then **always** `python3 scripts/clean-extracted-text.py /tmp/x.txt` before
grepping (see the GOTCHA in `chain-descent-general-cc-separability.md` §0). If it becomes
load-bearing, commit the cleaned extract here.
