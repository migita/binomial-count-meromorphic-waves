# Rewrite notes (branch `rewrite-hierarchies`, 17 Sep 2026)

Working notes for the author. Not part of the arXiv package; delete before merging.
`main` and `~/projects/KS-260829/arxiv_meromorphic_waves/` are untouched.

## Principle

Readability first. The four audited proofs (classification, weighted Bézout, prime-index theorem with the Lean remark,
elliptic count) are moved as blocks with their wording unchanged. New text goes into the front matter, the lead-ins, the
two pure subfamilies, the single-equation section and the examples. Secondary material is dropped rather than compressed.

## Section map

| New | Content | Source |
| --- | --- | --- |
| Abstract | physical hypotheses; "exceptional, so we count"; the two pure subfamilies; one status paragraph; "one pole per period" | rewritten |
| 1 Introduction | hook; family; vocabulary; Classification / The count / Pure subfamilies / A single equation / Method / Earlier work / Organization | rewritten; "Earlier work" kept almost verbatim |
| 2 Equations, waves and what is counted | reduction (2.1)–(2.4), change of background (2.5), dispersive/dissipative/mixed, reflection-symmetric P (2.6), pulses and fronts, what a pair is | new |
| 3 The classification theorem | old §2. Hypothesis stated for the evolution equation; Noether sentence; **new Corollary 3.2** (waves are symmetric about their poles) | old §2, one paragraph cut |
| 4 Three finite algebraic systems | old §3.1–3.3 and Theorem; §3.4 replaced by a short "Fixed operators" pointer | old §3, −1.3 pages |
| 5 The count of rational-exponential pairs | 5.1–5.3 verbatim (divisibility, weighted degree, prime index, Lean remark = **Remark 5.5**), pulses and fronts (Prop. 5.6), **5.4 Reflection**: Prop. 5.7, **Theorem 5.8** with new part (iv) | old §4.1–4.3 + draft |
| 6 The count of elliptic pairs | Theorem 6.1 verbatim; background involution stated with its hypothesis; **Corollary 6.2** (purely dispersive, 2F_p) | old §4.4 + draft |
| 7 Which orders are settled | status table; prime powers; certificates p ≤ 73; p = 5; order seven as a sentence | old "Further orders" |
| 8 What the count means for a single equation | Prop. 8.1, Cor. 8.2 (solvable equations), Cor. 8.3 (generic equations of even order) | draft §4.6, tightened |
| 9 Examples | summary table; 9.1 order two; 9.2 order three with the merging lattices as the showcase for multiplicity; 9.3 Kawahara and seventh-order KdV (ten pairs, two real); 9.4 order five (six fronts, four = Kudryashov–Migita 2007) | rewritten |
| 10 Open questions | rigidity, simplicity, mixed equations of odd order (Fisher) | old §6 minus the Darboux paragraph |
| A Verification | + item 4 (`anc/symmetry_checks/`) | updated |

## Dropped

- old §3.4 "Eliminating the profile coefficients" (Bernoulli constants, candidates (3.7)–(3.9), elimination remarks);
- the comparison paragraph with Yuan–Li–Qi in the classification section (the attribution stays in the introduction and in §3);
- all three figures, `figures/`, `anc/make_figures.py`;
- KdV: cnoidal formula, fixed-operator discussion, nodal and cusp limits; KS: the displays (5.8)–(5.9) (merged into the scheme, attributions kept), "no operator in the table has an elliptic solution", the vessel-model paragraph; Kawahara: the `D^4+a_0` illustration, the Jacobi-function wave, energy-level remarks;
- the Darboux-identity paragraph of the open questions (kept for the sequel);
- from the reviewed draft: the uncertified orbit numbers 17/66/236, the separate table of F_p, Corollary "order seven" as an environment.

Held for a second paper and not mentioned: the even-order landscape beyond Fisher, the twisted reflection, real counts, v^k, the Grassmannian question.

## New mathematical statements (all need the author's eye)

1. Corollary 3.2: symmetry of every meromorphic wave about its poles in the two pure subfamilies.
2. Proposition 5.7 and Theorem 5.8 (i)–(iv). Part (iv): purely dispersive ⇒ pulses (unconditional); purely dissipative ⇒ fronts when X_p is reduced, and for real pairs unconditionally (integrate the profile equation along the real axis).
3. Corollary 6.2 and the sentence on M_p/2 elliptic waves with two backgrounds (assumes X_p reduced).
4. Proposition 8.1, Corollaries 8.2, 8.3.
5. Examples: the ten pairs at p = 6 and the six at p = 5.

Review status. (a) Mathematics: the reviewing Codex session audited all of 1–5 (report:
`~/projects/KS-260829/codex_binomial_review_20260917/mathematical_audit.md`, with an independent recomputation of the p = 5 and
p = 6 lists and of the KS multiplicities). No mathematical error was found; its wording and scope findings are applied.
(b) Readability: two cold reads are integrated — Codex (`readability_review.md`, `final_pass.md`) and a fresh reader with no
knowledge of the project. From them: the normalization is explained in ordinary language before the technical list; "a single
equation" is told through scaling curves and the KdV/Burgers contrast; uniqueness is stated for a fixed operator P; "order"
always means p (stated once in the introduction) and parities are written through p; "index" is defined; multiplicity is
explained like a multiple root, and the three algebraic notions are tied to "count with multiplicity" and "distinct"; the six
classical KS cases / ten members are explained in the first paragraph; the reflection is motivated before its formulas and
Theorem 5.8 has a plain restatement; Section 7 opens with "two facts"; Section 8 avoids orbit jargon; Fisher is tied to the
profile equation of KdV–Burgers; rational waves are said not to be counted, and why.

Later cuts and moves (all reversible): the proof itinerary in the Lean remark (kept in the repository docs; the appendix still
lists the files); Systems "Fixed operators"; the order-seven paragraph; the two long remainder polynomials at p = 6 (printed by
the script); the prime-power details moved from Section 7 to Appendix A; the closing paragraph of Section 3 and the paragraph
after Proposition 5.2 (repetitions); in the paragraph on simple/multiplicity/length/reduced, the "infinitesimal deformation"
equivalence and the "local uniqueness" sentence (the latter's point is now made in Section 10).

## For the author to decide or confirm

1. "the four with real coefficients are, after the scales are restored, the solutions (1.4) of Kudryashov–Migita 2007" (§9.4) and "Nikolaevskiy equation" as the p = 5 example of a purely dissipative equation (§2.2, Table 2).
2. Length: 36–37 pages (was 31). Readability was preferred to compression. Further wholesale cuts, if wanted: the prime-power paragraph of §7 (0.4 p), the literature-normalization sentences in §9.3 (0.2 p), parts of "Relation to earlier work".
3. The sentence citing Kudryashov–Sinelshchikov 2012 in §9.3 ("elliptic formulas with nonzero odd derivative coefficients in the
   full fifth-order evolution equation") is kept verbatim; a cold reader found it ambiguous (odd powers of D in P, or odd-order
   derivatives in the evolution equation?). Only the author can say which is meant.
4. Disclosure section: the Claude Code item now lists the new results and the reorganization; the Codex item is unchanged.
5. On adoption: copy `paper/` back to `arxiv_meromorphic_waves/` with a `history/` backup, rebuild the tarball and `validation.json` there (the branch already has a regenerated `MANIFEST.sha256`, README and `anc/symmetry_checks/`).
