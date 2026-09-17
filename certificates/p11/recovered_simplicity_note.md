# Recovered finite-order simplicity results for Table 1

The preserved research record establishes full count and simplicity for every `2 <= p <= 12`, combining the prime-index theorem with exact computations at `p=5,8,11`. The first unresolved full-family simplicity case in that record is `p=13` (index 25). Statements that p=11 remained open in `current_research_status.md` and the early p=11 status note predate the final certificate accounting.

## Fresh p=8 replay

The newly generated `full_p8_q32003_dp_slimgb.sing` is reconstructed directly from the polynomial continuation of the finite sums defining S_A. The reconstruction was also checked at enough integer arguments to identify the whole polynomial. Singular over F_32003 reports:

- dimension zero;
- quotient length 6435;
- unit ideal after adjoining the matching Jacobian determinant.

The run completed without a Singular error. Its input and transcript are in this directory. The Jacobian determinant was computed by division-free subset expansion, reducing at each step in the quotient ring. The same pipeline first reproduced the known p=5 length 126 and simplicity result.

The elementary lifting argument is enough: every geometric point of the finite-field quotient is simple. Work over a common finite extension of the residue field and lift each point by multivariate Hensel. This gives 6435 distinct simple characteristic-zero points. The previously proved characteristic-zero length is 6435, so these exhaust the scheme. No extra flatness assertion is needed.

## Preserved p=11 certificate

The complete archive is `codex_enumeration_paper_certificate_record.tar.gz`, not merely the partial `fable_archive/coll` snapshot. It is 11,958,177 bytes and contains 270 manifest-listed files plus the manifest itself. All 270 sizes and SHA-256 hashes have been verified. It includes all 96 first-generation corank-two batches, eight first-wave batches, forty second-wave batches, four final high-precision records, the corank-one record, the exact stage-one equations, the checker sources, the mathematical justification and the independent audit outputs.

The archive hash is `4c6f1e31260032a38ae32883e2ec6fab62222925930b6fa957ce12ac0d890a69`.

The characteristic-zero simple-point subtotals are:

| Source in the reduction at 19 | Simple characteristic-zero points |
| --- | ---: |
| Simple rational residue points | 119781 |
| Simple quadratic-extension residue points | 87372 |
| Corank-one local certificates | 97971 |
| Independently audited corank-two local certificates | 47592 |
| Total | 352716 |

The 47,801 corank-one residue labels are covered exactly once; all records certify their full local length with no flags. The 11,592 corank-two residue labels are also covered exactly once in the merged independent audit. Each selected entry was checked against its source audit record, including successful Hensel and separation flags. Overlapping partial records were not added twice. The known length is C(21,10)=352716, so the recorded lower bounds exhaust it.

For this review, all ten rational equations were independently reconstructed from the finite sums and matched exactly to the archived equations after their factor of 19. The four final high-precision records were also replayed using the archived independent checker in a separate extracted directory: all four passed, certifying 16 simple points. The entire historical computation was not rerun. The paper should describe p=11 as a preserved exact computational certificate, not as a new full replay performed during this rewrite.

`p11_archive_integrity.json`, `p11_record_validation.json` and `p11_high_precision_replay.json` record these checks. `validate_p11_record.py` reproduces the input, provenance, coverage and accounting checks. The complete archive provides the historical larger replay; its producer scripts require their documented path configuration. The independent branch verifier can be run from an extracted copy with explicit `--stage`, `--batches`, `--refinement-steps` and `--output` arguments, and the bounded replay just performed used only Python and SymPy.

## Suggested paper description

> Exact computations establish simplicity at the remaining orders p=5,8,11. Together with the prime-index theorem, they prove that all normalized pairs are distinct for every 2<=p<=12; in the elliptic case the lattice is generic. The order-eight certificate is a finite-field quotient-length and Jacobian calculation. The order-eleven certificate separates the points of a structured reduction at 19 by exact local lifting, with field-degree and disjointness checks. Its certified subtotals sum to the previously proved binomial length. Inputs, certificates and independent verification records are supplied in the ancillary material.

Keep the detailed local-field procedure in the appendix and the bundle documentation. The main status table needs the consecutive range and a clear indication of which finite orders use computation. If the larger archive has not yet been bundled with the new manuscript, say it is preserved and arrange that concrete source reference before claiming it is supplied.

## Pure-subfamily distinction

Additional pure-subfamily computations must be labelled separately from full X_p simplicity. To deduce generic simplicity of 2F_p elliptic pairs from a reduced pure rational-exponential scheme beyond the known full range, also show P_A(0) never vanishes there. A unit-ideal check for the pure matching ideal together with C_A(0) is sufficient. Then the nodal quadratic has two distinct roots and the existing finite-family argument applies.
