# Reducedness certificate for X_11: final accounting

Date: September 2, 2026, evening. Written by Fable (Claude). Supersedes `fable_p11_certificate_status.md` (15:30 UTC). All
computations live in `/tmp/fable/coll/`; nothing pre-existing in the project folder was modified. Codex's independent audits are in
`codex_dvr_p11_snapshot001_results.json`, `codex_dvr_p8_v2_residual_results.json`, `codex_reflection_p8.{py,md,json}`.

## 1. Statement

**Theorem (certified).** The normalized one-pole scheme \(\mathscr X_{11}\) is reduced of length \(\binom{21}{10}=352716\): the
order-eleven member of the family \(P(D)v+v^2/2=0\) (the travelling-wave reduction of the sixth-order dispersive Nikolaevskiy equation
itself is the case \(p=5\)) has exactly 352716 one-pole rational–exponential profiles (counted with their labels), all of them simple
points of the scheme.

The length is a theorem (Codex, gap-two argument at \(\ell=19\)). Reducedness is established by a certificate: every one of the
352716 points is exhibited as a distinct simple point over the 19-adics. It is the largest order settled so far, and the first settled by local certificates
at a structured prime rather than by a global Gröbner-basis computation: \(p=5\) (index 9) and \(p=8\) (index 15, already neither
prime nor a prime power) were certified by Gröbner bases, and every prime index by the prime-index theorem.

## 2. Route

Work at \(\ell=2p-3=19\). Modulo 19 the closure polynomial factors as \(u\,(x^{19}-x)\,S_A\), so the special fibre is combinatorial:
its points are products \(A=BC\) with \(B\mid x^{19}-x\) squarefree and \(C\mid S_A\) ("presentations"), 352716 of them, equal to the
length. Points of the special fibre carrying several presentations are collisions of characteristic-zero points; reducedness is the
statement that all collisions separate 19-adically.

| special fibre of \(\mathscr X_{11}\) at \(\ell=19\) | points | presentations |
|---|--:|--:|
| simple over \(\mathbb F_{19}\) | 119781 | 119781 |
| simple over \(\mathbb F_{361}\) (Jacobian rank checked) | 87372 | 87372 |
| singular, corank 1 | 47801 | 97971 |
| singular, corank 2 | 11592 | 47592 |
| total | | 352716 |

Simple special points lift uniquely (Hensel). Corank-1 points were separated by the tail-aware Newton-polygon certificate on the
one-variable restricted germ, with exact error tracking \((K,E)\) and the refinement height \(H=v_0+s\,i_0\) (repair by Codex):
**all 47801 certified**, local lengths equal to presentation counts everywhere. Corank-2 points were separated by exact certificates
in local fields: candidate branches from two-variable jets and Codex's descent over local fields; each candidate certified by the
strict Newton–Kantorovich condition \(v(F(a))>2\,v(\det J(a))\) on the exact ten-variable system in \(O_K=W[\varpi]\),
\(\varpi^b=19u\); orbits identified by the characteristic polynomial of a common linear form, compared pairwise at the common
guaranteed precision; a point is complete when the certified orbit degrees sum to its presentation count. The justification is
`fable_local_certificates_justification.md` (Lemmas 1–8, including Codex's five repairs and the equivariant lemma).

## 3. Validation on p = 8 (known reduced)

The same pipeline at \(\ell=13\) on \(\mathscr X_8\), whose reducedness is known from an independent Gröbner-basis certificate,
reproduces the count exactly: 1977 + 1548 simple special points, 942 corank-1 points (1938 points), 234 corank-2 points (972
points), total 1977 + 1548 + 1938 + 972 = 6435 \(=\binom{15}{7}\). The reflection-fixed corank-2 point \(x^7+4x^5+12x^3+9x\) was certified twice: by the generic
driver after a linear change, and by Codex's symmetry-preserving chart (unit quotient Jacobian, exact Hensel lift), agreeing
coordinate by coordinate modulo \(13^6\). Codex also re-certified all 11 second-generation p=8 results independently (exact
equations, field-generation discriminants, pairwise resultants).

## 4. Result for p = 11

| stage | special points | points certified |
|---|--:|--:|
| simple (both residue fields) | 207153 | 207153 |
| corank 1 | 47801 of 47801 | 97971 |
| corank 2, first-generation driver | 11145 of 11592 complete | 45804 |
| corank 2, second-generation driver (waves 1–2) | 444 of 447 | 1776 |
| corank 2, high-precision rerun | 3 of 3 | 12 |
| **total** | | **352716** |

No point was ever over-certified (certified degree exceeding the presentation count would signal an error in the certificate), and
no run raised an exception. The three points sent to the high-precision rerun,
\([9,16,9,16,2,5,11,1,4,2]\), \([10,16,0,2,17,13,6,5,5,1]\), \([3,6,17,18,11,10,7,3,11,11]\),
each had a single degree-4 branch certified but a linear-form discriminant of valuation 14 against a guaranteed precision of 12. At
precision 16 (`v2_single_hp.py`, \(K_{\rm ser}=16\), \(E_{\rm ser}=14\), \(M=40\)) all three certify as one degree-4 orbit each, as did
the one wave-1 point with the same profile. Codex's independent audit of that wave-1 point shows the valuation 14 belongs to the
chosen linear form, not to the orbit: the coordinate \(a_1\) alone is a primitive element with discriminant valuation 8, so the
precision-16 certificates are sound with margin. Final tally (`p11_final_tally.py`): **11592 of 11592 corank-2 special points
complete, 47592 of 47592 points; grand total 352716 of 352716.**

Independent audit (Codex, `codex_dvr_p11_snapshot001_results.json`, `codex_dvr_p11_v2_hp001_results.json`): all 11145
first-generation completions and all 443 core second-generation completions re-verified against the exact equations with
field-generation discriminants and pairwise resultants, zero failures (425 s on eight processes for the first generation). The
four high-precision records (`corank2v2_p11_wavehp_pt*.pkl`) are the last items in that audit queue.

## 5. What this does and does not establish

- Established: \(\mathscr X_{11}\) reduced of length 352716; hence the count conjecture holds at \(p=11\). Together with the prime-index theorem (all \(p\) with \(2p-1\) prime) and the certified \(p=8\), the conjecture is now
  confirmed at every order up to 12 and at every prime index.
- Not established: the statement for all orders remains a conjecture. Parity of \(p\) plays no role in the count or in reducedness: the prime-index
  theorem covers \(p=2,3,4,6,7,9,10,12\), Gröbner certificates cover \(p=5\) and \(p=8\), and this certificate covers \(p=11\), so
  the conjecture holds at every order \(p\le12\); odd \(p\) is the physically motivated case (even-order dissipative equations
  integrate once to odd order, while even \(p\) is the KdV-type hierarchy), and it is also where the one-pole class exhausts the
  rational–exponential sector and where the reflection acts on \(\mathscr X_p\) (see `fable_prime_index_theorem.md`); for even
  \(p\) the count is of the one-pole sector. The first open order is \(p=13\) (index 25); the
  structured route is available there since \(2p-3=23\) is prime, at roughly 15 times the size of \(p=11\).
- Attribution: classification in place of ansätze goes back to Eremenko (classical KS) and Demina–Kudryashov; what is new here is the
  class-level count and labelling and, at \(p=11\), the simplicity of every point.

## 6. Files

- Stage 1: `collision_analysis.py`, `stage1_p11.pkl`. Corank 1: `separator.py`, `local_analysis.py`, `stage2_p11_*.log`.
  Corank 2: `lfield.py`, `corank2_certify.py` (first generation, `corank2_p11_chunk*.pkl`), `corank2_v2.py` and
  `v2_p11_residual.py` (second generation, `corank2v2_p11_wave*_*.pkl`), `v2_single_hp.py`, `p11_final_tally.py`.
- Exports for independent audit: `fable_p8_v2_residual_final.json` and the p=11 pickles (same layout: `a_certified`, `field_def`,
  `charpoly`, `vF`, `vdelta`, `radius`).

## 7. Abandoned routes

The msolve runs on the pulse and front sectors (160 threads each, 180–300 GB) were stopped after the certificate closed: after about
ten hours they were at 12% of the degree-13 round and 2% of the degree-12 round respectively, with no prospect of finishing. The
weighted-ordering Singular run on the tail-5 stratum is superseded as well. Neither produced a verdict that is used above.
