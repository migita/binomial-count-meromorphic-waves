# Scope of the preserved computation

The following is the coverage section of the independent second-referee report of 17 September 2026; the complete package table uses its prime-only alternative, plus the prime-power index at degree 4, and retains every required stratum.

Source: `fable_rigidity_20260917/r3_theoremA_second_referee.md`.

## 4. "Rigidity for every `d <= 572`": independent pipeline (VERIFIED-COMPUTATIONALLY)

**Logic.** For `N = 2d+1` list the admissible triples `(q,e,g)`: `q` odd prime, `q^e in (N/2,N]`, `g = N-q^e < q` (even). `g = 0`: rigid by
Proposition 2. `g >= 2`: rigid if for every `s = 1..g` the ideal `I_{g,s} = (F_1..F_s) subset F_q[c_1..c_s]` contains a power of every
variable (then `V(I_{g,s}) = {0}` over `Fbar_q`, Proposition 2 applies).

**Pipeline (all own code).** `r3gen.py`: coefficient table `K_ij((g-1)/2) mod q`, own sparse polynomial division, `F_j` checked to
be weighted homogeneous of weight `g-s+j`. `r3check.py`: msolve 0.10.1, `-l 2` (exact sparse linear algebra, no probabilistic
step), `-g 1` (leading ideal in grevlex), one thread; from the leading ideal: (1) the smallest pure power `c_i^{k_i}` for
every `i` (the certificate that a power of every variable is in the ideal); (2) the Hilbert function of the staircase
with respect to `wt(c_i) = i`, compared in **every** weight with the Gaussian binomial `[g choose s]_t` (top weight `s(g-s)`, total
`C(g,s)`). Since reduction mod `q` can only increase the Hilbert function of the quotient, equality in every weight is
a two-sided check of the engine output. `r3cover.py`: candidates by increasing `g`, **all** strata of every tried pair
(no early exit), cache `results/strata.jsonl`.

**Result.**
* Every `1 <= d <= 572` has a certificate: table `results/cover_1_572_g16.txt` plus `results/cover_452_452_g18.txt`. Gap histogram
  `g=0: 205, 2: 148, 4: 99, 6: 50, 8: 34, 10: 15, 12: 9, 14: 5, 16: 6, 18: 1` (sum 572). No hole.
* 362 distinct certificate pairs `(q,g)` with `g >= 2`, 1692 strata: in every one a pure power of every variable is in the
  leading ideal and the Hilbert function equals `[g choose s]_t` in every weight. (For the tables with `d <= 572`, including
  the failed candidates and the primes-only variant, 1958 strata were computed; 20 of them are not supported at the origin.)
* Degrees that need `g >= 12` (all verified): `d = 152 (293+12), 164 (317+12), 197 (383+12), 259 (503+16), 268 (523+14), 269 (523+16),
  392 (773+12), 436 (859+14), 437 (863+12), 449 (887+12), 450 (887+14), 451 (887+16), 452 (887+18), 482 (953+12), 540 (1069+12),
  541 (1069+14), 542 (1069+16), 569 (1123+16), 570 (1129+12), 571 (1129+14), 572 (1129+16)`. `d = 73`: `(139, 8)`.
* `(887,18)`, `d = 452`: all 18 strata; pure powers `c_i^{19-s}` for every `i`; staircase sizes
  `18, 153, 816, 3060, 8568, 18564, 31824, 43758, 48620, 43758, ...` `= C(18,s)`; msolve times up to 651 s (`s = 11`), 669 s wall
  for the pair on 8 threads.
* Smallest-gap candidates that fail (`d <= 572`, 15 cases, non-rigid strata in my convention, which includes `C(0) = 0`):
  `(7,2):[2]`, `(17,2):[2]`, `(5,4):[2]`, `(23,4):[4]`, `(31,4):[4]`, `(353,4):[3]`, `(389,6):[3]`, `(23,8):[4]`, `(241,8):[5..8]`,
  `(23,10):[10]`, `(509,10):[8,9,10]`, `(863,10):[4,5,6]`, `(1129,10):[6]`; they occur at `d = 17, 25, 124, 145, 172, 178, 197, 259,
  266, 268, 269, 314, 436, 482, 569`. This is the same list as in `attack_arithmetic_global.md` Section 8 (restricted to
  `d <= 572`), and the first bad strata agree with `attack_exceptional_mass.md` Section 6.
* Comparison with the Round 2 table `scripts_arithmetic_global/cover_table_1_700.txt`: identical certificates in 569 of 572
  rows; in the three rows where Round 2 uses the chain criterion (`d = 197, 268, 314`) my table has an ordinary
  certificate (`383+12`, `523+14`, `619+10`), so **the chain criterion (Corollary 4.2 of `arithmetic_global`) is not needed for
  `d <= 572`**; I did not referee it.
* Weights for the actual degree: for every one of the 572 certificates the residues `beta(d-i,d-j)/beta(d,d) mod q` computed
  from exact factorials agree with `K_ij((g-1)/2) mod q` for `i+j <= g`, `i,j <= g` (`r3cover.py`), and for **all** `0 <= i,j <= d` the
  valuation is `>= 0` with equality iff `i+j <= g` (`r3valuations.py`, Legendre's formula; 0 failures in 572). This covers
  the 32 prime-power rows.
* Prime powers: 32 rows use `e > 1` (17 with `g = 0`, 15 with `g > 0`: `d = 61, 85, 122, 181, 182, 265, 267, 313, 365, 421-425, 481`).
  With primes only (`r3cover.py ... e1`, table `results/cover_1_572_g16_e1.txt`): every `d <= 572` has an `e = 1` certificate with
  `g <= 16`, except `d = 452` (`g = 18`, above) and `d = 4` (`N = 9`: `7+2` and `5+4` are both bad; `9 = 3^2` is the certificate).
  So apart from `d = 4` the claim rests on the case `e = 1`; and the case `e >= 1` is proved in Section 1.
* Second engine (`r3singular.py`): Singular `std` in the weighted ordering `wp(1..s)`, `vdim` and the nilpotency index of
  every variable. All 20 certificate pairs with `g in {12,14,16}` (274 strata; up to 269 s per stratum): `vdim = C(g,s)`,
  all variables nilpotent, 0 disagreements with msolve. 40 random certificate pairs with `g <= 10` (seed 20260917) and all
  13 failed pairs (240 strata): 0 disagreements (20 non-rigid strata reproduced as `vdim = -1`). `(887,18)`: see Section 5.
* Third engine, no Groebner bases (`r3macaulay.py`): ranks of `Phi_w mod q` for `w_0 < w <= w_0+s` by python-flint; see Section 5
  for the scope reached.

**What this does and does not establish.** It establishes, by three engines that agree, the hypothesis of Proposition 2
for one triple `(q,e,g)` per degree `d <= 572`; together with Proposition 2 this gives rigidity in these degrees. The
computations are deterministic but are not accompanied by replayable certificates (no cofactors are stored).
`d = 573` needs `(1129,18)` (done as a bonus, Section 5) and `d = 574` a gap-20 computation (not attempted).

---

