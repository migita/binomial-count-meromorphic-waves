# Why the degree table proves rigidity

Let `H_A(x)=integral_0^x A(t)A(x-t)dt` and `beta(I,J)=I!J!/(I+J+1)!`.
For a table row, write `2d+1=q^e+g`, with `q` an odd prime, `e>=1`, and `g` even with `0<=g<q`.

For a monic polynomial `C=x^s+c1*x^(s-1)+...+cs`, set `c0=1` and

`S_(g,C)(x) = sum_(0<=i,j<=s, i+j<=g) K_ij c_i c_j x^(g-i-j)`,

where

`K_ij = falling(g,i+j)/(falling((g-1)/2,i)*falling((g-1)/2,j))`.

These rational coefficients are defined modulo every `q>g`.
For each `s=1,...,g`, the computation forms all `s` coefficients of the remainder of `S_(g,C)` on division by the monic C.
With `weight(c_i)=i`, the coefficient of `x^(s-j)` is homogeneous of weight `g-s+j`.

## Reduction from degree d to the gap systems

The uniform reduction lemmas in `paper/anc/rigidity/proof.tex` give this implication for every even gap `g<q`.
For completeness, its key coefficient identity is

`beta(d-i,d-j)/beta(d,d) = falling(2d+1,i+j)/(falling(d,i)*falling(d,j))`.

Legendre's formula shows that the ratio is q-integral for all `0<=i,j<=d`, has positive valuation when `i+j>g`, and reduces to `K_ij` when `i+j<=g`; the leading beta coefficient has valuation `-e`.
Thus, for an integral monic A,

`H_A/beta(d,d) = x^(q^e) S_(g,A)  (mod q)`.

If a nonmonomial complex solution existed, the rational polynomial equations and a nonzero-coefficient condition would give an algebraic solution.
At a place above q, scale its roots so that all are integral and at least one nonzero root is a unit, keeping A monic.
This scaling preserves convolution divisibility, and the reduced polynomial has the form `Abar=x^(d-s) C` with `C(0)!=0` and `s>=1`.
Monic division preserves integrality, so reduction gives `C | S_(g,C)`.
Since the residual polynomial is monic of degree g, necessarily `1<=s<=g`.
For `g=0` this is already impossible; otherwise it contradicts the origin-support check in stratum s.
Degree zero is immediate.

## What the Gröbner output establishes

A pure power of every coefficient variable in the leading ideal makes the quotient finite-dimensional, over F_q and after any field extension.
The ideal is homogeneous for positive weights, so a nonzero geometric zero would generate a positive-dimensional scaling orbit; therefore its only geometric zero is the origin.
This rules out every C with nonzero constant coefficient and proves the hypothesis of the reduction above.
A search for F_q-rational points alone would not suffice, but the ideal-dimension argument works over the algebraic closure.

As an additional check, the recorded and replayed staircases have Hilbert series

`product_(j=1..s)(1-t^(g-s+j)) / product_(i=1..s)(1-t^i) = [g choose s]_t`,

and hence dimension `binomial(g,s)`.
The origin here is generally nonreduced: the purpose of these systems is to exclude support away from the origin, not to prove simplicity.

Together, all strata for every positive-gap pair and the exact 572-row arithmetic table prove rigidity through degree 572.
The computations recorded here use exact finite-field linear algebra; they are computational records with reproducible generators, rather than the integer ideal-membership identities supplied by the older degree-72 package.
They imply no new simplicity result for the discrete wave-counting schemes.
