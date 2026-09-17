# Rates, denominators and labels

The real unit-rate pairs through order four have rational coefficients.
Some familiar radicals appear when a physical coefficient is fixed instead
of the wave's rate. The denominators of the normalized pairs carry a
different kind of information: they can occur only at primes where the
continuous rigidity system acquires a nonzero solution after reduction.

The statements below separate a general implication from exact low-degree
calculations. The replay scripts use rational and integer arithmetic.

## Every normalized operator has a small positive integer root

Write the paper's normalized profile as

$$
v_A(z)=s_p A(D)Q(z),\qquad Q(z)=\frac{e^z}{1+e^z},\qquad
\deg A=p-1,
$$

with $A$ monic. Since

$$
v_A(z)=s_p\sum_{n\ge1}(-1)^{n-1}A(n)e^{nz},
$$

let $m$ be the first positive integer for which $A(m)\ne0$.
There are at most $p-1$ preceding zeros, so $1\le m\le p$.
In $P_A(D)v_A+v_A^2/2=0$, the square begins at exponent $2m$.
The coefficient of $e^{mz}$ is therefore
$s_p(-1)^{m-1}A(m)P_A(m)=0$, giving **$P_A(m)=0$**.

This holds at every order. It requires neither a prime index, simplicity,
nor rational coefficients. The integer is the leading tail exponent in
the unit-rate coordinate.

## Where the familiar radicals enter

At rate $\kappa$, the normalized operator becomes
$\kappa^pP_A(D/\kappa)$. Fixing a physical coefficient can therefore
require solving an equation for $\kappa$.

| Example | Exact unit-rate relation |
|---|---|
| KS, $\sqrt{47}$ | $P_A=(\rho-3)(\rho-4)(\rho-5)$; its $\rho$ coefficient is $3\cdot4+3\cdot5+4\cdot5=47$. |
| KS, $\sqrt{73}$ | $P_A=(\rho-2)(\rho-5)(\rho-9)$; its $\rho$ coefficient is $2\cdot5+2\cdot9+5\cdot9=73$. |
| Rosenau–KdV, $\sqrt{313}$ | For $P_A=\rho^4-13\rho^2+36$ and the zero-background `rosenau_kdv` preset, matching gives $c\kappa^2=1/13$ and $169c(c-1)=36$, hence $c=(13\pm\sqrt{313})/26$. |
| Benney–Lin, $\sqrt{806}$ | For the 3751 front below, $[\rho^3]P_A=-4$ and $[\rho]P_A=-35594/3751$; the equal $D^3,D$ physical coefficients require $\kappa^2=7502/17797$, hence $\kappa=\pm11\sqrt{806}/481$. |

`verify_catalogue.py` proves that all real normalized pairs at
$p=1,2,3,4$ are rational, with respective counts $1,3,8,21$.
The assertion is about those orders. It does not make every algebraic
coefficient at higher orders a removable normalization artifact.

## A denominator prime forces bad geometric reduction

Put $d=p-1$ and

$$
A(\rho)=\rho^d+a_1\rho^{d-1}+\cdots+a_d,\qquad
H_A(\rho)=\int_0^\rho A(s)A(\rho-s)\,ds.
$$

Call a prime $q>2d+1$ **bad** if the coefficients of
$\operatorname{rem}_A H_A$ have a nonzero common zero over
$\overline{\mathbb F}_q$. A common zero is nonzero when at least one
$a_i\ne0$; the polynomial $A=\rho^d$ is the origin.

For any normalized pair with algebraic coefficients, if some coefficient
is nonintegral at a place above such a prime $q$, then $q$ is bad.
Equivalently, good reduction of this leading system forces every pair to
be integral at every place above $q$. No converse is asserted in general.

To prove the implication, give $a_i$ weight $i$. The discrete matching
equations have coefficients integral at $q>2d+1$; their highest weighted
parts are the coefficients of $\operatorname{rem}_A H_A$. Suppose that
some $a_i$ has negative valuation and set
$t=\min_i v(a_i)/i<0$. After a finite extension choose $\lambda$
with $v(\lambda)=-t>0$, and put $b_i=\lambda^i a_i$.
All $b_i$ are integral and at least one is a unit. Multiplying each
matching equation by the appropriate power of $\lambda$, its lower
weighted terms vanish in the residue field and its highest terms give
the continuous equations at $(\bar b_1,\ldots,\bar b_d)$. This is the
required nonzero geometric zero. The coefficients of $P_A$ and $v_A$
are polynomials in the $a_i$ with $q$-integral coefficients, so the
same conclusion covers the whole pair.

## Exact spectra in degrees two and three

The initial brute-force calculation searched $\mathbb F_q$-points
for $2d+1<q<48$. It correctly found $11$ at degree two and
$11,31$ at degree three. The exact computation here settles **every**
prime above the threshold, over the algebraic closure:

| Degree $d$ | Profile order $p$ | All bad primes $q>2d+1$ | Denominator primes of real rational $A$'s |
|---|---|---|---|
| 2 | 3 | $11$ | $11$ |
| 3 | 4 | $11,31,71,4217$ | $3,11,31$ |

The prime $3$ in the real order-four list is outside the stated
$q>7$ range. The primes $71$ and $4217$ cannot be seen in a
search below 48, or by inspecting only the real pairs.

To exclude every other prime, `denominator_certificates.json` supplies
integer identities

$$
D_i a_i^{N_i}=\sum_j U_{ij}(a_1,\ldots,a_d)F_j(a_1,\ldots,a_d),
$$

where the $F_j$ are the continuous remainder coefficients with
denominators cleared and $U_{ij}$ have integer coefficients. For a
prime not dividing any $D_i$, a common zero must have every coordinate
zero, over any extension field. The primes above the threshold dividing
these constants are exactly the claimed exceptional set.

For example, at degree two let

$$
F_0=a_1^3a_2-7a_1a_2^2,\qquad
F_1=a_1^4-8a_1^2a_2+11a_2^2.
$$

Two small identities are

$$
4a_1^7=(-283a_1^2+495a_2)F_0+(4a_1^3+315a_1a_2)F_1,
$$
$$
44a_2^4=(-a_1^3-3a_1a_2)F_0+(a_1^2a_2+4a_2^2)F_1.
$$

Each remaining prime has an explicit nonzero witness:

| $d$ | $q$ | Monic $A$ with $A\mid H_A$ modulo $q$ |
|---|---|---|
| 2 | 11 | $\rho^2+1$ |
| 3 | 11 | $\rho^3+\rho^2+4\rho$ |
| 3 | 31 | $\rho^3+\rho$ |
| 3 | 71 | $\rho^3+1$ |
| 3 | 4217 | $\rho^3+\rho^2-1622\rho-1360$ |

In the first, third and fourth rows the coefficient of the added
monomial can vary freely. More generally the weighted dilations of any
listed witness supply a nontrivial family. `verify_arithmetic.py` checks
the integral identities and witnesses without relying on a stored basis
or a bounded search.

The two extra primes actually occur in nonreal order-four pairs. Exact
elimination gives the irreducible factor for their $a_3$ coordinate

$$
158618644149091393a_3^4+726361140427644a_3^2+21252490207488,
$$

whose leading coefficient is $31^3\cdot71\cdot4217^3$. Its coefficients
are positive and its powers even, so it has no real root. Its root product
is the constant coefficient divided by the leading coefficient; this is
nonintegral at $31,71,4217$, forcing a nonintegral root at a place above
each prime. Since the matching scheme is finite, its elimination polynomial
describes actual projected points, so these roots occur in pairs.
Together with the rational pairs involving $11$, this proves equality
between the bad-prime set and the primes of nonintegrality **in degrees
two and three, considering all algebraic pairs and only $q>2d+1$**.
The all-degree assertion remains only the implication proved above.

## A name for the 3751 front

For the real pair

$$
A=\rho^3-\frac{12}{11}\rho^2+\frac{839}{3751}\rho-\frac{498}{3751},
\qquad
P_A=\frac{(\rho-3)(\rho-2)(3751\rho^2+3751\rho+11620)}{3751},
$$

the index $2p-1=7$ is prime. Reduction gives
$A=(\rho-1)(\rho-4)(\rho-5)$ in $\mathbb F_7[\rho]$, so its
prime-index label is **$\{1,4,5\}\subset\mathbb F_7$**. The mirror
has label $\{2,3,6\}$. Both are checked by the lookup normalization.

The subset interpretation is supplied by the prime-index theorem; a
chosen place, or compatible embedding into the relevant adic field, is
part of the labeling for algebraic coefficients. It is not an unqualified
label by $\mathbb F_{2p-1}$ at composite indices. The CLI emits a
subset automatically when the index is prime and the coefficients are
rational and integral there.
