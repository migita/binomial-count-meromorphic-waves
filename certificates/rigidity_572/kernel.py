#!/usr/bin/env python3
"""
Second-referee pipeline (own code, written from the definitions only).

Objects.
  beta(I,J) = I! J! / (I+J+1)!,   H_A = sum_{I,J} beta(I,J) a_I a_J x^{I+J+1},  N = 2d+1.
  K_ij(delta) = (2 delta+1)_(i+j) / ( delta_(i) delta_(j) )   (falling factorials)
  residual system of gap g (even), stratum s (1<=s<=g):
      C = x^s + c_1 x^{s-1} + ... + c_s,  c_0 = 1,
      S_{g,C} = sum_{0<=i,j<=s, i+j<=g} K_ij((g-1)/2) c_i c_j x^{g-i-j},
      F_j = [x^{s-j}] rem(S_{g,C}, C),  j=1..s      (weighted homogeneous of weight g-s+j, wt c_i = i).

Two generators of the coefficient table:
  (a) kappa_formula(g, mod)      : K_ij((g-1)/2) exactly (Fractions) or mod a prime
  (b) kappa_from_degree(d,q,e)   : the honest reduction mod q of beta(d-i,d-j)/beta(d,d), N = 2d+1 = q^e+g,
                                   computed from factorials for the actual degree d (no formula used).
"""
from fractions import Fraction
from math import factorial
import itertools, sys

# ----------------------------------------------------------------- coefficient tables
def falling(x, k):
    r = 1
    for t in range(k):
        r = r * (x - t)
    return r

def K_exact(g, i, j):
    if i + j > g:
        return Fraction(0)
    delta = Fraction(g - 1, 2)
    return Fraction(falling(g, i + j)) / (falling(delta, i) * falling(delta, j))

def kappa_formula(g, smax, mod=None):
    """table[(i,j)] for 0<=i,j<=smax, i+j<=g. Exact Fractions if mod is None, else residues mod `mod`."""
    tab = {}
    for i in range(smax + 1):
        for j in range(smax + 1):
            if i + j <= g:
                k = K_exact(g, i, j)
                if mod is None:
                    tab[(i, j)] = k
                else:
                    assert k.denominator % mod != 0, ("denominator divisible by prime", g, i, j, mod)
                    tab[(i, j)] = k.numerator * pow(k.denominator, -1, mod) % mod
    return tab

def vq(n, q):
    n = abs(n); v = 0
    while n % q == 0:
        n //= q; v += 1
    return v

def kappa_from_degree(d, q, e, smax):
    """Honest reduction: rho_ij = beta(d-i,d-j)/beta(d,d) as an exact rational, for 0<=i,j<=smax.
    Returns (table of residues mod q for ALL (i,j) with i,j<=smax, min valuation, list of unit positions)."""
    N = 2 * d + 1
    g = N - q ** e
    assert 0 <= g < q and g % 2 == 0 and q ** e > N // 2
    fd = factorial(d)
    tab = {}
    units = []
    minval = None
    for i in range(smax + 1):
        for j in range(smax + 1):
            if d - i < 0 or d - j < 0:
                continue
            num = factorial(d - i) * factorial(d - j) * factorial(N)
            den = factorial(N - i - j) * fd * fd
            r = Fraction(num, den)
            v = vq(r.numerator, q) - vq(r.denominator, q)
            minval = v if minval is None else min(minval, v)
            if v < 0:
                raise ValueError("non-integral ratio", d, q, e, i, j)
            if v == 0:
                units.append((i, j))
                tab[(i, j)] = r.numerator * pow(r.denominator, -1, q) % q
            else:
                tab[(i, j)] = 0
    return tab, minval, units

# ----------------------------------------------------------------- sparse polynomials in c_1..c_s
# dict: exponent tuple -> coefficient (int, reduced mod p if p given; or Fraction/int if p None)
def padd(a, b, p):
    r = dict(a)
    for m, c in b.items():
        v = r.get(m, 0) + c
        if p: v %= p
        if v == 0:
            r.pop(m, None)
        else:
            r[m] = v
    return r

def pmul(a, b, p):
    r = {}
    for m1, c1 in a.items():
        for m2, c2 in b.items():
            m = tuple(x + y for x, y in zip(m1, m2))
            v = r.get(m, 0) + c1 * c2
            if p: v %= p
            if v == 0:
                r.pop(m, None)
            else:
                r[m] = v
    return r

def pscale(a, k, p):
    r = {}
    for m, c in a.items():
        v = c * k
        if p: v %= p
        if v != 0:
            r[m] = v
    return r

def var(s, i):
    """c_i as polynomial (i=0 -> 1)."""
    m = [0] * s
    if i > 0:
        m[i - 1] = 1
    return {tuple(m): 1}

def stratum_system(g, s, tab, p=None):
    """F_1..F_s from a coefficient table tab[(i,j)] (entries for i+j<=g are used, others ignored).
    Returns list of dict polynomials."""
    zero = {}
    one = {tuple([0] * s): 1}
    c = [var(s, i) for i in range(s + 1)]
    # R[e][k] = coefficient of x^k in x^e mod C, k=0..s-1
    R = []
    for e in range(g + 1):
        if e < s:
            vec = [dict() for _ in range(s)]
            vec[e] = dict(one)
        else:
            prev = R[e - 1]
            top = prev[s - 1]
            vec = [dict() for _ in range(s)]
            for k in range(1, s):
                vec[k] = dict(prev[k - 1])
            # x^s = - sum_{i=1}^s c_i x^{s-i}
            for i in range(1, s + 1):
                k = s - i
                vec[k] = padd(vec[k], pscale(pmul(top, c[i], p), -1, p), p)
        R.append(vec)
    rem = [dict() for _ in range(s)]
    for i in range(s + 1):
        for j in range(s + 1):
            if i + j <= g:
                kij = tab[(i, j)]
                if kij == 0:
                    continue
                cc = pscale(pmul(c[i], c[j], p), kij, p)
                vec = R[g - i - j]
                for k in range(s):
                    if vec[k]:
                        rem[k] = padd(rem[k], pmul(cc, vec[k], p), p)
    return [rem[s - j] for j in range(1, s + 1)]

def weight(m):
    return sum((i + 1) * e for i, e in enumerate(m))

def check_weighted_homogeneous(F, g, s):
    for j, f in enumerate(F, start=1):
        for m in f:
            assert weight(m) == g - s + j, (g, s, j, m)

def poly_to_str(f, names):
    if not f:
        return "0"
    terms = []
    for m, c in sorted(f.items(), reverse=True):
        mon = "*".join(f"{names[i]}^{e}" for i, e in enumerate(m) if e > 0)
        terms.append(f"{c}*{mon}" if mon else f"{c}")
    return "+".join(terms).replace("+-", "-")

if __name__ == "__main__":
    # tiny self-test: g=2, s=2 over Q must give 7 c1 x + 8 c1^2 - 17 c2
    tab = kappa_formula(2, 2)
    F = stratum_system(2, 2, tab)
    print("g=2,s=2:", [poly_to_str(f, ["c1", "c2"]) for f in F])
    tab = kappa_formula(2, 1)
    F = stratum_system(2, 1, tab)
    print("g=2,s=1:", [poly_to_str(f, ["c1"]) for f in F])
