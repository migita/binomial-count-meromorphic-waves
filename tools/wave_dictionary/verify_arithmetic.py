#!/usr/bin/env python3
"""Replay the integral identities and witnesses proving the bad-prime spectra.

No stored Groebner basis, finite-point exhaustion or algebraic-closure solver
is needed: the identities exclude every other prime and the witnesses include
each exceptional prime. q<=2d+1 is deliberately outside this calculation.
"""

import json
from pathlib import Path

import sympy as s

from core import RHO, identify, parse


HERE = Path(__file__).resolve().parent
WITNESSES = {
    2: {11: [0, 1]},
    3: {11: [1, 4, 0], 31: [0, 1, 0], 71: [0, 0, 1],
        4217: [1, -1622, -1360]},
}


def verify():
    records = json.loads((HERE/"denominator_certificates.json").read_text())
    for d in (2, 3):
        record = records[str(d)]
        variables = s.symbols("a1:%s" % (d+1))
        A = RHO**d+sum(a*RHO**(d-1-j) for j, a in enumerate(variables))
        coefficients = list(reversed(s.Poly(A, RHO).all_coeffs()))
        H = sum(coefficients[i]*coefficients[j]*s.factorial(i)*s.factorial(j)
                /s.factorial(i+j+1)*RHO**(i+j+1)
                for i in range(d+1) for j in range(d+1))
        remainder = s.rem(H, A, RHO)
        assert s.expand(remainder-parse(record["continuous_remainder"])) == 0
        F = [s.Poly(s.Poly(remainder, RHO).nth(k), *variables).clear_denoms()[1].as_expr()
             for k in range(d)]
        assert all(s.expand(f-parse(g)) == 0 for f, g in zip(F, record["integral_equations"]))
        possible = set()
        assert len(record["nilpotence_certificates"]) == d
        for variable, certificate in zip(variables, record["nilpotence_certificates"]):
            assert certificate["variable"] == str(variable)
            constant, power = int(certificate["constant"]), int(certificate["power"])
            assert constant and power > 0
            multipliers = [parse(v) for v in certificate["multipliers"]]
            assert len(multipliers) == d
            assert all(s.Poly(u, *variables).domain.is_ZZ for u in multipliers)
            identity = sum(u*f for u, f in zip(multipliers, F))-constant*variable**power
            assert s.expand(identity) == 0
            possible.update(q for q in s.factorint(abs(constant)) if q > 2*d+1)
        assert possible == set(WITNESSES[d]) == set(record["geometrically_bad_primes"])
        for q, values in WITNESSES[d].items():
            sub = dict(zip(variables, values))
            assert any(v % q for v in values)
            assert all(int(f.subs(sub)) % q == 0 for f in F)
        print("d=%s: every prime q>%s settled; bad primes %s." % (d, 2*d+1, sorted(possible)))
    catalogue = json.loads((HERE/"real_pairs_p1_p4.json").read_text())
    for p in (3, 4):
        primes = set()
        for row in catalogue[str(p)]:
            for a in row["a"]:
                primes.update(s.factorint(s.denom(s.Rational(a))))
        print("p=%s: denominator primes of the real rational A coefficients: %s." % (p, sorted(primes)))
    row = next(row for row in catalogue["4"] if row["a"] == ["-12/11", "839/3751", "-498/3751"])
    E, Q = s.symbols("E Q")
    label = identify(parse(row["profile"]).subs(Q, E/(1+E)))["prime_index_label"]
    assert label == {"prime": 7, "subset": [1, 4, 5]}
    mirror = next(row for row in catalogue["4"] if row["a"] == ["12/11", "839/3751", "498/3751"])
    assert identify(parse(mirror["profile"]).subs(Q, E/(1+E)))["prime_index_label"] == {"prime": 7, "subset": [2, 3, 6]}
    print("3751 front and mirror: labels {1,4,5} and {2,3,6} in F_7 verified.")
    P = parse(row["P_factored"])
    assert s.Poly((RHO-3)*(RHO-4)*(RHO-5), RHO).nth(1) == 47
    assert s.Poly((RHO-2)*(RHO-5)*(RHO-9), RHO).nth(1) == 73
    c = (13+s.sqrt(313))/26
    assert s.simplify(169*c*(c-1)-36) == 0
    rate = 11*s.sqrt(806)/481
    assert s.simplify(rate**2-s.Poly(P, RHO).nth(3)/s.Poly(P, RHO).nth(1)) == 0
    print("Rate identities for radicals 47,73,313,806 verified.")


if __name__ == "__main__":
    verify()
