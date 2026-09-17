#!/usr/bin/env python3
"""Recompute the p<=4 real catalogue over Q, including real completeness.

The low-degree elimination happens here, once for the verification; the wave
constructor does not use a catalogue or a Groebner basis. Nonlinear real
eliminant factors cause an explicit failure rather than being discarded.
"""

from functools import reduce
import json
from pathlib import Path

import sympy as s

from core import RHO, parse


HERE = Path(__file__).resolve().parent


def matching(p):
    variables = s.symbols("a1:%s" % p)
    A = RHO**(p-1)+sum(a*RHO**(p-2-j) for j, a in enumerate(variables))
    j = s.Symbol("j")
    summand = s.Poly(s.expand(A.subs(RHO, j)*A.subs(RHO, RHO-j)), j)
    convolution = s.expand(sum(co*s.summation(j**n, (j, 1, RHO-1))
                               for (n,), co in summand.terms()))
    quotient, remainder = s.div(convolution, A, RHO)
    equations = [s.Poly(co, *variables).clear_denoms()[1].as_expr()
                 for co in s.Poly(remainder, RHO).all_coeffs()] if variables else []
    return variables, A, convolution, quotient, equations


def real_rational_solutions(equations, variables, basis=None):
    if not variables:
        if any(s.expand(e) != 0 for e in equations):
            return []
        return [()]
    if basis is None:
        basis = s.groebner(equations, *variables, order="grevlex", domain=s.QQ)
    if list(basis) == [1]:
        return []
    assert basis.is_zero_dimensional, "Expected a finite ideal."
    if str(basis.order) != "lex":
        basis = basis.fglm("lex")
    v = variables[-1]
    eliminants = [s.Poly(e, v) for e in basis if e.free_symbols <= {v}]
    assert eliminants, "Elimination did not produce a univariate polynomial."
    eliminant = reduce(s.gcd, eliminants).sqf_part()
    roots = []
    for factor, multiplicity in s.factor_list(eliminant)[1]:
        if factor.degree() == 1:
            roots.append(-factor.nth(0)/factor.nth(1))
        else:
            assert factor.count_roots(-s.oo, s.oo) == 0, "An irrational real coordinate requires further isolation."
    result = []
    for root in roots:
        specialized = [e.subs(v, root) for e in basis]
        result.extend(tail+(root,) for tail in real_rational_solutions(specialized, variables[:-1]))
    return result


def verify():
    data = json.loads((HERE/"real_pairs_p1_p4.json").read_text())
    counts = {}
    Q = s.Symbol("Q")
    derivative = lambda f: s.expand(Q*(1-Q)*s.diff(f, Q))
    for p in range(1, 5):
        variables, A, convolution, quotient, equations = matching(p)
        initial = None
        if p == 4:
            initial = s.groebner(equations, *variables, order="grevlex", domain=s.QQ).fglm("lex")
            eliminants = [e for e in initial if e.free_symbols <= {variables[-1]}]
            assert len(eliminants) == 1
            nonlinear = [f for f, multiplicity in s.factor_list(eliminants[0])[1]
                         if s.degree(f, variables[-1]) > 1]
            assert len(nonlinear) == 1
            quartic = 158618644149091393*variables[-1]**4+726361140427644*variables[-1]**2+21252490207488
            assert s.Poly(nonlinear[0], variables[-1]).monic() == s.Poly(quartic, variables[-1]).monic()
            assert s.factorint(158618644149091393) == {31: 3, 71: 1, 4217: 3}
            assert all(21252490207488 % q for q in (31, 71, 4217))
            print("p=4: nonreal quartic verified; nonintegral roots occur above 31, 71 and 4217.", flush=True)
        real = set(real_rational_solutions(equations, variables, initial))
        stored = {tuple(s.Rational(a) for a in row["a"]) for row in data[str(p)]}
        assert real == stored, (p, "Real catalogue is incomplete or has extra entries.")
        assert len(stored) == len(data[str(p)]), "Duplicate catalogue entries."
        sp = 2*s.factorial(2*p-1)/s.factorial(p-1)**2
        for row in data[str(p)]:
            substitute = dict(zip(variables, map(s.Rational, row["a"])))
            expected_A = A.subs(substitute)
            expected_P = s.expand(sp*quotient.subs(substitute)/2)
            assert s.expand(parse(row["A"])-expected_A) == 0
            assert s.expand(parse(row["P_factored"])-expected_P) == 0
            assert [s.Rational(v) for v in row["P"]] == s.Poly(expected_P, RHO).all_coeffs()
            profile = parse(row["profile"])
            value, ode = profile, profile**2/2
            for coefficient in reversed(s.Poly(expected_P, RHO).all_coeffs()):
                ode += coefficient*value
                value = derivative(value)
            assert s.expand(ode) == 0
            first = next(n for n in range(1, p+1) if expected_A.subs(RHO, n) != 0)
            assert expected_P.subs(RHO, first) == 0
        counts[p] = len(real)
        print("p=%s: all %s real pairs recovered exactly; each is rational and satisfies the ODE." % (p, len(real)), flush=True)
    return counts


if __name__ == "__main__":
    verify()
