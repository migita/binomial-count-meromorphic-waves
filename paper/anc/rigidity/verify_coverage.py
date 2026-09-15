"""Replay the finite degree-72 rigidity certificate using only SymPy.

The mathematical reduction is in proof.pdf / proof.tex. All residual degrees,
integer identities, prime certificates and original convolution coefficients
for the 72 chosen degrees are checked.
"""
import json
from fractions import Fraction
from functools import lru_cache
from math import factorial, gcd, lcm
from pathlib import Path

import sympy as s

HERE = Path(__file__).resolve().parent
X = s.Symbol("x")


def falling(x, n):
    result = 1
    for j in range(n):
        result *= x - j
    return result


def weight(gap, i, j):
    delta = s.Rational(gap - 1, 2)
    return s.Rational(falling(gap, i + j), falling(delta, i) * falling(delta, j))


def residual_system(gap, degree):
    a = s.symbols(f"a1:{degree + 1}")
    coeffs = (s.Integer(1),) + a
    C = sum(coeffs[i] * X ** (degree - i) for i in range(degree + 1))
    kernel = sum(weight(gap, i, j) * coeffs[i] * coeffs[j] * X ** (gap - i - j)
                 for i in range(degree + 1) for j in range(degree + 1)
                 if i + j <= gap)
    R = s.Poly(s.rem(kernel, C, X), X)
    variables = a[:-1]
    equations, scales = [], []
    for j in range(degree):
        f = s.expand(R.nth(j).subs(a[-1], 1))
        if f == 0:
            continue
        co = s.Poly(f, *variables, domain=s.QQ).coeffs() if variables else [f]
        den = lcm(*(int(s.denom(c)) for c in co))
        equations.append(s.expand(den * f))
        scales.append(den)
    return variables, equations, scales


def prime_certificate(n, catalog, checked):
    n = int(n)
    if n in checked:
        return
    data = catalog[str(n)]
    if n == 2:
        assert data.get("base_prime") is True
        checked.add(n)
        return
    assert n > 2 and n % 2
    factors = {int(q): int(e) for q, e in data["predecessor_factors"].items()}
    assert factors and all(q >= 2 and e >= 1 for q, e in factors.items())
    assert s.prod(q ** e for q, e in factors.items()) == n - 1
    for q in factors:
        prime_certificate(q, catalog, checked)
    a = int(data["lucas_witness"])
    assert 1 < a < n and pow(a, n - 1, n) == 1
    for q in factors:
        assert gcd(pow(a, (n - 1) // q, n) - 1, n) == 1
    checked.add(n)


def verify_residual_certificate(record):
    gap = int(record["gap"])
    assert gap in (2, 4, 6) and len(record["strata"]) == gap
    checked, excluded = set(), set()
    monomials = 0
    for degree, entry in enumerate(record["strata"], 1):
        assert entry["degree"] == degree
        variables, equations, scales = residual_system(gap, degree)
        names = {str(a): a for a in variables}
        saved = [s.sympify(f, locals=names) for f in entry["equations"]]
        assert len(saved) == len(equations)
        assert all(s.expand(a - b) == 0 for a, b in zip(saved, equations))
        assert scales == entry["equation_denominator_scales"]
        D = int(entry["identity_constant"])
        assert D > 0
        U = [s.sympify(f, locals=names) for f in entry["integral_multipliers"]]
        assert len(U) == len(equations)
        for f in U:
            if variables:
                poly = s.Poly(f, *variables, domain=s.ZZ)
                monomials += len(poly.terms()) if not poly.is_zero else 0
            else:
                assert s.Rational(f).q == 1
                monomials += int(f != 0)
        assert s.expand(sum(u * f for u, f in zip(U, equations)) - D) == 0
        covered = lcm(D, *scales)
        factors = {int(q): int(e) for q, e in entry["excluded_prime_factors"].items()}
        assert all(e >= 1 for e in factors.values())
        assert s.prod(q ** e for q, e in factors.items()) == covered
        for q in factors:
            prime_certificate(q, record["primality_certificates"], checked)
        excluded.update(factors)
    assert sorted(excluded) == record["all_excluded_prime_factors"]
    assert sorted(q for q in excluded if q > gap) == record["relevant_excluded_primes"]
    return excluded, {"gap": gap, "all_residual_degrees": gap,
                      "integer_multiplier_monomials": monomials,
                      "certified_primes": len(checked)}


@lru_cache(None)
def beta(i, j):
    return Fraction(factorial(i) * factorial(j), factorial(i + j + 1))


def residue(c, p):
    c = Fraction(c)
    assert c.denominator % p
    return c.numerator * pow(c.denominator, -1, p) % p


def coefficient_congruence(d, p, e, gap):
    P = p ** e
    assert 2 * d + 1 == P + gap and gap in (0, 2, 4, 6) and 0 <= gap < p
    u = residue(P * beta(d, d), p)
    assert u != 0
    expected_weights = {}
    if gap:
        for r in range(gap + 1):
            for t in range(gap + 1 - r):
                expected_weights[r, t] = residue(weight(gap, r, t), p)
    checked = 0
    for i in range(d + 1):
        for j in range(d + 1):
            actual = residue(P * beta(i, j), p)
            r, t = d - i, d - j
            predicted = 0
            if r + t <= gap:
                predicted = u if gap == 0 else u * expected_weights[r, t] % p
            assert actual == predicted
            checked += 1
    return checked


def main():
    record = json.loads((HERE / "certificate.json").read_text())
    assert record["gap"] == 6 and not record["all_degree_rigidity_proved"]
    assert set(record["supporting_gap_certificates"]) == {"2", "4"}
    exclusions, reports = {}, []
    for gap in (2, 4, 6):
        data = record if gap == 6 else record["supporting_gap_certificates"][str(gap)]
        exclusions[gap], report = verify_residual_certificate(data)
        reports.append(report)
    coverage = record["conservative_arithmetic_coverage"]
    assert coverage["covered_through"] == 72
    assert len(coverage["rows"]) == 72
    primes, coefficient_checks = set(), 0
    for d, row in enumerate(coverage["rows"], 1):
        assert row["degree"] == d
        p, e, gap = int(row["prime"]), int(row["exponent"]), int(row["gap"])
        assert e >= 1 and p > max(2, gap)
        prime_certificate(p, record["primality_certificates"], primes)
        if gap:
            assert p not in exclusions[gap]
        coefficient_checks += coefficient_congruence(d, p, e, gap)
    report = {
        "consecutive_polynomial_degrees": [0, 72],
        "corresponding_ODE_orders": [2, 73],
        "universal_rigidity_proved": False,
        "simplicity_inferred_from_rigidity": False,
        "residual_certificates": reports,
        "original_ordered_bilinear_coefficients_checked": coefficient_checks,
        "all_72_degree_choices_verified": True,
    }
    (HERE / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
    print("Every residual identity, prime certificate and degree choice passed.")
    print(f"Checked {coefficient_checks} original ordered bilinear coefficients.")
    print("Rigidity verified through polynomial degree 72; ODE order 73.")
    print("No simplicity or unrestricted all-degree conclusion is asserted.")


if __name__ == "__main__":
    main()
