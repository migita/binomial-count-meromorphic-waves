"""Exact substitutions and reconstruction checks for the manuscript.

Run with Python 3 and SymPy. The optional Singular input proves the full
order-five count separately; this script does not label the general
rigidity or simplicity conjecture as proved.
"""
import argparse
import json
from functools import lru_cache
from math import factorial
from pathlib import Path

import sympy as s

HERE = Path(__file__).resolve().parent
X, Q, Z = s.symbols("rho Q z")
WX, WY, G2, G3 = s.symbols("X Y g2 g3")


@lru_cache(None)
def power_sum(k):
    # Sum n^k for 1 <= n < rho, as an exact polynomial in rho.
    return s.expand((s.bernoulli(k + 1, X) - s.bernoulli(k + 1, 0)) / (k + 1)
                    - int(k == 0))


def discrete(A):
    A = s.Poly(A, X)
    out = 0
    for (i,), ai in A.terms():
        for (j,), aj in A.terms():
            out += ai * aj * sum(
                (-1) ** k * s.binomial(j, k) * X ** (j - k) * power_sum(i + k)
                for k in range(j + 1)
            )
    return s.expand(out)


def continuous(A):
    A = s.Poly(A, X)
    return s.expand(sum(
        ai * aj * s.Rational(factorial(i) * factorial(j), factorial(i + j + 1))
        * X ** (i + j + 1)
        for (i,), ai in A.terms() for (j,), aj in A.terms()
    ))


def dq(f):
    return s.expand(Q * (1 - Q) * s.diff(f, Q))


def operator(P, f, derivation=dq):
    P = s.Poly(P, X)
    derivatives = [f]
    for j in range(P.degree()):
        derivatives.append(derivation(derivatives[-1]))
    return s.expand(sum(P.nth(j) * derivatives[j] for j in range(P.degree() + 1)))


def wred(f):
    return s.rem(s.expand(f), WY ** 2 - 4 * WX ** 3 + G2 * WX + G3, WY)


def wd(f):
    return wred(s.diff(f, WX) * WY + s.diff(f, WY) * (6 * WX ** 2 - G2 / 2))


def wd_power(f, n):
    for unused in range(n):
        f = wd(f)
    return f


def universal_formula_checks():
    rows = []
    for d in range(1, 5):
        a = s.symbols(f"a0:{d}")
        A = X ** d + sum(a[j] * X ** j for j in range(d))
        S = discrete(A)
        w = operator(A, Q)
        assert s.expand(w ** 2 + operator(S, Q)) == 0
        assert s.Poly(S, X).LC() == s.Rational(factorial(d) ** 2, factorial(2 * d + 1))
        assert s.expand(S.subs(X, 0) + A.subs(X, 0) ** 2) == 0
        quotient, remainder = s.div(S, A, X)
        assert s.expand(remainder.subs(X, 0) + A.subs(X, 0)
                        * (A.subs(X, 0) + quotient.subs(X, 0))) == 0
        H = continuous(A)
        # Independent direct integral for the continuous transform.
        t = s.Symbol("t")
        direct = s.integrate(A.subs(X, t) * A.subs(X, X - t), (t, 0, X))
        assert s.expand(H - direct) == 0
        # Leading-term comparison used in the all-order injectivity proof.
        # This finite replay audits the formula; the proof is in the text.
        delta = s.Symbol("delta")
        for e in range(d):
            difference = s.Poly(S - discrete(A - delta * X ** e), X)
            cross_beta = s.Rational(factorial(e) * factorial(d),
                                    factorial(e + d + 1))
            assert difference.degree() == e + d + 1
            assert s.expand(difference.LC() - 2 * delta * cross_beta) == 0
            assert 2 * cross_beta > s.Rational(factorial(d) ** 2, factorial(2 * d + 1))
        rows.append({"degree": d, "discrete_square_identity": True,
                     "continuous_integral_identity": True,
                     "injectivity_leading_difference_degrees_checked": list(range(d))})
    return rows


def energy_checks():
    rows = []
    for p in (2, 4, 6, 8, 10):
        m = p // 2
        jets = s.symbols(f"v0:{p + 1}")
        parameters = s.symbols(f"b0:{m}")

        def B(j):
            return sum((-1) ** ell * jets[ell + 1] * jets[2 * j - 1 - ell]
                       for ell in range(j - 1)) + s.Rational((-1) ** (j - 1), 2) * jets[j] ** 2

        energy = B(m) + sum(parameters[j] * B(j) for j in range(1, m))
        energy += parameters[0] * jets[0] ** 2 / 2 + jets[0] ** 3 / 6
        derivative = sum(s.diff(energy, jets[j]) * jets[j + 1] for j in range(p))
        E = jets[p] + sum(parameters[j] * jets[2 * j] for j in range(m)) + jets[0] ** 2 / 2
        assert s.expand(derivative - jets[1] * E) == 0
        n = s.Symbol("n")
        pole = -2 * s.Rational(factorial(2 * p - 1), factorial(p - 1))
        indicial = s.prod(n - j for j in range(p, 2 * p)) + pole
        assert indicial.subs(n, 3 * p) == 0
        slope = -p * pole * s.diff(indicial, n).subs(n, 3 * p)
        assert slope > 0
        if p == 2:
            assert slope == 168
        if p == 4:
            assert slope == 7163520
        rows.append({"order": p, "energy_identity": True, "energy_slope": str(slope)})
    return rows


def elliptic_family_checks():
    """Reconstruct the elimination and the nodal coefficient change.

    These finite checks audit the formulas used by the uniform proof.
    They are not an all-degree proof of rigidity.
    """
    rows = []
    for p in range(2, 5):
        sp = s.Integer(2 * factorial(2 * p - 1)) / factorial(p - 1) ** 2
        profile_vars = s.symbols(f"u0:{p - 2}")
        background = s.Symbol("background")
        variables = tuple(profile_vars) + (background,)
        operator_vars = s.symbols(f"op0:{p}")
        P = X ** p + sum(operator_vars[j] * X ** j for j in range(p))
        V = -sp * wd_power(WX, p - 2) + background
        V += sum(profile_vars[j] * wd_power(WX, j) for j in range(p - 2))
        R = wred(operator(P, V, wd) + V ** 2 / 2)
        pivots = []
        for k in range(2 * p - 1, p - 1, -1):
            monomial = WX ** (k // 2) if k % 2 == 0 else WX ** ((k - 3) // 2) * WY
            coefficient = s.Poly(R, WX, WY).coeff_monomial(monomial)
            new_var = operator_vars[k - p]
            pivot = s.diff(coefficient, new_var)
            assert pivot.is_Rational and pivot != 0
            assert s.diff(coefficient, new_var, 2) == 0
            value = s.expand(-coefficient.subs(new_var, 0) / pivot)
            R = s.expand(R.subs(new_var, value))
            pivots.append(str(pivot))
        assert not set(operator_vars).intersection(R.free_symbols)
        weights = dict(zip(profile_vars, range(p - 2, 0, -1)))
        weights[background] = p
        weights[G2], weights[G3] = 4, 6
        residual_weights = []
        for (i, j), coefficient in s.Poly(R, WX, WY).terms():
            pole_order = 2 * i + 3 * j
            assert pole_order <= p - 1 and pole_order != 1
            target_weight = 2 * p - pole_order
            all_variables = variables + (G2, G3)
            for exponents, unused in s.Poly(coefficient, *all_variables).terms():
                assert sum(e * weights[v] for e, v in zip(exponents, all_variables)) == target_weight
            leading = sum(
                cc * s.prod(v ** e for v, e in zip(variables, exponents))
                for exponents, cc in s.Poly(coefficient, *variables).terms()
                if sum(e * weights[v] for e, v in zip(exponents, variables)) == target_weight
            )
            assert s.expand(leading - coefficient.subs({G2: 0, G3: 0})) == 0
            residual_weights.append(target_weight)
        assert sorted(residual_weights) == list(range(p + 1, 2 * p - 1)) + [2 * p]
        length = s.Rational(s.prod(residual_weights), s.prod(weights[v] for v in variables))
        assert length == 2 * s.binomial(2 * p - 2, p - 2)

        nodal_X = Q ** 2 - Q + s.Rational(1, 12)
        nodal_Y = (2 * Q - 1) * Q * (1 - Q)
        node = {G2: s.Rational(1, 12), G3: -s.Rational(1, 216),
                WX: nodal_X, WY: nodal_Y}
        assert s.expand((WY ** 2 - 4 * WX ** 3 + G2 * WX + G3).subs(node)) == 0
        assert s.expand(dq(nodal_X) - nodal_Y) == 0
        assert s.expand(dq(nodal_Y) - 6 * nodal_X ** 2 + s.Rational(1, 24)) == 0
        pulse_vars = s.symbols(f"pulse1:{p - 1}")
        A = X ** (p - 1) + sum(pulse_vars[j - 1] * X ** j for j in range(1, p - 1))
        beta = s.Symbol("endpoint")
        v = sp * operator(A, Q)
        assert v.subs(Q, 0) == v.subs(Q, 1) == 0
        coefficient_change = s.solve(s.Poly(s.expand(V.subs(node) - beta - v), Q).all_coeffs(),
                                     variables, dict=True)
        assert len(coefficient_change) == 1
        change = coefficient_change[0]
        determinant = s.Matrix([change[t] for t in variables]).jacobian(tuple(pulse_vars) + (beta,)).det()
        assert determinant.is_Rational and determinant != 0
        assert s.expand(V.subs(node).subs(change) - beta - v) == 0
        residual = operator(P, beta + v) + (beta + v) ** 2 / 2
        predicted = beta * operator_vars[0] + beta ** 2 / 2
        predicted += sp * operator((P + beta) * A - sp * discrete(A) / 2, Q)
        assert s.expand(residual - predicted) == 0
        rows.append({"order": p, "elimination_pivots": pivots,
                     "variable_weights": [weights[v] for v in variables],
                     "equation_weights": sorted(residual_weights),
                     "elliptic_length": int(length),
                     "nodal_coefficient_change_determinant": str(determinant),
                     "nodal_matching_identity": True})
    return rows


def order_two():
    a, a0, a1, background = s.symbols("a a0 a1 background")
    A = X + a
    quotient, remainder = s.div(discrete(A), A, X)
    P = X ** 2 + 5 * a * X + a ** 2 - 6 * a - 1
    assert s.expand(6 * quotient - P) == 0
    assert s.expand(remainder + a * (a - 1) * (a + 1) / 6) == 0
    v = 12 * ((a + 1) * Q - Q ** 2)
    assert s.expand(12 * operator(A, Q) - v) == 0
    for value in (-1, 0, 1):
        assert s.diff(remainder, a).subs(a, value) != 0
        assert s.expand(operator(P.subs(a, value), v.subs(a, value))
                        + v.subs(a, value) ** 2 / 2) == 0
    V = -12 * WX + background
    R = wred(operator(X ** 2 + a1 * X + a0, V, wd) + V ** 2 / 2)
    target = -12 * a1 * WY - 12 * (a0 + background) * WX
    target += 6 * G2 + a0 * background + background ** 2 / 2
    assert s.expand(R - target) == 0
    assert s.expand(R.subs({a1: 0, background: -a0}) - (12 * G2 - a0 ** 2) / 2) == 0

    # Restore the coefficients of the integrated physical equation.
    delta, kappa, speed = s.symbols("delta kappa speed")
    astar = a ** 2 - 6 * a - 1
    equilibrium = speed + delta * kappa ** 2 * astar
    u = equilibrium + delta * kappa ** 2 * v
    nu = delta * kappa * 5 * a
    integration_constant = speed * equilibrium - equilibrium ** 2 / 2
    physical = delta * kappa ** 2 * dq(dq(u)) + nu * kappa * dq(u)
    physical += -speed * u + u ** 2 / 2 + integration_constant
    assert s.expand(physical - delta ** 2 * kappa ** 4
                    * (operator(P, v) + v ** 2 / 2)) == 0

    # Algebraic check of the bounded Jacobi representation at g2=1/12,g3=0.
    sn = s.Symbol("sn")
    aa = 1 / (4 * s.sqrt(3))
    xx = -aa + aa * sn ** 2
    xxprime2 = (2 * aa * sn) ** 2 * (2 * aa) * (1 - sn ** 2) * (1 - sn ** 2 / 2)
    assert s.simplify(xxprime2 - (4 * xx ** 3 - xx / 12)) == 0
    assert s.simplify(-12 * xx + 1 - (1 + s.sqrt(3) * (1 - sn ** 2))) == 0
    nodal_X = Q ** 2 - Q + s.Rational(1, 12)
    assert s.expand(-12 * nodal_X + 1 - 12 * Q * (1 - Q)) == 0
    return {"rational_exponential_pairs": 3, "all_simple": True,
            "elliptic_length": 2, "elliptic_generic_points": 2,
            "elliptic_g2_zero_multiplicities": [2],
            "physical_scaling_verified": True, "Jacobi_and_nodal_profiles_verified": True}


def order_three():
    a, b = s.symbols("a b")
    A = X ** 2 + a * X + b
    S = discrete(A)
    quot, rem = s.div(S, A, X)
    P = X ** 3 + 4 * a * X ** 2 + (a ** 2 + 19 * b) * X - a ** 3 + 7 * a * b - 5 * a - 30 * b
    E0 = a * b * (a ** 2 - 7 * b + 5)
    E1 = a ** 4 - 8 * a ** 2 * b + 11 * b ** 2 + 10 * b - 1
    assert s.expand(30 * quot - P) == 0
    assert s.expand(30 * rem - E1 * X - E0) == 0
    f = 2 * Q ** 3 - (a + 3) * Q ** 2 + (a + b + 1) * Q
    assert s.expand(operator(A, Q) - f) == 0
    jac = s.Matrix([E0, E1]).jacobian((a, b)).det()
    points = [(1, 0, -24), (-1, 0, -24), (s.I, 0, -16), (-s.I, 0, -16),
              (0, -1, 144), (0, s.Rational(1, 11), s.Rational(576, 121)),
              (3, 2, -144), (-3, 2, -144), (4, 3, 384), (-4, 3, 384)]
    for aa, bb, jj in points:
        rule = {a: aa, b: bb}
        assert E0.subs(rule) == E1.subs(rule) == 0
        assert s.simplify(jac.subs(rule) - jj) == 0
        v = 60 * f.subs(rule)
        assert s.expand(operator(P.subs(rule), v) + v ** 2 / 2) == 0
    # Published six-case tables, with the signs of nonzero dispersion identified.
    # Kudryashov--Zargaryan (1996), Table 1: (sigma^2, S).
    kz_table = {
        (s.Integer(0), -s.Rational(11, 38)),
        (s.Integer(0), s.Rational(1, 38)),
        (s.Rational(144, 47), -s.Rational(1, 94)),
        (s.Rational(256, 73), -s.Rational(1, 146)),
        (s.Integer(16), -s.Rational(1, 2)),
        (s.Integer(16), s.Rational(1, 2)),
    }
    # Conte--Musette (2009), Table 1: (B^2/mu, K/mu^3, k^2/mu), nu=k=1.
    cm_table = {
        (s.Integer(0), -s.Rational(4950, 19 ** 3), s.Rational(11, 19)),
        (s.Integer(0), s.Rational(450, 19 ** 3), -s.Rational(1, 19)),
        (s.Rational(144, 47), -s.Rational(1800, 47 ** 3), s.Rational(1, 47)),
        (s.Rational(256, 73), -s.Rational(4050, 73 ** 3), s.Rational(1, 73)),
        (s.Integer(16), s.Integer(-18), s.Integer(1)),
        (s.Integer(16), s.Integer(-8), s.Integer(-1)),
    }
    kz_observed, cm_observed = [], []
    for aa, bb, unused in points:
        pp = s.Poly(P.subs({a: aa, b: bb}), X)
        mu_value, B_value, a0_value = pp.nth(1), pp.nth(2), pp.nth(0)
        ratio = s.simplify(B_value ** 2 / mu_value)
        kz_observed.append((ratio, -1 / (2 * mu_value)))
        cm_observed.append((ratio, s.simplify(-a0_value ** 2 / (2 * mu_value ** 3)),
                            1 / mu_value))
    assert set(kz_observed) == kz_table
    assert set(cm_observed) == cm_table
    for row in kz_table:
        assert kz_observed.count(row) == (1 if row[0] == 0 else 2)
    B, mu, K = s.symbols("B mu K")
    w = -60 * WY - 15 * B * WX - B ** 3 / 64
    R = wred(wd_power(w, 3) + B * wd_power(w, 2) + mu * wd(w) + w ** 2 / 2 + K)
    rule = {mu: B ** 2 / 16, G2: B ** 4 / 3072,
            G3: (K + 13 * B ** 6 / 4096) / 1080}
    assert s.expand(R.subs(rule)) == 0
    a0, uu, bb, a2, a1 = s.symbols("a0 uu bb a2 a1")
    generic_V = -60 * WY + uu * WX + bb
    generic_R = wred(operator(X ** 3 + a2 * X ** 2 + a1 * X + a0, generic_V, wd)
                     + generic_V ** 2 / 2)
    assert s.Poly(generic_R, WX, WY).coeff_monomial(WX * WY) == -48 * uu - 720 * a2
    after_a2 = s.expand(generic_R.subs(a2, -uu / 15))
    assert s.Poly(after_a2, WX, WY).coeff_monomial(WX ** 2) == uu ** 2 / 10 - 360 * a1
    after_a1 = s.expand(after_a2.subs(a1, uu ** 2 / 3600))
    assert s.Poly(after_a1, WX, WY).coeff_monomial(WY) == uu ** 3 / 3600 - 60 * bb - 60 * a0
    V = -60 * WY - 15 * B * WX - B ** 3 / 64 - a0
    R = wred(operator(X ** 3 + B * X ** 2 + B ** 2 * X / 16 + a0, V, wd) + V ** 2 / 2)
    F1 = B ** 4 - 3072 * G2
    F2 = a0 ** 2 - 13 * B ** 6 / 2048 + 2160 * G3
    assert s.expand(R - s.Rational(15, 64) * F1 * WX
                    + s.Rational(25, 8192) * B ** 2 * F1 + F2 / 2) == 0
    jac_elliptic = s.Matrix([F1, F2]).jacobian((B, a0)).det()
    assert jac_elliptic == 8 * B ** 3 * a0
    jj = 1728 * G2 ** 3 / (G2 ** 3 - 27 * G3 ** 2)
    assert s.cancel(jj.subs({G2: B ** 4 / 3072, G3: 13 * B ** 6 / 4423680}) + 300) == 0
    special = {G2: s.Rational(1, 12), G3: s.Rational(13, 1080)}
    assert jj.subs(special) == -300
    special_multiplicities = []
    for root in (4, -4, 4 * s.I, -4 * s.I):
        assert F1.subs(special).subs(B, root) == 0
        assert s.diff(F1, B).subs(B, root) != 0
        rhs = s.expand((13 * B ** 6 / 2048 - 2160 * G3).subs(special).subs(B, root))
        if root in (4, -4):
            assert rhs == 0
            special_multiplicities.append(2)
        else:
            assert rhs == -52
            special_multiplicities.extend((1, 1))
    zero_g2 = s.groebner([F1.subs({G2: 0, G3: 1}), F2.subs({G2: 0, G3: 1})],
                         B, a0, order="lex")
    assert [g.as_expr() for g in zero_g2.polys] == [B ** 4, a0 ** 2 + 2160]
    # At each exponential point, residue zero occurs exactly for the four pulses.
    for aa, bbvalue, unused in points:
        PP = s.Poly(P.subs({a: aa, b: bbvalue}), X)
        residue_condition = PP.nth(2) ** 2 - 16 * PP.nth(1)
        assert s.simplify(residue_condition + 304 * bbvalue) == 0
        if bbvalue == 0:
            elliptic_g2 = PP.nth(2) ** 4 / 3072
            elliptic_g3 = (-PP.nth(0) ** 2 / 2 + 13 * PP.nth(2) ** 6 / 4096) / 1080
            assert s.simplify(elliptic_g2 - s.Rational(1, 12)) == 0
            assert s.simplify(elliptic_g3 + s.Rational(1, 216)) == 0
    alpha, gamma, beta, delta, lam = s.symbols("alpha gamma beta delta lam")
    vessel = ((gamma - beta) / (2 * alpha)) ** 2 - 16 * (delta / (2 * alpha)) * (-lam / (2 * alpha))
    assert s.expand(4 * alpha ** 2 * vessel - (gamma - beta) ** 2 - 16 * delta * lam) == 0
    return {"points": 10, "real_points": 8, "real_fronts": 6, "real_pulses": 2,
            "all_jacobians_nonzero": True, "KS_elliptic_identity": True,
            "Kudryashov_Zargaryan_1996_table_1_verified": True,
            "Conte_Musette_2009_table_1_verified": True,
            "classical_six_cases_with_signs_restored_give_ten_pairs": True,
            "elliptic_scheme_exact_elimination": True, "elliptic_length": 8,
            "elliptic_exceptional_j": [0, -300],
            "elliptic_j_minus_300_multiplicities": special_multiplicities,
            "elliptic_j_zero_multiplicities": [4, 4],
            "exponential_operators_have_only_singular_elliptic_invariants": True,
            "vessel_parameter_identity": True}


def order_four():
    a0, b, c = s.symbols("a0 b c")
    A = X ** 3 + c * X
    quotient, remainder = s.div(discrete(A), A, X)
    P = X ** 4 + 13 * c * X ** 2 + (31 * c ** 2 - 70 * c + 7) / 3
    factor = (c + 1) * (31 * c ** 2 - 31 * c + 10)
    assert s.expand(140 * quotient - P) == 0
    assert s.expand(remainder + X * factor / 420) == 0
    v_exp = 280 * (1 + c) * Q * (1 - Q) - 1680 * Q ** 2 * (1 - Q) ** 2
    assert s.expand(v_exp - 280 * operator(A, Q)) == 0
    assert s.gcd(s.Poly(factor, c), s.Poly(s.diff(factor, c), c)).degree() == 0
    for value in (-1, s.Rational(1, 2) + 3 * s.I / (2 * s.sqrt(31)),
                  s.Rational(1, 2) - 3 * s.I / (2 * s.sqrt(31))):
        assert s.simplify(factor.subs(c, value)) == 0
    # Demina--Kudryashov (2010), equation (31): their parameter is 1/c.
    for kappa_dk in (-s.Integer(1), (31 + 3 * s.I * s.sqrt(31)) / 20,
                     (31 - 3 * s.I * s.sqrt(31)) / 20):
        assert s.simplify(factor.subs(c, 1 / kappa_dk)) == 0
    residual_exp = s.Poly(operator(P, v_exp) + v_exp ** 2 / 2, Q)
    assert all(s.rem(co, factor, c) == 0 for co in residual_exp.all_coeffs())
    assert s.expand(P.subs(c, -1) - (X ** 2 - 4) * (X ** 2 - 9)) == 0

    # Recover the entire even-family elliptic scheme by triangular elimination.
    yy, dd, ee = s.symbols("yy dd ee")
    Vgeneric = -1680 * WX ** 2 + yy * WY + dd * WX + ee
    Rgeneric = wred(operator(X ** 4 + b * X ** 2 + a0, Vgeneric, wd) + Vgeneric ** 2 / 2)
    pivot_odd = s.Poly(Rgeneric, WX, WY).coeff_monomial(WX ** 2 * WY)
    assert pivot_odd == -1320 * yy
    Reven = s.expand(Rgeneric.subs(yy, 0))
    leading = s.Poly(Reven, WX, WY).coeff_monomial(WX ** 3)
    assert s.solve(leading, dd) == [-280 * b / 13]
    next_coefficient = s.Poly(Reven.subs(dd, -280 * b / 13), WX, WY).coeff_monomial(WX ** 2)
    assert s.solve(next_coefficient, ee) == [-a0 + 168 * G2 + 31 * b ** 2 / 507]
    V = -1680 * WX ** 2 - 280 * b * WX / 13 + 168 * G2 + 31 * b ** 2 / 507 - a0
    R = wred(operator(X ** 4 + b * X ** 2 + a0, V, wd) + V ** 2 / 2)
    F = 31 * b ** 3 - 42588 * b * G2 - 4745520 * G3
    H = 23184 * G2 ** 2 + s.Rational(7980, 169) * b ** 2 * G2
    H += s.Rational(101520, 13) * b * G3
    assert s.expand(R + s.Rational(280, 6591) * F * WX
                    - (H - a0 ** 2 + s.Rational(31, 257049) * b * F) / 2) == 0
    cubic = s.Poly(F.subs({G2: 1, G3: 0}), b)
    rhs = s.Poly(H.subs({G2: 1, G3: 0}), b)
    assert s.gcd(cubic, cubic.diff()).degree() == 0
    assert s.gcd(cubic, rhs).degree() == 0

    # Demina--Kudryashov (2010), equations (23), (25), with b=-beta.
    old_g3 = s.Rational(7, 780) * (-b) * G2 - 31 * (-b) ** 3 / 4745520
    assert s.expand(F.subs(G3, old_g3)) == 0
    old_a0square = 23184 * (G2 ** 2 - b ** 2 * G2 / 1014
                           + s.Rational(1457, 662158224) * b ** 4)
    assert s.expand(H.subs(G3, old_g3) - old_a0square) == 0
    w0, C0, C1, wvar, beta = s.symbols("w0 C0 C1 w beta")
    old_profile = 280 * WX ** 2 - s.Rational(140, 39) * beta * WX + C0 / 6
    old_profile -= s.Rational(31, 3042) * beta ** 2 + 28 * G2
    assert s.expand(-6 * (old_profile - w0) - V.subs({b: -beta, a0: C0 - 6 * w0})) == 0
    assert s.expand((C0 - 6 * w0) ** 2 - C0 ** 2 - 12 * C1
                    - 12 * (3 * w0 ** 2 - C0 * w0 - C1)) == 0

    v = -1680 * WX ** 2 + 168 * G2 - a0
    R = wred(wd_power(v, 4) + a0 * v + v ** 2 / 2)
    target = 201600 * G3 * WX + 11592 * G2 ** 2 - a0 ** 2 / 2
    assert s.expand(R - target) == 0
    for sign in (-1, 1):
        assert s.simplify(R.subs({G3: 0, G2: sign * a0 / (12 * s.sqrt(161))})) == 0
    wp = Z ** -2 + G2 * Z ** 2 / 20 + G2 ** 2 * Z ** 6 / 1200 + G2 ** 3 * Z ** 10 / 156000
    assert s.expand(-1680 * wp ** 2).coeff(Z, 8) == -21 * G2 ** 3 / 130
    sn = s.Symbol("sn")
    xx = (sn ** 2 - 1) / 2
    xxprime2 = sn ** 2 * (1 - sn ** 2) * (1 - sn ** 2 / 2)
    assert s.expand(xxprime2 - (4 * xx ** 3 - xx)) == 0
    # The mixed fourth-order datum mentioned in the open-questions paragraph.
    Pmixed = s.Poly((X + 2) * (X + 3) * ((X + 3) ** 2 + 1), X)
    h = s.Symbol("h")
    co = [s.Integer(-1680)]
    for n in range(1, 13):
        pivot = s.prod(n - j for j in range(4, 8)) - 1680
        forcing = -sum(
            Pmixed.nth(j) * s.ff(n - 8 + j, j) * co[n - 4 + j]
            for j in range(4) if n - 4 + j >= 0
        ) - sum(co[k] * co[n - k] for k in range(1, n)) / s.Integer(2)
        if n == 12:
            assert pivot == 0 and forcing == 0
            co.append(h)
        else:
            co.append(s.cancel(forcing / pivot))
    ss, tt = s.symbols("s t")
    quadratic_symbol, symbol_rem = s.div(
        ((ss + 2) * Pmixed.as_expr().subs(X, tt)
         + (tt + 2) * Pmixed.as_expr().subs(X, ss)) / 2,
        ss + tt + 6, ss,
    )
    assert s.expand(symbol_rem) == 0
    jets = s.symbols("v0:5")
    quadratic = sum(c * jets[i] * jets[j]
                    for (i, j), c in s.Poly(quadratic_symbol, ss, tt).terms())
    J = quadratic + jets[0] ** 3 / 6
    DJ = sum(s.diff(J, jets[i]) * jets[i + 1] for i in range(4))
    E = sum(Pmixed.nth(i) * jets[i] for i in range(5)) + jets[0] ** 2 / 2
    assert s.expand(DJ + 6 * J - (jets[1] + 2 * jets[0]) * E) == 0
    laurent = sum(co[n] * Z ** (n - 4) for n in range(13))
    evaluated = s.expand(J.subs({jets[i]: s.diff(laurent, Z, i) for i in range(4)}))
    Jconstant = evaluated.coeff(Z, 0)
    assert s.diff(Jconstant, h) == 7163520
    assert Jconstant.subs(h, 0) == -s.Rational(74483523366508697, 30859192310661)
    return {"even_family_rational_exponential_pairs": 3, "all_three_simple": True,
            "even_family_elliptic_length": 6, "generic_six_simple": True,
            "elliptic_scheme_exact_elimination": True, "2010_normalization_verified": True,
            "2010_three_period_parameters_verified": True,
            "b_zero_Weierstrass_residual": str(target), "two_nonsingular_choices_at_b_zero": True,
            "marked_coefficient_checked": True, "Jacobi_representation_checked": True,
            "mixed_test_resonance_obstruction": 0,
            "mixed_test_Darboux_identity_verified": True,
            "mixed_test_Darboux_constant_at_h_zero": str(Jconstant.subs(h, 0))}




def fisher():
    t, lam = s.symbols("t lam")
    U = s.Function("U")(t)

    def D(f):
        return lam * t * s.diff(f, t)

    f = t ** 2 * U
    assert s.expand(D(D(f)) - 5 * lam * D(f) + 6 * lam ** 2 * f
                    - lam ** 2 * t ** 4 * s.diff(U, t, 2)) == 0
    v = -12 * lam ** 2 * f
    R = s.expand(D(D(v)) - 5 * lam * D(v) + 6 * lam ** 2 * v + v ** 2 / 2)
    assert s.expand(R.subs(s.diff(U, t, 2), 6 * U ** 2)) == 0
    return {"elliptic_exponential_identity_verified": True}


def p5_input():
    variables = s.symbols("a1:5")
    A = X ** 4 + sum(variables[j - 1] * X ** (4 - j) for j in range(1, 5))
    R = s.Poly(s.rem(discrete(A), A, X), X)
    equations = []
    for k in range(4):
        poly = s.Poly(R.nth(k), *variables, domain=s.QQ)
        poly = poly.clear_denoms()[1].primitive()[1]
        equations.append(poly.as_expr())
    return "\n".join([
        "// Generated directly from the discrete convolution; all arithmetic is rational.",
        "ring r=0,(a1,a2,a3,a4),dp;",
        "short=0;",
        "option(redSB);",
        "ideal I=" + ",\n".join(str(f).replace("**", "^") for f in equations) + ";",
        "ideal G=std(I);",
        'print("DIMENSION");print(dim(G));',
        'print("LENGTH");print(vdim(G));',
        "matrix J=jacob(I);",
        "ideal singularLocus=std(G+ideal(det(J)));",
        'print("ALL_SIMPLE");print(reduce(1,singularLocus)==0);',
        "quit;",
        "",
    ])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--write-inputs", action="store_true")
    args = parser.parse_args()
    report = {
        "universal_rigidity_claimed": False,
        "universal_simplicity_claimed": False,
        "generic_identities": universal_formula_checks(),
        "energy_identities": energy_checks(),
        "elliptic_family": elliptic_family_checks(),
        "order_two": order_two(),
        "order_three": order_three(),
        "order_four": order_four(),
        "Fisher": fisher(),
    }
    content = p5_input()
    path = HERE / "p5_count.sing"
    if args.write_inputs:
        path.write_text(content)
    assert path.read_text() == content, "p5_count.sing differs from the reconstructed input"
    (HERE / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
    print("All manuscript identities and input reconstructions passed.")
    print("The full p=5 count is verified separately by p5_count.sing.")
    print("The general rigidity and simplicity conjectures remain open.")


if __name__ == "__main__":
    main()
