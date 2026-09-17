"""Exact substitution and scope regressions; run python3 -m unittest -v."""

import json
from pathlib import Path
import subprocess
import sys
import unittest

import sympy as s

from core import (DT, DX, DY, RHO, T, X, Y, UnsupportedReduction,
                  elliptic_profile, identify, parse, reduce_pde,
                  riccati_profile, solve_univariate)


HERE = Path(__file__).resolve().parent


class DictionaryTests(unittest.TestCase):
    def assert_expression(self, actual, expected):
        self.assertEqual(s.simplify(s.expand(actual-expected)), 0)

    def test_kdv_exponential_and_rational(self):
        red = reduce_pde(DT+DX**3, DX, 1)
        wave = riccati_profile(red, rate=1, background=0)
        self.assertEqual(wave["status"], "verified")
        Q = s.Symbol("Q")
        self.assert_expression(wave["profile_in_Q"], 12*Q*(1-Q))
        z = s.Symbol("z")
        rational = riccati_profile(red, "rational")["profile"].subs(T, 1/z)
        self.assert_expression(rational, 1-12/z**2)
        ode = s.diff(rational, z, 2)-rational+rational**2/2
        self.assert_expression(s.diff(ode, z), 0)

    def test_kdv_burgers_front_and_wrong_rate(self):
        red = reduce_pde(DT-5*DX**2+DX**3, DX, -6)
        wave = riccati_profile(red, rate=1, background=0)
        self.assertEqual(wave["status"], "verified")
        self.assert_expression(wave["profile_in_Q"], -12*s.Symbol("Q")**2)
        self.assertEqual(riccati_profile(red, rate=2)["status"], "no_match")
        self.assertEqual(elliptic_profile(red)["status"], "no_match")

    def test_fisher_front_has_no_free_integration_constant(self):
        red = reduce_pde(DT-DX**2-1, 2, 5/s.sqrt(6))
        wave = riccati_profile(red, rate=1/s.sqrt(6))
        self.assertEqual(wave["status"], "verified")
        Q = s.Symbol("Q")
        self.assert_expression(wave["profile_in_Q"], (1-Q)**2)
        E = s.Symbol("E")
        U = wave["profile_in_Q"].subs(Q, E/(1+E))
        dz = lambda f: s.cancel(E/s.sqrt(6)*s.diff(f, E))
        self.assert_expression(-5/s.sqrt(6)*dz(U)-dz(dz(U))-U+U**2, 0)
        self.assertEqual(riccati_profile(red, "rational")["status"], "no_match")

    def test_imaginary_rate_is_not_discarded(self):
        red = reduce_pde(DT-DX**2-1, 2, 0)
        wave = riccati_profile(red, rate=s.I)
        self.assertEqual(wave["status"], "verified")
        x = s.Symbol("x", real=True)
        U = wave["profile"].subs(T, -s.tan(x/2)/2)
        self.assert_expression(-s.diff(U, x, 2)-U+U**2, 0)

    def test_all_33_reference_pairs_reconstructed(self):
        data = json.loads((HERE/"real_pairs_p1_p4.json").read_text())
        for p, rows in data.items():
            for row in rows:
                P = parse(row["P_factored"])
                # A PDE with integrated profile P(D)U+U^2/2+K=0.
                red = reduce_pde(DX*P.subs(RHO, DX), DX, 0)
                wave = riccati_profile(red, rate=1, background=0)
                self.assertEqual(wave["status"], "verified", (p, row["A"]))
                self.assert_expression(wave["profile_in_Q"], parse(row["profile"]))

    def test_nonreal_pair_absent_from_real_catalogue(self):
        P = (RHO**2-1)*(RHO+4*s.I)
        red = reduce_pde(DX*P.subs(RHO, DX), DX, 0)
        wave = riccati_profile(red, rate=1, background=0)
        self.assertEqual(wave["status"], "verified")
        Q = s.Symbol("Q")
        expected = 120*Q**3-60*(3+s.I)*Q**2+60*(1+s.I)*Q
        self.assert_expression(wave["profile_in_Q"], expected)

    def test_higher_order_power_fronts(self):
        Q = s.Symbol("Q")
        for p in (5, 6, 8):
            P = s.prod(RHO-j for j in range(p, 2*p))
            red = reduce_pde(DX*P.subs(RHO, DX), DX, 0)
            wave = riccati_profile(red, rate=1, background=0)
            self.assertEqual(wave["status"], "verified")
            expected = (-1)**(p-1)*2*s.factorial(2*p-1)/s.factorial(p-1)*Q**p
            self.assert_expression(wave["profile_in_Q"], expected)

    def test_elliptic_kdv_and_dispersive_ks(self):
        red = reduce_pde(DT+DX**3, DX, 1)
        wave = elliptic_profile(red, 4, 1)
        self.assertEqual(wave["status"], "verified")
        self.assert_expression(wave["profile"], 1-12*X)
        red = reduce_pde(DT+DX**2+4*DX**3+DX**4, DX, 0)
        wave = elliptic_profile(red, s.Rational(1, 12), 0)
        self.assertEqual(wave["status"], "verified")
        self.assert_expression(wave["profile"], -60*X-60*Y-1)
        self.assertEqual(elliptic_profile(red, 0, 0)["status"], "no_match")
        red = reduce_pde(DT-DX**2, DX, 1)
        self.assertEqual(elliptic_profile(red)["status"], "no_match")
        red = reduce_pde(DX**5+DX, DX, 0)
        wave = elliptic_profile(red, 1, 0)
        self.assertEqual(wave["status"], "verified")
        self.assert_expression(wave["profile"], 167-1680*X**2)
        red = reduce_pde(DX**7, DX, 0)
        self.assertEqual(elliptic_profile(red, 0, 1)["status"], "verified")

    def test_plane_wave_and_degree_drop(self):
        c, k, ell, B = s.symbols("c k ell B")
        red = reduce_pde(DX*(DT+DX**3)+3*DY**2, DX**2, c, (k, ell, 0))
        self.assertEqual(red["integrations"], 2)
        self.assert_expression(red["P_about_B"], RHO**2+B/k**2-c/k**3+3*ell**2/k**4)
        # The order is recomputed after a parameter is specialized to zero.
        red = reduce_pde(DT+DX-DX**2+0*DX**5, DX, 0)
        self.assertEqual(red["order"], 1)
        with self.assertRaises(UnsupportedReduction):
            reduce_pde(DT**2+DT-DX**2+DX**4, DX**2, 1)
        with self.assertRaises(UnsupportedReduction):
            reduce_pde(DT+DX**3, DX+DX**3, 1)

    def test_normalization_primitive_period_and_background(self):
        E = s.Symbol("E")
        for expression in (4*E**2/(1+E**2)**2, 7+24*E/(1+2*E)**2):
            result = identify(expression)
            self.assertEqual(result["status"], "verified")
            self.assert_expression(result["A"], RHO)
            self.assert_expression(result["P"], RHO**2-1)
        self.assertEqual(identify(4*E**2/(1+E**2)**2)["primitive_frequency_multiplier"], 2)
        with self.assertRaises(UnsupportedReduction):
            identify(E/(1+E)**2+E/(1+2*E)**2)

    def test_exact_univariate_solve_and_unresolved_parameters(self):
        kappa, c = s.symbols("kappa c")
        red = reduce_pde(DT+DX**3, DX, 1)
        wave = riccati_profile(red, background=0)
        self.assertEqual(solve_univariate(wave, kappa)["roots"], [-1, 1])
        symbolic = riccati_profile(reduce_pde(DT+DX**3, DX, c), background=0)
        self.assertEqual(solve_univariate(symbolic, kappa)["status"], "implicit")
        polynomial = kappa**5-kappa+1
        guarded = {"status": "conditional", "conditions": [(kappa-2)*polynomial], "guards": [polynomial]}
        self.assertEqual(solve_univariate(guarded, kappa)["roots"], [2])
        a, b = s.symbols("a b")
        wave = riccati_profile(red, rate=1, background=(a-1)/b)
        self.assertTrue(any(s.simplify(g/b).is_number for g in wave["guards"] if g.has(b)))

    def test_safe_arithmetic_and_cli_errors(self):
        self.assertEqual(parse("0.1 + 1/3"), s.Rational(13, 30))
        for text in ("__import__('os')", "open('x')", "(1).__class__", "[1,2]", "1/0"):
            with self.assertRaises(ValueError):
                parse(text)
        process = subprocess.run([sys.executable, str(HERE/"dictionary.py"), "waves", "--linear", "Dt+Dx**3",
                                  "--quadratic", "Dx+Dx**3", "--json"], capture_output=True, text=True)
        self.assertEqual(process.returncode, 2)
        self.assertEqual(json.loads(process.stdout)["status"], "unsupported")


if __name__ == "__main__":
    unittest.main()
