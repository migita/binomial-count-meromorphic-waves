"""Exact checks of the statements that are read off the labels (Sections 3.4 and 6 of the paper), at the prime indices 5 (p = 3) and 7 (p = 4).

For every rational-exponential pair with rational coefficients (all ten... eight real ones at p = 3, all 21 real ones at p = 4), and for the
two complex pairs at p = 3 under both choices of i modulo 5:
  * the label L = roots of A modulo l; the labels are distinct l-integral reductions and, at p = 3, exhaust the two-element subsets of F_5;
  * A(0) = 0 (pulse) if and only if 0 is in L                              (Proposition 3.6);
  * the label of the mirror image iota A is -L, and iota A = A iff L = -L  (Theorem 6.2(ii));
  * P_A(0) != 0 at every pulse                                            (Proposition 3.6).
For symbolic coefficients at p = 3, 4, 5: on the fixed subspace of iota, dR_r/dalpha_j = 0 unless j = r + 1 (mod 2) (Theorem 6.2(ii)),
and R_0 = -A(0)(A(0) + C_A(0)) (equation for the constant remainder).  SymPy only."""
import itertools, sympy as sp
rho, m_, j_ = sp.symbols('rho m j_')

def star(F, G):
    expr = sp.expand(F.subs(rho, j_)*G.subs(rho, m_ - j_))
    tot = 0
    for (e,), co in sp.Poly(expr, j_).terms():
        tot += co*sp.summation(j_**e, (j_, 1, m_ - 1))
    return sp.expand(tot.subs(m_, rho))

def pair_data(A, p):
    sp_ = 2*sp.factorial(2*p - 1)/sp.factorial(p - 1)**2
    C, R = sp.div(sp.Poly(star(A, A), rho), sp.Poly(A, rho))
    return sp.expand(C.as_expr()*sp_/2), R.as_expr()

def label(A, l, imod=None):
    P = sp.Poly(A, rho)
    co = [c_ if imod is None else sp.sympify(c_).subs(sp.I, imod) for c_ in P.all_coeffs()]
    co = [(sp.Rational(c_).p*pow(sp.Rational(c_).q, -1, l)) % l for c_ in co]
    return frozenset(s for s in range(l) if sum(c_*pow(s, k, l) for k, c_ in enumerate(reversed(co))) % l == 0)

ok = True
# ------------------------------------------------------------------ p = 3
l = 5
ks = [(1, 0), (-1, 0), (0, -1), (0, sp.Rational(1, 11)), (3, 2), (-3, 2), (4, 3), (-4, 3)]
labels = {}
for a, b in ks:
    A = rho**2 + a*rho + b
    P, R = pair_data(A, 3); assert R == 0
    S = label(A, l); labels[(a, b)] = S
    assert len(S) == 2
    ok &= ((b == 0) == (0 in S))
    ok &= (labels.get((-a, b), None) in (None, frozenset((-s) % l for s in S)))
    if b == 0: ok &= (P.subs(rho, 0) != 0)
for imod in (2, 3):
    for sgn in (1, -1):
        A = rho**2 + sgn*sp.I*rho
        P, R = pair_data(A, 3); assert sp.simplify(R) == 0
        labels[(sgn*sp.I, 0, imod)] = label(A, l, imod)
real_labels = set(labels[k] for k in labels if len(k) == 2)
cplx = set(labels[k] for k in labels if len(k) == 3)
print("p = 3 labels:", {str(k): sorted(v) for k, v in labels.items()})
ok &= (real_labels | cplx == set(frozenset(c) for c in itertools.combinations(range(5), 2)))
print("   the ten labels are the ten two-element subsets of F_5:", real_labels | cplx == set(frozenset(c) for c in itertools.combinations(range(5), 2)))
# ------------------------------------------------------------------ p = 4 (the 21 real pairs, all rational)
l = 7
half = [(-4, 3, 0), (-3, 2, 0), (0, -1, 0), (sp.Rational(-38, 3), sp.Rational(113, 3), -26), (-9, 23, -15), (-8, 17, -10), (-7, 14, -8),
        (-6, 11, -6), (-3, -1, 3), (-2, -1, 2), (sp.Rational(-12, 11), sp.Rational(839, 3751), sp.Rational(-498, 3751))]
allp = sorted(set(half + [(-a1, a2, -a3) for a1, a2, a3 in half]), key=str)
print("p = 4: number of real pairs checked:", len(allp))
lab4 = {}
for t in allp:
    A = rho**3 + t[0]*rho**2 + t[1]*rho + t[2]
    P, R = pair_data(A, 4); assert R == 0
    S = label(A, l); lab4[t] = S
    assert len(S) == 3, (t, S)
    ok &= ((t[2] == 0) == (0 in S))
    if t[2] == 0: ok &= (P.subs(rho, 0) != 0)
for t in allp:
    mirror = (-t[0], t[1], -t[2])
    ok &= (lab4[mirror] == frozenset((-s) % l for s in lab4[t]))
    ok &= ((mirror == t) == (lab4[t] == frozenset((-s) % l for s in lab4[t])))
ok &= (len(set(lab4.values())) == len(allp))
print("   labels distinct:", len(set(lab4.values())) == len(allp), "; pulses:", sum(1 for t in allp if t[2] == 0), "fronts:", sum(1 for t in allp if t[2] != 0))
print("   label of the front with 3751:", sorted(lab4[(sp.Rational(-12, 11), sp.Rational(839, 3751), sp.Rational(-498, 3751))]))
# ------------------------------------------------------------------ symbolic identities
for p in (3, 4, 5):
    d = p - 1
    al = sp.symbols('a1:%d' % (d + 1))
    A = rho**d + sum(a_*rho**(d - 1 - i) for i, a_ in enumerate(al))
    Cq, Rq = sp.div(sp.Poly(star(A, A), rho), sp.Poly(A, rho))
    R = Rq.as_expr(); C = Cq.as_expr()
    R0 = sp.Poly(R, rho).coeff_monomial(1)
    ok &= (sp.expand(R0 + al[-1]*(al[-1] + C.subs(rho, 0))) == 0)
    fixed = {a_: 0 for i, a_ in enumerate(al) if (i + 1) % 2 == 1}
    good = True
    for r in range(d):
        Rr = sp.Poly(R, rho).coeff_monomial(rho**r)
        for jj, a_ in enumerate(al, start=1):
            if (jj - (r + 1)) % 2 != 0:
                good &= (sp.expand(sp.diff(Rr, a_).subs(fixed)) == 0)
    ok &= good
    print(f"p = {p}: R_0 = -A(0)(A(0)+C_A(0)) and the parity splitting of the Jacobian on the fixed subspace:", good)
print("ALL CHECKS PASSED" if ok else "SOME CHECK FAILED")
