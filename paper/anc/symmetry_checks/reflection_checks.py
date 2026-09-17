"""Exact checks for the draft subsection on reflection symmetry (17 Sep 2026).
 1. S_{iota A}(rho) = -S_A(-rho) - 2A(0)A(-rho),  R_{iota A}(rho) = -R_A(-rho)   (symbolic A, d = 1..5)
 2. at solutions: P_{iota A}(rho) = (-1)^p [P_A(-rho) + s_p A(0)]                 (p = 2, 3 exact solution lists)
 3. the six symmetric pairs at p = 5 (exact), reality, fronts/pulses
 4. fixed-equation scaling: u = b_p lam^p v_A(lam(x-ct)), c = -b_p lam^p a_0, b_j = b_p lam^(p-j) a_j  (p = 2, 3)
"""
import sympy as sp
rho, n, j = sp.symbols('rho n j')
def S_of(A):
    expr = sp.expand(A.subs(rho, j) * A.subs(rho, n - j))
    tot = 0
    for (k,), co in sp.Poly(expr, j).terms():
        tot += co * sp.summation(j**k, (j, 1, n - 1))
    return sp.expand(tot.subs(n, rho))
def sp_(p): return sp.Rational(2) * sp.factorial(2*p - 1) / sp.factorial(p - 1)**2

# 1 ------------------------------------------------------------------
for d in range(1, 6):
    al = sp.symbols('a1:%d' % (d + 1))
    A = rho**d + sum(a * rho**(d - 1 - i) for i, a in enumerate(al))
    iA = sp.expand((-1)**d * A.subs(rho, -rho))
    S, Si = S_of(A), S_of(iA)
    ok1 = sp.expand(Si - (-S.subs(rho, -rho) - 2 * A.subs(rho, 0) * A.subs(rho, -rho))) == 0
    R = sp.rem(sp.Poly(S, rho), sp.Poly(A, rho)).as_expr()
    Ri = sp.rem(sp.Poly(Si, rho), sp.Poly(iA, rho)).as_expr()
    ok2 = sp.expand(Ri + R.subs(rho, -rho)) == 0
    print(f"d={d}: S_(iota A) formula {ok1};  R_(iota A)(rho) = -R_A(-rho) {ok2}")

# 2 ------------------------------------------------------------------
a, b = sp.symbols('a b')
P3 = rho**3 + 4*a*rho**2 + (a**2 + 19*b)*rho - a**3 + 7*a*b - 5*a - 30*b        # eq. (ksoperator)
lhs = P3.subs(a, -a)
rhs = -(P3.subs(rho, -rho) + 60*b)
print("p=3: P_(iota A) = -(P_A(-rho) + s_3 A(0)) identically in (a,b):", sp.expand(lhs - rhs) == 0)
P2 = rho**2 + 5*a*rho + a**2 - 6*a - 1
print("p=2: P_(iota A) = P_A(-rho) + s_2 A(0) on a(a-1)(a+1)=0:",
      all(sp.expand((P2.subs(a, -a0) - (P2.subs(rho, -rho) + 12*a)).subs(a, a0)) == 0 for a0 in (-1, 0, 1)))

# 3 ------------------------------------------------------------------
c1, c2 = sp.symbols('c1 c2')
A5 = rho**4 + c1*rho**2 + c2
S5 = S_of(A5)
q5, r5 = sp.div(sp.Poly(S5, rho), sp.Poly(A5, rho))
eqs = [sp.factor(c) for c in r5.all_coeffs() if c != 0]
print("p=5 symmetric remainder equations (odd powers only):", [sp.degree(m, rho) for m in r5.as_expr().as_ordered_terms()][:0] or
      sorted({mon[0] for mon in r5.monoms()}))
G = sp.groebner([sp.numer(sp.together(e)) for e in eqs], c2, c1, order='lex')
elim = [g for g in G.exprs if not g.has(c2)][0]
print("  eliminant in c1:", sp.factor(elim))
sols = sp.solve([sp.numer(sp.together(e)) for e in eqs], [c1, c2], dict=True)
P5 = (sp_(5) / 2 * q5.as_expr())
for s in sols:
    A = sp.factor(A5.subs(s))
    real = all(sp.im(sp.N(v)) == 0 for v in s.values())
    print("  A =", A, "| real" if real else "| complex", "| front" if s[c2] != 0 else "| pulse",
          "| P_A =", sp.nsimplify(sp.expand(P5.subs(s))) if real else "")
print("  number of solutions:", len(sols))

# 4 ------------------------------------------------------------------
x, t, lam, bp = sp.symbols('x t lambda b_p')
Q = lambda z: 1 / (1 + sp.exp(-z))
for p, Apoly, Ppoly, sols_ in [(2, rho + a, P2, [{a: -1}, {a: 0}, {a: 1}]),
                               (3, rho**2 + a*rho + b, P3, [{a: 1, b: 0}, {a: 3, b: 2}, {a: 0, b: sp.Rational(1, 11)}, {a: sp.I, b: 0}])]:
    for s in sols_:
        Pc = sp.Poly(Ppoly.subs(s), rho).all_coeffs()[::-1]           # a_0..a_p
        zz = sp.symbols('z')
        vA = sp_(p) * sum(co * sp.diff(Q(zz), zz, k) for k, co in enumerate(sp.Poly(Apoly.subs(s), rho).all_coeffs()[::-1]))
        c = -bp * lam**p * Pc[0]
        u = bp * lam**p * vA.subs(zz, lam * (x - c * t))
        bj = [None] + [bp * lam**(p - jj) * Pc[jj] for jj in range(1, p + 1)]
        pde = sp.diff(u, t) + u * sp.diff(u, x) + sum(bj[jj] * sp.diff(u, x, jj + 1) for jj in range(1, p + 1))
        val = sp.simplify(pde.subs({x: sp.Rational(3, 7), t: sp.Rational(2, 5), lam: sp.Rational(5, 4), bp: sp.Rational(-7, 3)}))
        print(f"p={p} {s}: PDE residual at a rational test point =", sp.nsimplify(sp.N(val, 30), tolerance=1e-20))
