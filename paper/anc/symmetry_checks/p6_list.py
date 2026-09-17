"""The ten purely dispersive pairs at p = 6 (seventh-order KdV family): A = rho^5 + c1 rho^3 + c2 rho."""
import sympy as sp
rho, n, j = sp.symbols('rho n j')
c1, c2 = sp.symbols('c1 c2')
def S_of(A):
    e = sp.expand(A.subs(rho, j) * A.subs(rho, n - j)); tot = 0
    for (k,), co in sp.Poly(e, j).terms():
        tot += co * sp.summation(j**k, (j, 1, n - 1))
    return sp.expand(tot.subs(n, rho))
A = rho**5 + c1*rho**3 + c2*rho
S = S_of(A)
q, r = sp.div(sp.Poly(S, rho), sp.Poly(A, rho))
eqs = [sp.factor(c) for c in r.all_coeffs() if c != 0]
print("remainder powers:", sorted({m[0] for m in r.monoms()}))
for e in eqs: print("  eq:", e)
nums = [sp.numer(sp.together(e)) for e in eqs]
G = sp.groebner(nums, c2, c1, order='lex')
elim = [g for g in G.exprs if not g.has(c2)][0]
print("eliminant in c1:", sp.factor(elim))
lin = [g for g in G.exprs if g.has(c2)]
print("number of basis elements with c2:", len(lin), "; degrees in c2:", [sp.degree(g, c2) for g in lin])
fac = sp.factor_list(elim)[1]
for f, m in fac:
    print("  factor deg", sp.degree(f, c1), "mult", m, ":", f, "| real roots:", len(sp.real_roots(f)))
s_p = 2*sp.factorial(11)/sp.factorial(5)**2
P = sp.expand(s_p/2 * q.as_expr())
print("s_6 =", s_p)
print("P_A =", sp.collect(P, rho))
# rational solutions
for f, m in fac:
    if sp.degree(f, c1) == 1:
        v1 = sp.solve(f, c1)[0]
        sol2 = sp.solve([g.subs(c1, v1) for g in lin], c2)
        print("  c1 =", v1, " c2 =", sol2, " A =", sp.factor(A.subs({c1: v1, c2: list(sol2.values())[0] if isinstance(sol2, dict) else sol2[0]})))
