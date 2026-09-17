"""Even p: elliptic pairs with EVEN operator on a fixed nonsingular lattice. Predicted length 2*C(p-1, p/2-1); exact vdim."""
import sympy as sp, sys, time
from math import comb
from itertools import product
X, Y = sp.symbols('X Y')
def run(p, g2, g3):
    def Dop(F): return sp.expand(sp.diff(F, X) * Y + sp.diff(F, Y) * (6*X**2 - sp.Rational(g2) / 2))
    def nf(F):
        out = 0
        for (k,), co in sp.Poly(sp.expand(F), Y).terms():
            out += co * (4*X**3 - g2*X - g3)**(k // 2) * Y**(k % 2)
        return sp.expand(out)
    s_p = 2 * sp.factorial(2*p - 1) / sp.factorial(p - 1)**2
    ders = [X]
    for _ in range(2*p):
        ders.append(nf(Dop(ders[-1])))
    us = sp.symbols('u0:%d:2' % (p - 2)) if p > 2 else ()
    us = tuple(sp.Symbol('u%d' % k) for k in range(0, p - 2, 2))
    As = tuple(sp.Symbol('a%d' % k) for k in range(0, p, 2))
    b = sp.Symbol('b')
    V = b - s_p * ders[p - 2] + sum(u * ders[k] for u, k in zip(us, range(0, p - 2, 2)))
    def DV(m):   # D^m V
        return (-s_p * ders[p - 2 + m] + sum(u * ders[k + m] for u, k in zip(us, range(0, p - 2, 2)))) if m > 0 else V
    E = nf(DV(p) + sum(a * DV(k) for a, k in zip(As, range(0, p, 2))) + V**2 / 2)
    eqs = [c for c in sp.Poly(E, X, Y).coeffs()]
    gens = list(As) + list(us) + [b]
    G = sp.groebner(eqs, *gens, order='grevlex', domain='QQ')
    lms = [sp.Poly(g, *gens).monoms(order='grevlex')[0] for g in G.exprs]
    bound = [None] * len(gens)
    for lm in lms:
        nz = [i for i, e in enumerate(lm) if e]
        if len(nz) == 1:
            i = nz[0]; bound[i] = lm[i] if bound[i] is None else min(bound[i], lm[i])
    vd = sum(1 for mon in product(*[range(bb) for bb in bound]) if not any(all(m >= l for m, l in zip(mon, lm)) for lm in lms))
    return vd, len(eqs), len(gens)
for p in (2, 4, 6):
    t = time.time()
    vd, ne, ng = run(p, 2, 1)
    print(f"p={p}: lattice (g2,g3)=(2,1): {ne} equations, {ng} unknowns, vdim={vd}, predicted 2*C({p-1},{p//2-1})={2*comb(p-1, p//2-1)}  [{time.time()-t:.1f}s]", flush=True)
