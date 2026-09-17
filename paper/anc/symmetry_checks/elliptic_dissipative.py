"""Odd p: elliptic pairs whose operator is purely dissipative (P - P(0) odd) on a fixed nonsingular lattice.
The matching system has one more equation than unknowns; on the sample lattice (g2,g3)=(2,1) it has NO solution
(the Groebner basis is {1}), hence none on a generic lattice.  For p=3 the exact condition is g2=0."""
import sympy as sp, time
X, Y = sp.symbols('X Y')
def run(p, g2, g3):
    def Dop(F): return sp.expand(sp.diff(F, X)*Y + sp.diff(F, Y)*(6*X**2 - sp.Rational(g2)/2))
    def nf(F):
        out = 0
        for (k,), co in sp.Poly(sp.expand(F), Y).terms():
            out += co*(4*X**3 - g2*X - g3)**(k//2)*Y**(k % 2)
        return sp.expand(out)
    s_p = 2*sp.factorial(2*p-1)/sp.factorial(p-1)**2
    ders = [X]
    for _ in range(2*p): ders.append(nf(Dop(ders[-1])))
    odd = list(range(1, p-2, 2))                                   # profile: beta + sum_{j odd} t_j D^j X, top j = p-2 fixed
    ts = tuple(sp.Symbol('t%d' % j) for j in odd)
    As = tuple(sp.Symbol('a%d' % j) for j in range(1, p, 2)) + (sp.Symbol('a0'),)
    beta = sp.Symbol('beta')
    V = beta - s_p*ders[p-2] + sum(t*ders[j] for t, j in zip(ts, odd))
    DV = lambda m: (-s_p*ders[p-2+m] + sum(t*ders[j+m] for t, j in zip(ts, odd))) if m > 0 else V
    E = nf(DV(p) + sum(a*DV(j) for a, j in zip(As[:-1], range(1, p, 2))) + As[-1]*V + V**2/2)
    eqs = sp.Poly(E, X, Y).coeffs()
    gens = list(As) + list(ts) + [beta]
    G = sp.groebner(eqs, *gens, order='grevlex', domain='QQ')
    return len(eqs), len(gens), G.exprs
for p in (3, 5, 7):
    t = time.time(); ne, ng, G = run(p, 2, 1)
    print(f"p={p}: {ne} equations, {ng} unknowns, Groebner basis = {G if len(G) < 3 else '[%d elements]' % len(G)}  [{time.time()-t:.1f}s]", flush=True)
