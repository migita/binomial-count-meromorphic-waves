# Reflection-symmetric sub-count: A(rho) = rho^d + c1 rho^(d-2) + ...  (parity (-1)^d)
# Predicted length: C(d, floor(d/2)).  Exact Groebner dimension over QQ.
import sympy as sp, sys, time
from math import comb
rho, n = sp.symbols('rho n')
def S_of(A):
    # polynomial continuation of sum_{j=1}^{n-1} A(j)A(n-j) via Faulhaber
    j = sp.symbols('j')
    expr = sp.expand(A.subs(rho, j) * A.subs(rho, n - j))
    P = sp.Poly(expr, j)
    tot = 0
    for (k,), co in P.terms():
        m = sp.symbols('m')
        # sum_{j=1}^{n-1} j^k
        tot += co * sp.summation(j**k, (j, 1, n - 1))
    return sp.expand(tot).subs(n, rho)
def vdim(G, gens):
    # count standard monomials for a zero-dimensional ideal (grevlex GB)
    lms = [sp.Poly(g, *gens).monoms(order='grevlex')[0] for g in G.exprs]
    from itertools import product
    bound = [None]*len(gens)
    for lm in lms:
        nz = [i for i,e in enumerate(lm) if e]
        if len(nz) == 1:
            i = nz[0]; bound[i] = lm[i] if bound[i] is None else min(bound[i], lm[i])
    assert all(b is not None for b in bound), "not zero-dimensional"
    cnt = 0
    for mon in product(*[range(b) for b in bound]):
        if not any(all(m >= l for m, l in zip(mon, lm)) for lm in lms):
            cnt += 1
    return cnt
for p in [int(a) for a in sys.argv[1:]]:
    d = p - 1
    ks = list(range(d - 2, -1, -2))
    cs = sp.symbols('c1:%d' % (len(ks) + 1))
    A = rho**d + sum(c * rho**k for c, k in zip(cs, ks))
    t = time.time()
    if not cs:
        print(f'p={p} d={d}: no unknowns, A=rho^{d}; count 1, predicted {comb(d,d//2)}'); continue
    S = S_of(A)
    R = sp.rem(sp.Poly(S, rho), sp.Poly(A, rho))
    eqs = [sp.factor(c) for c in R.all_coeffs() if c != 0]
    G = sp.groebner([sp.numer(sp.together(e)) for e in eqs], *cs, order='grevlex', domain='QQ')
    J = sp.Matrix([sp.numer(sp.together(e)) for e in eqs]).jacobian(list(cs)).det()
    Gj = sp.groebner(list(G.exprs) + [J], *cs, order='grevlex', domain='QQ')
    print(f"p={p} d={d} unknowns={len(cs)} equations={len(eqs)} vdim={vdim(G, cs)} predicted={comb(d, d//2)} "
          f"reduced={'yes' if Gj.exprs == [1] else 'NO'}  [{time.time()-t:.1f}s]", flush=True)
