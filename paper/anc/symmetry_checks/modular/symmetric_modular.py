"""Finite-field certificates that the F_p pairs of the two pure subfamilies are distinct (X_p^sym reduced).

For each p the reflection-symmetric matching system (A of parity (-1)^d, d = p-1) is built exactly, reduced modulo a prime q,
and two independent programs are asked for:
  Singular:  vdim(std(I)) over F_q  and  whether std(I + det(jacob(I))) is the unit ideal;
  msolve:    degree of the ideal, degree of the eliminating polynomial and of its squarefree part over F_q.
Certificate: vdim = F_p and unit Jacobian ideal  (resp. all three msolve degrees equal to F_p).
Then the F_p geometric points mod q are simple; each lifts uniquely to a simple point in characteristic zero (multivariable
Hensel lemma), the lifts are distinct, and since the characteristic-zero length is F_p (rigidity, certified for p <= 73) they
are all the points: X_p^sym is reduced.  Usage:  python3 symmetric_modular.py q p1 p2 ...   (needs Singular and/or msolve)"""
import sympy as sp, subprocess, sys, time, json, os, re, hashlib
from math import comb
SING = os.environ.get('SINGULAR', '/tmp/ks-singular/root/usr/bin/Singular')
MSOLVE = os.environ.get('MSOLVE', '/tmp/msolve/msolve')
_SROOT = os.path.dirname(os.path.dirname(os.path.dirname(SING)))          # .../root  when SING = .../root/usr/bin/Singular
_LIB = os.path.join(_SROOT, 'usr/lib/x86_64-linux-gnu')
ENV = dict(os.environ)
if os.path.isdir(_LIB):                                                     # unpacked Debian package: point the loader at it
    ENV['LD_LIBRARY_PATH'] = ':'.join([_LIB, os.path.join(_LIB, 'singular/MOD'), ENV.get('LD_LIBRARY_PATH', '')])
    ENV['SINGULAR_ROOT_DIR'] = os.path.join(_SROOT, 'usr')
    ENV['SINGULARPATH'] = os.path.join(_SROOT, 'usr/share/singular/LIB')
n, k = sp.symbols('n k')
_T = {}
def mono_conv(i, j):
    key = (min(i, j), max(i, j))
    if key not in _T:
        e = sp.expand(k**key[0] * (n - k)**key[1]); tot = 0
        for (a,), co in sp.Poly(e, k).terms():
            tot += co * sp.summation(k**a, (k, 1, n - 1))
        _T[key] = sp.Poly(sp.expand(tot), n, domain='QQ')
    return _T[key]
def system(p):
    d = p - 1
    exps = list(range(d - 2, -1, -2))
    cs = sp.symbols('c1:%d' % (len(exps) + 1))
    gens = (n,) + tuple(cs)
    coeff = {d: sp.Poly(1, *gens, domain='QQ')}
    for c, e in zip(cs, exps): coeff[e] = sp.Poly(c, *gens, domain='QQ')
    A = sum((coeff[e] * sp.Poly(n**e, *gens, domain='QQ') for e in coeff), sp.Poly(0, *gens, domain='QQ'))
    S = sp.Poly(0, *gens, domain='QQ')
    for i in coeff:
        for j in coeff:
            S = S + coeff[i] * coeff[j] * sp.Poly(mono_conv(i, j).as_expr(), *gens, domain='QQ')
    R = S
    while R.degree(n) >= d:
        dg = R.degree(n)
        lead = sp.Poly(sum(co * sp.prod([g**m for g, m in zip(gens[1:], mon[1:])]) for mon, co in R.terms() if mon[0] == dg), *gens, domain='QQ')
        R = R - lead * sp.Poly(n**(dg - d), *gens, domain='QQ') * A
    eqs = []
    for r in range(d):
        e = sp.expand(sum(co * sp.prod([g**m for g, m in zip(gens[1:], mon[1:])]) for mon, co in R.terms() if mon[0] == r))
        if e != 0:
            eqs.append(sp.Poly(e, *cs).clear_denoms()[1].primitive()[1].as_expr())
    return cs, eqs
def run(cmd, timeout, **kw):
    t = time.time()
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout, **kw)
        return r.stdout + r.stderr, time.time() - t, r.returncode
    except subprocess.TimeoutExpired:
        return 'TIMEOUT', time.time() - t, None
q = int(sys.argv[1]); timeout = int(os.environ.get('TIMEOUT', '3600'))
results = []
for p in [int(x) for x in sys.argv[2:]]:
    d = p - 1; m = d // 2; Fp = comb(d, m)
    t0 = time.time(); cs, eqs = system(p); tb = time.time() - t0
    names = ','.join(str(c) for c in cs); body = ',\n'.join(str(e).replace('**', '^') for e in eqs)
    row = {'p': p, 'q': q, 'unknowns': len(cs), 'F_p': Fp, 'build_seconds': round(tb, 1)}
    # --- Singular
    spath = f'sym_p{p}_q{q}.sing'
    open(spath, 'w').write(f"ring R = {q}, ({names}), wp({','.join(str(i) for i in range(1, len(cs)+1))});\n"
        f"ideal I = {body};\nideal G = std(I);\nprint(\"DIM\"); dim(G);\nprint(\"VDIM\"); vdim(G);\n"
        "poly J = det(jacob(I));\nideal H = std(G + J);\nprint(\"UNIT\"); H[1] == 1;\nquit;\n")
    out, secs, rc = run([SING, '-q', spath], timeout, env=ENV)
    open(spath.replace('.sing', '.sing.out'), 'w').write(out)
    mm = re.search(r'VDIM\s+(-?\d+)', out); uu = re.search(r'UNIT\s+(\d+)', out)
    row['singular'] = {'vdim': int(mm.group(1)) if mm else None, 'unit_jacobian_ideal': (uu.group(1) == '1') if uu else None,
                       'seconds': round(secs, 1), 'returncode': rc, 'input_sha256': hashlib.sha256(open(spath, 'rb').read()).hexdigest()[:16]}
    # --- msolve
    mpath = f'sym_p{p}_q{q}.ms'
    open(mpath, 'w').write(f"{names}\n{q}\n{body}\n")
    out, secs, rc = run([MSOLVE, '-v', '1', '-t', '4', '-f', mpath, '-o', mpath + '.out'], timeout)
    open(mpath + '.log', 'w').write(out)
    g = lambda pat: (int(re.search(pat, out).group(1)) if re.search(pat, out) else None)
    row['msolve'] = {'degree_of_ideal': g(r'degree of ideal\s+(\d+)'), 'deg_elim': g(r'deg\. elim\. pol\.\s+(\d+)'),
                     'deg_sqfr_elim': g(r'deg\. sqfr\. elim\. pol\.\s+(\d+)'), 'seconds': round(secs, 1), 'returncode': rc}
    if os.path.exists(mpath + '.out'): os.remove(mpath + '.out')      # the parametrization itself is not needed
    s_ok = row['singular']['vdim'] == Fp and row['singular']['unit_jacobian_ideal'] is True
    m_ok = row['msolve']['degree_of_ideal'] == Fp == row['msolve']['deg_elim'] == row['msolve']['deg_sqfr_elim']
    row['certified_by'] = [x for x, ok in (('singular', s_ok), ('msolve', m_ok)) if ok]
    results.append(row)
    print(json.dumps(row), flush=True)
    json.dump(results, open(f'symmetric_modular_q{q}_p{sys.argv[2]}-{p}.json', 'w'), indent=1)
