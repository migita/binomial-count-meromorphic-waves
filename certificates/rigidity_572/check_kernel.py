#!/usr/bin/env python3
"""Compare all 90 sparse gap-system families with independent polynomial division over QQ."""

import argparse
from fractions import Fraction
import json
from pathlib import Path
import time
import sympy as sp

from kernel import kappa_formula,stratum_system


def check():
    x=sp.Symbol('x')
    started=time.monotonic()
    checked=0
    for g in range(2,19,2):
        for s in range(1,g+1):
            variables=sp.symbols(f'c1:{s+1}')
            c=(sp.Integer(1),)+variables
            C=sum(c[i]*x**(s-i) for i in range(s+1))
            delta=sp.Rational(g-1,2)
            S=sum(sp.ff(g,i+j)/(sp.ff(delta,i)*sp.ff(delta,j))*c[i]*c[j]*x**(g-i-j)
                  for i in range(s+1) for j in range(s+1) if i+j<=g)
            domain=sp.QQ.poly_ring(*variables)
            remainder=sp.rem(sp.Poly(S,x,domain=domain),sp.Poly(C,x,domain=domain))
            sparse=stratum_system(g,s,kappa_formula(g,s))
            for j in range(1,s+1):
                direct={monomial:Fraction(int(coefficient.p),int(coefficient.q))
                        for monomial,coefficient in sp.Poly(remainder.nth(s-j),*variables,domain=sp.QQ).terms()
                        if coefficient}
                if direct!=sparse[j-1]:
                    raise ValueError(f'Remainder mismatch at gap={g}, stratum={s}, coefficient={j}')
            checked+=1
    return {'independent_method':'SymPy polynomial division over QQ versus the sparse remainder generator',
            'strata_checked':checked,'maximum_gap':18,'all_passed':True,
            'elapsed_seconds':round(time.monotonic()-started,3)}


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    text=json.dumps(check(),indent=2)+'\n'
    print(text,end='')
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(text)
