"""Generate exact modular matching systems from polynomial finite sums."""

import argparse
from functools import lru_cache
from math import comb
from pathlib import Path
import json
import sympy as s

ROOT=Path(__file__).resolve().parent
rho=s.Symbol('rho')


@lru_cache(None)
def monomial_convolution(i,j):
    result=0
    for k in range(j+1):
        m=i+k
        powers=(s.bernoulli(m+1,rho)-s.bernoulli(m+1,0))/(m+1)-int(m==0)
        result+=(-1)**k*s.binomial(j,k)*rho**(j-k)*powers
    return s.Poly(result,rho,domain=s.QQ).as_expr()


def system(p,kind):
    d=p-1
    weights=list(range(1,d+1)) if kind=='full' else list(range(2,d+1,2))
    variables=s.symbols(' '.join(f'a{i}' for i in weights),seq=True)
    coefficients={d:s.Integer(1), **{d-w:v for w,v in zip(weights,variables)}}
    A=sum(c*rho**i for i,c in coefficients.items())
    S=s.expand(sum(ci*cj*monomial_convolution(i,j) for i,ci in coefficients.items() for j,cj in coefficients.items()))
    domain=s.QQ.poly_ring(*variables)
    quotient,remainder=s.div(s.Poly(S,rho,domain=domain),s.Poly(A,rho,domain=domain))
    equations=[]
    for k in range(d):
        coefficient=remainder.nth(k)
        if coefficient==0: continue
        poly=s.Poly(coefficient,*variables,domain=s.QQ).clear_denoms()[1].primitive()[1]
        equations.append(poly.as_expr())
    assert len(equations)==len(variables)
    # Validate the convolution on enough integer arguments to determine it.
    for n in range(1,2*d+3):
        actual=sum(A.subs(rho,k)*A.subs(rho,n-k) for k in range(1,n))
        assert s.expand(S.subs(rho,n)-actual)==0
    return variables,weights,A,S,quotient.as_expr(),equations


def singular(expr):
    return str(expr).replace('**','^')


def generate(p,kind,prime,order,algorithm):
    variables,weights,A,S,quotient,eqs=system(p,kind)
    n=len(variables)
    expected=comb(2*p-1,p-1) if kind=='full' else comb(p-1,(p-1)//2)
    tag=f'{kind}_p{p}_q{prime}_{order}_{algorithm}'
    ordering='dp' if order=='dp' else 'wp('+','.join(map(str,weights))+')'
    lines=[
        '// Exact input reconstructed from sum_{k=1}^{n-1} A(k) A(n-k).',
        f'ring r={prime},('+','.join(map(str,variables))+f'),{ordering};',
        'short=0;',
        'option(redSB);',
        'ideal I='+',\n'.join(map(singular,eqs))+';',
        f'print("CASE {tag} EXPECTED {expected}");',
        'int started=timer;',
        'print("BEGIN_GROEBNER");',
        f'ideal G={algorithm}(I);',
        'print("GROEBNER_SECONDS "+string(timer-started));',
        'print("DIMENSION "+string(dim(G)));',
        'print("LENGTH "+string(vdim(G)));',
        f'write("{tag}.basis.sing","ideal G="+string(G)+";");',
        'print("BEGIN_JACOBIAN");',
        'matrix J=jacob(I);',
        'poly det0=1;',
    ]
    # A division-free determinant evaluated inside the quotient ring; reduce
    # at each step so no giant unreduced determinant is ever constructed.
    for mask in range(1,1<<n):
        cols=[i for i in range(n) if mask&(1<<i)]
        row=len(cols)
        terms=[]
        for position,col in enumerate(cols):
            sign='-' if (row-1+position)%2 else '+'
            terms.append(f'{sign}J[{row},{col+1}]*det{mask^(1<<col)}')
        lines.append(f'poly det{mask}=reduce('+''.join(terms).lstrip('+')+',G);')
    lines += [
        'print("DETERMINANT_SECONDS "+string(timer-started));',
        f'ideal K={algorithm}(G+ideal(det{(1<<n)-1}));',
        'print("ALL_SIMPLE "+string(reduce(1,K)==0));',
        'print("TOTAL_SECONDS "+string(timer-started));',
    ]
    if kind=='pure' and p%2==0:
        constant=s.Poly(quotient,rho).nth(0)
        numerator=s.fraction(s.together(constant))[0]
        lines += [
            'poly backgroundConstant='+singular(numerator)+';',
            f'ideal Z={algorithm}(G+ideal(backgroundConstant));',
            'print("NONZERO_BACKGROUND "+string(reduce(1,Z)==0));',
        ]
    lines += ['quit;','']
    (ROOT/(tag+'.sing')).write_text('\n'.join(lines))
    (ROOT/(tag+'.input.json')).write_text(json.dumps({
        'p':p,'kind':kind,'prime':prime,'order':order,'algorithm':algorithm,
        'variables':list(map(str,variables)),'weights':weights,'expected_length':expected,
        'A':str(A),'equations':list(map(str,eqs)),
        'integer_sum_reconstruction_verified':True,
    },indent=2)+'\n')
    print(tag, 'variables',n,'terms',sum(len(s.Poly(e,*variables).terms()) for e in eqs),'expected',expected,flush=True)


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('p',type=int,nargs='+')
    parser.add_argument('--kind',choices=['full','pure'],default='full')
    parser.add_argument('--prime',type=int,default=32003)
    parser.add_argument('--order',choices=['dp','wp'],default='dp')
    parser.add_argument('--algorithm',choices=['std','slimgb'],default='std')
    args=parser.parse_args()
    assert s.isprime(args.prime) and args.prime>2*max(args.p)
    for p in args.p:
        generate(p,args.kind,args.prime,args.order,args.algorithm)
