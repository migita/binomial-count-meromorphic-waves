#!/usr/bin/env python3
"""Validate the complete coverage, recorded outcomes, file hashes and exact degree-weight reductions.

This does not rerun Gröbner bases; use replay.py for fresh solver computations.
"""

import argparse
from collections import Counter
import csv
import hashlib
import json
from math import comb
from pathlib import Path
import time

from kernel import kappa_formula, kappa_from_degree

ROOT=Path(__file__).resolve().parent


def prime(n):
    if n<2:
        return False
    if n%2==0:
        return n==2
    return all(n%d for d in range(3,int(n**0.5)+1,2))


def verify():
    started=time.monotonic()
    manifest=json.loads((ROOT/'MANIFEST.json').read_text())
    for name,expected in manifest['files'].items():
        path=ROOT/name
        if path.stat().st_size!=expected['bytes'] or hashlib.sha256(path.read_bytes()).hexdigest()!=expected['sha256']:
            raise ValueError(f'File integrity check failed: {name}')
    with (ROOT/'coverage.csv').open() as f:
        rows=[{key:int(value) for key,value in row.items()} for row in csv.DictReader(f)]
    if len(rows)!=572 or [r['d'] for r in rows]!=list(range(1,573)):
        raise ValueError('The coverage must contain every degree 1..572 exactly once and in order')
    records={}
    for line in (ROOT/'results.jsonl').read_text().splitlines():
        record=json.loads(line)
        key=record['q'],record['g'],record['s']
        if key in records:
            raise ValueError(f'Duplicate stratum record: {key}')
        records[key]=record
    required=set()
    ordered_weights=0
    for row in rows:
        d,q,e,g=(row[k] for k in ['d','q','e','g'])
        if not (prime(q) and q%2 and e>=1 and 0<=g<q and g%2==0 and g<=18 and 2*d+1==q**e+g and 2*q**e>2*d+1):
            raise ValueError(f'Invalid prime-power-gap row: {row}')
        if g==0:
            continue
        # Independent actual-degree beta ratios from factorials, including all
        # coefficients that must disappear when i+j exceeds the gap.
        actual,minimum,units=kappa_from_degree(d,q,e,g)
        expected=kappa_formula(g,g,mod=q)
        if minimum!=0:
            raise ValueError(f'Unexpected minimum valuation at degree {d}')
        for i in range(g+1):
            for j in range(g+1):
                ordered_weights+=1
                if i+j<=g:
                    if actual[(i,j)]!=expected[(i,j)] or (i,j) not in units:
                        raise ValueError(f'Weight mismatch at {(d,i,j)}')
                elif actual[(i,j)]!=0:
                    raise ValueError(f'A discarded weight survives at {(d,i,j)}')
        for s in range(1,g+1):
            key=q,g,s
            required.add(key)
            record=records.get(key)
            if not record or record.get('rigid') is not True or record.get('hilbert_ok') is not True:
                raise ValueError(f'Missing or inconclusive stratum: {key}')
            if record.get('error') or record.get('timeout') or record.get('n_zero_generators')!=0:
                raise ValueError(f'Invalid computation record: {key}')
            if record.get('vdim')!=comb(g,s) or record.get('expected_vdim')!=comb(g,s):
                raise ValueError(f'Unexpected recorded quotient dimension: {key}')
            powers=record.get('pure_powers',[])
            if len(powers)!=s or not all(isinstance(value,int) and value>0 for value in powers):
                raise ValueError(f'Missing leading-ideal pure power: {key}')
    if set(records)!=required:
        raise ValueError('The result file must contain exactly the strata used by the coverage table')
    return {'degrees':572,'degree_zero':'trivial','maximum_degree':572,'maximum_ode_order':573,
            'positive_gap_pairs':len({(q,g) for q,g,s in required}),'strata':len(required),
            'maximum_gap':max(r['g'] for r in rows),'gap_histogram':dict(sorted(Counter(r['g'] for r in rows).items())),
            'actual_degree_weights_checked':ordered_weights,'file_hashes_verified':len(manifest['files']),
            'coverage_and_record_checks_passed':True,'fresh_groebner_replay':False,
            'claim':'Continuous-convolution rigidity through degree 572; counting formulas WITH MULTIPLICITY through ODE order 573.',
            'elapsed_seconds':round(time.monotonic()-started,3)}


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    result=verify()
    text=json.dumps(result,indent=2)+'\n'
    print(text,end='')
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(text)
