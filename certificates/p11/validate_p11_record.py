"""Check preserved p=11 inputs, audit provenance, coverage and accounting.

This does not repeat every local lifting calculation. Its output distinguishes
the old complete record from the fresh, bounded high-precision replay.
"""

from collections import Counter
from io import BytesIO
import hashlib
import json
from math import comb
from pathlib import Path
import sys
import sympy as s

from generate_systems import system,rho

ROOT=Path(__file__).resolve().parent
BUNDLE=ROOT/'p11_archive_replay'
PROJECT=BUNDLE/'project'
sys.path.insert(0,str(PROJECT))
from codex_verify_corank_candidates import DataOnlyUnpickler


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_data(path):
    return DataOnlyUnpickler(BytesIO(path.read_bytes())).load()


merged=json.loads((PROJECT/'codex_dvr_p11_merged_final.json').read_text())
stage_path=BUNDLE/'coll/stage1_p11.pkl'
assert digest(stage_path)==merged['stage_sha256']
stage=read_data(stage_path)
assert stage['p']==11 and stage['ell']==19

print('Reconstructing p=11 equations independently from finite sums.',flush=True)
variables,weights,A,S,C,eqs=system(11,'full')
domain=s.QQ.poly_ring(*variables)
R=s.Poly(s.expand(S-A*C),rho,domain=domain)
for k,stored in enumerate(stage['G']):
    computed={monomial:(int(coefficient.p),int(coefficient.q))
              for monomial,coefficient in s.Poly(19*R.nth(k),*variables,domain=s.QQ).terms()}
    assert computed==stored, f'Equation {k} differs from the archived input'
    assert all(denominator%19 for numerator,denominator in computed.values())
print('All ten archived rational equations match 19 times the reconstructed remainder.',flush=True)

source_audits={}
for source in merged['source_audits']:
    path=PROJECT/source['path']
    assert digest(path)==source['sha256']
    source_audits[source['path']]=json.loads(path.read_text())
for name,expected in merged['mathematical_checker_sha256'].items():
    assert digest(PROJECT/name)==expected

expected_c2={tuple(point) for point,corank,_ in stage['singular'] if corank==2}
selected=merged['selected']
labels=[tuple(row['point']) for row in selected]
assert len(labels)==len(set(labels))==len(expected_c2)==11592
assert set(labels)==expected_c2
c2_total=0
for choice in selected:
    audit=source_audits[choice['audit_source']]['results'][choice['audit_record']]
    assert tuple(audit['point'])==tuple(choice['point'])
    assert audit['status']=='certified' and audit['check']['certified'] is True
    count=audit['check']['simple_points_certified']
    assert count==choice['simple_points_certified']
    assert all(branch['hensel_certified'] for branch in audit['check']['branches'])
    assert all(check['passed'] for check in audit['check']['separation_checks'])
    c2_total+=count
assert c2_total==47592

c1=read_data(BUNDLE/'coll/stage2_p11_corank1_all.pkl')['results']
expected_c1={tuple(point) for point,corank,_ in stage['singular'] if corank==1}
c1_labels=[tuple(row['point']) for row in c1]
assert len(c1_labels)==len(set(c1_labels))==len(expected_c1)==47801
assert set(c1_labels)==expected_c1 and expected_c1.isdisjoint(expected_c2)
assert all(row['certified'] and not row.get('flags') and row['distinct']==row['L'] for row in c1)
c1_total=sum(row['distinct'] for row in c1)
assert c1_total==97971
simple_rational=stage['n_simple_rational']
simple_quadratic=2*len(stage['ext'])
assert simple_rational==119781 and simple_quadratic==87372
total=simple_rational+simple_quadratic+c1_total+c2_total
assert total==comb(21,10)==352716

replay=json.loads((ROOT/'p11_high_precision_replay.json').read_text())
assert replay['checked_special_points']==4 and replay['statuses']=={'certified':4}
assert replay['simple_points_certified_lower_bound']==16
assert replay['claimed_complete_but_not_independently_certified']==0

result={
    'p':11,'residue_characteristic':19,
    'independently_reconstructed_equations_match':True,
    'source_audit_and_checker_hashes_match':True,
    'corank_one_exact_label_coverage':len(c1_labels),
    'corank_one_local_lengths':dict(Counter(row['L'] for row in c1)),
    'corank_two_exact_label_coverage':len(labels),
    'corank_two_selected_audit_entries_validated':True,
    'distinct_residue_labels_not_added_twice':True,
    'preserved_subtotals':{'simple_rational':simple_rational,'simple_quadratic':simple_quadratic,'corank_one':c1_total,'corank_two':c2_total},
    'preserved_total_simple_points':total,
    'fresh_high_precision_replay':{'special_points':4,'simple_points':16,'failed':0},
    'full_fresh_equation_level_replay':False,
    'scope':'Validates the preserved complete certificate record and independently reconstructs its equations. The complete old local computations are carried forward; only the four final high-precision records were freshly replayed in this run.',
}
(ROOT/'p11_record_validation.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2),flush=True)
