"""Run one local exact check with bounded CPU, memory, and wall time."""

import argparse
import datetime
import json
import os
from pathlib import Path
import resource
import re
import subprocess
import time

parser=argparse.ArgumentParser()
parser.add_argument('input',type=Path)
parser.add_argument('--seconds',type=int,default=240)
parser.add_argument('--memory-gb',type=int,default=8)
args=parser.parse_args()
path=args.input.resolve()
root=Path('/tmp/ks-singular/root/usr')
env=dict(os.environ)
env.update({
    'LD_LIBRARY_PATH':str(root/'lib/x86_64-linux-gnu')+':'+str(root/'lib/x86_64-linux-gnu/singular/MOD'),
    'SINGULARPATH':str(root/'share/singular/LIB'),
    'SINGULAR_PROCS_DIR':str(root/'lib/x86_64-linux-gnu/singular/MOD'),
    'OMP_NUM_THREADS':'1',
    'OPENBLAS_NUM_THREADS':'1',
})


def limits():
    resource.setrlimit(resource.RLIMIT_AS,(args.memory_gb*1024**3,args.memory_gb*1024**3))
    resource.setrlimit(resource.RLIMIT_CPU,(args.seconds+5,args.seconds+10))


log=path.with_suffix('.log')
path.with_suffix('.basis.sing').unlink(missing_ok=True)
t0=time.monotonic()
print('START',path.name,datetime.datetime.now(datetime.timezone.utc).isoformat(),flush=True)
with log.open('w') as f:
    proc=subprocess.Popen([str(root/'bin/Singular'),'-q',str(path)],cwd=path.parent,env=env,stdout=f,stderr=subprocess.STDOUT,preexec_fn=limits)
    print('SINGULAR_PID',proc.pid,flush=True)
    timed_out=False
    try:
        code=proc.wait(timeout=args.seconds)
    except subprocess.TimeoutExpired:
        timed_out=True
        proc.kill()
        code=proc.wait()
text=log.read_text(errors='replace')
errors=bool(re.search(r'^\s*\?',text,re.M))
markers={key:int(value) for key,value in re.findall(r'^(DIMENSION|LENGTH|ALL_SIMPLE|NONZERO_BACKGROUND) (-?\d+)$',text,re.M)}
expected=json.loads(path.with_suffix('.input.json').read_text())['expected_length']
valid=code==0 and not timed_out and not errors and markers.get('DIMENSION')==0 and markers.get('LENGTH')==expected and markers.get('ALL_SIMPLE')==1
record={'input':path.name,'exit_code':code,'timed_out':timed_out,'singular_errors':errors,'markers':markers,'certificate_ready':valid,'elapsed_seconds':round(time.monotonic()-t0,3),'log':str(log)}
path.with_suffix('.run.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record),flush=True)
print(text[-6000:],flush=True)
