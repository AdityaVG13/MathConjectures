#!/usr/bin/env python3
"""Freeze and replay every project Lean module in a fresh, isolated search path.
No existing project olean is used. External pinned mathlib cache is reused.
"""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
import subprocess, os, json, hashlib, re, tempfile, datetime, argparse, shutil
ROOT=Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('--jobs',type=int,default=3);p.add_argument('--plan',action='store_true');a=p.parse_args()
def run(cmd): return subprocess.check_output(cmd,cwd=ROOT,text=True).strip()
def now(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
modules={}
for base in ['src','new']:
 for path in sorted((ROOT/base).rglob('*.lean')):
  rel=path.relative_to(ROOT/base)
  if any(x.startswith('.') for x in rel.parts):continue
  if rel.parts[0]=='Objects':rel=Path(*rel.parts[1:])
  name='.'.join(rel.with_suffix('').parts)
  if name in modules:raise SystemExit('Duplicate module '+name)
  data=path.read_bytes();imports=[i for line in re.findall(r'^import\s+(.+)$',data.decode(),re.M) for i in line.split()]
  modules[name]={'source':str(path.relative_to(ROOT)),'sha256':hashlib.sha256(data).hexdigest(),'imports':imports}
for m,e in modules.items():
 for i in e['imports']:
  if i not in modules and not i.startswith(('Mathlib','Lean','Std','Init','Batteries','Qq','Aesop','ProofWidgets','Plausible')):raise SystemExit(f'Unaccounted import {m}: {i}')
order=[];todo=set(modules)
while todo:
 ready=sorted(m for m in todo if not (set(modules[m]['imports']) & todo))
 if not ready:raise SystemExit('Dependency cycle '+str(todo))
 order+=ready;todo-=set(ready)
print(f'Validated {len(modules)} project sources',flush=True)
if a.plan:
 print('\n'.join(order));raise SystemExit
version=run(['lake','env','lean','--version'])
if '4.35.0' not in version or 'eb6cafb7290e8' not in version:raise SystemExit('Wrong Lean '+version)
manifest=json.loads((ROOT/'lake-manifest.json').read_text());packages=ROOT/'.lake/packages'
for d in manifest['packages']:
 repo=packages/d['name']
 if run(['git','-C',str(repo),'rev-parse','HEAD'])!=d['rev']:raise SystemExit('Wrong dependency '+d['name'])
 if run(['git','-C',str(repo),'status','--porcelain','--untracked-files=no']):raise SystemExit('Dirty dependency '+d['name'])
prefix=Path(run(['lake','env','lean','--print-prefix']));lean=prefix/'bin/lean'
libs=[]
for x in run(['lake','env','printenv','LEAN_PATH']).split(os.pathsep):
 path=(ROOT/x).resolve()
 if path.is_relative_to(packages.resolve()) and path.exists():libs.append(str(path))
libs.append(str(prefix/'lib/lean'))
out=Path(tempfile.mkdtemp(prefix='complete-replay.',dir=ROOT))
for m,e in modules.items():
 dest=out/(m.replace('.','/')+'.lean');dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(ROOT/e['source'],dest)
env=dict(os.environ);env.pop('LEAN_SRC_PATH',None);env['LEAN_PATH']=os.pathsep.join([str(out)]+libs)
record={'started':now(),'version':version,'modules':modules,'order':order,'lean_path':env['LEAN_PATH'],'results':[],'status':'RUNNING','note':'All project sources rebuilt from frozen copies; no prior project olean used.'}
def save(): (out/'RESULTS.json').write_text(json.dumps(record,indent=2)+'\n')
save();print('Fresh output '+str(out),flush=True)
def compile(m):
 rel=m.replace('.','/');log=out/(rel+'.log')
 with log.open('wb') as f:r=subprocess.run([str(lean),'-o',rel+'.olean',rel+'.lean'],cwd=out,env=env,stdout=f,stderr=subprocess.STDOUT)
 return {'module':m,'exit_code':r.returncode,'finished':now(),'log':str(log.relative_to(out))}
pending=set(order);done=set();failed=False
with ThreadPoolExecutor(max_workers=a.jobs) as pool:
 running={}
 while pending or running:
  for m in order:
   if not failed and m in pending and set(modules[m]['imports']).intersection(modules)<=done and len(running)<a.jobs:
    print('START '+m,flush=True);running[pool.submit(compile,m)]=m;pending.remove(m)
  if not running:break
  ready,_=wait(running,return_when=FIRST_COMPLETED)
  for f in ready:
   m=running.pop(f);r=f.result();record['results'].append(r);save()
   if r['exit_code']:
    failed=True;print('FAIL '+m+'\n'+(out/r['log']).read_text()[-12000:],flush=True)
   else:done.add(m);print('PASS '+m,flush=True)
record['status']='FAILED' if failed or pending else 'COMPLETE';record['finished']=now()
record['live_source_changes']=[m for m,e in modules.items() if hashlib.sha256((ROOT/e['source']).read_bytes()).hexdigest()!=e['sha256']]
save();print(record['status']+': '+str(out),flush=True)
raise SystemExit(1 if record['status']!='COMPLETE' else 0)
