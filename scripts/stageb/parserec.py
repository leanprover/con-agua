import os
HERE=os.path.dirname(os.path.abspath(__file__)); ROOT=os.path.join(HERE,'..','..')
import re,json
src=open(os.path.join(ROOT,'vendor/con-leche/ConLeche/Frontend/Scan/Fast.lean')).read()
ty=open(os.path.join(ROOT,'vendor/con-leche/ConLeche/Frontend/Scan/Types.lean')).read()
keys=re.findall(r'\| (k[A-Za-z]+)', ty[ty.index('inductive Key where'):ty.index('deriving DecidableEq', ty.index('inductive Key where'))])
code={k:i for i,k in enumerate(keys)}
recs={}
for m in re.finditer(r'def (scan\w+Loop) \(b : @& ByteArray\) \(i : USize\) \(wantMember : Bool\)', src):
    name=m.group(1)
    start=m.start()
    end=src.index('termination_by', start)
    body=src[start:end]
    mm0=re.search(r"\(seen &&& (\d+)\) != \1 then \.err ⟨i\.toNat, \.missingKey⟩", body)
    if not mm0: continue
    mask=int(mm0.group(1))
    arms=[]
    for a in re.finditer(r'\| \.(k\w+) =>\n\s+if \(seen &&& (\d+)\) != 0 then \.err ⟨i\.toNat, \.duplicateKey⟩\n\s+else\n\s+(.*)\n', body):
        k,bit,line=a.group(1),int(a.group(2)),a.group(3).strip()
        if line.startswith('let e := numEnd b v'): kind='nat'
        elif line.startswith('let e := scanBinderInfo b v'): kind='binderInfo'
        else:
            mm=re.match(r'match (scan\w+) b v with',line); kind=mm.group(1)
        arms.append((k,code[k],bit,kind))
    recs[name]=dict(mask=mask,arms=arms)
print(json.dumps(recs,indent=0))
