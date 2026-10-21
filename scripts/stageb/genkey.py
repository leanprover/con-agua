import os
HERE=os.path.dirname(os.path.abspath(__file__)); ROOT=os.path.join(HERE,'..','..')
import re,sys
src=open(os.path.join(ROOT,'vendor/con-leche/ConLeche/Frontend/Scan/Fast.lean')).read()
ty=open(os.path.join(ROOT,'vendor/con-leche/ConLeche/Frontend/Scan/Types.lean')).read()
keys=re.findall(r'\| (k[A-Za-z]+)', ty[ty.index('inductive Key where'):ty.index('deriving DecidableEq', ty.index('inductive Key where'))])
code={k:i for i,k in enumerate(keys)}
body=src[src.index('def keyAt '):src.index('def valueAt')]
body=body[:body.rindex('/--')]
lines=body.split('\n')
# parse: groups by first byte
groups=[]  # (byte, [(kl, [(bytes, key)] or direct key)])
cur=None; curkl=None
for ln in lines:
    s=ln.strip()
    m=re.match(r"\| (\d+) =>",s)
    if m:
        cur=(int(m.group(1)),[]); groups.append(cur); continue
    m=re.match(r"(?:else )?if kl == (\d+) then",s)
    if m:
        curkl=(int(m.group(1)),[]); cur[1].append(curkl); continue
    m=re.match(r"(?:else )?if lit(\d+) b j ([\d ]+) then\s*$",s)
    if m:
        pend=[int(x) for x in m.group(2).split()]; continue
    m=re.match(r"(?:else )?if lit(\d+) b j ([\d ]+) then \.(k\w+)",s)
    if m:
        curkl[1].append(([int(x) for x in m.group(2).split()],m.group(3))); continue
    m=re.match(r"^\.(k\w+)\s",s+' ')
    if m and m.group(1)!='kUnknown':
        if 'pend' in dir() and pend is not None:
            curkl[1].append((pend,m.group(1))); pend=None
        else:
            curkl[1].append((None,m.group(1)))
        continue
    pend=pend if 'pend' in dir() else None
# emit model
out=[]
out.append("def keyAtN (b : Array UInt8) (i kl : Word) : Word :=")
out.append("  let c := byteW b (i + 1)")
first=True
for byte,kls in groups:
    out.append(f"  {'if' if first else 'else if'} c = {byte} then  -- '{chr(byte)}'"); first=False
    f2=True
    for kl,cands in kls:
        out.append(f"    {'if' if f2 else 'else if'} kl = {kl} then"); f2=False
        f3=True
        for bs,k in cands:
            if bs is None:
                out.append(f"      {code[k]}  -- {k}"); f3=None; break
            conds=" ∧ ".join(f"byteW b (i + {t+2}) = {c}" for t,c in enumerate(bs))
            name=chr(byte)+''.join(chr(c) for c in bs)
            out.append(f"      {'if' if f3 else 'else if'} {conds} then {code[k]}  -- \"{name}\""); f3=False
        if f3 is not None: out.append("      else 0")
    out.append("    else 0")
out.append("  else 0")
model="\n".join(out)
# emit L
L=[]
L.append("def keyAt : FunDecl := lfn (i, kl) locals (c) {")
L.append("  c := IN.u8[i + 1];")
for byte,kls in groups:
    L.append(f"  if c == {byte} {{  -- '{chr(byte)}'")
    for kl,cands in kls:
        L.append(f"    if kl == {kl} {{")
        direct=False
        for bs,k in cands:
            if bs is None:
                L.append(f"      return {code[k]}  -- {k}"); direct=True; break
            conds=" && ".join(f"IN.u8[i + {t+2}] == {c}" for t,c in enumerate(bs))
            name=chr(byte)+''.join(chr(c) for c in bs)
            L.append(f"      if {conds} {{ return {code[k]} }};  -- \"{name}\"")
        if not direct: L.append("      return 0")
        L.append("    };")
    L.append("    return 0")
    L.append("  };")
L.append("  return 0")
L.append("}")
print(model); print(); print("\n".join(L))
print(sum(len(k) for _,k in groups), file=sys.stderr)
