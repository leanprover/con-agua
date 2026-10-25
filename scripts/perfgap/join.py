import re,sys
def rd(p,pat):
    D={}
    for ln in open(p):
        m=re.match(pat,ln)
        if m: D[m.group(3)]=(int(m.group(1).replace(',','')),int(m.group(2).replace(',','')))
    return D
L=rd(sys.argv[1],r'\s*[\d.]+%\s+[\d.]+%\s+([\d,]+)\s+([\d,]+)\s+[\d.]+\s+(\S+)')
C=rd(sys.argv[2],r'\s*[\d.]+%\s+([\d,]+)\s+([\d,]+)\s+[\d.]+\s+(\S+)')
rows=sorted(((n-C.get(f,(0,0))[0],f,n,C.get(f,(0,0))[0],c) for f,(n,c) in L.items()),reverse=True)
totL=sum(v[0] for v in L.values()); totC=sum(v[0] for v in C.values())
print(f"L {totL/1e9:.1f}G clang {totC/1e9:.1f}G gap {(totL-totC)/1e9:.1f}G")
cum=0
for g,f,n,cn,c in rows[:int(sys.argv[3])]:
    cum+=g
    print(f"{f:22s} gap {g/1e9:6.2f}G cum {cum/1e9:6.1f}G ({100*cum/(totL-totC):4.1f}%)  L {n/max(c,1):6.1f}/call clang {cn/max(c,1):6.1f}/call  calls {c/1e6:7.1f}M")
