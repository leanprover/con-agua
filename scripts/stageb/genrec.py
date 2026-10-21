import os
HERE=os.path.dirname(os.path.abspath(__file__)); ROOT=os.path.join(HERE,'..','..')
import json
import subprocess,sys
recs=json.loads(subprocess.check_output([sys.executable,os.path.join(HERE,'parserec.py')]))
ty=open(os.path.join(ROOT,'vendor/con-leche/ConLeche/Frontend/Scan/Types.lean')).read()
NAMES=[("scanStrNameLoop","strName","scan_str_name","`{\"pre\":p,\"str\":s}`"),
 ("scanNumNameLoop","numName","scan_num_name","`{\"i\":n,\"pre\":p}`"),
 ("scanAppExprLoop","app","scan_app","`{\"arg\":A,\"fn\":F}`"),
 ("scanLamExprLoop","binder","scan_binder","a `lam` or `forallE` binder (con-leche's two loops have the same keys; Rust's `scan_binder_expr_loop`)"),
 ("scanLetExprLoop","letE","scan_let","a `letE`"),
 ("scanConstExprLoop","constE","scan_const","`{\"name\":N,\"us\":[…]}`"),
 ("scanProjExprLoop","proj","scan_proj","`{\"idx\":i,\"struct\":S,\"typeName\":T}`"),
 ("scanRuleLoop","rule","scan_rule","a recursor rule"),
 ("LIST:rule","rules","scan_rules","the `[…]` of rules"),
 ("scanIndRecLoop","indRec","scan_ind_rec","a recursor of an inductive declaration"),
 ("LIST:indRec","indRecs","scan_ind_recs","the `[…]` of recursors"),
 ("scanIndTypeLoop","indType","scan_ind_type","a type of an inductive declaration"),
 ("LIST:indType","indTypes","scan_ind_types","the `[…]` of types"),
 ("scanIndCtorLoop","indCtor","scan_ind_ctor","a constructor of an inductive declaration"),
 ("LIST:indCtor","indCtors","scan_ind_ctors","the `[…]` of constructors"),
 ("scanAxiomDeclLoop","axiomD","scan_axiom","an `axiom` declaration"),
 ("scanDefDeclLoop","defD","scan_def","a `def` declaration"),
 ("scanThmDeclLoop","thmD","scan_thm","a `thm` declaration"),
 ("scanOpaqueDeclLoop","opaqueD","scan_opaque","an `opaque` declaration"),
 ("scanQuotDeclLoop","quotD","scan_quot","a `quot` declaration"),
 ("scanIndDeclLoop","indD","scan_ind_decl","an `inductive` declaration"),
]
cap=lambda s: s[0].upper()+s[1:]
keyname={}
import re
keys=re.findall(r'\| (k[A-Za-z]+)', ty[ty.index('inductive Key where'):ty.index('deriving DecidableEq', ty.index('inductive Key where'))])
lit=lambda k: k[1].lower()+k[2:]
# program hypotheses (name, fn string, decl)
H=[("hpw","skip_ws","L.Scan.Leaves.skipWs"),("hpd","skip_digits","L.Scan.Leaves.skipDigits"),
 ("hpk","key_end","L.Scan.Leaves.keyEnd"),("hpn","num_end","L.Scan.Leaves.numEnd"),
 ("hpa","key_at","L.Scan.Key.keyAt"),("hpv","value_at","L.Scan.Key.valueAt"),
 ("hpm","next_member","nextMember"),("hps","slot_nat","slotNat"),
 ("hpmw","match_word","matchWord"),("hpi","scan_binder_info","scanBinderInfo"),
 ("hph","scan_hints","scanHints"),("hpl","scan_nat_list","scanNatList"),
 ("hpml","match_lit","L.Scan.Lit.matchLit"),("hpb","scan_bool","L.Scan.Lit.scanBool"),
 ("hpc","utf8_char","L.Scan.Utf8.utf8Char"),("hpu8","utf8_valid","L.Scan.Str.utf8Valid"),
 ("hpbi","byte_in","L.Scan.Str.byteIn"),("hphv","hex_val","L.Scan.Str.hexVal"),
 ("hp4","hex4","L.Scan.Str.hex4"),("hp3","hex3","L.Scan.Str.hex3"),
 ("hpue","unescape","L.Scan.Str.unescape"),("hpsc","str_close","L.Examples.strClose"),
 ("hpe","has_escape","L.Scan.Leaves.hasEscape"),("hpt","scan_string","L.Scan.Str.scanString")]
for (_,short,fn,_) in NAMES: H.append(("hp_"+short,fn,"scan"+cap(short)))
NH=len(H)
U=lambda k: " ".join(["‹_›"]*k)
ALL="p b hb "+" ".join(h for h,_,_ in H)
spec={
 'nat':"slotNat_spec p b hb "+U(3)+" n",
 'binderInfo':"scanBinderInfo_spec p b hb "+U(2)+" n",
 'scanBool':"L.Scan.Lit.scanBool_spec p "+U(2)+" b hb64 n",
 'scanString':"L.Scan.Str.scanString_spec p b hb "+U(10)+" n",
 'scanNatList':"scanNatList_spec p b hb "+U(3)+" n",
 'scanHints':"scanHints_spec p b hb "+U(8)+" n",
}
for x in ['rules','indRecs','indTypes','indCtors','rule','indRec','indType','indCtor']:
    spec[x]="scan%s_spec %s n"%(cap(x),ALL)
kindmap={'scanRules':'rules','scanIndRecs':'indRecs','scanIndTypes':'indTypes','scanIndCtors':'indCtors'}
model={'nat':"slotNatN b ks v",'binderInfo':"binderInfoN b v",'scanBool':"boolEndN b v",
 'scanString':"L.Scan.Str.scanStringN b v",'scanNatList':"(natListEntryN b v).1",'scanHints':"hintsN b v",
 'rules':"rulesN b v",'indRecs':"indRecsN b v",'indTypes':"indTypesN b v",'indCtors':"indCtorsN b v"}
def lcall(kind):
    if kind=='nat': return ["e := call slot_nat(ks, v);","if e == 0 { return 0 }"]
    if kind=='binderInfo': c="e := call scan_binder_info(v);"
    elif kind=='scanBool': return ["(ok, x, e) := call scan_bool(v);","if ok == 0 { return 0 };","if e <= ks { return 0 }"]
    elif kind=='scanString': c="e := call scan_string(v);"
    elif kind=='scanNatList': c="(e, x) := call scan_nat_list(v);"
    elif kind=='scanHints': c="e := call scan_hints(v);"
    else: c="e := call %s(v);"%{'rules':'scan_rules','indRecs':'scan_ind_recs','indTypes':'scan_ind_types','indCtors':'scan_ind_ctors'}[kind]
    return [c,"if e == 0 { return 0 };","if e <= ks { return 0 }"]
VARS="(p : Prog) (b : Array UInt8) (hb : b.size < 2 ^ 63)\n    "+"\n    ".join(f'({h} : p.lookup "{f}" = some {d})' for h,f,d in H)
INCL=" ".join(h for h,_,_ in H)
out=[]
specs_used={}
for (src,short,fn,desc) in NAMES:
    C=cap(short)
    if src.startswith("LIST:"):
        item=src[5:]
        out.append(f'''/-! ## `{fn}`: {desc} -/

def {short}Loop : Stmt := lblk (i, cnt, w, c, e) {{
  while i < len(IN.u8) {{
    c := IN.u8[i];
    if c == 32 || c == 9 || c == 13 {{
      i += 1
    }} else if c == 93 {{
      if w != 0 && cnt != 0 {{ return 0 }};
      return i + 1
    }} else if c == 44 {{
      if w != 0 {{ return 0 }};
      i += 1;
      w := 1
    }} else if c == 123 {{
      if w == 0 {{ return 0 }};
      e := call scan_{'_'.join(re.findall('[a-z]+|[A-Z][a-z]*',item)).lower()}(i);
      if e == 0 {{ return 0 }};
      if e <= i {{ return 0 }};
      cnt += 1;
      i := e;
      w := 0
    }} else {{
      return 0
    }}
  }}
}}

def scan{C} : FunDecl := lfn (i) locals (cnt, w, c, e) {{
  if i < len(IN.u8) && IN.u8[i] == 91 {{
    i += 1;
    w := 1;
    ⟪{short}Loop⟫
  }};
  return 0
}}

/-- `{fn}(i)`. -/
def {short}N (b : Array UInt8) (i : Word) : Word := objListEntryN ({item}N b) b i

@@SPLIT@@

attribute [local lang_grind] Mbr.err

theorem {short}Loop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n {short}Loop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objListN ({item}N b) b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := {short}Loop) rfl]
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld8, ih,
        {spec[item]}] <;> finish

theorem {short}Loop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) {short}Loop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objListN ({item}N b) b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ :=
  Triple.step_exec ({short}Loop_spec {ALL} (n + 1) s₀)

theorem scan{C}_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "{fn}" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [{short}N b i]; ⊤⦄ := by
  rw [invoke_eq _ hp_{short}]
  simp only [callFn, scan{C}]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, {short}N, objListEntryN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, {short}Loop_step_spec {ALL} n] <;> finish

''')
        continue
    r=recs[src]
    arms=r['arms']; mask=r['mask']
    kinds=[kindmap.get(a[3],a[3]) for a in arms]
    L=[]
    first=True
    for (k,code,bit,_),kind in zip(arms,kinds):
        L.append(f"    {'if' if first else '} else if'} k == {code} {{  -- `{lit(k)}`"); first=False
        L.append(f"      if (seen & {bit}) != 0 {{ return 0 }};")
        for c in lcall(kind): L.append("      "+c.rstrip(';')+";")
        L.append(f"      seen := seen | {bit}")
    L.append("    } else {\n      return 0\n    };")
    body="\n".join(L)
    bitdef=" else ".join(f"if k = {code} then {bit}" for (k,code,bit,_) in arms)+" else 0"
    valdef=" else ".join(f"if k = {code} then {model[kind]}" for (k,code,bit,_),kind in zip(arms,kinds))+" else 0"
    callees=sorted(set(spec[k] for k in kinds),key=str)
    hb64 = "\n    have hb64 : b.size < 2 ^ 64 := by omega" if 'scanBool' in kinds else ""
    out.append(f'''/-! ## `{fn}`: {desc} -/

def {short}Loop : Stmt := lblk (i, w, seen, tag, ks, k, v, e, ok, x) {{
  while 0 == 0 {{
    (tag, ks, w, k, v) := call next_member(i, w);
    if tag == 0 {{ return 0 }};
    if tag == 1 {{
      if w != 0 && seen != 0 {{ return 0 }};
      if (seen & {mask}) != {mask} {{ return 0 }};
      return ks + 1
    }};
{body}
    i := e;
    w := 0
  }}
}}

def scan{C} : FunDecl := lfn (i) locals (w, seen, tag, ks, k, v, e, ok, x) {{
  if i < len(IN.u8) && IN.u8[i] == 123 {{
    i += 1;
    w := 1;
    ⟪{short}Loop⟫
  }};
  return 0
}}

/-- The key bits of {desc}. -/
def {short}Bit (k : Word) : Word :=
  {bitdef}
/-- The value scanners of {desc}. -/
def {short}Val (b : Array UInt8) (k ks v : Word) : Word :=
  {valdef}
/-- `{fn}(i)`. -/
def {short}N (b : Array UInt8) (i : Word) : Word := objEntryN {short}Bit ({short}Val b) {mask} b i

@@SPLIT@@

attribute [local lang_grind] {short}Bit {short}Val Mbr.err

theorem {short}Loop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n {short}Loop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN {short}Bit ({short}Val b) {mask} b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := {short}Loop) rfl]{hb64}
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        nextMember_spec p b hb hpw hpk hpa hpv hpm n,
        {(","+chr(10)+"        ").join(callees)}] <;> finish

theorem {short}Loop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) {short}Loop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN {short}Bit ({short}Val b) {mask} b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ :=
  Triple.step_exec ({short}Loop_spec {ALL} (n + 1) s₀)

theorem scan{C}_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "{fn}" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [{short}N b i]; ⊤⦄ := by
  rw [invoke_eq _ hp_{short}]
  simp only [callFn, scan{C}]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, {short}N, objEntryN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8, {short}Loop_step_spec {ALL} n] <;> finish

''')
defs=[o.split("@@SPLIT@@")[0] for o in out]
prfs=[o.split("@@SPLIT@@")[1] for o in out]
txt="\n".join(defs)+"\n/-! ## Specs -/\n\nsection specs\nvariable "+VARS+"\ninclude hb "+INCL+"\n"+"\n".join(prfs)+"\nend specs\n"
open(os.path.join(HERE,'records_gen.lean'),'w').write(txt)
print(len(txt.splitlines()))
