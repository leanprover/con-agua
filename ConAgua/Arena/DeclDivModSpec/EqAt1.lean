module

public import ConAgua.Arena.DeclDivModSpec.DivModTypePins
public import ConAgua.Arena.DeclDivModSpec.PureRun
public import ConAgua.Arena.IndRealNames
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.IndInstallSpec.DomsW
import Std.Tactic.BVDecide.Normalize.BitVec
import all ConAgua.Arena.DeclArmsNat
import all ConAgua.Arena.IndIface

@[expose] public section

/-!
# EqAt1: `ConRon.Arena.certCtx`, `ConRon.Arena.eqAt1`, `ConRon.Arena.natOne`, `ConRon.Arena.natVar`

The refinement theorems `natVar_refines`, `natOne_refines`, `eqAt1_refines`, `certCtx_refines` and the lemmas only they use.
-/

section

noncomputable section

/-!
# The `Nat.div` family's pin gate, bottom up: the statement builders (lane `decls3`, `decls3-divmod`)

Part 2: `nat_var`, `nat_one`, `eq_at1`, `cert_ctx` (with `cert_ctx_pins`, `cert_ctx_main`) against
the twin's `natVar`, `natOne`, `eqAt1`, `certCtx`.

* `CertCtxR m cx c`: the 21-word `IW` record at `cx` holds the twin's `CertCtxA` `c` (the word of each
  field, in the layout of `cert_ctx`).
* `StmtAt m p (hyps, e)`: the statement record `[hyps.off, hyps.len, e]` at `p`;
  `StmtL m o l ss`: the slice `(o, l)` of pointers to such records.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## One step of a model, as a lemma -/

theorem CallRef.bind_ {α β : Type} {p : Prog} {f : FnName} {args : List Word}
    {pre : Mem → AState → Prop} {op : AM α}
    {post : Mem → Mem → AState → List Word → α → Prop}
    (h : CallRef p f args pre op post) {n : Nat} {m : Mem} {a : AState} (hpre : pre m a)
    {K : List Word → Mem → Option β} {res : β}
    (hw : ntBW (callW p n f args m) K = some res) :
    ∃ r1 m1 x a1, op.run a = .ok (x, a1) ∧ post m m1 a1 r1 x ∧ K r1 m1 = some res :=
  let ⟨r1, m1, hc, hw⟩ := ntBW_some hw; let ⟨x, a1, hr, hp⟩ := h n m a r1 m1 hpre hc; ⟨r1, m1, x, a1, hr, hp, hw⟩

theorem FRef.bind_ {β : Type} {p : Prog} {f : FnName} {args : List Word} {pre : Mem → Prop}
    {post : Mem → Mem → List Word → Prop} (h : FRef p f args pre post) {n : Nat} {m : Mem}
    (hpre : pre m) {K : List Word → Mem → Option β} {res : β}
    (hw : ntBW (callW p n f args m) K = some res) :
    ∃ r1 m1, post m m1 r1 ∧ K r1 m1 = some res :=
  let ⟨r1, m1, hc, hw⟩ := ntBW_some hw; ⟨r1, m1, h n m r1 m1 hpre hc, hw⟩

/-! ## The lookups -/

structure DmProg2 (p : Prog) : Prop extends DmProg1 p where
  lNatVar : p.lookup "nat_var" = some natVarL
  lNatOne : p.lookup "nat_one" = some natOneL
  lEqAt1 : p.lookup "eq_at1" = some eqAt1L
  lIl : IlF p
  lCertCtxPins : p.lookup "cert_ctx_pins" = some certCtxPinsL
  lCertCtxMain : p.lookup "cert_ctx_main" = some certCtxMainL
  lCertCtx : p.lookup "cert_ctx" = some certCtxL
  lCertGuard : p.lookup "cert_guard" = some certGuardL
  lCertEq : p.lookup "cert_eq" = some certEqL
  lCertHalves : p.lookup "cert_halves" = some certHalvesL
  lStmt1 : p.lookup "stmt1" = some stmt1
  lCertTwoEqs : p.lookup "cert_two_eqs" = some certTwoEqsL
  lCertGcd : p.lookup "cert_gcd" = some certGcdL
  lCertShiftLeft : p.lookup "cert_shift_left" = some certShiftLeftL
  lCertShiftRight : p.lookup "cert_shift_right" = some certShiftRightL
  lCertLand : p.lookup "cert_land" = some certLandL
  lCertLorRhs : p.lookup "cert_lor_rhs" = some certLorRhsL
  lCertLor : p.lookup "cert_lor" = some certLorL
  lCertXorRhs : p.lookup "cert_xor_rhs" = some certXorRhsL
  lCertXor : p.lookup "cert_xor" = some certXorL
  lCertRecRhs : p.lookup "cert_rec_rhs" = some certRecRhsL
  lCertDivModEqs : p.lookup "cert_div_mod_eqs" = some certDivModEqsL
  lCertDivModGuards : p.lookup "cert_div_mod_guards" = some certDivModGuardsL
  lCertDivMod : p.lookup "cert_div_mod" = some certDivModL
  lDivModCertStmtsAt : p.lookup "div_mod_cert_stmts_at" = some divModCertStmtsAtL
  lDivModCertStmts : p.lookup "div_mod_cert_stmts" = some divModCertStmtsL
  lDivModCertApplied : p.lookup "div_mod_cert_applied" = some divModCertAppliedL

section nat
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

/-! ### `Sim` steps for the certificate builders -/

/-- `w` is the word of the index `x` (`decW0E` of a result is `DW (r.headD 0) x`). -/
def DW {κ : IdxKind} (w : Word) (x : Idx κ) : Prop := H w ∧ decI w = x

theorem DW.of {κ : IdxKind} {w : Word} {x : Idx κ} (e : w = x.word.toUInt64) : DW w x :=
  e ▸ ⟨dmWord_lt32 x, decI_word x⟩

/-- The post of a `KeepPost` callee, its growth counted from `m0`. -/
abbrev KG {α : Type} (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m0 : Mem)
    (dec : Mem → List Word → α → Prop) : List Word → α → Mem → AState → Prop :=
  fun r x m' a' => StageR vis fe m' a' ∧ IWGrow m0 m' ∧ dec m' r x

theorem CallRef.simG {α : Type} {f : FnName} {args : List Word} {pre : Mem → AState → Prop}
    {op : AM α} {dec : Mem → List Word → α → Prop} (h : CallRef p f args pre op (KeepPost vis fe dec))
    {n : Nat} {m m0 : Mem} {a : AState} (hp : pre m a) (hG : IWGrow m0 m) :
    Sim (callW p n f args m) op a (KG dn vis fe m0 dec) :=
  (h.sim hp).mono fun _ _ _ _ ⟨hS', hg, hd⟩ => ⟨hS', hG.trans hg, hd⟩

theorem natAp2_dw (hN : NatEqProg p) {n : Nat} {m m0 : Mem} {a : AState} {c x y : Word} {c' : NIdx}
    {x' y' : EIdx} (hS : StageR vis fe m a) (hG : IWGrow m0 m) (h1 : DW c c') (h2 : DW x x')
    (h3 : DW y y') : Sim (callW p n "nat_ap2" [c, x, y] m) (natAp2 c' x' y') a (KG dn vis fe m0 decW0E) := by
  obtain ⟨h1, rfl⟩ := h1; obtain ⟨h2, rfl⟩ := h2; obtain ⟨h3, rfl⟩ := h3
  exact (natAp2_ref hN c x y).simG ⟨hS, h1, h2, h3⟩ hG

/-- A model function's `RelW` as a `Sim`. -/
theorem RelW.simS {α : Type} {W : Mem → List Word → Option (List Word × Mem)} {args : List Word}
    {pre : Mem → AState → Prop} {op : AM α} {post : Mem → Mem → AState → List Word → α → Prop}
    (h : RelW W args pre op post) {m : Mem} {a : AState} (hp : pre m a) :
    Sim (W m args) op a (fun r x m' a' => post m m' a' r x) := fun r m' e => h m m' a r e hp

/-! ## `nat_var` -/

/-- **`nat_var` is its model `natVarW`** (generated). -/
l_model natVar_specW (p : Prog) (hp : p.lookup "nat_var" = some natVarL)
  fns [hp ↦ natVarW list]
  specs [callW_spec p n "pin_at", callW_spec p n "const_e", callW_spec p n "intern_fvar"]
  grind [arena_grind] heartbeats 1600000 bind ntBW

theorem natVar_ref (hD : DmProg2 p) (i : Word) :
    CallRef p "nat_var" [i] (StageR vis fe) (natVar i.toNat) (KeepPost vis fe decW0E) := by
  sorry

/-! ## `nat_one` -/

/-- **`nat_one` is its model `natOneW`** (generated). -/
l_model natOne_specW (p : Prog) (hp : p.lookup "nat_one" = some natOneL)
  fns [hp ↦ natOneW list]
  specs [callW_spec p n "pin_at", callW_spec p n "const_e", callW_spec p n "nat_ap1"]
  grind [arena_grind] heartbeats 1600000 bind ntBW

theorem natOne_ref (hD : DmProg2 p) :
    CallRef p "nat_one" [] (StageR vis fe) natOne (KeepPost vis fe decW0E) := by
  sorry

/-! ## `eq_at1` -/

theorem slNew1_dec {κ : IdxKind} {m m1 : Mem} {r : List Word} {x : Word} (hR : RecPost m m1 r [x]) (hx : H x)
    (hr : r = [r.headD 0, 1]) :
    decHL m1 (r.headD 0).toNat (r.tail.headD 0).toNat = some [(decI x : Idx κ)] := by
  obtain ⟨hq, -, -, -, hget⟩ := hR
  have hq' : (r.headD 0).toNat = iwTop m := by rw [hq]; rfl
  have hr1 : r.tail.headD 0 = 1 := by rw [hr]; rfl
  rw [hr1, hq']
  have := decHL_words (k := κ) m1 [x] (iwTop m) (by simpa using hx)
    (fun j hj => by simpa [iwA] using hget j hj)
  simpa using this

/-- **`eq_at1` is its model `eqAt1W`** (generated). -/
l_model eqAt1_specW (p : Prog) (hp : p.lookup "eq_at1" = some eqAt1L) (hil : IlF p)
  fns [hp ↦ eqAt1W list]
  specs [callW_spec p n "pin_word", callW_spec p n "intern_succ", callW_spec p n "sl_new1", ilF_spec p hil n, callW_spec p n "pin_at", callW_spec p n "intern_const", callW_spec p n "mk_app"]
  grind [arena_grind] heartbeats 1600000 bind ntBW

theorem eqAt1_ref (hD : DmProg2 p) (ty a b : Word) :
    CallRef p "eq_at1" [ty, a, b] (StageR vis fe)
      (eqAt1 (decE ty) (decE a) (decE b)) (KeepPost vis fe decW0E) := by
  sorry

/-! ## `cert_ctx` -/

/-- The 21 words of a context, in `cert_ctx`'s layout. -/
def ctxWords (c : CertCtxA) : List Word :=
  [c.natTy.word.toUInt64, c.x.word.toUInt64, c.y.word.toUInt64, c.one.word.toUInt64,
   c.bleN.word.toUInt64, c.boolTy.word.toUInt64, c.bT.word.toUInt64, c.bF.word.toUInt64,
   c.z.word.toUInt64, c.two.word.toUInt64, c.modN.word.toUInt64, c.divN.word.toUInt64,
   c.addN.word.toUInt64, c.mulN.word.toUInt64, c.subN.word.toUInt64, c.gcdN.word.toUInt64,
   c.slN.word.toUInt64, c.srN.word.toUInt64, c.landN.word.toUInt64, c.lorN.word.toUInt64,
   c.xorN.word.toUInt64]

/-- **The context record**: `IW[cx ‥ cx + 20]` holds the context's words, below the pool's top. -/
def CertCtxR (m : Mem) (cx : Word) (c : CertCtxA) : Prop :=
  cx.toNat + 21 ≤ iwTop m ∧ ∀ j < 21, iwA m (cx.toNat + j) = (ctxWords c)[j]?

theorem CertCtxR.grow {m m' : Mem} {cx : Word} {c : CertCtxA} (h : CertCtxR m cx c) (hg : IWGrow m m') :
    CertCtxR m' cx c := by
  sorry

/-- A field of the context, as the word `cert_*` reads. -/
theorem CertCtxR.rd {m : Mem} {cx : Word} {c : CertCtxA} (h : CertCtxR m cx c) (k : Word)
    (hk : k.toNat < 21) : rdW (m.arr64 IW) (cx + k) = (ctxWords c).getD k.toNat 0 := by
  sorry

theorem RecPost.rd {m m' : Mem} {r ws : List Word} (h : RecPost m m' r ws) (k : Word)
    (hk : k.toNat < ws.length) : rdW (m'.arr64 IW) (r.headD 0 + k) = ws.getD k.toNat 0 := by
  obtain ⟨hq, -, -, htop, hget⟩ := h
  have hq' : (r.headD 0).toNat = iwTop m := by rw [hq]; rfl
  have ht : iwTop m' < 2 ^ 64 := (rdW (m'.arr64 CTL) 200).toNat_lt
  have hx : (r.headD 0 + k).toNat = iwTop m + k.toNat := by
    rw [UInt64.toNat_add, hq']; exact Nat.mod_eq_of_lt (by omega)
  have := hget k.toNat hk
  simp only [rdW, hx, this]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

theorem CertCtxR.of_rec {m m' : Mem} {r : List Word} {c : CertCtxA} (h : RecPost m m' r (ctxWords c)) :
    CertCtxR m' (r.headD 0) c := by
  obtain ⟨hq, -, -, htop, hget⟩ := h
  have hq' : (r.headD 0).toNat = iwTop m := by rw [hq]; rfl
  refine ⟨by rw [hq', htop]; simp [ctxWords], fun j hj => ?_⟩
  rw [hq']
  simpa [iwA] using hget j (by simpa [ctxWords] using hj)

/-! ### The twin's pin reads and interners keep the pins -/

theorem keeps_pinAt (i : Nat) : Keeps cp (pinAt i) := by prim_keeps pinAt
theorem keeps_pinEmptyLevels : Keeps cp pinEmptyLevels := by prim_keeps pinEmptyLevels
theorem keeps_constE (n : NIdx) : Keeps cp (constE n) := by
  unfold constE emptyLevels
  exact Keeps.bind keeps_pinEmptyLevels fun _ => keeps_internE _
theorem keeps_natAp1 (n : NIdx) (a : EIdx) : Keeps cp (natAp1 n a) := by
  unfold natAp1
  exact Keeps.bind (keeps_constE _) fun _ => keeps_internE _
theorem keeps_natVar (i : Nat) : Keeps cp (natVar i) := by
  unfold natVar pinNat
  exact Keeps.bind (keeps_pinAt _) fun _ => Keeps.bind (keeps_constE _) fun _ => keeps_internE _
theorem keeps_natOne : Keeps cp natOne := by
  unfold natOne pinNatSucc pinNatZero
  exact Keeps.bind (keeps_pinAt _) fun _ => Keeps.bind (keeps_pinAt _) fun _ =>
    Keeps.bind (keeps_constE _) fun _ => keeps_natAp1 _ _

theorem pins_of_keeps {α : Type} {op : AM α} (h : Keeps cp op) {a a' : AState} {x : α}
    (hr : op.run a = .ok (x, a')) : a'.pins = a.pins := congrArg Prod.snd (h.run hr)

/-- A pin read at a state with the same pins. -/
theorem pinAt_run' {m : Mem} {a a' : AState} (hF : PinsFull m a.pins) (hp : a'.pins = a.pins)
    (i : Nat) (hi : i < 51) : (pinAt i).run a' = .ok (decI (pinW m (1 + i)), a') :=
  pinAt_run (hp ▸ hF) i hi

/-! ## `cert_ctx` -/

/-- The memory after `cert_ctx_pins(q, pi)`. -/
def certCtxPinsMem (m : Mem) (q pi : Word) : Mem := (((((((((((m).set64 IW (q + 10) (rdW (m.arr64 IW) (pi + 8))).set64 IW (q + 11) (rdW (m.arr64 IW) (pi + 7))).set64 IW (q + 12) (rdW (m.arr64 IW) (pi + 1))).set64 IW (q + 13) (rdW (m.arr64 IW) (pi + 3))).set64 IW (q + 14) (rdW (m.arr64 IW) (pi + 2))).set64 IW (q + 15) (rdW (m.arr64 IW) (pi + 9))).set64 IW (q + 16) (rdW (m.arr64 IW) (pi + 13))).set64 IW (q + 17) (rdW (m.arr64 IW) (pi + 14))).set64 IW (q + 18) (rdW (m.arr64 IW) (pi + 10))).set64 IW (q + 19) (rdW (m.arr64 IW) (pi + 11))).set64 IW (q + 20) (rdW (m.arr64 IW) (pi + 12))

theorem certCtxPinsMem_eq (m : Mem) (q pi : Word) :
    certCtxPinsMem m q pi = wrIW m (q + 10) [rdW (m.arr64 IW) (pi + 8), rdW (m.arr64 IW) (pi + 7), rdW (m.arr64 IW) (pi + 1), rdW (m.arr64 IW) (pi + 3), rdW (m.arr64 IW) (pi + 2), rdW (m.arr64 IW) (pi + 9), rdW (m.arr64 IW) (pi + 13), rdW (m.arr64 IW) (pi + 14), rdW (m.arr64 IW) (pi + 10), rdW (m.arr64 IW) (pi + 11), rdW (m.arr64 IW) (pi + 12)] := by
  simp [certCtxPinsMem, wrIW, UInt64.add_assoc]

theorem certCtxPins_specW (p : Prog) (hp : p.lookup "cert_ctx_pins" = some certCtxPinsL)
    (n : Nat) (s₀ : St) (q pi : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "cert_ctx_pins" [q, pi]
    ⦃fun r s' => LocEq s' s₀ ∧ r = [0] ∧ s'.mem = certCtxPinsMem s₀.mem q pi; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, certCtxPinsL]
  sym only [lang_grind, arena_grind] =>
    vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64] <;>
    finish (gen := 20) (instances := 10000) [certCtxPinsMem, rdW_eq]

theorem certCtxPins_model {p : Prog} (hp : p.lookup "cert_ctx_pins" = some certCtxPinsL) {n : Nat}
    {m m' : Mem} {q pi : Word} {r : List Word}
    (h : callW p n "cert_ctx_pins" [q, pi] m = some (r, m')) :
    r = [0] ∧ m' = certCtxPinsMem m q pi := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ k =>
  obtain ⟨s', rfl, -, hr, hm⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (certCtxPins_specW p hp k _ q pi) h
  exact ⟨hr, hm⟩

/-- The memory after `cert_ctx_main(q, …)`. -/
def certCtxMainMem (m : Mem) (q natTy x y one bleN boolTy bT bF z two : Word) : Mem := ((((((((((m).set64 IW (q) (natTy)).set64 IW (q + 1) (x)).set64 IW (q + 2) (y)).set64 IW (q + 3) (one)).set64 IW (q + 4) (bleN)).set64 IW (q + 5) (boolTy)).set64 IW (q + 6) (bT)).set64 IW (q + 7) (bF)).set64 IW (q + 8) (z)).set64 IW (q + 9) (two)

theorem certCtxMain_specW (p : Prog) (hp : p.lookup "cert_ctx_main" = some certCtxMainL)
    (n : Nat) (s₀ : St) (q natTy x y one bleN boolTy bT bF z two : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "cert_ctx_main" [q, natTy, x, y, one, bleN, boolTy, bT, bF, z, two]
    ⦃fun r s' => LocEq s' s₀ ∧ r = [0] ∧ s'.mem = certCtxMainMem s₀.mem q natTy x y one bleN boolTy bT bF z two; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, certCtxMainL]
  sym only [lang_grind, arena_grind] =>
    vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64] <;>
    finish (gen := 20) (instances := 10000) [certCtxMainMem]

theorem certCtxMain_model {p : Prog} (hp : p.lookup "cert_ctx_main" = some certCtxMainL) {n : Nat}
    {m m' : Mem} {q natTy x y one bleN boolTy bT bF z two : Word} {r : List Word}
    (h : callW p n "cert_ctx_main" [q, natTy, x, y, one, bleN, boolTy, bT, bF, z, two] m = some (r, m')) :
    r = [0] ∧ m' = certCtxMainMem m q natTy x y one bleN boolTy bT bF z two := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ k =>
  obtain ⟨s', rfl, -, hr, hm⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (certCtxMain_specW p hp k _ q natTy x y one bleN boolTy bT bF z two) h
  exact ⟨hr, hm⟩

/-- The model of `cert_ctx()`. -/
def certCtxW (p : Prog) (n : Nat) (m : Mem) : Option (List Word × Mem) :=
  ntBW (callW p n "nat_op_pins" [] m) fun r0 m0 =>
  ntBW (callW p n "const_e" [rdW (m0.arr64 IW) (r0.headD 0 + 15)] m0) fun r1 m1 =>
  ntBW (callW p n "nat_var" [0] m1) fun r2 m2 =>
  ntBW (callW p n "nat_var" [1] m2) fun r3 m3 =>
  ntBW (callW p n "nat_one" [] m3) fun r4 m4 =>
  ntBW (callW p n "const_e" [rdW (m4.arr64 IW) (r0.headD 0 + 20)] m4) fun r5 m5 =>
  ntBW (callW p n "const_e" [rdW (m5.arr64 IW) (r0.headD 0 + 18)] m5) fun r6 m6 =>
  ntBW (callW p n "const_e" [rdW (m6.arr64 IW) (r0.headD 0 + 19)] m6) fun r7 m7 =>
  ntBW (callW p n "const_e" [rdW (m7.arr64 IW) (r0.headD 0 + 16)] m7) fun r8 m8 =>
  ntBW (callW p n "nat_ap1" [rdW (m8.arr64 IW) (r0.headD 0 + 17), r4.headD 0] m8) fun r9 m9 =>
  ntBW (callW p n "iw_alloc" [21] m9) fun rq mq =>
  ntBW (callW p n "cert_ctx_pins" [rq.headD 0, r0.headD 0] mq) fun _ mp =>
  ntBW (callW p n "cert_ctx_main" [rq.headD 0, r1.headD 0, r2.headD 0, r3.headD 0, r4.headD 0,
    rdW (m4.arr64 IW) (r0.headD 0 + 6), r5.headD 0, r6.headD 0, r7.headD 0, r8.headD 0, r9.headD 0] mp) fun _ mf =>
  some ([rq.headD 0], mf)

private theorem getElem_toNat_rdW {a : Array Word} {x : Word} (h : x.toNat < a.size) :
    a[x.toNat] = rdW a x := (rdW_eq a x _ rfl h).symm

/-- Straight-line code: after `vcgen`, each callee's `LocEq` post fixes the next state's locals, so
the states are taken apart and their locals substituted; `certCtxW` then unfolds call by call.
(`sym … finish` took ~265 s here, crawling the `setLoc` chains.) -/
theorem certCtx_specW (p : Prog) (hp : p.lookup "cert_ctx" = some certCtxL) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "cert_ctx" []
    ⦃fun r s' => LocEq s' s₀ ∧ certCtxW p n s₀.mem = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, certCtxL]
  vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "nat_op_pins", callW_spec p n "const_e", callW_spec p n "nat_var",
      callW_spec p n "nat_one", callW_spec p n "nat_ap1", callW_spec p n "iw_alloc",
      callW_spec p n "cert_ctx_pins", callW_spec p n "cert_ctx_main"]
  all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons, BinOp.eval, Nat.reduceEqDiff,
      reduceIte] at *)
  · rfl
  · rename_i s13 a13 rs11 s12 a12 h6 rs10 s11 rs9 s10 a11 rs8 s9 a10 rs7 s8 a9 h5 h4 rs6 s7 h3 rs5 s6
      h2 rs4 s5 h1 rs3 s4 h0 rs2 s3 rs1 s2 a8 rs0 s1 s0' a7 a6 a5 a4 a3 a2 a1 a0
    subst a13
    obtain ⟨l12, c12⟩ := a12
    obtain ⟨l11, c11⟩ := a7
    obtain ⟨l10, c10⟩ := a11
    obtain ⟨l9, c9⟩ := a10
    obtain ⟨l8, c8⟩ := a9
    obtain ⟨l7, c7⟩ := a6
    obtain ⟨l6, c6⟩ := a5
    obtain ⟨l5, c5⟩ := a4
    obtain ⟨l4, c4⟩ := a3
    obtain ⟨l3, c3⟩ := a2
    obtain ⟨l2, c2⟩ := a8
    obtain ⟨l1, c1⟩ := a1
    obtain ⟨l0, c0⟩ := a0
    obtain ⟨m12, L12⟩ := s12
    obtain ⟨m11, L11⟩ := s11
    obtain ⟨m10, L10⟩ := s10
    obtain ⟨m9, L9⟩ := s9
    obtain ⟨m8, L8⟩ := s8
    obtain ⟨m7, L7⟩ := s7
    obtain ⟨m6, L6⟩ := s6
    obtain ⟨m5, L5⟩ := s5
    obtain ⟨m4, L4⟩ := s4
    obtain ⟨m3, L3⟩ := s3
    obtain ⟨m2, L2⟩ := s2
    obtain ⟨m1, L1⟩ := s1
    obtain ⟨m0, L0⟩ := s0'
    simp only [LocEq] at l12 l11 l10 l9 l8 l7 l6 l5 l4 l3 l2 l1 l0
    subst l12 l11 l10 l9 l8 l7 l6 l5 l4 l3 l2 l1 l0
    simp (config := {decide := true}) only [St.setLoc_loc, Locals.init_nil, reduceIte,
      getElem_toNat_rdW] at c12 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 ⊢
    simp only [certCtxW, c12, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, c0, bW_some, Sig.retVal, Sig.retOr]

theorem rdW_iw_grow {m m' : Mem} (hg : IWGrow m m') {i : Word} (hi : i.toNat < iwTop m) :
    rdW (m'.arr64 IW) i = rdW (m.arr64 IW) i := by
  simp only [rdW]; rw [hg.iwGet i.toNat hi]

theorem RecPost.rdGrow {m m0 mk : Mem} {r ws : List Word} (h : RecPost m m0 r ws)
    (hg : IWGrow m0 mk) (k : Word) (hk : k.toNat < ws.length) :
    rdW (mk.arr64 IW) (r.headD 0 + k) = ws.getD k.toNat 0 := by
  have hq' : (r.headD 0).toNat = iwTop m := by rw [h.1]; rfl
  have ht : iwTop m0 < 2 ^ 64 := (rdW (m0.arr64 CTL) 200).toNat_lt
  have hx : (r.headD 0 + k).toNat = iwTop m + k.toNat := by
    rw [UInt64.toNat_add, hq']; exact Nat.mod_eq_of_lt (by have := h.2.2.2.1; omega)
  rw [rdW_iw_grow hg (by rw [hx]; have := h.2.2.2.1; omega)]
  exact RecPost.rd h k hk

/-- A record written in two slices, the second one first. -/
theorem recPost_wr2 (m : Mem) (ws1 ws2 : List Word) (k : Word)
    (hk : k.toNat = ws1.length + ws2.length) (hI : IWOK m)
    (hroom : iwTop m + (ws1.length + ws2.length) ≤ (m.arr64 IW).size) :
    RecPost m (wrIW (wrIW (allocMem m k) (rdW (m.arr64 CTL) 200 + UInt64.ofNat ws1.length) ws2)
      (rdW (m.arr64 CTL) 200) ws1) [rdW (m.arr64 CTL) 200] (ws1 ++ ws2) := by
  sorry

/-- `ctxWords` of the context of `decI`s. -/
theorem ctxWords_decI (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : Word)
    (h0 : H w0) (h1 : H w1) (h2 : H w2) (h3 : H w3) (h4 : H w4) (h5 : H w5) (h6 : H w6) (h7 : H w7)
    (h8 : H w8) (h9 : H w9) (h10 : H w10) (h11 : H w11) (h12 : H w12) (h13 : H w13) (h14 : H w14)
    (h15 : H w15) (h16 : H w16) (h17 : H w17) (h18 : H w18) (h19 : H w19) (h20 : H w20) :
    ctxWords ⟨decI w0, decI w1, decI w2, decI w3, decI w4, decI w5, decI w6, decI w7, decI w8,
      decI w9, decI w10, decI w11, decI w12, decI w13, decI w14, decI w15, decI w16, decI w17,
      decI w18, decI w19, decI w20⟩ =
    [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20] := by
  simp only [ctxWords, decI_word_self _ h0, decI_word_self _ h1, decI_word_self _ h2,
    decI_word_self _ h3, decI_word_self _ h4, decI_word_self _ h5, decI_word_self _ h6,
    decI_word_self _ h7, decI_word_self _ h8, decI_word_self _ h9, decI_word_self _ h10,
    decI_word_self _ h11, decI_word_self _ h12, decI_word_self _ h13, decI_word_self _ h14,
    decI_word_self _ h15, decI_word_self _ h16, decI_word_self _ h17, decI_word_self _ h18,
    decI_word_self _ h19, decI_word_self _ h20]

theorem chain10_eq (mp : Mem) (q v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : Word) :
    (((((((((mp.set64 IW q v0).set64 IW (q + 1) v1).set64 IW (q + 2) v2).set64 IW (q + 3) v3).set64 IW
      (q + 4) v4).set64 IW (q + 5) v5).set64 IW (q + 6) v6).set64 IW (q + 7) v7).set64 IW
      (q + 8) v8).set64 IW (q + 9) v9 = wrIW mp q [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9] := by
  simp [wrIW, UInt64.add_assoc]

theorem certCtx_ref (hD : DmProg2 p) :
    CallRef p "cert_ctx" [] (StageR vis fe) certCtx
      (KeepPost vis fe (fun m r (c : CertCtxA) => CertCtxR m (r.headD 0) c)) := by
  sorry

/-! ### The context's fields -/

theorem CertCtxR.f0 {m : Mem} {cx : Word} {c : CertCtxA} (h : CertCtxR m cx c) :
    rdW (m.arr64 IW) cx = c.natTy.word.toUInt64 := by
  have := h.rd 0 (by decide); rwa [UInt64.add_zero] at this

theorem CertCtxR.f1 {m : Mem} {cx : Word} {c : CertCtxA} (h : CertCtxR m cx c) :
    rdW (m.arr64 IW) (cx + 1) = c.x.word.toUInt64 := h.rd 1 (by decide)

theorem CertCtxR.f2 {m : Mem} {cx : Word} {c : CertCtxA} (h : CertCtxR m cx c) :
    rdW (m.arr64 IW) (cx + 2) = c.y.word.toUInt64 := h.rd 2 (by decide)

theorem CertCtxR.f3 {m : Mem} {cx : Word} {c : CertCtxA} (h : CertCtxR m cx c) :
    rdW (m.arr64 IW) (cx + 3) = c.one.word.toUInt64 := h.rd 3 (by decide)

theorem CertCtxR.f4 {m : Mem} {cx : Word} {c : CertCtxA} (h : CertCtxR m cx c) :
    rdW (m.arr64 IW) (cx + 4) = c.bleN.word.toUInt64 := h.rd 4 (by decide)

theorem CertCtxR.f5 {m : Mem} {cx : Word} {c : CertCtxA} (h : CertCtxR m cx c) :
    rdW (m.arr64 IW) (cx + 5) = c.boolTy.word.toUInt64 := h.rd 5 (by decide)

theorem CertCtxR.f6 {m : Mem} {cx : Word} {c : CertCtxA} (h : CertCtxR m cx c) :
    rdW (m.arr64 IW) (cx + 6) = c.bT.word.toUInt64 := h.rd 6 (by decide)

theorem CertCtxR.f7 {m : Mem} {cx : Word} {c : CertCtxA} (h : CertCtxR m cx c) :
    rdW (m.arr64 IW) (cx + 7) = c.bF.word.toUInt64 := h.rd 7 (by decide)

theorem CertCtxR.f8 {m : Mem} {cx : Word} {c : CertCtxA} (h : CertCtxR m cx c) :
    rdW (m.arr64 IW) (cx + 8) = c.z.word.toUInt64 := h.rd 8 (by decide)

theorem CertCtxR.f9 {m : Mem} {cx : Word} {c : CertCtxA} (h : CertCtxR m cx c) :
    rdW (m.arr64 IW) (cx + 9) = c.two.word.toUInt64 := h.rd 9 (by decide)

theorem CertCtxR.f10 {m : Mem} {cx : Word} {c : CertCtxA} (h : CertCtxR m cx c) :
    rdW (m.arr64 IW) (cx + 10) = c.modN.word.toUInt64 := h.rd 10 (by decide)

theorem CertCtxR.f11 {m : Mem} {cx : Word} {c : CertCtxA} (h : CertCtxR m cx c) :
    rdW (m.arr64 IW) (cx + 11) = c.divN.word.toUInt64 := h.rd 11 (by decide)

theorem CertCtxR.f12 {m : Mem} {cx : Word} {c : CertCtxA} (h : CertCtxR m cx c) :
    rdW (m.arr64 IW) (cx + 12) = c.addN.word.toUInt64 := h.rd 12 (by decide)

theorem CertCtxR.f13 {m : Mem} {cx : Word} {c : CertCtxA} (h : CertCtxR m cx c) :
    rdW (m.arr64 IW) (cx + 13) = c.mulN.word.toUInt64 := h.rd 13 (by decide)

theorem CertCtxR.f14 {m : Mem} {cx : Word} {c : CertCtxA} (h : CertCtxR m cx c) :
    rdW (m.arr64 IW) (cx + 14) = c.subN.word.toUInt64 := h.rd 14 (by decide)

theorem CertCtxR.f15 {m : Mem} {cx : Word} {c : CertCtxA} (h : CertCtxR m cx c) :
    rdW (m.arr64 IW) (cx + 15) = c.gcdN.word.toUInt64 := h.rd 15 (by decide)

theorem CertCtxR.f16 {m : Mem} {cx : Word} {c : CertCtxA} (h : CertCtxR m cx c) :
    rdW (m.arr64 IW) (cx + 16) = c.slN.word.toUInt64 := h.rd 16 (by decide)

theorem CertCtxR.f17 {m : Mem} {cx : Word} {c : CertCtxA} (h : CertCtxR m cx c) :
    rdW (m.arr64 IW) (cx + 17) = c.srN.word.toUInt64 := h.rd 17 (by decide)

theorem CertCtxR.f18 {m : Mem} {cx : Word} {c : CertCtxA} (h : CertCtxR m cx c) :
    rdW (m.arr64 IW) (cx + 18) = c.landN.word.toUInt64 := h.rd 18 (by decide)

theorem CertCtxR.f19 {m : Mem} {cx : Word} {c : CertCtxA} (h : CertCtxR m cx c) :
    rdW (m.arr64 IW) (cx + 19) = c.lorN.word.toUInt64 := h.rd 19 (by decide)

theorem CertCtxR.f20 {m : Mem} {cx : Word} {c : CertCtxA} (h : CertCtxR m cx c) :
    rdW (m.arr64 IW) (cx + 20) = c.xorN.word.toUInt64 := h.rd 20 (by decide)

theorem decE_word (x : EIdx) : decE x.word.toUInt64 = x := decI_word x

theorem decE_eq_decI (w : Word) : (decE w : EIdx) = decI w := rfl

@[refines ConRon.Arena.natVar]
theorem natVar_refines (hD : DmProg2 p) (i : Word) :
    RefAM p "nat_var" [i] (StageR vis fe) (natVar i.toNat) (KeepPost vis fe decW0E) :=
  (natVar_ref hD i).refAM

@[refines ConRon.Arena.natOne]
theorem natOne_refines (hD : DmProg2 p) :
    RefAM p "nat_one" [] (StageR vis fe) natOne (KeepPost vis fe decW0E) :=
  (natOne_ref hD ).refAM

@[refines ConRon.Arena.eqAt1]
theorem eqAt1_refines (hD : DmProg2 p) (ty a b : Word) :
    RefAM p "eq_at1" [ty, a, b] (StageR vis fe)
      (eqAt1 (decE ty) (decE a) (decE b)) (KeepPost vis fe decW0E) :=
  (eqAt1_ref hD ty a b).refAM

instance : Inhabited CertCtxA :=
  ⟨⟨default, default, default, default, default, default, default, default, default, default,
    default, default, default, default, default, default, default, default, default, default,
    default⟩⟩

@[refines ConRon.Arena.certCtx]
theorem certCtx_refines (hD : DmProg2 p) :
    RefAM p "cert_ctx" [] (StageR vis fe) certCtx
      (KeepPost vis fe (fun m r (c : CertCtxA) => CertCtxR m (r.headD 0) c)) :=
  (certCtx_ref hD ).refAM

end nat

end L.Ind

end

end

section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

section nat
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

theorem Rec3At.grow {m m' : Mem} {p a b c : Word} (h : Rec3At m p a b c) (hg : IWGrow m m') :
    Rec3At m' p a b c := by
  sorry

theorem rec3At_of_post {m m1 : Mem} {r : List Word} {a b c : Word} (h : RecPost m m1 r [a, b, c])
    (_hI : IWOK m) : Rec3At m1 (r.headD 0) a b c := by
  obtain ⟨hq, hK, hroom, htop, hget⟩ := h
  have hq' : (r.headD 0).toNat = iwTop m := by rw [hq]; rfl
  refine ⟨by rw [hq']; simp at htop; omega, ?_, ?_, ?_⟩
  · have := hget 0 (by simp); simp only [iwA, hq']; simpa using this
  · have := hget 1 (by simp); simp only [iwA, hq']; simpa using this
  · have := hget 2 (by simp); simp only [iwA, hq']; simpa using this

theorem StmtAt.grow {m m' : Mem} {p : Word} {st : List EIdx × EIdx} (h : StmtAt m p st)
    (hg : IWGrow m m') : StmtAt m' p st := by
  obtain ⟨ho, hl, e, hr, hb, hd, he, hs⟩ := h
  exact ⟨ho, hl, e, hr.grow hg, Nat.le_trans hb hg.iw, by rw [decHL_grow hg hb]; exact hd, he, hs⟩

def decStmt (m : Mem) (r : List Word) (st : List EIdx × EIdx) : Prop := StmtAt m (r.headD 0) st

/-- **`cert_guard` is its model `certGuardW`** (generated). -/
l_model certGuard_specW (p : Prog) (hp : p.lookup "cert_guard" = some certGuardL)
  fns [hp ↦ certGuardW list]
  specs [callW_spec p n "eq_at1", callW_spec p n "nat_ap2"]
  grind [arena_grind] heartbeats 1600000 bind ntBW

theorem certGuard_ref (hD : DmProg2 p) (cx a b rv : Word) (cc : CertCtxA) :
    CallRef p "cert_guard" [cx, a, b, rv] (fun m s => StageR vis fe m s ∧ CertCtxR m cx cc ∧ H a ∧ H b ∧ H rv)
      (certGuard cc (decE a) (decE b) (decE rv)) (KeepPost vis fe decW0E) := by
  sorry

/-- **`cert_eq` is its model `certEqW`** (generated). -/
l_model certEq_specW (p : Prog) (hp : p.lookup "cert_eq" = some certEqL)
  fns [hp ↦ certEqW list]
  specs [callW_spec p n "eq_at1", callW_spec p n "nat_ap2"]
  grind [arena_grind] heartbeats 1600000 bind ntBW

theorem certEq_ref (hD : DmProg2 p) (cx c rhs : Word) (cc : CertCtxA) :
    CallRef p "cert_eq" [cx, c, rhs] (fun m s => StageR vis fe m s ∧ CertCtxR m cx cc ∧ H c ∧ H rhs)
      (certEq cc (decI c) (decE rhs)) (KeepPost vis fe decW0E) := by
  sorry

/-- **`cert_halves` is its model `certHalvesW`** (generated). -/
l_model certHalves_specW (p : Prog) (hp : p.lookup "cert_halves" = some certHalvesL)
  fns [hp ↦ certHalvesW list]
  specs [callW_spec p n "nat_ap2"]
  grind [arena_grind] heartbeats 1600000 bind ntBW

theorem certHalves_ref (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    CallRef p "cert_halves" [cx, c] (fun m s => StageR vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (certHalves cc (decI c)) (KeepPost vis fe decW0E) := by
  sorry

theorem rec2_dec {κ : IdxKind} {m m1 : Mem} {r : List Word} {a b : Word} (hR : RecPost m m1 r [a, b])
    (ha : H a) (hb : H b) :
    decHL m1 (r.headD 0).toNat 2 = some [(decI a : Idx κ), decI b] := by
  obtain ⟨hq, -, -, -, hget⟩ := hR
  have hq' : (r.headD 0).toNat = iwTop m := by rw [hq]; rfl
  rw [hq']
  have := decHL_words (k := κ) m1 [a, b] (iwTop m)
    (by intro w hw; simp at hw; rcases hw with rfl | rfl <;> assumption)
    (fun j hj => by simpa [iwA] using hget j hj)
  simpa using this

/-- A statement record from `rec3(o, l, e)`, given the hypothesis slice. -/
theorem stmtAt_of_rec3 {m m1 : Mem} {r : List Word} {o l e : Word} {hyps : List EIdx}
    (hR : RecPost m m1 r [o, l, e]) (hI : IWOK m) (hb : o.toNat + l.toNat ≤ iwTop m)
    (hd : decHL m o.toNat l.toNat = some hyps) (he : H e) :
    StmtAt m1 (r.headD 0) (hyps, decE e) := by
  have hg := hR.2.1.1
  exact ⟨o, l, e, rec3At_of_post hR hI, Nat.le_trans hb hg.iw, by rw [decHL_grow hg hb]; exact hd, he, rfl⟩

theorem stmtL_of_rec2 {m m1 : Mem} {r : List Word} {s1 s2 : Word} {st1 st2 : List EIdx × EIdx}
    (hR : RecPost m m1 r [s1, s2]) (h1 : StmtAt m s1 st1) (h2 : StmtAt m s2 st2) :
    decStmtL m1 [r.headD 0, 2] [st1, st2] := by
  obtain ⟨hq, hK, hroom, htop, hget⟩ := hR
  have hq' : (r.headD 0).toNat = iwTop m := by rw [hq]; rfl
  have hg := hK.1
  simp only [decStmtL, StmtL, List.getD_cons_zero, List.getD_cons_succ, hq']
  have hl : [s1, s2].length = 2 := rfl
  have h2w : (2 : Word).toNat = 2 := rfl
  refine ⟨by rw [hl] at htop; omega, rfl, fun j hj => ?_⟩
  match j, hj with
  | 0, _ =>
    refine ⟨s1, ?_, h1.grow hg⟩
    have := hget 0 (by simp); simp only [iwA]; simpa using this
  | 1, _ =>
    refine ⟨s2, ?_, h2.grow hg⟩
    have := hget 1 (by simp); simp only [iwA]; simpa using this

theorem stmtL_of_rec3 {m m1 : Mem} {r : List Word} {s1 s2 s3 : Word} {st1 st2 st3 : List EIdx × EIdx}
    (hR : RecPost m m1 r [s1, s2, s3]) (h1 : StmtAt m s1 st1) (h2 : StmtAt m s2 st2)
    (h3 : StmtAt m s3 st3) : decStmtL m1 [r.headD 0, 3] [st1, st2, st3] := by
  obtain ⟨hq, hK, hroom, htop, hget⟩ := hR
  have hq' : (r.headD 0).toNat = iwTop m := by rw [hq]; rfl
  have hg := hK.1
  simp only [decStmtL, StmtL, List.getD_cons_zero, List.getD_cons_succ, hq']
  have hl : [s1, s2, s3].length = 3 := rfl
  have h3w : (3 : Word).toNat = 3 := rfl
  refine ⟨by rw [hl] at htop; omega, rfl, fun j hj => ?_⟩
  match j, hj with
  | 0, _ =>
    refine ⟨s1, ?_, h1.grow hg⟩
    have := hget 0 (by simp); simp only [iwA]; simpa using this
  | 1, _ =>
    refine ⟨s2, ?_, h2.grow hg⟩
    have := hget 1 (by simp); simp only [iwA]; simpa using this
  | 2, _ =>
    refine ⟨s3, ?_, h3.grow hg⟩
    have := hget 2 (by simp); simp only [iwA]; simpa using this

theorem decStmtL_pair {m : Mem} {r : List Word} {ss : List (List EIdx × EIdx)} (h : decStmtL m r ss) :
    decStmtL m [r.headD 0, r.tail.headD 0] ss := by
  unfold decStmtL at *
  rw [ntGetD0, ntGetD1] at h
  exact h

/-! ## `stmt1` -/

/-- **`stmt1` is its model `stmt1W`** (generated). -/
l_model stmt1_specW (p : Prog) (hp : p.lookup "stmt1" = some stmt1)
  fns [hp ↦ stmt1W list]
  specs [callW_spec p n "sl_new1", callW_spec p n "rec3"]
  grind [arena_grind] heartbeats 1600000 bind ntBW

theorem stmt1_ref (hD : DmProg2 p) (h e : Word) :
    CallRef p "stmt1" [h, e] (fun m s => StageR vis fe m s ∧ H h ∧ H e)
      (pure ([decE h], decE e) : AM (List EIdx × EIdx)) (KeepPost vis fe decStmt) := by
  sorry

/-! ## `cert_two_eqs` -/

/-- **`cert_two_eqs` is its model `certTwoEqsW`** (generated). -/
l_model certTwoEqs_specW (p : Prog) (hp : p.lookup "cert_two_eqs" = some certTwoEqsL)
  fns [hp ↦ certTwoEqsW list]
  specs [callW_spec p n "cert_eq", callW_spec p n "stmt1", callW_spec p n "rec2"]
  grind [arena_grind] heartbeats 1600000 bind ntBW

theorem certTwoEqs_ref (hD : DmProg2 p) (cx c h1 h2 r1 r2 : Word) (cc : CertCtxA) :
    CallRef p "cert_two_eqs" [cx, c, h1, h2, r1, r2]
      (fun m s => StageR vis fe m s ∧ CertCtxR m cx cc ∧ H c ∧ H h1 ∧ H h2 ∧ H r1 ∧ H r2)
      (certTwoEqs cc (decI c) (decE h1) (decE h2) (decE r1) (decE r2))
      (KeepPost vis fe decStmtL) := by
  sorry

/-- `cert_guard` at decoded arguments, the context grown from `m0`. -/
theorem certGuard_dw (hD : DmProg2 p) {n : Nat} {m m0 : Mem} {s : AState} {cx a b rv : Word}
    {cc : CertCtxA} {a' b' rv' : EIdx} (hS : StageR vis fe m s) (hC : CertCtxR m0 cx cc)
    (hG : IWGrow m0 m) (ha : DW a a') (hb : DW b b') (hr : DW rv rv') :
    Sim (callW p n "cert_guard" [cx, a, b, rv] m) (certGuard cc a' b' rv') s (KG dn vis fe m0 decW0E) := by
  obtain ⟨ha, rfl⟩ := ha; obtain ⟨hb, rfl⟩ := hb; obtain ⟨hr, rfl⟩ := hr
  exact (certGuard_ref hD cx a b rv cc).simG ⟨hS, hC.grow hG, ha, hb, hr⟩ hG

/-- `cert_two_eqs` at decoded arguments, the context grown from `m0`. -/
theorem certTwoEqs_dw (hD : DmProg2 p) {n : Nat} {m m0 : Mem} {s : AState} {cx c h1 h2 r1 r2 : Word}
    {cc : CertCtxA} {h1' h2' r1' r2' : EIdx} (hS : StageR vis fe m s) (hC : CertCtxR m0 cx cc)
    (hG : IWGrow m0 m) (hc : H c) (d1 : DW h1 h1') (d2 : DW h2 h2') (d3 : DW r1 r1') (d4 : DW r2 r2') :
    Sim (callW p n "cert_two_eqs" [cx, c, h1, h2, r1, r2] m) (certTwoEqs cc (decI c) h1' h2' r1' r2') s
      (KG dn vis fe m0 decStmtL) := by
  obtain ⟨d1, rfl⟩ := d1; obtain ⟨d2, rfl⟩ := d2; obtain ⟨d3, rfl⟩ := d3; obtain ⟨d4, rfl⟩ := d4
  exact (certTwoEqs_ref hD cx c h1 h2 r1 r2 cc).simG ⟨hS, hC.grow hG, hc, d1, d2, d3, d4⟩ hG

end nat

end L.Ind

end

section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

section nat
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

/-- The model's `if c = w` against the twin's `if decI c == N`, `w` the word of `N`. -/
theorem Sim.iteW {β α : Type} {N : NIdx} {c w : Word} {e1 e2 : Option (β × Mem)} {o1 o2 : AM α}
    {a : AState} {R : β → α → Mem → AState → Prop} (hw : w = N.word.toUInt64) (hc : H c)
    (h1 : c = w → Sim e1 o1 a R) (h2 : c ≠ w → Sim e2 o2 a R) :
    Sim (if c = w then e1 else e2) (if decI c == N then o1 else o2) a R := by
  subst hw
  have hb := decI_beq (k := IdxKind.name) _ _ hc (dmWord_lt32 N)
  rw [decI_word] at hb
  by_cases hd : c = N.word.toUInt64
  · rw [ite_eq_left hd, hb, decide_eq_true hd, ite_eq_left rfl]; exact h1 hd
  · rw [ite_eq_right hd, hb, decide_eq_false hd]; exact h2 hd

/-- A last callee returning a statement list `(o, l)`. -/
theorem CallRef.simPair {f : FnName} {args : List Word} {pre : Mem → AState → Prop}
    {op : AM (List (List EIdx × EIdx))} (h : CallRef p f args pre op (KeepPost vis fe decStmtL)) {n : Nat}
    {m m0 : Mem} {a : AState} (hp : pre m a) (hG : IWGrow m0 m) :
    Sim (ntBW (callW p n f args m) fun r m' => some ([r.headD 0, r.tail.headD 0], m')) op a
      (fun r x m' a' => KeepPost vis fe decStmtL m0 m' a' r x) := by
  sorry

/-- **`cert_lor_rhs` is its model `certLorRhsW`** (generated). -/
l_model certLorRhs_specW (p : Prog) (hp : p.lookup "cert_lor_rhs" = some certLorRhsL)
  fns [hp ↦ certLorRhsW list]
  specs [callW_spec p n "cert_halves", callW_spec p n "nat_ap2"]
  grind [arena_grind] finish [ntBW, rdW_eq] gen 30 heartbeats 1600000 bind ntBW instances 10000

theorem certLorRhs_ref (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    CallRef p "cert_lor_rhs" [cx, c] (fun m s => StageR vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (certLorRhs cc (decI c)) (KeepPost vis fe decW0E) := by
  sorry

/-- **`cert_xor_rhs` is its model `certXorRhsW`** (generated). -/
l_model certXorRhs_specW (p : Prog) (hp : p.lookup "cert_xor_rhs" = some certXorRhsL)
  fns [hp ↦ certXorRhsW list]
  specs [callW_spec p n "cert_halves", callW_spec p n "nat_ap2"]
  grind [arena_grind] finish [ntBW, rdW_eq] gen 30 heartbeats 1600000 bind ntBW instances 10000

theorem certXorRhs_ref (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    CallRef p "cert_xor_rhs" [cx, c] (fun m s => StageR vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (certXorRhs cc (decI c)) (KeepPost vis fe decW0E) := by
  sorry

/-- **`cert_gcd` is its model `certGcdW`** (generated). -/
l_model certGcd_specW (p : Prog) (hp : p.lookup "cert_gcd" = some certGcdL)
  fns [hp ↦ certGcdW list]
  specs [callW_spec p n "cert_guard", callW_spec p n "cert_two_eqs", callW_spec p n "nat_ap2"]
  grind [arena_grind] finish [ntBW, rdW_eq] gen 30 heartbeats 1600000 bind ntBW instances 10000

theorem certGcd_ref (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    CallRef p "cert_gcd" [cx, c] (fun m s => StageR vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (certGcd cc (decI c)) (KeepPost vis fe decStmtL) := by
  sorry

/-- **`cert_shift_left` is its model `certShiftLeftW`** (generated). -/
l_model certShiftLeft_specW (p : Prog) (hp : p.lookup "cert_shift_left" = some certShiftLeftL)
  fns [hp ↦ certShiftLeftW list]
  specs [callW_spec p n "cert_guard", callW_spec p n "cert_two_eqs", callW_spec p n "nat_ap2"]
  grind [arena_grind] finish [ntBW, rdW_eq] gen 30 heartbeats 1600000 bind ntBW instances 10000

theorem certShiftLeft_ref (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    CallRef p "cert_shift_left" [cx, c] (fun m s => StageR vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (certShiftLeft cc (decI c)) (KeepPost vis fe decStmtL) := by
  sorry

/-- **`cert_shift_right` is its model `certShiftRightW`** (generated). -/
l_model certShiftRight_specW (p : Prog) (hp : p.lookup "cert_shift_right" = some certShiftRightL)
  fns [hp ↦ certShiftRightW list]
  specs [callW_spec p n "cert_guard", callW_spec p n "cert_two_eqs", callW_spec p n "nat_ap2"]
  grind [arena_grind] finish [ntBW, rdW_eq] gen 30 heartbeats 1600000 bind ntBW instances 10000

theorem certShiftRight_ref (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    CallRef p "cert_shift_right" [cx, c] (fun m s => StageR vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (certShiftRight cc (decI c)) (KeepPost vis fe decStmtL) := by
  sorry

/-- **`cert_land` is its model `certLandW`** (generated). -/
l_model certLand_specW (p : Prog) (hp : p.lookup "cert_land" = some certLandL)
  fns [hp ↦ certLandW list]
  specs [callW_spec p n "cert_guard", callW_spec p n "cert_halves", callW_spec p n "cert_two_eqs", callW_spec p n "nat_ap2"]
  grind [arena_grind] finish [ntBW, rdW_eq] gen 30 heartbeats 1600000 bind ntBW instances 10000

theorem certLand_ref (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    CallRef p "cert_land" [cx, c] (fun m s => StageR vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (certLand cc (decI c)) (KeepPost vis fe decStmtL) := by
  sorry

/-- **`cert_lor` is its model `certLorW`** (generated). -/
l_model certLor_specW (p : Prog) (hp : p.lookup "cert_lor" = some certLorL)
  fns [hp ↦ certLorW list]
  specs [callW_spec p n "cert_guard", callW_spec p n "cert_lor_rhs", callW_spec p n "cert_two_eqs"]
  grind [arena_grind] finish [ntBW, rdW_eq] gen 30 heartbeats 1600000 bind ntBW instances 10000

theorem certLor_ref (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    CallRef p "cert_lor" [cx, c] (fun m s => StageR vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (certLor cc (decI c)) (KeepPost vis fe decStmtL) := by
  sorry

/-- **`cert_xor` is its model `certXorW`** (generated). -/
l_model certXor_specW (p : Prog) (hp : p.lookup "cert_xor" = some certXorL)
  fns [hp ↦ certXorW list]
  specs [callW_spec p n "cert_guard", callW_spec p n "cert_two_eqs", callW_spec p n "cert_xor_rhs"]
  grind [arena_grind] finish [ntBW, rdW_eq] gen 30 heartbeats 1600000 bind ntBW instances 10000

theorem certXor_ref (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    CallRef p "cert_xor" [cx, c] (fun m s => StageR vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (certXor cc (decI c)) (KeepPost vis fe decStmtL) := by
  sorry

/-! ## `cert_rec_rhs` -/

/-- **`cert_rec_rhs` is its model `certRecRhsW`** (generated). -/
l_model certRecRhs_specW (p : Prog) (hp : p.lookup "cert_rec_rhs" = some certRecRhsL)
  fns [hp ↦ certRecRhsW list]
  specs [callW_spec p n "nat_ap2", callW_spec p n "pin_at", callW_spec p n "nat_ap1"]
  grind [arena_grind] finish [ntBW, rdW_eq] gen 30 heartbeats 1600000 bind ntBW instances 10000

theorem certRecRhs_ref (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    CallRef p "cert_rec_rhs" [cx, c] (fun m s => StageR vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (certRecRhs cc (decI c)) (KeepPost vis fe decW0E) := by
  sorry

/-! ## `cert_div_mod_eqs` -/

/-- **`cert_div_mod_eqs` is its model `certDivModEqsW`** (generated). -/
l_model certDivModEqs_specW (p : Prog) (hp : p.lookup "cert_div_mod_eqs" = some certDivModEqsL)
  fns [hp ↦ certDivModEqsW list]
  specs [callW_spec p n "cert_eq", callW_spec p n "rec2", callW_spec p n "rec3", callW_spec p n "stmt1"]
  grind [arena_grind] finish [ntBW] gen 30 heartbeats 1600000 bind ntBW instances 10000

theorem certDivModEqs_ref (hD : DmProg2 p) (cx c h1 h2 h3 h4 recRhs baseRhs : Word) (cc : CertCtxA) :
    CallRef p "cert_div_mod_eqs" [cx, c, h1, h2, h3, h4, recRhs, baseRhs]
      (fun m s => StageR vis fe m s ∧ CertCtxR m cx cc ∧ H c ∧ H h1 ∧ H h2 ∧ H h3 ∧ H h4 ∧
        H recRhs ∧ H baseRhs)
      (certDivModEqs cc (decI c) (decE h1) (decE h2) (decE h3) (decE h4) (decE recRhs) (decE baseRhs))
      (KeepPost vis fe decStmtL) := by
  sorry

/-- **`cert_div_mod_guards` is its model `certDivModGuardsW`** (generated). -/
l_model certDivModGuards_specW (p : Prog) (hp : p.lookup "cert_div_mod_guards" = some certDivModGuardsL)
  fns [hp ↦ certDivModGuardsW list]
  specs [callW_spec p n "cert_div_mod_eqs", callW_spec p n "cert_guard"]
  grind [arena_grind] finish [ntBW, rdW_eq] gen 30 heartbeats 1600000 bind ntBW instances 10000

theorem certDivModGuards_ref (hD : DmProg2 p) (cx c recRhs baseRhs : Word) (cc : CertCtxA) :
    CallRef p "cert_div_mod_guards" [cx, c, recRhs, baseRhs] (fun m s => StageR vis fe m s ∧ CertCtxR m cx cc ∧ H c ∧ H recRhs ∧ H baseRhs)
      (certDivModGuards cc (decI c) (decE recRhs) (decE baseRhs)) (KeepPost vis fe decStmtL) := by
  sorry

/-! ## `cert_div_mod` -/

/-- **`cert_div_mod` is its model `certDivModW`** (generated). -/
l_model certDivMod_specW (p : Prog) (hp : p.lookup "cert_div_mod" = some certDivModL)
  fns [hp ↦ certDivModW list]
  specs [callW_spec p n "cert_rec_rhs", callW_spec p n "cert_div_mod_guards"]
  grind [arena_grind] finish [ntBW, rdW_eq] gen 30 heartbeats 1600000 bind ntBW instances 10000

theorem certDivMod_ref (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    CallRef p "cert_div_mod" [cx, c] (fun m s => StageR vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (certDivMod cc (decI c)) (KeepPost vis fe decStmtL) := by
  sorry

/-! ## `div_mod_cert_stmts_at` -/
/-- **`div_mod_cert_stmts_at` is its model `divModCertStmtsAtW`** (generated). -/
l_model divModCertStmtsAt_specW (p : Prog) (hp : p.lookup "div_mod_cert_stmts_at" = some divModCertStmtsAtL)
  fns [hp ↦ divModCertStmtsAtW list]
  specs [callW_spec p n "cert_gcd", callW_spec p n "cert_shift_left", callW_spec p n "cert_shift_right", callW_spec p n "cert_land", callW_spec p n "cert_lor", callW_spec p n "cert_xor", callW_spec p n "cert_div_mod"]
  grind [arena_grind] finish [ntBW, rdW_eq] gen 30 heartbeats 1600000 bind ntBW instances 10000

theorem divModCertStmtsAt_ref (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    CallRef p "div_mod_cert_stmts_at" [cx, c] (fun m s => StageR vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (divModCertStmtsAt cc (decI c)) (KeepPost vis fe decStmtL) := by
  refine CallRef.of_sim (M := fun k mq => divModCertStmtsAtW p (k + 1) mq cx c)
    (fun k s₀ => divModCertStmtsAt_specW p hD.lDivModCertStmtsAt (k + 1) s₀ cx c) fun k m s ⟨hS, hC, hc⟩ => ?_
  rw [divModCertStmtsAtW.eq_2]; unfold divModCertStmtsAt
  refine Sim.iteW hC.f15 hc (fun _ => (certGcd_ref hD cx c cc).simPair ⟨hS, hC, hc⟩ (.refl m)) fun _ => ?_
  refine Sim.iteW hC.f16 hc (fun _ => (certShiftLeft_ref hD cx c cc).simPair ⟨hS, hC, hc⟩ (.refl m)) fun _ => ?_
  refine Sim.iteW hC.f17 hc (fun _ => (certShiftRight_ref hD cx c cc).simPair ⟨hS, hC, hc⟩ (.refl m)) fun _ => ?_
  refine Sim.iteW hC.f18 hc (fun _ => (certLand_ref hD cx c cc).simPair ⟨hS, hC, hc⟩ (.refl m)) fun _ => ?_
  refine Sim.iteW hC.f19 hc (fun _ => (certLor_ref hD cx c cc).simPair ⟨hS, hC, hc⟩ (.refl m)) fun _ => ?_
  refine Sim.iteW hC.f20 hc (fun _ => (certXor_ref hD cx c cc).simPair ⟨hS, hC, hc⟩ (.refl m)) fun _ => ?_
  exact (certDivMod_ref hD cx c cc).simPair ⟨hS, hC, hc⟩ (.refl m)

end nat

end L.Ind

end
