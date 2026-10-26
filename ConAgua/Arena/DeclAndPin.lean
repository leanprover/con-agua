import ConAgua.Arena.DeclBase
import ConAgua.Arena.Pins
import ConAgua.Arena.Rom
import ConAgua.Census.Attr
import ConAgua.Arena.WhnfBase

/-!
# The fold's `And` pin: `and_pin_ok(i)` refines `andPinOk` (con-leche's ANDPIN)

The twin's `andPinOk` (`vendor/con-ron/ConRon/Arena/Basis.lean`) rejects a record that declares
`And`, `And.intro` or `And.rec` unless it is the pinned `And` block. For every record kind the
front produces (`DeclAt`: axiom, definition, theorem, opaque, quotient), that is
`andPinNameFree cv.name`: the name is not one of the three pinned handles (`PINS[12]`,
`PINS[49]`, `PINS[50]`, slots `PIN_AND`, `PIN_AND_INTRO`, `PIN_AND_REC`). An inductive block's
arm (`canonEqList` against the interned `andPin`) waits for the front's inductive records: no
`DeclAt` holds of `indDecl`/`basisDecl` yet, so under `LoopR` record `i` is never one.

`and_pin_ok(i)`: the flag, then the name word of record `i` (`DECL[2 + 8 i]`, `dw D i 1`) cut to
its low 32 bits (`decI` reads only those, so no bound on the record's word is needed), compared
with the three pin words. Returns `1` (free) or `0`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Front (DECL DLP DeclsF DeclAt CVAt dw)

/-- `and_block_named(bo, bl)`: some member of the inductive block at `DLP[bo ‥ bo + bl)` (record
pointers into `DLP` (`DIND`), a record's name at `+ 1`) declares one of the three pinned `And` names. -/
-- con-ron: ConRon/Arena/Basis.lean:109-114 ConRon.Arena.blockAndNamed
@[l_impl ConRon.Arena.blockAndNamed]
def andBlockNamed : FunDecl := lfn (bo, bl) locals (s, x, r) {
  if bl == 0 { return 0 };
  s := DLP.u64[bo];
  x := DLP.u64[s + 1] & 4294967295;
  if x == PINS.u64[12] || x == PINS.u64[49] || x == PINS.u64[50] { return 1 };
  r := call and_block_named(bo + 1, bl - 1);
  return r
}

/-- `and_pin_ok(i)`: `1` if record `i` may stand: a one-constant record whose name is none of the
three pinned `And` names, or an inductive block that declares none of them, or one that does and
is the pinned `And` block (two parameters, equal to the ROM's `andPin` up to the canonical form:
the block copied into `EREC` and an `IW` slice, `canon_eq_list`). -/
-- con-ron: ConRon/Arena/Basis.lean:123-143 ConRon.Arena.andPinOk
@[l_impl ConRon.Arena.andPinOk]
def andPinOkL : FunDecl := lfn (i) locals (x, k, bo, bl, nmd, np, o, l, io, il, po, pl, e) {
  if PINS.u64[0] == 0 { abort R_PIN_DATA };
  k := DECL.u64[1 + 8 * i];
  if k == 6 {
    bo := DECL.u64[3 + 8 * i];
    bl := DECL.u64[4 + 8 * i];
    nmd := call and_block_named(bo, bl);
    if nmd == 0 { return 1 };
    np := DECL.u64[5 + 8 * i];
    if np != 2 { return 0 };
    (o, l) := call ind_block_to_erec(i);
    (io, il) := call er_to_iw(o, l);
    (po, pl) := call rom_and_pin();
    e := call canon_eq_list(io, il, po, pl);
    return e
  };
  x := DECL.u64[2 + 8 * i] & 4294967295;
  if x == PINS.u64[12] || x == PINS.u64[49] || x == PINS.u64[50] { return 0 };
  return 1
}

/-- The low 32 bits of a word: what `decI` reads. -/
def lo32 (w : Word) : Word := w &&& 4294967295

/-- **The model of `and_pin_ok`**. -/
def andPinW (m : Mem) (i : Word) : Word :=
  if lo32 (rdW (m.arr64 DECL) (2 + 8 * i)) = rdW (m.arr64 PINS) 12 ∨
    lo32 (rdW (m.arr64 DECL) (2 + 8 * i)) = rdW (m.arr64 PINS) 49 ∨
    lo32 (rdW (m.arr64 DECL) (2 + 8 * i)) = rdW (m.arr64 PINS) 50 then 0 else 1

theorem andPinOk_specW (p : Prog) (hp : p.lookup "and_pin_ok" = some andPinOkL) (n : Nat) (s₀ : St)
    (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "and_pin_ok" [i]
    ⦃fun r s' => LocEq s' s₀ ∧ (rdW (s₀.mem.arr64 DECL) (1 + 8 * i) ≠ 6 →
      s'.mem = s₀.mem ∧ rdW (s₀.mem.arr64 PINS) 0 ≠ 0 ∧ r = [andPinW s₀.mem i]); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, andPinOkL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, callW_spec p n "and_block_named",
        callW_spec p n "ind_block_to_erec", callW_spec p n "er_to_iw", callW_spec p n "rom_and_pin",
        callW_spec p n "canon_eq_list"] <;>
      finish [andPinW, lo32, rdW_eq]

/-! ## The twin side -/

theorem decI_lo32 {k : IdxKind} (w : Word) : (decI (lo32 w) : Idx k) = decI w := by
  simp only [decI, lo32]
  congr 1
  apply UInt32.toNat_inj.mp
  simp only [UInt64.toNat_toUInt32, UInt64.toNat_and]
  rw [show (UInt64.toNat 4294967295) = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp

theorem decI_iff {k : IdxKind} (x y : Word) (hx : x.toNat < 2 ^ 32) (hy : y.toNat < 2 ^ 32) :
    (decI x : Idx k) = decI y ↔ x = y := by
  constructor
  · intro h
    simp only [decI] at h
    have h' := congrArg (fun z : Idx k => z.word) h
    simp only at h'
    have := congrArg UInt32.toNat h'
    simp [UInt64.toNat_toUInt32] at this
    apply UInt64.toNat_inj.mp
    omega
  · rintro rfl; rfl

theorem lo32_lt (w : Word) : (lo32 w).toNat < 2 ^ 32 := by
  simp only [lo32, UInt64.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

/-- The twin's `andPinNameFree`, at a filled pin table. -/
theorem andPinNameFree_run {m : Mem} {a : AState} (hF : PinsFull m a.pins) (w : Word) :
    (andPinNameFree (decI w)).run a =
      .ok (!(lo32 w = pinW m 12 ∨ lo32 w = pinW m 49 ∨ lo32 w = pinW m 50), a) := by
  have e1 := pinAt_run hF 11 (by decide)
  have e2 := pinAt_run hF 48 (by decide)
  have e3 := pinAt_run hF 49 (by decide)
  have l1 := hF.names_lt 11 (by decide)
  have l2 := hF.names_lt 48 (by decide)
  have l3 := hF.names_lt 49 (by decide)
  simp only [show 1 + 11 = 12 from rfl, show 1 + 48 = 49 from rfl, show 1 + 49 = 50 from rfl] at e1 e2 e3 l1 l2 l3
  have hl := lo32_lt w
  rw [← decI_lo32 w]
  have e : (andPinNameFree (decI (lo32 w))).run a =
      .ok (!([(decI (pinW m 12) : NIdx), decI (pinW m 49), decI (pinW m 50)].contains (decI (lo32 w))), a) := by
    simp only [andPinNameFree, andPinNameHs, pinAnd, pinAndIntro, pinAndRec, PIN_AND, PIN_AND_INTRO,
      PIN_AND_REC, StateT.run_bind, e1]
    simp only [bind, Except.bind]
    rw [e2]; simp only
    rw [e3]; rfl
  rw [e]
  congr
  have k1 := decI_iff (k := .name) _ _ hl l1
  have k2 := decI_iff (k := .name) _ _ hl l2
  have k3 := decI_iff (k := .name) _ _ hl l3
  by_cases h1 : lo32 w = pinW m 12 <;> by_cases h2 : lo32 w = pinW m 49 <;>
    by_cases h3 : lo32 w = pinW m 50 <;> simp_all [eq_comm]

/-- `andPinOk` on a record the front produces is the name test. -/
theorem andPinOk_run {D P : Array Word} {i : Nat} {d : IDeclaration} (hd : DeclAt D P i d)
    {m : Mem} {a : AState} (hF : PinsFull m a.pins) :
    (andPinOk d).run a =
      .ok (!(lo32 (dw D i 1) = pinW m 12 ∨ lo32 (dw D i 1) = pinW m 49 ∨ lo32 (dw D i 1) = pinW m 50), a) := by
  cases d with
  | axiomDecl cv => simp only [andPinOk]; rw [← hd.2.1]; exact andPinNameFree_run hF _
  | defnDecl cv v h => simp only [andPinOk]; rw [← hd.2.1.1]; exact andPinNameFree_run hF _
  | thmDecl cv v => simp only [andPinOk]; rw [← hd.2.1.1]; exact andPinNameFree_run hF _
  | opaqueDecl cv v => simp only [andPinOk]; rw [← hd.2.1.1]; exact andPinNameFree_run hF _
  | quotDecl k cv => simp only [andPinOk]; rw [← hd.2.1.1]; exact andPinNameFree_run hF _
  | indDecl b nP | basisDecl k => exact hd.elim

/-- **`and_pin_ok` refines `andPinOk`** on record `i` of the loop's declarations. -/
@[refines_part ConRon.Arena.andPinOk "one-constant records (the front's record kinds)"]
theorem andPinOk_refines {pins : List INatOpPinSet} (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration) (p : Prog)
    (hp : p.lookup "and_pin_ok" = some andPinOkL) :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (vis : Word) (fe : IFEnv) (pend : Array PendingCheck)
      (i : Word) (_hi : i.toNat < ds.size), (∀ b k, dsAt ds i ≠ .indDecl b k) →
      LoopR pins dn s₀.mem a₀ vis fe pend ds →
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "and_pin_ok" [i]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (andPinOk (dsAt ds i)) a₀ ∧
      LoopR pins dn s'.mem (AM.st (andPinOk (dsAt ds i)) a₀) vis fe pend ds ∧
      AM.res (andPinOk (dsAt ds i)) a₀ = (r.headD 0 != 0); ⊤⦄ := by
  intro n s₀ a₀ vis fe pend i _hi hone hR
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hk⟩ := M.of_run (P := fun s => s = s₀) hs hrun (andPinOk_specW p hp n s₀ i)
  subst hs
  have hdecl : DeclAt (s.mem.arr64 DECL) (s.mem.arr64 DLP) i.toNat (dsAt ds i) := by
    have := hR.decls.recs i.toNat _hi
    exact declAt_of_F (by simpa [dsAt, Array.getD, _hi] using this) hone
  have hk6 : rdW (s.mem.arr64 DECL) (1 + 8 * i) ≠ 6 := by
    have h1 := hR.decls.room
    have h2 := hR.decls.dsize
    have : rdW (s.mem.arr64 DECL) (1 + 8 * i) = dw (s.mem.arr64 DECL) i.toNat 0 := by
      have : (1 + 8 * i).toNat = 1 + 8 * i.toNat + 0 := by
        rw [UInt64.toNat_add, UInt64.toNat_mul]; simp; omega
      simp [rdW, dw, this]
    rw [this]
    generalize dsAt ds i = d at hdecl
    cases d <;> simp only [DeclAt] at hdecl <;> (try exact hdecl.elim) <;> rw [hdecl.1] <;> decide
  obtain ⟨hm, hflag, hr⟩ := hk hk6
  have hF := hR.check.pins.full (by have e0 : rdW (s.mem.arr64 PINS) 0 = pinW s.mem 0 := rfl; rw [← e0]; exact hflag)
  have hrun' := andPinOk_run hdecl hF
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun'
  have hw : rdW (s.mem.arr64 DECL) (2 + 8 * i) = dw (s.mem.arr64 DECL) i.toNat 1 := by
    have h1 := hR.decls.room
    have h2 := hR.decls.dsize
    have : (2 + 8 * i).toNat = 1 + 8 * i.toNat + 1 := by
      rw [UInt64.toNat_add, UInt64.toNat_mul]; simp; omega
    simp [rdW, dw, this]
  refine ⟨hloc, hok, by rw [hst, hm]; exact hR, ?_⟩
  rw [hres, hr]
  have e12 : rdW (s.mem.arr64 PINS) 12 = pinW s.mem 12 := rfl
  have e49 : rdW (s.mem.arr64 PINS) 49 = pinW s.mem 49 := rfl
  have e50 : rdW (s.mem.arr64 PINS) 50 = pinW s.mem 50 := rfl
  simp only [andPinW, hw, e12, e49, e50, List.headD_cons]
  generalize lo32 (dw (s.mem.arr64 DECL) i.toNat 1) = x
  by_cases h1 : x = pinW s.mem 12 <;> by_cases h2 : x = pinW s.mem 49 <;>
    by_cases h3 : x = pinW s.mem 50 <;> simp [h1, h2, h3]

end L.Arena
