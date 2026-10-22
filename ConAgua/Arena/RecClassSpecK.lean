import ConAgua.Arena.RecClassSpecJ

/-!
# `RecClass`: `ClassGen.minorTy` — models and specs (lane `indproofs2`, helper `rec2`)
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem loc_init12 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Word) (r : List Word) :
    Locals.init (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: r) 12 = x12 :=
  rfl

/-- `class_gen_ih_parts` at every fuel. -/
def rec2IhF (n : Nat) (m : Mem) (g t tele w d : Word) : Option (List Word × Mem) :=
  fuelW n (ihW m g t tele w d)

theorem rec2IhParts_specF (p : Prog) (hp : p.lookup "class_gen_ih_parts" = some classGenIhParts)
    (n : Nat) (s₀ : St) (g t tele w d : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_ih_parts" [g, t, tele, w, d]
    ⦃fun r s' => LocEq s' s₀ ∧ rec2IhF n s₀.mem g t tele w d = some (r, s'.mem); ⊤⦄ := by
  cases n with
  | zero => exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  | succ n => exact classGenIhParts_spec p hp n s₀ g t tele w d

/-! ## `class_gen_minor_ty_ih1_tail` -/

def iclK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r7, m7) => some ([1, r7.headD 0], m7)

def iclK1 (n : Nat) (e body : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r6, m6) =>
    if e + r6.tail.headD 0 < e then none else iclK2 (closeW n m6 (r6.headD 0) (r6.tail.headD 0) e body)

/-- **The model of `class_gen_minor_ty_ih1_close`.** -/
def iclW : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, xso, xsl, e, body => iclK1 n e body (stubM "fvar_type_ds" m [xso, xsl])

def itK5 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0, r.tail.headD 0], m)

def itK4b (n : Nat) (xso xsl e : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) => itK5 (iclW n m5 xso xsl e (r5.headD 0))

def itK4 (n : Nat) (xso xsl e mt : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => itK4b n xso xsl e (stubM "mk_app_n_f" m4 [mt, r4.headD 0, r4.tail.headD 0])

def itK3 (n : Nat) (xso xsl idxo idxl e fx : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => itK4 n xso xsl e (r3.headD 0) (snocW n m3 idxo idxl fx)

def itK2 (n : Nat) (g t xso xsl idxo idxl e : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => itK3 n xso xsl idxo idxl e (r2.headD 0) (rec2MotVarF n m2 g t)

def itK1 (n : Nat) (g t xso xsl idxo idxl e : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => itK2 n g t xso xsl idxo idxl e (stubM "mk_app_n_f" m1 [r1.headD 0, xso, xsl])

/-- **The model of `class_gen_minor_ty_ih1_tail`.** -/
def itW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, g, t, xso, xsl, idxo, idxl, fvso, fvsl, i, e =>
    itK1 n g t xso xsl idxo idxl e (fuelW n (exprGetDW m fvso fvsl i))

/-! ## `class_gen_minor_ty_ih1` -/

def i1K3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0, r.tail.headD 0], m)

def i1K2 (n : Nat) (g t fvso fvsl i e : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if r2.headD 0 = 0 then some ([0, 0], m2)
    else i1K3 (itW n m2 g t (r2.tail.headD 0) (r2.tail.tail.headD 0) (r2.tail.tail.tail.headD 0)
      (r2.tail.tail.tail.tail.headD 0) fvso fvsl i e)

def i1K1 (n : Nat) (g t tele fvso fvsl i e : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => i1K2 n g t fvso fvsl i e (rec2IhF n m1 g t tele (r1.headD 0) e)

/-- **The model of `class_gen_minor_ty_ih1`.** -/
def i1W : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, g, t, tele, wso, wsl, fvso, fvsl, i, e =>
    i1K1 n g t tele fvso fvsl i e (fuelW n (exprGetDW m wso wsl i))

/-! ## `class_gen_minor_ty_ihs_go` -/

def isK4 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => some ([1, r4.headD 0, r4.tail.headD 0], m4)

def isK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0], m)

def isK2 (n : Nat) (ih : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if r2.headD 0 = 0 then some ([0, 0, 0], m2)
    else isK4 (consW n m2 ih (r2.tail.headD 0) (r2.tail.tail.headD 0))

/-- The tag of field `i`'s kind (`0` past the kinds). -/
def isTag (m : Mem) (x i : Word) : Word :=
  if i < rdW (m.arr64 IW) (x + 3) then rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (x + 2) + i))
  else 0

/-- Field `i`'s kind record. -/
def isKp (m : Mem) (x i : Word) : Word := rdW (m.arr64 IW) (rdW (m.arr64 IW) (x + 2) + i)

mutual
/-- **The model of `class_gen_minor_ty_ihs_go`.** -/
def isW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, g, x, d, nF, wso, wsl, fvso, fvsl, i, l =>
    if nF ≤ i then some ([1, 0, 0], m)
    else if isTag m x i = 1 then
      if d + nF < d then none
      else if d + nF + l < d + nF then none
      else isK1 n g x d nF wso wsl fvso fvsl i l
        (i1W n m g (rdW (m.arr64 IW) (isKp m x i + 1)) (rdW (m.arr64 IW) (isKp m x i + 2)) wso wsl fvso fvsl
          i (d + nF + l))
    else isK3 (isW n m g x d nF wso wsl fvso fvsl (i + 1) l)
def isK1 (n : Nat) (g x d nF wso wsl fvso fvsl i l : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if r1.headD 0 = 0 then some ([0, 0, 0], m1)
    else isK2 n (r1.tail.headD 0) (isW n m1 g x d nF wso wsl fvso fvsl (i + 1) (l + 1))
end

/-! ## `class_gen_minor_ty_concl2`, `_concl`, `_body`, `class_gen_minor_ty` -/

def mcK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r6, m6) => some ([1, r6.headD 0], m6)

def mcK2 (n : Nat) (d body : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) =>
    if d + r5.tail.headD 0 < d then none else mcK3 (closeW n m5 (r5.headD 0) (r5.tail.headD 0) d body)

def mcK1 (n : Nat) (d ihso ihsl body : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => mcK2 n d body (appendW n m4 (r4.headD 0) (r4.tail.headD 0) ihso ihsl)

/-- **The model of `class_gen_minor_ty_close`.** -/
def mcW : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, m, fo, fl, ihso, ihsl, d, res => mcK1 n d ihso ihsl res (stubM "fvar_type_ds" m [fo, fl])

def c2K3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0, r.tail.headD 0], m)

def c2K2b (n : Nat) (d fo fl ihso ihsl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => c2K3 (mcW n m3 fo fl ihso ihsl d (r3.headD 0))

def c2K2 (n : Nat) (d fo fl ihso ihsl mc : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => c2K2b n d fo fl ihso ihsl (stubM "mk_app_n_f" m2 [mc, r2.headD 0, r2.tail.headD 0])

def c2K1 (n : Nat) (d nPc fo fl ihso ihsl rao ral capp : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    c2K2 n d fo fl ihso ihsl (r1.headD 0)
      (snocW n m1 (if nPc < ral then rao + nPc else rao) (if nPc < ral then ral - nPc else 0) capp)

/-- **The model of `class_gen_minor_ty_concl2`.** -/
def c2W : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, g, c, d, nPc, fo, fl, ihso, ihsl, rao, ral, capp =>
    c2K1 n d nPc fo fl ihso ihsl rao ral capp (rec2MotVarF n m g c)

def cK4 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0, r.tail.headD 0], m)

def cK3 (n : Nat) (g c d nPc fo fl ihso ihsl rao ral : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => cK4 (c2W n m3 g c d nPc fo fl ihso ihsl rao ral (r3.headD 0))

def cK2b (n : Nat) (g c d nPc fo fl ihso ihsl rao ral cc : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) =>
    cK3 n g c d nPc fo fl ihso ihsl rao ral (stubM "mk_app_n_f" m3 [cc, r3.headD 0, r3.tail.headD 0])

def cK2 (n : Nat) (g c d ds0 dl0 nPc fo fl ihso ihsl rao ral : Word) :
    Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (cc, m2) =>
    if 4294967296 ≤ cc then none
    else cK2b n g c d nPc fo fl ihso ihsl rao ral cc (appendW n m2 ds0 dl0 fo fl)

def cK1 (n : Nat) (g c x d lvls ds0 dl0 nPc fo fl ihso ihsl : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    cK2 n g c d ds0 dl0 nPc fo fl ihso ihsl (r1.headD 0) (r1.tail.headD 0)
      (ceinternW m1 (rdW (m1.arr64 EREC) (rdW (m1.arr64 IW) x)) lvls)

/-- **The model of `class_gen_minor_ty_concl`.** -/
def cW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, g, c, x, d, lvls, ds0, dl0, nPc, fo, fl, res, ihso, ihsl =>
    cK1 n g c x d lvls ds0 dl0 nPc fo fl ihso ihsl (stubM "get_app_args_f" m [CWF, res])

def bK3 (n : Nat) (g c x d lvls ds0 dl0 nPc fo fl res : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) =>
    if r3.headD 0 = 0 then some ([0, 0], m3)
    else cK4 (cW n m3 g c x d lvls ds0 dl0 nPc fo fl res (r3.tail.headD 0) (r3.tail.tail.headD 0))

def bK2 (n : Nat) (g c x d lvls ds0 dl0 nPc fo fl res : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if r2.headD 0 = 0 then some ([0, 0], m2)
    else bK3 n g c x d lvls ds0 dl0 nPc fo fl res
      (isW n m2 g x d (rdW (m2.arr64 IW) (x + 1)) (r2.tail.headD 0) (r2.tail.tail.headD 0) fo fl 0 0)

def bK1 (n : Nat) (g c x d lvls ds0 dl0 nPc : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if r1.headD 0 = 0 then some ([0, 0], m1)
    else bK2 n g c x d lvls ds0 dl0 nPc (r1.tail.headD 0) (r1.tail.tail.headD 0) (r1.tail.tail.tail.headD 0)
      (pdW n m1 (r1.tail.headD 0) (r1.tail.tail.headD 0) (rdW (m1.arr64 IW) (x + 5)))

/-- **The model of `class_gen_minor_ty_body`.** -/
def bW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, g, c, x, d, lvls, ds0, dl0, nPc =>
    bK1 n g c x d lvls ds0 dl0 nPc
      (stubM "open_pis_at_fvars_f" m [rdW (m.arr64 IW) (x + 1), rdW (m.arr64 IW) (x + 4), d])

def mnK1 (n : Nat) (g c x d : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    cK4 (bW n m1 g c x d (rdW (m1.arr64 IW) (r1.headD 0 + 1)) (rdW (m1.arr64 IW) (r1.headD 0 + 2))
      (rdW (m1.arr64 IW) (r1.headD 0 + 3)) (rdW (m1.arr64 IW) (r1.headD 0 + 4)))

/-- **The model of `class_gen_minor_ty`.** -/
def mnW : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, g, c, x, d =>
    mnK1 n g c x d (tmaW n m (rdW (m.arr64 IW) (g + 3)) (rdW (m.arr64 IW) (g + 4)) c)

/-! ## Arms -/

section arms
variable (n : Nat) (m m1 m2 m3 m4 m5 m6 m7 : Mem)
  (g t c x d e tele xso xsl idxo idxl fvso fvsl wso wsl i l nF fx mt body ih nPc fo fl ihso ihsl rao ral
    capp mc lvls ds0 dl0 res cc : Word) (r r1 r2 r3 r4 r5 r6 r7 : List Word)
theorem itW_eq : itW (n + 1) m g t xso xsl idxo idxl fvso fvsl i e =
    itK1 n g t xso xsl idxo idxl e (fuelW n (exprGetDW m fvso fvsl i)) := rfl
theorem itK1_some : itK1 n g t xso xsl idxo idxl e (some (r1, m1)) =
    itK2 n g t xso xsl idxo idxl e (stubM "mk_app_n_f" m1 [r1.headD 0, xso, xsl]) := rfl
theorem itK2_some : itK2 n g t xso xsl idxo idxl e (some (r2, m2)) =
    itK3 n xso xsl idxo idxl e (r2.headD 0) (rec2MotVarF n m2 g t) := rfl
theorem itK3_some : itK3 n xso xsl idxo idxl e fx (some (r3, m3)) =
    itK4 n xso xsl e (r3.headD 0) (snocW n m3 idxo idxl fx) := rfl
theorem itK4_some : itK4 n xso xsl e mt (some (r4, m4)) =
    itK4b n xso xsl e (stubM "mk_app_n_f" m4 [mt, r4.headD 0, r4.tail.headD 0]) := rfl
theorem itK4b_some : itK4b n xso xsl e (some (r5, m5)) = itK5 (iclW n m5 xso xsl e (r5.headD 0)) := rfl
theorem itK5_some : itK5 (some (r, m)) = some ([r.headD 0, r.tail.headD 0], m) := rfl
theorem iclW_eq : iclW (n + 1) m xso xsl e body = iclK1 n e body (stubM "fvar_type_ds" m [xso, xsl]) := rfl
theorem iclK1_big (h : e + r6.tail.headD 0 < e) : iclK1 n e body (some (r6, m6)) = none := by rw [iclK1, if_pos h]
theorem iclK1_ok (h : ¬ e + r6.tail.headD 0 < e) : iclK1 n e body (some (r6, m6)) =
    iclK2 (closeW n m6 (r6.headD 0) (r6.tail.headD 0) e body) := by rw [iclK1, if_neg h]
theorem iclK2_some : iclK2 (some (r7, m7)) = some ([1, r7.headD 0], m7) := rfl
theorem i1W_eq : i1W (n + 1) m g t tele wso wsl fvso fvsl i e =
    i1K1 n g t tele fvso fvsl i e (fuelW n (exprGetDW m wso wsl i)) := rfl
theorem i1K1_some : i1K1 n g t tele fvso fvsl i e (some (r1, m1)) =
    i1K2 n g t fvso fvsl i e (rec2IhF n m1 g t tele (r1.headD 0) e) := rfl
theorem i1K2_fail (h : r2.headD 0 = 0) : i1K2 n g t fvso fvsl i e (some (r2, m2)) = some ([0, 0], m2) := by
  rw [i1K2, if_pos h]
theorem i1K2_ok (h : r2.headD 0 ≠ 0) : i1K2 n g t fvso fvsl i e (some (r2, m2)) =
    i1K3 (itW n m2 g t (r2.tail.headD 0) (r2.tail.tail.headD 0) (r2.tail.tail.tail.headD 0)
      (r2.tail.tail.tail.tail.headD 0) fvso fvsl i e) := by
  rw [i1K2, if_neg h]
theorem i1K3_some : i1K3 (some (r, m)) = some ([r.headD 0, r.tail.headD 0], m) := rfl
theorem isW_end (h : nF ≤ i) : isW (n + 1) m g x d nF wso wsl fvso fvsl i l = some ([1, 0, 0], m) := by
  simp only [isW]; rw [if_pos h]
theorem isW_rec (h : ¬ nF ≤ i) (ht : isTag m x i = 1) (h1 : ¬ d + nF < d) (h2 : ¬ d + nF + l < d + nF) :
    isW (n + 1) m g x d nF wso wsl fvso fvsl i l = isK1 n g x d nF wso wsl fvso fvsl i l
      (i1W n m g (rdW (m.arr64 IW) (isKp m x i + 1)) (rdW (m.arr64 IW) (isKp m x i + 2)) wso wsl fvso fvsl
        i (d + nF + l)) := by
  simp only [isW]; rw [if_neg h, if_pos ht, if_neg h1, if_neg h2]
theorem isW_ov1 (h : ¬ nF ≤ i) (ht : isTag m x i = 1) (h1 : d + nF < d) :
    isW (n + 1) m g x d nF wso wsl fvso fvsl i l = none := by
  simp only [isW]; rw [if_neg h, if_pos ht, if_pos h1]
theorem isW_ov2 (h : ¬ nF ≤ i) (ht : isTag m x i = 1) (h1 : ¬ d + nF < d) (h2 : d + nF + l < d + nF) :
    isW (n + 1) m g x d nF wso wsl fvso fvsl i l = none := by
  simp only [isW]; rw [if_neg h, if_pos ht, if_neg h1, if_pos h2]
theorem isW_ord (h : ¬ nF ≤ i) (ht : ¬ isTag m x i = 1) :
    isW (n + 1) m g x d nF wso wsl fvso fvsl i l = isK3 (isW n m g x d nF wso wsl fvso fvsl (i + 1) l) := by
  simp only [isW]; rw [if_neg h, if_neg ht]
theorem isK1_fail (h : r1.headD 0 = 0) : isK1 n g x d nF wso wsl fvso fvsl i l (some (r1, m1)) =
    some ([0, 0, 0], m1) := by rw [isK1, if_pos h]
theorem isK1_ok (h : r1.headD 0 ≠ 0) : isK1 n g x d nF wso wsl fvso fvsl i l (some (r1, m1)) =
    isK2 n (r1.tail.headD 0) (isW n m1 g x d nF wso wsl fvso fvsl (i + 1) (l + 1)) := by rw [isK1, if_neg h]
theorem isK2_fail (h : r2.headD 0 = 0) : isK2 n ih (some (r2, m2)) = some ([0, 0, 0], m2) := by
  rw [isK2, if_pos h]
theorem isK2_ok (h : r2.headD 0 ≠ 0) : isK2 n ih (some (r2, m2)) =
    isK4 (consW n m2 ih (r2.tail.headD 0) (r2.tail.tail.headD 0)) := by rw [isK2, if_neg h]
theorem isK3_some : isK3 (some (r, m)) = some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0], m) := rfl
theorem isK4_some : isK4 (some (r4, m4)) = some ([1, r4.headD 0, r4.tail.headD 0], m4) := rfl
theorem c2W_eq : c2W (n + 1) m g c d nPc fo fl ihso ihsl rao ral capp =
    c2K1 n d nPc fo fl ihso ihsl rao ral capp (rec2MotVarF n m g c) := rfl
theorem c2K1_some : c2K1 n d nPc fo fl ihso ihsl rao ral capp (some (r1, m1)) =
    c2K2 n d fo fl ihso ihsl (r1.headD 0)
      (snocW n m1 (if nPc < ral then rao + nPc else rao) (if nPc < ral then ral - nPc else 0) capp) := rfl
theorem c2K2_some : c2K2 n d fo fl ihso ihsl mc (some (r2, m2)) =
    c2K2b n d fo fl ihso ihsl (stubM "mk_app_n_f" m2 [mc, r2.headD 0, r2.tail.headD 0]) := rfl
theorem c2K2b_some : c2K2b n d fo fl ihso ihsl (some (r3, m3)) = c2K3 (mcW n m3 fo fl ihso ihsl d (r3.headD 0)) := rfl
theorem c2K3_some : c2K3 (some (r, m)) = some ([r.headD 0, r.tail.headD 0], m) := rfl
theorem mcW_eq : mcW (n + 1) m fo fl ihso ihsl d res = mcK1 n d ihso ihsl res (stubM "fvar_type_ds" m [fo, fl]) := rfl
theorem mcK1_some : mcK1 n d ihso ihsl body (some (r4, m4)) =
    mcK2 n d body (appendW n m4 (r4.headD 0) (r4.tail.headD 0) ihso ihsl) := rfl
theorem mcK2_big (h : d + r5.tail.headD 0 < d) : mcK2 n d body (some (r5, m5)) = none := by rw [mcK2, if_pos h]
theorem mcK2_ok (h : ¬ d + r5.tail.headD 0 < d) : mcK2 n d body (some (r5, m5)) =
    mcK3 (closeW n m5 (r5.headD 0) (r5.tail.headD 0) d body) := by rw [mcK2, if_neg h]
theorem mcK3_some : mcK3 (some (r6, m6)) = some ([1, r6.headD 0], m6) := rfl
theorem cW_eq : cW (n + 1) m g c x d lvls ds0 dl0 nPc fo fl res ihso ihsl =
    cK1 n g c x d lvls ds0 dl0 nPc fo fl ihso ihsl (stubM "get_app_args_f" m [CWF, res]) := rfl
theorem cK1_some : cK1 n g c x d lvls ds0 dl0 nPc fo fl ihso ihsl (some (r1, m1)) =
    cK2 n g c d ds0 dl0 nPc fo fl ihso ihsl (r1.headD 0) (r1.tail.headD 0)
      (ceinternW m1 (rdW (m1.arr64 EREC) (rdW (m1.arr64 IW) x)) lvls) := rfl
theorem cK2_big (h : 4294967296 ≤ cc) : cK2 n g c d ds0 dl0 nPc fo fl ihso ihsl rao ral (some (cc, m2)) = none := by
  rw [cK2, if_pos h]
theorem cK2_ok (h : ¬ 4294967296 ≤ cc) : cK2 n g c d ds0 dl0 nPc fo fl ihso ihsl rao ral (some (cc, m2)) =
    cK2b n g c d nPc fo fl ihso ihsl rao ral cc (appendW n m2 ds0 dl0 fo fl) := by
  rw [cK2, if_neg h]
theorem cK2b_some : cK2b n g c d nPc fo fl ihso ihsl rao ral cc (some (r3, m3)) =
    cK3 n g c d nPc fo fl ihso ihsl rao ral (stubM "mk_app_n_f" m3 [cc, r3.headD 0, r3.tail.headD 0]) := rfl
theorem cK3_some : cK3 n g c d nPc fo fl ihso ihsl rao ral (some (r3, m3)) =
    cK4 (c2W n m3 g c d nPc fo fl ihso ihsl rao ral (r3.headD 0)) := rfl
theorem cK4_some : cK4 (some (r, m)) = some ([r.headD 0, r.tail.headD 0], m) := rfl
theorem bW_eq : bW (n + 1) m g c x d lvls ds0 dl0 nPc = bK1 n g c x d lvls ds0 dl0 nPc
    (stubM "open_pis_at_fvars_f" m [rdW (m.arr64 IW) (x + 1), rdW (m.arr64 IW) (x + 4), d]) := rfl
theorem bK1_fail (h : r1.headD 0 = 0) : bK1 n g c x d lvls ds0 dl0 nPc (some (r1, m1)) = some ([0, 0], m1) := by
  rw [bK1, if_pos h]
theorem bK1_ok (h : r1.headD 0 ≠ 0) : bK1 n g c x d lvls ds0 dl0 nPc (some (r1, m1)) =
    bK2 n g c x d lvls ds0 dl0 nPc (r1.tail.headD 0) (r1.tail.tail.headD 0) (r1.tail.tail.tail.headD 0)
      (pdW n m1 (r1.tail.headD 0) (r1.tail.tail.headD 0) (rdW (m1.arr64 IW) (x + 5))) := by
  rw [bK1, if_neg h]
theorem bK2_fail (h : r2.headD 0 = 0) : bK2 n g c x d lvls ds0 dl0 nPc fo fl res (some (r2, m2)) =
    some ([0, 0], m2) := by rw [bK2, if_pos h]
theorem bK2_ok (h : r2.headD 0 ≠ 0) : bK2 n g c x d lvls ds0 dl0 nPc fo fl res (some (r2, m2)) =
    bK3 n g c x d lvls ds0 dl0 nPc fo fl res
      (isW n m2 g x d (rdW (m2.arr64 IW) (x + 1)) (r2.tail.headD 0) (r2.tail.tail.headD 0) fo fl 0 0) := by
  rw [bK2, if_neg h]
theorem bK3_fail (h : r3.headD 0 = 0) : bK3 n g c x d lvls ds0 dl0 nPc fo fl res (some (r3, m3)) =
    some ([0, 0], m3) := by rw [bK3, if_pos h]
theorem bK3_ok (h : r3.headD 0 ≠ 0) : bK3 n g c x d lvls ds0 dl0 nPc fo fl res (some (r3, m3)) =
    cK4 (cW n m3 g c x d lvls ds0 dl0 nPc fo fl res (r3.tail.headD 0) (r3.tail.tail.headD 0)) := by
  rw [bK3, if_neg h]
theorem mnW_eq : mnW (n + 1) m g c x d =
    mnK1 n g c x d (tmaW n m (rdW (m.arr64 IW) (g + 3)) (rdW (m.arr64 IW) (g + 4)) c) := rfl
theorem mnK1_some : mnK1 n g c x d (some (r1, m1)) =
    cK4 (bW n m1 g c x d (rdW (m1.arr64 IW) (r1.headD 0 + 1)) (rdW (m1.arr64 IW) (r1.headD 0 + 2))
      (rdW (m1.arr64 IW) (r1.headD 0 + 3)) (rdW (m1.arr64 IW) (r1.headD 0 + 4))) := rfl
end arms

attribute [ind_grind] itW_eq itK1_some itK2_some itK3_some itK4_some itK4b_some itK5_some iclW_eq iclK1_big iclK1_ok
  iclK2_some
  i1W_eq i1K1_some i1K2_fail i1K2_ok i1K3_some isW_end isW_rec isW_ov1 isW_ov2 isW_ord isK1_fail isK1_ok
  isK2_fail isK2_ok isK3_some isK4_some c2W_eq c2K1_some c2K2_some c2K2b_some c2K3_some mcW_eq mcK1_some mcK2_big mcK2_ok
  mcK3_some cW_eq cK1_some cK2_big cK2_ok cK2b_some cK3_some cK4_some bW_eq bK1_fail bK1_ok bK2_fail bK2_ok
  bK3_fail bK3_ok mnW_eq mnK1_some

/-! ## Specs -/

/-- The lookups `class_gen_minor_ty` needs. -/
structure MnProg (p : Prog) extends GtProg p : Prop where
  ihp : p.lookup "class_gen_ih_parts" = some classGenIhParts
  cons : p.lookup "sl_cons" = some slCons
  tpd : p.lookup "target_pi_doms_with" = some targetPiDomsWith
  it : p.lookup "class_gen_minor_ty_ih1_tail" = some classGenMinorTyIh1Tail
  icl : p.lookup "class_gen_minor_ty_ih1_close" = some classGenMinorTyIh1Close
  i1 : p.lookup "class_gen_minor_ty_ih1" = some classGenMinorTyIh1
  isg : p.lookup "class_gen_minor_ty_ihs_go" = some classGenMinorTyIhsGo
  c2 : p.lookup "class_gen_minor_ty_concl2" = some classGenMinorTyConcl2
  mcl : p.lookup "class_gen_minor_ty_close" = some classGenMinorTyClose
  cc : p.lookup "class_gen_minor_ty_concl" = some classGenMinorTyConcl
  bd : p.lookup "class_gen_minor_ty_body" = some classGenMinorTyBody
  mnci : p.lookup "class_gen_minor_ci" = some classGenMinorCi
  mn : p.lookup "class_gen_minor_ty" = some classGenMinorTy

section specs
variable (p : Prog) (h : MnProg p)
include h

theorem classGenMinorTyIh1Close_spec (n : Nat) (s₀ : St) (xso xsl e body : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_minor_ty_ih1_close" [xso, xsl, e, body]
    ⦃fun r s' => LocEq s' s₀ ∧ iclW n s₀.mem xso xsl e body = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.icl]
  simp only [callFn, classGenMinorTyIh1Close]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        stubM_spec p "fvar_type_ds" n, closeTelescope_spec p h.db h.ff h.fp h.ifa h.mkf h.ct n] <;>
      finish (gen := 20)

theorem classGenMinorTyIh1Tail_spec (n : Nat) (s₀ : St) (g t xso xsl idxo idxl fvso fvsl i e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_minor_ty_ih1_tail" [g, t, xso, xsl, idxo, idxl, fvso, fvsl, i, e]
    ⦃fun r s' => LocEq s' s₀ ∧ itW n s₀.mem g t xso xsl idxo idxl fvso fvsl i e = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.it]
  simp only [callFn, classGenMinorTyIh1Tail]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        rec2ExprGetD_specF p h.bf h.bp h.ib h.egd n, stubM_spec p "mk_app_n_f" n,
        rec2MotVar_specF p h.toMtProg h.fvf h.fvp h.ifv h.sv h.ms h.mv n,
        slSnoc_specW p h.alloc h.copy h.snoc n, classGenMinorTyIh1Close_spec p h n] <;>
      finish (gen := 20) [loc_init4, loc_init5, loc_init6, loc_init7, loc_init8, loc_init9]

theorem classGenMinorTyIh1_spec (n : Nat) (s₀ : St) (g t tele wso wsl fvso fvsl i e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_minor_ty_ih1" [g, t, tele, wso, wsl, fvso, fvsl, i, e]
    ⦃fun r s' => LocEq s' s₀ ∧ i1W n s₀.mem g t tele wso wsl fvso fvsl i e = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.i1]
  simp only [callFn, classGenMinorTyIh1]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        rec2ExprGetD_specF p h.bf h.bp h.ib h.egd n, rec2IhParts_specF p h.ihp n,
        classGenMinorTyIh1Tail_spec p h n] <;>
      finish (gen := 20) [loc_init4, loc_init5, loc_init6, loc_init7, loc_init8]

theorem classGenMinorTyIhsGo_spec (n : Nat) : ∀ (s₀ : St) (g x d nF wso wsl fvso fvsl i l : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_minor_ty_ihs_go" [g, x, d, nF, wso, wsl, fvso, fvsl, i, l]
    ⦃fun r s' => LocEq s' s₀ ∧ isW n s₀.mem g x d nF wso wsl fvso fvsl i l = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ g x d nF wso wsl fvso fvsl i l
    rw [invoke_eq _ h.isg]; simp only [callFn, classGenMinorTyIhsGo]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ g x d nF wso wsl fvso fvsl i l
    rw [invoke_eq _ h.isg]
    simp only [callFn, classGenMinorTyIhsGo]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        classGenMinorTyIh1_spec p h n, slCons_specW p h.alloc h.copy h.cons n, ih] <;>
      finish (gen := 20) [rdW_eq, isTag, isKp, loc_init4, loc_init5, loc_init6, loc_init7, loc_init8, loc_init9]

theorem classGenMinorTyClose_spec (n : Nat) (s₀ : St) (fo fl ihso ihsl d res : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_minor_ty_close" [fo, fl, ihso, ihsl, d, res]
    ⦃fun r s' => LocEq s' s₀ ∧ mcW n s₀.mem fo fl ihso ihsl d res = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.mcl]
  simp only [callFn, classGenMinorTyClose]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, stubM_spec p "fvar_type_ds" n,
        slAppend_specW p h.alloc h.copy h.app n, closeTelescope_spec p h.db h.ff h.fp h.ifa h.mkf h.ct n] <;>
      finish (gen := 20) [loc_init4, loc_init5]

theorem classGenMinorTyConcl2_spec (n : Nat) (s₀ : St) (g c d nPc fo fl ihso ihsl rao ral capp : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_minor_ty_concl2" [g, c, d, nPc, fo, fl, ihso, ihsl, rao, ral, capp]
    ⦃fun r s' => LocEq s' s₀ ∧ c2W n s₀.mem g c d nPc fo fl ihso ihsl rao ral capp = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.c2]
  simp only [callFn, classGenMinorTyConcl2]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        rec2MotVar_specF p h.toMtProg h.fvf h.fvp h.ifv h.sv h.ms h.mv n,
        slSnoc_specW p h.alloc h.copy h.snoc n, stubM_spec p "mk_app_n_f" n,
        classGenMinorTyClose_spec p h n] <;>
      finish (gen := 20) [loc_init4, loc_init5, loc_init6, loc_init7, loc_init8, loc_init9, loc_init10]

theorem classGenMinorTyConcl_spec (n : Nat) (s₀ : St) (g c x d lvls ds0 dl0 nPc fo fl res ihso ihsl : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_minor_ty_concl"
      [g, c, x, d, lvls, ds0, dl0, nPc, fo, fl, res, ihso, ihsl]
    ⦃fun r s' => LocEq s' s₀ ∧ cW n s₀.mem g c x d lvls ds0 dl0 nPc fo fl res ihso ihsl = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.cc]
  simp only [callFn, classGenMinorTyConcl]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        stubM_spec p "get_app_args_f" n, internConst_spec p h.cf h.cp h.ic n,
        slAppend_specW p h.alloc h.copy h.app n, stubM_spec p "mk_app_n_f" n,
        classGenMinorTyConcl2_spec p h n] <;>
      finish (gen := 80) [rdW_eq, loc_init4, loc_init5, loc_init6, loc_init7, loc_init8, loc_init9,
        loc_init10, loc_init11, loc_init12]

theorem classGenMinorTyBody_spec (n : Nat) (s₀ : St) (g c x d lvls ds0 dl0 nPc : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_minor_ty_body" [g, c, x, d, lvls, ds0, dl0, nPc]
    ⦃fun r s' => LocEq s' s₀ ∧ bW n s₀.mem g c x d lvls ds0 dl0 nPc = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.bd]
  simp only [callFn, classGenMinorTyBody]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        stubM_spec p "open_pis_at_fvars_f" n, targetPiDomsWith_spec p h.ev h.copy h.alloc h.cons h.tpd n,
        classGenMinorTyIhsGo_spec p h n, classGenMinorTyConcl_spec p h n] <;>
      finish (gen := 20) [rdW_eq, loc_init4, loc_init5, loc_init6, loc_init7]

theorem classGenMinorCi_spec (n : Nat) (s₀ : St) (ci : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_minor_ci" [ci]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      r = [rdW (s₀.mem.arr64 IW) (ci + 1), rdW (s₀.mem.arr64 IW) (ci + 2), rdW (s₀.mem.arr64 IW) (ci + 3),
        rdW (s₀.mem.arr64 IW) (ci + 4)]; ⊤⦄ := by
  rw [invoke_eq _ h.mnci]
  simp only [callFn, classGenMinorCi]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish (gen := 20) [rdW_eq]

theorem classGenMinorTy_spec (n : Nat) (s₀ : St) (g c x d : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_minor_ty" [g, c, x, d]
    ⦃fun r s' => LocEq s' s₀ ∧ mnW n s₀.mem g c x d = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.mn]
  simp only [callFn, classGenMinorTy]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        targetMajorAt_spec p h.alloc h.pw h.mtm h.tmd h.tma n, classGenMinorCi_spec p h n,
        classGenMinorTyBody_spec p h n] <;>
      finish (gen := 20) [rdW_eq]

end specs

end L.Ind
