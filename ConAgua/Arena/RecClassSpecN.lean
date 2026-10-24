import ConAgua.Arena.RecClassSpecM

/-!
# `RecClass`: `classGenRule` — models and specs (lane `indproofs2`, helper `rec2`)
-/


noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem loc_init13 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : Word) (r : List Word) :
    Locals.init (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: r) 13 =
      x13 := rfl
theorem loc_init14 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : Word) (r : List Word) :
    Locals.init (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: r)
      14 = x14 := rfl
theorem loc_init15 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Word) (r : List Word) :
    Locals.init
      (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: r)
      15 = x15 := rfl

/-! ## `find_slot`, `pvars_go` -/

/-- **The model of `class_gen_rule_find_slot_go`.** -/
def fsgW : Nat → Mem → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, so, sl, j, c, cn =>
    if sl ≤ j then some ([0, 0], m)
    else if rdW (m.arr64 IW) (rdW (m.arr64 IW) (so + j)) = 1 ∧
        rdW (m.arr64 IW) (rdW (m.arr64 IW) (so + j) + 1) = c ∧
        rdW (m.arr64 IW) (rdW (m.arr64 IW) (so + j) + 2) = cn then some ([1, j], m)
    else fcK (fsgW n m so sl (j + 1) c cn)

/-- **The model of `class_gen_rule_find_slot`.** -/
def gfsW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, g, c, cn => fcK (fsgW n m (rdW (m.arr64 IW) (g + 7)) (rdW (m.arr64 IW) (g + 8)) 0 c cn)

def pvK2 (n : Nat) (v : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => fcK (consW n m2 v (r2.headD 0) (r2.tail.headD 0))

def pvK1 (n : Nat) (next : Mem → Option (List Word × Mem)) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => pvK2 n (r1.headD 0) (next m1)

/-- **The model of `class_gen_rule_pvars_go`.** -/
def pvW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, g, rP, i =>
    if rP ≤ i then some ([0, 0], m)
    else pvK1 n (fun m1 => pvW n m1 g rP (i + 1))
      (if i < rdW (m.arr64 IW) (g + 0) then
        fuelW n (exprGetDW m (rdW (m.arr64 IW) (g + 1)) (rdW (m.arr64 IW) (g + 2)) i)
      else slotVarW m g (i - rdW (m.arr64 IW) (g + 0)))

/-! ## One call -/

def c1cK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([1, r.headD 0], m)

def c1cK1 (n : Nat) (e app : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if e + r1.tail.headD 0 < e then none else c1cK2 (closeLamsW n m1 (r1.headD 0) (r1.tail.headD 0) e app)

/-- **The model of `class_gen_rule_call1_close`.** -/
def c1cW : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, xso, xsl, e, app => c1cK1 n e app (ftdsF m [xso, xsl])

def c1tK6 (n : Nat) (xso xsl e : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r6, m6) => fcK (c1cW n m6 xso xsl e (r6.headD 0))

def c1tK5 (n : Nat) (xso xsl e rc : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) => c1tK6 n xso xsl e (mknF m5 [rc, r5.headD 0, r5.tail.headD 0])

def c1tK4 (n : Nat) (xso xsl e rc fx : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => c1tK5 n xso xsl e rc (snocW n m4 (r4.headD 0) (r4.tail.headD 0) fx)

def c1tK3 (n : Nat) (pvo pvl xso xsl idxo idxl e fx : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rc, m3) =>
    if 4294967296 ≤ rc then none else c1tK4 n xso xsl e rc fx (appendW n m3 pvo pvl idxo idxl)

def c1tK2 (n : Nat) (pvo pvl rlvls xso xsl idxo idxl r e : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => c1tK3 n pvo pvl xso xsl idxo idxl e (r2.headD 0) (ceinternW m2 r rlvls)

def c1tK1 (n : Nat) (pvo pvl rlvls xso xsl idxo idxl r e : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => c1tK2 n pvo pvl rlvls xso xsl idxo idxl r e (mknF m1 [r1.headD 0, xso, xsl])

/-- **The model of `class_gen_rule_call1_tail`.** -/
def c1tW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, fvso, fvsl, pvo, pvl, rlvls, xso, xsl, idxo, idxl, r, i, e =>
    c1tK1 n pvo pvl rlvls xso xsl idxo idxl r e (fuelW n (exprGetDW m fvso fvsl i))

def c1K3 (n : Nat) (fvso fvsl pvo pvl rlvls xso xsl idxo idxl i e : Word) (m2 : Mem) :
    Option (List Word) → Option (List Word × Mem)
  | none => none
  | some r3 =>
    if r3.headD 0 = 0 then some ([0, 0], m2)
    else fcK (c1tW n m2 fvso fvsl pvo pvl rlvls xso xsl idxo idxl (r3.tail.headD 0) i e)

def c1K2 (n : Nat) (t fvso fvsl pvo pvl rlvls rco rcl cgo cgl i e : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if r2.headD 0 = 0 then some ([0, 0], m2)
    else c1K3 n fvso fvsl pvo pvl rlvls (r2.tail.headD 0) (r2.tail.tail.headD 0) (r2.tail.tail.tail.headD 0)
      (r2.tail.tail.tail.tail.headD 0) i e m2 (classRecOfW n m2 rco rcl cgo cgl t)

def c1K1 (n : Nat) (g t tele fvso fvsl pvo pvl rlvls rco rcl cgo cgl i e : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    c1K2 n t fvso fvsl pvo pvl rlvls rco rcl cgo cgl i e (rec2IhF n m1 g t tele (r1.headD 0) e)

/-- **The model of `class_gen_rule_call1`.** -/
def c1W : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, g, t, tele, wso, wsl, fvso, fvsl, pvo, pvl, rlvls, rco, rcl, cgo, cgl, i, e =>
    c1K1 n g t tele fvso fvsl pvo pvl rlvls rco rcl cgo cgl i e (fuelW n (exprGetDW m wso wsl i))

/-! ## The calls -/

mutual
/-- **The model of `class_gen_rule_calls_go`.** -/
def cgW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, g, x, wso, wsl, fvso, fvsl, pvo, pvl, rlvls, rco, rcl, cgo, cgl, e, nn, i =>
    if nn = 0 then some ([1, 0, 0], m)
    else if isTag m x i = 1 then
      cgK1 n g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e nn i
        (c1W n m g (rdW (m.arr64 IW) (isKp m x i + 1)) (rdW (m.arr64 IW) (isKp m x i + 2)) wso wsl fvso fvsl
          pvo pvl rlvls rco rcl cgo cgl i e)
    else isK3 (cgW n m g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e (nn - 1) (i + 1))
def cgK1 (n : Nat) (g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e nn i : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if r1.headD 0 = 0 then some ([0, 0, 0], m1)
    else isK2 n (r1.tail.headD 0)
      (cgW n m1 g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e (nn - 1) (i + 1))
end

/-! ## The closing, the body, the rule -/

def grcK5 (n : Nat) (body : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) => c1cK2 (closeLamsW n m5 (r5.headD 0) (r5.tail.headD 0) 0 body)

def grcK4 (n : Nat) (g body : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) =>
    grcK5 n body (appendW n m4 (rdW (m4.arr64 IW) (g + 12)) (rdW (m4.arr64 IW) (g + 13)) (r4.headD 0) (r4.tail.headD 0))

def grcK3 (n : Nat) (g fo fl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => grcK4 n g (r3.headD 0) (ftdsF m3 [fo, fl])

def grcK2 (n : Nat) (g fo fl sv : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => grcK3 n g fo fl (mknF m2 [sv, r2.headD 0, r2.tail.headD 0])

def grcK1 (n : Nat) (g fo fl ihso ihsl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => grcK2 n g fo fl (r1.headD 0) (appendW n m1 fo fl ihso ihsl)

/-- **The model of `class_gen_rule_close`.** -/
def grcW : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, m, g, s, fo, fl, ihso, ihsl => grcK1 n g fo fl ihso ihsl (slotVarW m g s)

def rbK3 (n : Nat) (g s fo fl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) =>
    if r3.headD 0 = 0 then some ([0, 0], m3)
    else fcK (grcW n m3 g s fo fl (r3.tail.headD 0) (r3.tail.tail.headD 0))

def rbK2 (n : Nat) (g rco rcl cgo cgl rlvls x rP s fo fl wso wsl : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if rP + rdW (m2.arr64 IW) (x + 1) < rP then none
    else rbK3 n g s fo fl (cgW n m2 g x wso wsl fo fl (r2.headD 0) (r2.tail.headD 0) rlvls rco rcl cgo cgl
      (rP + rdW (m2.arr64 IW) (x + 1)) (rdW (m2.arr64 IW) (x + 1)) 0)

def rbK1 (n : Nat) (g rco rcl cgo cgl rlvls x rP s fo fl : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if r1.headD 0 = 0 then some ([0, 0], m1)
    else rbK2 n g rco rcl cgo cgl rlvls x rP s fo fl (r1.tail.headD 0) (r1.tail.tail.headD 0) (pvW n m1 g rP 0)

/-- **The model of `class_gen_rule_body`.** -/
def rbW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, g, rco, rcl, cgo, cgl, rlvls, x, rP, s, fo, fl =>
    rbK1 n g rco rcl cgo cgl rlvls x rP s fo fl (pdW n m fo fl (rdW (m.arr64 IW) (x + 5)))

def ruK2 (n : Nat) (g rco rcl cgo cgl rlvls x rP s : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if r2.headD 0 = 0 then some ([0, 0], m2)
    else fcK (rbW n m2 g rco rcl cgo cgl rlvls x rP s (r2.tail.headD 0) (r2.tail.tail.headD 0))

def ruK1 (n : Nat) (g rco rcl cgo cgl rlvls x rP : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if r1.headD 0 = 0 then some ([0, 0], m1)
    else ruK2 n g rco rcl cgo cgl rlvls x rP (r1.tail.headD 0)
      (opfF m1 [rdW (m1.arr64 IW) (x + 1), rdW (m1.arr64 IW) (x + 4), rP])

/-- **The model of `class_gen_rule`.** -/
def ruW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, g, rco, rcl, cgo, cgl, rlvls, c, x =>
    ruK1 n g rco rcl cgo cgl rlvls x (rdW (m.arr64 IW) (g + 13))
      (gfsW n m g c (rdW (m.arr64 EREC) (rdW (m.arr64 IW) x)))

/-! ## Arms -/

section arms
variable (n : Nat) (m m1 m2 m3 m4 m5 m6 : Mem) (next : Mem → Option (List Word × Mem))
  (g x so sl j c cn rP i v e app fvso fvsl pvo pvl rlvls xso xsl idxo idxl r t tele wso wsl rco rcl cgo cgl
    nn s fo fl ihso ihsl body sv rc fx : Word) (r1 r2 r3 r4 r5 r6 : List Word)
theorem fsgW_end (h : sl ≤ j) : fsgW (n + 1) m so sl j c cn = some ([0, 0], m) := by simp [fsgW, h]
theorem fsgW_hit (h : ¬ sl ≤ j) (h2 : rdW (m.arr64 IW) (rdW (m.arr64 IW) (so + j)) = 1 ∧
    rdW (m.arr64 IW) (rdW (m.arr64 IW) (so + j) + 1) = c ∧ rdW (m.arr64 IW) (rdW (m.arr64 IW) (so + j) + 2) = cn) :
    fsgW (n + 1) m so sl j c cn = some ([1, j], m) := by
  simp only [fsgW]; rw [if_neg h, if_pos h2]
theorem fsgW_miss (h : ¬ sl ≤ j) (h2 : ¬ (rdW (m.arr64 IW) (rdW (m.arr64 IW) (so + j)) = 1 ∧
    rdW (m.arr64 IW) (rdW (m.arr64 IW) (so + j) + 1) = c ∧ rdW (m.arr64 IW) (rdW (m.arr64 IW) (so + j) + 2) = cn)) :
    fsgW (n + 1) m so sl j c cn = fcK (fsgW n m so sl (j + 1) c cn) := by
  simp only [fsgW]; rw [if_neg h, if_neg h2]
theorem gfsW_eq : gfsW (n + 1) m g c cn = fcK (fsgW n m (rdW (m.arr64 IW) (g + 7)) (rdW (m.arr64 IW) (g + 8)) 0 c cn) :=
  rfl
theorem pvW_end (h : rP ≤ i) : pvW (n + 1) m g rP i = some ([0, 0], m) := by simp [pvW, h]
theorem pvW_step (h : ¬ rP ≤ i) : pvW (n + 1) m g rP i = pvK1 n (fun m1 => pvW n m1 g rP (i + 1))
    (if i < rdW (m.arr64 IW) (g + 0) then
      fuelW n (exprGetDW m (rdW (m.arr64 IW) (g + 1)) (rdW (m.arr64 IW) (g + 2)) i)
    else slotVarW m g (i - rdW (m.arr64 IW) (g + 0))) := by
  simp only [pvW]; rw [if_neg h]
theorem pvK1_some : pvK1 n next (some (r1, m1)) = pvK2 n (r1.headD 0) (next m1) := rfl
theorem pvK2_some : pvK2 n v (some (r2, m2)) = fcK (consW n m2 v (r2.headD 0) (r2.tail.headD 0)) := rfl
theorem c1cW_eq : c1cW (n + 1) m xso xsl e app = c1cK1 n e app (ftdsF m [xso, xsl]) := rfl
theorem c1cK1_big (h : e + r1.tail.headD 0 < e) : c1cK1 n e app (some (r1, m1)) = none := by rw [c1cK1, if_pos h]
theorem c1cK1_ok (h : ¬ e + r1.tail.headD 0 < e) : c1cK1 n e app (some (r1, m1)) =
    c1cK2 (closeLamsW n m1 (r1.headD 0) (r1.tail.headD 0) e app) := by rw [c1cK1, if_neg h]
theorem c1cK2_some : c1cK2 (some (r2, m2)) = some ([1, r2.headD 0], m2) := rfl
theorem c1tW_eq : c1tW (n + 1) m fvso fvsl pvo pvl rlvls xso xsl idxo idxl r i e =
    c1tK1 n pvo pvl rlvls xso xsl idxo idxl r e (fuelW n (exprGetDW m fvso fvsl i)) := rfl
theorem c1tK1_some : c1tK1 n pvo pvl rlvls xso xsl idxo idxl r e (some (r1, m1)) =
    c1tK2 n pvo pvl rlvls xso xsl idxo idxl r e (mknF m1 [r1.headD 0, xso, xsl]) := rfl
theorem c1tK2_some : c1tK2 n pvo pvl rlvls xso xsl idxo idxl r e (some (r2, m2)) =
    c1tK3 n pvo pvl xso xsl idxo idxl e (r2.headD 0) (ceinternW m2 r rlvls) := rfl
theorem c1tK3_big (h : 4294967296 ≤ rc) : c1tK3 n pvo pvl xso xsl idxo idxl e fx (some (rc, m3)) = none := by
  rw [c1tK3, if_pos h]
theorem c1tK3_ok (h : ¬ 4294967296 ≤ rc) : c1tK3 n pvo pvl xso xsl idxo idxl e fx (some (rc, m3)) =
    c1tK4 n xso xsl e rc fx (appendW n m3 pvo pvl idxo idxl) := by rw [c1tK3, if_neg h]
theorem c1tK4_some : c1tK4 n xso xsl e rc fx (some (r4, m4)) =
    c1tK5 n xso xsl e rc (snocW n m4 (r4.headD 0) (r4.tail.headD 0) fx) := rfl
theorem c1tK5_some : c1tK5 n xso xsl e rc (some (r5, m5)) =
    c1tK6 n xso xsl e (mknF m5 [rc, r5.headD 0, r5.tail.headD 0]) := rfl
theorem c1tK6_some : c1tK6 n xso xsl e (some (r6, m6)) = fcK (c1cW n m6 xso xsl e (r6.headD 0)) := rfl
theorem c1W_eq : c1W (n + 1) m g t tele wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl i e =
    c1K1 n g t tele fvso fvsl pvo pvl rlvls rco rcl cgo cgl i e (fuelW n (exprGetDW m wso wsl i)) := rfl
theorem c1K1_some : c1K1 n g t tele fvso fvsl pvo pvl rlvls rco rcl cgo cgl i e (some (r1, m1)) =
    c1K2 n t fvso fvsl pvo pvl rlvls rco rcl cgo cgl i e (rec2IhF n m1 g t tele (r1.headD 0) e) := rfl
theorem c1K2_fail (h : r2.headD 0 = 0) : c1K2 n t fvso fvsl pvo pvl rlvls rco rcl cgo cgl i e (some (r2, m2)) =
    some ([0, 0], m2) := by rw [c1K2, if_pos h]
theorem c1K2_ok (h : r2.headD 0 ≠ 0) : c1K2 n t fvso fvsl pvo pvl rlvls rco rcl cgo cgl i e (some (r2, m2)) =
    c1K3 n fvso fvsl pvo pvl rlvls (r2.tail.headD 0) (r2.tail.tail.headD 0) (r2.tail.tail.tail.headD 0)
      (r2.tail.tail.tail.tail.headD 0) i e m2 (classRecOfW n m2 rco rcl cgo cgl t) := by rw [c1K2, if_neg h]
theorem c1K3_fail (h : r3.headD 0 = 0) : c1K3 n fvso fvsl pvo pvl rlvls xso xsl idxo idxl i e m2 (some r3) =
    some ([0, 0], m2) := by rw [c1K3, if_pos h]
theorem c1K3_ok (h : r3.headD 0 ≠ 0) : c1K3 n fvso fvsl pvo pvl rlvls xso xsl idxo idxl i e m2 (some r3) =
    fcK (c1tW n m2 fvso fvsl pvo pvl rlvls xso xsl idxo idxl (r3.tail.headD 0) i e) := by rw [c1K3, if_neg h]
theorem cgW_end (h : nn = 0) : cgW (n + 1) m g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e nn i =
    some ([1, 0, 0], m) := by simp only [cgW]; rw [if_pos h]
theorem cgW_rec (h : ¬ nn = 0) (ht : isTag m x i = 1) :
    cgW (n + 1) m g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e nn i =
      cgK1 n g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e nn i
        (c1W n m g (rdW (m.arr64 IW) (isKp m x i + 1)) (rdW (m.arr64 IW) (isKp m x i + 2)) wso wsl fvso fvsl
          pvo pvl rlvls rco rcl cgo cgl i e) := by
  simp only [cgW]; rw [if_neg h, if_pos ht]
theorem cgW_ord (h : ¬ nn = 0) (ht : ¬ isTag m x i = 1) :
    cgW (n + 1) m g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e nn i =
      isK3 (cgW n m g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e (nn - 1) (i + 1)) := by
  simp only [cgW]; rw [if_neg h, if_neg ht]
theorem cgK1_fail (h : r1.headD 0 = 0) :
    cgK1 n g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e nn i (some (r1, m1)) = some ([0, 0, 0], m1) := by
  rw [cgK1, if_pos h]
theorem cgK1_ok (h : r1.headD 0 ≠ 0) :
    cgK1 n g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e nn i (some (r1, m1)) =
      isK2 n (r1.tail.headD 0) (cgW n m1 g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e (nn - 1) (i + 1)) := by
  rw [cgK1, if_neg h]
theorem grcW_eq : grcW (n + 1) m g s fo fl ihso ihsl = grcK1 n g fo fl ihso ihsl (slotVarW m g s) := rfl
theorem grcK1_some : grcK1 n g fo fl ihso ihsl (some (r1, m1)) = grcK2 n g fo fl (r1.headD 0) (appendW n m1 fo fl ihso ihsl) :=
  rfl
theorem grcK2_some : grcK2 n g fo fl sv (some (r2, m2)) =
    grcK3 n g fo fl (mknF m2 [sv, r2.headD 0, r2.tail.headD 0]) := rfl
theorem grcK3_some : grcK3 n g fo fl (some (r3, m3)) = grcK4 n g (r3.headD 0) (ftdsF m3 [fo, fl]) := rfl
theorem grcK4_some : grcK4 n g body (some (r4, m4)) =
    grcK5 n body (appendW n m4 (rdW (m4.arr64 IW) (g + 12)) (rdW (m4.arr64 IW) (g + 13)) (r4.headD 0) (r4.tail.headD 0)) :=
  rfl
theorem grcK5_some : grcK5 n body (some (r5, m5)) = c1cK2 (closeLamsW n m5 (r5.headD 0) (r5.tail.headD 0) 0 body) := rfl
theorem rbW_eq : rbW (n + 1) m g rco rcl cgo cgl rlvls x rP s fo fl =
    rbK1 n g rco rcl cgo cgl rlvls x rP s fo fl (pdW n m fo fl (rdW (m.arr64 IW) (x + 5))) := rfl
theorem rbK1_fail (h : r1.headD 0 = 0) : rbK1 n g rco rcl cgo cgl rlvls x rP s fo fl (some (r1, m1)) =
    some ([0, 0], m1) := by rw [rbK1, if_pos h]
theorem rbK1_ok (h : r1.headD 0 ≠ 0) : rbK1 n g rco rcl cgo cgl rlvls x rP s fo fl (some (r1, m1)) =
    rbK2 n g rco rcl cgo cgl rlvls x rP s fo fl (r1.tail.headD 0) (r1.tail.tail.headD 0) (pvW n m1 g rP 0) := by
  rw [rbK1, if_neg h]
theorem rbK2_big (h : rP + rdW (m2.arr64 IW) (x + 1) < rP) :
    rbK2 n g rco rcl cgo cgl rlvls x rP s fo fl wso wsl (some (r2, m2)) = none := by rw [rbK2, if_pos h]
theorem rbK2_ok (h : ¬ rP + rdW (m2.arr64 IW) (x + 1) < rP) :
    rbK2 n g rco rcl cgo cgl rlvls x rP s fo fl wso wsl (some (r2, m2)) =
      rbK3 n g s fo fl (cgW n m2 g x wso wsl fo fl (r2.headD 0) (r2.tail.headD 0) rlvls rco rcl cgo cgl
        (rP + rdW (m2.arr64 IW) (x + 1)) (rdW (m2.arr64 IW) (x + 1)) 0) := by rw [rbK2, if_neg h]
theorem rbK3_fail (h : r3.headD 0 = 0) : rbK3 n g s fo fl (some (r3, m3)) = some ([0, 0], m3) := by
  rw [rbK3, if_pos h]
theorem rbK3_ok (h : r3.headD 0 ≠ 0) : rbK3 n g s fo fl (some (r3, m3)) =
    fcK (grcW n m3 g s fo fl (r3.tail.headD 0) (r3.tail.tail.headD 0)) := by rw [rbK3, if_neg h]
theorem ruW_eq : ruW (n + 1) m g rco rcl cgo cgl rlvls c x = ruK1 n g rco rcl cgo cgl rlvls x
    (rdW (m.arr64 IW) (g + 13)) (gfsW n m g c (rdW (m.arr64 EREC) (rdW (m.arr64 IW) x))) := rfl
theorem ruK1_fail (h : r1.headD 0 = 0) : ruK1 n g rco rcl cgo cgl rlvls x rP (some (r1, m1)) = some ([0, 0], m1) := by
  rw [ruK1, if_pos h]
theorem ruK1_ok (h : r1.headD 0 ≠ 0) : ruK1 n g rco rcl cgo cgl rlvls x rP (some (r1, m1)) =
    ruK2 n g rco rcl cgo cgl rlvls x rP (r1.tail.headD 0)
      (opfF m1 [rdW (m1.arr64 IW) (x + 1), rdW (m1.arr64 IW) (x + 4), rP]) := by
  rw [ruK1, if_neg h]
theorem ruK2_fail (h : r2.headD 0 = 0) : ruK2 n g rco rcl cgo cgl rlvls x rP s (some (r2, m2)) = some ([0, 0], m2) := by
  rw [ruK2, if_pos h]
theorem ruK2_ok (h : r2.headD 0 ≠ 0) : ruK2 n g rco rcl cgo cgl rlvls x rP s (some (r2, m2)) =
    fcK (rbW n m2 g rco rcl cgo cgl rlvls x rP s (r2.tail.headD 0) (r2.tail.tail.headD 0)) := by
  rw [ruK2, if_neg h]
end arms

attribute [ind_grind] fsgW_end fsgW_hit fsgW_miss gfsW_eq pvW_end pvW_step pvK1_some pvK2_some c1cW_eq
  c1cK1_big c1cK1_ok c1cK2_some c1tW_eq c1tK1_some c1tK2_some c1tK3_big c1tK3_ok c1tK4_some c1tK5_some
  c1tK6_some c1W_eq c1K1_some c1K2_fail c1K2_ok c1K3_fail c1K3_ok cgW_end cgW_rec cgW_ord cgK1_fail cgK1_ok
  grcW_eq grcK1_some grcK2_some grcK3_some grcK4_some grcK5_some rbW_eq rbK1_fail rbK1_ok rbK2_big rbK2_ok rbK3_fail
  rbK3_ok ruW_eq ruK1_fail ruK1_ok ruK2_fail ruK2_ok

/-! ## Specs -/

/-- The lookups `class_gen_rule` needs. -/
structure RuProg (p : Prog) extends PbProg p : Prop where
  lf : p.lookup "lam_find" = some lamFind
  lp : p.lookup "lam_push" = some lamPush
  il : p.lookup "intern_lam" = some internLamL
  mkl : p.lookup "mk_lam" = some mkLam
  cl : p.lookup "close_lams" = some closeLams
  cro : p.lookup "class_rec_of" = some classRecOf
  fsg : p.lookup "class_gen_rule_find_slot_go" = some classGenRuleFindSlotGo
  fs : p.lookup "class_gen_rule_find_slot" = some classGenRuleFindSlot
  pv : p.lookup "class_gen_rule_pvars_go" = some classGenRulePvarsGo
  c1c : p.lookup "class_gen_rule_call1_close" = some classGenRuleCall1Close
  c1t : p.lookup "class_gen_rule_call1_tail" = some classGenRuleCall1Tail
  c1 : p.lookup "class_gen_rule_call1" = some classGenRuleCall1
  cg : p.lookup "class_gen_rule_calls_go" = some classGenRuleCallsGo
  rc : p.lookup "class_gen_rule_close" = some classGenRuleClose
  rb : p.lookup "class_gen_rule_body" = some classGenRuleBody
  ru : p.lookup "class_gen_rule" = some classGenRule

section specs
variable (p : Prog) (h : RuProg p)
include h

theorem findSlotGo_spec (n : Nat) : ∀ (s₀ : St) (so sl j c cn : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_rule_find_slot_go" [so, sl, j, c, cn]
    ⦃fun r s' => LocEq s' s₀ ∧ fsgW n s₀.mem so sl j c cn = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ so sl j c cn
    rw [invoke_eq _ h.fsg]; simp only [callFn, classGenRuleFindSlotGo]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ so sl j c cn
    rw [invoke_eq _ h.fsg]
    simp only [callFn, classGenRuleFindSlotGo]
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih]
    all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
      List.headD_nil, List.tail_nil, Locals.init, List.getD_cons_zero, List.getD_cons_succ, Cmp.eval,
      BinOp.eval, Nat.reduceEqDiff, reduceIte, beq_iff_eq, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at *)
    all_goals grind (gen := 20) [lang_grind, arena_grind, ind_grind, rdW_eq, loc_init4]

theorem findSlot_spec (n : Nat) (s₀ : St) (g c cn : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_rule_find_slot" [g, c, cn]
    ⦃fun r s' => LocEq s' s₀ ∧ gfsW n s₀.mem g c cn = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.fs]
  simp only [callFn, classGenRuleFindSlot]
  rcases n with _ | n
  · vcgen [exec] <;> grind
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, findSlotGo_spec p h n]
  all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
    List.headD_nil, List.tail_nil, Locals.init, List.getD_cons_zero, List.getD_cons_succ, Cmp.eval,
    BinOp.eval, Nat.reduceEqDiff, reduceIte, beq_iff_eq, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at *)
  all_goals grind (gen := 20) [lang_grind, arena_grind, ind_grind, rdW_eq]

theorem pvarsGo_spec (n : Nat) : ∀ (s₀ : St) (g rP i : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_rule_pvars_go" [g, rP, i]
    ⦃fun r s' => LocEq s' s₀ ∧ pvW n s₀.mem g rP i = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ g rP i
    rw [invoke_eq _ h.pv]; simp only [callFn, classGenRulePvarsGo]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ g rP i
    rw [invoke_eq _ h.pv]
    simp only [callFn, classGenRulePvarsGo]
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      rec2ExprGetD_specF p h.bf h.bp h.ib h.egd n,
      slotVar_spec p h.pw h.sf h.sp h.isort h.fvf h.fvp h.ifv h.sv n,
      slCons_specW p h.alloc h.copy h.cons n, ih]
    all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
      List.headD_nil, List.tail_nil, Locals.init, List.getD_cons_zero, List.getD_cons_succ, Cmp.eval,
      BinOp.eval, Nat.reduceEqDiff, reduceIte, beq_iff_eq, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at *)
    all_goals grind (gen := 20) [lang_grind, arena_grind, ind_grind, rdW_eq]

theorem call1Close_spec (n : Nat) (s₀ : St) (xso xsl e app : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_rule_call1_close" [xso, xsl, e, app]
    ⦃fun r s' => LocEq s' s₀ ∧ c1cW n s₀.mem xso xsl e app = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.c1c]
  simp only [callFn, classGenRuleCall1Close]
  rcases n with _ | n
  · vcgen [exec] <;> grind
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
    ftdsF_spec p h.ad n, closeLams_spec p h.db h.lf h.lp h.il h.mkl h.cl h.ab n]
  all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
    List.headD_nil, List.tail_nil, Locals.init, List.getD_cons_zero, List.getD_cons_succ, Cmp.eval,
    BinOp.eval, Nat.reduceEqDiff, reduceIte, beq_iff_eq, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at *)
  all_goals grind (gen := 20) [lang_grind, arena_grind, ind_grind]

theorem call1Tail_spec (n : Nat) (s₀ : St) (fvso fvsl pvo pvl rlvls xso xsl idxo idxl r i e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_rule_call1_tail"
      [fvso, fvsl, pvo, pvl, rlvls, xso, xsl, idxo, idxl, r, i, e]
    ⦃fun r' s' => LocEq s' s₀ ∧ c1tW n s₀.mem fvso fvsl pvo pvl rlvls xso xsl idxo idxl r i e = some (r', s'.mem);
      ⊤⦄ := by
  rw [invoke_eq _ h.c1t]
  simp only [callFn, classGenRuleCall1Tail]
  rcases n with _ | n
  · vcgen [exec] <;> grind
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
    rec2ExprGetD_specF p h.bf h.bp h.ib h.egd n, mknF_spec p h.ad n,
    internConst_spec p h.cf h.cp h.ic n, slAppend_specW p h.alloc h.copy h.app n,
    slSnoc_specW p h.alloc h.copy h.snoc n, call1Close_spec p h n]
  all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
    List.headD_nil, List.tail_nil, Locals.init, List.getD_cons_zero, List.getD_cons_succ, Cmp.eval,
    BinOp.eval, Nat.reduceEqDiff, reduceIte, beq_iff_eq, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at *)
  all_goals grind (gen := 20) (instances := 5000) [lang_grind, arena_grind, ind_grind, loc_init4, loc_init5, loc_init6, loc_init7, loc_init8, loc_init9, loc_init10, loc_init11]

theorem call1_spec (n : Nat) (s₀ : St) (g t tele wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl i e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_rule_call1"
      [g, t, tele, wso, wsl, fvso, fvsl, pvo, pvl, rlvls, rco, rcl, cgo, cgl, i, e]
    ⦃fun r s' => LocEq s' s₀ ∧
      c1W n s₀.mem g t tele wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl i e = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.c1]
  simp only [callFn, classGenRuleCall1]
  rcases n with _ | n
  · vcgen [exec] <;> grind
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
    rec2ExprGetD_specF p h.bf h.bp h.ib h.egd n, rec2IhParts_specF p h.ihp h.ad h.opf n,
    classRecOf_spec p h.cro n, call1Tail_spec p h n]
  all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
    List.headD_nil, List.tail_nil, Locals.init, List.getD_cons_zero, List.getD_cons_succ, Cmp.eval,
    BinOp.eval, Nat.reduceEqDiff, reduceIte, beq_iff_eq, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at *)
  all_goals grind (gen := 20) (instances := 5000) [lang_grind, arena_grind, ind_grind, loc_init4, loc_init5, loc_init6, loc_init7, loc_init8, loc_init9, loc_init10, loc_init11, loc_init12, loc_init13, loc_init14, loc_init15]

set_option maxHeartbeats 2000000 in
theorem callsGo_spec (n : Nat) : ∀ (s₀ : St) (g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e nn i : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_rule_calls_go"
      [g, x, wso, wsl, fvso, fvsl, pvo, pvl, rlvls, rco, rcl, cgo, cgl, e, nn, i]
    ⦃fun r s' => LocEq s' s₀ ∧
      cgW n s₀.mem g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e nn i = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intros
    rw [invoke_eq _ h.cg]; simp only [callFn, classGenRuleCallsGo]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e nn i
    rw [invoke_eq _ h.cg]
    simp only [callFn, classGenRuleCallsGo]
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      call1_spec p h n, slCons_specW p h.alloc h.copy h.cons n, ih]
    all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
      List.headD_nil, List.tail_nil, Locals.init, List.getD_cons_zero, List.getD_cons_succ, Cmp.eval,
      BinOp.eval, Nat.reduceEqDiff, reduceIte, beq_iff_eq, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at *)
    all_goals grind (gen := 20) (instances := 5000) [lang_grind, arena_grind, ind_grind, rdW_eq, isTag, isKp, loc_init4, loc_init5, loc_init6, loc_init7, loc_init8, loc_init9, loc_init10, loc_init11, loc_init12, loc_init13, loc_init14, loc_init15]

theorem ruleClose_spec (n : Nat) (s₀ : St) (g s fo fl ihso ihsl : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "class_gen_rule_close" [g, s, fo, fl, ihso, ihsl]
    ⦃fun r s' => LocEq s' s₀ ∧ grcW n s₀.mem g s fo fl ihso ihsl = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.rc]
  simp only [callFn, classGenRuleClose]
  rcases n with _ | n
  · vcgen [exec] <;> grind
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
    slotVar_spec p h.pw h.sf h.sp h.isort h.fvf h.fvp h.ifv h.sv n,
    slAppend_specW p h.alloc h.copy h.app n, mknF_spec p h.ad n, ftdsF_spec p h.ad n,
    closeLams_spec p h.db h.lf h.lp h.il h.mkl h.cl h.ab n]
  all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
    List.headD_nil, List.tail_nil, Locals.init, List.getD_cons_zero, List.getD_cons_succ, Cmp.eval,
    BinOp.eval, Nat.reduceEqDiff, reduceIte, beq_iff_eq, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at *)
  all_goals grind (gen := 20) [lang_grind, arena_grind, ind_grind, rdW_eq, loc_init4, loc_init5]

theorem ruleBody_spec (n : Nat) (s₀ : St) (g rco rcl cgo cgl rlvls x rP s fo fl : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "class_gen_rule_body" [g, rco, rcl, cgo, cgl, rlvls, x, rP, s, fo, fl]
    ⦃fun r s' => LocEq s' s₀ ∧ rbW n s₀.mem g rco rcl cgo cgl rlvls x rP s fo fl = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.rb]
  simp only [callFn, classGenRuleBody]
  rcases n with _ | n
  · vcgen [exec] <;> grind
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
    targetPiDomsWith_spec p h.ev h.copy h.alloc h.cons h.tpd h.hi1 n, pvarsGo_spec p h n, callsGo_spec p h n,
    ruleClose_spec p h n]
  all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
    List.headD_nil, List.tail_nil, Locals.init, List.getD_cons_zero, List.getD_cons_succ, Cmp.eval,
    BinOp.eval, Nat.reduceEqDiff, reduceIte, beq_iff_eq, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at *)
  all_goals grind (gen := 20) (instances := 5000) [lang_grind, arena_grind, ind_grind, rdW_eq, loc_init4, loc_init5, loc_init6, loc_init7, loc_init8, loc_init9, loc_init10]

theorem classGenRule_spec (n : Nat) (s₀ : St) (g rco rcl cgo cgl rlvls c x : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "class_gen_rule" [g, rco, rcl, cgo, cgl, rlvls, c, x]
    ⦃fun r s' => LocEq s' s₀ ∧ ruW n s₀.mem g rco rcl cgo cgl rlvls c x = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.ru]
  simp only [callFn, classGenRule]
  rcases n with _ | n
  · vcgen [exec] <;> grind
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
    findSlot_spec p h n, opfF_spec p h.opf n, ruleBody_spec p h n]
  all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
    List.headD_nil, List.tail_nil, Locals.init, List.getD_cons_zero, List.getD_cons_succ, Cmp.eval,
    BinOp.eval, Nat.reduceEqDiff, reduceIte, beq_iff_eq, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at *)
  all_goals grind (gen := 20) (instances := 5000) [lang_grind, arena_grind, ind_grind, rdW_eq, loc_init4, loc_init5, loc_init6, loc_init7]

end specs

end L.Ind
