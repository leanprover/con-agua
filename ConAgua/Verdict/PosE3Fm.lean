import ConAgua.Arena.IndPos2
import ConAgua.L.ErrSpec
import ConAgua.Verdict.PosE
import ConAgua.Verdict.DeclValE

/-!
# `nest_fields`' error model (lane `verdicts-b`, helper `ia2`, fork `kn2b`)

The generator's `errors` model of `nest_fields` with its recursive call through `callE`
(`l_model … specs [callE_spec p n "nest_fields"] … errors trace`, the generated definitions and
equations below); its spec by hand (the generator's step proof, without the induction: the
recursive call is a `callE`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

def nfE.k_nest_fields (_p : Prog) : Except L.Err (List L.Word × L.Mem) → Except L.Err (List L.Word × L.Mem)
  | Except.error ε => Except.error ε
  | Except.ok (r, m₁) =>
    Except.ok
      ([(List.headD r 0), (List.headD (List.tail r) 0), (List.headD (List.tail (List.tail r)) 0),
          (List.headD (List.tail (List.tail (List.tail r))) 0),
          (List.headD (List.tail (List.tail (List.tail (List.tail r)))) 0),
          (List.headD (List.tail (List.tail (List.tail (List.tail (List.tail r))))) 0)],
        (m₁))
def nfE.k_sl_snoc_2 (p : Prog) (n : Nat) (vis : L.Word) (ctx : L.Word) (fuel : L.Word) (progOff : L.Word)
    (progLen : L.Word) (base : L.Word) (nF : L.Word) (j : L.Word) (ksOff : L.Word) (ksLen : L.Word) (b : L.Word)
    (ns2 : L.Word) : Except L.Err (List L.Word × L.Mem) → Except L.Err (List L.Word × L.Mem)
  | Except.error ε => Except.error ε
  | Except.ok (r, m₁) =>
    (nfE.k_nest_fields (p)
      (L.callE p n "nest_fields"
        [(vis), (ctx), (fuel), (progOff), (progLen), (base), ((nF) - (1 : L.Word)), ((j) + (1 : L.Word)), (b), (ns2),
          (ksOff), (ksLen), (List.headD r 0), (List.headD (List.tail r) 0)]
        (m₁)))
def nfE.k_sl_snoc (p : Prog) (n : Nat) (vis : L.Word) (ctx : L.Word) (fuel : L.Word) (progOff : L.Word)
    (progLen : L.Word) (base : L.Word) (nF : L.Word) (j : L.Word) (ndsOff : L.Word) (ndsLen : L.Word)
    (b : L.Word) (nd : L.Word) (ns2 : L.Word) :
    Except L.Err (List L.Word × L.Mem) → Except L.Err (List L.Word × L.Mem)
  | Except.error ε => Except.error ε
  | Except.ok (r, m₁) =>
    (nfE.k_sl_snoc_2 (p) (n) (vis) (ctx) (fuel) (progOff) (progLen) (base) (nF) (j) (List.headD r 0)
      (List.headD (List.tail r) 0) (b) (ns2) (L.callE p n "sl_snoc" [(ndsOff), (ndsLen), (nd)] (m₁)))
def nfE.k_instantiate1_fast (p : Prog) (n : Nat) (vis : L.Word) (ctx : L.Word) (fuel : L.Word) (progOff : L.Word)
    (progLen : L.Word) (base : L.Word) (nF : L.Word) (j : L.Word) (ksOff : L.Word) (ksLen : L.Word)
    (ndsOff : L.Word) (ndsLen : L.Word) (k : L.Word) (nd : L.Word) (ns2 : L.Word) :
    Except L.Err (List L.Word × L.Mem) → Except L.Err (List L.Word × L.Mem)
  | Except.error ε => Except.error ε
  | Except.ok (r, m₁) =>
    (nfE.k_sl_snoc (p) (n) (vis) (ctx) (fuel) (progOff) (progLen) (base) (nF) (j) (ndsOff) (ndsLen) (List.headD r 0)
      (nd) (ns2) (L.callE p n "sl_snoc" [(ksOff), (ksLen), (k)] (m₁)))
def nfE.k_intern_fvar (p : Prog) (n : Nat) (vis : L.Word) (ctx : L.Word) (fuel : L.Word) (progOff : L.Word)
    (progLen : L.Word) (base : L.Word) (nF : L.Word) (j : L.Word) (ksOff : L.Word) (ksLen : L.Word)
    (ndsOff : L.Word) (ndsLen : L.Word) (b : L.Word) (k : L.Word) (nd : L.Word) (ns2 : L.Word) :
    Except L.Err (List L.Word × L.Mem) → Except L.Err (List L.Word × L.Mem)
  | Except.error ε => Except.error ε
  | Except.ok (r, m₁) =>
    if 4294967296 ≤ (List.headD r 0) then Except.error (L.Err.abort 0)
    else
      (nfE.k_instantiate1_fast (p) (n) (vis) (ctx) (fuel) (progOff) (progLen) (base) (nF) (j) (ksOff) (ksLen) (ndsOff)
        (ndsLen) (k) (nd) (ns2) (L.callE p n "instantiate1_fast" [(CWF), (b), (List.headD r 0), 0] (m₁)))
def nfE.k_nest_pos (p : Prog) (n : Nat) (vis : L.Word) (ctx : L.Word) (fuel : L.Word) (progOff : L.Word)
    (progLen : L.Word) (base : L.Word) (nF : L.Word) (j : L.Word) (ksOff : L.Word) (ksLen : L.Word)
    (ndsOff : L.Word) (ndsLen : L.Word) (a : L.Word) (b : L.Word) (bj : L.Word) :
    Except L.Err (List L.Word × L.Mem) → Except L.Err (List L.Word × L.Mem)
  | Except.error ε => Except.error ε
  | Except.ok (r, m₁) =>
    (nfE.k_intern_fvar (p) (n) (vis) (ctx) (fuel) (progOff) (progLen) (base) (nF) (j) (ksOff) (ksLen) (ndsOff) (ndsLen)
      (b) (List.headD r 0) (List.headD (List.tail r) 0) (List.headD (List.tail (List.tail r)) 0)
      (L.callE p n "intern_fvar" [(bj), (a)] (m₁)))
def nfE.k_e_view (p : Prog) (n : Nat) (vis : L.Word) (ctx : L.Word) (fuel : L.Word) (progOff : L.Word)
    (progLen : L.Word) (base : L.Word) (nF : L.Word) (j : L.Word) (ns : L.Word) (ksOff : L.Word) (ksLen : L.Word)
    (ndsOff : L.Word) (ndsLen : L.Word) (bj : L.Word) :
    Except L.Err (List L.Word × L.Mem) → Except L.Err (List L.Word × L.Mem)
  | Except.error ε => Except.error ε
  | Except.ok (r, m₁) =>
    (nfE.k_nest_pos (p) (n) (vis) (ctx) (fuel) (progOff) (progLen) (base) (nF) (j) (ksOff) (ksLen) (ndsOff) (ndsLen)
      (List.headD (List.tail r) 0) (List.headD (List.tail (List.tail r)) 0) (bj)
      (L.callE p n "nest_pos"
        [(vis), (ctx), (fuel), (progOff), (progLen), (bj), 0, (List.headD (List.tail r) 0), (ns)] (m₁)))
def nfE (p : Prog) (n : Nat) (m : L.Mem) (vis : L.Word) (ctx : L.Word) (fuel : L.Word) (progOff : L.Word)
    (progLen : L.Word) (base : L.Word) (nF : L.Word) (j : L.Word) (cur : L.Word) (ns : L.Word) (ksOff : L.Word)
    (ksLen : L.Word) (ndsOff : L.Word) (ndsLen : L.Word) : Except L.Err (List L.Word × L.Mem) :=
  match n with
  | 0 => Except.error L.Err.outOfFuel
  | n + 1 =>
    if (nF) = 0 then Except.ok ([(ksOff), (ksLen), (ndsOff), (ndsLen), (cur), (ns)], (m))
    else
      if ((cur) >>> (28 : L.Word) : L.Word) ≠ 6 then Except.error (L.Err.abort (R_NESTED_POSITIVITY_INVALID_NESTED))
      else
        if ((base) + (j)) < (base) then Except.error (L.Err.abort 0)
        else
          if (((base) + (j)) + (1 : L.Word)) = 0 then Except.error (L.Err.abort 0)
          else
            (nfE.k_e_view (p) (n) (vis) (ctx) (fuel) (progOff) (progLen) (base) (nF) (j) (ns) (ksOff) (ksLen) (ndsOff)
              (ndsLen) ((base) + (j)) (L.callE p n "e_view" [(cur)] (m)))
theorem nfE.arm1 (p : Prog) (n : Nat) (m : L.Mem) (vis : L.Word) (ctx : L.Word) (fuel : L.Word) (progOff : L.Word)
    (progLen : L.Word) (base : L.Word) (nF : L.Word) (j : L.Word) (cur : L.Word) (ns : L.Word) (ksOff : L.Word)
    (ksLen : L.Word) (ndsOff : L.Word) (ndsLen : L.Word) (hc1 : (nF) = 0) :
    nfE p (n + 1) m vis ctx fuel progOff progLen base nF j cur ns ksOff ksLen ndsOff ndsLen =
      Except.ok ([(ksOff), (ksLen), (ndsOff), (ndsLen), (cur), (ns)], (m)) :=
  by rw [nfE.eq_2, ite_eq_left hc1]
grind_pattern [arena_grind]nfE.arm1 =>
  nfE p (n + 1) m vis ctx fuel progOff progLen base nF j cur ns ksOff ksLen ndsOff ndsLen
theorem nfE.arm2 (p : Prog) (n : Nat) (m : L.Mem) (vis : L.Word) (ctx : L.Word) (fuel : L.Word) (progOff : L.Word)
    (progLen : L.Word) (base : L.Word) (nF : L.Word) (j : L.Word) (cur : L.Word) (ns : L.Word) (ksOff : L.Word)
    (ksLen : L.Word) (ndsOff : L.Word) (ndsLen : L.Word) (hc1 : (nF) ≠ 0)
    (hc2 : ((cur) >>> (28 : L.Word) : L.Word) = 6) (hc3 : ¬((base) + (j)) < (base))
    (hc4 : (((base) + (j)) + (1 : L.Word)) ≠ 0) :
    nfE p (n + 1) m vis ctx fuel progOff progLen base nF j cur ns ksOff ksLen ndsOff ndsLen =
      (nfE.k_e_view (p) (n) (vis) (ctx) (fuel) (progOff) (progLen) (base) (nF) (j) (ns) (ksOff) (ksLen) (ndsOff)
        (ndsLen) ((base) + (j)) (L.callE p n "e_view" [(cur)] (m))) :=
  by rw [nfE.eq_2, ite_eq_right hc1, ite_eq_right (not_not_intro hc2), ite_eq_right hc3, ite_eq_right hc4]
grind_pattern [arena_grind]nfE.arm2 =>
  nfE p (n + 1) m vis ctx fuel progOff progLen base nF j cur ns ksOff ksLen ndsOff ndsLen
theorem nfE.abort1 (p : Prog) (n : Nat) (m : L.Mem) (vis : L.Word) (ctx : L.Word) (fuel : L.Word)
    (progOff : L.Word) (progLen : L.Word) (base : L.Word) (nF : L.Word) (j : L.Word) (cur : L.Word) (ns : L.Word)
    (ksOff : L.Word) (ksLen : L.Word) (ndsOff : L.Word) (ndsLen : L.Word) (hc1 : (nF) ≠ 0)
    (hc2 : ((cur) >>> (28 : L.Word) : L.Word) ≠ 6) :
    nfE p (n + 1) m vis ctx fuel progOff progLen base nF j cur ns ksOff ksLen ndsOff ndsLen =
      Except.error (L.Err.abort (R_NESTED_POSITIVITY_INVALID_NESTED)) :=
  by rw [nfE.eq_2, ite_eq_right hc1, ite_eq_left hc2]
grind_pattern [arena_grind]nfE.abort1 =>
  nfE p (n + 1) m vis ctx fuel progOff progLen base nF j cur ns ksOff ksLen ndsOff ndsLen
theorem nfE.abort2 (p : Prog) (n : Nat) (m : L.Mem) (vis : L.Word) (ctx : L.Word) (fuel : L.Word)
    (progOff : L.Word) (progLen : L.Word) (base : L.Word) (nF : L.Word) (j : L.Word) (cur : L.Word) (ns : L.Word)
    (ksOff : L.Word) (ksLen : L.Word) (ndsOff : L.Word) (ndsLen : L.Word) (hc1 : (nF) ≠ 0)
    (hc2 : ((cur) >>> (28 : L.Word) : L.Word) = 6) (hc3 : ((base) + (j)) < (base)) :
    nfE p (n + 1) m vis ctx fuel progOff progLen base nF j cur ns ksOff ksLen ndsOff ndsLen =
      Except.error (L.Err.abort 0) :=
  by rw [nfE.eq_2, ite_eq_right hc1, ite_eq_right (not_not_intro hc2), ite_eq_left hc3]
grind_pattern [arena_grind]nfE.abort2 =>
  nfE p (n + 1) m vis ctx fuel progOff progLen base nF j cur ns ksOff ksLen ndsOff ndsLen
theorem nfE.abort3 (p : Prog) (n : Nat) (m : L.Mem) (vis : L.Word) (ctx : L.Word) (fuel : L.Word)
    (progOff : L.Word) (progLen : L.Word) (base : L.Word) (nF : L.Word) (j : L.Word) (cur : L.Word) (ns : L.Word)
    (ksOff : L.Word) (ksLen : L.Word) (ndsOff : L.Word) (ndsLen : L.Word) (hc1 : (nF) ≠ 0)
    (hc2 : ((cur) >>> (28 : L.Word) : L.Word) = 6) (hc3 : ¬((base) + (j)) < (base))
    (hc4 : (((base) + (j)) + (1 : L.Word)) = 0) :
    nfE p (n + 1) m vis ctx fuel progOff progLen base nF j cur ns ksOff ksLen ndsOff ndsLen =
      Except.error (L.Err.abort 0) :=
  by rw [nfE.eq_2, ite_eq_right hc1, ite_eq_right (not_not_intro hc2), ite_eq_right hc3, ite_eq_left hc4]
grind_pattern [arena_grind]nfE.abort3 =>
  nfE p (n + 1) m vis ctx fuel progOff progLen base nF j cur ns ksOff ksLen ndsOff ndsLen
theorem nfE.k_nest_fields.arm1 (p : Prog) (r : List L.Word) (m₁ : L.Mem) :
    nfE.k_nest_fields p (Except.ok (r, m₁)) =
      Except.ok
        ([(List.headD r 0), (List.headD (List.tail r) 0), (List.headD (List.tail (List.tail r)) 0),
            (List.headD (List.tail (List.tail (List.tail r))) 0),
            (List.headD (List.tail (List.tail (List.tail (List.tail r)))) 0),
            (List.headD (List.tail (List.tail (List.tail (List.tail (List.tail r))))) 0)],
          (m₁)) :=
  by rw [nfE.k_nest_fields.eq_2]
grind_pattern [arena_grind]nfE.k_nest_fields.arm1 => nfE.k_nest_fields p (Except.ok (r, m₁))
theorem nfE.k_nest_fields.none (p : Prog) (ε : L.Err) : nfE.k_nest_fields p (Except.error ε) = Except.error ε := by
  rw [nfE.k_nest_fields.eq_1]
grind_pattern [arena_grind]nfE.k_nest_fields.none => nfE.k_nest_fields p (Except.error ε)
theorem nfE.k_sl_snoc_2.arm1 (p : Prog) (n : Nat) (vis : L.Word) (ctx : L.Word) (fuel : L.Word) (progOff : L.Word)
    (progLen : L.Word) (base : L.Word) (nF : L.Word) (j : L.Word) (ksOff : L.Word) (ksLen : L.Word) (b : L.Word)
    (ns2 : L.Word) (r : List L.Word) (m₁ : L.Mem) :
    nfE.k_sl_snoc_2 p n vis ctx fuel progOff progLen base nF j ksOff ksLen b ns2 (Except.ok (r, m₁)) =
      (nfE.k_nest_fields (p)
        (L.callE p n "nest_fields"
          [(vis), (ctx), (fuel), (progOff), (progLen), (base), ((nF) - (1 : L.Word)), ((j) + (1 : L.Word)), (b),
            (ns2), (ksOff), (ksLen), (List.headD r 0), (List.headD (List.tail r) 0)]
          (m₁))) :=
  by rw [nfE.k_sl_snoc_2.eq_2]
grind_pattern [arena_grind]nfE.k_sl_snoc_2.arm1 =>
  nfE.k_sl_snoc_2 p n vis ctx fuel progOff progLen base nF j ksOff ksLen b ns2 (Except.ok (r, m₁))
theorem nfE.k_sl_snoc_2.none (p : Prog) (n : Nat) (vis : L.Word) (ctx : L.Word) (fuel : L.Word) (progOff : L.Word)
    (progLen : L.Word) (base : L.Word) (nF : L.Word) (j : L.Word) (ksOff : L.Word) (ksLen : L.Word) (b : L.Word)
    (ns2 : L.Word) (ε : L.Err) :
    nfE.k_sl_snoc_2 p n vis ctx fuel progOff progLen base nF j ksOff ksLen b ns2 (Except.error ε) = Except.error ε :=
  by rw [nfE.k_sl_snoc_2.eq_1]
grind_pattern [arena_grind]nfE.k_sl_snoc_2.none =>
  nfE.k_sl_snoc_2 p n vis ctx fuel progOff progLen base nF j ksOff ksLen b ns2 (Except.error ε)
theorem nfE.k_sl_snoc.arm1 (p : Prog) (n : Nat) (vis : L.Word) (ctx : L.Word) (fuel : L.Word) (progOff : L.Word)
    (progLen : L.Word) (base : L.Word) (nF : L.Word) (j : L.Word) (ndsOff : L.Word) (ndsLen : L.Word)
    (b : L.Word) (nd : L.Word) (ns2 : L.Word) (r : List L.Word) (m₁ : L.Mem) :
    nfE.k_sl_snoc p n vis ctx fuel progOff progLen base nF j ndsOff ndsLen b nd ns2 (Except.ok (r, m₁)) =
      (nfE.k_sl_snoc_2 (p) (n) (vis) (ctx) (fuel) (progOff) (progLen) (base) (nF) (j) (List.headD r 0)
        (List.headD (List.tail r) 0) (b) (ns2) (L.callE p n "sl_snoc" [(ndsOff), (ndsLen), (nd)] (m₁))) :=
  by rw [nfE.k_sl_snoc.eq_2]
grind_pattern [arena_grind]nfE.k_sl_snoc.arm1 =>
  nfE.k_sl_snoc p n vis ctx fuel progOff progLen base nF j ndsOff ndsLen b nd ns2 (Except.ok (r, m₁))
theorem nfE.k_sl_snoc.none (p : Prog) (n : Nat) (vis : L.Word) (ctx : L.Word) (fuel : L.Word) (progOff : L.Word)
    (progLen : L.Word) (base : L.Word) (nF : L.Word) (j : L.Word) (ndsOff : L.Word) (ndsLen : L.Word)
    (b : L.Word) (nd : L.Word) (ns2 : L.Word) (ε : L.Err) :
    nfE.k_sl_snoc p n vis ctx fuel progOff progLen base nF j ndsOff ndsLen b nd ns2 (Except.error ε) =
      Except.error ε :=
  by rw [nfE.k_sl_snoc.eq_1]
grind_pattern [arena_grind]nfE.k_sl_snoc.none =>
  nfE.k_sl_snoc p n vis ctx fuel progOff progLen base nF j ndsOff ndsLen b nd ns2 (Except.error ε)
theorem nfE.k_instantiate1_fast.arm1 (p : Prog) (n : Nat) (vis : L.Word) (ctx : L.Word) (fuel : L.Word)
    (progOff : L.Word) (progLen : L.Word) (base : L.Word) (nF : L.Word) (j : L.Word) (ksOff : L.Word)
    (ksLen : L.Word) (ndsOff : L.Word) (ndsLen : L.Word) (k : L.Word) (nd : L.Word) (ns2 : L.Word)
    (r : List L.Word) (m₁ : L.Mem) :
    nfE.k_instantiate1_fast p n vis ctx fuel progOff progLen base nF j ksOff ksLen ndsOff ndsLen k nd ns2
        (Except.ok (r, m₁)) =
      (nfE.k_sl_snoc (p) (n) (vis) (ctx) (fuel) (progOff) (progLen) (base) (nF) (j) (ndsOff) (ndsLen) (List.headD r 0)
        (nd) (ns2) (L.callE p n "sl_snoc" [(ksOff), (ksLen), (k)] (m₁))) :=
  by rw [nfE.k_instantiate1_fast.eq_2]
grind_pattern [arena_grind]nfE.k_instantiate1_fast.arm1 =>
  nfE.k_instantiate1_fast p n vis ctx fuel progOff progLen base nF j ksOff ksLen ndsOff ndsLen k nd ns2
    (Except.ok (r, m₁))
theorem nfE.k_instantiate1_fast.none (p : Prog) (n : Nat) (vis : L.Word) (ctx : L.Word) (fuel : L.Word)
    (progOff : L.Word) (progLen : L.Word) (base : L.Word) (nF : L.Word) (j : L.Word) (ksOff : L.Word)
    (ksLen : L.Word) (ndsOff : L.Word) (ndsLen : L.Word) (k : L.Word) (nd : L.Word) (ns2 : L.Word) (ε : L.Err) :
    nfE.k_instantiate1_fast p n vis ctx fuel progOff progLen base nF j ksOff ksLen ndsOff ndsLen k nd ns2
        (Except.error ε) =
      Except.error ε :=
  by rw [nfE.k_instantiate1_fast.eq_1]
grind_pattern [arena_grind]nfE.k_instantiate1_fast.none =>
  nfE.k_instantiate1_fast p n vis ctx fuel progOff progLen base nF j ksOff ksLen ndsOff ndsLen k nd ns2
    (Except.error ε)
theorem nfE.k_intern_fvar.arm1 (p : Prog) (n : Nat) (vis : L.Word) (ctx : L.Word) (fuel : L.Word)
    (progOff : L.Word) (progLen : L.Word) (base : L.Word) (nF : L.Word) (j : L.Word) (ksOff : L.Word)
    (ksLen : L.Word) (ndsOff : L.Word) (ndsLen : L.Word) (b : L.Word) (k : L.Word) (nd : L.Word) (ns2 : L.Word)
    (r : List L.Word) (m₁ : L.Mem) (hc1 : ¬4294967296 ≤ (List.headD r 0)) :
    nfE.k_intern_fvar p n vis ctx fuel progOff progLen base nF j ksOff ksLen ndsOff ndsLen b k nd ns2
        (Except.ok (r, m₁)) =
      (nfE.k_instantiate1_fast (p) (n) (vis) (ctx) (fuel) (progOff) (progLen) (base) (nF) (j) (ksOff) (ksLen) (ndsOff)
        (ndsLen) (k) (nd) (ns2) (L.callE p n "instantiate1_fast" [(CWF), (b), (List.headD r 0), 0] (m₁))) :=
  by rw [nfE.k_intern_fvar.eq_2, ite_eq_right hc1]
grind_pattern [arena_grind]nfE.k_intern_fvar.arm1 =>
  nfE.k_intern_fvar p n vis ctx fuel progOff progLen base nF j ksOff ksLen ndsOff ndsLen b k nd ns2 (Except.ok (r, m₁))
theorem nfE.k_intern_fvar.abort1 (p : Prog) (n : Nat) (vis : L.Word) (ctx : L.Word) (fuel : L.Word)
    (progOff : L.Word) (progLen : L.Word) (base : L.Word) (nF : L.Word) (j : L.Word) (ksOff : L.Word)
    (ksLen : L.Word) (ndsOff : L.Word) (ndsLen : L.Word) (b : L.Word) (k : L.Word) (nd : L.Word) (ns2 : L.Word)
    (r : List L.Word) (m₁ : L.Mem) (hc1 : 4294967296 ≤ (List.headD r 0)) :
    nfE.k_intern_fvar p n vis ctx fuel progOff progLen base nF j ksOff ksLen ndsOff ndsLen b k nd ns2
        (Except.ok (r, m₁)) =
      Except.error (L.Err.abort 0) :=
  by rw [nfE.k_intern_fvar.eq_2, ite_eq_left hc1]
grind_pattern [arena_grind]nfE.k_intern_fvar.abort1 =>
  nfE.k_intern_fvar p n vis ctx fuel progOff progLen base nF j ksOff ksLen ndsOff ndsLen b k nd ns2 (Except.ok (r, m₁))
theorem nfE.k_intern_fvar.none (p : Prog) (n : Nat) (vis : L.Word) (ctx : L.Word) (fuel : L.Word)
    (progOff : L.Word) (progLen : L.Word) (base : L.Word) (nF : L.Word) (j : L.Word) (ksOff : L.Word)
    (ksLen : L.Word) (ndsOff : L.Word) (ndsLen : L.Word) (b : L.Word) (k : L.Word) (nd : L.Word) (ns2 : L.Word)
    (ε : L.Err) :
    nfE.k_intern_fvar p n vis ctx fuel progOff progLen base nF j ksOff ksLen ndsOff ndsLen b k nd ns2
        (Except.error ε) =
      Except.error ε :=
  by rw [nfE.k_intern_fvar.eq_1]
grind_pattern [arena_grind]nfE.k_intern_fvar.none =>
  nfE.k_intern_fvar p n vis ctx fuel progOff progLen base nF j ksOff ksLen ndsOff ndsLen b k nd ns2 (Except.error ε)
theorem nfE.k_nest_pos.arm1 (p : Prog) (n : Nat) (vis : L.Word) (ctx : L.Word) (fuel : L.Word) (progOff : L.Word)
    (progLen : L.Word) (base : L.Word) (nF : L.Word) (j : L.Word) (ksOff : L.Word) (ksLen : L.Word)
    (ndsOff : L.Word) (ndsLen : L.Word) (a : L.Word) (b : L.Word) (bj : L.Word) (r : List L.Word) (m₁ : L.Mem) :
    nfE.k_nest_pos p n vis ctx fuel progOff progLen base nF j ksOff ksLen ndsOff ndsLen a b bj (Except.ok (r, m₁)) =
      (nfE.k_intern_fvar (p) (n) (vis) (ctx) (fuel) (progOff) (progLen) (base) (nF) (j) (ksOff) (ksLen) (ndsOff)
        (ndsLen) (b) (List.headD r 0) (List.headD (List.tail r) 0) (List.headD (List.tail (List.tail r)) 0)
        (L.callE p n "intern_fvar" [(bj), (a)] (m₁))) :=
  by rw [nfE.k_nest_pos.eq_2]
grind_pattern [arena_grind]nfE.k_nest_pos.arm1 =>
  nfE.k_nest_pos p n vis ctx fuel progOff progLen base nF j ksOff ksLen ndsOff ndsLen a b bj (Except.ok (r, m₁))
theorem nfE.k_nest_pos.none (p : Prog) (n : Nat) (vis : L.Word) (ctx : L.Word) (fuel : L.Word) (progOff : L.Word)
    (progLen : L.Word) (base : L.Word) (nF : L.Word) (j : L.Word) (ksOff : L.Word) (ksLen : L.Word)
    (ndsOff : L.Word) (ndsLen : L.Word) (a : L.Word) (b : L.Word) (bj : L.Word) (ε : L.Err) :
    nfE.k_nest_pos p n vis ctx fuel progOff progLen base nF j ksOff ksLen ndsOff ndsLen a b bj (Except.error ε) =
      Except.error ε :=
  by rw [nfE.k_nest_pos.eq_1]
grind_pattern [arena_grind]nfE.k_nest_pos.none =>
  nfE.k_nest_pos p n vis ctx fuel progOff progLen base nF j ksOff ksLen ndsOff ndsLen a b bj (Except.error ε)
theorem nfE.k_e_view.arm1 (p : Prog) (n : Nat) (vis : L.Word) (ctx : L.Word) (fuel : L.Word) (progOff : L.Word)
    (progLen : L.Word) (base : L.Word) (nF : L.Word) (j : L.Word) (ns : L.Word) (ksOff : L.Word) (ksLen : L.Word)
    (ndsOff : L.Word) (ndsLen : L.Word) (bj : L.Word) (r : List L.Word) (m₁ : L.Mem) :
    nfE.k_e_view p n vis ctx fuel progOff progLen base nF j ns ksOff ksLen ndsOff ndsLen bj (Except.ok (r, m₁)) =
      (nfE.k_nest_pos (p) (n) (vis) (ctx) (fuel) (progOff) (progLen) (base) (nF) (j) (ksOff) (ksLen) (ndsOff) (ndsLen)
        (List.headD (List.tail r) 0) (List.headD (List.tail (List.tail r)) 0) (bj)
        (L.callE p n "nest_pos"
          [(vis), (ctx), (fuel), (progOff), (progLen), (bj), 0, (List.headD (List.tail r) 0), (ns)] (m₁))) :=
  by rw [nfE.k_e_view.eq_2]
grind_pattern [arena_grind]nfE.k_e_view.arm1 =>
  nfE.k_e_view p n vis ctx fuel progOff progLen base nF j ns ksOff ksLen ndsOff ndsLen bj (Except.ok (r, m₁))
theorem nfE.k_e_view.none (p : Prog) (n : Nat) (vis : L.Word) (ctx : L.Word) (fuel : L.Word) (progOff : L.Word)
    (progLen : L.Word) (base : L.Word) (nF : L.Word) (j : L.Word) (ns : L.Word) (ksOff : L.Word) (ksLen : L.Word)
    (ndsOff : L.Word) (ndsLen : L.Word) (bj : L.Word) (ε : L.Err) :
    nfE.k_e_view p n vis ctx fuel progOff progLen base nF j ns ksOff ksLen ndsOff ndsLen bj (Except.error ε) =
      Except.error ε :=
  by rw [nfE.k_e_view.eq_1]
grind_pattern [arena_grind]nfE.k_e_view.none =>
  nfE.k_e_view p n vis ctx fuel progOff progLen base nF j ns ksOff ksLen ndsOff ndsLen bj (Except.error ε)

theorem nfE_spec (p : Prog) (hf : p.lookup "nest_fields" = some nestFieldsL) (n : Nat) (s₀ : St)
    (vis ctx fuel progOff progLen base nF j cur ns ksOff ksLen ndsOff ndsLen : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_fields"
      [vis, ctx, fuel, progOff, progLen, base, nF, j, cur, ns, ksOff, ksLen, ndsOff, ndsLen]
    ⦃fun r s' => LocEq s' s₀ ∧
      nfE p n s₀.mem vis ctx fuel progOff progLen base nF j cur ns ksOff ksLen ndsOff ndsLen = .ok (r, s'.mem);
     fun ε => ε.code ≠ 0 →
      nfE p n s₀.mem vis ctx fuel progOff progLen base nF j cur ns ksOff ksLen ndsOff ndsLen = .error ε⦄ := by
  cases n with
  | zero =>
    rw [_root_.L.invoke_eq _ (hf)]; simp only [_root_.L.callFn, _root_.L.Ind.nestFieldsL]
    vcgen [_root_.L.exec] <;> grind
  | succ n =>
    rw [_root_.L.invoke_eq _ (hf)]; simp only [_root_.L.callFn, _root_.L.Ind.nestFieldsL]
    vcgen [_root_.L.exec, _root_.L.step, _root_.L.evalE, _root_.L.evalC, _root_.L.evalArgs, _root_.L.setLoc,
            _root_.L.setLocs, _root_.L.ld8_specE, _root_.L.st64, _root_.L.setG, ld64_rdW_specE, evalE_tld, tld,
            evalE_cnt, tcntM, evalE_tierE, evalE_idxE, callE_spec p n "nest_fields", _root_.L.callE_spec p n "e_view",
            _root_.L.callE_spec p n "nest_pos", _root_.L.callE_spec p n "intern_fvar",
            _root_.L.callE_spec p n "instantiate1_fast", _root_.L.callE_spec p n "sl_snoc"] <;>
          (try
              simp_all [_root_.L.LocEq, _root_.L.St.setLoc_loc, _root_.L.St.setLoc_mem, _root_.L.St.setLocs_nil,
                _root_.L.St.setLocs_cons, _root_.L.Locals.init_cons_zero,
                _root_.L.Locals.init_cons_succ, _root_.L.Sig.retVal, _root_.L.Sig.retOr, _root_.L.BinOp.eval,
                _root_.L.Cmp.eval, nfE,
                nfE.k_nest_fields, nfE.k_sl_snoc_2, nfE.k_sl_snoc, nfE.k_instantiate1_fast, nfE.k_intern_fvar,
                nfE.k_nest_pos, nfE.k_e_view]) <;>
        grind [lang_grind, arena_grind]

end L.Ind
