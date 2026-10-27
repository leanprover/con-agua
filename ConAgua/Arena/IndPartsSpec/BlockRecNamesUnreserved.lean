import ConAgua.Arena.IndDecStab
import ConAgua.Arena.IndPosSpec.MatesW
import ConAgua.Arena.IndReal
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.Census.Attr
import ConAgua.L.GrindAttr

/-!
# BlockRecNamesUnreserved: `ConRon.Arena.blockRecNamesUnreserved`

The refinement theorems `blockRecNamesUnreserved_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `block_rec_names_unreserved` -/

mutual
/-- **The model of `block_rec_names_unreserved`.** -/
def recUW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, ro, rl =>
    if rl = 0 then some ([1], m)
    else recUK1 n ro rl
      (rrnF m [rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) ro))])

/-- After `reserved_rec_name`. -/
def recUK1 (n : Nat) (ro rl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if r1.headD 0 ≠ 0 then some ([0], m1) else recUK2 (recUW n m1 (ro + 1) (rl - 1))

/-- After the recursive call. -/
def recUK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) => some ([r.headD 0], m2)
end

section arms
variable (n : Nat) (m m1 m2 : Mem) (ro rl : Word) (r1 r : List Word)
theorem recUW_nil (h : rl = 0) : recUW (n + 1) m ro rl = some ([1], m) := by simp [recUW, h]
theorem recUW_cons (h : rl ≠ 0) : recUW (n + 1) m ro rl = recUK1 n ro rl
    (rrnF m [rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) ro))]) := by
  simp [recUW, h]
theorem recUK1_hit (h : r1.headD 0 ≠ 0) : recUK1 n ro rl (some (r1, m1)) = some ([0], m1) := by
  simp only [recUK1]; rw [ite_eq_left h]
theorem recUK1_miss (h : r1.headD 0 = 0) :
    recUK1 n ro rl (some (r1, m1)) = recUK2 (recUW n m1 (ro + 1) (rl - 1)) := by
  simp only [recUK1]; rw [ite_eq_right (by simpa using h)]
theorem recUK2_some : recUK2 (some (r, m2)) = some ([r.headD 0], m2) := rfl
end arms

grind_pattern [ind_grind] recUW_nil => recUW (n + 1) m ro rl
grind_pattern [ind_grind] recUW_cons => recUW (n + 1) m ro rl
grind_pattern [ind_grind] recUK1_hit => recUK1 n ro rl (some (r1, m1))
grind_pattern [ind_grind] recUK1_miss => recUK1 n ro rl (some (r1, m1))
grind_pattern [ind_grind] recUK2_some => recUK2 (some (r, m2))

section spec
variable (p : Prog) (hp : p.lookup "block_rec_names_unreserved" = some blockRecNamesUnreserved)
  (hrrn : RrnF p)
include hp hrrn

theorem blockRecNamesUnreserved_spec (n : Nat) : ∀ (s₀ : St) (ro rl : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_rec_names_unreserved" [ro, rl]
    ⦃fun r s' => LocEq s' s₀ ∧ recUW n s₀.mem ro rl = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ ro rl; rw [invoke_eq _ hp]; simp only [callFn, blockRecNamesUnreserved]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ ro rl
    rw [invoke_eq _ hp]
    simp only [callFn, blockRecNamesUnreserved]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        rrnF_spec p hrrn n, ih] <;>
      finish (gen := 20) [rdW_eq]

end spec

theorem decCVp_name_p {m : Mem} {q : Nat} {cv : IConstantVal} (h : decCVp m q = some cv)
    (hb : q < 2 ^ 64) :
    (rdW (m.arr64 EREC) (UInt64.ofNat q)).toNat < 2 ^ 32 ∧
      decI (rdW (m.arr64 EREC) (UInt64.ofNat q)) = cv.name := by
  simp only [decCVp, decCV, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨nm, hnm, lv, -, ty, -, hcv⟩ := h
  have hnm' : nm = cv.name := by rw [← hcv]
  rcases hw : (erA m)[q]? with _ | w
  · simp [hd?, hw] at hnm
  by_cases hl : w.toNat < 2 ^ 32
  · simp [hd?, hw, hl] at hnm
    have hrd : rdW (m.arr64 EREC) (UInt64.ofNat q) = w := by
      have e : (UInt64.ofNat q).toNat = q := UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; omega)
      simp only [rdW, e]
      have : (m.arr64 EREC)[q]? = some w := hw
      rw [this]; rfl
    rw [hrd]
    exact ⟨hl, by rw [← hnm', ← hnm]⟩
  · simp [hd?, hw, hl] at hnm

theorem decPL_tail {m : Mem} {α : Type} {f : Nat → Option α} {o k : Nat} {x : α} {xs : List α}
    (h : decPL m f o (k + 1) = some (x :: xs)) : decPL m f (o + 1) k = some xs := by
  rw [decPL_succ] at h
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, List.cons.injEq] at h
  obtain ⟨v, -, y, -, ys, hys, -, rfl⟩ := h
  exact hys

theorem decPL_head {m : Mem} {α : Type} {f : Nat → Option α} {o k : Nat} {x : α} {xs : List α}
    (h : decPL m f o (k + 1) = some (x :: xs)) : ∃ v, iwN m o = some v ∧ f v = some x := by
  rw [decPL_succ] at h
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, List.cons.injEq] at h
  obtain ⟨v, hv, y, hy, ys, -, rfl, -⟩ := h
  exact ⟨v, hv, hy⟩

theorem recUW_ok (n : Nat) : ∀ (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)
    (m0 m m' : Mem) (a : AState) (ro rl : Word) (r : List Word) (recs : List RecShape),
    recUW n m ro rl = some (r, m') → IWGrow m0 m → StageR dn vis fe m a →
    (∀ m'', IWGrow m0 m'' → decPL m'' (decRS m'') ro.toNat rl.toNat = some recs) →
    ro.toNat + rl.toNat < 2 ^ 64 →
    ∃ b a', (ConRon.Arena.blockRecNamesUnreserved recs).run a = .ok (b, a') ∧
      r = [if b then 1 else 0] ∧ StageR dn vis fe m' a' ∧ IWGrow m m' := by
  induction n with
  | zero => intro dn fe vis m0 m m' a ro rl r recs h; simp [recUW] at h
  | succ n ih =>
    intro dn fe vis m0 m m' a ro rl r recs h hg0 hS hdec hb
    by_cases hl : rl = 0
    · rw [recUW_nil n m ro rl hl] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have hrecs : recs = [] := by
        have := hdec m hg0
        rw [hl] at this
        simp only [UInt64.toNat_zero, decPL, List.range_zero, List.mapM_nil, pure,
          Option.some.injEq] at this
        exact this.symm
      subst hrecs
      exact ⟨true, a, rfl, rfl, hS, IWGrow.refl _⟩
    · obtain ⟨k, hk⟩ : ∃ k, rl.toNat = k + 1 := by
        have : rl.toNat ≠ 0 := fun h0 => hl (UInt64.toNat_inj.mp (by simpa using h0))
        exact ⟨rl.toNat - 1, by omega⟩
      have hd := hdec m hg0
      rw [hk] at hd
      -- the list is non-empty
      have hlen := decPL_length m hd
      cases hrecs : recs with
      | nil => rw [hrecs] at hlen; simp at hlen
      | cons rc rest =>
      rw [hrecs] at hd hdec
      obtain ⟨v, hv, hrcd⟩ := decPL_head hd
      obtain ⟨⟨a0, hva, hcvR⟩, -, -, -, -⟩ := decRS_some hrcd
      rw [recUW_cons n m ro rl hl] at h
      obtain ⟨hv', hvb⟩ := iwN_rdW hv (by omega)
      obtain ⟨hva', hab⟩ := iwN_rdW hva (by omega)
      obtain ⟨hn32, hnI⟩ := decCVp_name_p hcvR hab
      rw [ofNat_toNat_word] at hv'
      have hrd : rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) ro)) =
          rdW (m.arr64 EREC) (UInt64.ofNat a0) := by rw [hv', hva']
      rw [hrd] at h
      obtain ⟨r1, m1, hra, h⟩ := ipK_inv h (by simp [recUK1])
      obtain ⟨x1, a1, hrun1, hS1, hg1, hx1, -⟩ :=
        rrnF_ok dn vis fe _ hn32 m m1 a r1 hra hS
      rw [hnI] at hrun1
      by_cases hhit : r1.headD 0 ≠ 0
      · rw [recUK1_hit n m1 ro rl r1 hhit] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        have hx : x1 = true := by rw [← hx1]; simpa using hhit
        refine ⟨false, a1, ?_, rfl, hS1, hg1⟩
        simp only [ConRon.Arena.blockRecNamesUnreserved, StateT.run_bind, hrun1, except_ok_bind, hx]
        rfl
      · have hmiss : r1.headD 0 = 0 := by simpa using hhit
        rw [recUK1_miss n m1 ro rl r1 hmiss] at h
        obtain ⟨r2, m2, hrec, h⟩ := ipK_inv h (by simp [recUK2])
        rw [recUK2_some] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        have hx : x1 = false := by
          rw [← hx1, hmiss]; rfl
        have hro1 : (ro + 1).toNat = ro.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
        have hrl1 : (rl - 1).toNat = k := by
          rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp [hk]
        obtain ⟨b, a2, hrun2, hr2, hS2, hg2⟩ := ih dn fe vis m0 m1 m2 a1 (ro + 1) (rl - 1) r2 rest
          hrec ((IWGrow.trans (hg0) hg1)) hS1
          (fun m'' hg'' => by
            rw [hro1, hrl1]
            exact decPL_tail (by rw [← hk]; exact hdec m'' hg''))
          (by rw [hro1, hrl1]; omega)
        refine ⟨b, a2, ?_, ?_, hS2, hg1.trans hg2⟩
        · simp only [ConRon.Arena.blockRecNamesUnreserved, StateT.run_bind, hrun1, except_ok_bind, hx]
          simpa using hrun2
        · rw [hr2]; simp

/-- **`block_rec_names_unreserved` refines `blockRecNamesUnreserved`** (through `reserved_rec_name`'s
refinement, `rrnF_ok`). The recursor records must keep decoding as the pool grows (`hstab`: every
record lies below the pool's top). -/
@[refines ConRon.Arena.blockRecNamesUnreserved]
theorem blockRecNamesUnreserved_refines (p : Prog)
    (hp : p.lookup "block_rec_names_unreserved" = some blockRecNamesUnreserved) (hrrn : RrnF p)
    (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
    (vis ro rl : Word) (recs : List RecShape) (hS : StageR dn vis fe s₀.mem a₀)
    (hstab : ∀ m'', IWGrow s₀.mem m'' → decPL m'' (decRS m'') ro.toNat rl.toNat = some recs)
    (hb : ro.toNat + rl.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_rec_names_unreserved" [ro, rl]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.blockRecNamesUnreserved recs) a₀ ∧
      r = [if AM.res (ConRon.Arena.blockRecNamesUnreserved recs) a₀ then 1 else 0] ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.blockRecNamesUnreserved recs) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (blockRecNamesUnreserved_spec p hp hrrn n s₀ ro rl) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨b, a', hrun, hr, hS', hg⟩ := recUW_ok n dn fe vis s₀.mem s₀.mem s'.mem a₀ ro rl r recs hm
    (IWGrow.refl _) hS hstab hb
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hres]; exact hr, by rw [hst]; exact hS', hg⟩

/-! ## `check_shapeless_formers` -/

/-- A block: an `EREC` slice of constant-record pointers, decoded. -/
def decEBlk (dn : NIdx → Option ConLeche.Name) (m : Mem) (off cnt : Nat) :
    Option (List IConstantInfo) :=
  (List.range cnt).mapM fun j => do decCI (erA m) dn (← nat? (erA m) (off + j))

/-! ## `block_shape_with_sort` -/

/-- One word copy inside `IW`: `IW[d] := IW[s]`. -/
def cpyIW (m : Mem) (d s : Word) : Mem := m.set64 IW d (rdW (m.arr64 IW) s)

/-- The nine writes of `block_shape_with_sort` to the fresh record `q` (copying `p`'s words, with
the sort `s` and the flag `f` in words 6 and 8). -/
def wsWrites (m : Mem) (q p s f : Word) : Mem :=
  let m4 := cpyIW m q p
  let m5 := cpyIW m4 (q + 1) (p + 1)
  let m6 := cpyIW m5 (q + 2) (p + 2)
  let m7 := cpyIW m6 (q + 3) (p + 3)
  let m8 := cpyIW m7 (q + 4) (p + 4)
  let m9 := cpyIW m8 (q + 5) (p + 5)
  let m10 := m9.set64 IW (q + 6) s
  let m11 := cpyIW m10 (q + 7) (p + 7)
  m11.set64 IW (q + 8) f

mutual

def wsK1 (p s : Word) (m : Mem) : Option Word → Option (List Word × Mem)
  | none => none
  | some z => wsK2 p s (stubM "lvl_eq_c" m [s, z])

def wsK2 (p s : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    match allocW m2 9 with
    | none => none
    | some (q, m3) => some ([q], wsWrites m3 q p s (if r2.headD 0 = 2 then 1 else 0))
end

section arms
variable (n : Nat) (m m1 m2 : Mem) (p s : Word) (r1 r2 : List Word)
theorem wsK2_some : wsK2 p s (some (r2, m2)) = (match allocW m2 9 with
    | none => none
    | some (q, m3) => some ([q], wsWrites m3 q p s (if r2.headD 0 = 2 then 1 else 0))) := rfl
end arms

grind_pattern [ind_grind] wsK2_some => wsK2 p s (some (r2, m2))

/-- **`block_shape_with_sort`'s model, its `lvl_eq_c` call read through `cR`** (`wsW` is the
stubs' reading, `wsC_stub`). -/
def wsK1C (cR : CallM) (n : Nat) (p s : Word) (m : Mem) : Option Word → Option (List Word × Mem)
  | none => none
  | some z => wsK2 p s (cR n "lvl_eq_c" [s, z] m)

def wsC (cR : CallM) : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, p, s => wsK1C cR n p s m (pinWordV m 53)

theorem wsC_step (cR : CallM) (n : Nat) (m : Mem) (p s : Word) :
    wsC cR (n + 1) m p s = wsK1C cR n p s m (pinWordV m 53) := rfl
theorem wsK1C_some (cR : CallM) (n : Nat) (m : Mem) (p s z : Word) :
    wsK1C cR n p s m (some z) = wsK2 p s (cR n "lvl_eq_c" [s, z] m) := rfl
grind_pattern [ind_grind] wsC_step => wsC cR (n + 1) m p s
grind_pattern [ind_grind] wsK1C_some => wsK1C cR n p s m (some z)

section spec
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hpw : p.lookup "pin_word" = some pinWordL)
  (hp : p.lookup "block_shape_with_sort" = some blockShapeWithSort)
include ha hpw hp

set_option maxHeartbeats 1600000 in
theorem blockShapeWithSort_specC (cR : CallM) (hcR : CallSpec p cR) (n : Nat) (s₀ : St) (q s : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "block_shape_with_sort" [q, s]
    ⦃fun r s' => LocEq s' s₀ ∧ wsC cR n s₀.mem q s = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockShapeWithSort]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        pinWord_specV p hpw n, hcR n "lvl_eq_c", iwAlloc_specW p ha n] <;>
      finish (gen := 20) [wsWrites, cpyIW]

end spec

/-- Word `j` of the new record. -/
def wsWd (m : Mem) (p s f : Word) (j : Nat) : Word :=
  if j = 6 then s else if j = 8 then f else rdW (m.arr64 IW) (p + UInt64.ofNat j)

section wsget
variable (m : Mem) (q p s f : Word) (hpq : p.toNat + 9 ≤ q.toNat)
  (hqs : q.toNat + 9 ≤ (m.arr64 IW).size) (hsz : (m.arr64 IW).size < 2 ^ 64)

/-- After `k` writes the first `k` cells of the record hold their words. -/
def WsP (k : Nat) (m' : Mem) : Prop :=
  (m'.arr64 IW).size = (m.arr64 IW).size ∧
  ∀ i, (m'.arr64 IW)[i]? =
    if q.toNat ≤ i ∧ i < q.toNat + k then some (wsWd m p s f (i - q.toNat)) else (m.arr64 IW)[i]?

include hpq hqs hsz in
theorem wsP_step (k : Nat) (hk : k < 9) (m' : Mem) (hP : WsP m q p s f k m') (d v : Word)
    (hd : d.toNat = q.toNat + k) (hv : v = wsWd m p s f k) :
    WsP m q p s f (k + 1) (m'.set64 IW d v) := by
  obtain ⟨hS, hG⟩ := hP
  refine ⟨by rw [Mem.arr64_set64_same]; simpa using hS, fun i => ?_⟩
  rw [set64IW_get, hG]
  by_cases hi : i = q.toNat + k
  · subst hi
    have : (q.toNat + k < (m'.arr64 IW).size) := by omega
    rw [ite_eq_left ⟨by omega, this⟩, ite_eq_left ⟨by omega, by omega⟩]
    have : q.toNat + k - q.toNat = k := by omega
    rw [this, hv]
  · by_cases hi2 : q.toNat ≤ i ∧ i < q.toNat + k
    · rw [ite_eq_right (by omega), ite_eq_left hi2, ite_eq_left (by omega)]
    · rw [ite_eq_right (by omega), ite_eq_right hi2, ite_eq_right (by omega)]

include hpq hqs hsz in
theorem wsP_rd (k : Nat) (m' : Mem) (hP : WsP m q p s f k m') (j : Nat) (hj : j < 9) :
    rdW (m'.arr64 IW) (p + UInt64.ofNat j) = rdW (m.arr64 IW) (p + UInt64.ofNat j) := by
  obtain ⟨hS, hG⟩ := hP
  have hx : (p + UInt64.ofNat j).toNat = p.toNat + j := by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; omega)]
    exact Nat.mod_eq_of_lt (by omega)
  simp only [rdW, hx, hG, ite_eq_right (show ¬ (q.toNat ≤ p.toNat + j ∧ p.toNat + j < q.toNat + k) by omega)]

include hpq hqs hsz in
theorem wsWrites_get : WsP m q p s f 9 (wsWrites m q p s f) := by
  have h0 : WsP m q p s f 0 m := ⟨rfl, fun i => by rw [ite_eq_right (by omega)]⟩
  have qk : ∀ k : Nat, k < 9 → (q + UInt64.ofNat k).toNat = q.toNat + k := by
    intro k hk
    rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have cpy : ∀ (k : Nat) (hk : k < 9) (hk6 : k ≠ 6) (hk8 : k ≠ 8) (m' : Mem) (d e : Word)
      (hd : d = q + UInt64.ofNat k) (he : e = p + UInt64.ofNat k), WsP m q p s f k m' →
      WsP m q p s f (k + 1) (cpyIW m' d e) := by
    intro k hk hk6 hk8 m' d e hd he hP
    subst hd he
    exact wsP_step m q p s f hpq hqs hsz k hk m' hP (q + UInt64.ofNat k)
      (rdW (m'.arr64 IW) (p + UInt64.ofNat k)) (qk k hk)
      (by rw [wsP_rd m q p s f hpq hqs hsz k m' hP k hk]; simp [wsWd, hk6, hk8])
  have lit : ∀ (k : Nat) (hk : k < 9) (v : Word) (hv : v = wsWd m p s f k) (m' : Mem) (d : Word)
      (hd : d = q + UInt64.ofNat k), WsP m q p s f k m' → WsP m q p s f (k + 1) (m'.set64 IW d v) := by
    intro k hk v hv m' d hd hP
    subst hd
    exact wsP_step m q p s f hpq hqs hsz k hk m' hP _ v (qk k hk) hv
  have h1 := cpy 0 (by omega) (by omega) (by omega) m q p (by simp) (by simp) h0
  have h2 := cpy 1 (by omega) (by omega) (by omega) _ (q + 1) (p + 1) (by simp) (by simp) h1
  have h3 := cpy 2 (by omega) (by omega) (by omega) _ (q + 2) (p + 2) (by simp) (by simp) h2
  have h4 := cpy 3 (by omega) (by omega) (by omega) _ (q + 3) (p + 3) (by simp) (by simp) h3
  have h5 := cpy 4 (by omega) (by omega) (by omega) _ (q + 4) (p + 4) (by simp) (by simp) h4
  have h6 := cpy 5 (by omega) (by omega) (by omega) _ (q + 5) (p + 5) (by simp) (by simp) h5
  have h7 := lit 6 (by omega) s (by simp [wsWd]) _ (q + 6) (by simp) h6
  have h8 := cpy 7 (by omega) (by omega) (by omega) _ (q + 7) (p + 7) (by simp) (by simp) h7
  have h9 := lit 8 (by omega) f (by simp [wsWd]) _ (q + 8) (by simp) h8
  exact h9

end wsget

theorem iwN_congr {m : Mem} {i j : Nat} (h : (m.arr64 IW)[i]? = (m.arr64 IW)[j]?) :
    iwN m i = iwN m j := by simp only [iwN, nat?, iwA, h]

theorem decAt_congr {m : Mem} {α : Type} (g : Nat → Nat → Option (List α)) {i j : Nat}
    (h0 : (m.arr64 IW)[i]? = (m.arr64 IW)[j]?) (h1 : (m.arr64 IW)[i + 1]? = (m.arr64 IW)[j + 1]?) :
    decAt m g i = decAt m g j := by
  simp only [decAt, iwN_congr h0, iwN_congr h1]

/-- **A record copied from `p` with a new sort and flag decodes as the shape `with` those**. -/
theorem decBS_ws {m : Mem} {q p : Nat} {s f : Word} {bs : BlockShape}
    (hp : decBS m p = some bs) (hs : s.toNat < 2 ^ 32)
    (c0 : (m.arr64 IW)[q]? = (m.arr64 IW)[p]?) (c1 : (m.arr64 IW)[q + 1]? = (m.arr64 IW)[p + 1]?)
    (c2 : (m.arr64 IW)[q + 2]? = (m.arr64 IW)[p + 2]?) (c3 : (m.arr64 IW)[q + 3]? = (m.arr64 IW)[p + 3]?)
    (c4 : (m.arr64 IW)[q + 4]? = (m.arr64 IW)[p + 4]?) (c5 : (m.arr64 IW)[q + 5]? = (m.arr64 IW)[p + 5]?)
    (c7 : (m.arr64 IW)[q + 7]? = (m.arr64 IW)[p + 7]?)
    (c6 : (m.arr64 IW)[q + 6]? = some s) (c8 : (m.arr64 IW)[q + 8]? = some f) :
    decBS m q = some { bs with resSort := decI s, isProp := f != 0 } := by
  obtain ⟨h1, h2, h3, h4, -, h6, -⟩ := decBS_some hp
  have e1 := decAt_congr (m := m) (decPL m (decMS m)) c0 c1
  have e2 := decAt_congr (m := m) (decPL m (decRS m)) (i := q + 2) (j := p + 2) c2 c3
  rw [decBS]
  simp only [bind, pure]
  rw [e1, h1]
  simp only [Option.bind_some]
  rw [e2, h2]
  simp only [Option.bind_some]
  rw [iwN_congr c4, h3]
  simp only [Option.bind_some]
  have e5 : iwH m (q + 5) = (iwH m (p + 5) : Option NIdx) := by simp only [iwH, hd?, iwA, c5]
  rw [e5, h4]
  simp only [Option.bind_some]
  have e6 : iwH m (q + 6) = (some (decI s) : Option LIdx) := by
    simp only [iwH, hd?, iwA, c6]; simp; omega
  rw [e6]
  simp only [Option.bind_some]
  have e7 : iwB m (q + 7) = iwB m (p + 7) := by simp only [iwB, bool?, iwA, c7]
  rw [e7, h6]
  simp only [Option.bind_some]
  have e8 : iwB m (q + 8) = some (f != 0) := by simp only [iwB, bool?, iwA, c8]; rfl
  rw [e8]
  rfl

theorem wsWrites_frame (m : Mem) (q p s f : Word) : MemFrame [IW] [] m (wsWrites m q p s f) := by
  have fr : ∀ (m : Mem) (d x : Word), MemFrame [IW] [] m (m.set64 IW d x) :=
    fun m d x => MemFrame.set64 m IW (by decide) d x
  unfold wsWrites cpyIW
  exact ((((((((fr _ _ _).trans (fr _ _ _)).trans (fr _ _ _)).trans (fr _ _ _)).trans (fr _ _ _)).trans
    (fr _ _ _)).trans (fr _ _ _)).trans (fr _ _ _)).trans (fr _ _ _)

/-- Writing a fresh record above the top (given the pool's sizes) keeps the stage relation. -/
theorem stage_frame_iw {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m m' : Mem}
    {a : AState} (hS : StageR dn vis fe m a) (hf : MemFrame [IW] [200] m m')
    (htop : iwTop m' ≤ (m.arr64 IW).size) : StageR dn vis fe m' a := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hS.2
  have h129 : rdW (m'.arr64 CTL) 129 = rdW (m.arr64 CTL) 129 := hf.2.1 129 (by simp)
  have hE : m'.arr64 EREC = m.arr64 EREC := hf.1 EREC (by simp [EREC, IW]) (by decide)
  refine ⟨CheckR.frame_iw hf hS.1, by rw [hf.2.2.1 IW]; exact htop, ?_, ?_, ?_, ?_⟩
  · simp only [erTop, h129]; rw [hf.2.2.1 EREC]; exact h2
  · rw [hf.2.2.1 IW]; exact h3
  · rw [hf.2.2.1 EREC]; exact h4
  · rw [hf.2.2.1 CTL]; exact h5

/-- The flag `withSort` computes from the verdict. -/
def isPropOf (x : Option Bool) : Bool :=
  match x with
  | some true => true
  | some false => false
  | none => false

theorem lvlEq_prop {m : Mem} {r2 : List Word} {f : Word} {x2 : Option Bool}
    (hf : (if r2.headD 0 = 2 then (1 : Word) else 0) = f) (h : decLvlEq m r2 x2) :
    (f != 0) = isPropOf x2 := by
  unfold decLvlEq at h
  revert h hf
  cases x2 with
  | none => intro hf h; simp only at h; rw [← hf, h]; decide
  | some b => cases b <;> (intro hf h; simp only at h; rw [← hf, h]; decide)

theorem wsC_ok (cR : CallM) (n : Nat) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)
    (m m' : Mem) (a : AState) (p s : Word) (r : List Word) (bs : BlockShape)
    (h : wsC cR n m p s = some (r, m')) (hS : StageR dn vis fe m a) (hs : s.toNat < 2 ^ 32)
    (hstab : ∀ m'', IWGrow m m'' → decBS m'' p.toNat = some bs) (hp : p.toNat + 9 ≤ iwTop m)
    (hlvl : ∀ (k : Nat) (r2 : List Word) (m2 : Mem), pinW m 0 ≠ 0 →
      cR k "lvl_eq_c" [s, pinW m 53] m = some (r2, m2) →
      ∃ x2 a2, (lvlEq? (decI s) (decI (pinW m 53))).run a = .ok (x2, a2) ∧
        StageR dn vis fe m2 a2 ∧ IWGrow m m2 ∧ decLvlEq m2 r2 x2) :
    ∃ bs' a' q, (BlockShape.withSort bs (decI s)).run a = .ok (bs', a') ∧ r = [q] ∧
      decBS m' q.toNat = some bs' ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧
      q.toNat + 9 ≤ iwTop m' ∧
      (∀ j, j < 9 → j ≠ 6 → j ≠ 8 → (m'.arr64 IW)[q.toNat + j]? = (m'.arr64 IW)[p.toNat + j]?) ∧
      (DecB (fun m => decBS m p.toNat) m bs → DecB (fun m => decBS m q.toNat) m' bs') := by
  cases n with
  | zero => simp [wsC] at h
  | succ n =>
  rw [wsC_step] at h
  obtain ⟨z, hpz, h⟩ := ipK_inv1 h (by simp [wsK1C])
  rw [wsK1C_some] at h
  have hpne : rdW (m.arr64 PINS) 0 ≠ 0 := by
    intro h0; simp [pinWordV, h0] at hpz
  have hz : z = pinW m 53 := by
    simp only [pinWordV, hpne, ite_false, Option.some.injEq] at hpz
    rw [← hpz]; rfl
  have hpin0 : pinW m 0 ≠ 0 := hpne
  have hfull := hS.1.pins.full hpin0
  have hzlt : z.toNat < 2 ^ 32 := by rw [hz]; exact hfull.lv_lt.2.1
  have hrun1 : (zeroLevel).run a = .ok (decI z, a) := by rw [hz]; exact pinZeroLevel_run hfull
  obtain ⟨r2, m2, hrb, h⟩ := ipK_inv h (by simp [wsK2])
  rw [wsK2_some] at h
  obtain ⟨x2, a2, hrun2, hS2, hg2, hdec2⟩ :=
    hlvl n r2 m2 hpin0 (by rw [← hz]; exact hrb)
  rw [← hz] at hrun2
  rcases hal : allocW m2 9 with _ | ⟨q, m3⟩ <;> rw [hal] at h
  · simp at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have hg12 : IWGrow m m2 := hg2
  obtain ⟨hI2, hE2, hIsz2, hEsz2, hCsz2⟩ := hS2.2
  obtain ⟨hq, hm3, hroom⟩ := allocW_facts hal hIsz2
  subst hm3
  have hIW3 : (allocMem m2 9).arr64 IW = m2.arr64 IW := allocMem_IW m2 9
  have hqtop : q.toNat = iwTop m2 := by rw [hq]; rfl
  have hpq : p.toNat + 9 ≤ q.toNat := by
    have := hg12.1; omega
  have hqs : q.toNat + 9 ≤ ((allocMem m2 9).arr64 IW).size := by
    rw [hIW3]; simpa using hroom
  have hsz3 : ((allocMem m2 9).arr64 IW).size < 2 ^ 64 := by rw [hIW3]; exact hIsz2
  generalize hf : (if r2.headD 0 = 2 then (1 : Word) else 0) = f
  have hWs := wsWrites_get (allocMem m2 9) q p s f hpq hqs hsz3
  have hfr : MemFrame [IW] [] (allocMem m2 9) (wsWrites (allocMem m2 9) q p s f) :=
    wsWrites_frame _ _ _ _ _
  generalize hm' : wsWrites (allocMem m2 9) q p s f = m' at hWs hfr
  have hfr2 : MemFrame [IW] [200] m2 m' :=
    ((allocMem_frame m2 9).trans (hfr.mono (by simp) (by simp)))
  -- the pool grew
  have htop : rdW (m'.arr64 CTL) 200 = rdW (m2.arr64 CTL) 200 + 9 := by
    rw [hfr.2.1 200 (by simp), allocMem_top m2 9 hCsz2]
  have hlow : ∀ i < iwTop m2, (m'.arr64 IW)[i]? = (m2.arr64 IW)[i]? := by
    intro i hi
    rw [hWs.2 i, ite_eq_right (by omega), hIW3]
  have hg2' : IWGrow m2 m' := iwGrow_of_frame hfr2 (N := 9) htop (by have := hroom; simp at this; omega) hIsz2 hlow
  have hgm : IWGrow m m' := hg12.trans hg2'
  have hdecp := hstab m' hgm
  have hcell : ∀ j, j < 9 → j ≠ 6 → j ≠ 8 → (m'.arr64 IW)[q.toNat + j]? = (m'.arr64 IW)[p.toNat + j]? := by
    intro j hj h6 h8
    rw [hWs.2, ite_eq_left (by omega)]
    have e : q.toNat + j - q.toNat = j := by omega
    rw [e]
    have hpj : (m'.arr64 IW)[p.toNat + j]? = (m2.arr64 IW)[p.toNat + j]? := by
      rw [hWs.2, ite_eq_right (by omega), hIW3]
    rw [hpj]
    simp only [wsWd, h6, h8, ite_false, rdW]
    have hx : (p + UInt64.ofNat j).toNat = p.toNat + j := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; omega)]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hx, hIW3]
    have hlt : p.toNat + j < (m2.arr64 IW).size := by have := hg12.1; omega
    rw [Array.getElem?_eq_getElem hlt]; rfl
  have c6 : (m'.arr64 IW)[q.toNat + 6]? = some s := by
    rw [hWs.2, ite_eq_left (by omega)]; simp [wsWd]
  have c8 : (m'.arr64 IW)[q.toNat + 8]? = some f := by
    rw [hWs.2, ite_eq_left (by omega)]; simp [wsWd]
  have hdecq := decBS_ws hdecp hs (hcell 0 (by omega) (by omega) (by omega))
    (hcell 1 (by omega) (by omega) (by omega)) (hcell 2 (by omega) (by omega) (by omega))
    (hcell 3 (by omega) (by omega) (by omega)) (hcell 4 (by omega) (by omega) (by omega))
    (hcell 5 (by omega) (by omega) (by omega)) (hcell 7 (by omega) (by omega) (by omega)) c6 c8
  have hprop := lvlEq_prop (m := m2) hf hdec2
  have htop' : iwTop m' ≤ (m'.arr64 IW).size := by
    have e : iwTop m' = iwTop m2 + 9 := by
      simp only [iwTop, htop]; rw [UInt64.toNat_add]; simp
      have := hroom; simp at this; simp only [iwTop] at hqtop; omega
    rw [hfr2.2.2.1 IW, e]; have := hroom; simp at this; omega
  have htopq : q.toNat + 9 ≤ iwTop m' := by
    simp only [iwTop, htop]; rw [UInt64.toNat_add]; simp
    have := hroom; simp at this; simp only [iwTop] at hqtop; omega
  have hpT : ∀ j, j < 9 → p.toNat + j < iwTop m' := fun j hj => by have := hg12.1; have := hg2'.1; omega
  have hDecB : DecB (fun m => decBS m p.toNat) m bs →
      DecB (fun m => decBS m q.toNat) m' { bs with resSort := decI s, isProp := f != 0 } := by
    intro hT
    have hpd : decBS (truncM m') p.toNat = some bs := hT.grow (decBS_mono _) hgm
    have cT : ∀ j, j < 9 → j ≠ 6 → j ≠ 8 →
        ((truncM m').arr64 IW)[q.toNat + j]? = ((truncM m').arr64 IW)[p.toNat + j]? := by
      intro j hj h6 h8
      have e1 := truncM_iw_eq (m := m') (i := q.toNat + j) (by omega)
      have e2 := truncM_iw_eq (m := m') (i := p.toNat + j) (hpT j hj)
      simp only [iwA] at e1 e2
      rw [e1, e2]; exact hcell j hj h6 h8
    have c6T : ((truncM m').arr64 IW)[q.toNat + 6]? = some s := by
      have e1 := truncM_iw_eq (m := m') (i := q.toNat + 6) (by omega); simp only [iwA] at e1
      rw [e1]; exact c6
    have c8T : ((truncM m').arr64 IW)[q.toNat + 8]? = some f := by
      have e1 := truncM_iw_eq (m := m') (i := q.toNat + 8) (by omega); simp only [iwA] at e1
      rw [e1]; exact c8
    show decBS (truncM m') q.toNat = some _
    have := decBS_ws hpd hs (by simpa using cT 0 (by omega) (by omega) (by omega))
      (cT 1 (by omega) (by omega) (by omega)) (cT 2 (by omega) (by omega) (by omega))
      (cT 3 (by omega) (by omega) (by omega)) (cT 4 (by omega) (by omega) (by omega))
      (cT 5 (by omega) (by omega) (by omega)) (cT 7 (by omega) (by omega) (by omega)) c6T c8T
    exact this
  refine ⟨{ bs with resSort := decI s, isProp := f != 0 }, a2, q, ?_, rfl, hdecq,
    stage_frame_iw hS2 hfr2 (by rw [← hfr2.2.2.1 IW]; exact htop'), hgm, htopq, hcell, hDecB⟩
  unfold BlockShape.withSort
  simp only [StateT.run_bind, hrun1, except_ok_bind]
  simp only [hrun2, except_ok_bind]
  rw [hprop]
  rfl

end L.Ind

end
