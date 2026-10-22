import ConAgua.Arena.IndPartsSpec3

/-!
# Refinements of `IndParts`, part 4 (lane `indproofs`, helper `parts`)

The recursor-name checks (`block_rec_names_unreserved`).
-/

set_option experimental.vcgen true
set_option linter.deprecated false

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
      (stubM "reserved_rec_name" m [rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) ro))])

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
    (stubM "reserved_rec_name" m [rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) ro))]) := by
  simp [recUW, h]
theorem recUK1_hit (h : r1.headD 0 ≠ 0) : recUK1 n ro rl (some (r1, m1)) = some ([0], m1) := by
  simp only [recUK1]; rw [if_pos h]
theorem recUK1_miss (h : r1.headD 0 = 0) :
    recUK1 n ro rl (some (r1, m1)) = recUK2 (recUW n m1 (ro + 1) (rl - 1)) := by
  simp only [recUK1]; rw [if_neg (by simpa using h)]
theorem recUK2_some : recUK2 (some (r, m2)) = some ([r.headD 0], m2) := rfl
end arms

grind_pattern [ind_grind] recUW_nil => recUW (n + 1) m ro rl
grind_pattern [ind_grind] recUW_cons => recUW (n + 1) m ro rl
grind_pattern [ind_grind] recUK1_hit => recUK1 n ro rl (some (r1, m1))
grind_pattern [ind_grind] recUK1_miss => recUK1 n ro rl (some (r1, m1))
grind_pattern [ind_grind] recUK2_some => recUK2 (some (r, m2))

section spec
variable (p : Prog) (hp : p.lookup "block_rec_names_unreserved" = some blockRecNamesUnreserved)
include hp

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
        stubM_spec p "reserved_rec_name" n, ih] <;>
      finish (gen := 20) [rdW_eq]

end spec


theorem decCVp_name {m : Mem} {q : Nat} {cv : IConstantVal} (h : decCVp m q = some cv)
    (hb : q < 2 ^ 64) :
    (rdW (m.arr64 EREC) (UInt64.ofNat q)).toNat < 2 ^ 32 ∧
      decI (rdW (m.arr64 EREC) (UInt64.ofNat q)) = cv.name := by
  simp only [decCVp, decCV, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨nm, hnm, lv, -, ty, -, hcv⟩ := h
  have hnm' : nm = cv.name := by rw [← hcv]
  cases hw : (erA m)[q]? with
  | none => simp [hd?, hw] at hnm
  | some w =>
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
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
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
      obtain ⟨hn32, hnI⟩ := decCVp_name hcvR hab
      rw [ofNat_toNat_word] at hv'
      have hrd : rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) ro)) =
          rdW (m.arr64 EREC) (UInt64.ofNat a0) := by rw [hv', hva']
      rw [hrd] at h
      cases hra : stubM "reserved_rec_name" m [rdW (m.arr64 EREC) (UInt64.ofNat a0)] with
      | none => rw [hra] at h; simp [recUK1] at h
      | some rm1 =>
      obtain ⟨r1, m1⟩ := rm1
      rw [hra] at h
      obtain ⟨x1, a1, hrun1, hS1, hg1, hx1, -⟩ :=
        reservedRecName_spec dn vis fe _ hn32 m m1 a r1 hra hS
      rw [hnI] at hrun1
      by_cases hhit : r1.headD 0 ≠ 0
      · rw [recUK1_hit n m1 ro rl r1 hhit] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hx : x1 = true := by rw [← hx1]; simpa using hhit
        refine ⟨false, a1, ?_, rfl, hS1, hg1⟩
        simp only [ConRon.Arena.blockRecNamesUnreserved, StateT.run_bind, hrun1, except_ok_bind, hx]
        rfl
      · have hmiss : r1.headD 0 = 0 := by simpa using hhit
        rw [recUK1_miss n m1 ro rl r1 hmiss] at h
        cases hrec : recUW n m1 (ro + 1) (rl - 1) with
        | none => rw [hrec] at h; simp [recUK2] at h
        | some rm2 =>
        obtain ⟨r2, m2⟩ := rm2
        rw [hrec, recUK2_some] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
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


/-- **`block_rec_names_unreserved` refines `blockRecNamesUnreserved`** (through the stub
`reserved_rec_name`). The recursor records must keep decoding as the pool grows (`hstab`: every
record lies below the pool's top). -/
@[refines ConRon.Arena.blockRecNamesUnreserved]
theorem blockRecNamesUnreserved_refines (p : Prog)
    (hp : p.lookup "block_rec_names_unreserved" = some blockRecNamesUnreserved)
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
  refine triple_post (blockRecNamesUnreserved_spec p hp n s₀ ro rl) ?_
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

theorem decEBlk_succ (dn : NIdx → Option ConLeche.Name) (m : Mem) (off n : Nat) :
    decEBlk dn m off (n + 1) = (do
      let q ← nat? (erA m) off
      let x ← decCI (erA m) dn q
      let xs ← decEBlk dn m (off + 1) n
      pure (x :: xs)) := by
  have e1 : decEBlk dn m off (n + 1) = (List.range (n + 1)).mapM
      (fun j => (nat? (erA m) (off + j)).bind (decCI (erA m) dn)) := rfl
  have e2 : decEBlk dn m (off + 1) n = (List.range n).mapM
      (fun j => (nat? (erA m) (off + 1 + j)).bind (decCI (erA m) dn)) := rfl
  rw [e1, e2, mapM_shift_succ (fun i => (nat? (erA m) i).bind (decCI (erA m) dn)) off n]
  cases nat? (erA m) off <;> rfl

/-- **The model of `check_shapeless_formers`**: the memory after. -/
def sfW : Nat → Mem → Word → Word → Word → Option Mem
  | 0, _, _, _, _ => none
  | n + 1, m, vis, off, cnt =>
    if cnt = 0 then some m
    else if rdW (m.arr64 EREC) (rdW (m.arr64 EREC) off) = 3 then
      sfK1 n vis off cnt (stubM "check_constant_val" m [vis, rdW (m.arr64 EREC) off + 1])
    else sfW n m vis (off + 1) (cnt - 1)
where
  /-- After `check_constant_val`. -/
  sfK1 (n : Nat) (vis off cnt : Word) : Option (List Word × Mem) → Option Mem
    | none => none
    | some (_, m1) => sfW n m1 vis (off + 1) (cnt - 1)

section arms
variable (n : Nat) (m m1 : Mem) (vis off cnt : Word) (r : List Word)
theorem sfW_nil (h : cnt = 0) : sfW (n + 1) m vis off cnt = some m := by simp [sfW, h]
theorem sfW_skip (h : cnt ≠ 0) (h3 : rdW (m.arr64 EREC) (rdW (m.arr64 EREC) off) ≠ 3) :
    sfW (n + 1) m vis off cnt = sfW n m vis (off + 1) (cnt - 1) := by simp [sfW, h, h3]
theorem sfW_former (h : cnt ≠ 0) (h3 : rdW (m.arr64 EREC) (rdW (m.arr64 EREC) off) = 3) :
    sfW (n + 1) m vis off cnt =
      sfW.sfK1 n vis off cnt (stubM "check_constant_val" m [vis, rdW (m.arr64 EREC) off + 1]) := by
  simp [sfW, h, h3]
theorem sfK1_some : sfW.sfK1 n vis off cnt (some (r, m1)) = sfW n m1 vis (off + 1) (cnt - 1) := by
  simp [sfW.sfK1]
end arms

grind_pattern [ind_grind] sfW_nil => sfW (n + 1) m vis off cnt
grind_pattern [ind_grind] sfW_skip => sfW (n + 1) m vis off cnt
grind_pattern [ind_grind] sfW_former => sfW (n + 1) m vis off cnt
grind_pattern [ind_grind] sfK1_some => sfW.sfK1 n vis off cnt (some (r, m1))

section spec
variable (p : Prog) (hp : p.lookup "check_shapeless_formers" = some checkShapelessFormers)
include hp

theorem checkShapelessFormers_spec (n : Nat) : ∀ (s₀ : St) (vis off cnt : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_shapeless_formers" [vis, off, cnt]
    ⦃fun _ s' => LocEq s' s₀ ∧ sfW n s₀.mem vis off cnt = some s'.mem; ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ vis off cnt; rw [invoke_eq _ hp]; simp only [callFn, checkShapelessFormers]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ vis off cnt
    rw [invoke_eq _ hp]
    simp only [callFn, checkShapelessFormers]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        stubM_spec p "check_constant_val" n, ih] <;>
      finish (gen := 20) [rdW_eq]

end spec


theorem decCI_kind {a : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Nat} {ci : IConstantInfo}
    (h : decCI a dn q = some ci) :
    ∃ kd, nat? a q = some kd ∧
      (kd = 3 → ∃ cv caps, ci = .indInfo cv caps ∧ decCV a (q + 1) = some cv) ∧
      (kd ≠ 3 → ∀ cv caps, ci ≠ .indInfo cv caps) := by
  unfold decCI at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨kd, hkd, h⟩ := h
  refine ⟨kd, hkd, ?_, ?_⟩
  · intro hk
    subst hk
    simp only [pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, caps, hcaps, rfl⟩ := h
    exact ⟨cv, caps, rfl, hcv⟩
  · intro hk cv caps hci
    subst hci
    rcases kd with _ | _ | _ | _ | _ | _ | _ | k
    all_goals first
      | exact absurd rfl hk
      | (simp only [pure, Option.bind_eq_some_iff, Option.some.injEq] at h
         obtain ⟨_, _, h⟩ := h
         first | exact absurd h (by simp) | skip)
      | simp at h


theorem erN_rdW {m : Mem} {x : Word} {v : Nat} (h : nat? (erA m) x.toNat = some v) :
    rdW (m.arr64 EREC) x = UInt64.ofNat v ∧ v < 2 ^ 64 := by
  simp only [nat?, erA, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h
  simp only [rdW, hw, Option.getD_some]
  exact ⟨by simp, w.toNat_lt⟩

theorem decCV_idx {a : Array Word} {q : Nat} {cv : IConstantVal} (h : decCV a q = some cv) :
    q < a.size := by
  simp only [decCV, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨nm, hnm, -⟩ := h
  cases hw : a[q]? with
  | none => simp [hd?, hw] at hnm
  | some w => exact (Array.getElem?_eq_some_iff.mp hw).1

theorem sfW_ok (n : Nat) : ∀ (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)
    (m0 m m' : Mem) (a : AState) (off cnt : Word) (blk : List IConstantInfo),
    sfW n m vis off cnt = some m' → IWGrow m0 m → StageR dn vis fe m a →
    (∀ m'', IWGrow m0 m'' → decEBlk dn m'' off.toNat cnt.toNat = some blk) →
    off.toNat + cnt.toNat < 2 ^ 64 →
    ∃ a', (ConRon.Arena.checkShapelessFormers ConLeche.CheckMode.verified fe blk).run a = .ok ((), a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' := by
  induction n with
  | zero => intro dn fe vis m0 m m' a off cnt blk h; simp [sfW] at h
  | succ n ih =>
    intro dn fe vis m0 m m' a off cnt blk h hg0 hS hdec hb
    by_cases hc : cnt = 0
    · rw [sfW_nil n m vis off cnt hc] at h
      simp only [Option.some.injEq] at h
      subst h
      have hblk : blk = [] := by
        have := hdec m hg0
        rw [hc] at this
        simp only [UInt64.toNat_zero, decEBlk, List.range_zero, List.mapM_nil, pure,
          Option.some.injEq] at this
        exact this.symm
      subst hblk
      exact ⟨a, rfl, hS, IWGrow.refl _⟩
    · obtain ⟨k, hk⟩ : ∃ k, cnt.toNat = k + 1 := by
        have : cnt.toNat ≠ 0 := fun h0 => hc (UInt64.toNat_inj.mp (by simpa using h0))
        exact ⟨cnt.toNat - 1, by omega⟩
      have hd := hdec m hg0
      rw [hk, decEBlk_succ] at hd
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hd
      obtain ⟨q, hq, ci, hci, rest, hrest, hblk⟩ := hd
      subst hblk
      obtain ⟨hqw, hqb⟩ := erN_rdW (x := off) hq
      obtain ⟨kd, hkd, hk3, hkn3⟩ := decCI_kind hci
      have hoff1 : (off + 1).toNat = off.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      have hcnt1 : (cnt - 1).toNat = k := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp [hk]
      have hrestdec : ∀ m'', IWGrow m0 m'' → decEBlk dn m'' (off + 1).toNat (cnt - 1).toNat = some rest := by
        intro m'' hg''
        have := hdec m'' hg''
        rw [hk, decEBlk_succ] at this
        simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, List.cons.injEq] at this
        obtain ⟨q', hq', ci', hci', rest', hrest', -, rfl⟩ := this
        rw [hoff1, hcnt1]; exact hrest'
      obtain ⟨hkd', hkb⟩ : rdW (m.arr64 EREC) (rdW (m.arr64 EREC) off) = UInt64.ofNat kd ∧ kd < 2 ^ 64 := by
        rw [hqw]; exact (erN_rdW (x := UInt64.ofNat q) (by
          have : (UInt64.ofNat q).toNat = q := UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; omega)
          rw [this]; exact hkd))
      by_cases h3 : kd = 3
      · subst h3
        obtain ⟨cv, caps, hci3, hcv⟩ := hk3 rfl
        subst hci3
        have h3w : rdW (m.arr64 EREC) (rdW (m.arr64 EREC) off) = 3 := by rw [hkd']; rfl
        rw [sfW_former n m vis off cnt hc h3w] at h
        have hqw1 : rdW (m.arr64 EREC) off + 1 = UInt64.ofNat (q + 1) := by
          rw [hqw]; apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp
        rw [hqw1] at h
        cases hra : stubM "check_constant_val" m [vis, UInt64.ofNat (q + 1)] with
        | none => rw [hra] at h; simp [sfW.sfK1] at h
        | some rm1 =>
        obtain ⟨r1, m1⟩ := rm1
        rw [hra, sfK1_some] at h
        have hqlt := decCV_idx hcv
        have hEsz := hS.2.2.2.2.1
        have hqq : (UInt64.ofNat (q + 1)).toNat = q + 1 :=
          UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; simp only [erA] at hqlt; omega)
        have hcvp : decCVp m (UInt64.ofNat (q + 1)).toNat = some cv := by rw [hqq]; exact hcv
        obtain ⟨x1, a1, hrun1, hS1, hg1, -⟩ :=
          checkConstantVal_spec dn vis fe (UInt64.ofNat (q + 1)) cv m m1 a r1 hra ⟨hS, hcvp⟩
        obtain ⟨a', hrun, hS', hg'⟩ := ih dn fe vis m0 m1 m' a1 (off + 1) (cnt - 1) rest h
          (hg0.trans hg1) hS1 hrestdec (by rw [hoff1, hcnt1]; omega)
        refine ⟨a', ?_, hS', hg1.trans hg'⟩
        simp only [ConRon.Arena.checkShapelessFormers, StateT.run_bind, hrun1, except_ok_bind]
        exact hrun
      · have hne : rdW (m.arr64 EREC) (rdW (m.arr64 EREC) off) ≠ 3 := by
          rw [hkd']; intro h'
          apply h3
          have := congrArg UInt64.toNat h'
          rw [UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; exact hkb)] at this
          simpa using this
        rw [sfW_skip n m vis off cnt hc hne] at h
        obtain ⟨a', hrun, hS', hg'⟩ := ih dn fe vis m0 m m' a (off + 1) (cnt - 1) rest h hg0 hS
          hrestdec (by rw [hoff1, hcnt1]; omega)
        refine ⟨a', ?_, hS', hg'⟩
        cases ci with
        | indInfo cv caps => exact absurd rfl (hkn3 h3 cv caps)
        | _ => simpa [ConRon.Arena.checkShapelessFormers] using hrun


/-- **`check_shapeless_formers` refines `checkShapelessFormers`** (through the stub
`check_constant_val`); the block is an `EREC` slice of constant records that keeps decoding as the
pools grow (`hstab`). -/
@[refines ConRon.Arena.checkShapelessFormers]
theorem checkShapelessFormers_refines (p : Prog)
    (hp : p.lookup "check_shapeless_formers" = some checkShapelessFormers)
    (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
    (vis off cnt : Word) (blk : List IConstantInfo) (hS : StageR dn vis fe s₀.mem a₀)
    (hstab : ∀ m'', IWGrow s₀.mem m'' → decEBlk dn m'' off.toNat cnt.toNat = some blk)
    (hb : off.toNat + cnt.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_shapeless_formers" [vis, off, cnt]
    ⦃fun _ s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.checkShapelessFormers ConLeche.CheckMode.verified fe blk) a₀ ∧
      StageR dn vis fe s'.mem
        (AM.st (ConRon.Arena.checkShapelessFormers ConLeche.CheckMode.verified fe blk) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (checkShapelessFormers_spec p hp n s₀ vis off cnt) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨a', hrun, hS', hg⟩ := sfW_ok n dn fe vis s₀.mem s₀.mem s'.mem a₀ off cnt blk hm
    (IWGrow.refl _) hS hstab hb
  obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg⟩


/-- **`check_shapeless` refines `checkShapeless`**: the twin checks the formers and then always
fails (`notImplemented`); the L function checks them and then aborts, so it never returns. -/
@[refines ConRon.Arena.checkShapeless]
theorem checkShapeless_refines (p : Prog)
    (hf : p.lookup "check_shapeless_formers" = some checkShapelessFormers)
    (hp : p.lookup "check_shapeless" = some checkShapeless) (n : Nat) (s₀ : St)
    (vis off cnt : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_shapeless" [vis, off, cnt]
    ⦃fun _ _ => False; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkShapeless]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        checkShapelessFormers_spec p hf n] <;>
      finish

/-- The twin's `checkShapeless` never returns an environment. -/
theorem checkShapeless_fails (fe : IFEnv) (blk : List IConstantInfo) (a : AState) :
    ∃ e, (ConRon.Arena.checkShapeless ConLeche.CheckMode.verified fe blk).run a = .error e := by
  unfold ConRon.Arena.checkShapeless
  simp only [StateT.run_bind]
  cases h : (ConRon.Arena.checkShapelessFormers ConLeche.CheckMode.verified fe blk).run a with
  | error e => exact ⟨e, rfl⟩
  | ok q => exact ⟨_, rfl⟩

end L.Ind
