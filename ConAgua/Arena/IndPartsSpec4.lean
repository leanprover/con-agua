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

end L.Ind
