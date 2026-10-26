import ConAgua.Arena.WhnfDeltaSlot
import ConAgua.Arena.WhnfCoreApp
import ConAgua.Arena.WhnfCoreProj
import ConAgua.Arena.WriteSets
import ConAgua.Arena.ConstRefine

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

theorem decCV_words {a : Array Word} {q : Nat} {cv : IConstantVal} (h : decCV a q = some cv) :
    (∃ w, a[q]? = some w ∧ w.toNat < 2 ^ 32 ∧ cv.name = decI w) ∧
    (∃ w, a[q + 2]? = some w ∧ cv.levelParams.length = w.toNat) ∧
    (∃ w, a[q + 3]? = some w ∧ w.toNat < 2 ^ 32 ∧ cv.type = decI w) := by
  simp only [decCV, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
  obtain ⟨n, hn, l, hl, t, ht, hc⟩ := h
  cases Option.some.inj hc
  refine ⟨hd?_eq hn, ?_, hd?_eq ht⟩
  simp only [hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hl
  obtain ⟨o, ho, c, hc', hs⟩ := hl
  simp only [nat?, Option.map_eq_some_iff] at hc'
  obtain ⟨w, hw, rfl⟩ := hc'
  exact ⟨w, hw, hslice?_length hs⟩

/-! ## Environment records: the shape lemmas the nat-literal and delta functions read -/

theorem rdW_off {b : Array Word} {q c : Word} {i : Nat} {w : Word} (hb : b[i]? = some w)
    (hi : q.toNat + c.toNat = i) (hsz : b.size < 2 ^ 63) : rdW b (q + c) = w := by
  have hlt : i < b.size := (Array.getElem?_eq_some_iff.mp hb).1
  have : (q + c).toNat = i := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]; omega
  simp only [rdW, this, hb]; rfl

/-- Shape of a record whose `decCV` succeeds at `q + 1`, read at the words `q + 2`, `q + 3`, `q + 4`. -/
theorem decCV_rd {a b : Array Word} {q : Word} {cv : IConstantVal} (hab : ArrExt a b)
    (hsz : b.size < 2 ^ 63) (h : decCV a (q.toNat + 1) = some cv) :
    hslice? b (rdW b (q + 2)).toNat (rdW b (q + 3)).toNat = some cv.levelParams ∧
    cv.levelParams.length = (rdW b (q + 3)).toNat ∧
    cv.type = decI (rdW b (q + 4)) ∧ (rdW b (q + 4)).toNat < 2 ^ 32 := by
  obtain ⟨-, ⟨w3, hw3, hlen⟩, ⟨w4, hw4, hl4, hty⟩⟩ := decCV_words h
  have e3 : rdW b (q + 3) = w3 := rdW_off (hab _ _ hw3) (by simp <;> omega) hsz
  have e4 : rdW b (q + 4) = w4 := rdW_off (hab _ _ hw4) (by simp <;> omega) hsz
  refine ⟨?_, by rw [e3]; exact hlen, by rw [e4]; exact hty, by rw [e4]; exact hl4⟩
  simp only [decCV, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
  obtain ⟨n, hn, l, hl, t, ht, hc⟩ := h
  cases Option.some.inj hc
  simp only [hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hl
  obtain ⟨o, ho, c, hc', hs⟩ := hl
  simp only [nat?, Option.map_eq_some_iff] at ho hc'
  obtain ⟨w2, hw2, rfl⟩ := ho
  obtain ⟨w3', hw3', rfl⟩ := hc'
  have e2 : rdW b (q + 2) = w2 := rdW_off (hab _ _ hw2) (by simp <;> omega) hsz
  have e3' : w3' = w3 := by
    have := hw3'.symm.trans hw3; exact Option.some.inj this
  subst e3'
  rw [e2, e3]
  exact hab.hslice? hs

/-- The kind word of a decoded record, and what each kind decodes to. -/
theorem decCI_split {a b : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Word}
    {ci : IConstantInfo} (h : decCI a dn q.toNat = some ci) (hab : ArrExt a b)
    (hsz : b.size < 2 ^ 63) :
    (rdW b q = 1 → ∃ cv v hint, ci = .defnInfo cv v hint ∧ decCV a (q.toNat + 1) = some cv ∧
      v = decI (rdW b (q + 5)) ∧ (rdW b (q + 5)).toNat < 2 ^ 32) ∧
    (rdW b q ≠ 1 → ∀ cv v hint, ci ≠ .defnInfo cv v hint) ∧
    (rdW b q = 3 → ∃ cv caps, ci = .indInfo cv caps ∧ decCV a (q.toNat + 1) = some cv) ∧
    (rdW b q ≠ 3 → ∀ cv caps, ci ≠ .indInfo cv caps) ∧
    (rdW b q = 4 → ∃ cv np nf, ci = .ctorInfo cv np nf ∧ decCV a (q.toNat + 1) = some cv) ∧
    (rdW b q ≠ 4 → ∀ cv np nf, ci ≠ .ctorInfo cv np nf) := by
  cases hq : a[q.toNat]? with
  | none => simp [decCI, nat?, hq] at h
  | some w =>
  have hqb := hab _ _ hq
  have hrd : rdW b q = w := by simp [rdW, hqb]
  rw [hrd]
  simp only [decCI, nat?, hq, Option.map_some, Option.bind_eq_bind, Option.bind_some] at h
  have hne : ∀ k : Nat, k < 8 → w.toNat = k ∨ w.toNat ≠ k := fun k _ => by omega
  by_cases w1 : w.toNat = 1
  · have wv : w = 1 := UInt64.toNat_inj.mp (by rw [w1]; rfl)
    subst wv
    simp only [show UInt64.toNat 1 = 1 from rfl, Option.bind_eq_some_iff] at h
    obtain ⟨cv, hcv, v, hv, hint, -, hc⟩ := h
    cases hc
    obtain ⟨vw, hvw, hvl, rfl⟩ := hd?_eq hv
    have e5 : rdW b (q + 5) = vw := rdW_off (hab _ _ hvw) (by simp <;> omega) hsz
    refine ⟨fun _ => ⟨cv, _, _, rfl, hcv, by rw [e5], by rw [e5]; exact hvl⟩, fun hn => absurd rfl hn,
      fun h3 => absurd h3 (by decide), fun _ _ _ => by simp, fun h4 => absurd h4 (by decide),
      fun _ _ _ _ => by simp⟩
  by_cases w3 : w.toNat = 3
  · have wv : w = 3 := UInt64.toNat_inj.mp (by rw [w3]; rfl)
    subst wv
    simp only [show UInt64.toNat 3 = 3 from rfl, Option.bind_eq_some_iff] at h
    obtain ⟨cv, hcv, caps, -, hc⟩ := h
    cases hc
    refine ⟨fun h1 => absurd h1 (by decide), fun _ _ _ _ => by simp, fun _ => ⟨cv, _, rfl, hcv⟩,
      fun hn => absurd rfl hn, fun h4 => absurd h4 (by decide), fun _ _ _ _ => by simp⟩
  by_cases w4 : w.toNat = 4
  · have wv : w = 4 := UInt64.toNat_inj.mp (by rw [w4]; rfl)
    subst wv
    simp only [show UInt64.toNat 4 = 4 from rfl, Option.bind_eq_some_iff] at h
    obtain ⟨cv, hcv, np, -, nf, -, hc⟩ := h
    cases hc
    refine ⟨fun h1 => absurd h1 (by decide), fun _ _ _ _ => by simp, fun h3 => absurd h3 (by decide),
      fun _ _ _ => by simp, fun _ => ⟨cv, _, _, rfl, hcv⟩, fun hn => absurd rfl hn⟩
  have n1 : w ≠ 1 := fun e => w1 (by rw [e]; rfl)
  have n3 : w ≠ 3 := fun e => w3 (by rw [e]; rfl)
  have n4 : w ≠ 4 := fun e => w4 (by rw [e]; rfl)
  refine ⟨fun e => absurd e n1, ?_, fun e => absurd e n3, ?_, fun e => absurd e n4, ?_⟩
  · intro _ cv v hint hc; subst hc
    rcases hk : w.toNat with _ | _ | _ | _ | _ | _ | _ | k
    all_goals (rw [hk] at h w1 w3 w4; simp [Option.bind_eq_some_iff] at h w1 w3 w4)
  · intro _ cv v hc; subst hc
    rcases hk : w.toNat with _ | _ | _ | _ | _ | _ | _ | k
    all_goals (rw [hk] at h w1 w3 w4; simp [Option.bind_eq_some_iff] at h w1 w3 w4)
  · intro _ cv v n hc; subst hc
    rcases hk : w.toNat with _ | _ | _ | _ | _ | _ | _ | k
    all_goals (rw [hk] at h w1 w3 w4; simp [Option.bind_eq_some_iff] at h w1 w3 w4)

/-! ## Calls of the leaf readers, as facts about their runs -/

theorem pinAt_word_spec (p : Prog) (hp : p.lookup "pin_at" = some pinAtL) (n : Nat) (s₀ : St)
    (i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "pin_at" [i]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ pinW s₀.mem 0 ≠ 0 ∧ i.toNat < 51 ∧
      r.headD 0 = pinW s₀.mem (1 + i.toNat); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, pinAtL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;> finish [pinW_eq]

theorem pinWord_word_spec (p : Prog) (hp : p.lookup "pin_word" = some pinWordL) (n : Nat) (s₀ : St)
    (k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "pin_word" [k]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ pinW s₀.mem 0 ≠ 0 ∧
      r.headD 0 = pinW s₀.mem k.toNat; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, pinWordL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;> finish [pinW_eq]

theorem callW_pinAt (p : Prog) (hp : p.lookup "pin_at" = some pinAtL) (n : Nat) (m : Mem)
    (i : Word) (r : List Word) (m' : Mem) (h : callW p n "pin_at" [i] m = some (r, m')) :
    m' = m ∧ pinW m 0 ≠ 0 ∧ i.toNat < 51 ∧ r.headD 0 = pinW m (1 + i.toNat) := by
  obtain ⟨s', hs', hmem, -, h0, h1, h2⟩ :=
    triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (pinAt_word_spec p hp n _ i) h
  exact ⟨hs'.symm.trans hmem, h0, h1, h2⟩

theorem callW_pinWord (p : Prog) (hp : p.lookup "pin_word" = some pinWordL) (n : Nat) (m : Mem)
    (k : Word) (r : List Word) (m' : Mem) (h : callW p n "pin_word" [k] m = some (r, m')) :
    m' = m ∧ pinW m 0 ≠ 0 ∧ r.headD 0 = pinW m k.toNat := by
  obtain ⟨s', hs', hmem, -, h0, h2⟩ :=
    triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (pinWord_word_spec p hp n _ k) h
  exact ⟨hs'.symm.trans hmem, h0, h2⟩

/-! ## `CoreS` across a `const` interning -/

theorem keeps_cpl_internConst (n : NIdx) (us : LsIdx) : Keeps cpl (internE (.const n us)) := by
  simp only [internE]; exact keeps_cpl_internNodeE _

theorem keeps_cpl_internLit (l : ConLeche.Literal) : Keeps cpl (internE (.lit l)) := by
  simp only [internE]; exact keeps_cpl_internNodeE _

theorem CoreS.of_const {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState}
    {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb)
    (hD : ArenaD m' a') (hcpl : cpl a' = cpl a) (hf : MemFrame [CREC, CREC + 256, CSLOT, CSLOT + 256, CLP, CLP + 256] [18, 19] m m')
    {n : NIdx} {us : LsIdx} {r : EIdx} (hrun : (internE (.const n us)).run a = .ok (r, a'))
    (hus : ∃ ls, denoteLs a.store.lss us = some ls) :
    CoreS dn m' a' vis fe M eb :=
  hS.arena_frameD hD hcpl hf
    (fun b hb => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by simp [CREC, CSLOT, CLP, PINS])
    (fun b hb => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (fun x hx => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl <;> decide)
    (fun x hx => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl <;> decide)
    (hS.den.of_internConst hus hrun (hf.1 EREC (by simp [CREC, CSLOT, CLP, EREC]) (by decide)))
    (hmode := hS.mode.frame hf (by decide) (by decide))

theorem StackKept.of_const_frame {m m' : Mem} (hf : MemFrame [CREC, CREC + 256, CSLOT, CSLOT + 256, CLP, CLP + 256] [18, 19] m m') :
    StackKept m m' := by
  have hspn : m'.arr64 SPN = m.arr64 SPN :=
    hf.1 SPN (by simp [CREC, CSLOT, CLP, SPN]) (by decide)
  have h136 : rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 := hf.2.1 136 (by simp)
  exact StackKept.of_frame hf

/-- **An interned `const` handle word is below `2^32`.** -/
theorem ceinternW_hw (m : Mem) (a : AState) (hR : ConstR m a) (f x : Word) (hf : f.toNat < 2 ^ 32)
    (hx : x.toNat < 2 ^ 32) (w : Word) (m' : Mem) (hI : ceinternW m f x = some (w, m')) :
    w.toNat < 2 ^ 32 := by
  exact consInternM_lt constCS_wf hR hI

section progs
variable (p : Prog)

/-- **`intern_const` as a run.** -/
theorem callW_internConst (hpf : p.lookup "const_find" = some constFind)
    (hpp : p.lookup "const_push" = some constPush) (hp : p.lookup "intern_const" = some internConst)
    (n : Nat) (s₀ : St) (a₀ : AState) (hD : ArenaD s₀.mem a₀) (f x : Word) (hf : HW f) (hx : HW x)
    (r : List Word) (m' : Mem) (h : callW p n "intern_const" [f, x] s₀.mem = some (r, m')) :
    AM.ok (internE (.const (decI f) (decI x))) a₀ ∧
    ArenaD m' (AM.st (internE (.const (decI f) (decI x))) a₀) ∧
    AM.res (internE (.const (decI f) (decI x))) a₀ = decI (r.headD 0) ∧
    MemFrame [CREC, CREC + 256, CSLOT, CSLOT + 256, CLP, CLP + 256] [18, 19] s₀.mem m' ∧ HW (r.headD 0) := by
  obtain ⟨s', rfl, hm⟩ := triple_of_callW (internConst_spec p hpf hpp hp n s₀ f x) h
  obtain ⟨-, hm⟩ := hm
  obtain ⟨h1, h2, h3⟩ := internConst_D s₀.mem a₀ hD f x _ hf hx _ hm
  refine ⟨h1, h2, h3, ?_, ceinternW_hw s₀.mem a₀ ?_ f x hf hx _ _ hm⟩
  · exact ceinternW_frame (hI := hm)
  · exact hD.1.const

end progs

/-! ## The `Nat` functions' write set -/

/-- The `Nat` arms' program, with `nat_succ_lit`. -/
def natArmProg' : Prog := natArmProg ++ [("nat_succ_lit", natSuccLitL)]
def natFns : List FnName := natArmProg'.map (·.1)
/-- What they write: the pool, the `lit` table (2, 3), the `const` table (18, 19 = `CREC`, `CSLOT`,
and its `lp` column `CLP`), and the counts. -/
def natA : List ArrId := [POOL, POOL1, 2, 258, 3, 259, CREC, CREC + 256, CSLOT, CSLOT + 256, CLP, CLP + 256]
def natC : List Word := [0, 2, 3, 18, 19]
theorem natArmProg'_closed : closedA natArmProg' natA natC natFns = true := by decide +kernel

theorem WhnfDeltaProg'.natClosed_of_agree {p : Prog}
    (h : ∀ f ∈ natFns, p.lookup f = natArmProg'.lookup f) : closedA p natA natC natFns = true :=
  closedW_of_agree natArmProg'_closed h

/-! ## The program hypotheses -/

/-- `WhnfDeltaProg` plus the functions the callees' own specs need (the `mk_app`/`get_app_*` family
of `SpineProg`, the `const` and `lit` interning, the memo and pool functions). -/
structure WhnfDeltaProg' (p : Prog) : Prop extends WhnfDeltaProg p where
  spine : SpineProg p
  constFind' : p.lookup "const_find" = some constFind
  constPush' : p.lookup "const_push" = some constPush
  envIx' : p.lookup "env_ix" = some envIxL
  envRow' : p.lookup "env_row_get" = some envRowGetL
  predLit : p.lookup "nat_pred_lit" = some natPredLit
  natLimb' : p.lookup "nat_limb" = some natLimb
  subBorrow' : p.lookup "sub_borrow" = some subBorrow
  natTrim' : p.lookup "nat_trim" = some natTrim
  addCarry' : p.lookup "add_carry" = some addCarry
  natAdd' : p.lookup "nat_add" = some natAdd
  litHash' : p.lookup "lit_hash" = some litHash
  limbsEq' : p.lookup "limbs_eq" = some limbsEq
  litMatch' : p.lookup "lit_match" = some litMatch
  litFind' : p.lookup "lit_find" = some litFind
  litPush' : p.lookup "lit_push" = some litPush
  /-- `p` agrees with `natArmProg'` on the `Nat` functions (`natFns`): their write set
  (`natClosed`) and `nat_op_result`'s refinement (`CoreNatOp.lean`) carry over. -/
  natAgree : ∀ f ∈ natFns, p.lookup f = natArmProg'.lookup f

/-- The write set of the `Nat` functions (`natFns`): the pool, the `lit` and `const` tables. -/
theorem WhnfDeltaProg'.natClosed {p : Prog} (hp : WhnfDeltaProg' p) :
    closedA p natA natC natFns = true :=
  WhnfDeltaProg'.natClosed_of_agree hp.natAgree

theorem CoreSpec.zero {α : Type} [Inhabited α] {p : Prog} {f : FnName} {fd : FunDecl}
    (hf : p.lookup f = some fd) (args : List Word) (T : AM α) (dec : List Word → α) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb : Word) (ok : List Word → Prop) :
    CoreSpec p 0 f args T dec s₀ a₀ dn vis fe MM eb ok := by
  unfold CoreSpec
  rw [invoke_eq _ hf]
  simp only [callFn]
  vcgen [exec] <;> grind

/-! ## `const_e` -/

/-- The model of `const_e`. -/
def constEW (p : Prog) (n : Nat) (m : Mem) (nm : Word) : Option (Word × Mem) :=
  match callW p n "pin_word" [52] m with
  | none => none
  | some (r₁, m₁) =>
    match callW p n "intern_const" [nm, r₁.headD 0] m₁ with
    | none => none
    | some (r₂, m₂) => some (r₂.headD 0, m₂)

theorem constE_spec (p : Prog) (hp : p.lookup "const_e" = some constEL) (n : Nat) (s₀ : St)
    (nm : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "const_e" [nm]
    ⦃fun r s' => LocEq s' s₀ ∧ constEW p n s₀.mem nm = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, constEL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "pin_word", callW_spec p n "intern_const"] <;>
    finish [constEW]

theorem constE_run {m : Mem} {a : AState} (h : PinsFull m a.pins) (n : NIdx) :
    (constE n).run a = (internE (.const n (decI (pinW m 52)))).run a := by
  simp only [constE, emptyLevels, StateT.run_bind, pinEmptyLevels_run h]; rfl

/-- **A refinement spec from the calls' runs**: the callee's run (`callW`) and the post. -/
theorem CoreSpec.of_call {α : Type} [Inhabited α] {p : Prog} {n : Nat} {f : FnName}
    {args : List Word} {T : AM α} {dec : List Word → α} {s₀ : St} {a₀ : AState}
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word}
    {ok : List Word → Prop}
    (h : ∀ (r : List Word) (m' : Mem), callW p n f args s₀.mem = some (r, m') →
      CoreRef T a₀ dec dn s₀.mem vis fe M eb r m' ok) :
    CoreSpec p n f args T dec s₀ a₀ dn vis fe M eb ok := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hc⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun (callW_spec p n f args s₀)
  subst hs0
  exact ⟨hloc, h r s'.mem hc⟩

section refs
variable (p : Prog)

/-- **`const_e` as a run**: the twin's interning, the relation after it (same maps), only the
`const` tables written, and the result a handle word. -/
theorem callW_constE (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb nm : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (hnm : HW nm) (r : List Word) (m' : Mem)
    (h : callW p n "const_e" [nm] s₀.mem = some (r, m')) :
    AM.ok (constE (decI nm)) a₀ ∧ CoreS dn m' (AM.st (constE (decI nm)) a₀) vis fe MM eb ∧
    AM.res (constE (decI nm)) a₀ = decH r ∧ MemFrame [CREC, CREC + 256, CSLOT, CSLOT + 256, CLP, CLP + 256] [18, 19] s₀.mem m' ∧
    HW (r.headD 0) := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (constE_spec p hp.constE n s₀ nm) h
  cases h1 : callW p n "pin_word" [52] s₀.mem with
  | none => simp only [constEW, h1] at hW; cases hW
  | some q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  obtain ⟨rfl, -, hr₁⟩ := callW_pinWord p hp.pinWord n s₀.mem 52 r₁ m₁ h1
  simp only [show (52 : Word).toNat = 52 from rfl] at hr₁
  cases h2 : callW p n "intern_const" [nm, r₁.headD 0] s₀.mem with
  | none => simp only [constEW, h1, h2] at hW; cases hW
  | some q₂ =>
  obtain ⟨r₂, m₂⟩ := q₂
  simp only [constEW, h1, h2, Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hm⟩ := hW
  have hpw : HW (r₁.headD 0) := by rw [hr₁]; exact hC.pins.lv_lt.1
  obtain ⟨hok, hD', hres, hfr, hhw⟩ := callW_internConst p hp.constFind' hp.constPush' hp.internConst n
    s₀ a₀ hC.arena nm _ hnm hpw r₂ m₂ h2
  have hrun := constE_run hC.pins (decI nm)
  rw [← hr₁] at hrun
  obtain ⟨hok', hst', hres'⟩ := AM.congr_run hrun
  rw [← hm]
  refine ⟨by rw [hok']; exact hok, ?_, ?_, hfr, by rw [← hr]; exact hhw⟩
  · rw [hst']
    exact hC.of_const hD' (Keeps.run (keeps_cpl_internConst _ _) (AM.run_of_ok _ _ hok)) hfr
      (AM.run_of_ok _ _ hok) (by rw [hr₁, ← hC.pins.emptyLevels]; exact hC.den.emptyLs)
  · rw [hres', hres, decH, ← hr]; rfl

/-- **`const_e` refines `constE`.** `WhnfDeltaProg'` for the extra function lookups. -/
@[refines ConRon.Arena.constE]
theorem constE_refines (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb nm : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (hnm : HW nm) :
    CoreSpec p n "const_e" [nm] (constE (decI nm)) decH s₀ a₀ dn vis fe MM eb := by
  apply CoreSpec.of_call
  intro r m' h
  obtain ⟨hok, hS, hres, hfr, hhw⟩ := callW_constE p hp n s₀ a₀ dn vis fe MM eb nm hC hnm r m' h
  exact ⟨hok, ⟨MM, hS, KeptAll.refl _ _, StackKept.of_const_frame hfr⟩, hres, hhw⟩

end refs

/-! ## `nat_ind_ok`, `nat_zero_ok`, `nat_succ_ok` -/

/-- The model of `nat_ind_ok`. -/
def natIndOkW (p : Prog) (n : Nat) (m : Mem) (found q : Word) : Option (Word × Mem) :=
  if found = 0 then some (0, m)
  else if rdW (m.arr64 EREC) q ≠ 3 then some (0, m)
  else if rdW (m.arr64 EREC) (q + 3) ≠ 0 then some (0, m)
  else match callW p n "pin_word" [54] m with
    | none => none
    | some (r₁, m₁) => some (if rdW (m₁.arr64 EREC) (q + 4) = r₁.headD 0 then 1 else 0, m₁)

theorem natIndOk_spec (p : Prog) (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St) (found q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nat_ind_ok" [found, q]
    ⦃fun r s' => LocEq s' s₀ ∧ natIndOkW p n s₀.mem found q = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.natIndOk]
  simp only [callFn, natIndOkL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "pin_word"] <;>
    finish [natIndOkW]

/-- **A call that may only intern `const` nodes**: the twin's run succeeds, the relation holds
after it at the same maps, the result words decode to the twin's result, and the memory moved only in
the `const` tables. -/
def CRef {α : Type} [Inhabited α] (T : AM α) (a₀ : AState) (dec : List Word → α)
    (dn : NIdx → Option ConLeche.Name) (m₀ : Mem) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb : Word) (r : List Word) (m' : Mem) (ok : List Word → Prop) : Prop :=
  AM.ok T a₀ ∧ CoreS dn m' (AM.st T a₀) vis fe M eb ∧ AM.res T a₀ = dec r ∧
    MemFrame [CREC, CREC + 256, CSLOT, CSLOT + 256, CLP, CLP + 256] [18, 19] m₀ m' ∧ ok r

theorem CRef.pure {α : Type} [Inhabited α] {T : AM α} {a₀ : AState} {dec : List Word → α}
    {dn : NIdx → Option ConLeche.Name} {m : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {r : List Word} {ok : List Word → Prop}
    (hC : CoreS dn m a₀ vis fe M eb) (b : α) (hrun : T.run a₀ = .ok (b, a₀)) (hres : dec r = b)
    (hok : ok r) : CRef T a₀ dec dn m vis fe M eb r m ok := by
  obtain ⟨h1, h2, h3⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨h1, by rw [h2]; exact hC, by rw [h3, hres], MemFrame.refl _ _ _, hok⟩

theorem CRef.core {α : Type} [Inhabited α] {T : AM α} {a₀ : AState} {dec : List Word → α}
    {dn : NIdx → Option ConLeche.Name} {m₀ m' : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {r : List Word} {ok : List Word → Prop}
    (h : CRef T a₀ dec dn m₀ vis fe M eb r m' ok) : CoreRef T a₀ dec dn m₀ vis fe M eb r m' ok :=
  ⟨h.1, ⟨M, h.2.1, KeptAll.refl _ _, StackKept.of_const_frame h.2.2.2.1⟩, h.2.2.1, h.2.2.2.2⟩

theorem CoreSpec.of_callC {α : Type} [Inhabited α] {p : Prog} {n : Nat} {f : FnName}
    {args : List Word} {T : AM α} {dec : List Word → α} {s₀ : St} {a₀ : AState}
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word}
    {ok : List Word → Prop}
    (h : ∀ (r : List Word) (m' : Mem), callW p n f args s₀.mem = some (r, m') →
      CRef T a₀ dec dn s₀.mem vis fe M eb r m' ok) :
    CoreSpec p n f args T dec s₀ a₀ dn vis fe M eb ok :=
  CoreSpec.of_call fun r m' hc => (h r m' hc).core

theorem ResH_ite (P : Prop) [Decidable P] : ResH [if P then 1 else 0] := by
  unfold ResH HW; by_cases h : P <;> simp [h]

theorem decBool_ite' (P : Prop) [Decidable P] : decBool [if P then 1 else 0] = decide P := by
  by_cases h : P <;> simp [h, decBool]

theorem natIndOk_run_none (a : AState) : (natIndOk none).run a = .ok (false, a) := rfl

theorem natIndOk_run_other {ci : IConstantInfo} (h : ∀ cv caps, ci ≠ .indInfo cv caps) (a : AState) :
    (natIndOk (some ci)).run a = .ok (false, a) := by
  cases ci with
  | indInfo cv caps => exact absurd rfl (h cv caps)
  | _ => rfl

theorem natIndOk_run_ind {m : Mem} {a : AState} (hP : PinsFull m a.pins) (cv : IConstantVal)
    (caps : IIndCaps) :
    (natIndOk (some (.indInfo cv caps))).run a =
      .ok (cv.levelParams.isEmpty && cv.type == decI (pinW m 54), a) := by
  simp only [natIndOk, sortOne, StateT.run_bind, pinSortOne_run hP]; rfl

section refs2
variable (p : Prog)

theorem callW_natIndOk (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb found q : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb)
    (hdec : found ≠ 0 → ∃ ci, decCI (erecP s₀.mem) dn q.toNat = some ci)
    (r : List Word) (m' : Mem) (h : callW p n "nat_ind_ok" [found, q] s₀.mem = some (r, m')) :
    CRef (natIndOk (decFound dn s₀.mem found q)) a₀ decBool dn s₀.mem vis fe MM eb r m' ResH := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (natIndOk_spec p hp n s₀ found q) h
  by_cases hf : found = 0
  · unfold natIndOkW at hW
    rw [if_pos hf] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    rw [← hm]
    refine CRef.pure hC false ?_ ?_ ?_
    · simp only [decFound, hf, ↓reduceIte]; exact natIndOk_run_none _
    · simp only [decBool, ← hr]; rfl
    · unfold ResH HW; rw [← hr]; decide
  obtain ⟨ci, hci⟩ := hdec hf
  have hdf : decFound dn s₀.mem found q = some ci := by simp only [decFound, hf, ↓reduceIte, hci]
  rw [hdf]
  have hsp := decCI_split hci (erecP_ext _) hC.erec
  obtain ⟨-, -, hind, hnind, -, -⟩ := hsp
  unfold natIndOkW at hW
  rw [if_neg hf] at hW
  by_cases hk3 : rdW (s₀.mem.arr64 EREC) q ≠ 3
  · rw [if_pos hk3] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    rw [← hm]
    refine CRef.pure hC false (natIndOk_run_other (hnind hk3) _) ?_ ?_
    · simp only [decBool, ← hr]; rfl
    · unfold ResH HW; rw [← hr]; decide
  obtain ⟨cv, caps, rfl, hcv⟩ := hind (by simpa using hk3)
  obtain ⟨-, hlen, hty, htyl⟩ := decCV_rd (erecP_ext s₀.mem) hC.erec hcv
  rw [if_neg hk3] at hW
  by_cases hk4 : rdW (s₀.mem.arr64 EREC) (q + 3) ≠ 0
  · rw [if_pos hk4] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    rw [← hm]
    refine CRef.pure hC false ?_ ?_ ?_
    · rw [natIndOk_run_ind hC.pins]
      have : cv.levelParams.isEmpty = false := by
        rcases hl : cv.levelParams with _ | ⟨x, xs⟩
        · exfalso; rw [hl] at hlen; exact hk4 (UInt64.toNat_inj.mp (by simpa using hlen.symm))
        · rfl
      rw [this]; rfl
    · simp only [decBool, ← hr]; rfl
    · unfold ResH HW; rw [← hr]; decide
  rw [if_neg hk4] at hW
  have hk4' : rdW (s₀.mem.arr64 EREC) (q + 3) = 0 := by simpa using hk4
  rcases h1 : callW p n "pin_word" [54] s₀.mem with _ | ⟨r₁, m₁⟩
    <;> simp only [h1, reduceCtorEq] at hW
  obtain ⟨rfl, -, hr₁⟩ := callW_pinWord p hp.pinWord n s₀.mem 54 r₁ m₁ h1
  simp only [show (54 : Word).toNat = 54 from rfl] at hr₁
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hm⟩ := hW
  rw [← hm]
  have hb : (cv.levelParams.isEmpty && cv.type == decI (pinW s₀.mem 54)) =
      decide (rdW (s₀.mem.arr64 EREC) (q + 4) = r₁.headD 0) := by
    have hl0 : cv.levelParams.isEmpty = true := by
      simp only [List.isEmpty_iff, ← List.length_eq_zero_iff]; rw [hlen, hk4']; rfl
    rw [hl0, hty, hr₁, decI_beq _ _ htyl hC.pins.lv_lt.2.2]
    simp [hr₁]
  refine CRef.pure hC _ (by rw [natIndOk_run_ind hC.pins]) ?_ ?_
  · show decBool [r.headD 0] = _
    rw [← hr, hb]; exact decBool_ite' _
  · show ResH [r.headD 0]
    rw [← hr]; exact ResH_ite _

@[refines ConRon.Arena.natIndOk]
theorem natIndOk_refines (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb found q : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (hq : HW q)
    (hdec : found ≠ 0 → ∃ ci, decCI (erecP s₀.mem) dn q.toNat = some ci) :
    CoreSpec p n "nat_ind_ok" [found, q] (natIndOk (decFound dn s₀.mem found q)) decBool s₀ a₀ dn
      vis fe MM eb :=
  CoreSpec.of_callC fun r m' h => callW_natIndOk p hp n s₀ a₀ dn vis fe MM eb found q hC hdec r m' h

end refs2

/-! ## `nat_zero_ok` -/

/-- The model of `nat_zero_ok`. -/
def natZeroOkW (p : Prog) (n : Nat) (m : Mem) (found q : Word) : Option (Word × Mem) :=
  if found = 0 then some (0, m)
  else if rdW (m.arr64 EREC) q ≠ 4 then some (0, m)
  else match callW p n "pin_at" [1] m with
    | none => none
    | some (r₁, m₁) =>
      match callW p n "const_e" [r₁.headD 0] m₁ with
      | none => none
      | some (r₂, m₂) =>
        if rdW (m₂.arr64 EREC) (q + 3) ≠ 0 then some (0, m₂)
        else some (if rdW (m₂.arr64 EREC) (q + 4) = r₂.headD 0 then 1 else 0, m₂)

theorem natZeroOk_spec (p : Prog) (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St) (found q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nat_zero_ok" [found, q]
    ⦃fun r s' => LocEq s' s₀ ∧ natZeroOkW p n s₀.mem found q = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.natZeroOk]
  simp only [callFn, natZeroOkL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "pin_at", callW_spec p n "const_e"] <;>
    finish [natZeroOkW]

theorem pinNat_run {m : Mem} {a : AState} (h : PinsFull m a.pins) :
    pinNat.run a = .ok (decI (pinW m 2), a) := pinAt_run h 1 (by decide)

theorem natZeroOk_run_none (a : AState) : (natZeroOk none).run a = .ok (false, a) := rfl

theorem natZeroOk_run_other {ci : IConstantInfo} (h : ∀ cv np nf, ci ≠ .ctorInfo cv np nf)
    (a : AState) : (natZeroOk (some ci)).run a = .ok (false, a) := by
  cases ci with
  | ctorInfo cv np nf => exact absurd rfl (h cv np nf)
  | _ => rfl

theorem natZeroOk_run_ctor {m : Mem} {a a₁ : AState} (hP : PinsFull m a.pins) (cv : IConstantVal)
    (np nf : Nat) (nc : EIdx) (h : (constE (decI (pinW m 2))).run a = .ok (nc, a₁)) :
    (natZeroOk (some (.ctorInfo cv np nf))).run a =
      .ok (cv.levelParams.isEmpty && cv.type == nc, a₁) := by
  simp only [natZeroOk, StateT.run_bind, pinNat_run hP, except_ok_bind, h]; rfl

theorem MemFrame.arr_eq {A : List ArrId} {C : List Word} {m m' : Mem} (hf : MemFrame A C m m')
    (b : ArrId) (hb : b ∉ A) (hc : b ≠ CTL) : m'.arr64 b = m.arr64 b := hf.1 b hb hc

section refs3
variable (p : Prog)

theorem callW_natZeroOk (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb found q : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb)
    (hdec : found ≠ 0 → ∃ ci, decCI (erecP s₀.mem) dn q.toNat = some ci)
    (r : List Word) (m' : Mem) (h : callW p n "nat_zero_ok" [found, q] s₀.mem = some (r, m')) :
    CRef (natZeroOk (decFound dn s₀.mem found q)) a₀ decBool dn s₀.mem vis fe MM eb r m' ResH := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (natZeroOk_spec p hp.toWhnfDeltaProg n s₀ found q) h
  by_cases hf : found = 0
  · unfold natZeroOkW at hW
    rw [if_pos hf] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    rw [← hm]
    refine CRef.pure hC false ?_ ?_ ?_
    · simp only [decFound, hf, ↓reduceIte]; exact natZeroOk_run_none _
    · simp only [decBool, ← hr]; rfl
    · unfold ResH HW; rw [← hr]; decide
  obtain ⟨ci, hci⟩ := hdec hf
  have hdf : decFound dn s₀.mem found q = some ci := by simp only [decFound, hf, ↓reduceIte, hci]
  rw [hdf]
  obtain ⟨-, -, -, -, hctor, hnctor⟩ := decCI_split hci (erecP_ext _) hC.erec
  unfold natZeroOkW at hW
  rw [if_neg hf] at hW
  by_cases hk4 : rdW (s₀.mem.arr64 EREC) q ≠ 4
  · rw [if_pos hk4] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    rw [← hm]
    refine CRef.pure hC false (natZeroOk_run_other (hnctor hk4) _) ?_ ?_
    · simp only [decBool, ← hr]; rfl
    · unfold ResH HW; rw [← hr]; decide
  rw [if_neg hk4] at hW
  obtain ⟨cv, np, nf, rfl, hcv⟩ := hctor (by simpa using hk4)
  obtain ⟨-, hlen, hty, htyl⟩ := decCV_rd (erecP_ext s₀.mem) hC.erec hcv
  cases h1 : callW p n "pin_at" [1] s₀.mem with
  | none => rw [h1] at hW; cases hW
  | some q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  rw [h1] at hW
  obtain ⟨rfl, -, -, hr₁⟩ := callW_pinAt p hp.pinAt n s₀.mem 1 r₁ m₁ h1
  simp only [show (1 : Word).toNat = 1 from rfl] at hr₁
  dsimp only at hW
  have hnt : HW (r₁.headD 0) := by
    rw [hr₁]; exact hC.pins.names_lt 1 (by decide)
  cases h2 : callW p n "const_e" [r₁.headD 0] s₀.mem with
  | none => rw [h2] at hW; cases hW
  | some q₂ =>
  obtain ⟨r₂, m₂⟩ := q₂
  rw [h2] at hW
  obtain ⟨hok, hS, hres, hfr, hhw⟩ := callW_constE p hp n s₀ a₀ dn vis fe MM eb _ hC hnt r₂ m₂ h2
  dsimp only at hW
  have hr₁' : r₁.headD 0 = pinW s₀.mem 2 := hr₁
  rw [hr₁'] at hok hS hres
  have hE : m₂.arr64 EREC = s₀.mem.arr64 EREC := hfr.arr_eq EREC (by simp [CREC, CSLOT, CLP, EREC]) (by decide)
  have hrun := AM.run_of_ok _ _ hok
  have hrun' : (constE (decI (pinW s₀.mem 2))).run a₀ =
      .ok (decE (r₂.headD 0), AM.st (constE (decI (pinW s₀.mem 2))) a₀) := by
    rw [hrun, hres]; rfl
  have hz := natZeroOk_run_ctor hC.pins cv np nf _ hrun'
  obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
  by_cases hk3 : rdW (m₂.arr64 EREC) (q + 3) ≠ 0
  · rw [if_pos hk3] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    rw [← hm]
    refine ⟨hok', by rw [hst']; exact hS, ?_, hfr, ?_⟩
    · rw [hres']
      have : cv.levelParams.isEmpty = false := by
        rcases hl : cv.levelParams with _ | ⟨x, xs⟩
        · exfalso; rw [hl] at hlen; rw [hE] at hk3; exact hk3 (UInt64.toNat_inj.mp (by simpa using hlen.symm))
        · rfl
      rw [this]; simp only [decBool, ← hr]; rfl
    · unfold ResH HW; rw [← hr]; decide
  rw [if_neg hk3] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hm⟩ := hW
  rw [← hm]
  have hk3' : rdW (s₀.mem.arr64 EREC) (q + 3) = 0 := by rw [← hE]; simpa using hk3
  refine ⟨hok', by rw [hst']; exact hS, ?_, hfr, ?_⟩
  · rw [hres']
    have hl0 : cv.levelParams.isEmpty = true := by
      simp only [List.isEmpty_iff, ← List.length_eq_zero_iff]; rw [hlen, hk3']; rfl
    rw [hl0, hty]
    show _ = decBool [r.headD 0]
    rw [← hr, hE]
    show (true && (decI (rdW (s₀.mem.arr64 EREC) (q + 4)) == decI (r₂.headD 0))) = _
    rw [decI_beq _ _ htyl hhw]
    simp [decBool_ite']
  · show ResH [r.headD 0]
    rw [← hr]; exact ResH_ite _

@[refines ConRon.Arena.natZeroOk]
theorem natZeroOk_refines (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb found q : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (hq : HW q)
    (hdec : found ≠ 0 → ∃ ci, decCI (erecP s₀.mem) dn q.toNat = some ci) :
    CoreSpec p n "nat_zero_ok" [found, q] (natZeroOk (decFound dn s₀.mem found q)) decBool s₀ a₀ dn
      vis fe MM eb :=
  CoreSpec.of_callC fun r m' h => callW_natZeroOk p hp n s₀ a₀ dn vis fe MM eb found q hC hdec r m' h

end refs3

/-! ## `nat_succ_ok` -/

/-- The model of `nat_succ_ok`. -/
def natSuccOkW (p : Prog) (n : Nat) (m : Mem) (found q : Word) : Option (Word × Mem) :=
  if found = 0 then some (0, m)
  else if rdW (m.arr64 EREC) q ≠ 4 then some (0, m)
  else if rdW (m.arr64 EREC) (q + 3) ≠ 0 then some (0, m)
  else match callW p n "pin_at" [1] m with
    | none => none
    | some (r₁, m₁) =>
      match callW p n "const_e" [r₁.headD 0] m₁ with
      | none => none
      | some (r₂, m₂) =>
        if rdW (m₂.arr64 EREC) (q + 4) >>> 28 ≠ 6 then some (0, m₂)
        else if tierW (rdW (m₂.arr64 EREC) (q + 4)) ≠ 0 ∧ rdW (m₂.arr64 CTL) 1 = 0 then none
        else if tcnt m₂ FORALL (tierW (rdW (m₂.arr64 EREC) (q + 4))) ≤
            idxW (rdW (m₂.arr64 EREC) (q + 4)) then none
        else some (if tfld m₂ FORALL (tierW (rdW (m₂.arr64 EREC) (q + 4))) (idxW (rdW (m₂.arr64 EREC) (q + 4))) 0 = r₂.headD 0 ∧
            tfld m₂ FORALL (tierW (rdW (m₂.arr64 EREC) (q + 4))) (idxW (rdW (m₂.arr64 EREC) (q + 4))) 1 = r₂.headD 0 then 1 else 0, m₂)

theorem natSuccOk_spec (p : Prog) (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St) (found q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nat_succ_ok" [found, q]
    ⦃fun r s' => LocEq s' s₀ ∧ natSuccOkW p n s₀.mem found q = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.natSuccOk]
  simp only [callFn, natSuccOkL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt,
      tcntM, evalE_tierE, evalE_idxE,
      callW_spec p n "pin_at", callW_spec p n "const_e"] <;>
    finish [natSuccOkW, tierW, idxW]

theorem natSuccOk_run_none (a : AState) : (natSuccOk none).run a = .ok (false, a) := rfl

theorem natSuccOk_run_other {ci : IConstantInfo} (h : ∀ cv np nf, ci ≠ .ctorInfo cv np nf)
    (a : AState) : (natSuccOk (some ci)).run a = .ok (false, a) := by
  cases ci with
  | ctorInfo cv np nf => exact absurd rfl (h cv np nf)
  | _ => rfl

theorem natSuccOk_run_lps (a : AState) (cv : IConstantVal) (np nf : Nat)
    (h : cv.levelParams.isEmpty = false) :
    (natSuccOk (some (.ctorInfo cv np nf))).run a = .ok (false, a) := by
  simp only [natSuccOk, h]; rfl

theorem natSuccOk_run_nonforall {m : Mem} {a a₁ : AState} (hP : PinsFull m a.pins)
    (cv : IConstantVal) (np nf : Nat) (nc : EIdx) (hl : cv.levelParams.isEmpty = true)
    (h : (constE (decI (pinW m 2))).run a = .ok (nc, a₁))
    (ht : (cv.type.tag == ETag.forallE) = false) :
    (natSuccOk (some (.ctorInfo cv np nf))).run a = .ok (false, a₁) := by
  simp only [natSuccOk, hl, StateT.run_bind, pinNat_run hP, except_ok_bind, h, ht, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte, ite_false]; rfl

theorem natSuccOk_run_forall {m : Mem} {a a₁ : AState} (hP : PinsFull m a.pins)
    (cv : IConstantVal) (np nf : Nat) (nc dom body : EIdx) (hl : cv.levelParams.isEmpty = true)
    (h : (constE (decI (pinW m 2))).run a = .ok (nc, a₁))
    (ht : (cv.type.tag == ETag.forallE) = true) (hv : a₁.store.view cv.type = some (.forallE dom body)) :
    (natSuccOk (some (.ctorInfo cv np nf))).run a = .ok (dom == nc && body == nc, a₁) := by
  simp only [natSuccOk, hl, StateT.run_bind, pinNat_run hP, except_ok_bind, h, ht,
    view_run _ _ _ hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ite_false, ite_true]; rfl

section refs4
variable (p : Prog)

theorem callW_natSuccOk (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb found q : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb)
    (hdec : found ≠ 0 → ∃ ci, decCI (erecP s₀.mem) dn q.toNat = some ci)
    (r : List Word) (m' : Mem) (h : callW p n "nat_succ_ok" [found, q] s₀.mem = some (r, m')) :
    CRef (natSuccOk (decFound dn s₀.mem found q)) a₀ decBool dn s₀.mem vis fe MM eb r m' ResH := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (natSuccOk_spec p hp.toWhnfDeltaProg n s₀ found q) h
  by_cases hf : found = 0
  · unfold natSuccOkW at hW
    rw [if_pos hf] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    rw [← hm]
    refine CRef.pure hC false ?_ ?_ ?_
    · simp only [decFound, hf, ↓reduceIte]; exact natSuccOk_run_none _
    · simp only [decBool, ← hr]; rfl
    · unfold ResH HW; rw [← hr]; decide
  obtain ⟨ci, hci⟩ := hdec hf
  have hdf : decFound dn s₀.mem found q = some ci := by simp only [decFound, hf, ↓reduceIte, hci]
  rw [hdf]
  obtain ⟨-, -, -, -, hctor, hnctor⟩ := decCI_split hci (erecP_ext _) hC.erec
  unfold natSuccOkW at hW
  rw [if_neg hf] at hW
  by_cases hk4 : rdW (s₀.mem.arr64 EREC) q ≠ 4
  · rw [if_pos hk4] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    rw [← hm]
    refine CRef.pure hC false (natSuccOk_run_other (hnctor hk4) _) ?_ ?_
    · simp only [decBool, ← hr]; rfl
    · unfold ResH HW; rw [← hr]; decide
  rw [if_neg hk4] at hW
  obtain ⟨cv, np, nf, rfl, hcv⟩ := hctor (by simpa using hk4)
  obtain ⟨-, hlen, hty, htyl⟩ := decCV_rd (erecP_ext s₀.mem) hC.erec hcv
  by_cases hk3 : rdW (s₀.mem.arr64 EREC) (q + 3) ≠ 0
  · rw [if_pos hk3] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    rw [← hm]
    refine CRef.pure hC false ?_ ?_ ?_
    · apply natSuccOk_run_lps
      rcases hl : cv.levelParams with _ | ⟨x, xs⟩
      · exfalso; rw [hl] at hlen; exact hk3 (UInt64.toNat_inj.mp (by simpa using hlen.symm))
      · rfl
    · simp only [decBool, ← hr]; rfl
    · unfold ResH HW; rw [← hr]; decide
  rw [if_neg hk3] at hW
  have hk3' : rdW (s₀.mem.arr64 EREC) (q + 3) = 0 := by simpa using hk3
  have hl0 : cv.levelParams.isEmpty = true := by
    simp only [List.isEmpty_iff, ← List.length_eq_zero_iff]; rw [hlen, hk3']; rfl
  cases h1 : callW p n "pin_at" [1] s₀.mem with
  | none => rw [h1] at hW; cases hW
  | some q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  rw [h1] at hW
  obtain ⟨rfl, -, -, hr₁⟩ := callW_pinAt p hp.pinAt n s₀.mem 1 r₁ m₁ h1
  simp only [show (1 : Word).toNat = 1 from rfl] at hr₁
  dsimp only at hW
  have hnt : HW (r₁.headD 0) := by
    rw [hr₁]; exact hC.pins.names_lt 1 (by decide)
  cases h2 : callW p n "const_e" [r₁.headD 0] s₀.mem with
  | none => rw [h2] at hW; cases hW
  | some q₂ =>
  obtain ⟨r₂, m₂⟩ := q₂
  rw [h2] at hW
  obtain ⟨hok, hS, hres, hfr, hhw⟩ := callW_constE p hp n s₀ a₀ dn vis fe MM eb _ hC hnt r₂ m₂ h2
  dsimp only at hW
  have hr₁' : r₁.headD 0 = pinW s₀.mem 2 := hr₁
  rw [hr₁'] at hok hS hres
  have hE : m₂.arr64 EREC = s₀.mem.arr64 EREC :=
    hfr.arr_eq EREC (by simp [CREC, CSLOT, CLP, EREC]) (by decide)
  have hrun := AM.run_of_ok _ _ hok
  have hrun' : (constE (decI (pinW s₀.mem 2))).run a₀ =
      .ok (decE (r₂.headD 0), AM.st (constE (decI (pinW s₀.mem 2))) a₀) := by
    rw [hrun, hres]; rfl
  rw [hE] at hW
  by_cases hg : rdW (s₀.mem.arr64 EREC) (q + 4) >>> 28 ≠ 6
  · rw [if_pos hg] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    rw [← hm]
    have hz := natSuccOk_run_nonforall hC.pins cv np nf _ hl0 hrun' (by
      rw [hty]
      cases hb : ((decI (rdW (s₀.mem.arr64 EREC) (q + 4)) : EIdx).tag == ETag.forallE)
      · rfl
      · exfalso; exact hg ((decE_tag_forall _ htyl).mp (beq_iff_eq.mp hb)))
    obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
    refine ⟨hok', by rw [hst']; exact hS, ?_, hfr, ?_⟩
    · rw [hres']; simp only [decBool, ← hr]; rfl
    · unfold ResH HW; rw [← hr]; decide
  rw [if_neg hg] at hW
  have hg' : rdW (s₀.mem.arr64 EREC) (q + 4) >>> 28 = 6 := by simpa using hg
  by_cases hsc : tierW (rdW (s₀.mem.arr64 EREC) (q + 4)) ≠ 0 ∧ rdW (m₂.arr64 CTL) 1 = 0
  · rw [if_pos hsc] at hW; cases hW
  rw [if_neg hsc] at hW
  by_cases hbd : tcnt m₂ FORALL (tierW (rdW (s₀.mem.arr64 EREC) (q + 4))) ≤
      idxW (rdW (s₀.mem.arr64 EREC) (q + 4))
  · rw [if_pos hbd] at hW; cases hW
  rw [if_neg hbd] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hm⟩ := hW
  rw [← hm]
  have hvOK : viewOK m₂ (rdW (s₀.mem.arr64 EREC) (q + 4)) FORALL := ⟨hsc, by simpa using hbd⟩
  obtain ⟨hview, hd, hb⟩ := view_forall m₂ _ hS.arena.1 _ htyl hvOK hg'
  have hz := natSuccOk_run_forall hC.pins cv np nf _ _ _ hl0 hrun' (by
      rw [hty]; exact beq_iff_eq.mpr ((decE_tag_forall _ htyl).mpr hg')) (by rw [hty]; exact hview)
  obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
  refine ⟨hok', by rw [hst']; exact hS, ?_, hfr, ?_⟩
  · rw [hres']
    show _ = decBool [r.headD 0]
    rw [← hr]
    simp only [decE_eq]
    rw [decI_beq _ _ hd hhw, decI_beq _ _ hb hhw]
    rw [decBool_ite', Bool.decide_and]
  · show ResH [r.headD 0]
    rw [← hr]; exact ResH_ite _

@[refines ConRon.Arena.natSuccOk]
theorem natSuccOk_refines (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb found q : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (hq : HW q)
    (hdec : found ≠ 0 → ∃ ci, decCI (erecP s₀.mem) dn q.toNat = some ci) :
    CoreSpec p n "nat_succ_ok" [found, q] (natSuccOk (decFound dn s₀.mem found q)) decBool s₀ a₀ dn
      vis fe MM eb :=
  CoreSpec.of_callC fun r m' h => callW_natSuccOk p hp n s₀ a₀ dn vis fe MM eb found q hC hdec r m' h

end refs4

/-! ## `env_find` as a run -/

section refs5
variable (p : Prog)

/-- **`env_find` as a run**: memory unchanged, the result is the twin's lookup, and a found row
decodes. -/
theorem callW_envFind (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) {dn : NIdx → Option ConLeche.Name}
    {fe : IFEnv} (vis w : Word) (hE : EnvR dn s₀.mem vis fe) (hw : HW w) (r : List Word) (m' : Mem)
    (h : callW p n "env_find" [w, vis] s₀.mem = some (r, m')) :
    m' = s₀.mem ∧ fe.find? (decI w) = decFound dn s₀.mem (r.headD 0) (r.tail.headD 0) ∧
    (r.headD 0 ≠ 0 → ∃ ci, decCI (erecP s₀.mem) dn (r.tail.headD 0).toNat = some ci) := by
  obtain ⟨t₁, ht₁, hm₁, -, hfind⟩ := triple_of_callW
    (envFind_refines p hp.envIx' hp.envRow' hp.envFind n s₀ vis w hE hw) h
  obtain ⟨t₁', ht₁', hm₁', -, hfound⟩ := triple_of_callW
    (envFind_found p hp.envIx' hp.envRow' hp.envFind n s₀ vis w hw) h
  refine ⟨ht₁.symm.trans hm₁, hfind, fun h0 => ?_⟩
  obtain ⟨htag, hrow, hq⟩ := hfound h0
  obtain ⟨ci, hci⟩ := hE.found_some w hw htag hrow
  rw [← hq] at hci
  exact ⟨ci, hci⟩

end refs5

/-! ## `nat_op_stored` -/

/-- The model of `nat_op_stored`. -/
def natOpStoredW (p : Prog) (n : Nat) (m : Mem) (vis c : Word) : Option (Word × Mem) :=
  match callW p n "env_find" [c, vis] m with
  | none => none
  | some (r₁, m₁) =>
    if r₁.headD 0 = 0 then some (0, m₁)
    else some (if rdW (m₁.arr64 EREC) (r₁.tail.headD 0) = 1 then 1 else 0, m₁)

theorem natOpStored_spec (p : Prog) (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St) (vis c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nat_op_stored" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧ natOpStoredW p n s₀.mem vis c = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.natOpStored]
  simp only [callFn, natOpStoredL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "env_find"] <;>
    finish [natOpStoredW]

theorem natOpStored_run_other {ci : IConstantInfo} (h : ∀ cv v hint, ci ≠ .defnInfo cv v hint)
    (fe : IFEnv) (a : AState) (c : NIdx) (hf : fe.find? c = some ci) :
    (natOpStored fe c).run a = .ok (false, a) := by
  simp only [natOpStored, hf]
  cases ci with
  | defnInfo cv v hint => exact absurd rfl (h cv v hint)
  | _ => rfl

theorem natOpStored_run_defn (fe : IFEnv) (a : AState) (c : NIdx) (cv : IConstantVal) (v : EIdx)
    (hint : ConLeche.ReducibilityHint) (hf : fe.find? c = some (.defnInfo cv v hint)) :
    (natOpStored fe c).run a = .ok (true, a) := by
  simp only [natOpStored, hf]; rfl

theorem natOpStored_run_none (fe : IFEnv) (a : AState) (c : NIdx) (hf : fe.find? c = none) :
    (natOpStored fe c).run a = .ok (false, a) := by
  simp only [natOpStored, hf]; rfl

section refs6
variable (p : Prog)

theorem callW_natOpStored (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb c : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (hc : HW c) (r : List Word) (m' : Mem)
    (h : callW p n "nat_op_stored" [vis, c] s₀.mem = some (r, m')) :
    CRef (natOpStored fe (decI c)) a₀ decBool dn s₀.mem vis fe MM eb r m' ResH := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (natOpStored_spec p hp.toWhnfDeltaProg n s₀ vis c) h
  unfold natOpStoredW at hW
  cases h1 : callW p n "env_find" [c, vis] s₀.mem with
  | none => rw [h1] at hW; cases hW
  | some q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  rw [h1] at hW
  obtain ⟨rfl, hfind, hdec⟩ := callW_envFind p hp n s₀ vis c hC.env hc r₁ m₁ h1
  dsimp only at hW
  by_cases hf : r₁.headD 0 = 0
  · rw [if_pos hf] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    rw [← hm]
    have hnone : fe.find? (decI c) = none := by rw [hfind]; simp only [decFound, hf, ↓reduceIte]
    refine CRef.pure hC false (natOpStored_run_none fe _ _ hnone) ?_ ?_
    · simp only [decBool, ← hr]; rfl
    · unfold ResH HW; rw [← hr]; decide
  rw [if_neg hf] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hm⟩ := hW
  rw [← hm]
  obtain ⟨ci, hci⟩ := hdec hf
  have hfind' : fe.find? (decI c) = some ci := by
    rw [hfind]; simp only [decFound, hf, ↓reduceIte]; exact hci
  obtain ⟨hdefn, hndefn, -, -, -, -⟩ := decCI_split hci (erecP_ext _) hC.erec
  by_cases hk : rdW (s₀.mem.arr64 EREC) (r₁.tail.headD 0) = 1
  · obtain ⟨cv, v, hint, rfl, -⟩ := hdefn hk
    refine CRef.pure hC true (natOpStored_run_defn fe _ _ cv v hint hfind') ?_ ?_
    · simp only [decBool, ← hr, hk]; rfl
    · show ResH [r.headD 0]
      rw [← hr]; exact ResH_ite _
  · refine CRef.pure hC false (natOpStored_run_other (hndefn hk) fe _ _ hfind') ?_ ?_
    · simp only [decBool, ← hr, hk]; rfl
    · show ResH [r.headD 0]
      rw [← hr]; exact ResH_ite _

@[refines ConRon.Arena.natOpStored]
theorem natOpStored_refines (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb c : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (hc : HW c) :
    CoreSpec p n "nat_op_stored" [vis, c] (natOpStored fe (decI c)) decBool s₀ a₀ dn vis fe MM eb :=
  CoreSpec.of_callC fun r m' h => callW_natOpStored p hp n s₀ a₀ dn vis fe MM eb c hC hc r m' h

end refs6

/-! ## `nat_lit_supported` -/

/-- The model of `nat_lit_supported`. -/
def natLitSupportedW (p : Prog) (n : Nat) (m : Mem) (vis : Word) : Option (Word × Mem) :=
  match callW p n "pin_at" [1] m with
  | none => none
  | some (a₁, m₁) =>
  match callW p n "env_find" [a₁.headD 0, vis] m₁ with
  | none => none
  | some (b₁, m₂) =>
  match callW p n "nat_ind_ok" [b₁.headD 0, b₁.tail.headD 0] m₂ with
  | none => none
  | some (c₁, m₃) =>
  if c₁.headD 0 = 0 then some (0, m₃) else
  match callW p n "pin_at" [2] m₃ with
  | none => none
  | some (a₂, m₄) =>
  match callW p n "env_find" [a₂.headD 0, vis] m₄ with
  | none => none
  | some (b₂, m₅) =>
  match callW p n "nat_zero_ok" [b₂.headD 0, b₂.tail.headD 0] m₅ with
  | none => none
  | some (c₂, m₆) =>
  if c₂.headD 0 = 0 then some (0, m₆) else
  match callW p n "pin_at" [3] m₆ with
  | none => none
  | some (a₃, m₇) =>
  match callW p n "env_find" [a₃.headD 0, vis] m₇ with
  | none => none
  | some (b₃, m₈) =>
  match callW p n "nat_succ_ok" [b₃.headD 0, b₃.tail.headD 0] m₈ with
  | none => none
  | some (c₃, m₉) => some (c₃.headD 0, m₉)

section nls
variable (p : Prog) (n : Nat) (vis : Word) (m m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ : Mem)
  (a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ : List Word)

end nls

theorem natLitSupported_spec (p : Prog) (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St) (vis : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nat_lit_supported" [vis]
    ⦃fun r s' => LocEq s' s₀ ∧ natLitSupportedW p n s₀.mem vis = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.natLitSupported]
  simp only [callFn, natLitSupportedL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "pin_at", callW_spec p n "env_find", callW_spec p n "nat_ind_ok",
      callW_spec p n "nat_zero_ok", callW_spec p n "nat_succ_ok"] <;>
    finish (gen := 30) [natLitSupportedW]

theorem pinNatZero_run {m : Mem} {a : AState} (h : PinsFull m a.pins) :
    pinNatZero.run a = .ok (decI (pinW m 3), a) := pinAt_run h 2 (by decide)

theorem pinNatSucc_run {m : Mem} {a : AState} (h : PinsFull m a.pins) :
    pinNatSucc.run a = .ok (decI (pinW m 4), a) := pinAt_run h 3 (by decide)

section nlsRun
variable {m m' m'' : Mem} {a a₁ a₂ a₃ : AState} (fe : IFEnv)

theorem natLitSupported_run_1 (hP : PinsFull m a.pins)
    (hI : (natIndOk (fe.find? (decI (pinW m 2)))).run a = .ok (false, a₁)) :
    (natLitSupported fe).run a = .ok (false, a₁) := by
  simp only [natLitSupported, StateT.run_bind, pinNat_run hP, except_ok_bind, hI, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]; rfl

theorem natLitSupported_run_2 (hP : PinsFull m a.pins) (hP' : PinsFull m' a₁.pins)
    (hI : (natIndOk (fe.find? (decI (pinW m 2)))).run a = .ok (true, a₁))
    (hZ : (natZeroOk (fe.find? (decI (pinW m' 3)))).run a₁ = .ok (false, a₂)) :
    (natLitSupported fe).run a = .ok (false, a₂) := by
  simp only [natLitSupported, StateT.run_bind, pinNat_run hP, except_ok_bind, hI,
    pinNatZero_run hP', hZ, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]; rfl

theorem natLitSupported_run_3 (hP : PinsFull m a.pins) (hP' : PinsFull m' a₁.pins)
    (hP'' : PinsFull m'' a₂.pins) (b : Bool)
    (hI : (natIndOk (fe.find? (decI (pinW m 2)))).run a = .ok (true, a₁))
    (hZ : (natZeroOk (fe.find? (decI (pinW m' 3)))).run a₁ = .ok (true, a₂))
    (hS : (natSuccOk (fe.find? (decI (pinW m'' 4)))).run a₂ = .ok (b, a₃)) :
    (natLitSupported fe).run a = .ok (b, a₃) := by
  simp only [natLitSupported, StateT.run_bind, pinNat_run hP, except_ok_bind, hI,
    pinNatZero_run hP', hZ, pinNatSucc_run hP'', hS, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]

end nlsRun

section refs7
variable (p : Prog)

/-- **`pin_at(k); env_find(·, vis)` as runs**: the pinned name's lookup. -/
theorem callW_pinFind (hp : WhnfDeltaProg' p) (k : Word) (hk : k.toNat < 51) (n : Nat) (m : Mem)
    {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} (vis : Word) {a : AState}
    (hC : ∃ M eb, CoreS dn m a vis fe M eb) (r₁ : List Word) (m₁ : Mem) (r₂ : List Word) (m₂ : Mem)
    (h1 : callW p n "pin_at" [k] m = some (r₁, m₁))
    (h2 : callW p n "env_find" [r₁.headD 0, vis] m₁ = some (r₂, m₂)) :
    m₁ = m ∧ m₂ = m ∧ fe.find? (decI (pinW m (1 + k.toNat))) =
        decFound dn m (r₂.headD 0) (r₂.tail.headD 0) ∧
      (r₂.headD 0 ≠ 0 → ∃ ci, decCI (erecP m) dn (r₂.tail.headD 0).toNat = some ci) := by
  obtain ⟨M, eb, hC⟩ := hC
  obtain ⟨hm1, -, -, hr₁⟩ := callW_pinAt p hp.pinAt n m k r₁ m₁ h1
  subst m₁
  have hnt : HW (r₁.headD 0) := by
    rw [hr₁]; exact hC.pins.names_lt _ (by omega)
  obtain ⟨hm2, hfind, hdec⟩ := callW_envFind p hp n ⟨m, Locals.init []⟩ vis _ hC.env hnt r₂ m₂ h2
  subst m₂
  refine ⟨rfl, rfl, ?_, hdec⟩
  rw [← hr₁]
  exact hfind

end refs7

section refs8
variable (p : Prog)

theorem callW_natLitSupported (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (r : List Word) (m' : Mem)
    (h : callW p n "nat_lit_supported" [vis] s₀.mem = some (r, m')) :
    CRef (natLitSupported fe) a₀ decBool dn s₀.mem vis fe MM eb r m' ResH := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (natLitSupported_spec p hp.toWhnfDeltaProg n s₀ vis) h
  unfold natLitSupportedW at hW
  -- stage 1
  rcases h1 : callW p n "pin_at" [1] s₀.mem with _ | ⟨a₁, m₁⟩ <;> simp only [h1, reduceCtorEq] at hW
  rcases h2 : callW p n "env_find" [a₁.headD 0, vis] m₁ with _ | ⟨b₁, m₂⟩
    <;> simp only [h2, reduceCtorEq] at hW
  obtain ⟨hm1, hm2, hfind1, hdec1⟩ := callW_pinFind p hp 1 (by decide) n s₀.mem vis ⟨MM, eb, hC⟩
    a₁ m₁ b₁ m₂ h1 h2
  subst hm1 hm2
  rcases h3 : callW p n "nat_ind_ok" [b₁.headD 0, b₁.tail.headD 0] s₀.mem with _ | ⟨c₁, m₃⟩
    <;> simp only [h3, reduceCtorEq] at hW
  obtain ⟨hok1, hS1, hres1, hfr1, hrh1⟩ := callW_natIndOk p hp.toWhnfDeltaProg n s₀ a₀ dn vis fe MM eb
    _ _ hC hdec1 c₁ m₃ h3
  have hI : (natIndOk (fe.find? (decI (pinW s₀.mem 2)))).run a₀ =
      .ok (decBool c₁, AM.st (natIndOk (decFound dn s₀.mem (b₁.headD 0) (b₁.tail.headD 0))) a₀) := by
    have := AM.run_of_ok _ _ hok1
    rw [hres1] at this
    rw [show pinW s₀.mem 2 = pinW s₀.mem (1 + (1 : Word).toNat) from rfl, hfind1]
    exact this
  by_cases hc1 : c₁.headD 0 = 0
  · rw [if_pos hc1] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    rw [← hm]
    have hb : decBool c₁ = false := by simp only [decBool, hc1]; rfl
    rw [hb] at hI
    have hz := natLitSupported_run_1 fe hC.pins hI
    obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
    refine ⟨hok', by rw [hst']; exact hS1, ?_, hfr1, ?_⟩
    · rw [hres']; simp only [decBool, ← hr]; rfl
    · unfold ResH HW; rw [← hr]; decide
  rw [if_neg hc1] at hW
  have hb : decBool c₁ = true := by simp only [decBool, bne_iff_ne, ne_eq]; exact hc1
  rw [hb] at hI
  -- stage 2
  rcases h4 : callW p n "pin_at" [2] m₃ with _ | ⟨a₂, m₄⟩ <;> simp only [h4, reduceCtorEq] at hW
  rcases h5 : callW p n "env_find" [a₂.headD 0, vis] m₄ with _ | ⟨b₂, m₅⟩
    <;> simp only [h5, reduceCtorEq] at hW
  obtain ⟨hm4, hm5, hfind2, hdec2⟩ := callW_pinFind p hp 2 (by decide) n m₃ vis ⟨_, _, hS1⟩
    a₂ m₄ b₂ m₅ h4 h5
  subst m₄ m₅
  rcases h6 : callW p n "nat_zero_ok" [b₂.headD 0, b₂.tail.headD 0] m₃ with _ | ⟨c₂, m₆⟩
    <;> simp only [h6, reduceCtorEq] at hW
  obtain ⟨hok2, hS2, hres2, hfr2, hrh2⟩ : CRef
      (natZeroOk (decFound dn m₃ (b₂.headD 0) (b₂.tail.headD 0)))
      (AM.st (natIndOk (decFound dn s₀.mem (b₁.headD 0) (b₁.tail.headD 0))) a₀) decBool dn m₃ vis fe
      MM eb c₂ m₆ ResH :=
    callW_natZeroOk p hp n ⟨m₃, Locals.init []⟩ _ dn vis fe MM eb _ _ hS1 hdec2 c₂ m₆ h6
  have hZ : (natZeroOk (fe.find? (decI (pinW m₃ 3)))).run
      (AM.st (natIndOk (decFound dn s₀.mem (b₁.headD 0) (b₁.tail.headD 0))) a₀) =
      .ok (decBool c₂, AM.st (natZeroOk (decFound dn m₃ (b₂.headD 0) (b₂.tail.headD 0)))
        (AM.st (natIndOk (decFound dn s₀.mem (b₁.headD 0) (b₁.tail.headD 0))) a₀)) := by
    have := AM.run_of_ok _ _ hok2
    rw [hres2] at this
    rw [show pinW m₃ 3 = pinW m₃ (1 + (2 : Word).toNat) from rfl, hfind2]
    exact this
  by_cases hc2 : c₂.headD 0 = 0
  · rw [if_pos hc2] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    rw [← hm]
    have hb2 : decBool c₂ = false := by simp only [decBool, hc2]; rfl
    rw [hb2] at hZ
    have hz := natLitSupported_run_2 fe hC.pins hS1.pins hI hZ
    obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
    refine ⟨hok', by rw [hst']; exact hS2, ?_, hfr1.trans hfr2, ?_⟩
    · rw [hres']; simp only [decBool, ← hr]; rfl
    · unfold ResH HW; rw [← hr]; decide
  rw [if_neg hc2] at hW
  have hb2 : decBool c₂ = true := by simp only [decBool, bne_iff_ne, ne_eq]; exact hc2
  rw [hb2] at hZ
  -- stage 3
  rcases h7 : callW p n "pin_at" [3] m₆ with _ | ⟨a₃, m₇⟩ <;> simp only [h7, reduceCtorEq] at hW
  rcases h8 : callW p n "env_find" [a₃.headD 0, vis] m₇ with _ | ⟨b₃, m₈⟩
    <;> simp only [h8, reduceCtorEq] at hW
  obtain ⟨hm7, hm8, hfind3, hdec3⟩ := callW_pinFind p hp 3 (by decide) n m₆ vis ⟨_, _, hS2⟩
    a₃ m₇ b₃ m₈ h7 h8
  subst m₇ m₈
  rcases h9 : callW p n "nat_succ_ok" [b₃.headD 0, b₃.tail.headD 0] m₆ with _ | ⟨c₃, m₉⟩
    <;> simp only [h9, reduceCtorEq] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hm⟩ := hW
  rw [← hm]
  obtain ⟨hok3, hS3, hres3, hfr3, hrh3⟩ : CRef
      (natSuccOk (decFound dn m₆ (b₃.headD 0) (b₃.tail.headD 0)))
      (AM.st (natZeroOk (decFound dn m₃ (b₂.headD 0) (b₂.tail.headD 0)))
        (AM.st (natIndOk (decFound dn s₀.mem (b₁.headD 0) (b₁.tail.headD 0))) a₀)) decBool dn m₆ vis fe
      MM eb c₃ m₉ ResH :=
    callW_natSuccOk p hp n ⟨m₆, Locals.init []⟩ _ dn vis fe MM eb _ _ hS2 hdec3 c₃ m₉ h9
  have hS : (natSuccOk (fe.find? (decI (pinW m₆ 4)))).run
      (AM.st (natZeroOk (decFound dn m₃ (b₂.headD 0) (b₂.tail.headD 0)))
        (AM.st (natIndOk (decFound dn s₀.mem (b₁.headD 0) (b₁.tail.headD 0))) a₀)) =
      .ok (decBool c₃, AM.st (natSuccOk (decFound dn m₆ (b₃.headD 0) (b₃.tail.headD 0)))
        (AM.st (natZeroOk (decFound dn m₃ (b₂.headD 0) (b₂.tail.headD 0)))
          (AM.st (natIndOk (decFound dn s₀.mem (b₁.headD 0) (b₁.tail.headD 0))) a₀))) := by
    have := AM.run_of_ok _ _ hok3
    rw [hres3] at this
    rw [show pinW m₆ 4 = pinW m₆ (1 + (3 : Word).toNat) from rfl, hfind3]
    exact this
  have hz := natLitSupported_run_3 fe hC.pins hS1.pins hS2.pins (decBool c₃) hI hZ hS
  obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
  refine ⟨hok', by rw [hst']; exact hS3, ?_, (hfr1.trans hfr2).trans hfr3, ?_⟩
  · rw [hres']; simp only [decBool, ← hr]
  · show ResH [r.headD 0]
    rw [← hr]; exact hrh3

@[refines ConRon.Arena.natLitSupported]
theorem natLitSupported_refines (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) :
    CoreSpec p n "nat_lit_supported" [vis] (natLitSupported fe) decBool s₀ a₀ dn vis fe MM eb :=
  CoreSpec.of_callC fun r m' h => callW_natLitSupported p hp n s₀ a₀ dn vis fe MM eb hC r m' h

end refs8

end L.Arena
