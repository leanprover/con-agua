import ConAgua.Arena.WhnfDeltaSlot
import ConAgua.Arena.WhnfCoreApp
import ConAgua.Arena.WhnfCoreProj
import ConAgua.Arena.WriteSets
import ConAgua.Arena.ConstRefine

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

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

theorem rdW_at {b : Array Word} {q : Word} {w : Word} (hb : b[q.toNat]? = some w) :
    rdW b q = w := by simp only [rdW, hb]; rfl

theorem toNat_ofNat_lt (k : Nat) (hk : k < 2 ^ 64) : (UInt64.ofNat k).toNat = k := by
  simp; omega

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
    (hD : ArenaD m' a') (hcpl : cpl a' = cpl a) (hf : MemFrame [CREC, CSLOT] [18, 19] m m') :
    CoreS dn m' a' vis fe M eb :=
  hS.arena_frame hD hcpl hf
    (fun b hb => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with rfl | rfl <;> decide)
    (by simp [CREC, CSLOT, PINS])
    (fun b hb => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with rfl | rfl <;> decide)
    (fun x hx => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl <;> decide)
    (fun x hx => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl <;> decide)

theorem StackKept.of_const_frame {m m' : Mem} (hf : MemFrame [CREC, CSLOT] [18, 19] m m') :
    StackKept m m' := by
  have hspn : m'.arr64 SPN = m.arr64 SPN :=
    hf.1 SPN (by simp [CREC, CSLOT, SPN]) (by decide)
  have h136 : rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 := hf.2.1 136 (by simp)
  exact ⟨by simp only [spTop, h136], by rw [hspn], fun i _ => by simp only [spW, hspn]⟩

/-- **An interned `const` handle word is below `2^32`.** -/
theorem ceinternW_hw (m : Mem) (a : AState) (hR : ConstR m a) (f x : Word) (hf : f.toNat < 2 ^ 32)
    (hx : x.toNat < 2 ^ 32) (w : Word) (m' : Mem) (hI : ceinternW m f x = some (w, m')) :
    w.toNat < 2 ^ 32 := by
  rw [ceinternW_eq] at hI
  exact internM_hw constSch CeRecRel cehash constSch_wf m _ _ _ hR (ceMt m f x) _ _ _ _
    (probe_homeG constSch m 0 _ _ (ceprobeW_arm m f x 0) _)
    (probe_homeG constSch m 1 _ _ (ceprobeW_arm m f x 1) _) _ (cepushOK_room m) _ _ w m' hI

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
    MemFrame [CREC, CSLOT] [18, 19] s₀.mem m' ∧ HW (r.headD 0) := by
  obtain ⟨s', rfl, hm⟩ := triple_of_callW (internConst_spec p hpf hpp hp n s₀ f x) h
  obtain ⟨-, hm⟩ := hm
  obtain ⟨h1, h2, h3⟩ := internConst_D s₀.mem a₀ hD f x _ hf hx _ hm
  refine ⟨h1, h2, h3, ?_, ceinternW_hw s₀.mem a₀ ?_ f x hf hx _ _ hm⟩
  · have := internM_frame constSch constSch_wf _ _ _ _ _ _ _ _ (ceinternW_eq _ _ _ ▸ hm)
    simpa [constSch] using this
  · exact hD.1.const

end progs


/-! ## The `Nat` functions' write set -/

/-- The `Nat` arms' program, with `nat_succ_lit`. -/
def natArmProg' : Prog := natArmProg ++ [("nat_succ_lit", natSuccLitL)]
def natFns : List FnName := natArmProg'.map (·.1)
/-- What they write: the pool, the `lit` table (2, 3), the `const` table (18, 19 = `CREC`, `CSLOT`),
and the counts. -/
def natA : List ArrId := [POOL, 2, 3, CREC, CSLOT]
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
  /-- The write set of the `Nat` functions (`natFns`): the pool, the `lit` and `const` tables.
  Provable from `closedW_of_agree` and `natArmProg'_closed` whenever `p` agrees with
  `natArmProg'` on `natFns`. -/
  natClosed : closedA p natA natC natFns = true

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
    AM.res (constE (decI nm)) a₀ = decH r ∧ MemFrame [CREC, CSLOT] [18, 19] s₀.mem m' ∧
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
  · rw [hres', hres, decH, ← hr]; rfl

/-- **`const_e` refines `constE`.** `WhnfDeltaProg'` for the extra function lookups. -/
theorem constE_refines' (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
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
    MemFrame [CREC, CSLOT] [18, 19] m₀ m' ∧ ok r

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
  cases h1 : callW p n "pin_word" [54] s₀.mem with
  | none => rw [h1] at hW; cases hW
  | some q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  rw [h1] at hW
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

theorem natIndOk_refines' (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St) (a₀ : AState)
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
  have hE : m₂.arr64 EREC = s₀.mem.arr64 EREC := hfr.arr_eq EREC (by simp [CREC, CSLOT, EREC]) (by decide)
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

theorem natZeroOk_refines' (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
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
        else if rdW (m₂.arr64 CTL) (30 + tierW (rdW (m₂.arr64 EREC) (q + 4))) ≤
            idxW (rdW (m₂.arr64 EREC) (q + 4)) then none
        else some (if rdW (m₂.arr64 FAREC) (idxW (rdW (m₂.arr64 EREC) (q + 4)) * 4 +
              tierW (rdW (m₂.arr64 EREC) (q + 4)) * 2) = r₂.headD 0 ∧
            rdW (m₂.arr64 FAREC) (idxW (rdW (m₂.arr64 EREC) (q + 4)) * 4 +
              tierW (rdW (m₂.arr64 EREC) (q + 4)) * 2 + 1) = r₂.headD 0 then 1 else 0, m₂)

theorem natSuccOk_spec (p : Prog) (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St) (found q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nat_succ_ok" [found, q]
    ⦃fun r s' => LocEq s' s₀ ∧ natSuccOkW p n s₀.mem found q = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.natSuccOk]
  simp only [callFn, natSuccOkL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
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
    hfr.arr_eq EREC (by simp [CREC, CSLOT, EREC]) (by decide)
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
  by_cases hbd : rdW (m₂.arr64 CTL) (30 + tierW (rdW (s₀.mem.arr64 EREC) (q + 4))) ≤
      idxW (rdW (s₀.mem.arr64 EREC) (q + 4))
  · rw [if_pos hbd] at hW; cases hW
  rw [if_neg hbd] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hm⟩ := hW
  rw [← hm]
  have hvOK : viewOK m₂ (rdW (s₀.mem.arr64 EREC) (q + 4)) 30 := ⟨hsc, by simpa using hbd⟩
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

theorem natSuccOk_refines' (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
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

theorem natOpStored_refines' (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
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

theorem natLitSupportedW_1
    (h1 : callW p n "pin_at" [1] m = some (a₁, m₁))
    (h2 : callW p n "env_find" [a₁.headD 0, vis] m₁ = some (b₁, m₂))
    (h3 : callW p n "nat_ind_ok" [b₁.headD 0, b₁.tail.headD 0] m₂ = some (c₁, m₃))
    (h0 : c₁.headD 0 = 0) : natLitSupportedW p n m vis = some (0, m₃) := by
  simp only [natLitSupportedW, h1, h2, h3, h0, ↓reduceIte]

theorem natLitSupportedW_2
    (h1 : callW p n "pin_at" [1] m = some (a₁, m₁))
    (h2 : callW p n "env_find" [a₁.headD 0, vis] m₁ = some (b₁, m₂))
    (h3 : callW p n "nat_ind_ok" [b₁.headD 0, b₁.tail.headD 0] m₂ = some (c₁, m₃))
    (h0 : ¬ c₁.headD 0 = 0)
    (h4 : callW p n "pin_at" [2] m₃ = some (a₂, m₄))
    (h5 : callW p n "env_find" [a₂.headD 0, vis] m₄ = some (b₂, m₅))
    (h6 : callW p n "nat_zero_ok" [b₂.headD 0, b₂.tail.headD 0] m₅ = some (c₂, m₆))
    (h00 : c₂.headD 0 = 0) : natLitSupportedW p n m vis = some (0, m₆) := by
  simp only [natLitSupportedW, h1, h2, h3, h0, h4, h5, h6, h00, ↓reduceIte]

theorem natLitSupportedW_3
    (h1 : callW p n "pin_at" [1] m = some (a₁, m₁))
    (h2 : callW p n "env_find" [a₁.headD 0, vis] m₁ = some (b₁, m₂))
    (h3 : callW p n "nat_ind_ok" [b₁.headD 0, b₁.tail.headD 0] m₂ = some (c₁, m₃))
    (h0 : ¬ c₁.headD 0 = 0)
    (h4 : callW p n "pin_at" [2] m₃ = some (a₂, m₄))
    (h5 : callW p n "env_find" [a₂.headD 0, vis] m₄ = some (b₂, m₅))
    (h6 : callW p n "nat_zero_ok" [b₂.headD 0, b₂.tail.headD 0] m₅ = some (c₂, m₆))
    (h00 : ¬ c₂.headD 0 = 0)
    (h7 : callW p n "pin_at" [3] m₆ = some (a₃, m₇))
    (h8 : callW p n "env_find" [a₃.headD 0, vis] m₇ = some (b₃, m₈))
    (h9 : callW p n "nat_succ_ok" [b₃.headD 0, b₃.tail.headD 0] m₈ = some (c₃, m₉)) :
    natLitSupportedW p n m vis = some (c₃.headD 0, m₉) := by
  simp only [natLitSupportedW, h1, h2, h3, h0, h4, h5, h6, h00, h7, h8, h9, ↓reduceIte]

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
  cases h1 : callW p n "pin_at" [1] s₀.mem with
  | none => rw [h1] at hW; cases hW
  | some q₁ =>
  obtain ⟨a₁, m₁⟩ := q₁
  rw [h1] at hW; dsimp only at hW
  cases h2 : callW p n "env_find" [a₁.headD 0, vis] m₁ with
  | none => rw [h2] at hW; cases hW
  | some q₂ =>
  obtain ⟨b₁, m₂⟩ := q₂
  rw [h2] at hW; dsimp only at hW
  obtain ⟨hm1, hm2, hfind1, hdec1⟩ := callW_pinFind p hp 1 (by decide) n s₀.mem vis ⟨MM, eb, hC⟩
    a₁ m₁ b₁ m₂ h1 h2
  subst hm1 hm2
  cases h3 : callW p n "nat_ind_ok" [b₁.headD 0, b₁.tail.headD 0] s₀.mem with
  | none => rw [h3] at hW; cases hW
  | some q₃ =>
  obtain ⟨c₁, m₃⟩ := q₃
  rw [h3] at hW; dsimp only at hW
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
  cases h4 : callW p n "pin_at" [2] m₃ with
  | none => rw [h4] at hW; cases hW
  | some q₄ =>
  obtain ⟨a₂, m₄⟩ := q₄
  rw [h4] at hW; dsimp only at hW
  cases h5 : callW p n "env_find" [a₂.headD 0, vis] m₄ with
  | none => rw [h5] at hW; cases hW
  | some q₅ =>
  obtain ⟨b₂, m₅⟩ := q₅
  rw [h5] at hW; dsimp only at hW
  obtain ⟨hm4, hm5, hfind2, hdec2⟩ := callW_pinFind p hp 2 (by decide) n m₃ vis ⟨_, _, hS1⟩
    a₂ m₄ b₂ m₅ h4 h5
  subst m₄ m₅
  cases h6 : callW p n "nat_zero_ok" [b₂.headD 0, b₂.tail.headD 0] m₃ with
  | none => rw [h6] at hW; cases hW
  | some q₆ =>
  obtain ⟨c₂, m₆⟩ := q₆
  rw [h6] at hW; dsimp only at hW
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
  cases h7 : callW p n "pin_at" [3] m₆ with
  | none => rw [h7] at hW; cases hW
  | some q₇ =>
  obtain ⟨a₃, m₇⟩ := q₇
  rw [h7] at hW; dsimp only at hW
  cases h8 : callW p n "env_find" [a₃.headD 0, vis] m₇ with
  | none => rw [h8] at hW; cases hW
  | some q₈ =>
  obtain ⟨b₃, m₈⟩ := q₈
  rw [h8] at hW; dsimp only at hW
  obtain ⟨hm7, hm8, hfind3, hdec3⟩ := callW_pinFind p hp 3 (by decide) n m₆ vis ⟨_, _, hS2⟩
    a₃ m₇ b₃ m₈ h7 h8
  subst m₇ m₈
  cases h9 : callW p n "nat_succ_ok" [b₃.headD 0, b₃.tail.headD 0] m₆ with
  | none => rw [h9] at hW; cases hW
  | some q₉ =>
  obtain ⟨c₃, m₉⟩ := q₉
  rw [h9] at hW; dsimp only at hW
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

theorem natLitSupported_refines' (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) :
    CoreSpec p n "nat_lit_supported" [vis] (natLitSupported fe) decBool s₀ a₀ dn vis fe MM eb :=
  CoreSpec.of_callC fun r m' h => callW_natLitSupported p hp n s₀ a₀ dn vis fe MM eb hC r m' h

end refs8


/-! ## `raw_nat_lit` -/

/-- The model of `raw_nat_lit`: `(flag, off, cnt, memory)`. -/
def rawNatLitW (p : Prog) (n : Nat) (m : Mem) (h : Word) : Option (Word × Word × Word × Mem) :=
  if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if h >>> 28 = 0 then
    (if rdW (m.arr64 CTL) (22 + tierW h) ≤ idxW h then none else some (0, 0, 0, m))
  else if h >>> 28 = 1 then
    (if rdW (m.arr64 CTL) (26 + tierW h) ≤ idxW h then none else some (0, 0, 0, m))
  else if h >>> 28 = 2 then
    (if rdW (m.arr64 CTL) (16 + tierW h) ≤ idxW h then none else some (0, 0, 0, m))
  else if h >>> 28 = 3 then
    (if rdW (m.arr64 CTL) (18 + tierW h) ≤ idxW h then none else
      match callW p n "pin_at" [2] m with
      | none => none
      | some (r₁, m₁) =>
        match callW p n "pin_word" [52] m₁ with
        | none => none
        | some (r₂, m₂) =>
          if rdW (m₂.arr64 CREC) (idxW h * 4 + tierW h * 2) = r₁.headD 0 ∧
              rdW (m₂.arr64 CREC) (idxW h * 4 + tierW h * 2 + 1) = r₂.headD 0 then
            some (1, rdW (m₂.arr64 CTL) 0, 0, m₂)
          else some (0, 0, 0, m₂))
  else if h >>> 28 = 4 then
    (if rdW (m.arr64 CTL) (4 + tierW h) ≤ idxW h then none else some (0, 0, 0, m))
  else if h >>> 28 = 5 then
    (if rdW (m.arr64 CTL) (28 + tierW h) ≤ idxW h then none else some (0, 0, 0, m))
  else if h >>> 28 = 6 then
    (if rdW (m.arr64 CTL) (30 + tierW h) ≤ idxW h then none else some (0, 0, 0, m))
  else if h >>> 28 = 7 then
    (if rdW (m.arr64 CTL) (20 + tierW h) ≤ idxW h then none else some (0, 0, 0, m))
  else if h >>> 28 = 8 then
    (if rdW (m.arr64 CTL) (2 + tierW h) ≤ idxW h then none
      else if rdW (m.arr64 REC) (idxW h * 8 + tierW h * 4) = 0 then
        some (1, rdW (m.arr64 REC) (idxW h * 8 + tierW h * 4 + 1),
          rdW (m.arr64 REC) (idxW h * 8 + tierW h * 4 + 2), m)
      else some (0, 0, 0, m))
  else if h >>> 28 ≠ 9 then none
  else if rdW (m.arr64 CTL) (32 + tierW h) ≤ idxW h then none else some (0, 0, 0, m)

theorem rawNatLit_spec (p : Prog) (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St) (h : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "raw_nat_lit" [h]
    ⦃fun r s' => LocEq s' s₀ ∧
      rawNatLitW p n s₀.mem h = some (r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.rawNatLit]
  simp only [callFn, rawNatLitL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "pin_at", callW_spec p n "pin_word"] <;>
    finish (gen := 30) [rawNatLitW, tierW, idxW]


theorem rdW_ctl_top' (m : Mem) : rdW (m.arr64 CTL) 0 = m.top := by
  simp [rdW, Mem.top]

/-- **A `lit` node past the view checks**: the kind word `0` says `natVal`, with the record's
slice; any other kind says `strVal`. -/
theorem view_lit_nat (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hh : h.toNat < 2 ^ 32)
    (hv : viewOK m h 2) (hg : h >>> 28 = 8) :
    (rdW (m.arr64 REC) (idxW h * 8 + tierW h * 4) = 0 →
      ∃ N, a.store.view (decE h) = some (.lit (.natVal N)) ∧ NatRec m (tierW h) (idxW h) N) ∧
    (rdW (m.arr64 REC) (idxW h * 8 + tierW h * 4) ≠ 0 →
      ∃ s, a.store.view (decE h) = some (.lit (.strVal s))) := by
  obtain ⟨k, hk, hkr⟩ := node_of m a h litSch RecRel litH (·.lits) _ hR.lit.2 hv.2
  have hview : ∀ l, k = ⟨l⟩ → a.store.view (decE h) = some (.lit l) := by
    intro l hl
    rw [view_tier m a hR h hh hv.1, get_lit _ h hh hg, Tbl.node?, hk, hl]
    rfl
  obtain ⟨⟨N⟩ | ⟨s⟩⟩ := k
  · simp only [RecRel_natVal] at hkr
    exact ⟨fun _ => ⟨N, hview _ rfl, hkr⟩, fun hne => absurd hkr.1 hne⟩
  · simp only [RecRel_strVal, StrRec] at hkr
    exact ⟨fun h0 => absurd (hkr.1.symm.trans h0) (by decide), fun _ => ⟨s, hview _ rfl⟩⟩

/-- The result of a `raw_nat_lit` word triple, as the twin's option. -/
def rawDec (m : Mem) (r : List Word) : Option Nat :=
  if r.headD 0 = 0 then none
  else some (pv (m.arr64 POOL) (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat)

/-- The postcondition of a `raw_nat_lit` run. -/
def RawOut (m : Mem) (a₀ : AState) (h : Word) (r : List Word) : Prop :=
  (rawNatLit? (decE h)).run a₀ = .ok (rawDec m r, a₀) ∧ ResH r ∧
  (r.headD 0 ≠ 0 → SliceOK m (r.tail.headD 0) (r.tail.tail.headD 0) ∧
    Norm (m.arr64 POOL) (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat)

theorem RawOut.none {m : Mem} {a₀ : AState} {h : Word} {r : List Word}
    (hrun : (rawNatLit? (decE h)).run a₀ = .ok (none, a₀)) (hr0 : r.headD 0 = 0) :
    RawOut m a₀ h r :=
  ⟨by unfold rawDec; rw [if_pos hr0]; exact hrun, by unfold ResH HW; rw [hr0]; decide,
    fun hne => absurd hr0 hne⟩

theorem rawNatLit_run_other {a : AState} {h : EIdx} {v : ENodeView} (hv : a.store.view h = some v)
    (hl : ∀ N, v ≠ .lit (.natVal N)) (hc : ∀ c us, v ≠ .const c us) :
    (rawNatLit? h).run a = .ok (none, a) := by
  simp only [rawNatLit?, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]
  cases v with
  | lit l =>
    cases l with
    | natVal N => exact absurd rfl (hl N)
    | strVal s => rfl
  | const c us => exact absurd rfl (hc c us)
  | _ => rfl

theorem rawNatLit_run_lit {a : AState} {h : EIdx} {N : Nat}
    (hv : a.store.view h = some (.lit (.natVal N))) :
    (rawNatLit? h).run a = .ok (some N, a) := by
  simp only [rawNatLit?, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]; rfl

theorem rawNatLit_run_const {m : Mem} {a : AState} {h : EIdx} {c : NIdx} {us : LsIdx}
    (hP : PinsFull m a.pins) (hv : a.store.view h = some (.const c us)) :
    (rawNatLit? h).run a = .ok (if c == decI (pinW m 3) && us == decI (pinW m 52) then some 0
      else none, a) := by
  simp only [rawNatLit?, StateT.run_bind, view_run _ _ _ hv, except_ok_bind, emptyLevels,
    pinEmptyLevels_run hP, pinNatZero_run hP]; rfl


theorem view_other (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hh : h.toNat < 2 ^ 32)
    (c : Word) (hv : viewOK m h c)
    (hcg : (h >>> 28 = 0 ∧ c = 22) ∨ (h >>> 28 = 1 ∧ c = 26) ∨ (h >>> 28 = 2 ∧ c = 16) ∨
      (h >>> 28 = 4 ∧ c = 4) ∨ (h >>> 28 = 5 ∧ c = 28) ∨ (h >>> 28 = 6 ∧ c = 30) ∨
      (h >>> 28 = 7 ∧ c = 20) ∨ (h >>> 28 = 9 ∧ c = 32)) :
    ∃ v, a.store.view (decE h) = some v ∧ (∀ N, v ≠ .lit (.natVal N)) ∧
      (∀ c us, v ≠ .const c us) := by
  rcases hcg with ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩
  · exact ⟨_, view_bvar m a hR h hh hv g, fun N => nofun, fun c us => nofun⟩
  · obtain ⟨i, ty, hw⟩ := view_fvar m a hR h hh hv g
    exact ⟨_, hw, fun N => nofun, fun c us => nofun⟩
  · obtain ⟨u, hw⟩ := view_sort m a hR h hh hv g
    exact ⟨_, hw, fun N => nofun, fun c us => nofun⟩
  · exact ⟨_, (view_app m a hR h hh hv g).1, fun N => nofun, fun c us => nofun⟩
  · exact ⟨_, (view_lam m a hR h hh hv g).1, fun N => nofun, fun c us => nofun⟩
  · exact ⟨_, (view_forall m a hR h hh hv g).1, fun N => nofun, fun c us => nofun⟩
  · exact ⟨_, (view_let m a hR h hh hv g).1, fun N => nofun, fun c us => nofun⟩
  · exact ⟨_, (view_proj m a hR h hh hv g).1, fun N => nofun, fun c us => nofun⟩

theorem rawSimple {dn : NIdx → Option ConLeche.Name} {m : Mem} {a₀ : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a₀ vis fe M eb) {h : Word} (hh : HW h)
    (c : Word) (hsc : ¬(tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0))
    (hb : ¬ rdW (m.arr64 CTL) (c + tierW h) ≤ idxW h)
    (hcg : (h >>> 28 = 0 ∧ c = 22) ∨ (h >>> 28 = 1 ∧ c = 26) ∨ (h >>> 28 = 2 ∧ c = 16) ∨
      (h >>> 28 = 4 ∧ c = 4) ∨ (h >>> 28 = 5 ∧ c = 28) ∨ (h >>> 28 = 6 ∧ c = 30) ∨
      (h >>> 28 = 7 ∧ c = 20) ∨ (h >>> 28 = 9 ∧ c = 32))
    (r : List Word) (hr : r.headD 0 = 0) : RawOut m a₀ h r := by
  obtain ⟨v, hv, hl, hc⟩ := view_other m a₀ hS.arena.1 h hh c ⟨hsc, by simpa using hb⟩ hcg
  exact RawOut.none (rawNatLit_run_other hv hl hc) hr

section refs9
variable (p : Prog)

theorem callW_rawNatLit (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb h : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (hh : HW h) (r : List Word) (m' : Mem)
    (hcall : callW p n "raw_nat_lit" [h] s₀.mem = some (r, m')) :
    m' = s₀.mem ∧ RawOut s₀.mem a₀ h r := by
  cases n with
  | zero => rw [callW_zero] at hcall; cases hcall
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (rawNatLit_spec p hp.toWhnfDeltaProg n s₀ h) hcall
  unfold rawNatLitW at hW
  by_cases hsc : tierW h ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0
  · rw [if_pos hsc] at hW; cases hW
  rw [if_neg hsc] at hW
  -- the tags whose arm only checks the bound
  have simple : ∀ (c : Word) (g : Prop) [Decidable g], g →
      (g → (h >>> 28 = 0 ∧ c = 22) ∨ (h >>> 28 = 1 ∧ c = 26) ∨ (h >>> 28 = 2 ∧ c = 16) ∨
        (h >>> 28 = 4 ∧ c = 4) ∨ (h >>> 28 = 5 ∧ c = 28) ∨ (h >>> 28 = 6 ∧ c = 30) ∨
        (h >>> 28 = 7 ∧ c = 20) ∨ (h >>> 28 = 9 ∧ c = 32)) →
      (if rdW (s₀.mem.arr64 CTL) (c + tierW h) ≤ idxW h then none else
        some ((0 : Word), (0 : Word), (0 : Word), s₀.mem)) =
        some (r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, s'.mem) →
      s'.mem = s₀.mem ∧ RawOut s₀.mem a₀ h r := by
    intro c g _ hg hcg hW'
    by_cases hb : rdW (s₀.mem.arr64 CTL) (c + tierW h) ≤ idxW h
    · rw [if_pos hb] at hW'; cases hW'
    rw [if_neg hb] at hW'
    simp only [Option.some.injEq, Prod.mk.injEq] at hW'
    obtain ⟨hf, -, -, hm⟩ := hW'
    exact ⟨hm.symm, rawSimple hC hh c hsc hb (hcg hg) r hf.symm⟩
  by_cases g0 : h >>> 28 = 0
  · rw [if_pos g0] at hW
    obtain ⟨h1, h2⟩ := simple 22 _ g0 (fun _ => Or.inl ⟨g0, rfl⟩) hW
    exact ⟨h1, h2⟩
  rw [if_neg g0] at hW
  by_cases g1 : h >>> 28 = 1
  · rw [if_pos g1] at hW
    obtain ⟨h1, h2⟩ := simple 26 _ g1 (fun _ => Or.inr (Or.inl ⟨g1, rfl⟩)) hW
    exact ⟨h1, h2⟩
  rw [if_neg g1] at hW
  by_cases g2 : h >>> 28 = 2
  · rw [if_pos g2] at hW
    obtain ⟨h1, h2⟩ := simple 16 _ g2 (fun _ => Or.inr (Or.inr (Or.inl ⟨g2, rfl⟩))) hW
    exact ⟨h1, h2⟩
  rw [if_neg g2] at hW
  by_cases g3 : h >>> 28 = 3
  · rw [if_pos g3] at hW
    by_cases hb : rdW (s₀.mem.arr64 CTL) (18 + tierW h) ≤ idxW h
    · rw [if_pos hb] at hW; cases hW
    rw [if_neg hb] at hW
    cases h1 : callW p n "pin_at" [2] s₀.mem with
    | none => rw [h1] at hW; cases hW
    | some q₁ =>
    obtain ⟨r₁, m₁⟩ := q₁
    rw [h1] at hW
    obtain ⟨hm1, -, -, hr₁⟩ := callW_pinAt p hp.pinAt n s₀.mem 2 r₁ m₁ h1
    subst m₁
    dsimp only at hW
    cases h2 : callW p n "pin_word" [52] s₀.mem with
    | none => rw [h2] at hW; cases hW
    | some q₂ =>
    obtain ⟨r₂, m₂⟩ := q₂
    rw [h2] at hW
    obtain ⟨hm2, -, hr₂⟩ := callW_pinWord p hp.pinWord n s₀.mem 52 r₂ m₂ h2
    subst m₂
    dsimp only at hW
    simp only [show (2 : Word).toNat = 2 from rfl, show (52 : Word).toNat = 52 from rfl] at hr₁ hr₂
    have hvOK : viewOK s₀.mem h 18 := ⟨hsc, by simpa using hb⟩
    obtain ⟨n_, us_, hview, hn, hu, hnl, hul⟩ := view_const_words s₀.mem a₀ hC.arena.1 h hh hvOK g3
    have hrun := rawNatLit_run_const hC.pins hview
    rw [hn, hu] at hrun
    have hbool : ((decI (rdW (s₀.mem.arr64 CREC) (idxW h * 4 + tierW h * 2)) : NIdx) ==
            decI (pinW s₀.mem 3) &&
            (decI (rdW (s₀.mem.arr64 CREC) (idxW h * 4 + tierW h * 2 + 1)) : LsIdx) ==
              decI (pinW s₀.mem 52)) =
        decide (rdW (s₀.mem.arr64 CREC) (idxW h * 4 + tierW h * 2) = r₁.headD 0 ∧
          rdW (s₀.mem.arr64 CREC) (idxW h * 4 + tierW h * 2 + 1) = r₂.headD 0) := by
      rw [decI_beq _ _ hnl (hC.pins.names_lt 2 (by decide)), decI_beq _ _ hul hC.pins.lv_lt.1,
        Bool.decide_and, hr₁, hr₂]
    rw [hbool] at hrun
    by_cases hcond : rdW (s₀.mem.arr64 CREC) (idxW h * 4 + tierW h * 2) = r₁.headD 0 ∧
        rdW (s₀.mem.arr64 CREC) (idxW h * 4 + tierW h * 2 + 1) = r₂.headD 0
    · rw [if_pos hcond] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨hf, ho, hcn, hm⟩ := hW
      have hpv : pv (s₀.mem.arr64 POOL) (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat = 0 := by
        rw [← hcn]; rfl
      refine ⟨hm.symm, ?_, ?_, ?_⟩
      · unfold rawDec
        rw [if_neg (by rw [← hf]; decide), hpv]
        simpa [hcond] using hrun
      · unfold ResH HW; rw [← hf]; decide
      · intro _
        refine ⟨?_, ?_⟩
        · unfold SliceOK; rw [← ho, ← hcn, rdW_ctl_top']; simp
        · intro hpos; rw [← hcn] at hpos; simp at hpos
    · rw [if_neg hcond] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨hf, ho, hcn, hm⟩ := hW
      refine ⟨hm.symm, RawOut.none ?_ hf.symm⟩
      rw [decide_eq_false hcond] at hrun
      simpa only [Bool.false_eq_true, ↓reduceIte] using hrun
  rw [if_neg g3] at hW
  by_cases g4 : h >>> 28 = 4
  · rw [if_pos g4] at hW
    obtain ⟨h1, h2⟩ := simple 4 _ g4 (fun _ => Or.inr (Or.inr (Or.inr (Or.inl ⟨g4, rfl⟩)))) hW
    exact ⟨h1, h2⟩
  rw [if_neg g4] at hW
  by_cases g5 : h >>> 28 = 5
  · rw [if_pos g5] at hW
    obtain ⟨h1, h2⟩ := simple 28 _ g5
      (fun _ => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨g5, rfl⟩))))) hW
    exact ⟨h1, h2⟩
  rw [if_neg g5] at hW
  by_cases g6 : h >>> 28 = 6
  · rw [if_pos g6] at hW
    obtain ⟨h1, h2⟩ := simple 30 _ g6
      (fun _ => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨g6, rfl⟩)))))) hW
    exact ⟨h1, h2⟩
  rw [if_neg g6] at hW
  by_cases g7 : h >>> 28 = 7
  · rw [if_pos g7] at hW
    obtain ⟨h1, h2⟩ := simple 20 _ g7
      (fun _ => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨g7, rfl⟩))))))) hW
    exact ⟨h1, h2⟩
  rw [if_neg g7] at hW
  by_cases g8 : h >>> 28 = 8
  · rw [if_pos g8] at hW
    by_cases hb : rdW (s₀.mem.arr64 CTL) (2 + tierW h) ≤ idxW h
    · rw [if_pos hb] at hW; cases hW
    rw [if_neg hb] at hW
    have hvOK : viewOK s₀.mem h 2 := ⟨hsc, by simpa using hb⟩
    obtain ⟨hk0, hk1⟩ := view_lit_nat s₀.mem a₀ hC.arena.1 h hh hvOK g8
    by_cases hk : rdW (s₀.mem.arr64 REC) (idxW h * 8 + tierW h * 4) = 0
    · rw [if_pos hk] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨hf, ho, hcn, hm⟩ := hW
      obtain ⟨N, hview, hnat⟩ := hk0 hk
      obtain ⟨-, hsl, hnorm, hpv, -⟩ := hnat
      refine ⟨hm.symm, ?_, ?_, ?_⟩
      · unfold rawDec
        rw [if_neg (by rw [← hf]; decide), ← ho, ← hcn, hpv]
        exact rawNatLit_run_lit hview
      · unfold ResH HW; rw [← hf]; decide
      · intro _
        refine ⟨?_, ?_⟩
        · unfold SliceOK; rw [← ho, ← hcn]; exact hsl
        · rw [← ho, ← hcn]; exact hnorm
    · rw [if_neg hk] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨hf, ho, hcn, hm⟩ := hW
      obtain ⟨s, hview⟩ := hk1 hk
      exact ⟨hm.symm, RawOut.none (rawNatLit_run_other hview (fun N => nofun) (fun c us => nofun))
        hf.symm⟩
  rw [if_neg g8] at hW
  by_cases g9 : h >>> 28 ≠ 9
  · rw [if_pos g9] at hW; cases hW
  rw [if_neg g9] at hW
  have g9' : h >>> 28 = 9 := by simpa using g9
  obtain ⟨h1, h2⟩ := simple 32 _ g9'
    (fun _ => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨g9', rfl⟩))))))) hW
  exact ⟨h1, h2⟩

/-- **`raw_nat_lit` refines `rawNatLit?`**: the result is a flag and the literal's POOL slice
(`pv`), read-only. -/
theorem rawNatLit_refines' (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb h : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (hh : HW h) :
    CoreSpec p n "raw_nat_lit" [h] (rawNatLit? (decE h))
      (fun r => if r.headD 0 = 0 then none
        else some (pv (s₀.mem.arr64 POOL) (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat))
      s₀ a₀ dn vis fe MM eb := by
  apply CoreSpec.of_call
  intro r m' hcall
  obtain ⟨rfl, hrun, hres, -⟩ := callW_rawNatLit p hp n s₀ a₀ dn vis fe MM eb h hC hh r m' hcall
  exact CRef.core (m' := s₀.mem) (CRef.pure hC _ hrun rfl hres)

end refs9


/-! ## `nat_lit_to_ctor` -/

/-- The model of `nat_lit_to_ctor`. -/
def natLitToCtorW (p : Prog) (n : Nat) (m : Mem) (o cnt : Word) : Option (Word × Mem) :=
  if cnt = 0 then
    match callW p n "pin_at" [2] m with
    | none => none
    | some (r₁, m₁) =>
      match callW p n "const_e" [r₁.headD 0] m₁ with
      | none => none
      | some (r₂, m₂) => some (r₂.headD 0, m₂)
  else
    match callW p n "pin_at" [3] m with
    | none => none
    | some (r₁, m₁) =>
      match callW p n "const_e" [r₁.headD 0] m₁ with
      | none => none
      | some (r₂, m₂) =>
        match callW p n "nat_pred_lit" [o, cnt] m₂ with
        | none => none
        | some (r₃, m₃) =>
          match callW p n "mk_app" [r₂.headD 0, r₃.headD 0] m₃ with
          | none => none
          | some (r₄, m₄) => some (r₄.headD 0, m₄)

theorem natLitToCtor_spec (p : Prog) (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St) (o cnt : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nat_lit_to_ctor" [o, cnt]
    ⦃fun r s' => LocEq s' s₀ ∧ natLitToCtorW p n s₀.mem o cnt = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.natLitToCtor]
  simp only [callFn, natLitToCtorL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "pin_at", callW_spec p n "const_e", callW_spec p n "nat_pred_lit",
      callW_spec p n "mk_app"] <;>
    finish (gen := 30) [natLitToCtorW]


/-! ## Frames of the `Nat` functions -/

theorem CoreS.of_nat {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState}
    {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb)
    (hD : ArenaD m' a') (hcpl : cpl a' = cpl a) (hf : MemFrame natA natC m m') :
    CoreS dn m' a' vis fe M eb :=
  hS.arena_frame hD hcpl hf
    (fun b hb => by
      simp only [natA, List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide)
    (by simp [natA, POOL, CREC, CSLOT])
    (fun b hb => by
      simp only [natA, List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide)
    (fun x hx => by
      simp only [natC, List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide)
    (fun x hx => by
      simp only [natC, List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide)

theorem StackKept.of_nat_frame {m m' : Mem} (hf : MemFrame natA natC m m') : StackKept m m' := by
  have hspn : m'.arr64 SPN = m.arr64 SPN :=
    hf.1 SPN (by simp [natA, POOL, CREC, CSLOT, SPN]) (by decide)
  have h136 : rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 := hf.2.1 136 (by simp [natC])
  exact ⟨by simp only [spTop, h136], by rw [hspn], fun i _ => by simp only [spW, hspn]⟩

theorem keeps_cpl_natPredArm (a : Nat) : Keeps cpl (natPredArm a) := by
  unfold natPredArm
  exact Keeps.bind (keeps_cpl_internLit _) (fun _ => Keeps.pure _)

section refs10
variable (p : Prog)

theorem callW_natFrame (hc : closedA p natA natC natFns = true) (f : FnName) (hf : f ∈ natFns)
    (n : Nat) (vs : List Word) (m : Mem) (r : List Word) (m' : Mem)
    (h : callW p n f vs m = some (r, m')) : MemFrame natA natC m m' := by
  obtain ⟨s', rfl, hfr⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (invoke_memFrame hc n hf vs ⟨m, Locals.init []⟩) h
  exact hfr.1

theorem natPredLit_inst (hp : WhnfDeltaProg' p) : InternSpec p ArenaD :=
  fun a₀ n s₀ o l hA hq hn => internLit_refinesD p hp.litHash' hp.limbsEq' hp.litMatch' hp.litFind'
    hp.litPush' hp.internLit a₀ n s₀ o l hA hq hn

theorem callW_natPredLit (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb o cnt : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (hs : SliceOK s₀.mem o cnt) (r : List Word) (m' : Mem)
    (h : callW p n "nat_pred_lit" [o, cnt] s₀.mem = some (r, m')) :
    AM.ok (natPredArm (pv (s₀.mem.arr64 POOL) o.toNat cnt.toNat)) a₀ ∧
    CoreS dn m' (AM.st (natPredArm (pv (s₀.mem.arr64 POOL) o.toNat cnt.toNat)) a₀) vis fe MM eb ∧
    AM.res (natPredArm (pv (s₀.mem.arr64 POOL) o.toNat cnt.toNat)) a₀ = some (decE (r.headD 0)) ∧
    MemFrame natA natC s₀.mem m' := by
  obtain ⟨s', rfl, -, hok, hD, hres⟩ := triple_of_callW
    (natPredLit_refines p ArenaD (fun _ _ h => h.1.lit.1)
      (fun m m' a hA hg => ArenaD.grow m m' hg a hA) (natPredLit_inst p hp) hp.natLimb' hp.subBorrow'
      hp.natTrim' hp.natSub hp.predLit n s₀ a₀ hC.arena o cnt hs) h
  have hfr := callW_natFrame p hp.natClosed "nat_pred_lit" (by decide +kernel) n _ _ _ _ h
  exact ⟨hok, hC.of_nat hD (Keeps.run (keeps_cpl_natPredArm _) (AM.run_of_ok _ _ hok)) hfr, hres, hfr⟩

end refs10


theorem natLitToConstructor_zero_run {m : Mem} {a : AState} (h : PinsFull m a.pins) :
    (natLitToConstructor 0).run a = (constE (decI (pinW m 3))).run a := by
  simp only [natLitToConstructor, StateT.run_bind, pinNatZero_run h, except_ok_bind]

theorem natLitToConstructor_succ_run {m : Mem} {a a₁ a₂ a₃ : AState} (h : PinsFull m a.pins)
    (k : Nat) (sc l f : EIdx)
    (h1 : (constE (decI (pinW m 4))).run a = .ok (sc, a₁))
    (h2 : (internE (.lit (.natVal k))).run a₁ = .ok (l, a₂))
    (h3 : (internE (.app sc l)).run a₂ = .ok (f, a₃)) :
    (natLitToConstructor (k + 1)).run a = .ok (f, a₃) := by
  simp only [natLitToConstructor, StateT.run_bind, pinNatSucc_run h, except_ok_bind, h1, h2, h3]

theorem natPredArm_succ_run {a₁ a₂ : AState} {k : Nat} {x : EIdx}
    (h : (natPredArm (k + 1)).run a₁ = .ok (some x, a₂)) :
    (internE (.lit (.natVal k))).run a₁ = .ok (x, a₂) := by
  have e : (natPredArm (k + 1)).run a₁ =
      Except.map (fun q => (some q.1, q.2)) ((internE (.lit (.natVal k))).run a₁) := by
    simp only [natPredArm, Nat.add_sub_cancel, StateT.run_bind]
    cases (internE (.lit (.natVal k))).run a₁ <;> rfl
  rw [e] at h
  cases hh : (internE (.lit (.natVal k))).run a₁ with
  | error e => rw [hh] at h; cases h
  | ok q =>
    rw [hh] at h
    simp only [Except.map, Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨x', a'⟩ := q
    simp only at h1 h2
    rw [h1, h2]

section refs11
variable (p : Prog)

theorem natLitToCtor_refines' (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb o cnt : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (hs : SliceOK s₀.mem o cnt)
    (hnorm : Norm (s₀.mem.arr64 POOL) o.toNat cnt.toNat) :
    CoreSpec p n "nat_lit_to_ctor" [o, cnt]
      (natLitToConstructor (pv (s₀.mem.arr64 POOL) o.toNat cnt.toNat)) decH s₀ a₀ dn vis fe MM eb := by
  apply CoreSpec.of_call
  intro r m' hcall
  cases n with
  | zero => rw [callW_zero] at hcall; cases hcall
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (natLitToCtor_spec p hp.toWhnfDeltaProg n s₀ o cnt) hcall
  unfold natLitToCtorW at hW
  by_cases hc0 : cnt = 0
  · rw [if_pos hc0] at hW
    cases h1 : callW p n "pin_at" [2] s₀.mem with
    | none => rw [h1] at hW; cases hW
    | some q₁ =>
    obtain ⟨r₁, m₁⟩ := q₁
    rw [h1] at hW
    obtain ⟨hm1, -, -, hr₁⟩ := callW_pinAt p hp.pinAt n s₀.mem 2 r₁ m₁ h1
    subst m₁
    dsimp only at hW
    have hnt : HW (r₁.headD 0) := by rw [hr₁]; exact hC.pins.names_lt 2 (by decide)
    cases h2 : callW p n "const_e" [r₁.headD 0] s₀.mem with
    | none => rw [h2] at hW; cases hW
    | some q₂ =>
    obtain ⟨r₂, m₂⟩ := q₂
    rw [h2] at hW
    dsimp only at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    obtain ⟨hok, hS, hres, hfr, hhw⟩ := callW_constE p hp n s₀ a₀ dn vis fe MM eb _ hC hnt r₂ m₂ h2
    have hr₁' : r₁.headD 0 = pinW s₀.mem 3 := by
      simp only [show (2 : Word).toNat = 2 from rfl] at hr₁; exact hr₁
    rw [hr₁'] at hok hS hres
    have hpv : pv (s₀.mem.arr64 POOL) o.toNat cnt.toNat = 0 := by subst hc0; rfl
    rw [hpv]
    rw [← hm]
    refine ⟨?_, ?_, ?_, ?_⟩
    · obtain ⟨hok', -, -⟩ := AM.of_run_ok _ _ _ _ ((natLitToConstructor_zero_run hC.pins).trans
        (AM.run_of_ok _ _ hok)); exact hok'
    · obtain ⟨-, hst', -⟩ := AM.of_run_ok _ _ _ _ ((natLitToConstructor_zero_run hC.pins).trans
        (AM.run_of_ok _ _ hok))
      rw [hst']; exact ⟨MM, hS, KeptAll.refl _ _, StackKept.of_const_frame hfr⟩
    · obtain ⟨-, -, hres'⟩ := AM.of_run_ok _ _ _ _ ((natLitToConstructor_zero_run hC.pins).trans
        (AM.run_of_ok _ _ hok))
      rw [hres', hres]; simp only [decH, ← hr]
    · unfold ResH; rw [← hr]; exact hhw
  rw [if_neg hc0] at hW
  have hpos : 0 < cnt.toNat := by
    rcases Nat.eq_zero_or_pos cnt.toNat with h0 | h0
    · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hc0
    · exact h0
  obtain ⟨k, hk⟩ : ∃ k, pv (s₀.mem.arr64 POOL) o.toNat cnt.toNat = k + 1 :=
    ⟨pv (s₀.mem.arr64 POOL) o.toNat cnt.toNat - 1, by have := pv_pos_of_norm _ _ _ hnorm hpos; omega⟩
  rw [hk]
  cases h1 : callW p n "pin_at" [3] s₀.mem with
  | none => rw [h1] at hW; cases hW
  | some q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  rw [h1] at hW
  obtain ⟨hm1, -, -, hr₁⟩ := callW_pinAt p hp.pinAt n s₀.mem 3 r₁ m₁ h1
  subst m₁
  dsimp only at hW
  have hnt : HW (r₁.headD 0) := by rw [hr₁]; exact hC.pins.names_lt 3 (by decide)
  cases h2 : callW p n "const_e" [r₁.headD 0] s₀.mem with
  | none => rw [h2] at hW; cases hW
  | some q₂ =>
  obtain ⟨r₂, m₂⟩ := q₂
  rw [h2] at hW
  dsimp only at hW
  obtain ⟨hok, hS, hres, hfr, hhw⟩ := callW_constE p hp n s₀ a₀ dn vis fe MM eb _ hC hnt r₂ m₂ h2
  have hr₁' : r₁.headD 0 = pinW s₀.mem 4 := by
    simp only [show (3 : Word).toNat = 3 from rfl] at hr₁; exact hr₁
  rw [hr₁'] at hok hS hres
  have hPool : m₂.arr64 POOL = s₀.mem.arr64 POOL :=
    hfr.arr_eq POOL (by simp [CREC, CSLOT, POOL]) (by decide)
  have hTop : m₂.top = s₀.mem.top := by
    rw [← rdW_ctl_top', ← rdW_ctl_top']; exact hfr.2.1 0 (by simp)
  have hs₂ : SliceOK m₂ o cnt := by unfold SliceOK; rw [hTop]; exact hs
  cases h3 : callW p n "nat_pred_lit" [o, cnt] m₂ with
  | none => rw [h3] at hW; cases hW
  | some q₃ =>
  obtain ⟨r₃, m₃⟩ := q₃
  rw [h3] at hW
  dsimp only at hW
  obtain ⟨hok3, hS3, hres3, hfr3⟩ := callW_natPredLit p hp n ⟨m₂, Locals.init []⟩ _ dn vis fe MM eb o cnt
    hS hs₂ r₃ m₃ h3
  rw [hPool, hk] at hok3 hS3 hres3
  cases h4 : callW p n "mk_app" [r₂.headD 0, r₃.headD 0] m₃ with
  | none => rw [h4] at hW; cases hW
  | some q₄ =>
  obtain ⟨r₄, m₄⟩ := q₄
  rw [h4] at hW
  dsimp only at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hm⟩ := hW
  obtain ⟨hok4, hD4, hres4, hfr4, hhw4⟩ := callW_mkApp p hp.spine n ⟨m₃, Locals.init []⟩ _ hS3.arena
    (r₂.headD 0) (r₃.headD 0) r₄ m₄ h4
  -- the twin runs
  have e1 : (constE (decI (pinW s₀.mem 4))).run a₀ =
      .ok (decE (r₂.headD 0), AM.st (constE (decI (pinW s₀.mem 4))) a₀) := by
    rw [AM.run_of_ok _ _ hok, hres]; rfl
  have e2 : (internE (.lit (.natVal k))).run (AM.st (constE (decI (pinW s₀.mem 4))) a₀) =
      .ok (decE (r₃.headD 0), AM.st (natPredArm (k + 1)) (AM.st (constE (decI (pinW s₀.mem 4))) a₀)) :=
    natPredArm_succ_run (by rw [AM.run_of_ok _ _ hok3, hres3])
  have e3 : (internE (.app (decE (r₂.headD 0)) (decE (r₃.headD 0)))).run
      (AM.st (natPredArm (k + 1)) (AM.st (constE (decI (pinW s₀.mem 4))) a₀)) =
      .ok (decE (r₄.headD 0), AM.st (internE (.app (decE (r₂.headD 0)) (decE (r₃.headD 0))))
        (AM.st (natPredArm (k + 1)) (AM.st (constE (decI (pinW s₀.mem 4))) a₀))) := by
    rw [AM.run_of_ok _ _ hok4, hres4]
  have hz := natLitToConstructor_succ_run hC.pins k _ _ _ e1 e2 e3
  obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
  refine ⟨hok', ?_, ?_, ?_⟩
  · rw [hst', ← hm]
    refine ⟨MM, hS3.of_app hD4 (Keeps.run (keeps_cpl_internApp _ _) (AM.run_of_ok _ _ hok4)) hfr4,
      KeptAll.refl _ _, ?_⟩
    exact ((StackKept.of_const_frame hfr).trans (StackKept.of_nat_frame hfr3)).trans
      (StackKept.of_app_frame hfr4)
  · rw [hres', decH, ← hr]
  · unfold ResH; rw [← hr]; exact hhw4

end refs11


/-! ## `lit_to_ctor_if_nat` -/

/-- The model of `lit_to_ctor_if_nat`. -/
def litToCtorIfNatW (p : Prog) (n : Nat) (m : Mem) (vis h : Word) : Option (Word × Mem) :=
  if h >>> 28 ≠ 8 then some (h, m)
  else if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if rdW (m.arr64 CTL) (2 + tierW h) ≤ idxW h then none
  else if rdW (m.arr64 REC) (idxW h * 8 + tierW h * 4) ≠ 0 then some (h, m)
  else match callW p n "nat_lit_supported" [vis] m with
    | none => none
    | some (r₁, m₁) =>
      if r₁.headD 0 = 0 then some (h, m₁)
      else match callW p n "nat_lit_to_ctor" [rdW (m₁.arr64 REC) (idxW h * 8 + tierW h * 4 + 1),
          rdW (m₁.arr64 REC) (idxW h * 8 + tierW h * 4 + 2)] m₁ with
        | none => none
        | some (r₂, m₂) => some (r₂.headD 0, m₂)

theorem litToCtorIfNat_spec (p : Prog) (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St) (vis h : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "lit_to_ctor_if_nat" [vis, h]
    ⦃fun r s' => LocEq s' s₀ ∧ litToCtorIfNatW p n s₀.mem vis h = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.litToCtorIfNat]
  simp only [callFn, litToCtorIfNatL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "nat_lit_supported", callW_spec p n "nat_lit_to_ctor"] <;>
    finish (gen := 30) [litToCtorIfNatW, tierW, idxW]


theorem litToCtor_run_notlit (fe : IFEnv) (a : AState) (h : Word) (hh : HW h) (hg : h >>> 28 ≠ 8) :
    (litToCtorIfNat fe (decE h)).run a = .ok (decE h, a) := by
  have ht : ((decE h).tag == ETag.lit) = false := by rw [decE_lit_tag h hh]; simp [hg]
  simp [litToCtorIfNat, ht, StateT.run_pure]
  rfl

theorem litToCtor_run_str (fe : IFEnv) (a : AState) (h : Word) (hh : HW h) (hg : h >>> 28 = 8)
    (s : String) (hv : a.store.view (decE h) = some (.lit (.strVal s))) :
    (litToCtorIfNat fe (decE h)).run a = .ok (decE h, a) := by
  have ht : ((decE h).tag == ETag.lit) = true := by rw [decE_lit_tag h hh]; simp [hg]
  simp [litToCtorIfNat, ht, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]
  rfl

theorem litToCtor_run_unsup (fe : IFEnv) (a a₁ : AState) (h : Word) (hh : HW h)
    (hg : h >>> 28 = 8) (N : Nat) (hv : a.store.view (decE h) = some (.lit (.natVal N)))
    (hs : (natLitSupported fe).run a = .ok (false, a₁)) :
    (litToCtorIfNat fe (decE h)).run a = .ok (decE h, a₁) := by
  have ht : ((decE h).tag == ETag.lit) = true := by rw [decE_lit_tag h hh]; simp [hg]
  simp [litToCtorIfNat, ht, StateT.run_bind, view_run _ _ _ hv, except_ok_bind, hs]
  rfl

theorem litToCtor_run_sup (fe : IFEnv) (a a₁ a₂ : AState) (h : Word) (hh : HW h)
    (hg : h >>> 28 = 8) (N : Nat) (hv : a.store.view (decE h) = some (.lit (.natVal N)))
    (hs : (natLitSupported fe).run a = .ok (true, a₁)) (x : EIdx)
    (hc : (natLitToConstructor N).run a₁ = .ok (x, a₂)) :
    (litToCtorIfNat fe (decE h)).run a = .ok (x, a₂) := by
  have ht : ((decE h).tag == ETag.lit) = true := by rw [decE_lit_tag h hh]; simp [hg]
  simp [litToCtorIfNat, ht, StateT.run_bind, view_run _ _ _ hv, except_ok_bind, hs, hc]

section refs12
variable (p : Prog)

theorem litToCtorIfNat_refines' (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb h : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (hh : HW h) :
    CoreSpec p n "lit_to_ctor_if_nat" [vis, h] (litToCtorIfNat fe (decE h)) decH s₀ a₀ dn vis fe MM
      eb := by
  apply CoreSpec.of_call
  intro r m' hcall
  cases n with
  | zero => rw [callW_zero] at hcall; cases hcall
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (litToCtorIfNat_spec p hp.toWhnfDeltaProg n s₀ vis h) hcall
  unfold litToCtorIfNatW at hW
  by_cases hg : h >>> 28 ≠ 8
  · rw [if_pos hg] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    rw [← hm]
    exact (CRef.pure hC _ (litToCtor_run_notlit fe a₀ h hh hg) (by simp only [decH, ← hr]) (by
      unfold ResH; rw [← hr]; exact hh)).core
  rw [if_neg hg] at hW
  have hg8 : h >>> 28 = 8 := by simpa using hg
  by_cases hsc : tierW h ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0
  · rw [if_pos hsc] at hW; cases hW
  rw [if_neg hsc] at hW
  by_cases hbd : rdW (s₀.mem.arr64 CTL) (2 + tierW h) ≤ idxW h
  · rw [if_pos hbd] at hW; cases hW
  rw [if_neg hbd] at hW
  have hvOK : viewOK s₀.mem h 2 := ⟨hsc, by simpa using hbd⟩
  obtain ⟨hk0, hk1⟩ := view_lit_nat s₀.mem a₀ hC.arena.1 h hh hvOK hg8
  by_cases hk : rdW (s₀.mem.arr64 REC) (idxW h * 8 + tierW h * 4) ≠ 0
  · rw [if_pos hk] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    rw [← hm]
    obtain ⟨s, hv⟩ := hk1 hk
    exact (CRef.pure hC _ (litToCtor_run_str fe a₀ h hh hg8 s hv) (by simp only [decH, ← hr]) (by
      unfold ResH; rw [← hr]; exact hh)).core
  rw [if_neg hk] at hW
  have hk' : rdW (s₀.mem.arr64 REC) (idxW h * 8 + tierW h * 4) = 0 := by simpa using hk
  obtain ⟨N, hview, hnat⟩ := hk0 hk'
  obtain ⟨-, hsl, hnorm, hpv, -⟩ := hnat
  cases h1 : callW p n "nat_lit_supported" [vis] s₀.mem with
  | none => rw [h1] at hW; cases hW
  | some q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  rw [h1] at hW
  dsimp only at hW
  obtain ⟨hok1, hS1, hres1, hfr1, hrh1⟩ := callW_natLitSupported p hp n s₀ a₀ dn vis fe MM eb hC r₁ m₁ h1
  by_cases hs0 : r₁.headD 0 = 0
  · rw [if_pos hs0] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    rw [← hm]
    have hsup : (natLitSupported fe).run a₀ = .ok (false, AM.st (natLitSupported fe) a₀) := by
      have := AM.run_of_ok _ _ hok1
      rw [hres1] at this
      have hdb : decBool r₁ = false := by simp only [decBool, hs0]; rfl
      rwa [hdb] at this
    have hz := litToCtor_run_unsup fe a₀ _ h hh hg8 N hview hsup
    obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
    refine CRef.core (m' := m₁) ⟨hok', by rw [hst']; exact hS1, ?_, hfr1, ?_⟩
    · rw [hres']; simp only [decH, ← hr]
    · unfold ResH; rw [← hr]; exact hh
  rw [if_neg hs0] at hW
  have hsup : (natLitSupported fe).run a₀ = .ok (true, AM.st (natLitSupported fe) a₀) := by
    have := AM.run_of_ok _ _ hok1
    rw [hres1] at this
    have hdb : decBool r₁ = true := by simp only [decBool, bne_iff_ne, ne_eq]; exact hs0
    rwa [hdb] at this
  have hE : m₁.arr64 REC = s₀.mem.arr64 REC :=
    hfr1.arr_eq REC (by simp [CREC, CSLOT, REC, POOL]) (by decide)
  have hPool : m₁.arr64 POOL = s₀.mem.arr64 POOL :=
    hfr1.arr_eq POOL (by simp [CREC, CSLOT, POOL]) (by decide)
  have hTop : m₁.top = s₀.mem.top := by
    rw [← rdW_ctl_top', ← rdW_ctl_top']; exact hfr1.2.1 0 (by simp)
  rw [hE] at hW
  cases h2 : callW p n "nat_lit_to_ctor" [rdW (s₀.mem.arr64 REC) (idxW h * 8 + tierW h * 4 + 1),
      rdW (s₀.mem.arr64 REC) (idxW h * 8 + tierW h * 4 + 2)] m₁ with
  | none => rw [h2] at hW; cases hW
  | some q₂ =>
  obtain ⟨r₂, m₂⟩ := q₂
  rw [h2] at hW
  dsimp only at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hm⟩ := hW
  have hs₁ : SliceOK m₁ (rdW (s₀.mem.arr64 REC) (idxW h * 8 + tierW h * 4 + 1))
      (rdW (s₀.mem.arr64 REC) (idxW h * 8 + tierW h * 4 + 2)) := by
    unfold SliceOK; rw [hTop]; exact hsl
  have hn₁ : Norm (m₁.arr64 POOL) (rdW (s₀.mem.arr64 REC) (idxW h * 8 + tierW h * 4 + 1)).toNat
      (rdW (s₀.mem.arr64 REC) (idxW h * 8 + tierW h * 4 + 2)).toNat := by rw [hPool]; exact hnorm
  have hctor := natLitToCtor_refines' p hp n ⟨m₁, Locals.init []⟩ _ dn vis fe MM eb _ _ hS1 hs₁ hn₁
  obtain ⟨hok2, hA2, hres2, hrw2⟩ := CoreSpec.of_callW hctor h2
  have hc2 := AM.run_of_ok _ _ hok2
  rw [hres2] at hc2
  dsimp only at hc2 hA2 hrw2
  rw [hPool, hpv] at hc2
  rw [hPool, hpv] at hA2
  have hz := litToCtor_run_sup fe a₀ _ _ h hh hg8 N hview hsup _ hc2
  obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
  refine ⟨hok', ?_, ?_, ?_⟩
  · rw [hst', ← hm]
    exact CoreAfter.comp (KeptAll.refl _ _) (StackKept.of_const_frame hfr1) hA2
  · rw [hres']; simp only [decH, ← hr]
  · unfold ResH; rw [← hr]; exact hrw2

end refs12


/-! ## `const_val_at` -/

/-- `constValC` gains an entry (copy of `CoreS.set_wh`, at `cvSch`: array 103, `CTL` 110/111). -/
theorem CoreS.set_cv {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) (nm us x : Word)
    (hn : HW nm) (hu : HW us) (hx : HW x) (hs : msetG cvSch m nm us x = some m') :
    CoreS dn m' { a with caches := { a.caches with
        constValC := a.caches.constValC.insert (decI nm, decI us) (decE x) } } vis fe M eb ∧
      StackKept m m' := by
  have hf : MemFrame [103] [111] m m' :=
    msetG_frame cvSch (coreSch_wf _ _ (by decide) (by decide)) m m' _ _ x hs
  have hq := memoRV_set cvSch (coreSch_wf _ _ (by decide) (by decide)) pairKey VH
    (fun _ _ _ _ _ h => h) m a.caches.constValC hS.core.cv nm us x ⟨hn, hu⟩ (decE x) ⟨rfl, hx⟩ m' hs
  have fr : ∀ {κ ν : Type} [BEq κ] [Hashable κ] (S : MemoSch) (K : MemoKey κ) (dv : Word → ν)
      (mp : Std.HashMap κ ν), S.WF → S.arr ≠ 103 → S.cs ≠ 111 → MemoRG S K dv m mp →
      MemoRG S K dv m' mp :=
    fun S K dv mp hS' h1 h2 hR =>
      memoRV_frame S hS' K _ [103] [111] (by simpa using h1) (by simpa using h2) m m' hf
        (fun _ _ h => h) mp hR
  have mr : ∀ {κ ν : Type} [BEq κ] [Hashable κ] {S : MemoSch} {K : MemoKey (κ × Word)}
      {VR : Mem → Word → ν → Prop} {M₀ : Std.HashMap (κ × Word) ν} {t te : Std.HashMap κ ν}, S.WF →
      VConst VR → S.arr ≠ 103 → S.cs ≠ 111 → ModeR S K VR m M₀ eb t te →
      ModeR S K VR m' M₀ eb t te :=
    fun hS' hV h1 h2 h => h.frame hS' hV (by simpa using h1) (by simpa using h2) hf
  have frv : ∀ {κ : Type} [BEq κ] [Hashable κ] (S : MemoSch) (K : MemoKey κ)
      (mp : Std.HashMap κ EIdx), S.WF → S.arr ≠ 103 → S.cs ≠ 111 → MemoRV S K VH m mp →
      MemoRV S K VH m' mp :=
    fun S K mp hS' h1 h2 hR =>
      memoRV_frame S hS' K _ [103] [111] (by simpa using h1) (by simpa using h2) m m' hf
        (vh_const m m') mp hR
  have hspn : m'.arr64 SPN = m.arr64 SPN := hf.1 SPN (by simp [SPN]) (by decide)
  have h136 : rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 := hf.2.1 136 (by simp)
  refine ⟨⟨⟨ArenaR.caches_irrel _ (ArenaR.frame_ext [103] [111] (by simp) (by simp) m m' hf a
        hS.arena.1), DerR.of_store _ _ _ (DerR.frameM [103] [111] m m' hf (by simp) a hS.arena.2) rfl⟩,
      ⟨mr (coreSch_wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hS.core.wc,
        mr (coreSch_wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hS.core.wk,
        mr (coreSch_wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hS.core.wh,
        mr (coreSch_wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hS.core.inf,
        mr (coreSch_wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hS.core.io,
        mr (coreSch_wf _ _ (by decide) (by decide)) vb_const (by decide) (by decide) hS.core.de,
        hS.core.eb1,
        frv _ _ _ (coreSch_wf _ _ (by decide) (by decide)) (by decide) (by decide) hS.core.ct,
        hq,
        frv _ _ _ (coreSch_wf _ _ (by decide) (by decide)) (by decide) (by decide) hS.core.rr,
        fr _ _ _ _ (coreSch_wf _ _ (by decide) (by decide)) (by decide) (by decide) hS.core.lq,
        fr _ _ _ _ (coreSch_wf _ _ (by decide) (by decide)) (by decide) (by decide) hS.core.lsq⟩,
      hS.pins.congr (hf.1 PINS (by simp [PINS]) (by decide)),
      hS.env.frame (fun b hb => by simp at hb; subst hb; decide)
        (fun x hx => by simp at hx; subst hx; decide) hf,
      fun h l e => hS.readL h l e, fun h l e => hS.readLs h l e, hS.nwf,
      hf.2.2.1 EREC ▸ hS.erec, hf.2.2.1 SPN ▸ hS.spn⟩,
    by simp only [spTop, h136], by rw [hspn], fun i _ => by simp only [spW, hspn]⟩


/-- The model of `const_val_at`. -/
def constValAtW (p : Prog) (n : Nat) (m : Mem) (nm po pl value us : Word) : Option (Word × Mem) :=
  memoSlotW cvSch m nm us (callW p n "inst_lp" [po, pl, us, value] m)

theorem constValAt_spec (p : Prog) (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St)
    (nm po pl value us : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "const_val_at" [nm, po, pl, value, us]
    ⦃fun r s' => LocEq s' s₀ ∧ constValAtW p n s₀.mem nm po pl value us = some (r.headD 0, s'.mem);
      ⊤⦄ := by
  rw [invoke_eq _ hp.constValAt]
  simp only [callFn, constValAtL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec cvSch p _ hp.cvFind n, memoPutG_spec cvSch p _ hp.cvPut n,
      callW_spec p n "inst_lp"] <;>
    finish [constValAtW, memoSlotW_hit, memoSlotW_miss, msetG_eq, mvG]


theorem constValAt_run_hit (a : AState) (n : NIdx) (lps : List NIdx) (value : EIdx) (us : LsIdx)
    (r : EIdx) (hm : a.caches.constValC[(n, us)]? = some r) :
    (constValAt n lps value us).run a = .ok (r, a) := by
  simp only [constValAt, StateT.run_bind, StateT.run_get, pure_bind, hm]; rfl

theorem constValAt_run_miss (a a₁ : AState) (n : NIdx) (lps : List NIdx) (value : EIdx) (us : LsIdx)
    (r : EIdx) (hm : a.caches.constValC[(n, us)]? = none)
    (hI : (instLPFast coreWalkFuel lps us value).run a = .ok (r, a₁)) :
    (constValAt n lps value us).run a = .ok (r, { a₁ with caches := { a₁.caches with
      constValC := a₁.caches.constValC.insert (n, us) r } }) := by
  simp only [constValAt, StateT.run_bind, StateT.run_get, pure_bind, hm, hI, except_ok_bind]; rfl

section refs13
variable (p : Prog)

theorem callW_constValAt (hp : WhnfDeltaProg p) (hwc : WhnfCallees p) (n : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb nm po pl value us : Word) (lps : List NIdx) (hC : CoreS dn s₀.mem a₀ vis fe MM eb)
    (hnm : HW nm) (hv : HW value) (hu : HW us)
    (hlps : hslice? (s₀.mem.arr64 EREC) po.toNat pl.toNat = some lps) (r : List Word) (m' : Mem)
    (h : callW p n "const_val_at" [nm, po, pl, value, us] s₀.mem = some (r, m')) :
    CoreRef (constValAt (decI nm) lps (decE value) (decI us)) a₀ decH dn s₀.mem vis fe MM eb r m'
      ResH := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (constValAt_spec p hp n s₀ nm po pl value us) h
  unfold constValAtW memoSlotW at hW
  by_cases h0 : mfindG cvSch s₀.mem nm us = []
  · rw [if_pos h0] at hW; cases hW
  rw [if_neg h0] at hW
  have hf := memoRV_findP (k₁ := .name) (k₂ := .levels) hC.core.cv nm us hnm hu h0
  by_cases h1 : (mfindG cvSch s₀.mem nm us).headD 0 ≠ 0
  · rw [if_pos h1] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    rw [← hm]
    obtain ⟨hhit, hbd⟩ := hf.1 h1
    refine (CRef.pure hC _ (constValAt_run_hit a₀ _ _ _ _ _ hhit) ?_ ?_).core
    · simp only [decH, ← hr]
    · unfold ResH; rw [← hr]; exact hbd
  rw [if_neg h1] at hW
  have hmiss := hf.2 (by simpa using h1)
  cases hcall : callW p n "inst_lp" [po, pl, us, value] s₀.mem with
  | none => rw [hcall] at hW; cases hW
  | some q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  rw [hcall] at hW
  dsimp only at hW
  obtain ⟨hok, ⟨M', hS₁, hK₁, hSt₁⟩, hres, hrw⟩ :=
    CoreSpec.of_callW (hwc.instLP n ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe MM eb po pl us value lps hC hv
      hu hlps) hcall
  cases hset : msetG cvSch m₁ nm us (r₁.headD 0) with
  | none => rw [hset] at hW; cases hW
  | some m₂ =>
  rw [hset] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hm⟩ := hW
  have hrun := AM.run_of_ok _ _ hok
  rw [hres] at hrun
  have hz := constValAt_run_miss a₀ _ (decI nm) lps (decE value) (decI us) _ hmiss hrun
  obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
  obtain ⟨hS₂, hSt₂⟩ := hS₁.set_cv nm us (r₁.headD 0) hnm hu hrw hset
  refine ⟨hok', ?_, ?_, ?_⟩
  · rw [hst', ← hm]
    exact ⟨M', hS₂, hK₁, hSt₁.trans hSt₂⟩
  · rw [hres']; simp only [decH, ← hr]
  · unfold ResH; rw [← hr]; exact hrw

theorem constValAt_refines' (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb nm po pl value us : Word) (lps : List NIdx)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (hnm : HW nm) (hv : HW value) (hu : HW us)
    (hwc : WhnfCallees p) (hlps : hslice? (s₀.mem.arr64 EREC) po.toNat pl.toNat = some lps) :
    CoreSpec p n "const_val_at" [nm, po, pl, value, us]
      (constValAt (decI nm) lps (decE value) (decI us)) decH s₀ a₀ dn vis fe MM eb :=
  CoreSpec.of_call fun r m' h => callW_constValAt p hp hwc n s₀ a₀ dn vis fe MM eb nm po pl value us lps
    hC hnm hv hu hlps r m' h

end refs13


/-! ## `unfold_definition` -/

/-- The model of `unfold_defn_at`: `(flag, result, memory)`. -/
def unfoldDefnAtW (p : Prog) (n : Nat) (m : Mem) (e nw usw q : Word) : Option (Word × Word × Mem) :=
  if usw >>> 28 ≠ 0 then none
  else if tierW usw ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if rdW (m.arr64 CTL) (40 + tierW usw) ≤ idxW usw then none
  else if rdW (m.arr64 LSREC) (idxW usw * 6 + tierW usw * 3 + 1) ≠ rdW (m.arr64 EREC) (q + 3) then
    some (0, 0, m)
  else
  match callW p n "const_val_at" [nw, rdW (m.arr64 EREC) (q + 2), rdW (m.arr64 EREC) (q + 3),
      rdW (m.arr64 EREC) (q + 5), usw] m with
  | none => none
  | some (r₃, m₃) =>
  match callW p n "get_app_args" [e] m₃ with
  | none => none
  | some (r₄, m₄) =>
  match callW p n "mk_app_n" [r₃.headD 0, r₄.headD 0, r₄.tail.headD 0] m₄ with
  | none => none
  | some (r₅, m₅) => some (1, r₅.headD 0, m₅.set64 CTL 136 (rdW (m₃.arr64 CTL) 136))

theorem unfoldDefnAt_spec (p : Prog) (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St) (e nw usw q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "unfold_defn_at" [e, nw, usw, q]
    ⦃fun r s' => LocEq s' s₀ ∧
      unfoldDefnAtW p n s₀.mem e nw usw q = some (r.headD 0, r.tail.headD 0, s'.mem) ∧
      ((r.headD 0 ≠ 0) → (136 : Word).toNat < (s'.mem.arr64 CTL).size); ⊤⦄ := by
  rw [invoke_eq _ hp.unfoldDefnAt]
  simp only [callFn, unfoldDefnAtL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "const_val_at", callW_spec p n "get_app_args",
      callW_spec p n "mk_app_n"] <;>
    finish (gen := 30) [unfoldDefnAtW, tierW, idxW]

/-- The model of `unfold_definition`: `(flag, result, memory)`. -/
def unfoldDefinitionW (p : Prog) (n : Nat) (m : Mem) (vis e : Word) :
    Option (Word × Word × Mem) :=
  match callW p n "get_app_fn" [e] m with
  | none => none
  | some (r₁, m₁) =>
  if r₁.headD 0 >>> 28 ≠ 3 then some (0, 0, m₁)
  else if tierW (r₁.headD 0) ≠ 0 ∧ rdW (m₁.arr64 CTL) 1 = 0 then none
  else if rdW (m₁.arr64 CTL) (18 + tierW (r₁.headD 0)) ≤ idxW (r₁.headD 0) then none
  else
  match callW p n "env_find" [rdW (m₁.arr64 CREC) (idxW (r₁.headD 0) * 4 + tierW (r₁.headD 0) * 2),
      vis] m₁ with
  | none => none
  | some (r₂, m₂) =>
  if r₂.headD 0 = 0 then some (0, 0, m₂)
  else if rdW (m₂.arr64 EREC) (r₂.tail.headD 0) ≠ 1 then some (0, 0, m₂)
  else
  match callW p n "unfold_defn_at" [e,
      rdW (m₁.arr64 CREC) (idxW (r₁.headD 0) * 4 + tierW (r₁.headD 0) * 2),
      rdW (m₁.arr64 CREC) (idxW (r₁.headD 0) * 4 + tierW (r₁.headD 0) * 2 + 1),
      r₂.tail.headD 0] m₂ with
  | none => none
  | some (r₃, m₃) => some (r₃.headD 0, r₃.tail.headD 0, m₃)

theorem unfoldDefinition_spec (p : Prog) (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St) (vis e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "unfold_definition" [vis, e]
    ⦃fun r s' => LocEq s' s₀ ∧
      unfoldDefinitionW p n s₀.mem vis e = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.unfoldDefinition]
  simp only [callFn, unfoldDefinitionL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "get_app_fn", callW_spec p n "env_find", callW_spec p n "unfold_defn_at"] <;>
    finish (gen := 30) [unfoldDefinitionW, tierW, idxW]


/-- The twin's tail of `unfoldDefinition`, once the head is a `defnInfo` constant. -/
def unfoldTailT (n : NIdx) (us : LsIdx) (cv : IConstantVal) (value e : EIdx) : AM (Option EIdx) := do
  let usl ← viewLs us
  if usl.length = cv.levelParams.length then do
    let v ← constValAt n cv.levelParams value us
    let args ← getAppArgs coreWalkFuel e
    let r ← mkAppN v args
    pure (some r)
  else pure none

theorem LsStore.viewLen_eq_map (st : LsStore) (i : LsIdx) :
    st.viewLen i = (st.view i).map List.length := by
  simp only [LsStore.viewLen, LsStore.view, LsStore.persGetLen, LsTables.getLen, LsTables.get]
  split
  · split <;> simp [Option.map_map, Function.comp_def]
  · split
    · split <;> simp [Option.map_map, Function.comp_def]
    · rfl

theorem viewLs_run {a : AState} {h : LsIdx} {l : LsNodeView} (hv : a.store.lss.view h = some l) :
    (viewLs h).run a = .ok (l, a) := by
  simp [viewLs, StateT.run_bind, StateT.run_get, hv]; rfl

theorem unfoldTail_run_ne {a : AState} {n : NIdx} {us : LsIdx} {cv : IConstantVal} {value e : EIdx}
    {l : LsNodeView} (hv : a.store.lss.view us = some l) (hne : l.length ≠ cv.levelParams.length) :
    (unfoldTailT n us cv value e).run a = .ok (none, a) := by
  simp only [unfoldTailT, StateT.run_bind, viewLs_run hv, except_ok_bind, hne, ↓reduceIte]; rfl

theorem unfoldTail_run_ok {a a₁ a₂ : AState} {n : NIdx} {us : LsIdx} {cv : IConstantVal}
    {value e v r : EIdx} {args : List EIdx} {l : LsNodeView} (hv : a.store.lss.view us = some l)
    (heq : l.length = cv.levelParams.length)
    (hc : (constValAt n cv.levelParams value us).run a = .ok (v, a₁))
    (hargs : (getAppArgs coreWalkFuel e).run a₁ = .ok (args, a₁))
    (hmk : (mkAppN v args).run a₁ = .ok (r, a₂)) :
    (unfoldTailT n us cv value e).run a = .ok (some r, a₂) := by
  simp only [unfoldTailT, StateT.run_bind, viewLs_run hv, except_ok_bind, heq, ↓reduceIte, hc,
    hargs, hmk]; rfl

section refs14
variable (p : Prog)

/-- **`mk_app_n` as a run**: the twin's `mkAppN`, `ArenaD` after it, only the `app` tables written,
and the result a handle word. -/
theorem callW_mkAppN (hp : SpineProg p) (n : Nat) (s₀ : St) (a₀ : AState) (hD : ArenaD s₀.mem a₀)
    (f o k : Word) (xs : Array EIdx) (hf : HW f) (hx : SpineR s₀.mem o k xs) (r : List Word)
    (m' : Mem) (h : callW p n "mk_app_n" [f, o, k] s₀.mem = some (r, m')) :
    AM.ok (mkAppN (decE f) xs.toList) a₀ ∧ ArenaD m' (AM.st (mkAppN (decE f) xs.toList) a₀) ∧
    AM.res (mkAppN (decE f) xs.toList) a₀ = decE (r.headD 0) ∧
    MemFrame [AREC, ASLOT, ADER] [4, 5] s₀.mem m' ∧ HW (r.headD 0) := by
  obtain ⟨s', rfl, -, hok, hD', hres, hfr⟩ := triple_of_callW (Q := fun r s' =>
      LocEq s' s₀ ∧ AM.ok (mkAppN (decE f) xs.toList) a₀ ∧
        ArenaD s'.mem (AM.st (mkAppN (decE f) xs.toList) a₀) ∧
        AM.res (mkAppN (decE f) xs.toList) a₀ = decE (r.headD 0) ∧
        MemFrame [AREC, ASLOT, ADER] [4, 5] s₀.mem s'.mem)
    (mkAppN_refines p hp n s₀ a₀ hD f o k xs hf hx) h
  obtain ⟨s'', hm⟩ := triple_of_callW (mkAppNL_spec p hp.derb hp.appf hp.appp hp.appi hp.mkapp hp.mkn
    n s₀ f o k) h
  exact ⟨hok, hD', hres, hfr, mkAppNFromW_hw k.toNat s₀.mem a₀ f o k 0 (by simp) hD hf _ _ hm.2.2⟩

end refs14


section refs15
variable (p : Prog)

theorem callW_unfoldDefnAt (hp : WhnfDeltaProg' p) (hwc : WhnfCallees p) (n : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb e nw usw q : Word) (cv : IConstantVal) (value : EIdx) (hint : ConLeche.ReducibilityHint)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (he : HW e) (hnw : HW nw) (hus : HW usw)
    (hci : decCI (erecP s₀.mem) dn q.toNat = some (.defnInfo cv value hint))
    (hk1 : rdW (s₀.mem.arr64 EREC) q = 1) (r : List Word) (m' : Mem)
    (h : callW p n "unfold_defn_at" [e, nw, usw, q] s₀.mem = some (r, m')) :
    CoreRef (unfoldTailT (decI nw) (decI usw) cv value (decE e)) a₀ decOptR dn s₀.mem vis fe MM eb r
      m' ResW := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW, h136⟩ := triple_of_callW (unfoldDefnAt_spec p hp.toWhnfDeltaProg n s₀ e nw usw q) h
  obtain ⟨hdefn, -, -, -, -, -⟩ := decCI_split hci (erecP_ext _) hC.erec
  obtain ⟨cv', v', hint', hci_eq, hcv, hv', hvl⟩ := hdefn hk1
  injection hci_eq with hcv_eq hv_eq hh_eq
  subst hcv_eq hv_eq
  obtain ⟨hslice, hlen, -, -⟩ := decCV_rd (erecP_ext s₀.mem) hC.erec hcv
  unfold unfoldDefnAtW at hW
  by_cases g1 : usw >>> 28 ≠ 0
  · rw [if_pos g1] at hW; cases hW
  rw [if_neg g1] at hW
  have g1' : usw >>> 28 = 0 := by simpa using g1
  by_cases g2 : tierW usw ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0
  · rw [if_pos g2] at hW; cases hW
  rw [if_neg g2] at hW
  by_cases g3 : rdW (s₀.mem.arr64 CTL) (40 + tierW usw) ≤ idxW usw
  · rw [if_pos g3] at hW; cases hW
  rw [if_neg g3] at hW
  -- the level list's view
  have hls : lsNodeW s₀.mem usw = [rdW (s₀.mem.arr64 LSREC) (idxW usw * 6 + tierW usw * 3),
      rdW (s₀.mem.arr64 LSREC) (idxW usw * 6 + tierW usw * 3 + 1)] := by
    unfold lsNodeW
    rw [if_neg (by simpa using g1'), if_neg g2, if_neg g3]
  have hvl' := lsNodeW_viewLen hC.arena.1 hus hls
  rw [LsStore.viewLen_eq_map] at hvl'
  obtain ⟨l, hview, hllen⟩ : ∃ l, a₀.store.lss.view (decI usw) = some l ∧
      l.length = (rdW (s₀.mem.arr64 LSREC) (idxW usw * 6 + tierW usw * 3 + 1)).toNat := by
    cases hv : a₀.store.lss.view (decI usw) with
    | none => rw [hv] at hvl'; cases hvl'
    | some l => rw [hv] at hvl'; exact ⟨l, rfl, Option.some.inj hvl'⟩
  by_cases g4 : rdW (s₀.mem.arr64 LSREC) (idxW usw * 6 + tierW usw * 3 + 1) ≠
      rdW (s₀.mem.arr64 EREC) (q + 3)
  · rw [if_pos g4] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    rw [← hm]
    refine (CRef.pure hC _ (unfoldTail_run_ne hview ?_) ?_ ?_).core
    · intro hc
      apply g4
      apply UInt64.toNat_inj.mp
      rw [← hllen, hc, hlen]
    · simp only [decOptR, decOpt, ← hr0]; rfl
    · unfold ResW HW; rw [← hr0, ← hr1]; exact ⟨by decide, by decide⟩
  rw [if_neg g4] at hW
  have g4' : rdW (s₀.mem.arr64 LSREC) (idxW usw * 6 + tierW usw * 3 + 1) =
      rdW (s₀.mem.arr64 EREC) (q + 3) := by simpa using g4
  have hleneq : l.length = cv.levelParams.length := by rw [hllen, hlen, g4']
  -- const_val_at
  cases h1 : callW p n "const_val_at" [nw, rdW (s₀.mem.arr64 EREC) (q + 2),
      rdW (s₀.mem.arr64 EREC) (q + 3), rdW (s₀.mem.arr64 EREC) (q + 5), usw] s₀.mem with
  | none => rw [h1] at hW; cases hW
  | some q₁ =>
  obtain ⟨r₃, m₃⟩ := q₁
  rw [h1] at hW
  dsimp only at hW
  obtain ⟨hok1, ⟨M', hS₃, hK₃, hSt₃⟩, hres1, hrh1⟩ := callW_constValAt p hp.toWhnfDeltaProg hwc n s₀ a₀ dn vis
    fe MM eb nw _ _ _ usw cv.levelParams hC hnw hvl hus hslice r₃ m₃ h1
  have hv'' : value = decE (rdW (s₀.mem.arr64 EREC) (q + 5)) := hv'
  rw [← hv''] at hok1 hS₃ hres1
  have hrun1 := AM.run_of_ok _ _ hok1
  rw [hres1] at hrun1
  -- get_app_args
  cases h2 : callW p n "get_app_args" [e] m₃ with
  | none => rw [h2] at hW; cases hW
  | some q₂ =>
  obtain ⟨r₄, m₄⟩ := q₂
  rw [h2] at hW
  dsimp only at hW
  obtain ⟨t₂, ht₂, -, hfr₂, hgrew, -, -, xs, hxrun, hsp⟩ := triple_of_callW
    (getAppArgs_refines p hp.spine n ⟨m₃, Locals.init []⟩ _ hS₃.arena.1 e he hS₃.spn) h2
  subst ht₂
  have hS₄ : CoreS dn t₂.mem _ vis fe M' eb :=
    hS₃.frame_stk hfr₂ (fun b hb => by simpa using hb) (fun x hx => by simpa using hx)
  -- mk_app_n
  cases h3 : callW p n "mk_app_n" [r₃.headD 0, r₄.headD 0, r₄.tail.headD 0] t₂.mem with
  | none => rw [h3] at hW; cases hW
  | some q₃ =>
  obtain ⟨r₅, m₅⟩ := q₃
  rw [h3] at hW
  dsimp only at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr0, hr1, hm⟩ := hW
  obtain ⟨hok3, hD3, hres3, hfr3, hhw3⟩ := callW_mkAppN p hp.spine n ⟨t₂.mem, Locals.init []⟩ _
    hS₄.arena (r₃.headD 0) (r₄.headD 0) (r₄.tail.headD 0) xs.toArray hrh1 hsp r₅ m₅ h3
  rw [List.toList_toArray] at hok3 hD3 hres3
  have e0 : (constValAt (decI nw) cv.levelParams value (decI usw)).run a₀ =
      .ok (decE (r₃.headD 0), AM.st (constValAt (decI nw) cv.levelParams value (decI usw)) a₀) := by
    rw [hrun1]; rfl
  have e2 : (mkAppN (decE (r₃.headD 0)) xs).run
      (AM.st (constValAt (decI nw) cv.levelParams value (decI usw)) a₀) =
      .ok (decE (r₅.headD 0), AM.st (mkAppN (decE (r₃.headD 0)) xs)
        (AM.st (constValAt (decI nw) cv.levelParams value (decI usw)) a₀)) := by
    rw [AM.run_of_ok _ _ hok3, hres3]
  have hz := unfoldTail_run_ok hview hleneq e0 hxrun e2
  obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
  have hcpl : cpl (AM.st (mkAppN (decE (r₃.headD 0)) xs)
      (AM.st (constValAt (decI nw) cv.levelParams value (decI usw)) a₀)) =
      cpl (AM.st (constValAt (decI nw) cv.levelParams value (decI usw)) a₀) := by
    have := Keeps.run (keeps_cpl_mkAppNFrom (decE (r₃.headD 0)) xs.toArray 0)
      (a := AM.st (constValAt (decI nw) cv.levelParams value (decI usw)) a₀)
      (by rw [mkAppNFrom_eq_mkAppN, List.toList_toArray]; exact AM.run_of_ok _ _ hok3)
    simpa using this
  have hS₅ := hS₄.of_app hD3 hcpl hfr3
  have hspn5 : m₅.arr64 SPN = t₂.mem.arr64 SPN :=
    hfr3.1 SPN (by simp [AREC, ASLOT, ADER, SPN]) (by decide)
  have hfr6 : MemFrame [SPN] [136] m₅ (m₅.set64 CTL 136 (rdW (m₃.arr64 CTL) 136)) :=
    (MemFrame.setCtl m₅ 136 _).mono (by simp) (by simp)
  have hS₆ : CoreS dn (m₅.set64 CTL 136 (rdW (m₃.arr64 CTL) 136)) _ vis fe M' eb :=
    hS₅.frame_stk hfr6 (fun b hb => by simpa using hb) (fun x hx => by simpa using hx)
  have h136' : (136 : Word).toNat < (m₅.arr64 CTL).size := by
    have := h136 (by rw [← hr0]; decide)
    rw [← hm, size_set64] at this; exact this
  have hStK : StackKept m₃ (m₅.set64 CTL 136 (rdW (m₃.arr64 CTL) 136)) := by
    apply StackKept.restore _ (by rw [hspn5, hgrew.2.1]) h136'
    intro i hi
    simp only [spW, hspn5]
    exact hgrew.2.2 i hi
  refine ⟨hok', ?_, ?_, ?_⟩
  · rw [hst', ← hm]
    exact ⟨M', hS₆, hK₃, hSt₃.trans hStK⟩
  · rw [hres']
    simp only [decOptR, decOpt, ← hr0, ← hr1]
    simp
  · unfold ResW HW; rw [← hr0, ← hr1]; exact ⟨by decide, hhw3⟩

end refs15


theorem unfoldDef_run_notconst (fe : IFEnv) (e hh : EIdx) (a : AState)
    (hgf : (getAppFn coreWalkFuel e).run a = .ok (hh, a)) (ht : (hh.tag == ETag.const) = false) :
    (unfoldDefinition fe e).run a = .ok (none, a) := by
  simp only [unfoldDefinition, StateT.run_bind, hgf, except_ok_bind, ht]; rfl

theorem unfoldDef_run_nodefn (fe : IFEnv) (e hh : EIdx) (a : AState) (n : NIdx) (us : LsIdx)
    (hgf : (getAppFn coreWalkFuel e).run a = .ok (hh, a)) (ht : (hh.tag == ETag.const) = true)
    (hv : a.store.view hh = some (.const n us))
    (hfind : ∀ cv v hint, fe.find? n ≠ some (.defnInfo cv v hint)) :
    (unfoldDefinition fe e).run a = .ok (none, a) := by
  simp only [unfoldDefinition, StateT.run_bind, hgf, except_ok_bind, ht, ↓reduceIte,
    view_run _ _ _ hv]
  cases hf : fe.find? n with
  | none => rfl
  | some ci =>
    cases ci with
    | defnInfo cv v hint => exact absurd hf (hfind cv v hint)
    | _ => rfl

theorem unfoldDef_run_tail (fe : IFEnv) (e hh : EIdx) (a : AState) (n : NIdx) (us : LsIdx)
    (cv : IConstantVal) (value : EIdx) (hint : ConLeche.ReducibilityHint)
    (hgf : (getAppFn coreWalkFuel e).run a = .ok (hh, a)) (ht : (hh.tag == ETag.const) = true)
    (hv : a.store.view hh = some (.const n us)) (hfind : fe.find? n = some (.defnInfo cv value hint)) :
    (unfoldDefinition fe e).run a = (unfoldTailT n us cv value e).run a := by
  simp only [unfoldDefinition, StateT.run_bind, hgf, except_ok_bind, ht, ↓reduceIte,
    view_run _ _ _ hv, hfind, unfoldTailT]

section refs16
variable (p : Prog)

theorem callW_unfoldDefinition (hp : WhnfDeltaProg' p) (hwc : WhnfCallees p) (n : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb e : Word) (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (he : HW e) (r : List Word) (m' : Mem)
    (h : callW p n "unfold_definition" [vis, e] s₀.mem = some (r, m')) :
    CoreRef (unfoldDefinition fe (decE e)) a₀ decOptR dn s₀.mem vis fe MM eb r m' ResW := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (unfoldDefinition_spec p hp.toWhnfDeltaProg n s₀ vis e) h
  unfold unfoldDefinitionW at hW
  cases h1 : callW p n "get_app_fn" [e] s₀.mem with
  | none => rw [h1] at hW; cases hW
  | some q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  rw [h1] at hW
  obtain ⟨t₁, ht₁, hm₁, -, hhw1, hgf⟩ := triple_of_callW
    (getAppFn_refines p hp.spine n s₀ a₀ hC.arena.1 e he) h1
  have hm1 : m₁ = s₀.mem := by rw [← ht₁, hm₁]
  subst hm1
  dsimp only at hW
  by_cases g0 : r₁.headD 0 >>> 28 ≠ 3
  · rw [if_pos g0] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    rw [← hm]
    have ht : ((decE (r₁.headD 0)).tag == ETag.const) = false := by
      rw [decE_const_tag _ hhw1]; exact beq_eq_false_iff_ne.mpr g0
    refine (CRef.pure hC _ (unfoldDef_run_notconst fe _ _ a₀ hgf ht) ?_ ?_).core
    · simp only [decOptR, decOpt, ← hr0]; rfl
    · unfold ResW HW; rw [← hr0, ← hr1]; exact ⟨by decide, by decide⟩
  rw [if_neg g0] at hW
  have g0' : r₁.headD 0 >>> 28 = 3 := by simpa using g0
  have ht : ((decE (r₁.headD 0)).tag == ETag.const) = true := by
    rw [decE_const_tag _ hhw1]; exact beq_iff_eq.mpr g0'
  by_cases g1 : tierW (r₁.headD 0) ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0
  · rw [if_pos g1] at hW; cases hW
  rw [if_neg g1] at hW
  by_cases g2 : rdW (s₀.mem.arr64 CTL) (18 + tierW (r₁.headD 0)) ≤ idxW (r₁.headD 0)
  · rw [if_pos g2] at hW; cases hW
  rw [if_neg g2] at hW
  have hvOK : viewOK s₀.mem (r₁.headD 0) 18 := ⟨g1, by simpa using g2⟩
  obtain ⟨n_, us_, hview, hn, hu, hnl, hul⟩ :=
    view_const_words s₀.mem a₀ hC.arena.1 (r₁.headD 0) hhw1 hvOK g0'
  cases h2 : callW p n "env_find" [rdW (s₀.mem.arr64 CREC) (idxW (r₁.headD 0) * 4 +
      tierW (r₁.headD 0) * 2), vis] s₀.mem with
  | none => rw [h2] at hW; cases hW
  | some q₂ =>
  obtain ⟨r₂, m₂⟩ := q₂
  rw [h2] at hW
  obtain ⟨hm2, hfind, hdec⟩ := callW_envFind p hp n ⟨s₀.mem, Locals.init []⟩ vis _ hC.env hnl r₂ m₂ h2
  subst hm2
  dsimp only at hW
  by_cases g3 : r₂.headD 0 = 0
  · rw [if_pos g3] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    rw [← hm]
    have hnone : fe.find? n_ = none := by
      rw [hn, hfind]; simp only [decFound, g3, ↓reduceIte]
    refine (CRef.pure hC _ (unfoldDef_run_nodefn fe _ _ a₀ n_ us_ hgf ht hview
      (fun cv v hint hh => by rw [hnone] at hh; cases hh)) ?_ ?_).core
    · simp only [decOptR, decOpt, ← hr0]; rfl
    · unfold ResW HW; rw [← hr0, ← hr1]; exact ⟨by decide, by decide⟩
  rw [if_neg g3] at hW
  obtain ⟨ci, hci⟩ := hdec g3
  have hfind' : fe.find? n_ = some ci := by
    rw [hn, hfind]; simp only [decFound, g3, ↓reduceIte]; exact hci
  obtain ⟨hdefn, hndefn, -, -, -, -⟩ := decCI_split hci (erecP_ext _) hC.erec
  by_cases g4 : rdW (s₀.mem.arr64 EREC) (r₂.tail.headD 0) ≠ 1
  · rw [if_pos g4] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    rw [← hm]
    refine (CRef.pure hC _ (unfoldDef_run_nodefn fe _ _ a₀ n_ us_ hgf ht hview
      (fun cv v hint hh => hndefn g4 cv v hint (by rw [hfind'] at hh; exact Option.some.inj hh))) ?_ ?_).core
    · simp only [decOptR, decOpt, ← hr0]; rfl
    · unfold ResW HW; rw [← hr0, ← hr1]; exact ⟨by decide, by decide⟩
  rw [if_neg g4] at hW
  have g4' : rdW (s₀.mem.arr64 EREC) (r₂.tail.headD 0) = 1 := by simpa using g4
  obtain ⟨cv, value, hint, rfl, hcv, hv', hvl⟩ := hdefn g4'
  cases h3 : callW p n "unfold_defn_at" [e, rdW (s₀.mem.arr64 CREC) (idxW (r₁.headD 0) * 4 +
      tierW (r₁.headD 0) * 2), rdW (s₀.mem.arr64 CREC) (idxW (r₁.headD 0) * 4 +
      tierW (r₁.headD 0) * 2 + 1), r₂.tail.headD 0] s₀.mem with
  | none => rw [h3] at hW; cases hW
  | some q₃ =>
  obtain ⟨r₃, m₃⟩ := q₃
  rw [h3] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr0, hr1, hm⟩ := hW
  rw [← hm]
  have hci' : decCI (erecP s₀.mem) dn (r₂.tail.headD 0).toNat = some (.defnInfo cv value hint) := hci
  have hcore := callW_unfoldDefnAt p hp hwc n s₀ a₀ dn vis fe MM eb e _ _ (r₂.tail.headD 0) cv value hint
    hC he hnl hul hci' g4' r₃ m₃ h3
  have hrun := unfoldDef_run_tail fe (decE e) (decE (r₁.headD 0)) a₀ n_ us_ cv value hint hgf ht hview
    hfind'
  rw [hn, hu] at hrun
  obtain ⟨hok, hst, hres⟩ := AM.congr_run hrun
  obtain ⟨hok', hA, hres', hrw⟩ := hcore
  have hf : fe.find? n_ = some (.defnInfo cv value hint) := hfind'
  refine ⟨by rw [hok]; exact hok', ?_, ?_, ?_⟩
  · rw [hst]; exact hA
  · rw [hres, hres']; simp only [decOptR, ← hr0, ← hr1]
  · unfold ResW at hrw ⊢; rw [← hr0, ← hr1]; exact hrw

/-- **`unfold_definition` refines `unfoldDefinition`**, given the stub `inst_lp`'s spec. -/
theorem unfoldDefinition_refines' (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb e : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (he : HW e) (hwc : WhnfCallees p) :
    CoreSpec p n "unfold_definition" [vis, e] (unfoldDefinition fe (decE e)) decOptR s₀ a₀ dn vis fe
      MM eb ResW :=
  CoreSpec.of_call fun r m' h => callW_unfoldDefinition p hp hwc n s₀ a₀ dn vis fe MM eb e hC he r m' h

end refs16


/-! ## `nat_succ_lit` -/

/-- **An interned `lit` handle word is below `2^32`.** -/
theorem internW_hw (m : Mem) (a : AState) (hR : LitR m a) (o l : Word) (w : Word) (m' : Mem)
    (hI : internW m o l = some (w, m')) : w.toNat < 2 ^ 32 := by
  obtain ⟨hpool, hS⟩ := hR
  rw [internW_eq] at hI
  exact internM_hw litSch RecRel litH litS_wf m _ _ _ hS (litMt m o l _) _ _ _ _
    (probe_homeG litSch m 0 _ _ (probeW_arm m o l _ 0) _)
    (probe_homeG litSch m 1 _ _ (probeW_arm m o l _ 1) _) _ (pushOK_room m) _ _ w m' hI

/-- `intern_lit` refines `internE (.lit (.natVal _))` under `ArenaD`, with the handle word below
`2^32`. -/
theorem internLit_refinesD_hw (p : Prog) (hph : p.lookup "lit_hash" = some litHash)
    (hpe : p.lookup "limbs_eq" = some limbsEq) (hpm : p.lookup "lit_match" = some litMatch)
    (hpf : p.lookup "lit_find" = some litFind) (hpp : p.lookup "lit_push" = some litPush)
    (hp : p.lookup "intern_lit" = some internLit)
    (a₀ : AState) (n : Nat) (s₀ : St) (o l : Word) (hA : ArenaD s₀.mem a₀)
    (hq : SliceOK s₀.mem o l) (hn : Norm (s₀.mem.arr64 POOL) o.toNat l.toNat) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_lit" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (internE (.lit (.natVal (pv (s₀.mem.arr64 POOL) o.toNat l.toNat)))) a₀ ∧
      ArenaD s'.mem (AM.st (internE (.lit (.natVal (pv (s₀.mem.arr64 POOL) o.toNat l.toNat)))) a₀) ∧
      AM.res (internE (.lit (.natVal (pv (s₀.mem.arr64 POOL) o.toNat l.toNat)))) a₀ =
        decE (r.headD 0) ∧ HW (r.headD 0); ⊤⦄ := by
  have ⟨_, _, hps, htop⟩ := hA.1.lit.1
  have hspec := internLit_spec p hph hpe hpm hpf hpp hp n s₀ o l (by omega)
    (by simp only [SliceOK] at hq; omega)
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun hspec
  subst hs
  obtain ⟨h1, h2, h3⟩ := internLit_D s.mem a₀ hA o l _ hq hn _ hI
  exact ⟨hloc, h1, h2, h3, internW_hw s.mem a₀ hA.1.lit o l _ _ hI⟩


section addhw
variable (p : Prog) (hpl : p.lookup "nat_limb" = some natLimb)
  (hpc : p.lookup "add_carry" = some addCarry) (hpt : p.lookup "nat_trim" = some natTrim)
  (hpa : p.lookup "nat_add" = some natAdd) (hpn : p.lookup "nat_add_lit" = some natAddLit)
  (R : Mem → AState → Prop)
  (hpool : ∀ m a, R m a → PoolOK m)
  (hgrow : ∀ m m' a, R m a → Grows m m' → R m' a)
  (hI : ∀ (a₀ : AState) (n : Nat) (s₀ : St) (o l : Word), R s₀.mem a₀ →
    SliceOK s₀.mem o l → Norm (s₀.mem.arr64 POOL) o.toNat l.toNat →
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_lit" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (internE (.lit (.natVal (pv (s₀.mem.arr64 POOL) o.toNat l.toNat)))) a₀ ∧
      R s'.mem (AM.st (internE (.lit (.natVal (pv (s₀.mem.arr64 POOL) o.toNat l.toNat)))) a₀) ∧
      AM.res (internE (.lit (.natVal (pv (s₀.mem.arr64 POOL) o.toNat l.toNat)))) a₀ = decE (r.headD 0) ∧
      HW (r.headD 0); ⊤⦄)

include hpl hpc hpt hpa hpn hpool hgrow hI in
/-- `natAddLit_refines` with the result a handle word (`hI` carries `HW`). -/
theorem natAddLit_refines_hw (n : Nat) (s₀ : St) (a₀ : AState) (hR : R s₀.mem a₀)
    (oa la ob lb : Word) (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob lb) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_add_lit" [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (natAddArm (pv (s₀.mem.arr64 POOL) oa.toNat la.toNat)
        (pv (s₀.mem.arr64 POOL) ob.toNat lb.toNat)) a₀ ∧
      R s'.mem (AM.st (natAddArm (pv (s₀.mem.arr64 POOL) oa.toNat la.toNat)
        (pv (s₀.mem.arr64 POOL) ob.toNat lb.toNat)) a₀) ∧
      AM.res (natAddArm (pv (s₀.mem.arr64 POOL) oa.toNat la.toNat)
        (pv (s₀.mem.arr64 POOL) ob.toNat lb.toNat)) a₀ = some (decE (r.headD 0)) ∧
      HW (r.headD 0); ⊤⦄ := by
  have hok := hpool _ _ hR
  simp only [PoolOK, SliceOK] at hok ha hb
  rw [invoke_eq _ hpn]
  simp only [callFn, natAddLit]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalArgs, setLoc, setLocs, ld64, natAdd_spec p hpl hpc hpt hpa n,
        hI a₀ n] <;>
      finish [natAddArm, PoolOK, SliceOK]

end addhw


section succ
variable (p : Prog) (hpl : p.lookup "nat_limb" = some natLimb)
  (hpc : p.lookup "add_carry" = some addCarry) (hpt : p.lookup "nat_trim" = some natTrim)
  (hpa : p.lookup "nat_add" = some natAdd) (hpn : p.lookup "nat_add_lit" = some natAddLit)
  (R : Mem → AState → Prop)
  (hpool : ∀ m a, R m a → PoolOK m)
  (hgrow : ∀ m m' a, R m a → Grows m m' → R m' a)
  (hI : ∀ (a₀ : AState) (n : Nat) (s₀ : St) (o l : Word), R s₀.mem a₀ →
    SliceOK s₀.mem o l → Norm (s₀.mem.arr64 POOL) o.toNat l.toNat →
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_lit" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (internE (.lit (.natVal (pv (s₀.mem.arr64 POOL) o.toNat l.toNat)))) a₀ ∧
      R s'.mem (AM.st (internE (.lit (.natVal (pv (s₀.mem.arr64 POOL) o.toNat l.toNat)))) a₀) ∧
      AM.res (internE (.lit (.natVal (pv (s₀.mem.arr64 POOL) o.toNat l.toNat)))) a₀ = decE (r.headD 0) ∧
      HW (r.headD 0); ⊤⦄)
  (hg : p.lookup "nat_succ_lit" = some natSuccLitL)

include hpl hpc hpt hpa hpn hpool hgrow hI hg in
/-- **`nat_succ_lit` refines the `Nat.add` arm at the literal `1`**, with a handle word result. -/
theorem natSuccLit_refines_hw (n : Nat) (s₀ : St) (a₀ : AState) (hR : R s₀.mem a₀)
    (oa la : Word) (ha : SliceOK s₀.mem oa la) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_succ_lit" [oa, la]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (natAddArm (pv (s₀.mem.arr64 POOL) oa.toNat la.toNat) 1) a₀ ∧
      R s'.mem (AM.st (natAddArm (pv (s₀.mem.arr64 POOL) oa.toNat la.toNat) 1) a₀) ∧
      AM.res (natAddArm (pv (s₀.mem.arr64 POOL) oa.toNat la.toNat) 1) a₀ =
        some (decE (r.headD 0)) ∧ HW (r.headD 0); ⊤⦄ := by
  have hok := hpool _ _ hR
  simp only [PoolOK, SliceOK] at hok ha
  rw [invoke_eq _ hg]
  simp only [callFn, natSuccLitL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, natop_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        fun s => natAddLit_refines_hw p hpl hpc hpt hpa hpn R hpool hgrow hI n s a₀] <;>
      finish (gen := 20) [natAddArm, PoolOK, SliceOK, Grows]

end succ


theorem keeps_cpl_natAddArm (a b : Nat) : Keeps cpl (natAddArm a b) := by
  unfold natAddArm
  exact Keeps.bind (keeps_cpl_internLit _) (fun _ => Keeps.pure _)

section refs17
variable (p : Prog)

theorem natSuccLit_inst (hp : WhnfDeltaProg' p) :
    ∀ (a₀ : AState) (n : Nat) (s₀ : St) (o l : Word), ArenaD s₀.mem a₀ →
    SliceOK s₀.mem o l → Norm (s₀.mem.arr64 POOL) o.toNat l.toNat →
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_lit" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (internE (.lit (.natVal (pv (s₀.mem.arr64 POOL) o.toNat l.toNat)))) a₀ ∧
      ArenaD s'.mem (AM.st (internE (.lit (.natVal (pv (s₀.mem.arr64 POOL) o.toNat l.toNat)))) a₀) ∧
      AM.res (internE (.lit (.natVal (pv (s₀.mem.arr64 POOL) o.toNat l.toNat)))) a₀ = decE (r.headD 0) ∧
      HW (r.headD 0); ⊤⦄ :=
  fun a₀ n s₀ o l hA hq hn => internLit_refinesD_hw p hp.litHash' hp.limbsEq' hp.litMatch' hp.litFind'
    hp.litPush' hp.internLit a₀ n s₀ o l hA hq hn

/-- **`nat_succ_lit` as a run.** -/
theorem callW_natSuccLit (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb o cnt : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (hs : SliceOK s₀.mem o cnt) (r : List Word) (m' : Mem)
    (h : callW p n "nat_succ_lit" [o, cnt] s₀.mem = some (r, m')) :
    AM.ok (natAddArm (pv (s₀.mem.arr64 POOL) o.toNat cnt.toNat) 1) a₀ ∧
    CoreS dn m' (AM.st (natAddArm (pv (s₀.mem.arr64 POOL) o.toNat cnt.toNat) 1) a₀) vis fe MM eb ∧
    AM.res (natAddArm (pv (s₀.mem.arr64 POOL) o.toNat cnt.toNat) 1) a₀ = some (decE (r.headD 0)) ∧
    MemFrame natA natC s₀.mem m' ∧ HW (r.headD 0) := by
  obtain ⟨s', rfl, -, hok, hD, hres, hhw⟩ := triple_of_callW
    (natSuccLit_refines_hw p hp.natLimb' hp.addCarry' hp.natTrim' hp.natAdd' hp.natAddLit ArenaD
      (fun _ _ h => h.1.lit.1) (fun m m' a hA hg => ArenaD.grow m m' hg a hA)
      (natSuccLit_inst p hp) hp.natSuccLit n s₀ a₀ hC.arena o cnt hs) h
  have hfr := callW_natFrame p hp.natClosed "nat_succ_lit" (by decide +kernel) n _ _ _ _ h
  exact ⟨hok, hC.of_nat hD (Keeps.run (keeps_cpl_natAddArm _ _) (AM.run_of_ok _ _ hok)) hfr, hres,
    hfr, hhw⟩

end refs17


/-! ## `reduce_nat`: the twin's arms -/

/-- The `Nat.succ` arm of `reduceNat`, past the level test. -/
def redSuccT (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (c : NIdx) (b : EIdx) :
    AM (Option EIdx) := do
  let ns ← pinNatSucc
  if c == ns && (← natLitSupported fe) then do
    match ← rawNatLit? (← r.whnf depth b) with
    | some n => do
      let x ← internE (.lit (.natVal (n + 1)))
      pure (some x)
    | none => pure none
  else pure none

/-- The certified binary operation arm of `reduceNat`. -/
def redOpT (r : CoreFnsA) (depth : Nat) (c : NIdx) (a b : EIdx) : AM (Option EIdx) := do
  match ← rawNatLit? (← r.whnf depth a) with
  | some n₁ => do
    match ← rawNatLit? (← r.whnf depth b) with
    | some n₂ => natOpResult c n₁ n₂
    | none => pure none
  | none => pure none

/-- The safety-net arm of `reduceNat`. -/
def redWfT (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (c : NIdx) (a b : EIdx) :
    AM (Option EIdx) := do
  let wf ← natOpWfNames
  if wf.contains c && (← natLitSupported fe) then do
    match ← rawNatLit? (← r.whnf depth a) with
    | some _ => do
      match ← rawNatLit? (← r.whnf depth b) with
      | some _ =>
        fail (.notImplemented "native Nat computation on literals")
      | none => pure none
    | none => pure none
  else pure none

/-- The binary arm of `reduceNat`, past the level test. -/
def redBinT (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (c : NIdx) (a b : EIdx) :
    AM (Option EIdx) := do
  if (← natBinOpName c) && (← natOpStored fe c) then
    redOpT r depth c a b
  else
    redWfT r fe depth c a b

theorem reduceNat_notapp (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (e : EIdx) (a : AState)
    (h : (e.tag == ETag.app) = false) : (reduceNat r fe depth e).run a = .ok (none, a) := by
  simp only [reduceNat, h]; rfl

theorem reduceNat_other (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (e f b : EIdx) (a : AState)
    (h : (e.tag == ETag.app) = true) (hv : a.store.view e = some (.app f b)) (v : ENodeView)
    (hvf : a.store.view f = some v) (hc : ∀ c us, v ≠ .const c us) (hp : ∀ g x, v ≠ .app g x) :
    (reduceNat r fe depth e).run a = .ok (none, a) := by
  simp only [reduceNat, h, ↓reduceIte, StateT.run_bind, view_run _ _ _ hv, except_ok_bind,
    view_run _ _ _ hvf]
  cases v with
  | const c us => exact absurd rfl (hc c us)
  | app g x => exact absurd rfl (hp g x)
  | _ => rfl

theorem reduceNat_succ_lvl (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (e f b : EIdx) (a : AState)
    (c : NIdx) (us el : LsIdx) (h : (e.tag == ETag.app) = true)
    (hv : a.store.view e = some (.app f b)) (hvf : a.store.view f = some (.const c us))
    (hel : emptyLevels.run a = .ok (el, a)) (hne : (us != el) = true) :
    (reduceNat r fe depth e).run a = .ok (none, a) := by
  simp only [reduceNat, h, ↓reduceIte, StateT.run_bind, view_run _ _ _ hv, except_ok_bind,
    view_run _ _ _ hvf, hel, hne]; rfl

theorem reduceNat_succ_eq (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (e f b : EIdx) (a : AState)
    (c : NIdx) (us el : LsIdx) (h : (e.tag == ETag.app) = true)
    (hv : a.store.view e = some (.app f b)) (hvf : a.store.view f = some (.const c us))
    (hel : emptyLevels.run a = .ok (el, a)) (heq : (us != el) = false) :
    (reduceNat r fe depth e).run a = (redSuccT r fe depth c b).run a := by
  simp only [reduceNat, h, ↓reduceIte, StateT.run_bind, view_run _ _ _ hv, except_ok_bind,
    view_run _ _ _ hvf, hel, heq, redSuccT]
  rfl


theorem reduceNat_bin_notconst (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (e f b g x : EIdx)
    (a : AState) (h : (e.tag == ETag.app) = true) (hv : a.store.view e = some (.app f b))
    (hvf : a.store.view f = some (.app g x)) (hg : (g.tag == ETag.const) = false) :
    (reduceNat r fe depth e).run a = .ok (none, a) := by
  simp only [reduceNat, h, ↓reduceIte, StateT.run_bind, view_run _ _ _ hv, except_ok_bind,
    view_run _ _ _ hvf, hg]; rfl

theorem reduceNat_bin_lvl (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (e f b g x : EIdx)
    (a : AState) (c : NIdx) (us el : LsIdx) (h : (e.tag == ETag.app) = true)
    (hv : a.store.view e = some (.app f b)) (hvf : a.store.view f = some (.app g x))
    (hg : (g.tag == ETag.const) = true) (hvg : a.store.view g = some (.const c us))
    (hel : emptyLevels.run a = .ok (el, a)) (hne : (us != el) = true) :
    (reduceNat r fe depth e).run a = .ok (none, a) := by
  simp only [reduceNat, h, ↓reduceIte, StateT.run_bind, view_run _ _ _ hv, except_ok_bind,
    view_run _ _ _ hvf, hg, view_run _ _ _ hvg, hel, hne]; rfl

theorem reduceNat_bin_eq (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (e f b g x : EIdx)
    (a : AState) (c : NIdx) (us el : LsIdx) (h : (e.tag == ETag.app) = true)
    (hv : a.store.view e = some (.app f b)) (hvf : a.store.view f = some (.app g x))
    (hg : (g.tag == ETag.const) = true) (hvg : a.store.view g = some (.const c us))
    (hel : emptyLevels.run a = .ok (el, a)) (heq : (us != el) = false) :
    (reduceNat r fe depth e).run a = (redBinT r fe depth c x b).run a := by
  simp only [reduceNat, h, ↓reduceIte, StateT.run_bind, view_run _ _ _ hv, except_ok_bind,
    view_run _ _ _ hvf, hg, view_run _ _ _ hvg, hel, heq, redBinT, redOpT, redWfT]
  rfl

theorem redBin_run (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (c : NIdx) (a b : EIdx) (s : AState)
    (b1 b2 : Bool) (h1 : (natBinOpName c).run s = .ok (b1, s))
    (h2 : (natOpStored fe c).run s = .ok (b2, s)) :
    (redBinT r fe depth c a b).run s =
      if (b1 && b2) = true then (redOpT r depth c a b).run s else (redWfT r fe depth c a b).run s := by
  simp only [redBinT, StateT.run_bind, h1, h2, except_ok_bind]
  cases b1 <;> cases b2 <;> rfl

section redruns
variable (r : CoreFnsA) (fe : IFEnv) (depth : Nat)

theorem redSucc_run_skip (c : NIdx) (b : EIdx) (s s₁ : AState) (m : Mem) (hP : PinsFull m s.pins)
    (sup : Bool) (hs : (natLitSupported fe).run s = .ok (sup, s₁))
    (hc : (c == decI (pinW m 4) && sup) = false) : (redSuccT r fe depth c b).run s = .ok (none, s₁) := by
  simp only [redSuccT, StateT.run_bind, pinNatSucc_run hP, except_ok_bind, hs, hc]; rfl

theorem redSucc_run_none (c : NIdx) (b : EIdx) (s s₁ s₂ s₃ : AState) (m : Mem)
    (hP : PinsFull m s.pins) (sup : Bool) (hs : (natLitSupported fe).run s = .ok (sup, s₁))
    (hc : (c == decI (pinW m 4) && sup) = true) (wb : EIdx)
    (hw : (r.whnf depth b).run s₁ = .ok (wb, s₂))
    (hr : (rawNatLit? wb).run s₂ = .ok (none, s₃)) :
    (redSuccT r fe depth c b).run s = .ok (none, s₃) := by
  simp only [redSuccT, StateT.run_bind, pinNatSucc_run hP, except_ok_bind, hs, hc, ite_true, hw, hr]; rfl

theorem redSucc_run_some (c : NIdx) (b : EIdx) (s s₁ s₂ s₃ s₄ : AState) (m : Mem)
    (hP : PinsFull m s.pins) (sup : Bool) (hs : (natLitSupported fe).run s = .ok (sup, s₁))
    (hc : (c == decI (pinW m 4) && sup) = true) (wb : EIdx)
    (hw : (r.whnf depth b).run s₁ = .ok (wb, s₂)) (N : Nat)
    (hr : (rawNatLit? wb).run s₂ = .ok (some N, s₃)) (x : EIdx)
    (hi : (internE (.lit (.natVal (N + 1)))).run s₃ = .ok (x, s₄)) :
    (redSuccT r fe depth c b).run s = .ok (some x, s₄) := by
  simp only [redSuccT, StateT.run_bind, pinNatSucc_run hP, except_ok_bind, hs, hc, ite_true, hw, hr, hi]; rfl

theorem redOp_run_none1 (c : NIdx) (a b : EIdx) (s s₁ s₂ : AState) (wa : EIdx)
    (hw : (r.whnf depth a).run s = .ok (wa, s₁)) (hr : (rawNatLit? wa).run s₁ = .ok (none, s₂)) :
    (redOpT r depth c a b).run s = .ok (none, s₂) := by
  simp only [redOpT, StateT.run_bind, hw, except_ok_bind, hr]; rfl

theorem redOp_run_none2 (c : NIdx) (a b : EIdx) (s s₁ s₂ s₃ s₄ : AState) (wa wb : EIdx) (N : Nat)
    (hw : (r.whnf depth a).run s = .ok (wa, s₁)) (hr : (rawNatLit? wa).run s₁ = .ok (some N, s₂))
    (hw2 : (r.whnf depth b).run s₂ = .ok (wb, s₃)) (hr2 : (rawNatLit? wb).run s₃ = .ok (none, s₄)) :
    (redOpT r depth c a b).run s = .ok (none, s₄) := by
  simp only [redOpT, StateT.run_bind, hw, except_ok_bind, hr, hw2, hr2]; rfl

theorem redOp_run_some (c : NIdx) (a b : EIdx) (s s₁ s₂ s₃ s₄ s₅ : AState) (wa wb : EIdx)
    (N₁ N₂ : Nat) (o : Option EIdx)
    (hw : (r.whnf depth a).run s = .ok (wa, s₁)) (hr : (rawNatLit? wa).run s₁ = .ok (some N₁, s₂))
    (hw2 : (r.whnf depth b).run s₂ = .ok (wb, s₃))
    (hr2 : (rawNatLit? wb).run s₃ = .ok (some N₂, s₄))
    (hres : (natOpResult c N₁ N₂).run s₄ = .ok (o, s₅)) :
    (redOpT r depth c a b).run s = .ok (o, s₅) := by
  simp only [redOpT, StateT.run_bind, hw, except_ok_bind, hr, hw2, hr2, hres]

theorem redWf_run_skip (c : NIdx) (a b : EIdx) (s s₁ : AState) (wf : List NIdx)
    (hwf : natOpWfNames.run s = .ok (wf, s)) (sup : Bool)
    (hs : (natLitSupported fe).run s = .ok (sup, s₁)) (hc : (wf.contains c && sup) = false) :
    (redWfT r fe depth c a b).run s = .ok (none, s₁) := by
  simp only [redWfT, StateT.run_bind, hwf, except_ok_bind, hs, hc]; rfl

theorem redWf_run_none1 (c : NIdx) (a b : EIdx) (s s₁ s₂ s₃ : AState) (wf : List NIdx)
    (hwf : natOpWfNames.run s = .ok (wf, s)) (sup : Bool)
    (hs : (natLitSupported fe).run s = .ok (sup, s₁)) (hc : (wf.contains c && sup) = true)
    (wa : EIdx) (hw : (r.whnf depth a).run s₁ = .ok (wa, s₂))
    (hr : (rawNatLit? wa).run s₂ = .ok (none, s₃)) :
    (redWfT r fe depth c a b).run s = .ok (none, s₃) := by
  simp only [redWfT, StateT.run_bind, hwf, except_ok_bind, hs, hc, ite_true, hw, hr]; rfl

theorem redWf_run_none2 (c : NIdx) (a b : EIdx) (s s₁ s₂ s₃ s₄ s₅ : AState) (wf : List NIdx)
    (hwf : natOpWfNames.run s = .ok (wf, s)) (sup : Bool)
    (hs : (natLitSupported fe).run s = .ok (sup, s₁)) (hc : (wf.contains c && sup) = true)
    (wa wb : EIdx) (N : Nat) (hw : (r.whnf depth a).run s₁ = .ok (wa, s₂))
    (hr : (rawNatLit? wa).run s₂ = .ok (some N, s₃))
    (hw2 : (r.whnf depth b).run s₃ = .ok (wb, s₄))
    (hr2 : (rawNatLit? wb).run s₄ = .ok (none, s₅)) :
    (redWfT r fe depth c a b).run s = .ok (none, s₅) := by
  simp only [redWfT, StateT.run_bind, hwf, except_ok_bind, hs, hc, ite_true, hw, hr, hw2, hr2]; rfl

end redruns


/-! ## `reduce_nat_succ`, `reduce_nat_op`, `reduce_nat_wf` -/

/-- The model of `reduce_nat_succ`: `(flag, result, memory)`. -/
def reduceNatSuccW (p : Prog) (n : Nat) (m : Mem) (mode vis d c b : Word) :
    Option (Word × Word × Mem) :=
  match callW p n "nat_lit_supported" [vis] m with
  | none => none
  | some (r₁, m₁) =>
  match callW p n "pin_at" [3] m₁ with
  | none => none
  | some (r₂, m₂) =>
  if c ≠ r₂.headD 0 then some (0, 0, m₂)
  else if r₁.headD 0 = 0 then some (0, 0, m₂)
  else
  match callW p n "whnf" [mode, vis, d, b] m₂ with
  | none => none
  | some (r₃, m₃) =>
  match callW p n "raw_nat_lit" [r₃.headD 0] m₃ with
  | none => none
  | some (r₄, m₄) =>
  if r₄.headD 0 = 0 then some (0, 0, m₄)
  else
  match callW p n "nat_succ_lit" [r₄.tail.headD 0, r₄.tail.tail.headD 0] m₄ with
  | none => none
  | some (r₅, m₅) => some (1, r₅.headD 0, m₅)

theorem reduceNatSucc_spec (p : Prog) (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St)
    (mode vis d c b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "reduce_nat_succ" [mode, vis, d, c, b]
    ⦃fun r s' => LocEq s' s₀ ∧
      reduceNatSuccW p n s₀.mem mode vis d c b = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.reduceNatSucc]
  simp only [callFn, reduceNatSuccL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "nat_lit_supported", callW_spec p n "pin_at", callW_spec p n "whnf",
      callW_spec p n "raw_nat_lit", callW_spec p n "nat_succ_lit"] <;>
    finish (gen := 30) [reduceNatSuccW]

/-- The model of `reduce_nat_op`: `(flag, result, memory)`. -/
def reduceNatOpW (p : Prog) (n : Nat) (m : Mem) (mode vis d c a b : Word) :
    Option (Word × Word × Mem) :=
  match callW p n "whnf" [mode, vis, d, a] m with
  | none => none
  | some (r₁, m₁) =>
  match callW p n "raw_nat_lit" [r₁.headD 0] m₁ with
  | none => none
  | some (r₂, m₂) =>
  if r₂.headD 0 = 0 then some (0, 0, m₂)
  else
  match callW p n "whnf" [mode, vis, d, b] m₂ with
  | none => none
  | some (r₃, m₃) =>
  match callW p n "raw_nat_lit" [r₃.headD 0] m₃ with
  | none => none
  | some (r₄, m₄) =>
  if r₄.headD 0 = 0 then some (0, 0, m₄)
  else
  match callW p n "nat_op_result" [c, r₂.tail.headD 0, r₂.tail.tail.headD 0, r₄.tail.headD 0,
      r₄.tail.tail.headD 0] m₄ with
  | none => none
  | some (r₅, m₅) => some (r₅.headD 0, r₅.tail.headD 0, m₅)

section ropw
variable (p : Prog) (n : Nat) (mode vis d c a b : Word) (m m₁ m₂ m₃ m₄ m₅ : Mem)
  (r₁ r₂ r₃ r₄ r₅ : List Word)

theorem reduceNatOpW_1 (h1 : callW p n "whnf" [mode, vis, d, a] m = some (r₁, m₁))
    (h2 : callW p n "raw_nat_lit" [r₁.headD 0] m₁ = some (r₂, m₂)) (h0 : r₂.headD 0 = 0) :
    reduceNatOpW p n m mode vis d c a b = some (0, 0, m₂) := by
  simp only [reduceNatOpW, h1, h2, h0, ↓reduceIte]

theorem reduceNatOpW_2 (h1 : callW p n "whnf" [mode, vis, d, a] m = some (r₁, m₁))
    (h2 : callW p n "raw_nat_lit" [r₁.headD 0] m₁ = some (r₂, m₂)) (h0 : ¬ r₂.headD 0 = 0)
    (h3 : callW p n "whnf" [mode, vis, d, b] m₂ = some (r₃, m₃))
    (h4 : callW p n "raw_nat_lit" [r₃.headD 0] m₃ = some (r₄, m₄)) (h00 : r₄.headD 0 = 0) :
    reduceNatOpW p n m mode vis d c a b = some (0, 0, m₄) := by
  simp only [reduceNatOpW, h1, h2, h0, h3, h4, h00, ↓reduceIte]

theorem reduceNatOpW_3 (h1 : callW p n "whnf" [mode, vis, d, a] m = some (r₁, m₁))
    (h2 : callW p n "raw_nat_lit" [r₁.headD 0] m₁ = some (r₂, m₂)) (h0 : ¬ r₂.headD 0 = 0)
    (h3 : callW p n "whnf" [mode, vis, d, b] m₂ = some (r₃, m₃))
    (h4 : callW p n "raw_nat_lit" [r₃.headD 0] m₃ = some (r₄, m₄)) (h00 : ¬ r₄.headD 0 = 0)
    (h5 : callW p n "nat_op_result" [c, r₂.tail.headD 0, r₂.tail.tail.headD 0, r₄.tail.headD 0,
      r₄.tail.tail.headD 0] m₄ = some (r₅, m₅)) :
    reduceNatOpW p n m mode vis d c a b = some (r₅.headD 0, r₅.tail.headD 0, m₅) := by
  simp only [reduceNatOpW, h1, h2, h0, h3, h4, h00, h5, ↓reduceIte]

end ropw

theorem reduceNatOp_spec (p : Prog) (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St)
    (mode vis d c a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "reduce_nat_op" [mode, vis, d, c, a, b]
    ⦃fun r s' => LocEq s' s₀ ∧
      reduceNatOpW p n s₀.mem mode vis d c a b = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.reduceNatOp]
  simp only [callFn, reduceNatOpL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "whnf", callW_spec p n "raw_nat_lit", callW_spec p n "nat_op_result"] <;>
  simp_all [reduceNatOpW, Cmp.eval, BinOp.eval, LocEq, St.setLocs_cons, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil,
    Locals.init_cons_zero, Locals.init_cons_succ, Sig.retVal, Sig.retOr]


/-- `natOpWfNames` with its pins read: pin word `k` is `w k`. -/
def natOpWfSel (w : Nat → Word) (c : Word) : Bool :=
  decide (c = w 22) || decide (c = w 23) || decide (c = w 24) || decide (c = w 25) ||
  decide (c = w 26) || decide (c = w 27) || decide (c = w 28) || decide (c = w 29)

theorem natOpIsWfL_spec (p : Prog) (hp : p.lookup "nat_op_is_wf" = some natOpIsWfL) (n : Nat)
    (s₀ : St) (c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nat_op_is_wf" [c]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ pinW s₀.mem 0 ≠ 0 ∧
      (r.headD 0 != 0) = natOpWfSel (pinW s₀.mem) c ∧ HW (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, natOpIsWfL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish [natOpWfSel, pinW_eq, HW]

theorem natOpWfNames_run {m : Mem} {a : AState} (h : PinsFull m a.pins) :
    natOpWfNames.run a = .ok ([decI (pinW m 22), decI (pinW m 23), decI (pinW m 24),
      decI (pinW m 25), decI (pinW m 26), decI (pinW m 27), decI (pinW m 28), decI (pinW m 29)], a) := by
  simp only [natOpWfNames, natDivName, natModName, natGcdName, natLandName, natLorName, natXorName,
    natShiftLeftName, natShiftRightName, pinNatDiv, pinNatMod, pinNatGcd, pinNatLand, pinNatLor,
    pinNatXor, pinNatShiftLeft, pinNatShiftRight, PIN_NAT_DIV, PIN_NAT_MOD, PIN_NAT_GCD, PIN_NAT_LAND,
    PIN_NAT_LOR, PIN_NAT_XOR, PIN_NAT_SHIFT_LEFT, PIN_NAT_SHIFT_RIGHT, StateT.run_bind,
    pinAt_run h _ (by decide : 21 < 51), pinAt_run h _ (by decide : 22 < 51),
    pinAt_run h _ (by decide : 23 < 51), pinAt_run h _ (by decide : 24 < 51),
    pinAt_run h _ (by decide : 25 < 51), pinAt_run h _ (by decide : 26 < 51),
    pinAt_run h _ (by decide : 27 < 51), pinAt_run h _ (by decide : 28 < 51), except_ok_bind]
  rfl

theorem wfContains {m : Mem} {a : AState} (h : PinsFull m a.pins) (c : Word) (hc : HW c) :
    ([decI (pinW m 22), decI (pinW m 23), decI (pinW m 24), decI (pinW m 25), decI (pinW m 26),
      decI (pinW m 27), decI (pinW m 28), decI (pinW m 29)] : List NIdx).contains (decI c) =
      natOpWfSel (pinW m) c := by
  have hb : ∀ i, i < 51 → ((decI c : NIdx) == decI (pinW m (1 + i))) = decide (c = pinW m (1 + i)) :=
    fun i hi => decI_beq _ _ hc (h.names_lt i hi)
  have e22 : ((decI c : NIdx) == decI (pinW m 22)) = decide (c = pinW m 22) := hb 21 (by decide)
  have e23 : ((decI c : NIdx) == decI (pinW m 23)) = decide (c = pinW m 23) := hb 22 (by decide)
  have e24 : ((decI c : NIdx) == decI (pinW m 24)) = decide (c = pinW m 24) := hb 23 (by decide)
  have e25 : ((decI c : NIdx) == decI (pinW m 25)) = decide (c = pinW m 25) := hb 24 (by decide)
  have e26 : ((decI c : NIdx) == decI (pinW m 26)) = decide (c = pinW m 26) := hb 25 (by decide)
  have e27 : ((decI c : NIdx) == decI (pinW m 27)) = decide (c = pinW m 27) := hb 26 (by decide)
  have e28 : ((decI c : NIdx) == decI (pinW m 28)) = decide (c = pinW m 28) := hb 27 (by decide)
  have e29 : ((decI c : NIdx) == decI (pinW m 29)) = decide (c = pinW m 29) := hb 28 (by decide)
  simp only [List.contains, List.elem, natOpWfSel, e22, e23, e24, e25, e26, e27, e28, e29]
  generalize decide (c = pinW m 22) = x1
  generalize decide (c = pinW m 23) = x2
  generalize decide (c = pinW m 24) = x3
  generalize decide (c = pinW m 25) = x4
  generalize decide (c = pinW m 26) = x5
  generalize decide (c = pinW m 27) = x6
  generalize decide (c = pinW m 28) = x7
  generalize decide (c = pinW m 29) = x8
  revert x1 x2 x3 x4 x5 x6 x7 x8
  decide


/-- The model of `reduce_nat_wf`: `(flag, result, memory)` (`none` where the L code aborts). -/
def reduceNatWfW (p : Prog) (n : Nat) (m : Mem) (mode vis d c a b : Word) :
    Option (Word × Word × Mem) :=
  match callW p n "nat_op_is_wf" [c] m with
  | none => none
  | some (r₁, m₁) =>
  match callW p n "nat_lit_supported" [vis] m₁ with
  | none => none
  | some (r₂, m₂) =>
  if r₁.headD 0 ≠ 0 ∧ r₂.headD 0 ≠ 0 then
    match callW p n "whnf" [mode, vis, d, a] m₂ with
    | none => none
    | some (r₃, m₃) =>
    match callW p n "raw_nat_lit" [r₃.headD 0] m₃ with
    | none => none
    | some (r₄, m₄) =>
    if r₄.headD 0 = 0 then some (0, 0, m₄)
    else
    match callW p n "whnf" [mode, vis, d, b] m₄ with
    | none => none
    | some (r₅, m₅) =>
    match callW p n "raw_nat_lit" [r₅.headD 0] m₅ with
    | none => none
    | some (r₆, m₆) =>
    if r₆.headD 0 = 0 then some (0, 0, m₆) else none
  else some (0, 0, m₂)

theorem reduceNatWf_spec (p : Prog) (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St)
    (mode vis d c a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "reduce_nat_wf" [mode, vis, d, c, a, b]
    ⦃fun r s' => LocEq s' s₀ ∧
      reduceNatWfW p n s₀.mem mode vis d c a b = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.reduceNatWf]
  simp only [callFn, reduceNatWfL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "nat_op_is_wf", callW_spec p n "nat_lit_supported", callW_spec p n "whnf",
      callW_spec p n "raw_nat_lit"] <;>
  simp_all [reduceNatWfW, Cmp.eval, BinOp.eval, LocEq, St.setLocs_cons, St.setLoc_loc, St.setLoc_mem,
    St.setLocs_nil, Locals.init_cons_zero, Locals.init_cons_succ, Sig.retVal, Sig.retOr]


/-- The model of `reduce_nat_k`: `(flag, result, memory)`. -/
def reduceNatKW (p : Prog) (n : Nat) (m : Mem) (mode vis d f b : Word) :
    Option (Word × Word × Mem) :=
  if rdW (m.arr64 CTL) (18 + tierW f) ≤ idxW f then none
  else
    match callW p n "pin_word" [52] m with
    | none => none
    | some (r₁, m₁) =>
      if rdW (m.arr64 CREC) (idxW f * 4 + tierW f * 2 + 1) ≠ r₁.headD 0 then some (0, 0, m₁)
      else
        match callW p n "reduce_nat_succ" [mode, vis, d, rdW (m.arr64 CREC) (idxW f * 4 + tierW f * 2),
            b] m₁ with
        | none => none
        | some (r₂, m₂) => some (r₂.headD 0, r₂.tail.headD 0, m₂)

theorem reduceNatK_spec (p : Prog) (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St) (mode vis d f b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "reduce_nat_k" [mode, vis, d, f, b]
    ⦃fun r s' => LocEq s' s₀ ∧
      reduceNatKW p n s₀.mem mode vis d f b = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.reduceNatK]
  simp only [callFn, reduceNatKL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "pin_word", callW_spec p n "reduce_nat_succ"] <;>
    finish (gen := 30) [reduceNatKW, tierW, idxW]

/-- The model of `reduce_nat_ap`: `(flag, result, memory)`. -/
def reduceNatApW (p : Prog) (n : Nat) (m : Mem) (mode vis d f b : Word) :
    Option (Word × Word × Mem) :=
  if rdW (m.arr64 CTL) (4 + tierW f) ≤ idxW f then none
  else if rdW (m.arr64 AREC) (idxW f * 4 + tierW f * 2) >>> 28 ≠ 3 then some (0, 0, m)
  else if tierW (rdW (m.arr64 AREC) (idxW f * 4 + tierW f * 2)) ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if rdW (m.arr64 CTL) (18 + tierW (rdW (m.arr64 AREC) (idxW f * 4 + tierW f * 2))) ≤
      idxW (rdW (m.arr64 AREC) (idxW f * 4 + tierW f * 2)) then none
  else
    match callW p n "pin_word" [52] m with
    | none => none
    | some (r₁, m₁) =>
      if rdW (m.arr64 CREC) (idxW (rdW (m.arr64 AREC) (idxW f * 4 + tierW f * 2)) * 4 +
          tierW (rdW (m.arr64 AREC) (idxW f * 4 + tierW f * 2)) * 2 + 1) ≠ r₁.headD 0 then
        some (0, 0, m₁)
      else
        match callW p n "nat_bin_op_name" [rdW (m.arr64 CREC)
            (idxW (rdW (m.arr64 AREC) (idxW f * 4 + tierW f * 2)) * 4 +
              tierW (rdW (m.arr64 AREC) (idxW f * 4 + tierW f * 2)) * 2)] m₁ with
        | none => none
        | some (r₂, m₂) =>
        match callW p n "nat_op_stored" [vis, rdW (m.arr64 CREC)
            (idxW (rdW (m.arr64 AREC) (idxW f * 4 + tierW f * 2)) * 4 +
              tierW (rdW (m.arr64 AREC) (idxW f * 4 + tierW f * 2)) * 2)] m₂ with
        | none => none
        | some (r₃, m₃) =>
        if r₂.headD 0 ≠ 0 ∧ r₃.headD 0 ≠ 0 then
          match callW p n "reduce_nat_op" [mode, vis, d, rdW (m.arr64 CREC)
              (idxW (rdW (m.arr64 AREC) (idxW f * 4 + tierW f * 2)) * 4 +
                tierW (rdW (m.arr64 AREC) (idxW f * 4 + tierW f * 2)) * 2),
              rdW (m.arr64 AREC) (idxW f * 4 + tierW f * 2 + 1), b] m₃ with
          | none => none
          | some (r₄, m₄) => some (r₄.headD 0, r₄.tail.headD 0, m₄)
        else
          match callW p n "reduce_nat_wf" [mode, vis, d, rdW (m.arr64 CREC)
              (idxW (rdW (m.arr64 AREC) (idxW f * 4 + tierW f * 2)) * 4 +
                tierW (rdW (m.arr64 AREC) (idxW f * 4 + tierW f * 2)) * 2),
              rdW (m.arr64 AREC) (idxW f * 4 + tierW f * 2 + 1), b] m₃ with
          | none => none
          | some (r₄, m₄) => some (r₄.headD 0, r₄.tail.headD 0, m₄)

set_option maxHeartbeats 4000000 in
theorem reduceNatAp_spec (p : Prog) (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St) (mode vis d f b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "reduce_nat_ap" [mode, vis, d, f, b]
    ⦃fun r s' => LocEq s' s₀ ∧
      reduceNatApW p n s₀.mem mode vis d f b = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.reduceNatAp]
  simp only [callFn, reduceNatApL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "pin_word", callW_spec p n "nat_bin_op_name", callW_spec p n "nat_op_stored",
      callW_spec p n "reduce_nat_op", callW_spec p n "reduce_nat_wf"] <;>
    finish (gen := 30) [reduceNatApW, tierW, idxW]

/-- The model of `reduce_nat_head`: `(flag, result, memory)`. -/
def reduceNatHeadW (p : Prog) (n : Nat) (m : Mem) (mode vis d f b : Word) :
    Option (Word × Word × Mem) :=
  if tierW f ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if f >>> 28 = 3 then
    (match callW p n "reduce_nat_k" [mode, vis, d, f, b] m with
      | none => none
      | some (r₁, m₁) => some (r₁.headD 0, r₁.tail.headD 0, m₁))
  else if f >>> 28 = 4 then
    (match callW p n "reduce_nat_ap" [mode, vis, d, f, b] m with
      | none => none
      | some (r₁, m₁) => some (r₁.headD 0, r₁.tail.headD 0, m₁))
  else if f >>> 28 = 0 then
    (if rdW (m.arr64 CTL) (22 + tierW f) ≤ idxW f then none else some (0, 0, m))
  else if f >>> 28 = 1 then
    (if rdW (m.arr64 CTL) (26 + tierW f) ≤ idxW f then none else some (0, 0, m))
  else if f >>> 28 = 2 then
    (if rdW (m.arr64 CTL) (16 + tierW f) ≤ idxW f then none else some (0, 0, m))
  else if f >>> 28 = 5 then
    (if rdW (m.arr64 CTL) (28 + tierW f) ≤ idxW f then none else some (0, 0, m))
  else if f >>> 28 = 6 then
    (if rdW (m.arr64 CTL) (30 + tierW f) ≤ idxW f then none else some (0, 0, m))
  else if f >>> 28 = 7 then
    (if rdW (m.arr64 CTL) (20 + tierW f) ≤ idxW f then none else some (0, 0, m))
  else if f >>> 28 = 8 then
    (if rdW (m.arr64 CTL) (2 + tierW f) ≤ idxW f then none else some (0, 0, m))
  else if f >>> 28 ≠ 9 then none
  else if rdW (m.arr64 CTL) (32 + tierW f) ≤ idxW f then none
  else some (0, 0, m)

theorem reduceNatHead_spec (p : Prog) (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St)
    (mode vis d f b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "reduce_nat_head" [mode, vis, d, f, b]
    ⦃fun r s' => LocEq s' s₀ ∧
      reduceNatHeadW p n s₀.mem mode vis d f b = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.reduceNatHead]
  simp only [callFn, reduceNatHeadL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "reduce_nat_k", callW_spec p n "reduce_nat_ap"] <;>
    finish (gen := 30) [reduceNatHeadW, tierW, idxW]

/-- The model of `reduce_nat`: `(flag, result, memory)`. -/
def reduceNatW (p : Prog) (n : Nat) (m : Mem) (mode vis d e : Word) :
    Option (Word × Word × Mem) :=
  if e >>> 28 ≠ 4 then some (0, 0, m)
  else if tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if rdW (m.arr64 CTL) (4 + tierW e) ≤ idxW e then none
  else
    match callW p n "reduce_nat_head" [mode, vis, d, rdW (m.arr64 AREC) (idxW e * 4 + tierW e * 2),
        rdW (m.arr64 AREC) (idxW e * 4 + tierW e * 2 + 1)] m with
    | none => none
    | some (r₁, m₁) => some (r₁.headD 0, r₁.tail.headD 0, m₁)

theorem reduceNat_spec (p : Prog) (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St) (mode vis d e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "reduce_nat" [mode, vis, d, e]
    ⦃fun r s' => LocEq s' s₀ ∧
      reduceNatW p n s₀.mem mode vis d e = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.reduceNat]
  simp only [callFn, reduceNatL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "reduce_nat_head"] <;>
    finish (gen := 30) [reduceNatW, tierW, idxW]


theorem natAddArm_run_internE {a₁ a₂ : AState} {x : EIdx} {u v : Nat}
    (h : (natAddArm u v).run a₁ = .ok (some x, a₂)) :
    (internE (.lit (.natVal (u + v)))).run a₁ = .ok (x, a₂) := by
  have e : (natAddArm u v).run a₁ =
      Except.map (fun q => (some q.1, q.2)) ((internE (.lit (.natVal (u + v)))).run a₁) := by
    simp only [natAddArm, StateT.run_bind]
    cases (internE (.lit (.natVal (u + v)))).run a₁ <;> rfl
  rw [e] at h
  cases hh : (internE (.lit (.natVal (u + v)))).run a₁ with
  | error e => rw [hh] at h; cases h
  | ok q =>
    rw [hh] at h
    simp only [Except.map, Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨x', a'⟩ := q
    simp only at h1 h2
    rw [h1, h2]

/-- **`whnf` keeps the pool**: a call of the L `whnf` at fuel `n` from a related state only
appends to the limb pool (`Grows`). The twin's `whnf` returns numbers (`rawNatLit?`), so a slice
held across a `whnf` call must survive it; `WhnfSlot` says nothing about the pool. -/
def WhnfGrowsPool (p : Prog) (n : Nat) : Prop :=
  ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d e : Word) (r : List Word) (m' : Mem),
    SlotPre s₀ a₀ dn vis fe MM eb mode → HW e →
    callW p n "whnf" [mode, vis, d, e] s₀.mem = some (r, m') → Grows s₀.mem m'

/-- `WhnfGrowsPool` at every L fuel up to `n`. -/
def WhnfGrowsUpTo (p : Prog) (n : Nat) : Prop := ∀ k, k ≤ n → WhnfGrowsPool p k


theorem pinW_const_frame {m m' : Mem} (hf : MemFrame [CREC, CSLOT] [18, 19] m m') (k : Nat) :
    pinW m' k = pinW m k := by
  have : m'.arr64 PINS = m.arr64 PINS := hf.arr_eq PINS (by simp [CREC, CSLOT, PINS]) (by decide)
  simp only [pinW, this]

section refs18
variable (p : Prog)

theorem callW_reduceNatSucc (hp : WhnfDeltaProg' p) (n F : Nat) (hF : n ≤ F) (hn2 : n ≤ 2 ^ 62)
    (hk : KnotUpTo p n) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (MM : ModeMaps) (eb mode d c b : Word) (hS : SlotPre s₀ a₀ dn vis fe MM eb mode)
    (hc : HW c) (hb : HW b) (r : List Word) (m' : Mem)
    (h : callW p n "reduce_nat_succ" [mode, vis, d, c, b] s₀.mem = some (r, m')) :
    CoreRef (redSuccT (coreKnot (decMode mode) fe id F) fe d.toNat (decI c) (decE b)) a₀ decOptR dn
      s₀.mem vis fe MM eb r m' ResW := by
  have hC := hS.rel
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (reduceNatSucc_spec p hp.toWhnfDeltaProg n s₀ mode vis d c b) h
  unfold reduceNatSuccW at hW
  cases h1 : callW p n "nat_lit_supported" [vis] s₀.mem with
  | none => rw [h1] at hW; cases hW
  | some q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  rw [h1] at hW
  dsimp only at hW
  obtain ⟨hok1, hS1, hres1, hfr1, hrh1⟩ := callW_natLitSupported p hp n s₀ a₀ dn vis fe MM eb hC r₁ m₁ h1
  cases h2 : callW p n "pin_at" [3] m₁ with
  | none => rw [h2] at hW; cases hW
  | some q₂ =>
  obtain ⟨r₂, m₂⟩ := q₂
  rw [h2] at hW
  dsimp only at hW
  obtain ⟨hm2, -, -, hr₂⟩ := callW_pinAt p hp.pinAt n m₁ 3 r₂ m₂ h2
  subst m₂
  simp only [show (3 : Word).toNat = 3 from rfl] at hr₂
  have hr₂' : r₂.headD 0 = pinW s₀.mem 4 := by rw [hr₂, pinW_const_frame hfr1]
  -- the twin's `natLitSupported`
  have hsup : (natLitSupported fe).run a₀ = .ok (decBool r₁, AM.st (natLitSupported fe) a₀) := by
    have := AM.run_of_ok _ _ hok1
    rw [hres1] at this
    exact this
  generalize AM.st (natLitSupported fe) a₀ = a₁ at hsup hS1
  have hcw : HW (pinW s₀.mem 4) := hC.pins.names_lt 3 (by decide)
  have hskip : (c ≠ r₂.headD 0 ∨ r₁.headD 0 = 0) →
      ((decI c : NIdx) == decI (pinW s₀.mem 4) && decBool r₁) = false := by
    intro hh
    rw [decI_beq _ _ hc hcw]
    rcases hh with hh | hh
    · rw [hr₂'] at hh
      have : decide (c = pinW s₀.mem 4) = false := decide_eq_false hh
      rw [this]; rfl
    · have : decBool r₁ = false := by simp only [decBool, hh]; rfl
      rw [this]; simp
  have hgo : (c = r₂.headD 0) → ¬ r₁.headD 0 = 0 →
      ((decI c : NIdx) == decI (pinW s₀.mem 4) && decBool r₁) = true := by
    intro hh1 hh2
    rw [decI_beq _ _ hc hcw]
    have h1 : c = pinW s₀.mem 4 := by rw [← hr₂']; exact hh1
    have h2 : decBool r₁ = true := by simp only [decBool, bne_iff_ne, ne_eq]; exact hh2
    rw [h2]; simp [h1]
  by_cases hcn : c ≠ r₂.headD 0
  · rw [if_pos hcn] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    rw [← hm]
    have hz := redSucc_run_skip (coreKnot (decMode mode) fe id F) fe d.toNat (decI c) (decE b) a₀ a₁
      s₀.mem hC.pins (decBool r₁) hsup (hskip (Or.inl hcn))
    obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
    refine CRef.core (m' := m₁) ⟨hok', by rw [hst']; exact hS1, ?_, hfr1, ?_⟩
    · rw [hres']; simp only [decOptR, decOpt, ← hr0]; rfl
    · unfold ResW HW; rw [← hr0, ← hr1]; exact ⟨by decide, by decide⟩
  rw [if_neg hcn] at hW
  by_cases hs0 : r₁.headD 0 = 0
  · rw [if_pos hs0] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    rw [← hm]
    have hz := redSucc_run_skip (coreKnot (decMode mode) fe id F) fe d.toNat (decI c) (decE b) a₀ a₁
      s₀.mem hC.pins (decBool r₁) hsup (hskip (Or.inr hs0))
    obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
    refine CRef.core (m' := m₁) ⟨hok', by rw [hst']; exact hS1, ?_, hfr1, ?_⟩
    · rw [hres']; simp only [decOptR, decOpt, ← hr0]; rfl
    · unfold ResW HW; rw [← hr0, ← hr1]; exact ⟨by decide, by decide⟩
  rw [if_neg hs0] at hW
  have hcond := hgo (by simpa using hcn) hs0
  -- `whnf`
  cases h3 : callW p n "whnf" [mode, vis, d, b] m₁ with
  | none => rw [h3] at hW; cases hW
  | some q₃ =>
  obtain ⟨r₃, m₃⟩ := q₃
  rw [h3] at hW
  dsimp only at hW
  have hSP1 : SlotPre ⟨m₁, Locals.init []⟩ a₁ dn vis fe MM eb mode := ⟨hS1, hS.mode4, hS.eb_mode⟩
  have hkn : KnotOK p n := hk n (by omega)
  obtain ⟨hok3, ⟨M', hS3, hK3, hSt3⟩, hres3, hrw3⟩ := CoreSpec.of_callW
    (hkn.whnf F ⟨m₁, Locals.init []⟩ a₁ dn vis fe MM eb mode d b (by omega) (by omega) hSP1 hb) h3
  cases h4 : callW p n "raw_nat_lit" [r₃.headD 0] m₃ with
  | none => rw [h4] at hW; cases hW
  | some q₄ =>
  obtain ⟨r₄, m₄⟩ := q₄
  rw [h4] at hW
  dsimp only at hW
  have hrun3 := AM.run_of_ok _ _ hok3
  rw [hres3] at hrun3
  generalize AM.st ((coreKnot (decMode mode) fe id F).whnf d.toNat (decE b)) a₁ = a₂ at hrun3 hS3
  obtain ⟨hm4, hrun4, hres4, hslice4⟩ := callW_rawNatLit p hp n ⟨m₃, Locals.init []⟩ a₂ dn vis fe M' eb _
    hS3 hrw3 r₄ m₄ h4
  subst m₄
  have hStK1 := StackKept.of_const_frame hfr1
  by_cases hf : r₄.headD 0 = 0
  · rw [if_pos hf] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    rw [← hm]
    have hnone : rawDec m₃ r₄ = none := by unfold rawDec; rw [if_pos hf]
    rw [hnone] at hrun4
    have hz := redSucc_run_none (coreKnot (decMode mode) fe id F) fe d.toNat (decI c) (decE b) a₀ a₁ a₂ a₂
      s₀.mem hC.pins (decBool r₁) hsup hcond (decE (r₃.headD 0)) (by rw [hrun3]; rfl) hrun4
    obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
    refine ⟨hok', ?_, ?_, ?_⟩
    · rw [hst']; exact ⟨M', hS3, hK3, hStK1.trans hSt3⟩
    · rw [hres']; simp only [decOptR, decOpt, ← hr0]; rfl
    · unfold ResW HW; rw [← hr0, ← hr1]; exact ⟨by decide, by decide⟩
  rw [if_neg hf] at hW
  obtain ⟨hsl, hnorm⟩ := hslice4 hf
  cases h5 : callW p n "nat_succ_lit" [r₄.tail.headD 0, r₄.tail.tail.headD 0] m₃ with
  | none => rw [h5] at hW; cases hW
  | some q₅ =>
  obtain ⟨r₅, m₅⟩ := q₅
  rw [h5] at hW
  dsimp only at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr0, hr1, hm⟩ := hW
  rw [← hm]
  obtain ⟨hok5, hS5, hres5, hfr5, hhw5⟩ := callW_natSuccLit p hp n ⟨m₃, Locals.init []⟩ a₂ dn vis fe M' eb _ _
    hS3 hsl r₅ m₅ h5
  have hsome : rawDec m₃ r₄ = some (pv (m₃.arr64 POOL) (r₄.tail.headD 0).toNat
      (r₄.tail.tail.headD 0).toNat) := by unfold rawDec; rw [if_neg hf]
  rw [hsome] at hrun4
  have hi := natAddArm_run_internE (u := pv (m₃.arr64 POOL) (r₄.tail.headD 0).toNat
      (r₄.tail.tail.headD 0).toNat) (v := 1) (by rw [AM.run_of_ok _ _ hok5, hres5])
  have hz := redSucc_run_some (coreKnot (decMode mode) fe id F) fe d.toNat (decI c) (decE b) a₀ a₁ a₂ a₂ _
    s₀.mem hC.pins (decBool r₁) hsup hcond (decE (r₃.headD 0)) (by rw [hrun3]; rfl) _ hrun4 _ hi
  obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
  refine ⟨hok', ?_, ?_, ?_⟩
  · rw [hst']; exact ⟨M', hS5, hK3, (hStK1.trans hSt3).trans (StackKept.of_nat_frame hfr5)⟩
  · rw [hres']; simp only [decOptR, decOpt, ← hr0, ← hr1]; simp
  · unfold ResW HW; rw [← hr0, ← hr1]; exact ⟨by decide, hhw5⟩

end refs18


/-- **A slice below the old top survives a growth of the pool**: the slice, its value and its
normalisation. -/
theorem Grows.slice {m m' : Mem} (hg : Grows m m') {o l : Word} (hs : SliceOK m o l)
    (hn : Norm (m.arr64 POOL) o.toNat l.toNat) :
    SliceOK m' o l ∧ pv (m'.arr64 POOL) o.toNat l.toNat = pv (m.arr64 POOL) o.toNat l.toNat ∧
      Norm (m'.arr64 POOL) o.toNat l.toNat := by
  obtain ⟨-, hag, hle, -, -⟩ := hg
  refine ⟨?_, Agree.pv _ _ _ _ _ hag (by unfold SliceOK at hs; exact hs), ?_⟩
  · unfold SliceOK at hs ⊢; omega
  · intro hpos
    have := hn hpos
    have hlt : o.toNat + (l.toNat - 1) < m.top.toNat := by unfold SliceOK at hs; omega
    rw [show (m'.arr64 POOL)[o.toNat + (l.toNat - 1)]? = (m.arr64 POOL)[o.toNat + (l.toNat - 1)]? from
      hag _ hlt]
    exact this

/-- `nat_op_result` refines `natOpResult` under `CoreS` (the `Nat` lane's: `PinsNatOp.lean`'s
`natOpResultL_refines`, at `ArenaD` and `CoreS`, in the whnf program). Taken as a hypothesis. -/
def NatOpResultOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb c oa la ob lb : Word), CoreS dn s₀.mem a₀ vis fe MM eb → HW c →
    SliceOK s₀.mem oa la → SliceOK s₀.mem ob lb →
    Norm (s₀.mem.arr64 POOL) oa.toNat la.toNat → Norm (s₀.mem.arr64 POOL) ob.toNat lb.toNat →
    CoreSpec p n "nat_op_result" [c, oa, la, ob, lb]
      (natOpResult (decI c) (pv (s₀.mem.arr64 POOL) oa.toNat la.toNat)
        (pv (s₀.mem.arr64 POOL) ob.toNat lb.toNat)) decOptR s₀ a₀ dn vis fe MM eb ResW


section refs19
variable (p : Prog)

theorem callW_reduceNatOp (hp : WhnfDeltaProg' p) (hno : NatOpResultOK p) (n F : Nat) (hF : n ≤ F)
    (hn2 : n ≤ 2 ^ 62) (hk : KnotUpTo p n) (hgr : WhnfGrowsUpTo p n) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb mode d c a b : Word) (hS : SlotPre s₀ a₀ dn vis fe MM eb mode) (hc : HW c) (ha : HW a)
    (hb : HW b) (r : List Word) (m' : Mem)
    (h : callW p n "reduce_nat_op" [mode, vis, d, c, a, b] s₀.mem = some (r, m')) :
    CoreRef (redOpT (coreKnot (decMode mode) fe id F) d.toNat (decI c) (decE a) (decE b)) a₀ decOptR dn
      s₀.mem vis fe MM eb r m' ResW := by
  have hC := hS.rel
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (reduceNatOp_spec p hp.toWhnfDeltaProg n s₀ mode vis d c a b) h
  unfold reduceNatOpW at hW
  have hkn : KnotOK p n := hk n (by omega)
  -- first `whnf`
  cases h1 : callW p n "whnf" [mode, vis, d, a] s₀.mem with
  | none => rw [h1] at hW; cases hW
  | some q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  rw [h1] at hW
  dsimp only at hW
  obtain ⟨hok1, ⟨M₁, hS₁, hK₁, hSt₁⟩, hres1, hrw1⟩ := CoreSpec.of_callW
    (hkn.whnf F s₀ a₀ dn vis fe MM eb mode d a (by omega) (by omega) hS ha) h1
  have hrun1 := AM.run_of_ok _ _ hok1
  rw [hres1] at hrun1
  generalize AM.st ((coreKnot (decMode mode) fe id F).whnf d.toNat (decE a)) a₀ = a₁ at hrun1 hS₁
  cases h2 : callW p n "raw_nat_lit" [r₁.headD 0] m₁ with
  | none => rw [h2] at hW; cases hW
  | some q₂ =>
  obtain ⟨r₂, m₂⟩ := q₂
  rw [h2] at hW
  dsimp only at hW
  obtain ⟨hm2, hrun2, hres2, hslice2⟩ := callW_rawNatLit p hp n ⟨m₁, Locals.init []⟩ a₁ dn vis fe M₁ eb _
    hS₁ hrw1 r₂ m₂ h2
  subst m₂
  by_cases hf2 : r₂.headD 0 = 0
  · rw [if_pos hf2] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    rw [← hm]
    have hnone : rawDec m₁ r₂ = none := by unfold rawDec; rw [if_pos hf2]
    rw [hnone] at hrun2
    have hz := redOp_run_none1 (coreKnot (decMode mode) fe id F) d.toNat (decI c) (decE a) (decE b) a₀ a₁
      a₁ (decE (r₁.headD 0)) (by rw [hrun1]; rfl) hrun2
    obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
    refine ⟨hok', ?_, ?_, ?_⟩
    · rw [hst']; exact ⟨M₁, hS₁, hK₁, hSt₁⟩
    · rw [hres']; simp only [decOptR, decOpt, ← hr0]; rfl
    · unfold ResW HW; rw [← hr0, ← hr1]; exact ⟨by decide, by decide⟩
  rw [if_neg hf2] at hW
  obtain ⟨hsl2, hnorm2⟩ := hslice2 hf2
  have hsome2 : rawDec m₁ r₂ = some (pv (m₁.arr64 POOL) (r₂.tail.headD 0).toNat
      (r₂.tail.tail.headD 0).toNat) := by unfold rawDec; rw [if_neg hf2]
  rw [hsome2] at hrun2
  -- second `whnf`
  cases h3 : callW p n "whnf" [mode, vis, d, b] m₁ with
  | none => rw [h3] at hW; cases hW
  | some q₃ =>
  obtain ⟨r₃, m₃⟩ := q₃
  rw [h3] at hW
  dsimp only at hW
  have hSP₂ : SlotPre ⟨m₁, Locals.init []⟩ a₁ dn vis fe M₁ eb mode := ⟨hS₁, hS.mode4, hS.eb_mode⟩
  obtain ⟨hok3, ⟨M₃, hS₃, hK₃, hSt₃⟩, hres3, hrw3⟩ := CoreSpec.of_callW
    (hkn.whnf F ⟨m₁, Locals.init []⟩ a₁ dn vis fe M₁ eb mode d b (by omega) (by omega) hSP₂ hb) h3
  have hgrow : Grows m₁ m₃ := hgr n (by omega) ⟨m₁, Locals.init []⟩ a₁ dn vis fe M₁ eb mode d b r₃ m₃ hSP₂ hb h3
  have hrun3 := AM.run_of_ok _ _ hok3
  rw [hres3] at hrun3
  generalize AM.st ((coreKnot (decMode mode) fe id F).whnf d.toNat (decE b)) a₁ = a₂ at hrun3 hS₃
  cases h4 : callW p n "raw_nat_lit" [r₃.headD 0] m₃ with
  | none => rw [h4] at hW; cases hW
  | some q₄ =>
  obtain ⟨r₄, m₄⟩ := q₄
  rw [h4] at hW
  dsimp only at hW
  obtain ⟨hm4, hrun4, hres4, hslice4⟩ := callW_rawNatLit p hp n ⟨m₃, Locals.init []⟩ a₂ dn vis fe M₃ eb _
    hS₃ hrw3 r₄ m₄ h4
  subst m₄
  by_cases hf4 : r₄.headD 0 = 0
  · rw [if_pos hf4] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    rw [← hm]
    have hnone : rawDec m₃ r₄ = none := by unfold rawDec; rw [if_pos hf4]
    rw [hnone] at hrun4
    have hz := redOp_run_none2 (coreKnot (decMode mode) fe id F) d.toNat (decI c) (decE a) (decE b) a₀ a₁
      a₁ a₂ a₂ (decE (r₁.headD 0)) (decE (r₃.headD 0)) _ (by rw [hrun1]; rfl) hrun2
      (by rw [hrun3]; rfl) hrun4
    obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
    refine ⟨hok', ?_, ?_, ?_⟩
    · rw [hst']; exact ⟨M₃, hS₃, hK₁.trans hK₃, hSt₁.trans hSt₃⟩
    · rw [hres']; simp only [decOptR, decOpt, ← hr0]; rfl
    · unfold ResW HW; rw [← hr0, ← hr1]; exact ⟨by decide, by decide⟩
  rw [if_neg hf4] at hW
  obtain ⟨hsl4, hnorm4⟩ := hslice4 hf4
  have hsome4 : rawDec m₃ r₄ = some (pv (m₃.arr64 POOL) (r₄.tail.headD 0).toNat
      (r₄.tail.tail.headD 0).toNat) := by unfold rawDec; rw [if_neg hf4]
  rw [hsome4] at hrun4
  obtain ⟨hsl2', hpv2, hnorm2'⟩ := hgrow.slice hsl2 hnorm2
  cases h5 : callW p n "nat_op_result" [c, r₂.tail.headD 0, r₂.tail.tail.headD 0, r₄.tail.headD 0,
      r₄.tail.tail.headD 0] m₃ with
  | none => rw [h5] at hW; cases hW
  | some q₅ =>
  obtain ⟨r₅, m₅⟩ := q₅
  rw [h5] at hW
  dsimp only at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr0, hr1, hm⟩ := hW
  rw [← hm]
  obtain ⟨hok5, ⟨M₅, hS₅, hK₅, hSt₅⟩, hres5, hrw5⟩ := CoreSpec.of_callW
    (hno n ⟨m₃, Locals.init []⟩ a₂ dn vis fe M₃ eb c _ _ _ _ hS₃ hc hsl2' hsl4 hnorm2' hnorm4) h5
  have hres5' := AM.run_of_ok _ _ hok5
  rw [hres5] at hres5'
  dsimp only at hres5' hS₅
  rw [hpv2] at hres5' hS₅
  have hz := redOp_run_some (coreKnot (decMode mode) fe id F) d.toNat (decI c) (decE a) (decE b) a₀ a₁
    a₁ a₂ a₂ (AM.st (natOpResult (decI c) (pv (m₁.arr64 POOL) (r₂.tail.headD 0).toNat
      (r₂.tail.tail.headD 0).toNat) (pv (m₃.arr64 POOL) (r₄.tail.headD 0).toNat
      (r₄.tail.tail.headD 0).toNat)) a₂)
    (decE (r₁.headD 0)) (decE (r₃.headD 0))
    (pv (m₁.arr64 POOL) (r₂.tail.headD 0).toNat (r₂.tail.tail.headD 0).toNat)
    (pv (m₃.arr64 POOL) (r₄.tail.headD 0).toNat (r₄.tail.tail.headD 0).toNat)
    (decOptR r₅) (by rw [hrun1]; rfl) hrun2 (by rw [hrun3]; rfl) hrun4 hres5'
  obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
  refine ⟨hok', ?_, ?_, ?_⟩
  · rw [hst']; exact ⟨M₅, hS₅, (hK₁.trans hK₃).trans hK₅, (hSt₁.trans hSt₃).trans hSt₅⟩
  · rw [hres']; simp only [decOptR, ← hr0, ← hr1]
  · unfold ResW at hrw5 ⊢; rw [← hr0, ← hr1]; exact hrw5

end refs19


section refs20
variable (p : Prog)

theorem callW_reduceNatWf (hp : WhnfDeltaProg' p) (n F : Nat) (hF : n ≤ F) (hn2 : n ≤ 2 ^ 62)
    (hk : KnotUpTo p n) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (MM : ModeMaps) (eb mode d c a b : Word) (hS : SlotPre s₀ a₀ dn vis fe MM eb mode)
    (hc : HW c) (ha : HW a) (hb : HW b) (r : List Word) (m' : Mem)
    (h : callW p n "reduce_nat_wf" [mode, vis, d, c, a, b] s₀.mem = some (r, m')) :
    CoreRef (redWfT (coreKnot (decMode mode) fe id F) fe d.toNat (decI c) (decE a) (decE b)) a₀ decOptR
      dn s₀.mem vis fe MM eb r m' ResW := by
  have hC := hS.rel
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (reduceNatWf_spec p hp.toWhnfDeltaProg n s₀ mode vis d c a b) h
  unfold reduceNatWfW at hW
  have hkn : KnotOK p n := hk n (by omega)
  cases h1 : callW p n "nat_op_is_wf" [c] s₀.mem with
  | none => rw [h1] at hW; cases hW
  | some q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  rw [h1] at hW
  dsimp only at hW
  obtain ⟨s₁', hs₁', hm₁, -, -, hwfsel, -⟩ := triple_of_callW
    (natOpIsWfL_spec p hp.natOpIsWf n ⟨s₀.mem, Locals.init []⟩ c) h1
  have hm1 : m₁ = s₀.mem := by rw [← hs₁', hm₁]
  subst hm1
  cases h2 : callW p n "nat_lit_supported" [vis] s₀.mem with
  | none => rw [h2] at hW; cases hW
  | some q₂ =>
  obtain ⟨r₂, m₂⟩ := q₂
  rw [h2] at hW
  dsimp only at hW
  obtain ⟨hok2, hS2, hres2, hfr2, hrh2⟩ := callW_natLitSupported p hp n s₀ a₀ dn vis fe MM eb hC r₂ m₂ h2
  have hsup : (natLitSupported fe).run a₀ = .ok (decBool r₂, AM.st (natLitSupported fe) a₀) := by
    have := AM.run_of_ok _ _ hok2
    rw [hres2] at this
    exact this
  generalize AM.st (natLitSupported fe) a₀ = a₁ at hsup hS2
  have hwf := natOpWfNames_run hC.pins
  have hcont := wfContains hC.pins c hc
  have hbool : ∀ (hh : r₁.headD 0 ≠ 0 ∧ r₂.headD 0 ≠ 0), (([decI (pinW s₀.mem 22), decI (pinW s₀.mem 23),
      decI (pinW s₀.mem 24), decI (pinW s₀.mem 25), decI (pinW s₀.mem 26), decI (pinW s₀.mem 27),
      decI (pinW s₀.mem 28), decI (pinW s₀.mem 29)] : List NIdx).contains (decI c) && decBool r₂) = true := by
    intro hh
    rw [hcont]
    have h1 : natOpWfSel (pinW s₀.mem) c = true := by rw [← hwfsel]; simpa using hh.1
    have h2 : decBool r₂ = true := by simp only [decBool, bne_iff_ne, ne_eq]; exact hh.2
    rw [h1, h2]; rfl
  by_cases hgo : r₁.headD 0 ≠ 0 ∧ r₂.headD 0 ≠ 0
  · rw [if_pos hgo] at hW
    have hSP1 : SlotPre ⟨m₂, Locals.init []⟩ a₁ dn vis fe MM eb mode := ⟨hS2, hS.mode4, hS.eb_mode⟩
    cases h3 : callW p n "whnf" [mode, vis, d, a] m₂ with
    | none => rw [h3] at hW; cases hW
    | some q₃ =>
    obtain ⟨r₃, m₃⟩ := q₃
    rw [h3] at hW
    dsimp only at hW
    obtain ⟨hok3, ⟨M₃, hS₃, hK₃, hSt₃⟩, hres3, hrw3⟩ := CoreSpec.of_callW
      (hkn.whnf F ⟨m₂, Locals.init []⟩ a₁ dn vis fe MM eb mode d a (by omega) (by omega) hSP1 ha) h3
    have hrun3 := AM.run_of_ok _ _ hok3
    rw [hres3] at hrun3
    generalize AM.st ((coreKnot (decMode mode) fe id F).whnf d.toNat (decE a)) a₁ = a₂ at hrun3 hS₃
    cases h4 : callW p n "raw_nat_lit" [r₃.headD 0] m₃ with
    | none => rw [h4] at hW; cases hW
    | some q₄ =>
    obtain ⟨r₄, m₄⟩ := q₄
    rw [h4] at hW
    dsimp only at hW
    obtain ⟨hm4, hrun4, hres4, hslice4⟩ := callW_rawNatLit p hp n ⟨m₃, Locals.init []⟩ a₂ dn vis fe M₃ eb _
      hS₃ hrw3 r₄ m₄ h4
    subst m₄
    by_cases hf4 : r₄.headD 0 = 0
    · rw [if_pos hf4] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨hr0, hr1, hm⟩ := hW
      rw [← hm]
      have hnone : rawDec m₃ r₄ = none := by unfold rawDec; rw [if_pos hf4]
      rw [hnone] at hrun4
      have hz := redWf_run_none1 (coreKnot (decMode mode) fe id F) fe d.toNat (decI c) (decE a) (decE b)
        a₀ a₁ a₂ a₂ _ hwf (decBool r₂) hsup (hbool hgo) (decE (r₃.headD 0)) (by rw [hrun3]; rfl) hrun4
      obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
      refine ⟨hok', ?_, ?_, ?_⟩
      · rw [hst']; exact ⟨M₃, hS₃, hK₃, (StackKept.of_const_frame hfr2).trans hSt₃⟩
      · rw [hres']; simp only [decOptR, decOpt, ← hr0]; rfl
      · unfold ResW HW; rw [← hr0, ← hr1]; exact ⟨by decide, by decide⟩
    rw [if_neg hf4] at hW
    obtain ⟨hsl4, hnorm4⟩ := hslice4 hf4
    have hsome4 : rawDec m₃ r₄ = some (pv (m₃.arr64 POOL) (r₄.tail.headD 0).toNat
        (r₄.tail.tail.headD 0).toNat) := by unfold rawDec; rw [if_neg hf4]
    rw [hsome4] at hrun4
    cases h5 : callW p n "whnf" [mode, vis, d, b] m₃ with
    | none => rw [h5] at hW; cases hW
    | some q₅ =>
    obtain ⟨r₅, m₅⟩ := q₅
    rw [h5] at hW
    dsimp only at hW
    have hSP3 : SlotPre ⟨m₃, Locals.init []⟩ a₂ dn vis fe M₃ eb mode := ⟨hS₃, hS.mode4, hS.eb_mode⟩
    obtain ⟨hok5, ⟨M₅, hS₅, hK₅, hSt₅⟩, hres5, hrw5⟩ := CoreSpec.of_callW
      (hkn.whnf F ⟨m₃, Locals.init []⟩ a₂ dn vis fe M₃ eb mode d b (by omega) (by omega) hSP3 hb) h5
    have hrun5 := AM.run_of_ok _ _ hok5
    rw [hres5] at hrun5
    generalize AM.st ((coreKnot (decMode mode) fe id F).whnf d.toNat (decE b)) a₂ = a₃ at hrun5 hS₅
    cases h6 : callW p n "raw_nat_lit" [r₅.headD 0] m₅ with
    | none => rw [h6] at hW; cases hW
    | some q₆ =>
    obtain ⟨r₆, m₆⟩ := q₆
    rw [h6] at hW
    dsimp only at hW
    obtain ⟨hm6, hrun6, hres6, hslice6⟩ := callW_rawNatLit p hp n ⟨m₅, Locals.init []⟩ a₃ dn vis fe M₅ eb _
      hS₅ hrw5 r₆ m₆ h6
    subst m₆
    by_cases hf6 : r₆.headD 0 = 0
    · rw [if_pos hf6] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨hr0, hr1, hm⟩ := hW
      rw [← hm]
      have hnone : rawDec m₅ r₆ = none := by unfold rawDec; rw [if_pos hf6]
      rw [hnone] at hrun6
      have hz := redWf_run_none2 (coreKnot (decMode mode) fe id F) fe d.toNat (decI c) (decE a) (decE b)
        a₀ a₁ a₂ a₂ a₃ a₃ _ hwf (decBool r₂) hsup (hbool hgo) (decE (r₃.headD 0)) (decE (r₅.headD 0)) _
        (by rw [hrun3]; rfl) hrun4 (by rw [hrun5]; rfl) hrun6
      obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
      refine ⟨hok', ?_, ?_, ?_⟩
      · rw [hst']; exact ⟨M₅, hS₅, hK₃.trans hK₅, ((StackKept.of_const_frame hfr2).trans hSt₃).trans hSt₅⟩
      · rw [hres']; simp only [decOptR, decOpt, ← hr0]; rfl
      · unfold ResW HW; rw [← hr0, ← hr1]; exact ⟨by decide, by decide⟩
    · rw [if_neg hf6] at hW; cases hW
  · rw [if_neg hgo] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    rw [← hm]
    have hskip : (([decI (pinW s₀.mem 22), decI (pinW s₀.mem 23), decI (pinW s₀.mem 24),
        decI (pinW s₀.mem 25), decI (pinW s₀.mem 26), decI (pinW s₀.mem 27), decI (pinW s₀.mem 28),
        decI (pinW s₀.mem 29)] : List NIdx).contains (decI c) && decBool r₂) = false := by
      rw [hcont]
      by_cases h1 : r₁.headD 0 = 0
      · have : natOpWfSel (pinW s₀.mem) c = false := by
          rw [← hwfsel, h1]; rfl
        rw [this]; rfl
      · have h2 : r₂.headD 0 = 0 := Classical.byContradiction fun h2 => hgo ⟨h1, h2⟩
        have : decBool r₂ = false := by simp only [decBool, h2]; rfl
        rw [this]; simp
    have hz := redWf_run_skip (coreKnot (decMode mode) fe id F) fe d.toNat (decI c) (decE a) (decE b)
      a₀ a₁ _ hwf (decBool r₂) hsup hskip
    obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
    refine CRef.core (m' := m₂) ⟨hok', by rw [hst']; exact hS2, ?_, hfr2, ?_⟩
    · rw [hres']; simp only [decOptR, decOpt, ← hr0]; rfl
    · unfold ResW HW; rw [← hr0, ← hr1]; exact ⟨by decide, by decide⟩

end refs20


/-! ## `reduce_nat`: the dispatch -/

/-- The `.const c us` arm of `reduceNat`'s `match ← view f`. -/
def redConstT (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (c : NIdx) (us : LsIdx) (b : EIdx) :
    AM (Option EIdx) := do
  let el ← emptyLevels
  if us != el then pure none else redSuccT r fe depth c b

/-- The `.app g a` arm of `reduceNat`'s `match ← view f`. -/
def redAppT (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (g a b : EIdx) : AM (Option EIdx) := do
  if g.tag == ETag.const then
    match ← view g with
    | .const c us => do
      let el ← emptyLevels
      if us != el then pure none else redBinT r fe depth c a b
    | _ => pure none
  else pure none

/-- `reduceNat` past the application node. -/
def redHeadT (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (f b : EIdx) : AM (Option EIdx) := do
  match ← view f with
  | .const c us => redConstT r fe depth c us b
  | .app g a => redAppT r fe depth g a b
  | _ => pure none

theorem reduceNat_head_eq (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (e f b : EIdx) (a : AState)
    (h : (e.tag == ETag.app) = true) (hv : a.store.view e = some (.app f b)) :
    (reduceNat r fe depth e).run a = (redHeadT r fe depth f b).run a := by
  simp only [reduceNat, h, ↓reduceIte, StateT.run_bind, view_run _ _ _ hv, except_ok_bind, redHeadT,
    redConstT, redSuccT, redAppT, redBinT, redOpT, redWfT]
  rfl

theorem redHead_other (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (f b : EIdx) (a : AState)
    (v : ENodeView) (hvf : a.store.view f = some v) (hc : ∀ c us, v ≠ .const c us)
    (hp : ∀ g x, v ≠ .app g x) : (redHeadT r fe depth f b).run a = .ok (none, a) := by
  simp only [redHeadT, StateT.run_bind, view_run _ _ _ hvf, except_ok_bind]
  cases v with
  | const c us => exact absurd rfl (hc c us)
  | app g x => exact absurd rfl (hp g x)
  | _ => rfl

theorem redHead_const (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (f b : EIdx) (a : AState)
    (c : NIdx) (us : LsIdx) (hvf : a.store.view f = some (.const c us)) :
    (redHeadT r fe depth f b).run a = (redConstT r fe depth c us b).run a := by
  simp only [redHeadT, StateT.run_bind, view_run _ _ _ hvf, except_ok_bind]

theorem redHead_app (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (f b g x : EIdx) (a : AState)
    (hvf : a.store.view f = some (.app g x)) :
    (redHeadT r fe depth f b).run a = (redAppT r fe depth g x b).run a := by
  simp only [redHeadT, StateT.run_bind, view_run _ _ _ hvf, except_ok_bind]

theorem redConst_ne (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (c : NIdx) (us el : LsIdx) (b : EIdx)
    (a : AState) (hel : emptyLevels.run a = .ok (el, a)) (hne : (us != el) = true) :
    (redConstT r fe depth c us b).run a = .ok (none, a) := by
  simp only [redConstT, StateT.run_bind, hel, except_ok_bind, hne]; rfl

theorem redConst_eq (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (c : NIdx) (us el : LsIdx) (b : EIdx)
    (a : AState) (hel : emptyLevels.run a = .ok (el, a)) (heq : (us != el) = false) :
    (redConstT r fe depth c us b).run a = (redSuccT r fe depth c b).run a := by
  simp only [redConstT, StateT.run_bind, hel, except_ok_bind, heq]; rfl

theorem redApp_notconst (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (g x b : EIdx) (a : AState)
    (hg : (g.tag == ETag.const) = false) : (redAppT r fe depth g x b).run a = .ok (none, a) := by
  simp only [redAppT, hg]; rfl

theorem redApp_ne (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (g x b : EIdx) (a : AState)
    (c : NIdx) (us el : LsIdx) (hg : (g.tag == ETag.const) = true)
    (hv : a.store.view g = some (.const c us)) (hel : emptyLevels.run a = .ok (el, a))
    (hne : (us != el) = true) : (redAppT r fe depth g x b).run a = .ok (none, a) := by
  simp only [redAppT, hg, ↓reduceIte, StateT.run_bind, view_run _ _ _ hv, except_ok_bind, hel, hne]; rfl

theorem redApp_eq (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (g x b : EIdx) (a : AState)
    (c : NIdx) (us el : LsIdx) (hg : (g.tag == ETag.const) = true)
    (hv : a.store.view g = some (.const c us)) (hel : emptyLevels.run a = .ok (el, a))
    (heq : (us != el) = false) :
    (redAppT r fe depth g x b).run a = (redBinT r fe depth c x b).run a := by
  simp only [redAppT, hg, ↓reduceIte, StateT.run_bind, view_run _ _ _ hv, except_ok_bind, hel, heq]; rfl


theorem CoreRef.congr {α : Type} [Inhabited α] {T T' : AM α} {a₀ : AState} {dec : List Word → α}
    {dn : NIdx → Option ConLeche.Name} {m₀ m : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {r : List Word} {ok : List Word → Prop} (h : T.run a₀ = T'.run a₀)
    (hr : CoreRef T a₀ dec dn m₀ vis fe M eb r m ok) : CoreRef T' a₀ dec dn m₀ vis fe M eb r m ok := by
  obtain ⟨c1, c2, c3⟩ := AM.congr_run h
  obtain ⟨hok, hA, hres, hok'⟩ := hr
  exact ⟨c1 ▸ hok, c2 ▸ hA, c3 ▸ hres, hok'⟩

section refs21
variable (p : Prog)

theorem callW_reduceNatK (hp : WhnfDeltaProg' p) (N F : Nat) (hF : N ≤ F) (hn2 : N ≤ 2 ^ 62)
    (hk : KnotUpTo p N) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (MM : ModeMaps) (eb mode d f b : Word) (hS : SlotPre s₀ a₀ dn vis fe MM eb mode)
    (hf : HW f) (hb : HW b) (hg3 : f >>> 28 = 3) (hsc : ¬(tierW f ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0))
    (nn : NIdx) (uu : LsIdx) (hvf : a₀.store.view (decE f) = some (.const nn uu)) (r : List Word)
    (m' : Mem) (h : callW p N "reduce_nat_k" [mode, vis, d, f, b] s₀.mem = some (r, m')) :
    CoreRef (redConstT (coreKnot (decMode mode) fe id F) fe d.toNat nn uu (decE b)) a₀ decOptR dn
      s₀.mem vis fe MM eb r m' ResW := by
  have hC := hS.rel
  cases N with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (reduceNatK_spec p hp.toWhnfDeltaProg n s₀ mode vis d f b) h
  unfold reduceNatKW at hW
  by_cases hbd : rdW (s₀.mem.arr64 CTL) (18 + tierW f) ≤ idxW f
  · rw [if_pos hbd] at hW; cases hW
  rw [if_neg hbd] at hW
  obtain ⟨n_, us_, hview, hn, hu, hnl, hul⟩ :=
    view_const_words s₀.mem a₀ hC.arena.1 f hf ⟨hsc, by simpa using hbd⟩ hg3
  rw [hview] at hvf
  have hvf' := Option.some.inj hvf
  injection hvf' with hn' hu'
  subst hn' hu'
  subst hn hu
  cases h1 : callW p n "pin_word" [52] s₀.mem with
  | none => rw [h1] at hW; cases hW
  | some q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  rw [h1] at hW
  obtain ⟨hm1, -, hr₁⟩ := callW_pinWord p hp.pinWord n s₀.mem 52 r₁ m₁ h1
  subst m₁
  simp only [show (52 : Word).toNat = 52 from rfl] at hr₁
  dsimp only at hW
  have hel : emptyLevels.run a₀ = .ok (decI (pinW s₀.mem 52), a₀) := pinEmptyLevels_run hC.pins
  have hbne : ∀ v w : Word, HW v → HW w → ((decI v : LsIdx) != decI w) = !decide (v = w) := by
    intro v w hv hw; simp only [bne, decI_beq v w hv hw]
  by_cases hne : rdW (s₀.mem.arr64 CREC) (idxW f * 4 + tierW f * 2 + 1) ≠ r₁.headD 0
  · rw [if_pos hne] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    rw [← hm]
    have hz := redConst_ne (coreKnot (decMode mode) fe id F) fe d.toNat (decI (rdW (s₀.mem.arr64 CREC)
      (idxW f * 4 + tierW f * 2))) (decI (rdW (s₀.mem.arr64 CREC) (idxW f * 4 + tierW f * 2 + 1)))
      (decI (pinW s₀.mem 52)) (decE b) a₀ hel (by
        rw [hbne _ _ hul hC.pins.lv_lt.1]
        have : rdW (s₀.mem.arr64 CREC) (idxW f * 4 + tierW f * 2 + 1) ≠ pinW s₀.mem 52 := by
          rw [← hr₁]; exact hne
        simp [this])
    refine (CRef.pure hC _ hz ?_ ?_).core
    · simp only [decOptR, decOpt, ← hr0]; rfl
    · unfold ResW HW; rw [← hr0, ← hr1]; exact ⟨by decide, by decide⟩
  rw [if_neg hne] at hW
  have hne' : rdW (s₀.mem.arr64 CREC) (idxW f * 4 + tierW f * 2 + 1) = pinW s₀.mem 52 := by
    rw [← hr₁]; simpa using hne
  cases h2 : callW p n "reduce_nat_succ" [mode, vis, d, rdW (s₀.mem.arr64 CREC) (idxW f * 4 + tierW f * 2),
      b] s₀.mem with
  | none => rw [h2] at hW; cases hW
  | some q₂ =>
  obtain ⟨r₂, m₂⟩ := q₂
  rw [h2] at hW
  dsimp only at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr0, hr1, hm⟩ := hW
  rw [← hm]
  have hsucc := callW_reduceNatSucc p hp n F (by omega) (by omega) (hk.mono (by omega)) s₀ a₀ dn vis fe MM
    eb mode d _ b hS hnl hb r₂ m₂ h2
  have hcongr := redConst_eq (coreKnot (decMode mode) fe id F) fe d.toNat (decI (rdW (s₀.mem.arr64 CREC)
      (idxW f * 4 + tierW f * 2))) (decI (rdW (s₀.mem.arr64 CREC) (idxW f * 4 + tierW f * 2 + 1)))
      (decI (pinW s₀.mem 52)) (decE b) a₀ hel (by
        rw [hbne _ _ hul hC.pins.lv_lt.1]; simp [hne'])
  have hsucc' := CoreRef.congr hcongr.symm hsucc
  obtain ⟨hok, hA, hres, hrw⟩ := hsucc'
  refine ⟨hok, hA, ?_, ?_⟩
  · rw [hres]; simp only [decOptR, ← hr0, ← hr1]
  · unfold ResW at hrw ⊢; rw [← hr0, ← hr1]; exact hrw

end refs21


theorem natOpStored_run_pure (fe : IFEnv) (c : NIdx) (a : AState) :
    ∃ b, (natOpStored fe c).run a = .ok (b, a) := by
  unfold natOpStored
  cases fe.find? c with
  | none => exact ⟨false, rfl⟩
  | some ci => cases ci <;> exact ⟨_, rfl⟩

theorem bne_and_bne (x y : Word) : ((x != 0) && (y != 0)) = decide (x ≠ 0 ∧ y ≠ 0) := by
  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [hx, hy]

section refs22
variable (p : Prog)

theorem callW_reduceNatAp (hp : WhnfDeltaProg' p) (hno : NatOpResultOK p) (N F : Nat) (hF : N ≤ F)
    (hn2 : N ≤ 2 ^ 62) (hk : KnotUpTo p N) (hgr : WhnfGrowsUpTo p N) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb mode d f b : Word) (hS : SlotPre s₀ a₀ dn vis fe MM eb mode) (hf : HW f) (hb : HW b)
    (hg4 : f >>> 28 = 4) (hsc : ¬(tierW f ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0))
    (g x : EIdx) (hvf : a₀.store.view (decE f) = some (.app g x)) (r : List Word) (m' : Mem)
    (h : callW p N "reduce_nat_ap" [mode, vis, d, f, b] s₀.mem = some (r, m')) :
    CoreRef (redAppT (coreKnot (decMode mode) fe id F) fe d.toNat g x (decE b)) a₀ decOptR dn
      s₀.mem vis fe MM eb r m' ResW := by
  have hC := hS.rel
  cases N with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (reduceNatAp_spec p hp.toWhnfDeltaProg n s₀ mode vis d f b) h
  unfold reduceNatApW at hW
  by_cases hbd : rdW (s₀.mem.arr64 CTL) (4 + tierW f) ≤ idxW f
  · rw [if_pos hbd] at hW; cases hW
  rw [if_neg hbd] at hW
  obtain ⟨hviewf, hgw, hxw⟩ := view_app s₀.mem a₀ hC.arena.1 f hf ⟨hsc, by simpa using hbd⟩ hg4
  rw [hviewf] at hvf
  have hvf' := Option.some.inj hvf
  injection hvf' with hg' hx'
  subst hg' hx'
  generalize rdW (s₀.mem.arr64 AREC) (idxW f * 4 + tierW f * 2) = gw at hW hgw hviewf
  generalize rdW (s₀.mem.arr64 AREC) (idxW f * 4 + tierW f * 2 + 1) = xw at hW hxw hviewf
  by_cases g3 : gw >>> 28 ≠ 3
  · rw [if_pos g3] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    rw [← hm]
    have ht : ((decE (gw)).tag == ETag.const) = false := by
      rw [decE_const_tag _ hgw]; exact beq_eq_false_iff_ne.mpr g3
    refine (CRef.pure hC _ (redApp_notconst _ fe d.toNat (decE gw) (decE xw) (decE b) a₀ ht) ?_ ?_).core
    · simp only [decOptR, decOpt, ← hr0]; rfl
    · unfold ResW HW; rw [← hr0, ← hr1]; exact ⟨by decide, by decide⟩
  rw [if_neg g3] at hW
  have g3' : gw >>> 28 = 3 := by simpa using g3
  have ht : ((decE (gw)).tag == ETag.const) = true := by
    rw [decE_const_tag _ hgw]; exact beq_iff_eq.mpr g3'
  by_cases hs2 : tierW (gw) ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0
  · rw [if_pos hs2] at hW; cases hW
  rw [if_neg hs2] at hW
  by_cases hb2 : rdW (s₀.mem.arr64 CTL) (18 + tierW (gw)) ≤
      idxW (gw)
  · rw [if_pos hb2] at hW; cases hW
  rw [if_neg hb2] at hW
  obtain ⟨n_, us_, hview, hn, hu, hnl, hul⟩ := view_const_words s₀.mem a₀ hC.arena.1 _ hgw
    ⟨hs2, by simpa using hb2⟩ g3'
  subst hn hu
  generalize rdW (s₀.mem.arr64 CREC) (idxW gw * 4 + tierW gw * 2) = cw at *
  generalize rdW (s₀.mem.arr64 CREC) (idxW gw * 4 + tierW gw * 2 + 1) = uw at *
  cases h1 : callW p n "pin_word" [52] s₀.mem with
  | none => rw [h1] at hW; cases hW
  | some q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  rw [h1] at hW
  obtain ⟨hm1, hflag, hr₁⟩ := callW_pinWord p hp.pinWord n s₀.mem 52 r₁ m₁ h1
  subst m₁
  simp only [show (52 : Word).toNat = 52 from rfl] at hr₁
  dsimp only at hW
  have hel : emptyLevels.run a₀ = .ok (decI (pinW s₀.mem 52), a₀) := pinEmptyLevels_run hC.pins
  have hbne : ∀ v w : Word, HW v → HW w → ((decI v : LsIdx) != decI w) = !decide (v = w) := by
    intro v w hv hw; simp only [bne, decI_beq v w hv hw]
  have hcond := fun (hh : uw = pinW s₀.mem 52) =>
    (by rw [hbne _ _ hul hC.pins.lv_lt.1]; simp [hh] : ((decI uw : LsIdx) != decI (pinW s₀.mem 52)) = false)
  by_cases hne : uw ≠ r₁.headD 0
  · rw [if_pos hne] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    rw [← hm]
    have hz := redApp_ne (coreKnot (decMode mode) fe id F) fe d.toNat (decE gw) (decE xw) (decE b) a₀
      (decI cw) (decI uw) (decI (pinW s₀.mem 52)) ht hview hel (by
        rw [hbne _ _ hul hC.pins.lv_lt.1]
        have : uw ≠ pinW s₀.mem 52 := by rw [← hr₁]; exact hne
        simp [this])
    refine (CRef.pure hC _ hz ?_ ?_).core
    · simp only [decOptR, decOpt, ← hr0]; rfl
    · unfold ResW HW; rw [← hr0, ← hr1]; exact ⟨by decide, by decide⟩
  rw [if_neg hne] at hW
  have hne' : uw = pinW s₀.mem 52 := by rw [← hr₁]; simpa using hne
  have hcongrApp := redApp_eq (coreKnot (decMode mode) fe id F) fe d.toNat (decE gw) (decE xw) (decE b) a₀
    (decI cw) (decI uw) (decI (pinW s₀.mem 52)) ht hview hel (hcond hne')
  -- `nat_bin_op_name`
  cases h2 : callW p n "nat_bin_op_name" [cw] s₀.mem with
  | none => rw [h2] at hW; cases hW
  | some q₂ =>
  obtain ⟨r₂, m₂⟩ := q₂
  rw [h2] at hW
  obtain ⟨t₂, ht₂, hm₂, -, hsel2, -⟩ := triple_of_callW
    (natBinOpNameL_spec p hp.natBinOpName n ⟨s₀.mem, Locals.init []⟩ hflag cw) h2
  have hm2 : m₂ = s₀.mem := by rw [← ht₂, hm₂]
  subst hm2
  dsimp only at hW
  cases h3 : callW p n "nat_op_stored" [vis, cw] s₀.mem with
  | none => rw [h3] at hW; cases hW
  | some q₃ =>
  obtain ⟨r₃, m₃⟩ := q₃
  rw [h3] at hW
  dsimp only at hW
  obtain ⟨hok3, hS3, hres3, hfr3, hrh3⟩ := callW_natOpStored p hp n ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe MM eb cw
    hC hnl r₃ m₃ h3
  obtain ⟨b3, hb3⟩ := natOpStored_run_pure fe (decI cw) a₀
  have hst3 : AM.st (natOpStored fe (decI cw)) a₀ = a₀ := (AM.of_run_ok _ _ _ _ hb3).2.1
  have hbb3 : b3 = decBool r₃ := by
    have := (AM.of_run_ok _ _ _ _ hb3).2.2
    rw [hres3] at this; exact this.symm
  rw [hst3] at hS3
  have hbin : (natBinOpName (decI cw)).run a₀ = .ok (natBinOpSel (pinW s₀.mem ) cw, a₀) :=
    natBinOpName_run hC.pins cw hnl
  have hSP3 : SlotPre ⟨m₃, Locals.init []⟩ a₀ dn vis fe MM eb mode := ⟨hS3, hS.mode4, hS.eb_mode⟩
  have hbool : (natBinOpSel (pinW s₀.mem) cw && decBool r₃) = decide (r₂.headD 0 ≠ 0 ∧ r₃.headD 0 ≠ 0) := by
    rw [← hsel2]; exact bne_and_bne _ _
  have hredbin := redBin_run (coreKnot (decMode mode) fe id F) fe d.toNat (decI cw) (decE xw) (decE b) a₀
    (natBinOpSel (pinW s₀.mem) cw) (decBool r₃) hbin (by rw [hb3, hbb3])
  by_cases hgo : r₂.headD 0 ≠ 0 ∧ r₃.headD 0 ≠ 0
  · rw [if_pos hgo] at hW
    cases h4 : callW p n "reduce_nat_op" [mode, vis, d, cw, xw, b] m₃ with
    | none => rw [h4] at hW; cases hW
    | some q₄ =>
    obtain ⟨r₄, m₄⟩ := q₄
    rw [h4] at hW
    dsimp only at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    rw [← hm]
    have hop := callW_reduceNatOp p hp hno n F (by omega) (by omega) (hk.mono (by omega))
      (fun k hk' => hgr k (by omega)) ⟨m₃, Locals.init []⟩ a₀ dn vis fe MM eb mode d cw xw b hSP3 hnl hxw hb r₄ m₄ h4
    have hcg : (redAppT (coreKnot (decMode mode) fe id F) fe d.toNat (decE gw) (decE xw) (decE b)).run a₀ =
        (redOpT (coreKnot (decMode mode) fe id F) d.toNat (decI cw) (decE xw) (decE b)).run a₀ := by
      rw [hcongrApp, hredbin, hbool, decide_eq_true hgo]; rfl
    have hop' := CoreRef.congr hcg.symm hop
    obtain ⟨hok, hA, hres, hrw⟩ := hop'
    refine ⟨hok, CoreAfter.comp (KeptAll.refl _ _) (StackKept.of_const_frame hfr3) hA, ?_, ?_⟩
    · rw [hres]; simp only [decOptR, ← hr0, ← hr1]
    · unfold ResW at hrw ⊢; rw [← hr0, ← hr1]; exact hrw
  · rw [if_neg hgo] at hW
    cases h4 : callW p n "reduce_nat_wf" [mode, vis, d, cw, xw, b] m₃ with
    | none => rw [h4] at hW; cases hW
    | some q₄ =>
    obtain ⟨r₄, m₄⟩ := q₄
    rw [h4] at hW
    dsimp only at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    rw [← hm]
    have hwf := callW_reduceNatWf p hp n F (by omega) (by omega) (hk.mono (by omega))
      ⟨m₃, Locals.init []⟩ a₀ dn vis fe MM eb mode d cw xw b hSP3 hnl hxw hb r₄ m₄ h4
    have hcg : (redAppT (coreKnot (decMode mode) fe id F) fe d.toNat (decE gw) (decE xw) (decE b)).run a₀ =
        (redWfT (coreKnot (decMode mode) fe id F) fe d.toNat (decI cw) (decE xw) (decE b)).run a₀ := by
      rw [hcongrApp, hredbin, hbool, decide_eq_false hgo]; rfl
    have hwf' := CoreRef.congr hcg.symm hwf
    obtain ⟨hok, hA, hres, hrw⟩ := hwf'
    refine ⟨hok, CoreAfter.comp (KeptAll.refl _ _) (StackKept.of_const_frame hfr3) hA, ?_, ?_⟩
    · rw [hres]; simp only [decOptR, ← hr0, ← hr1]
    · unfold ResW at hrw ⊢; rw [← hr0, ← hr1]; exact hrw

end refs22


theorem view_nca (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hh : h.toNat < 2 ^ 32)
    (c : Word) (hv : viewOK m h c)
    (hcg : (h >>> 28 = 0 ∧ c = 22) ∨ (h >>> 28 = 1 ∧ c = 26) ∨ (h >>> 28 = 2 ∧ c = 16) ∨
      (h >>> 28 = 5 ∧ c = 28) ∨ (h >>> 28 = 6 ∧ c = 30) ∨ (h >>> 28 = 7 ∧ c = 20) ∨
      (h >>> 28 = 8 ∧ c = 2) ∨ (h >>> 28 = 9 ∧ c = 32)) :
    ∃ v, a.store.view (decE h) = some v ∧ (∀ c us, v ≠ .const c us) ∧ (∀ g x, v ≠ .app g x) := by
  rcases hcg with ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩
  · exact ⟨_, view_bvar m a hR h hh hv g, fun c us => nofun, fun c us => nofun⟩
  · obtain ⟨i, ty, hw⟩ := view_fvar m a hR h hh hv g
    exact ⟨_, hw, fun c us => nofun, fun c us => nofun⟩
  · obtain ⟨u, hw⟩ := view_sort m a hR h hh hv g
    exact ⟨_, hw, fun c us => nofun, fun c us => nofun⟩
  · exact ⟨_, (view_lam m a hR h hh hv g).1, fun c us => nofun, fun c us => nofun⟩
  · exact ⟨_, (view_forall m a hR h hh hv g).1, fun c us => nofun, fun c us => nofun⟩
  · exact ⟨_, (view_let m a hR h hh hv g).1, fun c us => nofun, fun c us => nofun⟩
  · obtain ⟨l, hw⟩ := view_lit m a hR h hh hv g
    exact ⟨_, hw, fun c us => nofun, fun c us => nofun⟩
  · exact ⟨_, (view_proj m a hR h hh hv g).1, fun c us => nofun, fun c us => nofun⟩

section refs23
variable (p : Prog)

theorem callW_reduceNatHead (hp : WhnfDeltaProg' p) (hno : NatOpResultOK p) (N F : Nat) (hF : N ≤ F)
    (hn2 : N ≤ 2 ^ 62) (hk : KnotUpTo p N) (hgr : WhnfGrowsUpTo p N) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb mode d f b : Word) (hS : SlotPre s₀ a₀ dn vis fe MM eb mode) (hf : HW f) (hb : HW b)
    (r : List Word) (m' : Mem)
    (h : callW p N "reduce_nat_head" [mode, vis, d, f, b] s₀.mem = some (r, m')) :
    CoreRef (redHeadT (coreKnot (decMode mode) fe id F) fe d.toNat (decE f) (decE b)) a₀ decOptR dn
      s₀.mem vis fe MM eb r m' ResW := by
  have hC := hS.rel
  cases N with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (reduceNatHead_spec p hp.toWhnfDeltaProg n s₀ mode vis d f b) h
  unfold reduceNatHeadW at hW
  by_cases hsc : tierW f ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0
  · rw [if_pos hsc] at hW; cases hW
  rw [if_neg hsc] at hW
  -- the tags that only check a bound
  have simple : ∀ (c : Word), (f >>> 28 = 0 ∧ c = 22) ∨ (f >>> 28 = 1 ∧ c = 26) ∨ (f >>> 28 = 2 ∧ c = 16) ∨
      (f >>> 28 = 5 ∧ c = 28) ∨ (f >>> 28 = 6 ∧ c = 30) ∨ (f >>> 28 = 7 ∧ c = 20) ∨
      (f >>> 28 = 8 ∧ c = 2) ∨ (f >>> 28 = 9 ∧ c = 32) →
      (if rdW (s₀.mem.arr64 CTL) (c + tierW f) ≤ idxW f then none else
        some ((0 : Word), (0 : Word), s₀.mem)) = some (r.headD 0, r.tail.headD 0, s'.mem) →
      CoreRef (redHeadT (coreKnot (decMode mode) fe id F) fe d.toNat (decE f) (decE b)) a₀ decOptR dn
        s₀.mem vis fe MM eb r s'.mem ResW := by
    intro c hcg hW'
    by_cases hbd : rdW (s₀.mem.arr64 CTL) (c + tierW f) ≤ idxW f
    · rw [if_pos hbd] at hW'; cases hW'
    rw [if_neg hbd] at hW'
    simp only [Option.some.injEq, Prod.mk.injEq] at hW'
    obtain ⟨hr0, hr1, hm⟩ := hW'
    rw [← hm]
    obtain ⟨v, hv, hc, hp'⟩ := view_nca s₀.mem a₀ hC.arena.1 f hf c ⟨hsc, by simpa using hbd⟩ hcg
    refine (CRef.pure hC _ (redHead_other _ fe d.toNat _ (decE b) a₀ v hv hc hp') ?_ ?_).core
    · simp only [decOptR, decOpt, ← hr0]; rfl
    · unfold ResW HW; rw [← hr0, ← hr1]; exact ⟨by decide, by decide⟩
  by_cases g3 : f >>> 28 = 3
  · rw [if_pos g3] at hW
    cases h1 : callW p n "reduce_nat_k" [mode, vis, d, f, b] s₀.mem with
    | none => rw [h1] at hW; cases hW
    | some q₁ =>
    obtain ⟨r₁, m₁⟩ := q₁
    rw [h1] at hW
    dsimp only at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    rw [← hm]
    by_cases hbd : rdW (s₀.mem.arr64 CTL) (18 + tierW f) ≤ idxW f
    · cases n with
      | zero => rw [callW_zero] at h1; cases h1
      | succ n' =>
      obtain ⟨s'', hs'', -, hW2⟩ := triple_of_callW (reduceNatK_spec p hp.toWhnfDeltaProg n' s₀ mode vis d f b) h1
      unfold reduceNatKW at hW2
      rw [if_pos hbd] at hW2; cases hW2
    obtain ⟨n_, us_, hview, -, -, -, -⟩ := view_const_words s₀.mem a₀ hC.arena.1 f hf
      ⟨hsc, by simpa using hbd⟩ g3
    have hK := callW_reduceNatK p hp n F (by omega) (by omega) (hk.mono (by omega)) s₀ a₀ dn vis fe MM eb
      mode d f b hS hf hb g3 hsc n_ us_ hview r₁ m₁ h1
    have hcg := redHead_const (coreKnot (decMode mode) fe id F) fe d.toNat (decE f) (decE b) a₀ n_ us_ hview
    have hK' := CoreRef.congr hcg.symm hK
    obtain ⟨hok, hA, hres, hrw⟩ := hK'
    refine ⟨hok, hA, ?_, ?_⟩
    · rw [hres]; simp only [decOptR, ← hr0, ← hr1]
    · unfold ResW at hrw ⊢; rw [← hr0, ← hr1]; exact hrw
  rw [if_neg g3] at hW
  by_cases g4 : f >>> 28 = 4
  · rw [if_pos g4] at hW
    cases h1 : callW p n "reduce_nat_ap" [mode, vis, d, f, b] s₀.mem with
    | none => rw [h1] at hW; cases hW
    | some q₁ =>
    obtain ⟨r₁, m₁⟩ := q₁
    rw [h1] at hW
    dsimp only at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    rw [← hm]
    by_cases hbd : rdW (s₀.mem.arr64 CTL) (4 + tierW f) ≤ idxW f
    · cases n with
      | zero => rw [callW_zero] at h1; cases h1
      | succ n' =>
      obtain ⟨s'', hs'', -, hW2⟩ := triple_of_callW (reduceNatAp_spec p hp.toWhnfDeltaProg n' s₀ mode vis d f b) h1
      unfold reduceNatApW at hW2
      rw [if_pos hbd] at hW2; cases hW2
    obtain ⟨hview, -, -⟩ := view_app s₀.mem a₀ hC.arena.1 f hf ⟨hsc, by simpa using hbd⟩ g4
    have hA := callW_reduceNatAp p hp hno n F (by omega) (by omega) (hk.mono (by omega))
      (fun k hk' => hgr k (by omega)) s₀ a₀ dn vis fe MM eb mode d f b hS hf hb g4 hsc _ _ hview r₁ m₁ h1
    have hcg := redHead_app (coreKnot (decMode mode) fe id F) fe d.toNat (decE f) (decE b) _ _ a₀ hview
    have hA' := CoreRef.congr hcg.symm hA
    obtain ⟨hok, hA2, hres, hrw⟩ := hA'
    refine ⟨hok, hA2, ?_, ?_⟩
    · rw [hres]; simp only [decOptR, ← hr0, ← hr1]
    · unfold ResW at hrw ⊢; rw [← hr0, ← hr1]; exact hrw
  rw [if_neg g4] at hW
  by_cases g0 : f >>> 28 = 0
  · rw [if_pos g0] at hW; exact simple 22 (Or.inl ⟨g0, rfl⟩) hW
  rw [if_neg g0] at hW
  by_cases g1 : f >>> 28 = 1
  · rw [if_pos g1] at hW; exact simple 26 (Or.inr (Or.inl ⟨g1, rfl⟩)) hW
  rw [if_neg g1] at hW
  by_cases g2 : f >>> 28 = 2
  · rw [if_pos g2] at hW; exact simple 16 (Or.inr (Or.inr (Or.inl ⟨g2, rfl⟩))) hW
  rw [if_neg g2] at hW
  by_cases g5 : f >>> 28 = 5
  · rw [if_pos g5] at hW; exact simple 28 (Or.inr (Or.inr (Or.inr (Or.inl ⟨g5, rfl⟩)))) hW
  rw [if_neg g5] at hW
  by_cases g6 : f >>> 28 = 6
  · rw [if_pos g6] at hW; exact simple 30 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨g6, rfl⟩))))) hW
  rw [if_neg g6] at hW
  by_cases g7 : f >>> 28 = 7
  · rw [if_pos g7] at hW
    exact simple 20 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨g7, rfl⟩)))))) hW
  rw [if_neg g7] at hW
  by_cases g8 : f >>> 28 = 8
  · rw [if_pos g8] at hW
    exact simple 2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨g8, rfl⟩))))))) hW
  rw [if_neg g8] at hW
  by_cases g9 : f >>> 28 ≠ 9
  · rw [if_pos g9] at hW; cases hW
  rw [if_neg g9] at hW
  have g9' : f >>> 28 = 9 := by simpa using g9
  exact simple 32 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨g9', rfl⟩)))))))
    (by simpa using hW)

end refs23


/-- `ReduceNatSpec` with the L fuel bounded by the `2^62` that the knot's `whnf` slot needs. -/
def ReduceNatSpec' (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d e : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe MM eb mode →
    HW e → KnotUpTo p n →
    CoreSpec p n "reduce_nat" [mode, vis, d, e]
      (reduceNat (coreKnot (decMode mode) fe id F) fe d.toNat (decE e)) decOptR s₀ a₀ dn vis fe MM eb
      ResW

section refs24
variable (p : Prog)

theorem callW_reduceNat (hp : WhnfDeltaProg' p) (hno : NatOpResultOK p) (N F : Nat) (hF : N ≤ F)
    (hn2 : N ≤ 2 ^ 62) (hk : KnotUpTo p N) (hgr : WhnfGrowsUpTo p N) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb mode d e : Word) (hS : SlotPre s₀ a₀ dn vis fe MM eb mode) (he : HW e)
    (r : List Word) (m' : Mem)
    (h : callW p N "reduce_nat" [mode, vis, d, e] s₀.mem = some (r, m')) :
    CoreRef (reduceNat (coreKnot (decMode mode) fe id F) fe d.toNat (decE e)) a₀ decOptR dn
      s₀.mem vis fe MM eb r m' ResW := by
  have hC := hS.rel
  cases N with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (reduceNat_spec p hp.toWhnfDeltaProg n s₀ mode vis d e) h
  unfold reduceNatW at hW
  have hap : ((decE e).tag == ETag.app) = (e >>> 28 == 4) := by
    by_cases g : e >>> 28 = 4
    · have := (decE_tag_app e he).mpr g
      rw [beq_iff_eq.mpr this, beq_iff_eq.mpr g]
    · have : ¬ (decE e).tag = ETag.app := fun h' => g ((decE_tag_app e he).mp h')
      rw [beq_eq_false_iff_ne.mpr this, beq_eq_false_iff_ne.mpr g]
  by_cases g4 : e >>> 28 ≠ 4
  · rw [if_pos g4] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    rw [← hm]
    refine (CRef.pure hC _ (reduceNat_notapp _ fe d.toNat (decE e) a₀ (by rw [hap]; exact beq_eq_false_iff_ne.mpr g4)) ?_ ?_).core
    · simp only [decOptR, decOpt, ← hr0]; rfl
    · unfold ResW HW; rw [← hr0, ← hr1]; exact ⟨by decide, by decide⟩
  rw [if_neg g4] at hW
  have g4' : e >>> 28 = 4 := by simpa using g4
  by_cases hsc : tierW e ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0
  · rw [if_pos hsc] at hW; cases hW
  rw [if_neg hsc] at hW
  by_cases hbd : rdW (s₀.mem.arr64 CTL) (4 + tierW e) ≤ idxW e
  · rw [if_pos hbd] at hW; cases hW
  rw [if_neg hbd] at hW
  obtain ⟨hview, hfw, hbw⟩ := view_app s₀.mem a₀ hC.arena.1 e he ⟨hsc, by simpa using hbd⟩ g4'
  generalize rdW (s₀.mem.arr64 AREC) (idxW e * 4 + tierW e * 2) = fw at hW hview hfw
  generalize rdW (s₀.mem.arr64 AREC) (idxW e * 4 + tierW e * 2 + 1) = bw at hW hview hbw
  cases h1 : callW p n "reduce_nat_head" [mode, vis, d, fw, bw] s₀.mem with
  | none => rw [h1] at hW; cases hW
  | some q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  rw [h1] at hW
  dsimp only at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr0, hr1, hm⟩ := hW
  rw [← hm]
  have hH := callW_reduceNatHead p hp hno n F (by omega) (by omega) (hk.mono (by omega))
    (fun k hk' => hgr k (by omega)) s₀ a₀ dn vis fe MM eb mode d fw bw hS hfw hbw r₁ m₁ h1
  have hcg := reduceNat_head_eq (coreKnot (decMode mode) fe id F) fe d.toNat (decE e) (decE fw) (decE bw) a₀
    (by rw [hap]; exact beq_iff_eq.mpr g4') hview
  have hH' := CoreRef.congr hcg.symm hH
  obtain ⟨hok, hA, hres, hrw⟩ := hH'
  refine ⟨hok, hA, ?_, ?_⟩
  · rw [hres]; simp only [decOptR, ← hr0, ← hr1]
  · unfold ResW at hrw ⊢; rw [← hr0, ← hr1]; exact hrw

/-- **`reduce_nat` refines `reduceNat`** (the statement of `reduceNat_refines`, with the fuel bound
`n ≤ 2 ^ 62` the knot's `whnf` slot needs, and the program/stub hypotheses explicit). -/
theorem reduceNat_refines' (hp : WhnfDeltaProg' p) (hno : NatOpResultOK p) (n : Nat)
    (hgr : WhnfGrowsUpTo p n) : ReduceNatSpec' p n := by
  intro F s₀ a₀ dn vis fe MM eb mode d e hF hn2 hS he hk
  exact CoreSpec.of_call fun r m' h => callW_reduceNat p hp hno n F hF hn2 hk hgr s₀ a₀ dn vis fe MM eb
    mode d e hS he r m' h

end refs24


/-! ## `whnf_step` -/

/-- The model of `whnf_step`: `(flag, result, memory)`. -/
def whnfStepW (p : Prog) (n : Nat) (m : Mem) (mode vis d e : Word) : Option (Word × Word × Mem) :=
  match callW p n "whnf_core" [mode, 0, vis, d, e] m with
  | none => none
  | some (r₁, m₁) =>
  match callW p n "reduce_nat" [mode, vis, d, r₁.headD 0] m₁ with
  | none => none
  | some (r₂, m₂) =>
  if r₂.headD 0 ≠ 0 then some (1, r₂.tail.headD 0, m₂)
  else
  match callW p n "unfold_definition" [vis, r₁.headD 0] m₂ with
  | none => none
  | some (r₃, m₃) =>
  if r₃.headD 0 ≠ 0 then some (1, r₃.tail.headD 0, m₃) else some (0, r₁.headD 0, m₃)

theorem whnfStep_spec (p : Prog) (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St) (mode vis d e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "whnf_step" [mode, vis, d, e]
    ⦃fun r s' => LocEq s' s₀ ∧
      whnfStepW p n s₀.mem mode vis d e = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.whnfStep]
  simp only [callFn, whnfStepL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "whnf_core", callW_spec p n "reduce_nat", callW_spec p n "unfold_definition"] <;>
  simp_all [whnfStepW, Cmp.eval, BinOp.eval, LocEq, St.setLocs_cons, St.setLoc_loc, St.setLoc_mem,
    St.setLocs_nil, Locals.init_cons_zero, Locals.init_cons_succ, Sig.retVal, Sig.retOr]

theorem whnfStep_run_nat (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (e e₁ e₂ : EIdx) (a a₁ a₂ : AState)
    (hw : (r.whnfCore false depth e).run a = .ok (e₁, a₁))
    (hr : (reduceNat r fe depth e₁).run a₁ = .ok (some e₂, a₂)) :
    (whnfStep r fe depth e).run a = .ok (.cont e₂, a₂) := by
  simp only [whnfStep, StateT.run_bind, hw, except_ok_bind, hr]; rfl

theorem whnfStep_run_unf (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (e e₁ e₂ : EIdx) (a a₁ a₂ a₃ : AState)
    (hw : (r.whnfCore false depth e).run a = .ok (e₁, a₁))
    (hr : (reduceNat r fe depth e₁).run a₁ = .ok (none, a₂))
    (hu : (unfoldDefinition fe e₁).run a₂ = .ok (some e₂, a₃)) :
    (whnfStep r fe depth e).run a = .ok (.cont e₂, a₃) := by
  simp only [whnfStep, StateT.run_bind, hw, except_ok_bind, hr, hu]; rfl

theorem whnfStep_run_done (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (e e₁ : EIdx) (a a₁ a₂ a₃ : AState)
    (hw : (r.whnfCore false depth e).run a = .ok (e₁, a₁))
    (hr : (reduceNat r fe depth e₁).run a₁ = .ok (none, a₂))
    (hu : (unfoldDefinition fe e₁).run a₂ = .ok (none, a₃)) :
    (whnfStep r fe depth e).run a = .ok (.done e₁, a₃) := by
  simp only [whnfStep, StateT.run_bind, hw, except_ok_bind, hr, hu]; rfl

/-- `WhnfStepSpec` with the fuel bound `n ≤ 2 ^ 62` (the knot's slots need it). -/
def WhnfStepSpec' (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d e : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe MM eb mode →
    HW e → KnotUpTo p n →
    CoreSpec p n "whnf_step" [mode, vis, d, e]
      (whnfStep (coreKnot (decMode mode) fe id F) fe d.toNat (decE e)) decStep s₀ a₀ dn vis fe MM eb
      ResW


section refs25
variable (p : Prog)

theorem whnfStep_refines' (hp : WhnfDeltaProg' p) (hwc : WhnfCallees p) (n : Nat)
    (hrn : ∀ k, k ≤ n → ReduceNatSpec' p k) : WhnfStepSpec' p n := by
  intro F s₀ a₀ dn vis fe MM eb mode d e hF hn2 hS he hk
  have hC := hS.rel
  apply CoreSpec.of_call
  intro r m' h
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (whnfStep_spec p hp.toWhnfDeltaProg n s₀ mode vis d e) h
  unfold whnfStepW at hW
  have hkn : KnotOK p n := hk n (by omega)
  cases h1 : callW p n "whnf_core" [mode, 0, vis, d, e] s₀.mem with
  | none => rw [h1] at hW; cases hW
  | some q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  rw [h1] at hW
  dsimp only at hW
  obtain ⟨hok1, ⟨M₁, hS₁, hK₁, hSt₁⟩, hres1, hrw1⟩ := CoreSpec.of_callW
    (hkn.whnfCore F s₀ a₀ dn vis fe MM eb mode 0 d e (by omega) (by omega) hS he) h1
  rw [show ((0 : Word) != 0) = false from rfl] at hok1 hS₁ hres1
  have hrun1 := AM.run_of_ok _ _ hok1
  rw [hres1] at hrun1
  generalize AM.st ((coreKnot (decMode mode) fe id F).whnfCore false d.toNat (decE e)) a₀ = a₁ at hrun1 hS₁
  have hSP1 : SlotPre ⟨m₁, Locals.init []⟩ a₁ dn vis fe M₁ eb mode := ⟨hS₁, hS.mode4, hS.eb_mode⟩
  cases h2 : callW p n "reduce_nat" [mode, vis, d, r₁.headD 0] m₁ with
  | none => rw [h2] at hW; cases hW
  | some q₂ =>
  obtain ⟨r₂, m₂⟩ := q₂
  rw [h2] at hW
  dsimp only at hW
  obtain ⟨hok2, ⟨M₂, hS₂, hK₂, hSt₂⟩, hres2, hrw2⟩ := CoreSpec.of_callW
    (hrn n (by omega) F ⟨m₁, Locals.init []⟩ a₁ dn vis fe M₁ eb mode d (r₁.headD 0) (by omega) (by omega)
      hSP1 hrw1 (hk.mono (by omega))) h2
  have hrun2 := AM.run_of_ok _ _ hok2
  rw [hres2] at hrun2
  generalize AM.st (reduceNat (coreKnot (decMode mode) fe id F) fe d.toNat (decE (r₁.headD 0))) a₁ = a₂ at hrun2 hS₂
  by_cases hf2 : r₂.headD 0 ≠ 0
  · rw [if_pos hf2] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    rw [← hm]
    have hsome : decOptR r₂ = some (decE (r₂.tail.headD 0)) := by simp only [decOptR, decOpt, if_neg hf2]
    rw [hsome] at hrun2
    have hz := whnfStep_run_nat (coreKnot (decMode mode) fe id F) fe d.toNat (decE e) (decE (r₁.headD 0)) _ a₀ a₁ a₂
      (by rw [hrun1]; rfl) hrun2
    obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
    refine ⟨hok', ?_, ?_, ?_⟩
    · rw [hst']; exact ⟨M₂, hS₂, hK₁.trans hK₂, hSt₁.trans hSt₂⟩
    · rw [hres']; simp only [decStep, ← hr0, ← hr1]; simp
    · unfold ResW at hrw2 ⊢; rw [← hr0, ← hr1]; exact ⟨by unfold HW; decide, hrw2.2⟩
  rw [if_neg hf2] at hW
  have hnone : decOptR r₂ = none := by simp only [decOptR, decOpt]; rw [if_pos (by simpa using hf2)]
  rw [hnone] at hrun2
  have hSP2 : SlotPre ⟨m₂, Locals.init []⟩ a₂ dn vis fe M₂ eb mode := ⟨hS₂, hS.mode4, hS.eb_mode⟩
  cases h3 : callW p n "unfold_definition" [vis, r₁.headD 0] m₂ with
  | none => rw [h3] at hW; cases hW
  | some q₃ =>
  obtain ⟨r₃, m₃⟩ := q₃
  rw [h3] at hW
  dsimp only at hW
  obtain ⟨hok3, ⟨M₃, hS₃, hK₃, hSt₃⟩, hres3, hrw3⟩ := CoreSpec.of_callW
    (unfoldDefinition_refines' p hp n ⟨m₂, Locals.init []⟩ a₂ dn vis fe M₂ eb (r₁.headD 0) hS₂ hrw1 hwc) h3
  have hrun3 := AM.run_of_ok _ _ hok3
  rw [hres3] at hrun3
  generalize AM.st (unfoldDefinition fe (decE (r₁.headD 0))) a₂ = a₃ at hrun3 hS₃
  by_cases hf3 : r₃.headD 0 ≠ 0
  · rw [if_pos hf3] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    rw [← hm]
    have hsome : decOptR r₃ = some (decE (r₃.tail.headD 0)) := by simp only [decOptR, decOpt, if_neg hf3]
    rw [hsome] at hrun3
    have hz := whnfStep_run_unf (coreKnot (decMode mode) fe id F) fe d.toNat (decE e) (decE (r₁.headD 0)) _ a₀ a₁ a₂ a₃
      (by rw [hrun1]; rfl) hrun2 hrun3
    obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
    refine ⟨hok', ?_, ?_, ?_⟩
    · rw [hst']; exact ⟨M₃, hS₃, (hK₁.trans hK₂).trans hK₃, (hSt₁.trans hSt₂).trans hSt₃⟩
    · rw [hres']; simp only [decStep, ← hr0, ← hr1]; simp
    · unfold ResW at hrw3 ⊢; rw [← hr0, ← hr1]; exact ⟨by unfold HW; decide, hrw3.2⟩
  rw [if_neg hf3] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr0, hr1, hm⟩ := hW
  rw [← hm]
  have hnone3 : decOptR r₃ = none := by simp only [decOptR, decOpt]; rw [if_pos (by simpa using hf3)]
  rw [hnone3] at hrun3
  have hz := whnfStep_run_done (coreKnot (decMode mode) fe id F) fe d.toNat (decE e) (decE (r₁.headD 0)) a₀ a₁ a₂ a₃
    (by rw [hrun1]; rfl) hrun2 hrun3
  obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
  refine ⟨hok', ?_, ?_, ?_⟩
  · rw [hst']; exact ⟨M₃, hS₃, (hK₁.trans hK₂).trans hK₃, (hSt₁.trans hSt₂).trans hSt₃⟩
  · rw [hres']; simp only [decStep, ← hr0, ← hr1]; simp [decH]
  · unfold ResW; rw [← hr0, ← hr1]; exact ⟨by unfold HW; decide, hrw1⟩

end refs25

end L.Arena
