import ConAgua.Arena.WhnfIotaRefine2
import ConAgua.Arena.Abs1Refine

/-!
# ι-reduction: proofs of `WhnfIota.lean`'s specs, part 3 (`rec_fire_args` … `eta_fab_args`)

Split from `WhnfIotaRefine.lean` (primed theorems, program hypotheses explicit).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## `rec_fire_args(fireKind, pvo, pvc, po, pc, us, ao, an, rP, ctorParams)` -/

/-- Model of `rec_fire_args`. -/
def rfaW (p : Prog) (k : Nat) (m : Mem) (fireKind pvo pvc po pc us ao an rP cp : Word) :
    Option (List Word × Mem) :=
  if fireKind = 1 then
    match callW p k "inst_spine_pins" [po, pc, us, ao, an, rP, pvo, pvc] m with
    | none => none
    | some (r, m₁) => some ([r.headD 0, r.tail.headD 0], m₁)
  else some ([ao, ispLen cp an], m)

theorem recFireArgs_spec (p : Prog) (hp : p.lookup "rec_fire_args" = some recFireArgsL) (k : Nat)
    (s₀ : St) (fireKind pvo pvc po pc us ao an rP cp : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (k + 1)) "rec_fire_args" [fireKind, pvo, pvc, po, pc, us, ao, an, rP, cp]
    ⦃fun r s' => LocEq s' s₀ ∧
      rfaW p k s₀.mem fireKind pvo pvc po pc us ao an rP cp = some ([r.headD 0, r.tail.headD 0], s'.mem);
      ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, recFireArgsL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
    callW_spec p k "inst_spine_pins"] <;>
  simp_all [rfaW, ispLen, Cmp.eval, LocEq, St.setLocs_cons, St.setLoc_loc,
    St.setLoc_mem, St.setLocs_nil, Locals.init_cons_zero, Locals.init_cons_succ, Sig.retVal,
    Sig.retOr] <;>
  (intro h; rename_i hd
   first
   | exact absurd (of_decide_eq_true hd) (UInt64.not_lt.mpr h)
   | exact absurd h (of_decide_eq_false hd))

theorem recFireArgs_nested_eq (rl : IRecRule) (lps : List NIdx) (us : LsIdx) (args : List EIdx)
    (rP : Nat) (lv : List LIdx) (pins : List EIdx) (h : rl.fire = .nested lv pins) :
    recFireArgs rl lps us args rP = instSpinePins lps us args rP pins := by
  simp [recFireArgs, h]

theorem recFireArgs_plain_run (rl : IRecRule) (lps : List NIdx) (us : LsIdx) (args : List EIdx)
    (rP : Nat) (h : rl.fire = .plain) (a : AState) :
    (recFireArgs rl lps us args rP).run a = .ok (args.take rl.ctorParams, a) := by
  simp [recFireArgs, h]; rfl

/-- **`rec_fire_args` refines `recFireArgs`.** Statement changes: `CoreAfterG` (the nested arm leaves a
slice on the stack) and both input slices below the stack top. -/
theorem recFireArgs_refines' (p : Prog) (hp : IotaProg' p) (hc : IotaCallees p) (hw : WhnfCallees p)
    (hE : ErecKeptInst p) :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb fireKind pvo pvc po pc us ao an rP ctorParams : Word) (rl : IRecRule)
    (lps : List NIdx) (args : Array EIdx), CoreS dn s₀.mem a₀ vis fe MM eb → HW us →
    hslice? (s₀.mem.arr64 EREC) po.toNat pc.toNat = some lps → SpineR s₀.mem ao an args →
    (fireKind = 1 → ∃ lvls pins, rl.fire = .nested lvls pins ∧ SpineR s₀.mem pvo pvc pins.toArray) →
    (fireKind ≠ 1 → rl.fire = .plain) → rl.ctorParams = ctorParams.toNat →
    ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat →
    (fireKind = 1 → pvo.toNat + pvc.toNat ≤ (spTop s₀.mem).toNat) →
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "rec_fire_args" [fireKind, pvo, pvc, po, pc, us, ao, an, rP, ctorParams]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (recFireArgs rl lps (decI us) args.toList rP.toNat) a₀ ∧
      CoreAfterG dn s₀.mem s'.mem (AM.st (recFireArgs rl lps (decI us) args.toList rP.toNat) a₀) vis
        fe MM eb ∧
      ∃ xs, AM.res (recFireArgs rl lps (decI us) args.toList rP.toNat) a₀ = xs ∧
        SpineR s'.mem (r.headD 0) (r.tail.headD 0) xs.toArray; ⊤⦄ := by
  intro n s₀ a₀ dn vis fe MM eb fireKind pvo pvc po pc us ao an rP cp rl lps args hS hus hlps hsa hnest
    hplain hcp hat hpt
  cases n with
  | zero => exact invoke_zero_triple
  | succ n =>
  refine triple_post (recFireArgs_spec p hp.recFireArgs n s₀ fireKind pvo pvc po pc us ao an rP cp)
    fun r s' ⟨hloc, hW⟩ => ⟨hloc, ?_⟩
  simp only [rfaW] at hW
  by_cases h1 : fireKind = 1
  · rw [if_pos h1] at hW
    obtain ⟨lv, pins, hfire, hsp⟩ := hnest h1
    rcases hc1 : callW p n "inst_spine_pins" [po, pc, us, ao, an, rP, pvo, pvc] s₀.mem with _ | ⟨r₁, m₁⟩ <;>
      simp only [hc1, reduceCtorEq] at hW
    obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨t₁, ht₁, hloc1, hok, hca, xs, hres, hxs⟩ := triple_of_callW
      (instSpinePins_refines' p hp hc hw hE n ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe MM eb po pc us ao an rP
        pvo pvc lps args pins.toArray hS hus hlps hsa hsp hat (hpt h1)) hc1
    rw [recFireArgs_nested_eq rl lps (decI us) args.toList rP.toNat lv pins hfire]
    simp only [List.toList_toArray] at hok hca hres
    simp only [ht₁] at hxs hca
    rw [← hm]
    have hr1 : r.headD 0 = r₁.headD 0 := by
      have := congrArg (fun l => l.headD 0) hr; simpa using this.symm
    have hr2 : r.tail.headD 0 = r₁.tail.headD 0 := by
      have := congrArg (fun l => l.tail.headD 0) hr; simpa using this.symm
    exact ⟨hok, hca, xs, hres, by rw [hr1, hr2]; exact hxs⟩
  · rw [if_neg h1] at hW
    obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
    have hfire := hplain h1
    obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ (recFireArgs_plain_run rl lps (decI us) args.toList
      rP.toNat hfire a₀)
    have hr1 : r.headD 0 = ao := by
      have := congrArg (fun l => l.headD 0) hr.symm; simpa using this
    have hr2 : r.tail.headD 0 = ispLen cp an := by
      have := congrArg (fun l => l.tail.headD 0) hr.symm; simpa using this
    refine ⟨hok, ?_, _, hres, ?_⟩
    · rw [hst, ← hm]; exact ⟨MM, hS, KeptAll.refl _ _, (StackKept.refl _).toGrew⟩
    · rw [hr1, hr2, ← hm, hcp, ← ispLen_take' cp an args.toList (by simp [hsa.size])]
      exact hsa.take _ (ispLen_le cp an).2

/-! ## `and_rescue_slots(vis, ctor, nP, us)` -/

theorem rdW_eq_getElem (a : Array Word) (x : Word) (h : x.toNat < a.size) : rdW a x = a[x.toNat] := by
  simp [rdW, h]


/-- A checked word read, as `ld64`: `none` out of bounds. -/
def ldE (a : Array Word) (x : Word) : Option Word :=
  if h : x.toNat < a.size then some a[x.toNat] else none

/-- Model of the `and_rescue_slots` loop at L fuel `k`. -/
def iotaArW (p : Prog) (vis ctor nP us an : Word) : Nat → Mem → Word → Option (List Word × Mem)
  | 0, _, _ => none
  | k + 1, m, j =>
    if j < 2 then
      match callW p k "find_proj" [vis, an, j] m with
      | none => none
      | some (r₁, m₁) =>
        if r₁.headD 0 = 0 then some ([0], m₁)
        else match callW p k "fire_ok" [r₁.tail.headD 0, j, us] m₁ with
          | none => none
          | some (r₂, m₂) =>
            match ldE (m₂.arr64 EREC) (r₁.tail.headD 0 + 6) with
            | none => none
            | some w₆ =>
              if w₆ ≠ ctor then some ([0], m₂)
              else match ldE (m₂.arr64 EREC) (r₁.tail.headD 0 + 5) with
                | none => none
                | some w₅ =>
                  if w₅ ≠ nP then some ([0], m₂)
                  else match ldE (m₂.arr64 EREC) (r₁.tail.headD 0 + 7) with
                    | none => none
                    | some w₇ =>
                      if w₇ ≠ 2 then some ([0], m₂)
                      else if r₂.headD 0 = 0 then some ([0], m₂)
                      else iotaArW p vis ctor nP us an k m₂ (j + 1)
    else some ([1], m)

theorem andRescueLoop_spec (p : Prog) (k : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p k andRescueLoop
    ⦃fun r s' => r ≠ .brk ∧
      iotaArW p (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4) k s₀.mem (s₀.loc 5) =
        some (r.retOr [1], s'.mem); ⊤⦄ := by
  induction k generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ k ih =>
    rw [exec, step_while (w := andRescueLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        callW_spec p k "find_proj", callW_spec p k "fire_ok", ih] <;>
      finish (gen := 20) [iotaArW, ldE]


/-- Model of `and_rescue_slots`. -/
def arTop (p : Prog) (k : Nat) (m : Mem) (vis ctor nP us : Word) : Option (List Word × Mem) :=
  match callW p k "pin_at" [11] m with
  | none => none
  | some (r₀, m₀) => iotaArW p vis ctor nP us (r₀.headD 0) (k + 1) m₀ 0

theorem andRescueSlots_spec (p : Prog) (hp : p.lookup "and_rescue_slots" = some andRescueSlotsL)
    (k : Nat) (s₀ : St) (vis ctor nP us : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (k + 1)) "and_rescue_slots" [vis, ctor, nP, us]
    ⦃fun r s' => LocEq s' s₀ ∧ arTop p k s₀.mem vis ctor nP us = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, andRescueSlotsL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p k "pin_at", fun s₀ => Triple.step_exec (andRescueLoop_spec p (k + 1) s₀)] <;>
    finish [arTop]

theorem andRescueSlotsGo_zero_run (fe : IFEnv) (an ctor : NIdx) (nP : Nat) (ust : LsIdx) (j : Nat)
    (a : AState) : (andRescueSlotsGo fe an ctor nP ust 0 j).run a = .ok (true, a) := by
  simp [andRescueSlotsGo]; rfl

theorem andRescueSlotsGo_none_run (fe : IFEnv) (an ctor : NIdx) (nP : Nat) (ust : LsIdx) (n j : Nat)
    (a : AState) (h : fe.findProj? an j = none) :
    (andRescueSlotsGo fe an ctor nP ust (n + 1) j).run a = .ok (false, a) := by
  simp only [andRescueSlotsGo, h]; rfl

theorem andRescueSlotsGo_stop_run (fe : IFEnv) (an ctor : NIdx) (nP : Nat) (ust : LsIdx) (n j : Nat)
    (a a₂ : AState) (e : IProjEntry) (b : Bool) (h : fe.findProj? an j = some e)
    (hb : (e.fireOk ust).run a = .ok (b, a₂))
    (hc : (e.ctor == ctor && e.numParams == nP && e.numFields == 2 && b) = false) :
    (andRescueSlotsGo fe an ctor nP ust (n + 1) j).run a = .ok (false, a₂) := by
  simp only [andRescueSlotsGo, h, StateT.run_bind, hb, except_ok_bind, hc]
  rfl

theorem andRescueSlotsGo_cont_run (fe : IFEnv) (an ctor : NIdx) (nP : Nat) (ust : LsIdx) (n j : Nat)
    (a a₂ a₃ : AState) (e : IProjEntry) (b res : Bool)
    (h : fe.findProj? an j = some e) (hb : (e.fireOk ust).run a = .ok (b, a₂))
    (hc : (e.ctor == ctor && e.numParams == nP && e.numFields == 2 && b) = true)
    (hr : (andRescueSlotsGo fe an ctor nP ust n (j + 1)).run a₂ = .ok (res, a₃)) :
    (andRescueSlotsGo fe an ctor nP ust (n + 1) j).run a = .ok (res, a₃) := by
  simp only [andRescueSlotsGo, h, StateT.run_bind, hb, except_ok_bind, hc, if_true]
  exact hr

theorem decTbl_bound (a : Array Word) (q : Nat) (tbl : IProjTable) (h : decTbl a q = some tbl) :
    q + 12 < a.size := by
  simp only [decTbl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, g, hg, -⟩ := h
  simp only [hlist?, nat?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hg
  obtain ⟨-, -, c, ⟨w, hw, -⟩, -⟩ := hg
  exact (Array.getElem?_eq_some_iff.mp hw).1

theorem ldE_eq (a : Array Word) (x : Word) (h : x.toNat < a.size) : ldE a x = some (rdW a x) := by
  simp [ldE, rdW, h]

theorem addW13 (q c : Word) (a : Array Word) (hq : q.toNat + 12 < a.size)
    (hsz : a.size < 2 ^ 63) (hc : c.toNat ≤ 12) : (q + c).toNat = q.toNat + c.toNat := by
  rw [UInt64.toNat_add]; simp; omega

/-- **The `and_rescue_slots` loop refines `andRescueSlotsGo`**. -/
theorem arW_ok (p : Prog) (hcc : ProjCallees p) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (eb ctor nP us anW : Word) (hctor : HW ctor) (hus : HW us) (hanW : HW anW) :
    ∀ (K k : Nat) (m : Mem) (a : AState) (M : ModeMaps) (j : Word) (L : List Word) (m' : Mem),
      j.toNat + K = 2 → CoreS dn m a vis fe M eb →
      (∃ (h : EIdx) (c : NIdx), a.store.view h = some (.const c (decI us))) →
      iotaArW p vis ctor nP us anW k m j = some (L, m') →
      AM.ok (andRescueSlotsGo fe (decI anW) (decI ctor) nP.toNat (decI us) K j.toNat) a ∧
      CoreAfter dn m m' (AM.st (andRescueSlotsGo fe (decI anW) (decI ctor) nP.toNat (decI us) K
        j.toNat) a) vis fe M eb ∧
      AM.res (andRescueSlotsGo fe (decI anW) (decI ctor) nP.toNat (decI us) K j.toNat) a = decBool L ∧
      HW (L.headD 0) := by
  intro K
  induction K with
  | zero =>
    intro k m a M j L m' hK hS hV hL
    have hn : ¬ j < 2 := fun h => by
      have : j.toNat < 2 := h
      omega
    cases k with
    | zero => simp [iotaArW] at hL
    | succ k =>
    simp only [iotaArW, hn, ↓reduceIte] at hL
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hL)
    refine CoreRef.of_run (ok := ResH) (andRescueSlotsGo_zero_run fe (decI anW) (decI ctor) nP.toNat (decI us)
      j.toNat a) ⟨M, hS, KeptAll.refl _ _, StackKept.refl _⟩ ?_ (by simp [ResH, HW])
    · simp [decBool]
  | succ K ih =>
    intro k m a M j L m' hK hS hV hL
    have hlt : j < 2 := by
      have : j.toNat < 2 := by omega
      exact this
    cases k with
    | zero => simp [iotaArW] at hL
    | succ k =>
    rcases hc1 : callW p k "find_proj" [vis, anW, j] m with _ | ⟨r₁, m₁⟩
    · simp only [iotaArW, hlt, ↓reduceIte, hc1] at hL; cases hL
    obtain ⟨hok1, ⟨M₁, hS₁, hK₁, hSt₁⟩, hres1, hr₁⟩ := CoreSpec.of_callW
      (hcc.findProj k ⟨m, Locals.init []⟩ a dn vis fe M eb anW j hS hanW) hc1
    have hSt₁ : StackKept m m₁ := hSt₁
    have hrunF : fe.findProj? (decI anW) j.toNat =
        decEntry (m.arr64 EREC) (r₁.headD 0) (r₁.tail.headD 0) j.toNat := hres1
    by_cases h0 : r₁.headD 0 = 0
    · simp only [iotaArW, hlt, ↓reduceIte, hc1, h0] at hL
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hL)
      have hnone : decEntry (m.arr64 EREC) (r₁.headD 0) (r₁.tail.headD 0) j.toNat = none := by
        simp only [decEntry, h0, ↓reduceIte]
      rw [hnone] at hrunF
      refine CoreRef.of_run (ok := ResH) (andRescueSlotsGo_none_run fe (decI anW) (decI ctor) nP.toNat (decI us)
        K j.toNat a hrunF) ⟨M₁, hS₁, hK₁, hSt₁⟩ ?_ (by simp [ResH, HW])
      · simp [decBool]
    obtain ⟨tbl, htbl, hfe⟩ := hcc.projFound k m a dn vis fe M eb anW j r₁ m₁ hS hc1 h0
    have hEr1 : m₁.arr64 EREC = m.arr64 EREC := hcc.erec k "find_proj" _ m r₁ m₁ (Or.inl rfl) hc1
    have hsome : decEntry (m.arr64 EREC) (r₁.headD 0) (r₁.tail.headD 0) j.toNat =
        some (tbl.entry j.toNat) := by
      simp only [decEntry, if_neg h0, htbl, Option.map_some]
    rw [hsome] at hrunF
    rcases hc2 : callW p k "fire_ok" [r₁.tail.headD 0, j, us] m₁ with _ | ⟨r₂, m₂⟩
    · simp only [iotaArW, hlt, ↓reduceIte, hc1, h0, hc2] at hL; cases hL
    obtain ⟨hrunB, ⟨M₂, hS₂, hK₂, hSt₂⟩, hr₂⟩ := CoreSpec.run
      (hcc.fireOk k ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb (r₁.tail.headD 0) j us tbl hS₁ hus
        (by rw [hEr1]; exact htbl) hfe (by simpa [IProjTable.entry] using findProj?_lt hrunF)
        hV) hc2
    have hSt₂ : StackKept m₁ m₂ := hSt₂
    have hEr2 : m₂.arr64 EREC = m₁.arr64 EREC := hcc.erec k "fire_ok" _ m₁ r₂ m₂ (Or.inr rfl) hc2
    -- the record's words
    have hE2 : m₂.arr64 EREC = m.arr64 EREC := hEr2.trans hEr1
    have hsz := hS.erec
    have hbd := decTbl_bound _ _ _ htbl
    obtain ⟨-, hnp, hw6, hct, hnf⟩ := decTbl_words htbl hsz
    have hx6 : (r₁.tail.headD 0 + 6).toNat < (m₂.arr64 EREC).size := by
      rw [addW13 _ _ _ hbd hsz (by decide), hE2]; simp only [UInt64.toNat_ofNat]; omega
    have hx5 : (r₁.tail.headD 0 + 5).toNat < (m₂.arr64 EREC).size := by
      rw [addW13 _ _ _ hbd hsz (by decide), hE2]; simp only [UInt64.toNat_ofNat]; omega
    have hx7 : (r₁.tail.headD 0 + 7).toNat < (m₂.arr64 EREC).size := by
      rw [addW13 _ _ _ hbd hsz (by decide), hE2]; simp only [UInt64.toNat_ofNat]; omega
    -- the common twin data
    have hW6 : rdW (m₂.arr64 EREC) (r₁.tail.headD 0 + 6) = rdW (m.arr64 EREC) (r₁.tail.headD 0 + 6) := by
      rw [hE2]
    have hW5 : rdW (m₂.arr64 EREC) (r₁.tail.headD 0 + 5) = rdW (m.arr64 EREC) (r₁.tail.headD 0 + 5) := by
      rw [hE2]
    have hW7 : rdW (m₂.arr64 EREC) (r₁.tail.headD 0 + 7) = rdW (m.arr64 EREC) (r₁.tail.headD 0 + 7) := by
      rw [hE2]
    have hfire : (tbl.entry j.toNat).fireOk (decI us) = (tbl.entry j.toNat).fireOk (decI us) := rfl
    have hb : (((tbl.entry j.toNat).fireOk (decI us)).run a) =
        .ok (decBool r₂, AM.st ((tbl.entry j.toNat).fireOk (decI us)) a) :=
      hrunB
    have hb' := hb
    have hfin : ((tbl.entry j.toNat).ctor == decI ctor && (tbl.entry j.toNat).numParams == nP.toNat &&
          (tbl.entry j.toNat).numFields == 2 && decBool r₂) = false → L = [0] → m' = m₂ →
        AM.ok (andRescueSlotsGo fe (decI anW) (decI ctor) nP.toNat (decI us) (K + 1) j.toNat) a ∧
        CoreAfter dn m m' (AM.st (andRescueSlotsGo fe (decI anW) (decI ctor) nP.toNat (decI us) (K + 1)
          j.toNat) a) vis fe M eb ∧
        AM.res (andRescueSlotsGo fe (decI anW) (decI ctor) nP.toNat (decI us) (K + 1) j.toNat) a =
          decBool L ∧ HW (L.headD 0) := by
      intro hcf hLe hme
      subst hLe; subst hme
      refine CoreRef.of_run (ok := ResH) (andRescueSlotsGo_stop_run fe (decI anW) (decI ctor) nP.toNat (decI us)
        K j.toNat a _ (tbl.entry j.toNat) (decBool r₂) hrunF hb' hcf) ⟨M₂, hS₂, hK₁.trans hK₂,
        hSt₁.trans hSt₂⟩ ?_ (by simp [ResH, HW])
      · simp [decBool]
    have hL' := hL
    simp only [iotaArW, hlt, ↓reduceIte, hc1, h0, hc2] at hL'
    rw [ldE_eq _ _ hx6] at hL'
    dsimp only at hL'
    by_cases hc6 : rdW (m₂.arr64 EREC) (r₁.tail.headD 0 + 6) = ctor
    · rw [if_neg (by simpa using hc6)] at hL'
      rw [ldE_eq _ _ hx5] at hL'
      dsimp only at hL'
      by_cases hc5 : rdW (m₂.arr64 EREC) (r₁.tail.headD 0 + 5) = nP
      · rw [if_neg (by simpa using hc5)] at hL'
        rw [ldE_eq _ _ hx7] at hL'
        dsimp only at hL'
        by_cases hc7 : rdW (m₂.arr64 EREC) (r₁.tail.headD 0 + 7) = 2
        · rw [if_neg (by simpa using hc7)] at hL'
          by_cases hr20 : r₂.headD 0 = 0
          · rw [if_pos hr20] at hL'
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hL')
            refine hfin ?_ rfl rfl
            have hb0 : decBool r₂ = false := by simp only [decBool]; rw [hr20]; rfl
            rw [hb0]; simp
          · rw [if_neg hr20] at hL'
            have h1 : (j + 1).toNat = j.toNat + 1 := uint64_succ_toNat 2 j hlt
            obtain ⟨hok3, ⟨M₃, hS₃, hK₃, hSt₃⟩, hres3, hL1⟩ := ih k m₂ _ M₂ (j + 1) L m'
              (by omega) hS₂ (by
                obtain ⟨h, c, hv⟩ := hV
                exact ⟨h, c, by
                  rw [show AM.st (pure (fe.findProj? (decI anW) j.toNat) : AM _) a = a from rfl,
                    fireOk_store hb]; exact hv⟩) hL'
            rw [h1] at hok3 hS₃ hres3
            have hrunR := AM.run_of_ok _ _ hok3
            have hcond : ((tbl.entry j.toNat).ctor == decI ctor && (tbl.entry j.toNat).numParams == nP.toNat &&
                (tbl.entry j.toNat).numFields == 2 && decBool r₂) = true := by
              have hh6 : HW (rdW (m₂.arr64 EREC) (r₁.tail.headD 0 + 6)) := by rw [hW6]; exact hw6
              have e1 : ((tbl.entry j.toNat).ctor == decI ctor) = true := by
                show (tbl.ctor == decI ctor) = true
                rw [hct, ← hW6, decI_beq _ _ hh6 hctor]
                exact decide_eq_true hc6
              have e2 : ((tbl.entry j.toNat).numParams == nP.toNat) = true := by
                show (tbl.numParams == nP.toNat) = true
                rw [hnp, ← hW5, hc5]; simp
              have e3 : ((tbl.entry j.toNat).numFields == 2) = true := by
                show (tbl.numFields == 2) = true
                rw [hnf, ← hW7, hc7]; rfl
              have e4 : decBool r₂ = true := by simp only [decBool]; simpa using hr20
              rw [e1, e2, e3, e4]; rfl
            refine CoreRef.of_run (ok := ResH) (andRescueSlotsGo_cont_run fe (decI anW) (decI ctor) nP.toNat
              (decI us) K j.toNat a _ _ (tbl.entry j.toNat) (decBool r₂) _ hrunF hb' hcond hrunR)
              ⟨M₃, hS₃, hK₁.trans (hK₂.trans hK₃), hSt₁.trans (hSt₂.trans hSt₃)⟩ hres3 hL1
        · rw [if_pos (by simpa using hc7)] at hL'
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hL')
          refine hfin ?_ rfl rfl
          have : (tbl.entry j.toNat).numFields ≠ 2 := by
            show tbl.numFields ≠ 2
            rw [hnf, ← hW7]
            intro h; apply hc7; exact UInt64.toNat_inj.mp (by simpa using h)
          simp [this]
      · rw [if_pos (by simpa using hc5)] at hL'
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hL')
        refine hfin ?_ rfl rfl
        have : (tbl.entry j.toNat).numParams ≠ nP.toNat := by
          show tbl.numParams ≠ nP.toNat
          rw [hnp, ← hW5]
          intro h; apply hc5; exact UInt64.toNat_inj.mp h
        simp [this]
    · rw [if_pos (by simpa using hc6)] at hL'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hL')
      refine hfin ?_ rfl rfl
      have hh6 : HW (rdW (m₂.arr64 EREC) (r₁.tail.headD 0 + 6)) := by rw [hW6]; exact hw6
      have : ((tbl.entry j.toNat).ctor == decI ctor) = false := by
        show (tbl.ctor == decI ctor) = false
        rw [hct, ← hW6, decI_beq _ _ hh6 hctor]
        exact decide_eq_false hc6
      simp [this]

theorem andRescueSlots_run (fe : IFEnv) (ctor : NIdx) (nP : Nat) (ust : LsIdx) (an : NIdx)
    (a a₁ : AState) (b : Bool) (hp : (pinAt PIN_AND).run a = .ok (an, a))
    (hr : (andRescueSlotsGo fe an ctor nP ust 2 0).run a = .ok (b, a₁)) :
    (andRescueSlots fe ctor nP ust).run a = .ok (b, a₁) := by
  simp only [andRescueSlots, pinAnd, StateT.run_bind, hp, except_ok_bind, hr]

/-- **`and_rescue_slots` refines `andRescueSlots`** (`find_proj`, `fire_ok` and their facts as
`ProjCallees`). -/
theorem andRescueSlots_refines' (p : Prog) (hp : IotaProg' p) (hcc : ProjCallees p) :
    AndRescueSlotsOK p := by
  intro n s₀ a₀ dn vis fe MM eb ctor nP us hS hctor hus hV
  cases n with
  | zero => exact invoke_zero_triple
  | succ n =>
  refine triple_post (andRescueSlots_spec p hp.andRescueSlots n s₀ vis ctor nP us) fun r s' ⟨hloc,
    hW⟩ => ⟨hloc, ?_⟩
  simp only [arTop] at hW
  rcases hc0 : callW p n "pin_at" [11] s₀.mem with _ | ⟨r₀, m₀⟩ <;>
    simp only [hc0, reduceCtorEq] at hW
  obtain ⟨t₀, ht₀, hm₀, hloc0, hanHW, hpin⟩ := triple_of_callW
    (pinAt_refines p hp.pinat n ⟨s₀.mem, Locals.init []⟩ a₀ ⟨fun _ => hS.pins⟩ 11) hc0
  have hmm : m₀ = s₀.mem := by rw [← ht₀]; exact hm₀
  subst hmm
  have hanW : HW (r₀.headD 0) := hanHW
  obtain ⟨hok, hca, hres, hL1⟩ := arW_ok p hcc dn vis fe eb ctor nP us (r₀.headD 0) hctor hus hanW 2
    (n + 1) s₀.mem a₀ MM 0 r s'.mem (by simp) hS hV hW
  have hrunA := andRescueSlots_run fe (decI ctor) nP.toNat (decI us) (decI (r₀.headD 0)) a₀ _ _
    (by simpa [PIN_AND] using hpin) (AM.run_of_ok _ _ hok)
  obtain ⟨hokF, hstF, hresF⟩ := AM.of_run_ok _ _ _ _ hrunA
  refine ⟨hokF, ?_, ?_, hL1⟩
  · rw [hstF]; simpa using hca
  · rw [hresF]; simpa using hres

/-! ## `fab_scope_ok(d, fab, major)` -/

/-- Model of `fab_scope_ok`. -/
def fsW (p : Prog) (k : Nat) (m : Mem) (d fab major : Word) : Option (List Word × Mem) :=
  match callW p k "wscoped_bfast" [d, fab] m with
  | none => none
  | some (r₁, m₁) =>
    if r₁.headD 0 = 0 then some ([0], m₁)
    else match callW p k "loose_bvars_bounded_fast" [4000000000, 0, fab] m₁ with
      | none => none
      | some (r₂, m₂) =>
        if r₂.headD 0 = 0 then some ([0], m₂)
        else match callW p k "leaf_guard" [fab, major] m₂ with
          | none => none
          | some (r₃, m₃) => some ([r₃.headD 0], m₃)

theorem fabScopeOk_spec (p : Prog) (hp : p.lookup "fab_scope_ok" = some fabScopeOkL) (k : Nat)
    (s₀ : St) (d fab major : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (k + 1)) "fab_scope_ok" [d, fab, major]
    ⦃fun r s' => LocEq s' s₀ ∧ fsW p k s₀.mem d fab major = some ([r.headD 0], s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, fabScopeOkL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
    callW_spec p k "wscoped_bfast", callW_spec p k "loose_bvars_bounded_fast",
    callW_spec p k "leaf_guard"] <;>
  simp_all [fsW, Cmp.eval, BinOp.eval, LocEq, St.setLocs_cons, St.setLoc_loc, St.setLoc_mem,
    St.setLocs_nil, Locals.init_cons_zero, Locals.init_cons_succ, Sig.retVal, Sig.retOr]

theorem fabScopeOk_stop1 (d : Nat) (fab major : EIdx) (a a₁ : AState)
    (h : (wscopedBFast coreWalkFuel d fab).run a = .ok (false, a₁)) :
    (fabScopeOk d fab major).run a = .ok (false, a₁) := by
  simp only [fabScopeOk, StateT.run_bind, h, except_ok_bind]; rfl

theorem fabScopeOk_stop2 (d : Nat) (fab major : EIdx) (a a₁ a₂ : AState)
    (h : (wscopedBFast coreWalkFuel d fab).run a = .ok (true, a₁))
    (h2 : (looseBVarsBoundedFast coreWalkFuel 0 fab).run a₁ = .ok (false, a₂)) :
    (fabScopeOk d fab major).run a = .ok (false, a₂) := by
  simp only [fabScopeOk, StateT.run_bind, h, except_ok_bind, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, h2, Bool.not_false]; rfl

theorem fabScopeOk_go (d : Nat) (fab major : EIdx) (a a₁ a₂ a₃ : AState) (b : Bool)
    (h : (wscopedBFast coreWalkFuel d fab).run a = .ok (true, a₁))
    (h2 : (looseBVarsBoundedFast coreWalkFuel 0 fab).run a₁ = .ok (true, a₂))
    (h3 : (leafGuard coreWalkFuel fab major).run a₂ = .ok (b, a₃)) :
    (fabScopeOk d fab major).run a = .ok (b, a₃) := by
  simp only [fabScopeOk, StateT.run_bind, h, except_ok_bind, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, h2, Bool.not_false, h3]

/-- **`fab_scope_ok` refines `fabScopeOk`** (the three walks as `IotaCallees`' stubs). -/
theorem fabScopeOk_refines' (p : Prog) (hp : IotaProg' p) (hc : IotaCallees p) : FabScopeOkOK p := by
  intro n s₀ a₀ dn vis fe MM eb d fab major hS hfab hmaj
  cases n with
  | zero => exact invoke_zero_triple
  | succ n =>
  refine triple_post (fabScopeOk_spec p hp.fabScopeOk n s₀ d fab major) fun r s' ⟨hloc, hW⟩ =>
    ⟨hloc, ?_⟩
  simp only [fsW] at hW
  rcases hc1 : callW p n "wscoped_bfast" [d, fab] s₀.mem with _ | ⟨r₁, m₁⟩ <;>
    simp only [hc1, reduceCtorEq] at hW
  obtain ⟨hrun1, ⟨M₁, hS₁, hK₁, hSt₁⟩, hr₁⟩ := CoreSpec.run
    (hc.wscopedBFast n ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe MM eb d fab hS hfab) hc1
  by_cases h0 : r₁.headD 0 = 0
  · rw [if_pos h0] at hW
    obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    rw [decBool_f_m2c h0] at hrun1
    have hr0 : r.headD 0 = 0 := by simpa using hr.symm
    refine CoreRef.of_run (fabScopeOk_stop1 d.toNat (decE fab) (decE major) a₀ _ hrun1) ⟨M₁, hS₁,
      hK₁, hSt₁⟩ ?_ ?_
    · simp only [decBool]; rw [hr0]; rfl
    · unfold ResH HW; rw [hr0]; decide
  rw [if_neg h0] at hW
  rw [decBool_t_m2c h0] at hrun1
  rcases hc2 : callW p n "loose_bvars_bounded_fast" [4000000000, 0, fab] m₁ with _ | ⟨r₂, m₂⟩ <;>
    simp only [hc2, reduceCtorEq] at hW
  obtain ⟨hrun2, ⟨M₂, hS₂, hK₂, hSt₂⟩, hr₂⟩ := CoreSpec.run
    (hc.looseBVarsBoundedFast n ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb 0 fab hS₁ hfab) hc2
  have h00 : (0 : Word).toNat = 0 := rfl
  rw [h00] at hrun2
  by_cases h20 : r₂.headD 0 = 0
  · rw [if_pos h20] at hW
    obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    rw [decBool_f_m2c h20] at hrun2
    have hr0 : r.headD 0 = 0 := by simpa using hr.symm
    refine CoreRef.of_run (fabScopeOk_stop2 d.toNat (decE fab) (decE major) a₀ _ _ hrun1 hrun2)
      ⟨M₂, hS₂, hK₁.trans hK₂, hSt₁.trans hSt₂⟩ ?_ ?_
    · simp only [decBool]; rw [hr0]; rfl
    · unfold ResH HW; rw [hr0]; decide
  rw [if_neg h20] at hW
  rw [decBool_t_m2c h20] at hrun2
  rcases hc3 : callW p n "leaf_guard" [fab, major] m₂ with _ | ⟨r₃, m₃⟩ <;>
    simp only [hc3, reduceCtorEq] at hW
  obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  obtain ⟨hok3, ⟨M₃, hS₃, hK₃, hSt₃⟩, hres3, hr₃⟩ := CoreSpec.of_callW
    (hc.leafGuard n ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb fab major hS₂ hfab hmaj) hc3
  have hrun3 := AM.run_of_ok _ _ hok3
  have hr3 : r₃.headD 0 = r.headD 0 := by simpa using hr
  refine CoreRef.of_run (fabScopeOk_go d.toNat (decE fab) (decE major) a₀ _ _ _ _ hrun1 hrun2
    hrun3) ⟨M₃, hS₃, hK₁.trans (hK₂.trans hK₃), hSt₁.trans (hSt₂.trans hSt₃)⟩ ?_ ?_
  · rw [hres3]; simp only [decBool]; rw [hr3]
  · unfold ResH HW; rw [← hr3]; exact hr₃

/-! ## `lit_major_to_ctor(mode, vis, d, h)` -/

/-- Model of `lit_major_to_ctor`. -/
def lmW (p : Prog) (k : Nat) (m : Mem) (mode vis d h : Word) : Option (List Word × Mem) :=
  if h >>> 28 ≠ 8 then
    match callW p k "lit_to_ctor_if_nat" [vis, h] m with
    | none => none
    | some (r, m₁) => some ([r.headD 0], m₁)
  else if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if tcnt m LIT (tierW h) ≤ idxW h then none
  else match ldE (m.arr64 (tierA REC (tierW h))) (LIT.ad (idxW h) 0) with
    | none => none
    | some kind =>
      if kind ≠ 1 then
        match callW p k "lit_to_ctor_if_nat" [vis, h] m with
        | none => none
        | some (r, m₁) => some ([r.headD 0], m₁)
      else match callW p k "str_lit_supported" [vis] m with
        | none => none
        | some (r₁, m₁) =>
          if r₁.headD 0 = 0 then some ([h], m₁)
          else match callW p k "str_lit_ctor" [h] m₁ with
            | none => none
            | some (r₂, m₂) =>
              match callW p k "whnf" [mode, vis, d, r₂.headD 0] m₂ with
              | none => none
              | some (r₃, m₃) => some ([r₃.headD 0], m₃)

theorem litMajorToCtor_spec (p : Prog) (hp : p.lookup "lit_major_to_ctor" = some litMajorToCtorL)
    (k : Nat) (s₀ : St) (mode vis d h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (k + 1)) "lit_major_to_ctor" [mode, vis, d, h]
    ⦃fun r s' => LocEq s' s₀ ∧ lmW p k s₀.mem mode vis d h = some ([r.headD 0], s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, litMajorToCtorL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt,
      tcntM, evalE_tierE, evalE_idxE,
      callW_spec p k "lit_to_ctor_if_nat", callW_spec p k "str_lit_supported",
      callW_spec p k "str_lit_ctor", callW_spec p k "whnf"] <;>
    finish (gen := 20) [lmW, ldE, tierW, idxW, tfld, tcnt, TRec.ad, TRec.wd, TRec.ex]

theorem viewLit_ok' (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hh : h.toNat < 2 ^ 32)
    (hv : viewOK m h LIT) (hg : h >>> 28 = 8) :
    ∃ l, a.store.viewLit (decE h) = some l ∧ a.store.view (decE h) = some (.lit l) ∧
      RecRel m (tierW h) (idxW h) ⟨l⟩ := by
  obtain ⟨k, hk, hkr⟩ := node_of m a h litCS RecRel (·.lits) _ hR.lit.2 hv.2
  refine ⟨k.l, ?_, ?_, hkr⟩
  · simp only [EStore.viewLit, EStore.persGetLit]
    rw [proj_tier m a hR h hh (fun t i => t.getLit i) hv.1]
    simp only [ETables.getLit, Tbl.node?, decE_idx]
    rw [hk]; rfl
  · rw [view_tier m a hR h hh hv.1, get_lit _ h hh hg, Tbl.node?, hk]; rfl

theorem litMajorToCtor_run_nolit (r : CoreFnsA) (fe : IFEnv) (d : Nat) (h : EIdx) (a : AState)
    (ht : h.tag ≠ ETag.lit) : (litMajorToCtor r fe d h).run a = (litToCtorIfNat fe h).run a := by
  simp [litMajorToCtor, ht]

theorem litMajorToCtor_run_nat (r : CoreFnsA) (fe : IFEnv) (d : Nat) (h : EIdx) (a : AState)
    (ht : h.tag = ETag.lit) (n : Nat) (hv : a.store.view h = some (.lit (.natVal n))) :
    (litMajorToCtor r fe d h).run a = (litToCtorIfNat fe h).run a := by
  have hv' : (view h).run a = .ok (.lit (.natVal n), a) := by
    simp [view, hv, StateT.run_bind, StateT.run_get]; rfl
  simp only [litMajorToCtor, ht, beq_self_eq_true, ↓reduceIte, StateT.run_bind, hv', except_ok_bind]

theorem litMajorToCtor_run_str_unsup (r : CoreFnsA) (fe : IFEnv) (d : Nat) (h : EIdx) (a a₁ : AState)
    (ht : h.tag = ETag.lit) (s : String) (hv : a.store.view h = some (.lit (.strVal s)))
    (hs : (strLitSupported fe).run a = .ok (false, a₁)) :
    (litMajorToCtor r fe d h).run a = .ok (h, a₁) := by
  have hv' : (view h).run a = .ok (.lit (.strVal s), a) := by
    simp [view, hv, StateT.run_bind, StateT.run_get]; rfl
  simp only [litMajorToCtor, ht, beq_self_eq_true, ↓reduceIte, StateT.run_bind, hv', except_ok_bind,
    hs]; rfl

theorem litMajorToCtor_run_str (r : CoreFnsA) (fe : IFEnv) (d : Nat) (h : EIdx) (a a₁ a₂ a₃ : AState)
    (ht : h.tag = ETag.lit) (s : String) (hv : a.store.view h = some (.lit (.strVal s)))
    (hs : (strLitSupported fe).run a = .ok (true, a₁)) (c res : EIdx)
    (hc : (strLitToConstructor s).run a₁ = .ok (c, a₂)) (hw : (r.whnf d c).run a₂ = .ok (res, a₃)) :
    (litMajorToCtor r fe d h).run a = .ok (res, a₃) := by
  have hv' : (view h).run a = .ok (.lit (.strVal s), a) := by
    simp [view, hv, StateT.run_bind, StateT.run_get]; rfl
  simp only [litMajorToCtor, ht, beq_self_eq_true, ↓reduceIte, StateT.run_bind, hv', except_ok_bind,
    hs, hc, hw]

theorem ldE_some (a : Array Word) (x w : Word) (h : ldE a x = some w) :
    x.toNat < a.size ∧ w = rdW a x := by
  unfold ldE at h
  split at h
  · rename_i hb
    simp only [Option.some.injEq] at h
    exact ⟨hb, by rw [← h, rdW_eq_getElem a x hb]⟩
  · cases h

/-- A refinement transports along twins with the same run. -/
theorem CoreRef.of_run_eq {α : Type} [Inhabited α] {T T' : AM α} {a₀ : AState} {dec : List Word → α}
    {dn : NIdx → Option ConLeche.Name} {m₀ m : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {r : List Word} {ok : List Word → Prop} (hT : T'.run a₀ = T.run a₀)
    (h : CoreRef T a₀ dec dn m₀ vis fe M eb r m ok) : CoreRef T' a₀ dec dn m₀ vis fe M eb r m ok := by
  simp only [CoreRef, AM.ok, AM.st, AM.res, hT] at h ⊢
  exact h

/-- **`lit_major_to_ctor` refines `litMajorToCtor`.** Statement changes (the knot's `whnf` slot needs
them): `n ≤ 2 ^ 62`, the eager bit `eb = (mode >>> 1) &&& 1`; and `SupKeep` (`strLitSupported` keeps the
store's views: `StrLitKeep.supKeep_of`) as a hypothesis. -/
theorem litMajorToCtor_refines' (p : Prog) (hp : IotaProg' p) (hc : IotaCallees p)
    (hw : WhnfCallees p) (hsup : ∀ fe : IFEnv, SupKeep fe) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d h : Word), CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 →
    eb = (mode >>> 1) &&& 1 → HW h →
    CoreSpec p (n + 1) "lit_major_to_ctor" [mode, vis, d, h]
      (litMajorToCtor (coreKnot (decMode mode) fe id F) fe d.toNat (decE h)) decH s₀ a₀ dn vis fe MM
      eb := by
  intro n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d h hS hm4 hebm hh
  refine triple_post (litMajorToCtor_spec p hp.litMajorToCtor n s₀ mode vis d h) fun r s' ⟨hloc,
    hW⟩ => ⟨hloc, ?_⟩
  have hR := hS.arena.1
  simp only [lmW] at hW
  by_cases h8 : h >>> 28 = 8
  · rw [if_neg (by simpa using h8)] at hW
    obtain ⟨hv1, hW⟩ := of_ite_none hW
    obtain ⟨hv2, hW⟩ := of_ite_none hW
    obtain ⟨l, hl, hview, hrel⟩ := viewLit_ok' s₀.mem a₀ hR h hh ⟨hv1, UInt64.not_le.mp hv2⟩ h8
    have htag : (decE h).tag = ETag.lit := (decE_tag_lit h hh).mpr h8
    cases hld : ldE (s₀.mem.arr64 (tierA REC (tierW h))) (LIT.ad (idxW h) 0) with
    | none => rw [hld] at hW; cases hW
    | some kind =>
    rw [hld] at hW
    obtain ⟨-, hkind⟩ := ldE_some _ _ _ hld
    dsimp only at hW
    cases l with
    | natVal N =>
      have hk0 : kind = 0 := by rw [hkind]; exact hrel.1
      rw [if_pos (by rw [hk0]; decide)] at hW
      rcases hc1 : callW p n "lit_to_ctor_if_nat" [vis, h] s₀.mem with _ | ⟨r₁, m₁⟩ <;>
        simp only [hc1, reduceCtorEq] at hW
      obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      have hr1 : r.headD 0 = r₁.headD 0 := by simpa using hr.symm
      have hcr := CoreRef.of_run_eq (T' := litMajorToCtor (coreKnot (decMode mode) fe id F) fe d.toNat (decE h))
        (litMajorToCtor_run_nat _ fe d.toNat (decE h) a₀ htag N hview)
        (CoreSpec.of_callW (hc.litToCtorIfNat n ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe MM eb h hS hh) hc1)
      obtain ⟨hok, hca, hres, hr₁⟩ := hcr
      refine ⟨hok, ?_, ?_, ?_⟩
      · exact hca
      · rw [hres]; simp only [decH]; rw [hr1]
      · unfold ResH HW at hr₁ ⊢; rw [hr1]; exact hr₁
    | strVal str =>
      have hk1 : kind = 1 := by rw [hkind]; exact hrel.1
      rw [if_neg (by rw [hk1]; decide)] at hW
      rcases hc1 : callW p n "str_lit_supported" [vis] s₀.mem with _ | ⟨r₁, m₁⟩ <;>
        simp only [hc1, reduceCtorEq] at hW
      obtain ⟨hrun1, ⟨M₁, hS₁, hK₁, hSt₁⟩, hr₁⟩ := CoreSpec.run
        (hw.strLitSupported n ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe MM eb hS) hc1
      by_cases h0 : r₁.headD 0 = 0
      · rw [if_pos h0] at hW
        obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
        rw [decBool_f_m2c h0] at hrun1
        have hr1 : r.headD 0 = h := by simpa using hr.symm
        refine CoreRef.of_run (litMajorToCtor_run_str_unsup (coreKnot (decMode mode) fe id F) fe
          d.toNat (decE h) a₀ _ htag str hview hrun1) ⟨M₁, hS₁, hK₁, hSt₁⟩ ?_ ?_
        · simp only [decH]; rw [hr1]
        · unfold ResH HW; rw [hr1]; exact hh
      · rw [if_neg h0] at hW
        rw [decBool_t_m2c h0] at hrun1
        rcases hc2 : callW p n "str_lit_ctor" [h] m₁ with _ | ⟨r₂, m₂⟩ <;>
          simp only [hc2, reduceCtorEq] at hW
        have hviewA : (AM.st (strLitSupported fe) a₀).store.view (decE h) = some (.lit (.strVal str)) :=
          hsup fe a₀ (decE h) _ hview
        obtain ⟨hrun2, ⟨M₂, hS₂, hK₂, hSt₂⟩, hr₂⟩ := CoreSpec.run
          (hw.strLitCtor n ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb h str hS₁ hh hviewA) hc2
        rcases hc3 : callW p n "whnf" [mode, vis, d, r₂.headD 0] m₂ with _ | ⟨r₃, m₃⟩ <;>
          simp only [hc3, reduceCtorEq] at hW
        obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
        obtain ⟨hok3, ⟨M₃, hS₃, hK₃, hSt₃⟩, hres3, hr₃⟩ := CoreSpec.of_callW
          ((hk n (Nat.le_refl _)).whnf F ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode d _ hnF hn62
            ⟨hS₂, hm4, hebm⟩ hr₂) hc3
        have hrun3 := AM.run_of_ok _ _ hok3
        have hr1 : r₃.headD 0 = r.headD 0 := by simpa using hr
        refine CoreRef.of_run (litMajorToCtor_run_str (coreKnot (decMode mode) fe id F) fe d.toNat
          (decE h) a₀ _ _ _ htag str hview hrun1 _ _ hrun2 hrun3) (hm ▸ ⟨M₃, hS₃, hK₁.trans
          (hK₂.trans hK₃), hSt₁.trans (hSt₂.trans hSt₃)⟩) ?_ ?_
        · simp only [decH]; rw [← hr1]; exact hres3
        · unfold ResH HW; rw [← hr1]; exact hr₃
  · rw [if_pos h8] at hW
    rcases hc1 : callW p n "lit_to_ctor_if_nat" [vis, h] s₀.mem with _ | ⟨r₁, m₁⟩ <;>
      simp only [hc1, reduceCtorEq] at hW
    obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have hr1 : r.headD 0 = r₁.headD 0 := by simpa using hr.symm
    have hcr := CoreRef.of_run_eq (T' := litMajorToCtor (coreKnot (decMode mode) fe id F) fe d.toNat (decE h))
      (litMajorToCtor_run_nolit _ fe d.toNat (decE h) a₀ (fun ht => h8 ((decE_tag_lit h hh).mp ht)))
      (CoreSpec.of_callW (hc.litToCtorIfNat n ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe MM eb h hS hh) hc1)
    obtain ⟨hok, hca, hres, hr₁⟩ := hcr
    refine ⟨hok, ?_, ?_, ?_⟩
    · exact hca
    · rw [hres]; simp only [decH]; rw [hr1]
    · unfold ResH HW at hr₁ ⊢; rw [hr1]; exact hr₁

/-! ## `mk_proj` as a run under `CoreS` -/

theorem pjinternW_hw (m : Mem) (a : AState) (hR : ProjR m a) (n u e : Word) (w : Word) (m' : Mem)
    (hI : pjinternW m n u e = some (w, m')) : w.toNat < 2 ^ 32 := by
  exact consInternM_lt projCS_wf hR hI

theorem mkProjW_hw (m : Mem) (a : AState) (hA : ArenaD m a) (n i e r : Word) (m' : Mem)
    (hI : mkProjW m n i e = some (r, m')) : r.toNat < 2 ^ 32 := by
  unfold mkProjW at hI
  split at hI
  · cases hI
  cases hI₁ : pjinternW m n i e with
  | none => simp [hI₁, mkK] at hI
  | some p =>
  obtain ⟨r₁, m₁⟩ := p
  simp only [hI₁, mkK_some] at hI
  cases hP : derPutW PJDER 32 m₁ (cnt2 m 32) r₁ (packBFL (derBW m e) (derFW m e) (exprLPW m e)) with
  | none => simp [hP] at hI
  | some m₂ =>
  simp only [hP, Option.some.injEq, Prod.mk.injEq] at hI
  obtain ⟨rfl, rfl⟩ := hI
  exact pjinternW_hw m a hA.1.proj n i e _ m₁ hI₁

theorem keeps_cpl_internProj (n : NIdx) (i : Nat) (e : EIdx) :
    Keeps cpl (internE (.proj n i e)) := by
  simp only [internE]; exact keeps_cpl_internNodeE _

/-- **`mk_proj` as a run.** -/
theorem callW_mkProj (p : Prog) (hp : IotaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
    (hD : ArenaD s₀.mem a₀) (nm i e : Word) (r : List Word) (m' : Mem)
    (h : callW p n "mk_proj" [nm, i, e] s₀.mem = some (r, m')) :
    AM.ok (internE (.proj (decI nm) i.toNat (decE e))) a₀ ∧
    ArenaD m' (AM.st (internE (.proj (decI nm) i.toNat (decE e))) a₀) ∧
    AM.res (internE (.proj (decI nm) i.toNat (decE e))) a₀ = decE (r.headD 0) ∧
    MemFrame [PJREC, PJSLOT, PJDER, PJREC + 256, PJSLOT + 256, PJDER + 256] [32, 33] s₀.mem m' ∧ HW (r.headD 0) := by
  obtain ⟨s', rfl, hm⟩ := triple_of_callW (mkProj_spec p hp.spine.derb hp.projf hp.projp hp.proji
    hp.mkproj n s₀ nm i e) h
  obtain ⟨-, hm⟩ := hm
  obtain ⟨h1, h2, h3⟩ := mkProj_ok s₀.mem a₀ hD nm i e _ _ hm
  exact ⟨h1, h2, h3, mkProjW_frameA _ _ _ _ _ _ hm, mkProjW_hw _ a₀ hD nm i e _ _ hm⟩

/-- `mk_proj`'s fine frame is within the store's. -/
theorem MemFrame.pjStore {m m' : Mem} (h : MemFrame [PJREC, PJSLOT, PJDER, PJREC + 256, PJSLOT + 256, PJDER + 256] [32, 33] m m') :
    MemFrame L.Rom.StoreA L.Rom.StoreC m m' := h.mono
  (fun b hb => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
    unfold L.Rom.StoreA
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> exact low_tier_mem _ (by decide))
  (fun x hx => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    unfold L.Rom.StoreC; rcases hx with rfl | rfl
    · exact List.mem_map.mpr ⟨32, by simp, rfl⟩
    · exact List.mem_map.mpr ⟨33, by simp, rfl⟩)

/-- **`CoreS` across a `proj` interning step.** -/
theorem CoreS.of_proj {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) (hD : ArenaD m' a')
    (hcpl : cpl a' = cpl a) (hf : MemFrame [PJREC, PJSLOT, PJDER, PJREC + 256, PJSLOT + 256, PJDER + 256] [32, 33] m m') :
    CoreS dn m' a' vis fe M eb :=
  hS.arena_frame hD hcpl hf
    (fun b hb => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
                    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by simp [PJREC, PJSLOT, PJDER])
    (fun b hb => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
                    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (fun x hx => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
                    rcases hx with rfl | rfl <;> decide)
    (fun x hx => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
                    rcases hx with rfl | rfl <;> decide)
    (by simp [PJREC, PJSLOT, PJDER]) (by simp)

/-! ## `eta_projs(T, b, nF)` -/

/-- Model of the `eta_projs` loop at L fuel `k`: the memory after the stores. -/
def etpW (p : Prog) (T b nF o : Word) : Nat → Mem → Word → Option Mem
  | 0, _, _ => none
  | k + 1, m, j =>
    if j < nF then
      match callW p k "mk_proj" [T, j, b] m with
      | none => none
      | some (r, m₁) =>
        if (o + j).toNat < (m₁.arr64 SPN).size then
          etpW p T b nF o k (m₁.set64 SPN (o + j) (r.headD 0)) (j + 1)
        else none
    else some m

theorem etpW_end (p : Prog) (T b nF o : Word) (k : Nat) (m : Mem) (j : Word) (h : ¬ j < nF) :
    etpW p T b nF o (k + 1) m j = some m := by
  simp only [etpW, h, ↓reduceIte]

theorem etpW_cont (p : Prog) (T b nF o : Word) (k : Nat) (m m₁ : Mem) (j : Word) (r : List Word)
    (h : j < nF) (hc : callW p k "mk_proj" [T, j, b] m = some (r, m₁))
    (hg : (o + j).toNat < (m₁.arr64 SPN).size) :
    etpW p T b nF o (k + 1) m j = etpW p T b nF o k (m₁.set64 SPN (o + j) (r.headD 0)) (j + 1) := by
  simp only [etpW, h, ↓reduceIte, hc, hg]

theorem etpW_bad (p : Prog) (T b nF o : Word) (k : Nat) (m m₁ : Mem) (j : Word) (r : List Word)
    (h : j < nF) (hc : callW p k "mk_proj" [T, j, b] m = some (r, m₁))
    (hg : ¬ (o + j).toNat < (m₁.arr64 SPN).size) :
    etpW p T b nF o (k + 1) m j = none := by
  simp only [etpW, h, ↓reduceIte, hc, hg]

theorem etaProjsLoop_spec (p : Prog) (k : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p k etaProjsLoop
    ⦃fun r s' => r = .normal ∧ s'.loc 2 = s₀.loc 2 ∧ s'.loc 3 = s₀.loc 3 ∧
      etpW p (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) k s₀.mem (s₀.loc 4) = some s'.mem; ⊤⦄ := by
  induction k generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ k ih =>
    rw [exec, step_while (w := etaProjsLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        callW_spec p k "mk_proj", ih] <;>
      finish (gen := 20) [etpW_end, etpW_cont, etpW_bad]


/-- Model of `eta_projs`. -/
def etpTop (p : Prog) (k : Nat) (m : Mem) (T b nF : Word) : Option (List Word × Mem) :=
  if (136 : Word).toNat < (m.arr64 CTL).size then
    if UInt64.ofNat (m.arr64 SPN).size < rdW (m.arr64 CTL) 136 then none
    else if UInt64.ofNat (m.arr64 SPN).size - rdW (m.arr64 CTL) 136 < nF then none
    else match etpW p T b nF (rdW (m.arr64 CTL) 136) (k + 1) m 0 with
      | none => none
      | some m' =>
        if (136 : Word).toNat < (m'.arr64 CTL).size then
          some ([rdW (m.arr64 CTL) 136, nF], m'.set64 CTL 136 (rdW (m.arr64 CTL) 136 + nF))
        else none
  else none

theorem etaProjs_spec (p : Prog) (hp : p.lookup "eta_projs" = some etaProjsL) (k : Nat)
    (s₀ : St) (T b nF : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (k + 1)) "eta_projs" [T, b, nF]
    ⦃fun r s' => LocEq s' s₀ ∧ etpTop p k s₀.mem T b nF = some ([r.headD 0, r.tail.headD 0], s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, etaProjsL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      fun s₀ => Triple.step_exec (etaProjsLoop_spec p (k + 1) s₀)] <;>
    finish (gen := 20) [etpTop, rdW, Mem.len64]

theorem projNodesGo_nil_run (T : NIdx) (b : EIdx) (j : Nat) (a : AState) :
    (projNodesGo T b 0 j).run a = .ok ([], a) := by
  simp [projNodesGo]; rfl

theorem projNodesGo_cons_run (T : NIdx) (b : EIdx) (n j : Nat) (a a₁ a₂ : AState) (pn : EIdx)
    (ys : List EIdx) (h1 : (internE (.proj T j b)).run a = .ok (pn, a₁))
    (h2 : (projNodesGo T b n (j + 1)).run a₁ = .ok (ys, a₂)) :
    (projNodesGo T b (n + 1) j).run a = .ok (pn :: ys, a₂) := by
  simp only [projNodesGo, StateT.run_bind, h1, except_ok_bind, h2]; rfl

/-- **The `eta_projs` loop refines `projNodesGo`**, by induction on the remaining count. -/
theorem etpW_ok (p : Prog) (hp : IotaProg' p) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (eb T b nF o : Word) (hT : HW T) (hb : HW b) :
    ∀ (K k : Nat) (m : Mem) (a : AState) (M : ModeMaps) (j : Word) (m' : Mem),
      nF.toNat - j.toNat = K → j.toNat ≤ nF.toNat → CoreS dn m a vis fe M eb →
      o.toNat + nF.toNat ≤ (m.arr64 SPN).size →
      etpW p T b nF o k m j = some m' →
      ∃ ys, AM.ok (projNodesGo (decI T) (decE b) K j.toNat) a ∧
        CoreS dn m' (AM.st (projNodesGo (decI T) (decE b) K j.toNat) a) vis fe M eb ∧
        AM.res (projNodesGo (decI T) (decE b) K j.toNat) a = ys ∧
        (∀ i : Word, i < o + j → spW m' i = spW m i) ∧ (m'.arr64 SPN).size = (m.arr64 SPN).size ∧
        spTop m' = spTop m ∧ SpineR m' (o + j) (nF - j) ys.toArray ∧ BKept m m' ∧ PoolGrew m m' := by
  intro K
  induction K with
  | zero =>
    intro k m a M j m' hK hj hS hso hL
    have hn : ¬ j < nF := fun h => by
      have : j.toNat < nF.toNat := h
      omega
    cases k with
    | zero => simp [etpW] at hL
    | succ k =>
    rw [etpW_end p T b nF o k m j hn] at hL
    cases hL
    obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ (projNodesGo_nil_run (decI T) (decE b) j.toNat a)
    refine ⟨[], hok, ?_, hres, fun i _ => rfl, rfl, rfl, ?_, BKept.refl _, PoolGrew.refl _⟩
    · rw [hst]; exact hS
    · have hjp : nF - j = 0 := by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega)]
        simp; omega
      rw [hjp]
      have hlen : (o + j).toNat ≤ (m.arr64 SPN).size := by
        have := hS.spn
        rw [UInt64.toNat_add]; simp; omega
      exact SpineR.nil_at m _ hlen
  | succ K ih =>
    intro k m a M j m' hK hj hS hso hL
    have hlt : j < nF := by
      have : j.toNat < nF.toNat := by omega
      exact this
    cases k with
    | zero => simp [etpW] at hL
    | succ k =>
    have hspn := hS.spn
    have hoj : (o + j).toNat = o.toNat + j.toNat := by
      rw [UInt64.toNat_add]; simp; omega
    rcases hc1 : callW p k "mk_proj" [T, j, b] m with _ | ⟨r₁, m₁⟩
    · simp only [etpW, hlt, ↓reduceIte, hc1] at hL; cases hL
    by_cases hgn : ¬ (o + j).toNat < (m₁.arr64 SPN).size
    · rw [etpW_bad p T b nF o k m m₁ j r₁ hlt hc1 hgn] at hL; cases hL
    have hg := Classical.not_not.mp hgn
    rw [etpW_cont p T b nF o k m m₁ j r₁ hlt hc1 hg] at hL
    obtain ⟨hok1, hD1, hres1, hfr1, hw1⟩ := callW_mkProj p hp k ⟨m, Locals.init []⟩ a hS.arena T j b
      r₁ m₁ hc1
    have hfr1c : MemFrame L.Rom.StoreA L.Rom.StoreC m m₁ := hfr1.pjStore
    have hrun1 := AM.run_of_ok _ _ hok1
    have hspn1 : m₁.arr64 SPN = m.arr64 SPN :=
      hfr1c.1 SPN (fun h => by
        unfold L.Rom.StoreA at h; simp [lowTierArrs, SPN] at h) (by decide)
    have hcpl := Keeps.run (keeps_cpl_internProj (decI T) j.toNat (decE b)) hrun1
    have hS1 : CoreS dn m₁ (AM.st (internE (.proj (decI T) j.toNat (decE b))) a) vis fe M eb :=
      hS.of_proj hD1 hcpl hfr1
    have hsz1 : (m₁.arr64 SPN).size = (m.arr64 SPN).size := by rw [hspn1]
    have hfrS : MemFrame [SPN] [] m₁ (m₁.set64 SPN (o + j) (r₁.headD 0)) :=
      MemFrame.set64 m₁ SPN (by decide) _ _
    have hS2 : CoreS dn (m₁.set64 SPN (o + j) (r₁.headD 0)) (AM.st (internE (.proj (decI T) j.toNat (decE b))) a)
        vis fe M eb := hS1.frame_stk hfrS (fun b hb => by simpa using hb) (fun x hx => by simp at hx)
    have hsz2 : ((m₁.set64 SPN (o + j) (r₁.headD 0)).arr64 SPN).size = (m.arr64 SPN).size := by
      rw [size_set64, hsz1]
    have h1 : (j + 1).toNat = j.toNat + 1 := uint64_succ_toNat nF j hlt
    obtain ⟨ys, hok3, hS3, hres3, hbelow, hsz3, htop3, hys, hbk3, hpg3⟩ := ih k _ _ M (j + 1) m' (by omega)
      (by omega) hS2 (by rw [hsz2]; exact hso) hL
    have hrunI := AM.run_of_ok _ _ hok1
    rw [hres1] at hrunI
    have hrunR := AM.run_of_ok _ _ hok3
    rw [h1] at hrunR hS3 hres3
    rw [hres3] at hrunR
    have hrun := projNodesGo_cons_run (decI T) (decE b) K j.toNat a _ _ _ ys hrunI hrunR
    obtain ⟨hokF, hstF, hresF⟩ := AM.of_run_ok _ _ _ _ hrun
    have hbelow' : ∀ i : Word, i < o + j → spW m' i = spW m i := by
      intro i hi
      have hi' : i < o + (j + 1) := by
        rw [UInt64.lt_iff_toNat_lt] at hi ⊢
        have : (o + (j + 1)).toNat = o.toNat + j.toNat + 1 := by
          rw [UInt64.toNat_add, h1]; simp; omega
        omega
      rw [hbelow i hi']
      have hne : o + j ≠ i := by
        intro h; rw [← h] at hi
        exact absurd (UInt64.lt_iff_toNat_lt.mp hi) (Nat.lt_irrefl _)
      rw [spW_set64_ne _ _ _ _ hne]
      simp only [spW, hspn1]
    have hfr12 : MemFrame [PJREC, PJSLOT, PJDER, PJREC + 256, PJSLOT + 256, PJDER + 256, SPN] [32, 33] m (m₁.set64 SPN (o + j) (r₁.headD 0)) :=
      (hfr1.mono (by simp) (by simp)).trans (hfrS.mono (by simp) (by simp))
    refine ⟨decE (r₁.headD 0) :: ys, hokF, ?_, ?_, hbelow', ?_, ?_, ?_,
      (BKept.of_frame hfr12 (by decide) (by decide)).trans hbk3,
      (PoolGrew.of_frame hfr12 (by decide) (by decide)).trans hpg3⟩
    · rw [hstF]; exact hS3
    · rw [hresF]
    · rw [hsz3, hsz2]
    · rw [htop3]
      unfold spTop
      rw [Mem.arr64_set64_ne _ _ _ _ _ (show CTL ≠ SPN by decide)]
      exact hfr1c.2.1 136 (fun h => by
        unfold L.Rom.StoreC at h
        obtain ⟨k', hk', hkk⟩ := List.mem_map.mp h
        have := List.mem_range.mp hk'
        have h' := congrArg UInt64.toNat hkk
        simp [UInt64.toNat_ofNat] at h'; omega)
    · have e1 : nF - j = (nF - (j + 1)) + 1 := by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_add, UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega),
          UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega), h1]
        simp; omega
      have e2 : o + (j + 1) = o + j + 1 := by rw [UInt64.add_assoc]
      rw [e1]
      rw [e2] at hys
      have hsizeM : (m'.arr64 SPN).size = (m.arr64 SPN).size := by rw [hsz3, hsz2]
      refine SpineR.cons_slot m' (o + j) (nF - (j + 1)) (r₁.headD 0) ys hw1 ?_ hys ?_
        (by rw [hsizeM]; exact hspn)
      · have := hbelow (o + j) (by
          rw [UInt64.lt_iff_toNat_lt, e2, UInt64.toNat_add]
          have : (o + j + 1).toNat = o.toNat + j.toNat + 1 := by
            rw [UInt64.toNat_add]; simp; omega
          rw [← e2]
          rw [UInt64.toNat_add, h1]; simp; omega)
        rw [this, spW_set64_eq _ _ _ hg]
      · rw [hsizeM, UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega), hoj]
        omega

/-- **`eta_projs` refines `etaProjs`.** Statement change: `CoreAfterG` (the result slice is left on
the stack: the top grows) in place of `CoreAfter`. -/
@[refines ConRon.Arena.etaProjs]
theorem etaProjs_refines (p : Prog) (hp : IotaProg' p) :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb T b nF : Word), CoreS dn s₀.mem a₀ vis fe MM eb → HW T → HW b →
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "eta_projs" [T, b, nF]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (etaProjs (decI T) (decE b) nF.toNat) a₀ ∧
      CoreAfterG dn s₀.mem s'.mem (AM.st (etaProjs (decI T) (decE b) nF.toNat) a₀) vis fe MM eb ∧
      r.headD 0 = spTop s₀.mem ∧ r.tail.headD 0 = nF ∧
      ∃ xs, AM.res (etaProjs (decI T) (decE b) nF.toNat) a₀ = xs ∧
        SpineR s'.mem (r.headD 0) (r.tail.headD 0) xs.toArray; ⊤⦄ := by
  intro n s₀ a₀ dn vis fe MM eb T b nF hS hT hb
  cases n with
  | zero => exact invoke_zero_triple
  | succ n =>
  refine triple_post (etaProjs_spec p hp.etaProjs n s₀ T b nF) fun r s' ⟨hloc, hW⟩ => ⟨hloc, ?_⟩
  simp only [etpTop] at hW
  obtain ⟨h136, hW⟩ := of_ite_none' hW
  obtain ⟨hg1, hW⟩ := of_ite_none hW
  obtain ⟨hg2, hW⟩ := of_ite_none hW
  cases hm : etpW p T b nF (rdW (s₀.mem.arr64 CTL) 136) (n + 1) s₀.mem 0 with
  | none => rw [hm] at hW; cases hW
  | some m' =>
  rw [hm] at hW
  dsimp only at hW
  obtain ⟨hg3, hW⟩ := of_ite_none' hW
  obtain ⟨hr, hmm⟩ := Prod.mk.inj (Option.some.inj hW)
  have hspn := hS.spn
  have h64 : (s₀.mem.arr64 SPN).size < 2 ^ 64 := by omega
  have hsolt : (rdW (s₀.mem.arr64 CTL) 136).toNat ≤ (s₀.mem.arr64 SPN).size := by
    have : ¬ (s₀.mem.arr64 SPN).size < (rdW (s₀.mem.arr64 CTL) 136).toNat := by
      intro h
      apply hg1
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' h64]; exact h
    omega
  have hso : (rdW (s₀.mem.arr64 CTL) 136).toNat + nF.toNat ≤ (s₀.mem.arr64 SPN).size := by
    have h2 : ¬ UInt64.ofNat (s₀.mem.arr64 SPN).size - rdW (s₀.mem.arr64 CTL) 136 < nF := hg2
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _ (by
      rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' h64]; exact hsolt),
      UInt64.toNat_ofNat_of_lt' h64] at h2
    omega
  obtain ⟨ys, hok, hS', hres, hbelow, hsz, htop, hys, hbk, hpg⟩ := etpW_ok p hp dn vis fe eb T b nF
    (rdW (s₀.mem.arr64 CTL) 136) hT hb (nF.toNat - (0 : Word).toNat) (n + 1) s₀.mem a₀ MM 0 m' rfl
    (by simp) hS hso hm
  have hr1 : r.headD 0 = rdW (s₀.mem.arr64 CTL) 136 := by
    have := congrArg (fun l => l.headD 0) hr.symm; simpa using this
  have hr2 : r.tail.headD 0 = nF := by
    have := congrArg (fun l => l.tail.headD 0) hr.symm; simpa using this
  have hfS : MemFrame [] [136] m' (m'.set64 CTL 136 (rdW (s₀.mem.arr64 CTL) 136 + nF)) :=
    MemFrame.setCtl _ _ _
  have hS'' := hS'.frame_stk hfS (fun b hb => by simpa using hb) (fun x hx => by simpa using hx)
  have hoo : (rdW (s₀.mem.arr64 CTL) 136 + nF).toNat = (rdW (s₀.mem.arr64 CTL) 136).toNat + nF.toNat := by
    rw [UInt64.toNat_add]; simp; omega
  simp only [etaProjs]
  refine ⟨hok, ⟨MM, ?_, KeptAll.refl _ _, ?_⟩, hr1, hr2, ys, hres, ?_⟩
  · rw [← hmm]; simpa using hS''
  · rw [← hmm]
    refine ⟨?_, ?_, fun i hi => ?_, hbk.trans (BKept.of_frame hfS (by decide) (by decide)),
      hpg.trans (PoolGrew.of_frame hfS (by decide) (by decide))⟩
    · unfold spTop
      rw [rdW_set64, if_pos ⟨rfl, rfl, hg3⟩, UInt64.le_iff_toNat_le, hoo]
      omega
    · rw [size_set64L, hsz]
    · rw [spW_setCtl]
      exact hbelow i (by rw [UInt64.add_zero]; exact hi)
  · rw [← hmm, hr1, hr2]
    have := hys.setCtl 136 (rdW (s₀.mem.arr64 CTL) 136 + nF)
    simpa using this

/-! ## `eta_fab_args(T, to, tn, major, nF)` -/

theorem word_add_split (off a : Word) (i : Nat) (h : a.toNat ≤ i) :
    off + i.toUInt64 = (off + a) + (i - a.toNat).toUInt64 := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h
  have : i - a.toNat = d := by omega
  rw [this, hd]
  simp [Nat.toUInt64, UInt64.ofNat_add, UInt64.add_assoc]

theorem SpineR.append {m : Mem} {off a b : Word} {xs ys : Array EIdx} (hx : SpineR m off a xs)
    (hy : SpineR m (off + a) b ys) (hspn : (m.arr64 SPN).size < 2 ^ 63) :
    SpineR m off (a + b) (xs ++ ys) := by
  have hxb := hx.bound
  have hyb := hy.bound
  have hoa : (off + a).toNat = off.toNat + a.toNat := by
    rw [UInt64.toNat_add]; simp; omega
  have hab : (a + b).toNat = a.toNat + b.toNat := by
    rw [UInt64.toNat_add]; simp; omega
  refine ⟨by simp [hx.size, hy.size, hab], by rw [hab]; omega, fun i hi => ?_, fun i hi => ?_⟩
  · rw [hab] at hi
    by_cases hia : i < a.toNat
    · exact hx.lt i hia
    · rw [word_add_split off a i (by omega)]
      exact hy.lt (i - a.toNat) (by omega)
  · simp only [Array.size_append, hx.size, hy.size] at hi
    by_cases hia : i < a.toNat
    · rw [Array.getElem_append_left (by rw [hx.size]; exact hia)]
      exact hx.get i (by rw [hx.size]; exact hia)
    · rw [Array.getElem_append_right (by rw [hx.size]; omega), word_add_split off a i (by omega)]
      have := hy.get (i - a.toNat) (by rw [hy.size]; omega)
      simpa [hx.size] using this

/-- Model of `eta_fab_args`. -/
def efaW (p : Prog) (k : Nat) (m : Mem) (T to tn major nF : Word) : Option (List Word × Mem) :=
  match callW p k "eta_projs" [T, major, nF] m with
  | none => none
  | some (r, m₁) => some ([to, tn + r.tail.headD 0], m₁)

theorem etaFabArgs_spec (p : Prog) (hp : p.lookup "eta_fab_args" = some etaFabArgsL) (k : Nat)
    (s₀ : St) (T to tn major nF : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (k + 1)) "eta_fab_args" [T, to, tn, major, nF]
    ⦃fun r s' => LocEq s' s₀ ∧ efaW p k s₀.mem T to tn major nF = some ([r.headD 0, r.tail.headD 0], s'.mem);
      ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, etaFabArgsL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p k "eta_projs"] <;>
  simp_all [efaW, Cmp.eval, BinOp.eval, LocEq, St.setLocs_cons, St.setLoc_loc, St.setLoc_mem,
    St.setLocs_nil, Locals.init_cons_zero, Locals.init_cons_succ, Sig.retVal, Sig.retOr]

theorem etaFabArgsE_run (T : NIdx) (targs : List EIdx) (major : EIdx) (nF : Nat) (a a₁ : AState)
    (ps : List EIdx) (h : (etaProjs T major nF).run a = .ok (ps, a₁)) :
    (etaFabArgsE T targs major nF).run a = .ok (targs ++ ps, a₁) := by
  simp only [etaFabArgsE, StateT.run_bind, h, except_ok_bind]; rfl

/-- **`eta_fab_args` refines `etaFabArgsE`.** Statement change: `CoreAfterG`. -/
@[refines ConRon.Arena.etaFabArgsE]
theorem etaFabArgs_refines (p : Prog) (hp : IotaProg' p) :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb T to tn major nF : Word) (targs : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → HW T → HW major → SpineR s₀.mem to tn targs →
    to + tn = spTop s₀.mem →
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "eta_fab_args" [T, to, tn, major, nF]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (etaFabArgsE (decI T) targs.toList (decE major) nF.toNat) a₀ ∧
      CoreAfterG dn s₀.mem s'.mem (AM.st (etaFabArgsE (decI T) targs.toList (decE major) nF.toNat) a₀)
        vis fe MM eb ∧
      ∃ xs, AM.res (etaFabArgsE (decI T) targs.toList (decE major) nF.toNat) a₀ = xs ∧
        SpineR s'.mem (r.headD 0) (r.tail.headD 0) xs.toArray; ⊤⦄ := by
  intro n s₀ a₀ dn vis fe MM eb T to tn major nF targs hS hT hmaj hsp htop
  cases n with
  | zero => exact invoke_zero_triple
  | succ n =>
  refine triple_post (etaFabArgs_spec p hp.etaFabArgs n s₀ T to tn major nF) fun r s' ⟨hloc, hW⟩ =>
    ⟨hloc, ?_⟩
  simp only [efaW] at hW
  rcases hc1 : callW p n "eta_projs" [T, major, nF] s₀.mem with _ | ⟨r₁, m₁⟩ <;>
    simp only [hc1, reduceCtorEq] at hW
  obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
  obtain ⟨t₁, ht₁, hloc1, hok, hca, hhead, htail, ys, hres, hys⟩ := triple_of_callW
    (etaProjs_refines p hp n ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe MM eb T major nF hS hT hmaj) hc1
  rw [ht₁] at hca hys
  obtain ⟨M₁, hS₁, hK₁, hSt₁⟩ := hca
  have hSt₁ : StackGrew s₀.mem m₁ := hSt₁
  have hspn := hS.spn
  have hsp₁ : SpineR m₁ to tn targs := by
    have hb := hsp.bound
    refine hsp.keep hSt₁.size hSt₁.below ?_ hspn
    have : (to + tn).toNat = to.toNat + tn.toNat := by
      rw [UInt64.toNat_add]; simp; omega
    rw [← this, htop]
    exact Nat.le_refl _
  have hr1 : r.headD 0 = to := by
    have := congrArg (fun l => l.headD 0) hr.symm; simpa using this
  have hr2 : r.tail.headD 0 = tn + r₁.tail.headD 0 := by
    have := congrArg (fun l => l.tail.headD 0) hr.symm; simpa using this
  have hys' : SpineR m₁ (to + tn) (r₁.tail.headD 0) ys.toArray := by
    have : r₁.headD 0 = to + tn := by rw [htop]; exact hhead
    rw [← this]; exact hys
  have happ := hsp₁.append hys' (by rw [hSt₁.size]; exact hspn)
  obtain ⟨hokF, hstF, hresF⟩ := AM.of_run_ok _ _ _ _
    (etaFabArgsE_run (decI T) targs.toList (decE major) nF.toNat a₀ _ ys
      (by simpa [etaProjs] using AM.run_of_ok _ _ hok |> fun h => by rw [hres] at h; exact h))
  refine ⟨hokF, ⟨M₁, ?_, hK₁, ?_⟩, targs.toList ++ ys, hresF, ?_⟩
  · rw [hstF, ← hm]; exact hS₁
  · rw [← hm]; exact hSt₁
  · rw [hr1, hr2, ← hm]
    have e : (targs.toList ++ ys).toArray = targs ++ ys.toArray := by
      apply Array.ext'
      simp
    rw [e]; simpa using happ

end L.Arena
