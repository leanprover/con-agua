import ConAgua.Arena.IndPartsSpec8
import ConAgua.Arena.IndPos2SpecC

/-!
# Refinements of `IndParts`, part 9 (lane `indproofs2`, helper `parts`): the groups

`ctorMember?`, `blockGroups` (with `block_groups_one`, the `filterM`, and `block_groups_go`, the
`mapM` over the members, both recursive). The relational lemmas compose the callees with `Sim`
(`IndSim.lean`); a stub's `RelAM` fact is a `Sim` (`partsSimStub`).
-/

set_option experimental.vcgen true
set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- A stub's twin-side fact as a `Sim`. -/
theorem partsSimStub {α : Type} {f : FnName} {args : List Word} {pre : Mem → AState → Prop} {op : AM α}
    {post : Mem → Mem → AState → List Word → α → Prop} (h : RelAM f args pre op post) {m : Mem}
    {a : AState} (hpre : pre m a) :
    Sim (stubM f m args) op a (fun r x m' a' => post m m' a' r x) :=
  fun r m' e => h m m' a r e hpre

/-! ## `ctor_member` -/

/-- `member_idx_at`'s model at every exec fuel. -/
def memWk : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, no, nl, lvls, e => memW n m no nl lvls e

theorem memberIdxAt_specK (p : Prog) (hv : p.lookup "e_view" = some eView)
    (hf : p.lookup "sl_find" = some slFind) (hp : p.lookup "member_idx_at" = some memberIdxAt)
    (n : Nat) (s₀ : St) (no nl lvls e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "member_idx_at" [no, nl, lvls, e]
    ⦃fun r s' => LocEq s' s₀ ∧ memWk n s₀.mem no nl lvls e = some (r, s'.mem); ⊤⦄ := by
  cases n with
  | zero => rw [invoke_eq _ hp]; simp only [callFn, memberIdxAt]; vcgen [exec] <;> grind
  | succ n => exact memberIdxAt_spec p hv hf hp n s₀ no nl lvls e

/-- After `member_idx_at`. -/
def ctmK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0, r.tail.headD 0], m)

/-- After `get_app_fn_f`. -/
def ctmK2 (n : Nat) (no nl lvls : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => ctmK3 (memWk n m no nl lvls (r.headD 0))

/-- After `strip_pis`. -/
def ctmK1 (n : Nat) (no nl lvls : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then some ([0, 0], m)
    else ctmK2 n no nl lvls (stubM "get_app_fn_f" m [CWF, r.tail.tail.tail.headD 0])

/-- **The model of `ctor_member`** (at exec fuel `n + 1`). -/
def ctmW (n : Nat) (m : Mem) (no nl lvls nP c : Word) : Option (List Word × Mem) :=
  if nP + rdW (m.arr64 IW) (c + 1) < nP then none
  else ctmK1 n no nl lvls (stubM "strip_pis" m [nP + rdW (m.arr64 IW) (c + 1),
    rdW (m.arr64 EREC) (rdW (m.arr64 IW) c + 3)])

section arms
variable (n : Nat) (m : Mem) (no nl lvls : Word) (r : List Word)
theorem ctmK1_none (h : r.headD 0 = 0) : ctmK1 n no nl lvls (some (r, m)) = some ([0, 0], m) := by
  simp only [ctmK1]; rw [if_pos h]
theorem ctmK1_some (h : r.headD 0 ≠ 0) : ctmK1 n no nl lvls (some (r, m)) =
    ctmK2 n no nl lvls (stubM "get_app_fn_f" m [CWF, r.tail.tail.tail.headD 0]) := by
  simp only [ctmK1]; exact if_neg (c := r.headD 0 = 0) h
theorem ctmK2_some : ctmK2 n no nl lvls (some (r, m)) = ctmK3 (memWk n m no nl lvls (r.headD 0)) := rfl
theorem ctmK3_some : ctmK3 (some (r, m)) = some ([r.headD 0, r.tail.headD 0], m) := rfl
end arms
attribute [ind_grind] ctmK1_none ctmK1_some ctmK2_some ctmK3_some

theorem ctorMember_spec (p : Prog) (hv : p.lookup "e_view" = some eView)
    (hf : p.lookup "sl_find" = some slFind) (hm : p.lookup "member_idx_at" = some memberIdxAt)
    (hp : p.lookup "ctor_member" = some ctorMember) (n : Nat) (s₀ : St) (no nl lvls nP c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "ctor_member" [no, nl, lvls, nP, c]
    ⦃fun r s' => LocEq s' s₀ ∧ ctmW n s₀.mem no nl lvls nP c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, ctorMember]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      stubM_spec p "strip_pis" n, stubM_spec p "get_app_fn_f" n,
      memberIdxAt_specK p hv hf hm n] <;>
    finish (gen := 20) [ctmW]

/-- `ctor_member`'s model at every exec fuel. -/
def ctmWk : Nat → Mem → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, no, nl, lvls, nP, c => ctmW n m no nl lvls nP c

theorem ctorMember_specK (p : Prog) (hv : p.lookup "e_view" = some eView)
    (hf : p.lookup "sl_find" = some slFind) (hm : p.lookup "member_idx_at" = some memberIdxAt)
    (hp : p.lookup "ctor_member" = some ctorMember) (n : Nat) (s₀ : St) (no nl lvls nP c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ctor_member" [no, nl, lvls, nP, c]
    ⦃fun r s' => LocEq s' s₀ ∧ ctmWk n s₀.mem no nl lvls nP c = some (r, s'.mem); ⊤⦄ := by
  cases n with
  | zero => rw [invoke_eq _ hp]; simp only [callFn, ctorMember]; vcgen [exec] <;> grind
  | succ n => exact ctorMember_spec p hv hf hm hp n s₀ no nl lvls nP c

/-! ## Reading decoded records' words -/

/-- A number of the pool decoded below the top: the word L reads there, below the top. -/
theorem partsIwRd {m : Mem} {i v : Nat} (h : iwN (truncM m) i = some v) {w : Word} (hw : w.toNat = i) :
    rdW (m.arr64 IW) w = UInt64.ofNat v ∧ v < 2 ^ 64 ∧ i < iwTop m := by
  simp only [iwN, nat?, Option.map_eq_some_iff] at h
  obtain ⟨x, hx, rfl⟩ := h
  obtain ⟨hi, hx'⟩ := truncM_iw_get hx
  simp only [iwA] at hx'
  refine ⟨?_, x.toNat_lt, hi⟩
  rw [rdW_of_get? hw.symm hx']; simp

theorem partsIwLt {m : Mem} {i v : Nat} (h : iwN (truncM m) i = some v) : i < iwTop m := by
  simp only [iwN, nat?, Option.map_eq_some_iff] at h
  obtain ⟨x, hx, -⟩ := h
  exact (truncM_iw_get hx).1

/-- The type handle of a constant decoded below the top. -/
theorem partsCVType {m : Mem} {q : Nat} {cv : IConstantVal} (h : decCVp (truncM m) q = some cv)
    {w : Word} (hw : w.toNat = q) :
    (rdW (m.arr64 EREC) (w + 3)).toNat < 2 ^ 32 ∧ decI (rdW (m.arr64 EREC) (w + 3)) = cv.type := by
  obtain ⟨x, hx, hxl, hxe⟩ := hd?_some (decCV_type h)
  obtain ⟨hi, hx'⟩ := truncM_er_get hx
  simp only [erA] at hx'
  have hE : erTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 129).toNat_lt
  have hw3 : (w + 3).toNat = q + 3 := by rw [UInt64.toNat_add]; simp; omega
  rw [rdW_of_get? hw3.symm hx']
  exact ⟨hxl, hxe.symm⟩

/-- A word sum that does not wrap. -/
theorem partsAddNoOv {a b : Word} (h : ¬ a + b < a) : (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at h
  have := b.toNat_lt; have := a.toNat_lt
  rw [UInt64.toNat_add]; omega

theorem partsDrop3 (r : List Word) : (r.drop 3).headD 0 = r.tail.tail.tail.headD 0 := by
  rcases r with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl

/-- **`ctor_member`'s model refines `ctorMember?`**: the constructor `[cv, nF]` decoded below the
tops at `c`, the member names a handle slice below the top. -/
theorem ctmW_sim {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat) {m : Mem}
    {a : AState} {no nl lvls nP c : Word} {cv : IConstantVal} {nF : Nat} {names : List NIdx}
    (hS : StageR dn vis fe m a) (hc : DecB (fun m => decCN m c.toNat) m (cv, nF))
    (hnm : DecB (fun m => decHL m no.toNat nl.toNat) m names) (hnb : no.toNat + nl.toNat ≤ iwTop m)
    (hlv : H lvls) :
    Sim (ctmW n m no nl lvls nP c) (ConRon.Arena.ctorMember? names (decI lvls) nP.toNat (cv, nF)) a
      (fun r o m' a' => MemIdxOut r o ∧ StageR dn vis fe m' a' ∧ IWGrow m m') := by
  obtain ⟨⟨cvp, hcvp, hcv⟩, hnF⟩ := decCN_some (show decCN (truncM m) c.toNat = some (cv, nF) from hc)
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨hcw, -, -⟩ := partsIwRd hcvp rfl
  have hc1lt := partsIwLt hnF
  have hc1 : (c + 1).toNat = c.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  obtain ⟨hnFw, hnFb, -⟩ := partsIwRd hnF hc1
  have hcvp64 : (UInt64.ofNat cvp).toNat = cvp := by
    have := (partsIwRd hcvp rfl).2.1; exact UInt64.toNat_ofNat_of_lt' this
  obtain ⟨htyl, htye⟩ := partsCVType hcv hcvp64
  intro r m' hmo
  unfold ctmW at hmo
  rw [hcw, hnFw] at hmo
  split at hmo
  · cases hmo
  rename_i hov
  have hk : (nP + UInt64.ofNat nF).toNat = nP.toNat + nF := by
    rw [partsAddNoOv hov, UInt64.toNat_ofNat_of_lt' hnFb]
  revert r m'
  show Sim _ _ a _
  have h1 := partsSimStub (stripPis_spec dn vis fe (nP + UInt64.ofNat nF)
    (rdW (m.arr64 EREC) (UInt64.ofNat cvp + 3)) htyl) hS
  rw [hk, htye] at h1
  refine Sim.bindK (body := fun r m1 => if r.headD 0 = 0 then some ([0, 0], m1)
      else ctmK2 n no nl lvls (stubM "get_app_fn_f" m1 [CWF, r.tail.tail.tail.headD 0]))
    rfl (fun _ _ => rfl) h1 ?_
  rintro r1 x1 m1 a1 ⟨hS1, hg1, hd1⟩
  cases x1 with
  | none =>
    have h0 : r1.headD 0 = 0 := hd1
    simp only [h0, if_true]
    exact Sim.ret ⟨rfl, hS1, hg1⟩
  | some q =>
    obtain ⟨l1, e1⟩ := q
    obtain ⟨h1', -, hbl, hbe⟩ := hd1
    rw [partsDrop3] at hbl hbe
    simp only [h1', show (1 : Word) ≠ 0 by decide, if_false]
    have h2 := partsSimStub (getAppFn_spec dn vis fe CWF _ hbl) hS1
    rw [CWF_eq, hbe] at h2
    show Sim (ctmK2 n no nl lvls _) (getAppFn coreWalkFuel e1 >>= fun hd =>
      ConRon.Arena.memberIdxAt? names (decI lvls) hd) a1 _
    refine Sim.bindK (K := ctmK2 n no nl lvls) (g := fun hd =>
      ConRon.Arena.memberIdxAt? names (decI lvls) hd)
      (body := fun r m2 => ctmK3 (memWk n m2 no nl lvls (r.headD 0))) rfl (fun _ _ => rfl) h2 ?_
    rintro r2 x2 m2 a2 ⟨hS2, hg2, hl2, he2⟩
    have hnames2 : decHL m2 no.toNat nl.toNat = some names :=
      hnm.stab (OMono.decHL _ _) m2 (hg1.trans hg2)
    have hb : no.toNat + nl.toNat < 2 ^ 64 := by omega
    obtain ⟨ws, hws, hnm', hwlt⟩ := slR_of_decHL m2 nl.toNat no.toNat names hnames2 hb
    rw [ofNat_toNat_word, ofNat_toNat_word] at hws
    have hlen : ws.length < 2 ^ 64 := by
      have := decHL_length m2 hnames2; rw [hnm'] at this; simp at this; omega
    refine Sim.congr (op := ConRon.Arena.memberIdxAt? names (decI lvls) x2 >>= pure) ?_ (bind_pure _)
    refine Sim.bindK (body := fun r m3 => some ([r.headD 0, r.tail.headD 0], m3)) rfl (fun _ _ => rfl)
      (Q := fun r o m3 a3 => m3 = m2 ∧ a3 = a2 ∧ MemIdxOut r o) ?_ ?_
    · intro r3 m3 e3
      cases n with
      | zero => cases e3
      | succ n =>
      obtain ⟨hm3, o, hrun, hout⟩ := memW_ok n m2 m3 a2 no nl lvls (r2.headD 0) r3 ws hS2.1.arena.1 hl2
        hlv hws hwlt hlen e3
      refine ⟨o, a2, ?_, hm3, rfl, hout⟩
      rw [hnm', ← he2]; exact hrun
    · rintro r3 o m3 a3 ⟨rfl, rfl, hout⟩
      refine Sim.ret ⟨?_, hS2, hg1.trans hg2⟩
      cases o <;> simp only [MemIdxOut] at hout ⊢ <;> subst hout <;> rfl

end L.Ind
