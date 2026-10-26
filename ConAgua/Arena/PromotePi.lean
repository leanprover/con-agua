import ConAgua.Arena.PromoteMemo
import ConAgua.Arena.PromoteFlag
import ConAgua.Arena.WhnfBase
import ConAgua.Arena.PromoteCopy

/-!
# The persistent interners `pi_*`: the flag bracket

Each `pi_X(args)` is `sc := CTL[1]; CTL[1] := 0; r := X(args); CTL[1] := sc; return r`. Its
model `piW p n X args m` runs the callee through `callW` (`WhnfBase.lean`) on the memory with
the flag cleared and puts the flag back; the specs are one `vcgen` each. The relational lemmas
(`pi*_rel`) combine the callee's own refinement at the cleared flags (`ArenaD.flag`) with
`PromoteTwin.lean`'s equation `internPersistentX = internX` at those flags.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- A run of a callee meets its spec (`WhnfCoreRefine.lean`'s `triple_of_callW`, restated here
to keep this file's imports below the whnf family). -/
theorem callW_triple {p : Prog} {n : Nat} {f : FnName} {args : List Word} {s₀ : St}
    {Q : List Word → St → Prop}
    (h : ⦃fun s => s = s₀⦄ invoke p (exec p n) f args ⦃fun r s' => Q r s'; ⊤⦄)
    {r : List Word} {m' : Mem} (hc : callW p n f args s₀.mem = some (r, m')) :
    ∃ s', s'.mem = m' ∧ Q r s' := by
  simp only [callW] at hc
  cases hr : (invoke p (exec p n) f args).run { mem := s₀.mem, loc := Locals.init [] } with
  | error e => simp [hr] at hc
  | ok q =>
    simp only [hr, Option.some.injEq] at hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hc
    have hrun : (invoke p (exec p n) f args).run s₀ = .ok (q.1, { q.2 with loc := s₀.loc }) := by
      rw [invoke_run_loc, hr]; rfl
    exact ⟨{ q.2 with loc := s₀.loc }, rfl, L.M.of_run (P := fun s => s = s₀) rfl hrun h⟩

/-- A run at L fuel `0` fails (`WhnfCoreSlot.lean`'s `callW_zero`, restated for the same reason). -/
theorem callW_zero' (p : Prog) (f : FnName) (vs : List Word) (m : Mem) : callW p 0 f vs m = none := by
  simp only [callW, invoke, lookupFn]
  cases p.lookup f with
  | none => rfl
  | some fd => rfl

/-! ## The model -/

/-- After the callee: put the flag word `sc` back. -/
def piK (sc : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m₁) => if (m₁.arr64 CTL).size ≤ 1 then none else some (r.headD 0, m₁.set64 CTL 1 sc)

/-- **The model of `pi_X(args)`**: the callee `f` run with the flag `CTL[1]` cleared, the flag
put back. -/
def piW (p : Prog) (n : Nat) (f : FnName) (args : List Word) (m : Mem) : Option (Word × Mem) :=
  if (m.arr64 CTL).size ≤ 1 then none
  else piK (rdW (m.arr64 CTL) 1) (callW p n f args (m.set64 CTL 1 0))

theorem piW_eq (p : Prog) (n : Nat) (f : FnName) (args : List Word) (m : Mem)
    (h : 1 < (m.arr64 CTL).size) :
    piW p n f args m = piK (rdW (m.arr64 CTL) 1) (callW p n f args (m.set64 CTL 1 0)) := by
  unfold piW; simp [Nat.not_le.mpr h]

theorem piK_some (sc : Word) (r : List Word) (m₁ : Mem) (h : 1 < (m₁.arr64 CTL).size) :
    piK sc (some (r, m₁)) = some (r.headD 0, m₁.set64 CTL 1 sc) := by
  simp [piK, Nat.not_le.mpr h]

/-- **The flag bracket's frame**: the callee's frame, the flag `CTL[1]` put back. -/
theorem frame_pi {A : List ArrId} {C : List Word} {m m₁ : Mem} (hc : 1 < (m.arr64 CTL).size)
    (hf : MemFrame A C (m.set64 CTL 1 0) m₁) :
    MemFrame A C m (m₁.set64 CTL 1 (rdW (m.arr64 CTL) 1)) := by
  have F := (((MemFrame.setCtl m 1 0).mono (A' := A) (C' := 1 :: C) (by simp) (by simp)).trans
    (hf.mono (fun _ hb => hb) (fun _ hx => List.mem_cons_of_mem _ hx))).trans
    ((MemFrame.setCtl m₁ 1 (rdW (m.arr64 CTL) 1)).mono (by simp) (by simp))
  have hs₁ : 1 < (m₁.arr64 CTL).size := by rw [hf.2.2.1]; simpa [size_set64] using hc
  refine ⟨F.1, fun x hx => ?_, F.2.2⟩
  by_cases h1 : x = 1
  · subst h1; rw [rdW_set64]; simp [hs₁]
  · exact F.2.1 x (by simp [h1, hx])

/-- **The model of a slice-taking `pi_X(pre, o, l)`** (lane tierpool): a tier-1 slice is first
copied to tier 0 (`pool_copy0`), then `piW` on the copy. -/
def pcW (p : Prog) (n : Nat) (f : FnName) (pre : List Word) (o l : Word) (m : Mem) :
    Option (Word × Mem) :=
  if o >>> 40 = 0 then piW p n f (pre ++ [o, l]) m
  else if Alloc0OK m l then piW p n f (pre ++ [alloc0Q m, l]) (cp0W (alloc0Mem m l) (alloc0Q m) o l 0)
  else none

/-! ## The specs -/

/-- `pool_copy0`'s run, as a model fact. -/
theorem callW_copy0 {p : Prog} (hc : p.lookup "pool_copy0" = some poolCopy0)
    (ha : p.lookup "pool_alloc0" = some poolAlloc0) {n : Nat} {o l : Word} {m : Mem} {rs : List Word}
    {m' : Mem} (h : callW p n "pool_copy0" [o, l] m = some (rs, m')) :
    Alloc0OK m l ∧ rs = [alloc0Q m] ∧ m' = cp0W (alloc0Mem m l) (alloc0Q m) o l 0 := by
  obtain ⟨s', rfl, -, h1, h2, h3⟩ := callW_triple (poolCopy0_spec' p hc ha n ⟨m, Locals.init []⟩ o l) h
  exact ⟨h1, h2, h3⟩

theorem init_l0 (a : Word) (r : List Word) : Locals.init (a :: r) 0 = a := rfl
theorem init_l1 (a b : Word) (r : List Word) : Locals.init (a :: b :: r) 1 = b := rfl
theorem init_l2 (a b c : Word) (r : List Word) : Locals.init (a :: b :: c :: r) 2 = c := rfl

section specs
variable (p : Prog) (hp : PromoteProg p) (n : Nat) (s₀ : St)
include hp

set_option hygiene false in
/-- One `pi_*` spec: the flag word read and written around the callee's run. -/
local macro "pi_spec " fn:term : tactic => `(tactic| (
  have hcp := fun {n o l m rs m'} => @callW_copy0 p (hp.get "pool_copy0") (hp.get "pool_alloc0") n o l m rs m'
  rw [invoke_eq _ $fn]
  simp only [callFn, piBVar, piFVar, piSort, piConst, piApp, piLam, piForall, piLet, piLit,
    piLitStr, piProj, piNAnon, piNStr, piNNum, piZero, piSucc, piMax, piImax, piParam, piLs]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, callW_spec] <;>
    finish [piW_eq, piK_some, pcW, init_l0, init_l1, init_l2, List.cons_append, List.nil_append]))

theorem piNStr_spec (q o l : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pi_nstr" [q, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ pcW p n "intern_nstr" [q] o l s₀.mem = some (r.headD 0, s'.mem);
      ⊤⦄ := by pi_spec (hp.get "pi_nstr")

theorem piBVar_spec (i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pi_bvar" [i]
    ⦃fun r s' => LocEq s' s₀ ∧ piW p n "intern_bvar" [i] s₀.mem = some (r.headD 0, s'.mem);
      ⊤⦄ := by pi_spec (hp.get "pi_bvar")

theorem piFVar_spec (i ty : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pi_fvar" [i, ty]
    ⦃fun r s' => LocEq s' s₀ ∧ piW p n "intern_fvar" [i, ty] s₀.mem = some (r.headD 0, s'.mem);
      ⊤⦄ := by pi_spec (hp.get "pi_fvar")

theorem piSort_spec (u : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pi_sort" [u]
    ⦃fun r s' => LocEq s' s₀ ∧ piW p n "intern_sort" [u] s₀.mem = some (r.headD 0, s'.mem);
      ⊤⦄ := by pi_spec (hp.get "pi_sort")

theorem piConst_spec (x us : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pi_const" [x, us]
    ⦃fun r s' => LocEq s' s₀ ∧ piW p n "intern_const" [x, us] s₀.mem = some (r.headD 0, s'.mem);
      ⊤⦄ := by pi_spec (hp.get "pi_const")

theorem piApp_spec (f x : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pi_app" [f, x]
    ⦃fun r s' => LocEq s' s₀ ∧ piW p n "mk_app" [f, x] s₀.mem = some (r.headD 0, s'.mem);
      ⊤⦄ := by pi_spec (hp.get "pi_app")

theorem piLam_spec (t b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pi_lam" [t, b]
    ⦃fun r s' => LocEq s' s₀ ∧ piW p n "mk_lam" [t, b] s₀.mem = some (r.headD 0, s'.mem);
      ⊤⦄ := by pi_spec (hp.get "pi_lam")

theorem piForall_spec (t b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pi_forall" [t, b]
    ⦃fun r s' => LocEq s' s₀ ∧ piW p n "mk_forall" [t, b] s₀.mem = some (r.headD 0, s'.mem);
      ⊤⦄ := by pi_spec (hp.get "pi_forall")

theorem piLet_spec (t v b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pi_let" [t, v, b]
    ⦃fun r s' => LocEq s' s₀ ∧ piW p n "mk_let" [t, v, b] s₀.mem = some (r.headD 0, s'.mem);
      ⊤⦄ := by pi_spec (hp.get "pi_let")

theorem piLit_spec (o l : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pi_lit" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ pcW p n "intern_lit" [] o l s₀.mem = some (r.headD 0, s'.mem);
      ⊤⦄ := by pi_spec (hp.get "pi_lit")

theorem piLitStr_spec (o l : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pi_lit_str" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ pcW p n "intern_lit_str" [] o l s₀.mem = some (r.headD 0, s'.mem);
      ⊤⦄ := by pi_spec (hp.get "pi_lit_str")

theorem piProj_spec (x i e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pi_proj" [x, i, e]
    ⦃fun r s' => LocEq s' s₀ ∧ piW p n "mk_proj" [x, i, e] s₀.mem = some (r.headD 0, s'.mem);
      ⊤⦄ := by pi_spec (hp.get "pi_proj")

theorem piNAnon_spec :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pi_nanon" []
    ⦃fun r s' => LocEq s' s₀ ∧ piW p n "intern_nanon" [] s₀.mem = some (r.headD 0, s'.mem);
      ⊤⦄ := by pi_spec (hp.get "pi_nanon")

theorem piNNum_spec (q u : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pi_nnum" [q, u]
    ⦃fun r s' => LocEq s' s₀ ∧ piW p n "intern_nnum" [q, u] s₀.mem = some (r.headD 0, s'.mem);
      ⊤⦄ := by pi_spec (hp.get "pi_nnum")

theorem piZero_spec :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pi_zero" []
    ⦃fun r s' => LocEq s' s₀ ∧ piW p n "intern_zero" [] s₀.mem = some (r.headD 0, s'.mem);
      ⊤⦄ := by pi_spec (hp.get "pi_zero")

theorem piSucc_spec (u : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pi_succ" [u]
    ⦃fun r s' => LocEq s' s₀ ∧ piW p n "intern_succ" [u] s₀.mem = some (r.headD 0, s'.mem);
      ⊤⦄ := by pi_spec (hp.get "pi_succ")

theorem piMax_spec (u v : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pi_max" [u, v]
    ⦃fun r s' => LocEq s' s₀ ∧ piW p n "intern_max" [u, v] s₀.mem = some (r.headD 0, s'.mem);
      ⊤⦄ := by pi_spec (hp.get "pi_max")

theorem piImax_spec (u v : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pi_imax" [u, v]
    ⦃fun r s' => LocEq s' s₀ ∧ piW p n "intern_imax" [u, v] s₀.mem = some (r.headD 0, s'.mem);
      ⊤⦄ := by pi_spec (hp.get "pi_imax")

theorem piParam_spec (x : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pi_param" [x]
    ⦃fun r s' => LocEq s' s₀ ∧ piW p n "intern_param" [x] s₀.mem = some (r.headD 0, s'.mem);
      ⊤⦄ := by pi_spec (hp.get "pi_param")

theorem piLs_spec (o l : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pi_ls" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ pcW p n "intern_ls" [] o l s₀.mem = some (r.headD 0, s'.mem);
      ⊤⦄ := by pi_spec (hp.get "pi_ls")

end specs

/-! ## The relation across the bracket -/

theorem ctl_size {m : Mem} {a : AState} (hR : ArenaR m a) : 1 < (m.arr64 CTL).size := by
  have := ConsR.ctl hR.app; simp [appCS, appSch] at this; omega

/-- **The bracket around a hash-consing over a lens** (names, levels, level lists): from the
callee's facts at the cleared flags (`hrun`, `hok`, `hR₁`, `hres`, the frame `hf`) and the
twin's equation `heq`, the persistent interning `opP` succeeds at `a` with the flags put back,
and the relation holds after the flag word is restored. -/
theorem pi_lens {β δ : Type} {k : IdxKind} [BEq β] [Hashable β] {L : Lens β δ k}
    {op opP : AM (Idx k)} {key : β} {tag : UInt32} {pf : Option (Idx k)} {d : δ}
    {err : CheckError} {A : List ArrId} {C : List Word} {m m₁ : Mem} {a : AState} {r : Word}
    (hD : ArenaD m a) (hrun : op.run (onA false a) = protoRun L key tag pf d err (onA false a))
    (hok : AM.ok op (onA false a)) (hR₁ : ArenaR m₁ (AM.st op (onA false a)))
    (hres : AM.res op (onA false a) = decI r) (hf : MemFrame A C (m.set64 CTL 1 0) m₁)
    (hA : ∀ b ∈ A, (b < 42 ∨ 46 < b) ∧ (b < 298 ∨ 302 < b))
    (hset : ∀ t, (L.setP (onA false a) t).store.pers = a.store.pers ∧
      (L.setP (onA false a) t).store.scr = a.store.scr ∧ cp (L.setP (onA false a) t) = cp a)
    (hsetS : ∀ t, (L.setS (onA false a) t).store.pers = a.store.pers ∧
      (L.setS (onA false a) t).store.scr = a.store.scr ∧ cp (L.setS (onA false a) t) = cp a)
    (heq : opP.run a = (op.run (onA false a)).map (fun r => (r.1, onA a.store.scratchOn r.2))) :
    ∃ a', opP.run a = .ok (decI r, a') ∧
      ArenaD (m₁.set64 CTL 1 (rdW (m.arr64 CTL) 1)) a' ∧ cp a' = cp a := by
  have hcs := AM.st_proto L op key tag pf d err (onA false a) hrun hok
  have hk : (AM.st op (onA false a)).store.pers = a.store.pers ∧
      (AM.st op (onA false a)).store.scr = a.store.scr ∧ cp (AM.st op (onA false a)) = cp a := by
    rcases hcs with h | ⟨t, h⟩ | ⟨t, h⟩ <;> rw [h]
    · exact ⟨rfl, rfl, rfl⟩
    · exact hset t
    · exact hsetS t
  have hD₁ : DerR m₁ (AM.st op (onA false a)) := by
    have h0 : DerR (m.set64 CTL 1 0) a := hD.2.setCtl 1 0
    have h1 : DerR m₁ a := DerR.frameM _ _ _ m₁ hf hA a h0
    exact ⟨by simp only [DerT2, hk.1, hk.2.1]; exact h1.bvar,
      by simp only [DerT2, hk.1, hk.2.1]; exact h1.fvar,
      by simp only [DerT2, hk.1, hk.2.1]; exact h1.sort,
      by simp only [DerT2, hk.1, hk.2.1]; exact h1.const,
      by simp only [DerT2, hk.1, hk.2.1]; exact h1.lit,
      by simp only [DerT2, hk.1, hk.2.1]; exact h1.app,
      by simp only [DerT2, hk.1, hk.2.1]; exact h1.lam,
      by simp only [DerT2, hk.1, hk.2.1]; exact h1.forallE,
      by simp only [DerT2, hk.1, hk.2.1]; exact h1.letE,
      by simp only [DerT2, hk.1, hk.2.1]; exact h1.proj⟩
  have hfl : (rdW (m.arr64 CTL) 1 != 0) = a.store.scratchOn := hD.1.flag_eq
  refine ⟨onA a.store.scratchOn (AM.st op (onA false a)), ?_, ?_, ?_⟩
  · rw [heq, AM.run_of_ok op _ hok, hres]; rfl
  · have h2 := (ArenaD.flag ⟨hR₁, hD₁⟩ (rdW (m.arr64 CTL) 1))
    rw [hfl] at h2; exact h2
  · exact hk.2.2

/-- The flag word cleared: the relation at the cleared flags. -/
theorem ArenaR.off {m : Mem} {a : AState} (hR : ArenaR m a) : ArenaR (m.set64 CTL 1 0) (onA false a) :=
  hR.flag 0

/-! ## A slice-taking `pi_X` reduced to `piW` on a tier-0 slice (lane tierpool) -/

/-- **`pcW` is `piW` on a tier-0 slice in use holding the same words**: the slice itself when it
is in tier 0, else its copy (`copy0_facts`), across a `Grow0` that keeps the arena. -/
theorem pc_cases {p : Prog} {n : Nat} {f : FnName} {pre : List Word} {o l r : Word} {m m' : Mem}
    {a : AState} (hD : ArenaD m a) (hs : SliceOK m o l)
    (h : pcW p n f pre o l m = some (r, m')) :
    ∃ m₁ o₁, piW p n f (pre ++ [o₁, l]) m₁ = some (r, m') ∧ ArenaD m₁ a ∧ SliceOK m₁ o₁ l ∧
      o₁.toNat < 2 ^ 40 ∧ MemFrame [POOL, PT0] [] m m₁ ∧ m₁.flag = m.flag ∧
      (∀ k < l.toNat, (vpool m₁)[o₁.toNat + k]?.getD 0 = (vpool m)[o.toNat + k]?.getD 0) ∧
      SlKeep m m₁ := by
  unfold pcW at h
  by_cases ho : o >>> 40 = 0
  · rw [if_pos ho] at h
    exact ⟨m, o, h, hD, hs, (tier0_iff' o).mp ho, MemFrame.refl _ _ _, rfl, fun _ _ => rfl,
      SlKeep.refl m⟩
  · rw [if_neg ho] at h
    by_cases hA : Alloc0OK m l
    · rw [if_pos hA] at h
      have hp := hD.1.lit.1
      have ho1 : 2 ^ 40 ≤ o.toNat := Nat.le_of_not_lt (fun hc => ho ((tier0_iff' _).mpr hc))
      have ht : m.top >>> 40 ≠ 0 := fun h0 => by
        have := (tier0_iff' _).mp h0; have := hs.1; omega
      obtain ⟨hq, hg, hs₁, hq40, hv, -, hfl, -⟩ := copy0_facts m o l hp ht hs ho1 hA
      rw [hq] at h
      exact ⟨_, _, h, ArenaD.grow0 hg hD, hs₁, hq40, hg.frame, hfl, hv, hg.slKeep hp⟩
    · rw [if_neg hA] at h; cases h

section names
variable (p : Prog) (hp : PromoteProg p) (n : Nat)
include hp

/-- **`pi_nanon` refines `internPersistentN .anonymous`.** -/
theorem piNAnon_rel (m : Mem) (a : AState) (hD : ArenaD m a) (r : Word) (m' : Mem)
    (h : piW p n "intern_nanon" [] m = some (r, m')) :
    ∃ a', (internPersistentN .anonymous).run a = .ok (decI r, a') ∧ ArenaD m' a' ∧ PW r ∧
      cp a' = cp a ∧ MemFrame [NAREC, NAREC + 256, NASLOT, NASLOT + 256] [34, 35] m m' := by
  have hc := ctl_size hD.1
  rw [piW_eq _ _ _ _ _ hc] at h
  cases hcall : callW p n "intern_nanon" [] (m.set64 CTL 1 0) with
  | none => rw [hcall] at h; cases h
  | some q =>
  obtain ⟨rr, m₁⟩ := q
  rw [hcall] at h
  obtain ⟨s', rfl, -, hI⟩ := callW_triple (internNAnon_spec p (hp.get "nanon_find") (hp.get "nanon_push")
    (hp.get "intern_nanon") n ⟨m.set64 CTL 1 0, Locals.init []⟩) hcall
  have hR₀ := hD.1.off
  obtain ⟨hok, hX, hres⟩ := naintern_correct _ (onA false a) hR₀.nanon _ _ hI
  have hf := consInternM_frame nanonCS_wf hI
  have hR₁ := hR₀.lift_nanon _ _ _ _ hX hf
    (AM.st_proto nanonLens _ _ _ _ _ _ _ (internNNode_anon_run _) hok)
  have hpw := consInternM_pw nanonCS_wf hR₀.nanon (by rw [rdW_set64]; simp [hc]) hI
  have hsz : 1 < (s'.mem.arr64 CTL).size := by rw [hf.2.2.1]; simpa [size_set64] using hc
  rw [piK_some _ _ _ hsz] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨a', h1, h2, h3⟩ := pi_lens hD (internNNode_anon_run _) hok hR₁ hres hf
    (by simp [ConsSch.wset, nanonCS, nanonSch, NAREC, NASLOT]) (fun _ => ⟨rfl, rfl, rfl⟩) (fun _ => ⟨rfl, rfl, rfl⟩)
    (internPersistentN_eq _ a hD.1.flagsEq trivial)
  refine ⟨a', h1, h2, hpw, h3, ?_⟩
  exact (frame_pi hc (hf.mono (by simp [ConsSch.wset, nanonCS, nanonSch]) (by simp [ConsSch.wset, nanonCS, nanonSch])))

/-- **`pi_nnum` refines `internPersistentN (.num _ _)`.** -/
theorem piNNum_rel (m : Mem) (a : AState) (hD : ArenaD m a) (q u : Word) (hq : PW q) (r : Word)
    (m' : Mem) (h : piW p n "intern_nnum" [q, u] m = some (r, m')) :
    ∃ a', (internPersistentN (.num (decI q) u.toNat)).run a = .ok (decI r, a') ∧ ArenaD m' a' ∧
      PW r ∧ cp a' = cp a ∧ MemFrame [NNREC, NNREC + 256, NNSLOT, NNSLOT + 256] [38, 39] m m' := by
  have hc := ctl_size hD.1
  rw [piW_eq _ _ _ _ _ hc] at h
  cases hcall : callW p n "intern_nnum" [q, u] (m.set64 CTL 1 0) with
  | none => rw [hcall] at h; cases h
  | some x =>
  obtain ⟨rr, m₁⟩ := x
  rw [hcall] at h
  obtain ⟨s', rfl, -, hI⟩ := callW_triple (internNNum_spec p (hp.get "nnum_find") (hp.get "nnum_push")
    (hp.get "intern_nnum") n ⟨m.set64 CTL 1 0, Locals.init []⟩ q u) hcall
  have hR₀ := hD.1.off
  obtain ⟨hok, hX, hres⟩ := nnintern_correct _ (onA false a) hR₀.nnum q u hq.1 _ _ hI
  have hf := consInternM_frame nnumCS_wf hI
  have hR₁ := hR₀.lift_nnum _ _ _ _ hX hf
    (AM.st_proto nnumLens _ _ _ _ _ _ _ (internNNode_num_run _ _ _) hok)
  have hpw := consInternM_pw nnumCS_wf hR₀.nnum (by rw [rdW_set64]; simp [hc]) hI
  have hsz : 1 < (s'.mem.arr64 CTL).size := by rw [hf.2.2.1]; simpa [size_set64] using hc
  rw [piK_some _ _ _ hsz] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨a', h1, h2, h3⟩ := pi_lens hD (internNNode_num_run _ _ _) hok hR₁ hres hf
    (by simp [ConsSch.wset, nnumCS, nnumSch, NNREC, NNSLOT]) (fun _ => ⟨rfl, rfl, rfl⟩) (fun _ => ⟨rfl, rfl, rfl⟩)
    (internPersistentN_eq _ a hD.1.flagsEq hq.pers)
  refine ⟨a', h1, h2, hpw, h3, ?_⟩
  exact (frame_pi hc (hf.mono (by simp [ConsSch.wset, nnumCS, nnumSch]) (by simp [ConsSch.wset, nnumCS, nnumSch])))

/-- **`pi_nstr` refines `internPersistentN (.str _ s)`**, `s` the string the pool slice holds. -/
theorem piNStr_rel0 (m : Mem) (a : AState) (hD : ArenaD m a) (q o l : Word) (hq : PW q)
    (hsl : SliceOK m o l) (ho : o.toNat < 2 ^ 40) (s : String)
    (hk : sliceL (vpool m) o.toNat l.toNat = strWords s)
    (r : Word) (m' : Mem) (h : piW p n "intern_nstr" [q, o, l] m = some (r, m')) :
    ∃ a', (internPersistentN (.str (decI q) s)).run a = .ok (decI r, a') ∧ ArenaD m' a' ∧
      PW r ∧ cp a' = cp a ∧ MemFrame [NSREC, NSREC + 256, NSSLOT, NSSLOT + 256] [36, 37] m m' := by
  have hc := ctl_size hD.1
  rw [piW_eq _ _ _ _ _ hc] at h
  cases hcall : callW p n "intern_nstr" [q, o, l] (m.set64 CTL 1 0) with
  | none => rw [hcall] at h; cases h
  | some x =>
  obtain ⟨rr, m₁⟩ := x
  rw [hcall] at h
  have hR₀ := hD.1.off
  have ⟨_, _, hps, htop⟩ := hR₀.lit.1
  have hpool : (m.set64 CTL 1 0).arr64 POOL = m.arr64 POOL :=
    Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have hpool1 : (m.set64 CTL 1 0).arr64 POOL1 = m.arr64 POOL1 :=
    Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have hpoolv := vpool_congr hpool hpool1
  have htop' : (m.set64 CTL 1 0).top = m.top := by simp only [top_rdW, rdW_set64]; simp
  have hsl₀ : SliceOK (m.set64 CTL 1 0) o l := by
    simp only [SliceOK, htop', Mem.ptop0_set64_ne m CTL 1 0 (by decide)] at hsl ⊢; exact hsl
  obtain ⟨s', rfl, -, hI⟩ := callW_triple (internNStr_spec p (hp.get "lit_hash") (hp.get "limbs_eq") (hp.get "nstr_match")
    (hp.get "nstr_find") (hp.get "nstr_push") (hp.get "intern_nstr") n ⟨m.set64 CTL 1 0, Locals.init []⟩ q o l
    (by dsimp only; omega) (by simp only [SliceOK] at hsl₀; dsimp only; omega)) hcall
  obtain ⟨hok, hX, hres⟩ := nsintern_correct _ (onA false a) hR₀.lit.1 hR₀.nstr q o l hq.1 hsl₀ s
    (by rw [hpoolv]; exact hk) (fun _ => ho) _ _ hI
  have hf := consInternM_frame nstrCS_wf hI
  have hR₁ := hR₀.lift_nstr _ _ _ _ hX hf
    (AM.st_proto nstrLens _ _ _ _ _ _ _ (internNNode_str_run _ _ _) hok)
  have hpw := consInternM_pw nstrCS_wf hR₀.nstr (by rw [rdW_set64]; simp [hc]) hI
  have hsz : 1 < (s'.mem.arr64 CTL).size := by rw [hf.2.2.1]; simpa [size_set64] using hc
  rw [piK_some _ _ _ hsz] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨a', h1, h2, h3⟩ := pi_lens hD (internNNode_str_run _ _ _) hok hR₁ hres hf
    (by simp [ConsSch.wset, nstrCS, nstrSch, NSREC, NSSLOT]) (fun _ => ⟨rfl, rfl, rfl⟩) (fun _ => ⟨rfl, rfl, rfl⟩)
    (internPersistentN_eq _ a hD.1.flagsEq hq.pers)
  refine ⟨a', h1, h2, hpw, h3, ?_⟩
  exact (frame_pi hc (hf.mono (by simp [ConsSch.wset, nstrCS, nstrSch]) (by simp [ConsSch.wset, nstrCS, nstrSch])))

/-- **`pi_nstr` refines `internPersistentN (.str _ s)`**, `s` the string the pool slice holds; a
tier-1 slice is first copied to tier 0 (lane tierpool). -/
theorem piNStr_rel (m : Mem) (a : AState) (hD : ArenaD m a) (q o l : Word) (hq : PW q)
    (hsl : SliceOK m o l) (s : String) (hk : sliceL (vpool m) o.toNat l.toNat = strWords s)
    (r : Word) (m' : Mem) (h : pcW p n "intern_nstr" [q] o l m = some (r, m')) :
    ∃ a', (internPersistentN (.str (decI q) s)).run a = .ok (decI r, a') ∧ ArenaD m' a' ∧
      PW r ∧ cp a' = cp a ∧
      MemFrame [POOL, PT0, NSREC, NSREC + 256, NSSLOT, NSSLOT + 256] [36, 37] m m' ∧
      SlKeep m m' := by
  obtain ⟨m₁, o₁, h₁, hD₁, hs₁, ho₁, hf₁, -, hv, hk₁⟩ := pc_cases hD hsl h
  obtain ⟨a', e1, e2, e3, e4, e5⟩ := piNStr_rel0 p hp n m₁ a hD₁ q o₁ l hq hs₁ ho₁ s
    (by rw [← hk]; exact (sliceL_eq_iff _ _ _ _ _).mpr hv) r m' h₁
  exact ⟨a', e1, e2, e3, e4, (hf₁.mono (by simp) (by simp)).trans (e5.mono (by simp) (by simp)),
    hk₁.trans (SlKeep.of_frame e5 (by decide) (by decide))⟩

end names

section levels
variable (p : Prog) (hp : PromoteProg p) (n : Nat)
include hp

/-- **`pi_zero` refines `internPersistentL .zero`.** -/
theorem piZero_rel (m : Mem) (a : AState) (hD : ArenaD m a) (r : Word) (m' : Mem)
    (h : piW p n "intern_zero" [] m = some (r, m')) :
    ∃ a', (internPersistentL .zero).run a = .ok (decI r, a') ∧ ArenaD m' a' ∧ PW r ∧
      cp a' = cp a ∧ MemFrame [ZREC, ZREC + 256, ZSLOT, ZSLOT + 256] [8, 9] m m' := by
  have hc := ctl_size hD.1
  rw [piW_eq _ _ _ _ _ hc] at h
  cases hcall : callW p n "intern_zero" [] (m.set64 CTL 1 0) with
  | none => rw [hcall] at h; cases h
  | some x =>
  obtain ⟨rr, m₁⟩ := x
  rw [hcall] at h
  obtain ⟨s', rfl, -, hI⟩ := callW_triple (internZero_spec p (hp.get "zero_find") (hp.get "zero_push")
    (hp.get "intern_zero") n ⟨m.set64 CTL 1 0, Locals.init []⟩) hcall
  have hR₀ := hD.1.off
  obtain ⟨hok, hX, hres⟩ := zintern_correct _ (onA false a) hR₀.zero _ _ hI
  have hL := zintern_hp _ (onA false a) hR₀.zero hR₀.zeroHp _ _ hI
  have hf := consInternM_frame zeroCS_wf hI
  have hR₁ := hR₀.lift_zero _ _ _ _ ⟨hX, hL⟩ hf
    (AM.st_proto zeroLens _ _ _ _ _ _ _ (internLNode_zero_run _) hok)
  have hpw := consInternM_pw zeroCS_wf hR₀.zero (by rw [rdW_set64]; simp [hc]) hI
  have hsz : 1 < (s'.mem.arr64 CTL).size := by rw [hf.2.2.1]; simpa [size_set64] using hc
  rw [piK_some _ _ _ hsz] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨a', h1, h2, h3⟩ := pi_lens hD (internLNode_zero_run _) hok hR₁ hres hf
    (by simp [ConsSch.wset, zeroCS, zeroSch, ZREC, ZSLOT]) (fun _ => ⟨rfl, rfl, rfl⟩) (fun _ => ⟨rfl, rfl, rfl⟩)
    (internPersistentL_eq _ a hD.1.flagsEq trivial)
  refine ⟨a', h1, h2, hpw, h3, ?_⟩
  exact (frame_pi hc (hf.mono (by simp [ConsSch.wset, zeroCS, zeroSch]) (by simp [ConsSch.wset, zeroCS, zeroSch])))

/-- **`pi_succ` refines `internPersistentL (.succ (decI u))`.** -/
theorem piSucc_rel (m : Mem) (a : AState) (hD : ArenaD m a) (u : Word) (hu : PW u) (r : Word) (m' : Mem)
    (h : piW p n "intern_succ" [u] m = some (r, m')) :
    ∃ a', (internPersistentL (.succ (decI u))).run a = .ok (decI r, a') ∧ ArenaD m' a' ∧ PW r ∧
      cp a' = cp a ∧ MemFrame [SREC, SREC + 256, SSLOT, SSLOT + 256, SHP, SHP + 256] [6, 7] m m' := by
  have hc := ctl_size hD.1
  rw [piW_eq _ _ _ _ _ hc] at h
  cases hcall : callW p n "intern_succ" [u] (m.set64 CTL 1 0) with
  | none => rw [hcall] at h; cases h
  | some x =>
  obtain ⟨rr, m₁⟩ := x
  rw [hcall] at h
  obtain ⟨s', rfl, -, hI⟩ := callW_triple (internSucc_spec p (hp.get "succ_find") (hp.get "succ_push")
    (hp.get "intern_succ") n ⟨m.set64 CTL 1 0, Locals.init []⟩ u) hcall
  have hR₀ := hD.1.off
  obtain ⟨hok, hX, hres⟩ := sintern_correct _ (onA false a) hR₀.succ u hu.1 _ _ hI
  have hL := sintern_hp _ (onA false a) hR₀.succ u hu.1 hR₀.succHp (lvlHPW_ok _ _ hR₀ u hu.1) _ _ hI
  have hf := sinternW_frame _ u _ _ hI
  have hR₁ := hR₀.lift_succ _ _ _ _ ⟨hX, hL⟩ hf
    (AM.st_proto succLens _ _ _ _ _ _ _ (internLNode_succ_run _ _) hok)
  have hpw := consInternM_pw succCS_wf hR₀.succ (by rw [rdW_set64]; simp [hc]) hI
  have hsz : 1 < (s'.mem.arr64 CTL).size := by rw [hf.2.2.1]; simpa [size_set64] using hc
  rw [piK_some _ _ _ hsz] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨a', h1, h2, h3⟩ := pi_lens hD (internLNode_succ_run _ _) hok hR₁ hres hf
    (by simp [SREC, SSLOT, SHP]) (fun _ => ⟨rfl, rfl, rfl⟩) (fun _ => ⟨rfl, rfl, rfl⟩)
    (internPersistentL_eq _ a hD.1.flagsEq hu.pers)
  refine ⟨a', h1, h2, hpw, h3, ?_⟩
  exact (frame_pi hc (hf.mono (by simp [ConsSch.wset, succSch]) (by simp [succSch])))

/-- **`pi_max` refines `internPersistentL (.max (decI u) (decI v))`.** -/
theorem piMax_rel (m : Mem) (a : AState) (hD : ArenaD m a) (u v : Word) (hu : PW u) (hv : PW v) (r : Word) (m' : Mem)
    (h : piW p n "intern_max" [u, v] m = some (r, m')) :
    ∃ a', (internPersistentL (.max (decI u) (decI v))).run a = .ok (decI r, a') ∧ ArenaD m' a' ∧ PW r ∧
      cp a' = cp a ∧ MemFrame [MREC, MREC + 256, MSLOT, MSLOT + 256, MHP, MHP + 256] [10, 11] m m' := by
  have hc := ctl_size hD.1
  rw [piW_eq _ _ _ _ _ hc] at h
  cases hcall : callW p n "intern_max" [u, v] (m.set64 CTL 1 0) with
  | none => rw [hcall] at h; cases h
  | some x =>
  obtain ⟨rr, m₁⟩ := x
  rw [hcall] at h
  obtain ⟨s', rfl, -, hI⟩ := callW_triple (internMax_spec p (hp.get "max_find") (hp.get "max_push")
    (hp.get "intern_max") n ⟨m.set64 CTL 1 0, Locals.init []⟩ u v) hcall
  have hR₀ := hD.1.off
  obtain ⟨hok, hX, hres⟩ := mintern_correct _ (onA false a) hR₀.max u v hu.1 hv.1 _ _ hI
  have hL := mintern_hp _ (onA false a) hR₀.max u v hu.1 hv.1 hR₀.maxHp (lvlHPW_or _ _ hR₀ u v hu.1 hv.1) _ _ hI
  have hf := minternW_frame _ u v _ _ hI
  have hR₁ := hR₀.lift_max _ _ _ _ ⟨hX, hL⟩ hf
    (AM.st_proto maxLens _ _ _ _ _ _ _ (internLNode_max_run _ _ _) hok)
  have hpw := consInternM_pw maxCS_wf hR₀.max (by rw [rdW_set64]; simp [hc]) hI
  have hsz : 1 < (s'.mem.arr64 CTL).size := by rw [hf.2.2.1]; simpa [size_set64] using hc
  rw [piK_some _ _ _ hsz] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨a', h1, h2, h3⟩ := pi_lens hD (internLNode_max_run _ _ _) hok hR₁ hres hf
    (by simp [MREC, MSLOT, MHP]) (fun _ => ⟨rfl, rfl, rfl⟩) (fun _ => ⟨rfl, rfl, rfl⟩)
    (internPersistentL_eq _ a hD.1.flagsEq ⟨hu.pers, hv.pers⟩)
  refine ⟨a', h1, h2, hpw, h3, ?_⟩
  exact (frame_pi hc (hf.mono (by simp [ConsSch.wset, maxSch]) (by simp [maxSch])))

/-- **`pi_imax` refines `internPersistentL (.imax (decI u) (decI v))`.** -/
theorem piImax_rel (m : Mem) (a : AState) (hD : ArenaD m a) (u v : Word) (hu : PW u) (hv : PW v) (r : Word) (m' : Mem)
    (h : piW p n "intern_imax" [u, v] m = some (r, m')) :
    ∃ a', (internPersistentL (.imax (decI u) (decI v))).run a = .ok (decI r, a') ∧ ArenaD m' a' ∧ PW r ∧
      cp a' = cp a ∧ MemFrame [IREC, IREC + 256, ISLOT, ISLOT + 256, IHP, IHP + 256] [12, 13] m m' := by
  have hc := ctl_size hD.1
  rw [piW_eq _ _ _ _ _ hc] at h
  cases hcall : callW p n "intern_imax" [u, v] (m.set64 CTL 1 0) with
  | none => rw [hcall] at h; cases h
  | some x =>
  obtain ⟨rr, m₁⟩ := x
  rw [hcall] at h
  obtain ⟨s', rfl, -, hI⟩ := callW_triple (internImax_spec p (hp.get "imax_find") (hp.get "imax_push")
    (hp.get "intern_imax") n ⟨m.set64 CTL 1 0, Locals.init []⟩ u v) hcall
  have hR₀ := hD.1.off
  obtain ⟨hok, hX, hres⟩ := imintern_correct _ (onA false a) hR₀.imax u v hu.1 hv.1 _ _ hI
  have hL := imintern_hp _ (onA false a) hR₀.imax u v hu.1 hv.1 hR₀.imaxHp (lvlHPW_or _ _ hR₀ u v hu.1 hv.1) _ _ hI
  have hf := iminternW_frame _ u v _ _ hI
  have hR₁ := hR₀.lift_imax _ _ _ _ ⟨hX, hL⟩ hf
    (AM.st_proto imaxLens _ _ _ _ _ _ _ (internLNode_imax_run _ _ _) hok)
  have hpw := consInternM_pw imaxCS_wf hR₀.imax (by rw [rdW_set64]; simp [hc]) hI
  have hsz : 1 < (s'.mem.arr64 CTL).size := by rw [hf.2.2.1]; simpa [size_set64] using hc
  rw [piK_some _ _ _ hsz] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨a', h1, h2, h3⟩ := pi_lens hD (internLNode_imax_run _ _ _) hok hR₁ hres hf
    (by simp [IREC, ISLOT, IHP]) (fun _ => ⟨rfl, rfl, rfl⟩) (fun _ => ⟨rfl, rfl, rfl⟩)
    (internPersistentL_eq _ a hD.1.flagsEq ⟨hu.pers, hv.pers⟩)
  refine ⟨a', h1, h2, hpw, h3, ?_⟩
  exact (frame_pi hc (hf.mono (by simp [ConsSch.wset, imaxSch]) (by simp [imaxSch])))

/-- **`pi_param` refines `internPersistentL (.param (decI u))`.** -/
theorem piParam_rel (m : Mem) (a : AState) (hD : ArenaD m a) (u : Word) (hu : PW u) (r : Word) (m' : Mem)
    (h : piW p n "intern_param" [u] m = some (r, m')) :
    ∃ a', (internPersistentL (.param (decI u))).run a = .ok (decI r, a') ∧ ArenaD m' a' ∧ PW r ∧
      cp a' = cp a ∧ MemFrame [PREC, PREC + 256, PSLOT, PSLOT + 256] [14, 15] m m' := by
  have hc := ctl_size hD.1
  rw [piW_eq _ _ _ _ _ hc] at h
  cases hcall : callW p n "intern_param" [u] (m.set64 CTL 1 0) with
  | none => rw [hcall] at h; cases h
  | some x =>
  obtain ⟨rr, m₁⟩ := x
  rw [hcall] at h
  obtain ⟨s', rfl, -, hI⟩ := callW_triple (internParam_spec p (hp.get "param_find") (hp.get "param_push")
    (hp.get "intern_param") n ⟨m.set64 CTL 1 0, Locals.init []⟩ u) hcall
  have hR₀ := hD.1.off
  obtain ⟨hok, hX, hres⟩ := pintern_correct _ (onA false a) hR₀.param u hu.1 _ _ hI
  have hL := pintern_hp _ (onA false a) hR₀.param u hu.1 hR₀.paramHp _ _ hI
  have hf := consInternM_frame paramCS_wf hI
  have hR₁ := hR₀.lift_param _ _ _ _ ⟨hX, hL⟩ hf
    (AM.st_proto paramLens _ _ _ _ _ _ _ (internLNode_param_run _ _) hok)
  have hpw := consInternM_pw paramCS_wf hR₀.param (by rw [rdW_set64]; simp [hc]) hI
  have hsz : 1 < (s'.mem.arr64 CTL).size := by rw [hf.2.2.1]; simpa [size_set64] using hc
  rw [piK_some _ _ _ hsz] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨a', h1, h2, h3⟩ := pi_lens hD (internLNode_param_run _ _) hok hR₁ hres hf
    (by simp [ConsSch.wset, paramCS, paramSch, PREC, PSLOT]) (fun _ => ⟨rfl, rfl, rfl⟩) (fun _ => ⟨rfl, rfl, rfl⟩)
    (internPersistentL_eq _ a hD.1.flagsEq hu.pers)
  refine ⟨a', h1, h2, hpw, h3, ?_⟩
  exact (frame_pi hc (hf.mono (by simp [ConsSch.wset, paramCS, paramSch]) (by simp [ConsSch.wset, paramCS, paramSch])))

/-- **`pi_ls` refines `internPersistentLs us`**, `us` the persistent handles the pool slice
holds. -/
theorem piLs_rel0 (m : Mem) (a : AState) (hD : ArenaD m a) (o l : Word) (hsl : SliceOK m o l)
    (ho : o.toNat < 2 ^ 40) (us : List LIdx) (hk : sliceL (vpool m) o.toNat l.toNat = lsWords us)
    (hus : lsKids us) (r : Word) (m' : Mem) (h : piW p n "intern_ls" [o, l] m = some (r, m')) :
    ∃ a', (internPersistentLs us).run a = .ok (decI r, a') ∧ ArenaD m' a' ∧
      PW r ∧ cp a' = cp a ∧ MemFrame [LSREC, LSREC + 256, LSSLOT, LSSLOT + 256, LSHP, LSHP + 256] [40, 41] m m' := by
  have hc := ctl_size hD.1
  rw [piW_eq _ _ _ _ _ hc] at h
  cases hcall : callW p n "intern_ls" [o, l] (m.set64 CTL 1 0) with
  | none => rw [hcall] at h; cases h
  | some x =>
  obtain ⟨rr, m₁⟩ := x
  rw [hcall] at h
  have hR₀ := hD.1.off
  have ⟨_, _, hps, htop⟩ := hR₀.lit.1
  have hpool : (m.set64 CTL 1 0).arr64 POOL = m.arr64 POOL :=
    Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have hpool1 : (m.set64 CTL 1 0).arr64 POOL1 = m.arr64 POOL1 :=
    Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have hpoolv := vpool_congr hpool hpool1
  have htop' : (m.set64 CTL 1 0).top = m.top := by simp only [top_rdW, rdW_set64]; simp
  have hsl₀ : SliceOK (m.set64 CTL 1 0) o l := by
    simp only [SliceOK, htop', Mem.ptop0_set64_ne m CTL 1 0 (by decide)] at hsl ⊢; exact hsl
  obtain ⟨s', rfl, -, hI⟩ := callW_triple (internLs_spec p (hp.get "lit_hash") (hp.get "limbs_eq") (hp.get "ls_match")
    (hp.get "ls_find") (hp.get "ls_push") (hp.get "intern_ls") n ⟨m.set64 CTL 1 0, Locals.init []⟩ o l
    (by dsimp only; omega) (by simp only [SliceOK] at hsl₀; dsimp only; omega)) hcall
  obtain ⟨hok, hX, hres⟩ := lsintern_correct _ (onA false a) hR₀.lit.1 hR₀.ls o l hsl₀ us
    (by rw [hpoolv]; exact hk) (fun _ => ho) _ _ hI
  have hL := lsintern_hp _ (onA false a) hR₀.lit.1 hR₀.ls o l hsl₀ us (by rw [hpoolv]; exact hk)
    (fun _ => ho) hR₀.lsHp
    (lsOrW_ok _ _ hR₀ o l hsl₀ us (by rw [hpoolv]; exact hk)) _ _ hI
  have hf := lsinternW_frame _ o l _ _ hI
  have hR₁ := hR₀.lift_ls _ _ _ _ ⟨hX, hL⟩ hf
    (AM.st_proto lsLens _ _ _ _ _ _ _ (internLsNode_run _ _) hok)
  have hpw := consInternM_pw lsCS_wf hR₀.ls (by rw [rdW_set64]; simp [hc]) hI
  have hsz : 1 < (s'.mem.arr64 CTL).size := by rw [hf.2.2.1]; simpa [size_set64] using hc
  rw [piK_some _ _ _ hsz] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨a', h1, h2, h3⟩ := pi_lens hD (internLsNode_run _ _) hok hR₁ hres hf
    (by simp [LSREC, LSSLOT, LSHP]) (fun _ => ⟨rfl, rfl, rfl⟩) (fun _ => ⟨rfl, rfl, rfl⟩)
    (internPersistentLs_eq _ a hD.1.flagsEq hus)
  refine ⟨a', h1, h2, hpw, h3, ?_⟩
  exact (frame_pi hc (hf.mono (by simp [ConsSch.wset, lsSch]) (by simp [lsSch])))


/-- **`pi_ls` refines `internPersistentLs us`**, the handles the pool slice holds; a tier-1 slice
is first copied to tier 0 (lane tierpool). -/
theorem piLs_rel (m : Mem) (a : AState) (hD : ArenaD m a) (o l : Word) (hsl : SliceOK m o l)
    (us : List LIdx) (hk : sliceL (vpool m) o.toNat l.toNat = lsWords us)
    (hus : lsKids us) (r : Word) (m' : Mem) (h : pcW p n "intern_ls" [] o l m = some (r, m')) :
    ∃ a', (internPersistentLs us).run a = .ok (decI r, a') ∧ ArenaD m' a' ∧
      PW r ∧ cp a' = cp a ∧
      MemFrame [POOL, PT0, LSREC, LSREC + 256, LSSLOT, LSSLOT + 256, LSHP, LSHP + 256] [40, 41] m m' := by
  obtain ⟨m₁, o₁, h₁, hD₁, hs₁, ho₁, hf₁, -, hv, -⟩ := pc_cases hD hsl h
  obtain ⟨a', e1, e2, e3, e4, e5⟩ := piLs_rel0 p hp n m₁ a hD₁ o₁ l hs₁ ho₁ us
    (by rw [← hk]; exact (sliceL_eq_iff _ _ _ _ _).mpr hv) hus r m' h₁
  exact ⟨a', e1, e2, e3, e4, (hf₁.mono (by simp) (by simp)).trans (e5.mono (by simp) (by simp))⟩
end levels

end L.Arena
