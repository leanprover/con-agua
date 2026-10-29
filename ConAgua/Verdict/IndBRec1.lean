import ConAgua.Arena.RecGenSpec.ClassMinorSlotW
import ConAgua.Arena.RecClassSpec.Rec2SimTMA
import ConAgua.Arena.RecClassSpec.MkTMWAfr
import ConAgua.Arena.RecGenSpec.ClassKeyCanon
import ConAgua.Arena.RecGenSpec.ClassMinorSlot
import ConAgua.Arena.RecGenSpec.RgW
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConRon.Bridge.Inductives.GenRec

/-!
# The recursor generation's leaves: one model and one refinement for both outcomes

`class_key_of` (`kof_ref`), `class_minor_slot` (`cms_ref`), `class_rec_ty_ok_guards` (`rg_ref`, against
the twin's guards of `classRecTyOk`, `rgT`): `l_model … unified` models, their callees outside the
verdict closure lifted (`class_minor_slot_go` through its run). Each refinement's ok half is the
function's `@[refines]` theorem and its callers' ok refinements (`RefE.run_okW`), its error half the
callers' error claims (`RefE.run_err`); an error of class `1`/`2` claims the twin's failure.
-/

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

l_model classKeyOfE_spec (p : Prog) (hL : KofProg p)
  fns [hL.kof ↦ classKeyOfE]
  specs [kc_specF hL n, ckc2_spec hL n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] finish [tierW, idxW]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What `class_key_of` gives besides the twin's key `x` (from `m`): the canonical key `r`, a
record below the top with its parameter slice, the stage invariant, the growth. -/
structure KofPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m : Mem) (r : Word)
    (m' : Mem) (x : ClassKey) (a' : AState) : Prop where
  key : DecB (fun m => decCK m r.toNat) m' x
  top : r.toNat + 4 ≤ iwTop m'
  ds : (rdW (m'.arr64 IW) (r + 2)).toNat + (rdW (m'.arr64 IW) (r + 3)).toNat ≤ iwTop m'
  stage : StageR dn vis fe m' a'
  grow : IWGrow m m'
  pos : PosMR m'

section kof
variable {p : Prog} (L : KofProg p) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)
include L

omit L in
/-- **`class_key_of` refines `classKeyOf`, both outcomes**: `class_key_canon` (`kcW_ok`), the
closedness test `class_key_of_closed` (`ckc2W_ok`, both outside the verdict closure), the one
reject site (the major's parameters mention more than the recursor's). -/
theorem kof_ref (n : Nat) {m : Mem} {a : AState} {nP po pl key : Word} {pfvs : List EIdx}
    {ck : ClassKey} (hS : StageR dn vis fe m a) (hpf : decHL m po.toNat pl.toNat = some pfvs)
    (hpb : po.toNat + pl.toNat ≤ iwTop m) (hk : DecB (fun m => decCK m key.toNat) m ck)
    (hP : PosMR m) :
    RefE (closedNV p _root_.L.Checker.nvFns = true) (classKeyOfE p n m nP po pl key) (ConRon.Arena.classKeyOf nP.toNat pfvs ck) a
      (fun v x a' => KofPost dn vis fe m v.1 v.2 x a') := by
  cases n with
  | zero => rw [classKeyOfE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  rw [classKeyOfE.arm1]
  rcases h1 : kcWf n m po pl key with _ | ⟨r1, m1⟩
  · rw [liftE_none, classKeyOfE.k_class_key_canon.none]; exact RefE.of_cls0 (by simp)
  obtain _ | k := n
  · simp [kcWf] at h1
  rw [liftE_some]
  obtain ⟨x1, a1, hrun1, hd1, hb1, hds1, hS1, hg1, hP1⟩ :=
    kcW_ok dn fe vis k m m1 a po pl key r1 pfvs ck h1 hS hpf hpb hk hP
  have htop1 : iwTop m1 < 2 ^ 64 := Nat.lt_of_le_of_lt hS1.iw.iw hS1.iw.iwSize
  obtain ⟨nk, hnk, rfl⟩ := decCK_decB_nk hd1
  obtain ⟨-, -, -, -, hds, -, -⟩ := pos2_nk_fields hnk htop1
  unfold ConRon.Arena.classKeyOf
  refine RefE.bind_right hrun1 ?_
  rw [classKeyOfE.k_class_key_canon.eq_2]
  rcases h2 : ckc2W (k + 1) m1 nP (rdW (m1.arr64 IW) (r1.headD 0 + 2))
      (rdW (m1.arr64 IW) (r1.headD 0 + 3)) with _ | ⟨r2, m2⟩
  · rw [liftE_none, classKeyOfE.k_class_key_of_closed.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨b, a2, hrun2, hS2, hg2, hb2, -⟩ := ckc2W_ok dn fe vis (k + 1) m1 m2 a1 nP _ _ nk.ds r2 h2 hS1
    hds (by omega) hds1
  refine RefE.bind_right hrun2 ?_
  by_cases h0 : r2.headD 0 = 0
  · rw [classKeyOfE.k_class_key_of_closed.abort1 p _ r2 _ h0]
    have hbf : b = false := by rw [← hb2, h0]; rfl
    subst hbf
    exact fun _ => ErrClaim.fail _ _ rfl
  rw [classKeyOfE.k_class_key_of_closed.arm1 p _ r2 _ h0]
  have hbt : b = true := by rw [← hb2]; exact bne_iff_ne.mpr h0
  subst hbt
  have ek (j : Word) (hj : j.toNat < 4) :
      rdW (m2.arr64 IW) (r1.headD 0 + j) = rdW (m1.arr64 IW) (r1.headD 0 + j) := by
    simp only [rdW, word_add_toNat (show (r1.headD 0).toNat + j.toNat < 2 ^ 64 by omega)]
    rw [hg2.iwGet _ (by omega)]
  refine RefE.ret rfl ?_
  dsimp only
  exact ⟨hd1.grow (decCK_mono _) hg2, by have := hg2.iw; omega,
    by rw [ek 2 (by decide), ek 3 (by decide)]; have := hg2.iw; omega, hS2, hg1.trans hg2,
    hP1.fr (ckc2W_mfr _ _ _ _ _ _ _ h2)⟩

/-- **`class_key_of` refines `classKeyOf`** (through `replace_fvars`' and `fvar_b`'s stubs;
`bvar_b` the master's walk, at exec fuel below `coreWalkFuel`; `kof_ref`'s ok half). -/
@[refines ConRon.Arena.classKeyOf]
theorem classKeyOf_refines (k : Nat) (s₀ : St) (a₀ : AState)
    (nP po pl key : Word) (pfvs : List EIdx) (ck : ClassKey) (hS : StageR dn vis fe s₀.mem a₀)
    (hpf : decHL s₀.mem po.toNat pl.toNat = some pfvs) (hpb : po.toNat + pl.toNat ≤ iwTop s₀.mem)
    (hk : DecB (fun m => decCK m key.toNat) s₀.mem ck) (hP : PosMR s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 2)) "class_key_of" [nP, po, pl, key]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classKeyOf nP.toNat pfvs ck) a₀ ∧
      DecB (fun m => decCK m (r.headD 0).toNat) s'.mem (AM.res (ConRon.Arena.classKeyOf nP.toNat pfvs ck) a₀) ∧
      (r.headD 0).toNat + 4 ≤ iwTop s'.mem ∧
      (rdW (s'.mem.arr64 IW) (r.headD 0 + 2)).toNat + (rdW (s'.mem.arr64 IW) (r.headD 0 + 3)).toNat ≤
        iwTop s'.mem ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.classKeyOf nP.toNat pfvs ck) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ PosMR s'.mem; ⊤⦄ := by
  refine triple_post (RefE.triple (classKeyOfE_spec p L (k + 2) s₀ nP po pl key)
    (kof_ref dn fe vis (k + 2) hS hpf hpb hk hP)) ?_
  rintro r s' ⟨hl, x, a', run, hR⟩
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl, hok, by rw [hres]; exact hR.key, hR.top, hR.ds, by rw [hst]; exact hR.stage, hR.grow,
    hR.pos⟩

end kof


l_model classMinorSlotE_spec (p : Prog) (hf : p.lookup "class_minor_slot" = some classMinorSlotL)
  fns [hf ↦ classMinorSlotE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] unified

/-- What `class_minor_slot` gives besides the twin's hit `y` (from `m`, `a`): the memory and the
twin's state unchanged, the slot word and the hit's `ihs` slice (decoded below the tops when the
class reading is). -/
structure CmsPost (m : Mem) (rd : Word) (R : ClassRead) (r : List Word) (m' : Mem)
    (y : Nat × List (Nat × Nat)) (a a' : AState) : Prop where
  mem : m' = m
  st : a' = a
  slot : r.headD 0 = UInt64.ofNat y.1
  ihs : decPL m (decNN m) (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat = some y.2
  ihsB : DecB (fun m => decCR m rd.toNat) m R →
    DecB (fun m => decPL m (decNN m) (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat) m y.2

/-- **`class_minor_slot` refines `classMinorSlot`, both outcomes**: the scan `class_minor_slot_go`
(outside the verdict closure) counts the twin's hits (`cmsGo_hits`); the one reject site (not
exactly one minor premise) means the twin's hit list is not a singleton. -/
theorem cms_ref {p : Prog} (hgo : p.lookup "class_minor_slot_go" = some classMinorSlotGo) (n : Nat)
    {m : Mem} {a : AState} {rd c cc : Word} {R : ClassRead} (hR : decCR m rd.toNat = some R)
    (hcc : cc.toNat < 2 ^ 32) (hsz : (m.arr64 IW).size + 5 < 2 ^ 64) :
    RefE (closedNV p _root_.L.Checker.nvFns = true) (classMinorSlotE p n m rd c cc)
      (ConRon.Arena.classMinorSlot R c.toNat (decI cc)) a
      (fun v y a' => CmsPost m rd R v.1 v.2 y a a') := by
  cases n with
  | zero => rw [classMinorSlotE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  simp only [classMinorSlotE]
  rcases h1 : callE p n "class_minor_slot_go"
      [rdW (m.arr64 IW) rd, rdW (m.arr64 IW) (rd + 1), 0, c, cc, 0, 0, 0, 0] m with e1 | ⟨r, m1⟩
  · rw [classMinorSlotE.k_class_minor_slot_go.none]
    exact fun hnv => ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h1
  obtain ⟨s', rfl, -, hm, x, y, z, w, hg, rfl⟩ := triple_of_callW
    (classMinorSlotGo_spec p hgo n ⟨m, Locals.init []⟩ _ _ 0 c cc 0 0 0 0) (callW_of_callE h1)
  simp only at hm hg
  obtain ⟨hlen, hhit⟩ := cmsGo_hits n m rd c cc R hR hcc hsz hg
  have hits := hitsFrom_eq c.toNat (decI cc) 0 R.slots
  simp only [Nat.zero_add] at hits
  by_cases hx : [x, y, z, w].headD 0 ≠ 1
  · rw [classMinorSlotE.k_class_minor_slot_go.abort1 p _ _ hx]
    refine fun _ => ?_
    simp only [List.headD_cons] at hx
    have hlen1 : (hitsFrom c.toNat (decI cc) 0 R.slots).length ≠ 1 := by
      intro h1'
      apply hx
      have : x.toNat = (1 : Word).toNat := by rw [hlen, h1']; rfl
      exact UInt64.toNat_inj.mp this
    show ErrClaim (ConRon.Arena.classMinorSlot R c.toNat (decI cc)) a _
    simp only [ConRon.Arena.classMinorSlot]
    erw [hits]
    match hh : hitsFrom c.toNat (decI cc) 0 R.slots, hlen1 with
    | [], _ => exact ErrClaim.fail _ _ (by decide)
    | _ :: _ :: _, _ => exact ErrClaim.fail _ _ (by decide)
  rw [classMinorSlotE.k_class_minor_slot_go.arm1 p _ _ (by simpa using hx)]
  simp only [List.headD_cons, ne_eq, Decidable.not_not] at hx
  have hlen1 : (hitsFrom c.toNat (decI cc) 0 R.slots).length = 1 := by
    rw [← hlen, hx]; rfl
  match hh : hitsFrom c.toNat (decI cc) 0 R.slots, hlen1 with
  | [(s, ihs)], _ =>
    obtain ⟨e1, e2⟩ := hhit s ihs hh
    refine RefE.ret (y := (s, ihs)) (a' := a) ?_ ?_
    · simp only [ConRon.Arena.classMinorSlot]
      erw [hits, hh]
      rfl
    · dsimp only
      simp only [List.headD_cons, List.tail_cons]
      exact ⟨hm, rfl, e1, e2, fun hRB => cmsGo_decB n hg hRB hh e1 e2 hsz⟩

/-- **`class_minor_slot` refines `classMinorSlot`**: the twin succeeds (without touching the state)
with the unique `.minor c cc` slot, and the words are its position and `ihs` slice (`cms_ref`'s
ok half). -/
@[refines ConRon.Arena.classMinorSlot]
theorem classMinorSlot_refines (p : Prog)
    (hgo : p.lookup "class_minor_slot_go" = some classMinorSlotGo)
    (hp : p.lookup "class_minor_slot" = some classMinorSlotL) (n : Nat) (s₀ : St) (a₀ : AState)
    (rd c cc : Word) (R : ClassRead) (hR : decCR s₀.mem rd.toNat = some R) (hcc : cc.toNat < 2 ^ 32)
    (hsz : (s₀.mem.arr64 IW).size + 5 < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "class_minor_slot" [rd, c, cc]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      AM.ok (ConRon.Arena.classMinorSlot R c.toNat (decI cc)) a₀ ∧
      AM.st (ConRon.Arena.classMinorSlot R c.toNat (decI cc)) a₀ = a₀ ∧
      r.headD 0 = UInt64.ofNat (AM.res (ConRon.Arena.classMinorSlot R c.toNat (decI cc)) a₀).1 ∧
      decPL s₀.mem (decNN s₀.mem) (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat =
        some (AM.res (ConRon.Arena.classMinorSlot R c.toNat (decI cc)) a₀).2; ⊤⦄ := by
  refine triple_post (RefE.triple (classMinorSlotE_spec p hp (n + 1) s₀ rd c cc)
    (cms_ref hgo (n + 1) (a := a₀) hR hcc hsz)) ?_
  rintro r s' ⟨hl, y, a', run, hR'⟩
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl, hR'.mem, hok, by rw [hst]; exact hR'.st, by rw [hres]; exact hR'.slot,
    by rw [hres]; exact hR'.ihs⟩


l_model classRecTyOkGuardsE_spec (p : Prog) (hp : RtoProg p)
  fns [hp.rg ↦ classRecTyOkGuardsE]
  specs [targetMajorAt_spec p hp.alloc hp.pw hp.mtm hp.tmd hp.tma hp.na n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **The twin's guards of `classRecTyOk`** (the prefix `class_rec_ty_ok_guards` stands for): the
class's major, the member guard, the rule prefix and major index guards. -/
def rgT (G : ClassGen) (RS : RecShape) (k c : Nat) : AM TargetMajor := do
  let ci ← ConRon.Arena.targetMajorAt G.cls c
  unless RS.tgt == ci.member.getD k do
    fail (.invalid "generated recursor: the recursor record's member is not its class's")
  unless RS.rP == G.nP + G.slots.length && RS.mI == RS.rP + ci.nIdx do
    fail (.invalid "generated recursor: the recursor record's rule prefix or major index is \
      not the generated one")
  pure ci

/-- `classRecTyOk` is its guards, then the rest. -/
theorem rgT_bind {γ : Type} (G : ClassGen) (RS : RecShape) (k c : Nat) (rest : AM γ) :
    (do
      let ci ← ConRon.Arena.targetMajorAt G.cls c
      unless RS.tgt == ci.member.getD k do
        fail (.invalid "generated recursor: the recursor record's member is not its class's")
      unless RS.rP == G.nP + G.slots.length && RS.mI == RS.rP + ci.nIdx do
        fail (.invalid "generated recursor: the recursor record's rule prefix or major index is \
          not the generated one")
      rest) = rgT G RS k c >>= fun _ => rest := by
  simp only [rgT, bind_assoc, ite_bindAM, fail_bindAM, pure_bind]

theorem memGuard_iff (tgt k8 : Nat) (k : Word) (ht : tgt < 2 ^ 64) (hk8 : k8 < 2 ^ 64) :
    (UInt64.ofNat tgt = (if (UInt64.ofNat k8 : Word) ≠ 0 then (UInt64.ofNat k8 : Word) - 1 else k)) ↔
      (tgt == (decON k8).getD k.toNat) = true := by
  by_cases hz : k8 = 0
  · subst hz
    simp only [show (UInt64.ofNat 0 : Word) = 0 from rfl, ne_eq, not_true_eq_false, ite_false, decON,
      ite_true, Option.getD_none, beq_iff_eq]
    constructor
    · intro h; have := congrArg UInt64.toNat h; rwa [UInt64.toNat_ofNat_of_lt' ht] at this
    · intro h; rw [h]; exact UInt64.ofNat_toNat
  · have hz' : (UInt64.ofNat k8 : Word) ≠ 0 := fun e => hz (rec2W_inj hk8 (by decide) e)
    have e1 : (UInt64.ofNat k8 - 1 : Word) = UInt64.ofNat (k8 - 1) := by
      obtain ⟨j, rfl⟩ : ∃ j, k8 = j + 1 := ⟨k8 - 1, by omega⟩
      simp [UInt64.ofNat_add]
    simp only [hz', ne_eq, not_false_eq_true, ite_true, e1, decON, hz, ite_false, Option.getD_some, beq_iff_eq]
    constructor
    · intro h; exact rec2W_inj ht (by omega) h
    · intro h; rw [h]

/-- What `class_rec_ty_ok_guards` gives besides the twin's major `tm` (from `m`, `a`): the twin's
run of `targetMajorAt` (the guards keep the state), the stage invariant, the growth, the
abstraction memo. -/
structure RgPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m : Mem) (a : AState)
    (G : ClassGen) (c : Word) (m' : Mem) (tm : TargetMajor) (a' : AState) : Prop where
  run : (ConRon.Arena.targetMajorAt G.cls c.toNat).run a = .ok (tm, a')
  stage : StageR dn vis fe m' a'
  grow : IWGrow m m'
  abs : AbsOK m'

section rg
variable (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)

/-- **`class_rec_ty_ok_guards` refines `classRecTyOk`'s guards (`rgT`), both outcomes**: the class's
major (`target_major_at`, outside the verdict closure), then the member guard and the rule prefix
and major index guards, each a reject site of the twin's. -/
theorem rg_ref {p : Prog} (n : Nat) {m : Mem} {a : AState} {g k rc c : Word} {G : ClassGen}
    {RS : RecShape} (hS : StageR dn vis fe m a) (hG : DecB (fun m => decCG m g.toNat) m G)
    (hns : G.nP + G.slots.length < 2 ^ 64) (hrc : DecB (fun m => decRS m rc.toNat) m RS)
    (hA : AbsOK m) :
    RefE (closedNV p _root_.L.Checker.nvFns = true) (classRecTyOkGuardsE p n m g k rc c)
      (rgT G RS k.toNat c.toNat) a (fun v tm a' => RgPost dn vis fe m a G c v.2 tm a') := by
  cases n with
  | zero => rw [classRecTyOkGuardsE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  have hsz := hS.iw.iwSize
  have htop := hS.iw.iw
  obtain ⟨-, hgt, ⟨o3, l3, h3, h4, hcls⟩, -⟩ := rec2CG_parts hG
  obtain ⟨e3, t3⟩ := rec2RdN (w := g) (k := 3) h3 hsz
  obtain ⟨e4, t4⟩ := rec2RdN (w := g) (k := 4) h4 hsz
  simp only [show UInt64.ofNat 3 = (3 : Word) from rfl, show UInt64.ofNat 4 = (4 : Word) from rfl] at e3 e4
  have hb3 : o3 + l3 < 2 ^ 64 := by
    by_cases hl : l3 = 0
    · have := iwN_rdW h3 (by omega); omega
    · have := rec2DecB_PL_top hcls hl; omega
  rw [classRecTyOkGuardsE.arm1, e3, e4]
  rcases h1 : tmaW n m (UInt64.ofNat o3) (UInt64.ofNat l3) c with _ | ⟨r1, m1⟩
  · rw [liftE_none, classRecTyOkGuardsE.k_target_major_at.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨tm, a1, hrun1, hS1, hg1, hTM, -⟩ := rec2SimTMA dn vis fe n m a (UInt64.ofNat o3) (UInt64.ofNat l3)
    c G.cls hS (by rw [t3, t4]; exact hcls) (by rw [t3, t4]; exact hb3) (r1, m1) h1
  dsimp only at hS1 hg1 hTM
  have hA1 : AbsOK m1 := tmaW_afr h1 hA
  unfold rgT
  refine RefE.bind_right hrun1 ?_
  have hsz1 := hS1.iw.iwSize
  obtain ⟨k8, hk8, hmem⟩ := decTM_member hTM
  obtain ⟨-, -, -, -, hni⟩ := rec2DecTM_parts hTM
  obtain ⟨e8, -⟩ := rec2RdN (w := r1.headD 0) (k := 8) hk8 hsz1
  obtain ⟨e5, -⟩ := rec2RdN (w := r1.headD 0) (k := 5) hni hsz1
  have k8lt := (iwN_rdW_at (w := r1.headD 0) (k := 8) hk8 hsz1).2
  have nilt := (iwN_rdW_at (w := r1.headD 0) (k := 5) hni hsz1).2
  simp only [show UInt64.ofNat 8 = (8 : Word) from rfl, show UInt64.ofNat 5 = (5 : Word) from rfl] at e8 e5
  obtain ⟨-, -, -, hrP, hmI, htgt⟩ := rec2DecRS_parts (hrc.stab (decRS_mono _) m1 hg1)
  obtain ⟨eP, -⟩ := rec2RdN (w := rc) (k := 1) hrP hsz1
  obtain ⟨eI, -⟩ := rec2RdN (w := rc) (k := 2) hmI hsz1
  obtain ⟨eT, -⟩ := rec2RdN (w := rc) (k := 3) htgt hsz1
  have rPlt := (iwN_rdW_at (w := rc) (k := 1) hrP hsz1).2
  have mIlt := (iwN_rdW_at (w := rc) (k := 2) hmI hsz1).2
  have tglt := (iwN_rdW_at (w := rc) (k := 3) htgt hsz1).2
  simp only [show UInt64.ofNat 1 = (1 : Word) from rfl, show UInt64.ofNat 2 = (2 : Word) from rfl,
    show UInt64.ofNat 3 = (3 : Word) from rfl] at eP eI eT
  obtain ⟨hnP, hsl⟩ := rec2CG_get (hG.stab (decCG_mono _) m1 hg1)
  obtain ⟨so, sl, hso, hsl', hsls⟩ := decAt_some hsl
  have hlen := decPL_length m1 hsls
  obtain ⟨eg, -⟩ := rec2RdN (w := g) (k := 0) (by simpa using hnP) hsz1
  obtain ⟨eg8, -⟩ := rec2RdN (w := g) (k := 8) (by simpa [Nat.add_assoc] using hsl') hsz1
  have nPlt := (iwN_rdW_at (w := g) (k := 0) (by simpa using hnP) hsz1).2
  simp only [show UInt64.ofNat 0 = (0 : Word) from rfl, UInt64.add_zero,
    show UInt64.ofNat 8 = (8 : Word) from rfl] at eg eg8
  have sllt := (iwN_rdW_at (w := g) (k := 8) (by simpa [Nat.add_assoc] using hsl') hsz1).2
  have hsl8 : sl = G.slots.length := hlen.symm
  have hmg := memGuard_iff RS.tgt k8 k tglt k8lt
  rw [← hmem] at hmg
  have key : ∀ memv : Word, memv = (if (UInt64.ofNat k8 : Word) ≠ 0 then (UInt64.ofNat k8 : Word) - 1 else k) →
      RefE (closedNV p _root_.L.Checker.nvFns = true) (classRecTyOkGuardsE.j1 p g rc (r1.headD 0) memv m1)
        (do
          unless RS.tgt == tm.member.getD k.toNat do
            fail (.invalid "generated recursor: the recursor record's member is not its class's")
          unless RS.rP == G.nP + G.slots.length && RS.mI == RS.rP + tm.nIdx do
            fail (.invalid "generated recursor: the recursor record's rule prefix or major index is \
              not the generated one")
          pure tm) a1 (fun v tm' a' => RgPost dn vis fe m a G c v.2 tm' a') := by
    intro memv hmv
    by_cases c1 : rdW (m1.arr64 IW) (rc + 3) = memv
    · have g1t : (RS.tgt == tm.member.getD k.toNat) = true := by
        apply hmg.mp; rw [← hmv, ← eT]; exact c1
      by_cases c2 : rdW (m1.arr64 IW) (rc + 1) = rdW (m1.arr64 IW) g + rdW (m1.arr64 IW) (g + 8)
      · have hrPe : RS.rP = G.nP + G.slots.length := by
          have := congrArg UInt64.toNat c2
          rw [eP, eg, eg8, UInt64.toNat_ofNat_of_lt' rPlt, rec2W_add _ _ nPlt sllt, hsl8] at this
          rw [this, Nat.mod_eq_of_lt hns]
        by_cases c3 : rdW (m1.arr64 IW) (rc + 1) + rdW (m1.arr64 IW) (r1.headD 0 + 5) <
            rdW (m1.arr64 IW) (rc + 1)
        · rw [classRecTyOkGuardsE.j1.abort3 p g rc _ memv m1 c1 c2 c3]
          exact RefE.of_cls0 rfl
        have hno : RS.rP + tm.nIdx < 2 ^ 64 := by
          rw [eP, e5] at c3
          have : ¬ (UInt64.ofNat RS.rP + UInt64.ofNat tm.nIdx : Word).toNat < (UInt64.ofNat RS.rP : Word).toNat :=
            fun x => c3 (UInt64.lt_iff_toNat_lt.mpr x)
          rw [rec2W_add _ _ rPlt nilt, UInt64.toNat_ofNat_of_lt' rPlt] at this
          omega
        by_cases c4 : rdW (m1.arr64 IW) (rc + 2) = rdW (m1.arr64 IW) (rc + 1) + rdW (m1.arr64 IW) (r1.headD 0 + 5)
        · rw [classRecTyOkGuardsE.j1.arm1 p g rc _ memv m1 c1 c2 c3 c4]
          have hmIe : RS.mI = RS.rP + tm.nIdx := by
            have := congrArg UInt64.toNat c4
            rw [eI, eP, e5, UInt64.toNat_ofNat_of_lt' mIlt, rec2W_add _ _ rPlt nilt, Nat.mod_eq_of_lt hno] at this
            exact this
          have g2t : (RS.rP == G.nP + G.slots.length && RS.mI == RS.rP + tm.nIdx) = true := by
            simp [hrPe, hmIe]
          refine RefE.ret (y := tm) (a' := a1) ?_ ⟨hrun1, hS1, hg1, hA1⟩
          simp only [g1t, g2t, ite_true]
          rfl
        · rw [classRecTyOkGuardsE.j1.abort4 p g rc _ memv m1 c1 c2 c3 c4]
          refine fun _ => ?_
          have g2f : (RS.rP == G.nP + G.slots.length && RS.mI == RS.rP + tm.nIdx) = false := by
            cases hh : (RS.rP == G.nP + G.slots.length && RS.mI == RS.rP + tm.nIdx)
            · rfl
            · exfalso
              simp only [Bool.and_eq_true, beq_iff_eq] at hh
              apply c4
              rw [eI, eP, e5, hh.2, UInt64.ofNat_add]
          simp only [g1t, g2f, Bool.false_eq_true, ite_true, ite_false]
          exact ErrClaim.bind_left (ErrClaim.fail _ _ (by decide))
      · rw [classRecTyOkGuardsE.j1.abort2 p g rc _ memv m1 c1 c2]
        refine fun _ => ?_
        have g2f : (RS.rP == G.nP + G.slots.length && RS.mI == RS.rP + tm.nIdx) = false := by
          cases hh : (RS.rP == G.nP + G.slots.length && RS.mI == RS.rP + tm.nIdx)
          · rfl
          · exfalso
            simp only [Bool.and_eq_true, beq_iff_eq] at hh
            apply c2
            rw [eP, eg, eg8, hh.1, ← hsl8, UInt64.ofNat_add]
        simp only [g1t, g2f, Bool.false_eq_true, ite_true, ite_false]
        exact ErrClaim.bind_left (ErrClaim.fail _ _ (by decide))
    · rw [classRecTyOkGuardsE.j1.abort1 p g rc _ memv m1 c1]
      refine fun _ => ?_
      rw [eT, hmv] at c1
      have g1f : (RS.tgt == tm.member.getD k.toNat) = false := by
        cases hh : (RS.tgt == tm.member.getD k.toNat)
        · rfl
        · exact absurd (hmg.mpr hh) c1
      simp only [g1f, Bool.false_eq_true, ite_false]
      exact ErrClaim.bind_left (ErrClaim.fail _ _ (by decide))
  by_cases hmz : rdW (m1.arr64 IW) (r1.headD 0 + 8) ≠ 0
  · rw [classRecTyOkGuardsE.k_target_major_at.arm1 p g k rc r1 m1 hmz]
    refine key _ ?_
    rw [e8] at hmz ⊢
    simp [hmz]
  · rw [classRecTyOkGuardsE.k_target_major_at.arm2 p g k rc r1 m1 (by simpa using hmz)]
    refine key _ ?_
    rw [e8] at hmz
    simp [hmz]

end rg

end L.Ind

end
