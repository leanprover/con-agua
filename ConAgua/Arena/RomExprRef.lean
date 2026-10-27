import ConAgua.Arena.RomExpr
import ConAgua.Arena.NatArms
import ConLeche.Verify.Cached.Erase
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# `rom_expr` refines `internExprGo`, the memo mirrored

The pure side of `RomExpr.lean`: from `ArenaD`, the memo relation `MemoR` (the L memo `RMEMO`
holds the handles of the twin's `EMemo` in the order the encoder's `seen` lists their keys), and
the ROM holding `(encExprM seen e).1` at `pos`, a run of the model `romExprW` is the twin's
`internExprGo m e`, the memo relation holds after at the encoder's new `seen`, and only the store
tier, the stack and the memo were written.
-/

open ConRon.Arena ConRon.Arena.Frontend
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Rom

open L.Arena

/-! ## Frames of the expression constructors -/

/-- The expression interner's frame: the store tier, the stack, the memo and its handle set. -/
def ExprA : List ArrId := RMEMO :: RSET :: RomA
def ExprC : List Word := 132 :: 148 :: 149 :: RomC

theorem frame_exprA {m m' : Mem} (h : MemFrame RomA RomC m m') : MemFrame ExprA ExprC m m' :=
  h.mono (fun b hb => by simp [ExprA, hb]) (fun x hx => by simp [ExprC, hx])

theorem frame_storeE {m m' : Mem} (h : MemFrame StoreA StoreC m m') : MemFrame ExprA ExprC m m' :=
  frame_exprA (frame_romA h)

theorem mkK_store (A : ArrId) (hA : A < 56) (hC : A ≠ CTL) (c s d r : Word) (m m' : Mem)
    (x : Option (Word × Mem)) (hx : ∀ r₁ m₁, x = some (r₁, m₁) → MemFrame StoreA StoreC m m₁)
    (h : mkK A c s d x = some (r, m')) : MemFrame StoreA StoreC m m' := by
  match x, hx, h with
  | some (r₁, m₁), hx, h =>
    rw [mkK_some] at h
    split at h
    · cases h
    · rename_i m₂ hP
      cases h
      exact (hx _ _ rfl).trans (frame_store (derPutW_frame A hC _ _ _ _ _ _ hP)
        (fun b hb => by
          have key : ∀ n : Nat, n < 56 → (n < 64 ∨ (256 ≤ n ∧ n < 320)) ∧
              (n + 256 < 64 ∨ (256 ≤ n + 256 ∧ n + 256 < 320)) := fun n h => by omega
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
          rcases hb with rfl | rfl
          · exact (key _ hA).1
          · exact (key _ hA).2) (by simp))

theorem mkAppW_store {m m' : Mem} {f x r : Word} (h : mkAppW m f x = some (r, m')) :
    MemFrame StoreA StoreC m m' := by
  unfold mkAppW at h; split at h; · cases h
  exact mkK_store ADER (by decide) (by decide) _ _ _ _ _ _ _ (fun r₁ m₁ hx => by
    exact frame_store (consInternM_frame appCS_wf hx) (by simp [ConsSch.wset, appCS, AREC, ASLOT])
      (by simp [appCS])) h
theorem mkLamW_store {m m' : Mem} {f x r : Word} (h : mkLamW m f x = some (r, m')) :
    MemFrame StoreA StoreC m m' := by
  unfold mkLamW at h; split at h; · cases h
  exact mkK_store LADER (by decide) (by decide) _ _ _ _ _ _ _ (fun r₁ m₁ hx => by
    exact frame_store (consInternM_frame lamCS_wf hx) (by simp [ConsSch.wset, lamCS, LAREC, LASLOT])
      (by simp [lamCS])) h
theorem mkForallW_store {m m' : Mem} {f x r : Word} (h : mkForallW m f x = some (r, m')) :
    MemFrame StoreA StoreC m m' := by
  unfold mkForallW at h; split at h; · cases h
  exact mkK_store FADER (by decide) (by decide) _ _ _ _ _ _ _ (fun r₁ m₁ hx => by
    exact frame_store (consInternM_frame forallCS_wf hx)
      (by simp [ConsSch.wset, forallCS, FAREC, FASLOT]) (by simp [forallCS])) h
theorem mkLetW_store {m m' : Mem} {t v x r : Word} (h : mkLetW m t v x = some (r, m')) :
    MemFrame StoreA StoreC m m' := by
  unfold mkLetW at h; split at h; · cases h
  exact mkK_store LEDER (by decide) (by decide) _ _ _ _ _ _ _ (fun r₁ m₁ hx => by
    exact frame_store (consInternM_frame letCS_wf hx) (by simp [ConsSch.wset, letCS, LEREC, LESLOT])
      (by simp [letCS])) h
theorem mkProjW_store {m m' : Mem} {n i e r : Word} (h : mkProjW m n i e = some (r, m')) :
    MemFrame StoreA StoreC m m' := by
  unfold mkProjW at h; split at h; · cases h
  exact mkK_store PJDER (by decide) (by decide) _ _ _ _ _ _ _ (fun r₁ m₁ hx => by
    exact frame_store (consInternM_frame projCS_wf hx) (by simp [ConsSch.wset, projCS, PJREC, PJSLOT])
      (by simp [projCS])) h
theorem binternW_store {m m' : Mem} {u r : Word} (h : binternW m u = some (r, m')) :
    MemFrame StoreA StoreC m m' := by
  exact frame_store (consInternM_frame bvarCS_wf h) (by simp [ConsSch.wset, bvarCS, BREC, BSLOT])
    (by simp [bvarCS])
theorem fvinternW_store {m m' : Mem} {u t r : Word} (h : fvinternW m u t = some (r, m')) :
    MemFrame StoreA StoreC m m' := by
  exact frame_store (fvinternW_frame (hI := h)) (by simp [FVREC, FVSLOT, FVLP])
    (by simp)

/-! ## The memo relation -/

/-- **The L memo is the twin's `EMemo`**, its keys listed in insertion order by `seen`. -/
structure MemoR (mem : Mem) (seen : List ConLeche.Expr) (m : EMemo) : Prop where
  cnt : (memoCnt mem).toNat = seen.length
  ent : ∀ k (hk : k < seen.length), (rdW (mem.arr64 RMEMO) (UInt64.ofNat k)).toNat < 2 ^ 32 ∧
    m[seen[k]]? = some (decI (rdW (mem.arr64 RMEMO) (UInt64.ofNat k)))
  keys : ∀ e, (m[e]?).isSome → e ∈ seen
  room : seen.length < 2 ^ 64
  csz : 132 < (mem.arr64 CTL).size

theorem MemoR.frame {mem mem' : Mem} {seen : List ConLeche.Expr} {m : EMemo} (h : MemoR mem seen m)
    (hf : MemFrame RomA RomC mem mem') : MemoR mem' seen m := by
  have hR : mem'.arr64 RMEMO = mem.arr64 RMEMO := hf.1 RMEMO (by decide) (by decide)
  have hc : memoCnt mem' = memoCnt mem :=
    hf.2.1 132 (by simp only [RomC, List.mem_cons]; intro h'; rcases h' with h' | h'
                   · exact absurd h' (by decide)
                   · exact not_mem_storeC _ (by decide) h')
  exact ⟨by rw [hc]; exact h.cnt, fun k hk => by rw [hR]; exact h.ent k hk, h.keys, h.room,
    by rw [hf.2.2.1]; exact h.csz⟩

theorem MemoR.miss {mem : Mem} {seen : List ConLeche.Expr} {m : EMemo} (h : MemoR mem seen m)
    {e : ConLeche.Expr} (he : e ∉ seen) : m[e]? = none := by
  cases hm : m[e]? with
  | none => rfl
  | some x => exact absurd (h.keys e (by simp [hm])) he

theorem MemoR.hit {mem : Mem} {seen : List ConLeche.Expr} {m : EMemo} (h : MemoR mem seen m)
    {e : ConLeche.Expr} (he : e ∈ seen) :
    (rdW (mem.arr64 RMEMO) (UInt64.ofNat (seen.idxOf e))).toNat < 2 ^ 32 ∧
    m[e]? = some (decI (rdW (mem.arr64 RMEMO) (UInt64.ofNat (seen.idxOf e)))) := by
  have hk := List.idxOf_lt_length_iff.mpr he
  obtain ⟨h1, h2⟩ := h.ent _ hk
  rw [List.getElem_idxOf hk] at h2
  exact ⟨h1, h2⟩

/-- `memo_push`'s memory without the handle set. -/
def mpushOld (m : Mem) (h : Word) : Mem := (m.set64 RMEMO (memoCnt m) h).set64 CTL 132 (memoCnt m + 1)

theorem MemoR.of_eq {mem mem' : Mem} {seen : List ConLeche.Expr} {m : EMemo} (h : MemoR mem seen m)
    (hR : mem'.arr64 RMEMO = mem.arr64 RMEMO) (hc : memoCnt mem' = memoCnt mem)
    (hs : (mem'.arr64 CTL).size = (mem.arr64 CTL).size) : MemoR mem' seen m :=
  ⟨by rw [hc]; exact h.cnt, fun k hk => by rw [hR]; exact h.ent k hk, h.keys, h.room,
    by rw [hs]; exact h.csz⟩

theorem MemoR.push0 {mem : Mem} {seen : List ConLeche.Expr} {m : EMemo} (h : MemoR mem seen m)
    {e : ConLeche.Expr} (he : e ∉ seen) (x : Word)
    (hx : x.toNat < 2 ^ 32) (hsz' : memoCnt mem < mem.len64 RMEMO) :
    MemoR (mpushOld mem x) (seen ++ [e]) (m.insert e (decI x)) := by
  have hcn := h.cnt
  have hl := UInt64.lt_iff_toNat_lt.mp hsz'
  simp only [Mem.len64, UInt64.toNat_ofNat'] at hl
  have hsz : (memoCnt mem).toNat < (mem.arr64 RMEMO).size :=
    Nat.lt_of_lt_of_le hl (Nat.mod_le _ _)
  have hroom : (memoCnt mem).toNat + 1 < 2 ^ 64 := by
    have := Nat.mod_lt (mem.arr64 RMEMO).size (show 2 ^ 64 > 0 by decide); omega
  have hR : ∀ k : Word, rdW ((mpushOld mem x).arr64 RMEMO) k =
      if k = memoCnt mem then x else rdW (mem.arr64 RMEMO) k := by
    intro k
    simp only [mpushOld, Mem.arr64_set64_ne _ _ _ _ _ (show RMEMO ≠ CTL by decide), Mem.arr64_set64_same,
      rdW_set!]
    by_cases e' : k = memoCnt mem
    · subst e'; simp [hsz]
    · have : ¬ (memoCnt mem).toNat = k.toNat := fun h' => e' (UInt64.toNat_inj.mp h'.symm)
      simp [e', this]
  have hcnt' : memoCnt (mpushOld mem x) = memoCnt mem + 1 := by
    have hs : 132 < ((mem.set64 RMEMO (memoCnt mem) x).arr64 CTL).size := by
      rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]; exact h.csz
    simp only [memoCnt] at hs ⊢
    simp only [mpushOld, memoCnt, Mem.arr64_set64_same, rdW_set!]
    simp [hs]
  refine ⟨?_, fun k hk => ?_, fun e' he' => ?_, by simp; omega, ?_⟩
  · rw [hcnt', UInt64.toNat_add]; simp; omega
  · simp only [List.length_append, List.length_cons, List.length_nil] at hk
    rw [hR]
    by_cases hks : k < seen.length
    · have hne : UInt64.ofNat k ≠ memoCnt mem := by
        intro h'; have := congrArg UInt64.toNat h'; rw [UInt64.toNat_ofNat'] at this; omega
      simp only [hne, ite_false, List.getElem_append_left hks]
      obtain ⟨e1, e2⟩ := h.ent k hks
      refine ⟨e1, ?_⟩
      rw [Std.HashMap.getElem?_insert]
      have : (e == seen[k]) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; intro h'; exact he (h' ▸ List.getElem_mem hks)
      simp [this, e2]
    · have hk' : k = seen.length := by omega
      subst hk'
      have : UInt64.ofNat seen.length = memoCnt mem := by
        apply UInt64.toNat_inj.mp; rw [UInt64.toNat_ofNat']; omega
      simp only [this, ite_true, List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem_cons_zero]
      exact ⟨hx, by simp⟩
  · rw [Std.HashMap.getElem?_insert] at he'
    simp only [List.mem_append, List.mem_singleton]
    split at he'
    · rename_i heq; right; exact (by simpa using heq : e = e').symm
    · left; exact h.keys e' he'
  · simp only [mpushOld, Mem.size_arr64_set64, Mem.arr64_set64_ne _ _ _ _ _ (show CTL ≠ RMEMO by decide)]
    exact h.csz

theorem MemoR.push {mem : Mem} {seen : List ConLeche.Expr} {m : EMemo} (h : MemoR mem seen m)
    {e : ConLeche.Expr} (he : e ∉ seen) (x : Word)
    (hx : x.toNat < 2 ^ 32) (hsz' : memoCnt mem < mem.len64 RMEMO) :
    MemoR (mpushMem mem x) (seen ++ [e]) (m.insert e (decI x)) := by
  have hf := mpushPut_frame mem x
  obtain ⟨hc, hl, hR⟩ := mpushPut_memo mem x
  have h1 := h.of_eq hR hc (hf.2.2.1 CTL)
  have := h1.push0 he x hx (by rw [hc, hl]; exact hsz')
  simpa only [mpushOld, mpushMem] using this

/-! ## The handle set `RSET` holds every memo entry -/

/-- **`RSET` holds the memo's handles**: a memo-library table (`MemoRG`) whose map contains the
handle of every memo entry. A probe miss for `h` then means `h` is no entry. -/
def RsetR (mem : Mem) : Prop :=
  ∃ mp : Std.HashMap EIdx Unit, MemoRG rsetSch bmKey (fun _ => ()) mem mp ∧
    ∀ k, k < (memoCnt mem).toNat → (decE (rdW (mem.arr64 RMEMO) (UInt64.ofNat k))) ∈ mp

theorem rsetSch_wf : rsetSch.WF := ⟨by decide, by decide⟩

theorem RsetR.frame {A : List ArrId} {C : List Word} {mem mem' : Mem} (h : RsetR mem)
    (hf : MemFrame A C mem mem') (hA1 : RSET ∉ A) (hA2 : RMEMO ∉ A) (hC1 : (148 : Word) ∉ C)
    (hC2 : (132 : Word) ∉ C) : RsetR mem' := by
  obtain ⟨mp, hR, hc⟩ := h
  have hR' := memoRG_frame rsetSch rsetSch_wf bmKey (fun _ => ()) A C hA1 hC1 mem mem' hf mp hR
  have hM : mem'.arr64 RMEMO = mem.arr64 RMEMO := hf.1 RMEMO hA2 (by decide)
  have hK : memoCnt mem' = memoCnt mem := hf.2.1 132 hC2
  exact ⟨mp, hR', fun k hk => by rw [hM]; rw [hK] at hk; exact hc k hk⟩

theorem RsetR.frameS {mem mem' : Mem} (h : RsetR mem) (hf : MemFrame StoreA StoreC mem mem') :
    RsetR mem' :=
  h.frame hf (by decide) (by decide) (not_mem_storeC _ (by decide))
    (not_mem_storeC _ (by decide))

theorem RsetR.frameR {mem mem' : Mem} (h : RsetR mem) (hf : MemFrame RomA RomC mem mem') :
    RsetR mem' :=
  h.frame hf (by decide) (by decide)
    (by simp only [RomC, List.mem_cons, not_or]; exact ⟨by decide, not_mem_storeC _ (by decide)⟩)
    (by simp only [RomC, List.mem_cons, not_or]; exact ⟨by decide, not_mem_storeC _ (by decide)⟩)

/-- **A probe miss means no memo entry**: under `RsetR`, if `memo_push`'s checks passed for `h`,
no entry of the memo is `h`. -/
theorem RsetR.miss {mem : Mem} {h : Word} (hR : RsetR mem) (hh : h.toNat < 2 ^ 32) (hok : rsetOK mem h)
    (k : Nat) (hk : k < (memoCnt mem).toNat) : rdW (mem.arr64 RMEMO) (UInt64.ofNat k) ≠ h := by
  obtain ⟨mp, hG, hc⟩ := hR
  obtain ⟨h1, h2⟩ := hok
  have hn := memoRG_miss rsetSch bmKey (fun _ => ()) mem mp hG h 0 ⟨hh, rfl⟩ h1 h2
  intro he
  have := hc k hk
  rw [he] at this
  simp only [bmKey] at hn
  exact absurd (Std.HashMap.mem_iff_isSome_getElem?.mp this) (by simp [hn])

theorem RsetR.push {mem mem' : Mem} {h : Word} (hR : RsetR mem) (hh : h.toNat < 2 ^ 32)
    (hW : mpushW mem h = some mem') : RsetR mem' := by
  obtain ⟨mp, hG, hc⟩ := hR
  have hW' := hW
  unfold mpushW at hW
  split at hW; · cases hW
  rename_i h1
  split at hW; · cases hW
  rename_i h2
  split at hW; · cases hW
  rename_i m₁ hput
  split at hW
  case isFalse => cases hW
  cases hW
  have hset : msetG rsetSch mem h 0 1 = some m₁ := by
    simp only [msetG, h1, ite_false]
    have : (mfindG rsetSch mem h 0).headD 0 = 0 := by simpa using h2
    rw [this]; exact hput
  have hG1 := memoRG_set rsetSch rsetSch_wf bmKey (fun _ => ()) mem mp hG h 0 1 ⟨hh, rfl⟩ m₁ hset
  rename_i hsz
  have hf1 := mputG_frame rsetSch rsetSch_wf mem m₁ _ _ _ _ _ hput
  have hc1 : memoCnt m₁ = memoCnt mem := hf1.2.1 132 (by simp [rsetSch])
  have hR1 : m₁.arr64 RMEMO = mem.arr64 RMEMO := hf1.1 RMEMO (by simp [rsetSch, RSET, RMEMO]) (by decide)
  have hf2 : MemFrame [RMEMO] [132] m₁ ((m₁.set64 RMEMO (memoCnt m₁) h).set64 CTL 132 (memoCnt m₁ + 1)) :=
    ((MemFrame.set64 _ RMEMO (by decide) _ _).mono (by simp) (by simp)).trans
      ((MemFrame.setCtl _ 132 _).mono (by simp) (by simp))
  have hG2 := memoRG_frame rsetSch rsetSch_wf bmKey (fun _ => ()) [RMEMO] [132] (by simp [rsetSch, RSET, RMEMO])
    (by simp [rsetSch]) _ _ hf2 _ hG1
  refine ⟨_, hG2, fun k hk => ?_⟩
  have hl := UInt64.lt_iff_toNat_lt.mp hsz
  simp only [Mem.len64, UInt64.toNat_ofNat'] at hl
  have hsz' : (memoCnt m₁).toNat < (m₁.arr64 RMEMO).size := Nat.lt_of_lt_of_le hl (Nat.mod_le _ _)
  have hroom : (memoCnt m₁).toNat + 1 < 2 ^ 64 := by
    have := Nat.mod_lt (m₁.arr64 RMEMO).size (show 2 ^ 64 > 0 by decide); omega
  have hcs : 132 < ((m₁.set64 RMEMO (memoCnt m₁) h).arr64 CTL).size := by
    rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
    rw [hf1.2.2.1 CTL]
    have := hG.1
    simp [rsetSch] at this; omega
  have hcnt : memoCnt ((m₁.set64 RMEMO (memoCnt m₁) h).set64 CTL 132 (memoCnt m₁ + 1)) = memoCnt m₁ + 1 := by
    simp only [memoCnt] at hcs ⊢
    simp only [Mem.arr64_set64_same, rdW_set!]
    simp [hcs]
  rw [hcnt, UInt64.toNat_add] at hk
  simp at hk
  simp only [Mem.arr64_set64_ne _ _ _ _ _ (show RMEMO ≠ CTL by decide), Mem.arr64_set64_same, rdW_set!]
  by_cases hkc : k = (memoCnt m₁).toNat
  · subst hkc
    simp [hsz', Std.HashMap.mem_insert, bmKey]
  · have hk' : k < (memoCnt mem).toNat := by rw [← hc1]; omega
    have hne : ¬ (memoCnt m₁).toNat = (UInt64.ofNat k).toNat := by
      rw [UInt64.toNat_ofNat']; rw [Nat.mod_eq_of_lt (by omega)]; omega
    have := hc k hk'
    rw [← hR1] at this
    have hne' : ¬ ((memoCnt m₁).toNat = k % 18446744073709551616) := by
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    simp only [Std.HashMap.mem_insert]
    right
    simpa [hne'] using this

end L.Rom

namespace L.Rom
open L.Arena

/-! ## The twin's arms, as runs -/

section twin
variable (m m₁ m₂ m₃ : EMemo) (a₀ a₁ a₂ a₃ a₄ : AState) (hf ha hb h : EIdx)

theorem iEG_hit (e : ConLeche.Expr) (hc : ∀ x, e ≠ .bvar x ∧ (∀ u, e ≠ .sort u) ∧ (∀ n us, e ≠ .const n us) ∧ ∀ l, e ≠ .lit l)
    (hm : m[e]? = some h) : (internExprGo m e).run a₀ = .ok ((m, h), a₀) := by
  cases e with
  | bvar x => exact absurd rfl (hc x).1
  | sort u => exact absurd rfl ((hc 0).2.1 u)
  | const n us => exact absurd rfl ((hc 0).2.2.1 n us)
  | lit l => exact absurd rfl ((hc 0).2.2.2 l)
  | _ => simp [internExprGo, hm] <;> rfl

/-- The `app`, `lam` and `forallE` arms (`hC` by `rfl`). -/
theorem iEG_two (C : ConLeche.Expr → ConLeche.Expr → ConLeche.Expr) (CI : EIdx → EIdx → ENodeView)
    (f x : ConLeche.Expr) (hC : ∀ m, internExprGo m (C f x) = match m[C f x]? with
      | some h => pure (m, h)
      | none => do
        let (m, hf) ← internExprGo m f
        let (m, ha) ← internExprGo m x
        let h ← internE (CI hf ha)
        pure (m.insert (C f x) h, h))
    (hm : m[C f x]? = none)
    (r1 : (internExprGo m f).run a₀ = .ok ((m₁, hf), a₁))
    (r2 : (internExprGo m₁ x).run a₁ = .ok ((m₂, ha), a₂))
    (r3 : (internE (CI hf ha)).run a₂ = .ok (h, a₃)) :
    (internExprGo m (C f x)).run a₀ = .ok ((m₂.insert (C f x) h, h), a₃) := by
  simp only [hC, hm, StateT.run_bind, r1]
  simp only [bind, Except.bind]
  rw [r2]; simp only
  rw [r3]; rfl

theorem iEG_let (t v b : ConLeche.Expr) (hm : m[ConLeche.Expr.letE t v b]? = none)
    (r1 : (internExprGo m t).run a₀ = .ok ((m₁, hf), a₁))
    (r2 : (internExprGo m₁ v).run a₁ = .ok ((m₂, ha), a₂))
    (r3 : (internExprGo m₂ b).run a₂ = .ok ((m₃, hb), a₃))
    (r4 : (internE (.letE hf ha hb)).run a₃ = .ok (h, a₄)) :
    (internExprGo m (.letE t v b)).run a₀ = .ok ((m₃.insert (.letE t v b) h, h), a₄) := by
  simp only [internExprGo, hm, StateT.run_bind, r1]
  simp only [bind, Except.bind]
  rw [r2]; simp only
  rw [r3]; simp only
  rw [r4]; rfl

theorem iEG_fvar (i : Nat) (ty : ConLeche.Expr) (hm : m[ConLeche.Expr.fvar i ty]? = none)
    (r1 : (internExprGo m ty).run a₀ = .ok ((m₁, hf), a₁))
    (r2 : (internE (.fvar i hf)).run a₁ = .ok (h, a₂)) :
    (internExprGo m (.fvar i ty)).run a₀ = .ok ((m₁.insert (.fvar i ty) h, h), a₂) := by
  simp only [internExprGo, hm, StateT.run_bind, r1]
  simp only [bind, Except.bind]
  rw [r2]; rfl

theorem iEG_proj (nm : ConLeche.Name) (i : Nat) (sub : ConLeche.Expr) (hn : NIdx)
    (hm : m[ConLeche.Expr.proj nm i sub]? = none)
    (r0 : (internName nm).run a₀ = .ok (hn, a₁))
    (r1 : (internExprGo m sub).run a₁ = .ok ((m₁, hf), a₂))
    (r2 : (internE (.proj hn i hf)).run a₂ = .ok (h, a₃)) :
    (internExprGo m (.proj nm i sub)).run a₀ = .ok ((m₁.insert (.proj nm i sub) h, h), a₃) := by
  simp only [internExprGo, hm, StateT.run_bind, r0]
  simp only [bind, Except.bind]
  rw [r1]; simp only
  rw [r2]; rfl

theorem iEG_lit (l : ConLeche.Literal) (r : (internE (.lit l)).run a₀ = .ok (h, a₁)) :
    (internExprGo m (.lit l)).run a₀ = .ok ((m, h), a₁) := by
  simp only [internExprGo, StateT.run_bind, r]; rfl

theorem iEG_bvar (i : Nat) (r : (internE (.bvar i)).run a₀ = .ok (h, a₁)) :
    (internExprGo m (.bvar i)).run a₀ = .ok ((m, h), a₁) := by
  simp only [internExprGo, StateT.run_bind, r]; rfl

theorem iEG_sort (u : ConLeche.Level) (hu : LIdx) (r0 : (internLevel u).run a₀ = .ok (hu, a₁))
    (r : (internE (.sort hu)).run a₁ = .ok (h, a₂)) :
    (internExprGo m (.sort u)).run a₀ = .ok ((m, h), a₂) := by
  simp only [internExprGo, StateT.run_bind, r0]
  simp only [bind, Except.bind]
  rw [r]; rfl

theorem iEG_const (nm : ConLeche.Name) (us : List ConLeche.Level) (hn : NIdx) (hus : LsIdx)
    (r0 : (internName nm).run a₀ = .ok (hn, a₁)) (r1 : (internLevels us).run a₁ = .ok (hus, a₂))
    (r : (internE (.const hn hus)).run a₂ = .ok (h, a₃)) :
    (internExprGo m (.const nm us)).run a₀ = .ok ((m, h), a₃) := by
  simp only [internExprGo, StateT.run_bind, r0]
  simp only [bind, Except.bind]
  rw [r1]; simp only
  rw [r]; rfl

end twin

/-! ## The refinement -/

/-- Every datum of the expression fits its encoding; no string literal. -/
def exprFits : ConLeche.Expr → Bool
  | .bvar i => decide (i < 2 ^ 64)
  | .sort u => levelFits u
  | .const n us => nameFits n && us.all levelFits && decide (us.length < 2 ^ 60)
  | .lit (.natVal n) => decide (n < 2 ^ 64)
  | .lit (.strVal _) => false
  | .fvar i ty => decide (i < 2 ^ 64) && exprFits ty
  | .app f a | .lam f a | .forallE f a => exprFits f && exprFits a
  | .letE t v b => exprFits t && exprFits v && exprFits b
  | .proj n i e => nameFits n && decide (i < 2 ^ 64) && exprFits e

theorem exNodeK_inv {q h q' : Word} {mem' : Mem} {x : Option (Word × Mem)}
    (hW : exNodeK q x = some (h, q', mem')) :
    ∃ m₃, x = some (h, m₃) ∧ h.toNat < 2 ^ 32 ∧ q' = q ∧
      memoCnt m₃ < m₃.len64 RMEMO ∧ mpushW m₃ h = some mem' ∧ mem' = mpushMem m₃ h := by
  match x, hW with
  | some (r, m₃), hW =>
    simp only [exNodeK] at hW
    split at hW
    · simp at hW
    rename_i hlt
    split at hW
    · simp at hW
    rename_i m'' hp
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl, rfl⟩ := hW
    obtain ⟨hsz, -, he⟩ := mpushW_eq hp
    exact ⟨m₃, rfl, by simp at hlt; exact UInt64.lt_iff_toNat_lt.mp hlt, rfl, hsz, hp, he⟩

theorem exLeafK_inv {q h q' : Word} {mem' : Mem} {x : Option (Word × Mem)}
    (hW : exLeafK q x = some (h, q', mem')) : x = some (h, mem') ∧ h.toNat < 2 ^ 32 ∧ q' = q := by
  match x, hW with
  | some (r, m₃), hW =>
    simp only [exLeafK] at hW
    split at hW
    · simp at hW
    rename_i hlt
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl, rfl⟩ := hW
    exact ⟨rfl, by simp at hlt; exact UInt64.lt_iff_toNat_lt.mp hlt, rfl⟩

theorem mpushMem_frame1 (m : Mem) (h : Word) : MemFrame [RMEMO, RSET] [132, 149] m (mpushMem m h) := by
  simp only [mpushMem]
  exact (((mpushPut_frame m h).mono (by simp)
    (by simp)).trans ((MemFrame.set64 _ RMEMO (by decide) _ _).mono (by simp) (by simp))).trans
    ((MemFrame.setCtl _ 132 _).mono (by simp) (by simp))

theorem mpushMem_frame (m : Mem) (h : Word) : MemFrame ExprA ExprC m (mpushMem m h) :=
  (mpushMem_frame1 m h).mono (by simp [ExprA]) (by simp [ExprC])

theorem mpushMem_stk (m : Mem) (h : Word) : stkTop (mpushMem m h) = stkTop m :=
  (mpushMem_frame1 m h).2.1 131 (by simp)

theorem frame_exprA_stk {m m' : Mem} (hf : MemFrame StoreA StoreC m m') : stkTop m' = stkTop m :=
  hf.2.1 131 (not_mem_storeC _ (by decide))

/-- The encoder adds to `seen` only subterms of the expression it encodes. -/
theorem encExprM_seen (e : ConLeche.Expr) :
    ∀ (seen : List ConLeche.Expr) (x : ConLeche.Expr), x ∈ (encExprM seen e).2 →
      x ∈ seen ∨ sizeOf x ≤ sizeOf e := by
  induction e with
  | bvar i => intro seen x hx; exact .inl (by simpa [encExprM] using hx)
  | sort u => intro seen x hx; exact .inl (by simpa [encExprM] using hx)
  | const n us => intro seen x hx; exact .inl (by simpa [encExprM] using hx)
  | lit l => intro seen x hx; cases l <;> exact .inl (by simpa [encExprM] using hx)
  | fvar i ty ih =>
    intro seen x hx
    simp only [encExprM] at hx
    split at hx
    · exact .inl hx
    · simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · rcases ih seen x hx with h | h
        · exact .inl h
        · right; simp; omega
      · exact .inr (Nat.le_refl _)
  | app f a ihf iha =>
    intro seen x hx
    simp only [encExprM] at hx
    split at hx
    · exact .inl hx
    · simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · rcases iha _ x hx with h | h
        · rcases ihf seen x h with h | h
          · exact .inl h
          · right; simp; omega
        · right; simp; omega
      · exact .inr (Nat.le_refl _)
  | lam f a ihf iha =>
    intro seen x hx
    simp only [encExprM] at hx
    split at hx
    · exact .inl hx
    · simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · rcases iha _ x hx with h | h
        · rcases ihf seen x h with h | h
          · exact .inl h
          · right; simp; omega
        · right; simp; omega
      · exact .inr (Nat.le_refl _)
  | forallE f a ihf iha =>
    intro seen x hx
    simp only [encExprM] at hx
    split at hx
    · exact .inl hx
    · simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · rcases iha _ x hx with h | h
        · rcases ihf seen x h with h | h
          · exact .inl h
          · right; simp; omega
        · right; simp; omega
      · exact .inr (Nat.le_refl _)
  | letE t v b iht ihv ihb =>
    intro seen x hx
    simp only [encExprM] at hx
    split at hx
    · exact .inl hx
    · simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · rcases ihb _ x hx with h | h
        · rcases ihv _ x h with h | h
          · rcases iht seen x h with h | h
            · exact .inl h
            · right; simp; omega
          · right; simp; omega
        · right; simp; omega
      · exact .inr (Nat.le_refl _)
  | proj n i sub ih =>
    intro seen x hx
    simp only [encExprM] at hx
    split at hx
    · exact .inl hx
    · simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · rcases ih seen x hx with h | h
        · exact .inl h
        · right; simp; omega
      · exact .inr (Nat.le_refl _)

section main
variable (rom : List UInt8) (hr : RomOK rom)
include hr

/-- The conclusion of the refinement at `e`. -/
def ExprPost (e : ConLeche.Expr) (seen : List ConLeche.Expr) (mem : Mem) (a : AState) (m : EMemo)
    (pos h q : Word) (mem' : Mem) : Prop :=
  ∃ (m' : EMemo) (a' : AState), (internExprGo m e).run a = .ok ((m', decI h), a') ∧ ArenaD mem' a' ∧
    MemoR mem' (encExprM seen e).2 m' ∧ h.toNat < 2 ^ 32 ∧
    q.toNat = pos.toNat + (encExprM seen e).1.length ∧ MemFrame ExprA ExprC mem mem' ∧
    stkTop mem' = stkTop mem ∧ (RsetR mem → RsetR mem')

/-- The prefix `t :: _` at `pos`: the bytes after the tag. -/
theorem drop_tag {pos : Word} {t : UInt8} {bs rest : List UInt8}
    (hd : rom.drop pos.toNat = (t :: bs) ++ rest) :
    rom.drop (pos + 1).toNat = bs ++ rest ∧ (pos + 1).toNat = pos.toNat + 1 := by
  have hp1 := drop_pos rom hr pos _ rest hd 1 (by simp)
  simp only [UInt64.ofNat_one] at hp1
  exact ⟨by simpa using drop_shift rom hr pos [t] bs rest (by simpa using hd) (pos + 1) hp1, hp1⟩

/-- A compound subterm the memo already holds: a back reference. -/
theorem ref_case (e : ConLeche.Expr)
    (hc : ∀ x, e ≠ .bvar x ∧ (∀ u, e ≠ .sort u) ∧ (∀ n us, e ≠ .const n us) ∧ ∀ l, e ≠ .lit l)
    (henc : ∀ seen, e ∈ seen → encExprM seen e = (9 :: u64B (seen.idxOf e), seen))
    (n : Nat) (mem : Mem) (a : AState) (pos : Word) (rest : List UInt8) (seen : List ConLeche.Expr)
    (m : EMemo) (h q : Word) (mem' : Mem) (hA : ArenaD mem a) (hM : MemoR mem seen m)
    (hin : e ∈ seen) (hd : rom.drop pos.toNat = (encExprM seen e).1 ++ rest)
    (hW : romExprW rom n mem pos = some (h, q, mem')) :
    ExprPost e seen mem a m pos h q mem' := by
  unfold ExprPost
  rw [henc seen hin] at hd ⊢
  have h0 : romB rom pos = 9 := romB_head rom hr pos 9 _ rest hd
  cases n with
  | zero => simp [romExprW] at hW
  | succ n =>
  rw [romExprW_ref rom n mem pos h0] at hW
  have hidx := List.idxOf_lt_length_iff.mpr hin
  have hroom := hM.room
  have hd1 : rom.drop (pos + 1).toNat = u64B (seen.idxOf e) ++ rest := by
    simpa using (drop_tag (bs := (u64B (seen.idxOf e))) rom hr (by simpa using hd)).1
  have hu := u64W_of_drop rom (pos + 1) _ _ hd1 (by omega) hr
  simp only [romRefW, hu] at hW
  split at hW
  case isFalse => simp at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨rfl, rfl, rfl⟩ := hW
  obtain ⟨hlt, hm⟩ := hM.hit hin
  refine ⟨m, a, iEG_hit m a _ e hc hm, hA, hM, hlt, ?_, MemFrame.refl _ _ _, rfl, id⟩
  have hp := drop_pos rom hr pos _ rest hd 9 (by simp [u64B])
  simp only [show UInt64.ofNat 9 = (9 : Word) from rfl] at hp
  rw [hp]; simp [u64B]

/-- The statement of `romExprW_ok` at `e`. -/
def ExprStmt (e : ConLeche.Expr) : Prop :=
  ∀ (n : Nat) (mem : Mem) (a : AState) (pos : Word) (rest : List UInt8) (seen : List ConLeche.Expr)
    (m : EMemo) (h q : Word) (mem' : Mem), ArenaD mem a → ModeOK mem → MemoR mem seen m →
    rom.drop pos.toNat = (encExprM seen e).1 ++ rest → (stkTop mem).toNat < 2 ^ 61 →
    131 < (mem.arr64 CTL).size → romExprW rom n mem pos = some (h, q, mem') →
    ExprPost e seen mem a m pos h q mem'

/-- **The `app`, `lam` and `forallE` arms**: two children, then the node `mkW` interns. -/
theorem two_case (C : ConLeche.Expr → ConLeche.Expr → ConLeche.Expr) (CI : EIdx → EIdx → ENodeView)
    (b : UInt8) (hb : b = 5 ∨ b = 6 ∨ b = 7) (mkW : Mem → Word → Word → Option (Word × Mem))
    (htwo : ∀ a c q m, exTwoK b.toUInt64 a (some (c, q, m)) = exNodeK q (mkW m a c))
    (hok : ∀ m a, ArenaD m a → ∀ f x r m', mkW m f x = some (r, m') →
      AM.ok (internE (CI (decE f) (decE x))) a ∧ ArenaD m' (AM.st (internE (CI (decE f) (decE x))) a) ∧
      AM.res (internE (CI (decE f) (decE x))) a = decE r)
    (hsto : ∀ {m m' f x r}, mkW m f x = some (r, m') → MemFrame StoreA StoreC m m')
    (f x : ConLeche.Expr)
    (hiEG : ∀ (m m₁ m₂ : EMemo) (a₀ a₁ a₂ a₃ : AState) (hf ha h : EIdx), m[C f x]? = none →
      (internExprGo m f).run a₀ = .ok ((m₁, hf), a₁) → (internExprGo m₁ x).run a₁ = .ok ((m₂, ha), a₂) →
      (internE (CI hf ha)).run a₂ = .ok (h, a₃) →
      (internExprGo m (C f x)).run a₀ = .ok ((m₂.insert (C f x) h, h), a₃))
    (hfit : exprFits (C f x) = (exprFits f && exprFits x))
    (henc : ∀ seen, C f x ∉ seen → encExprM seen (C f x) =
      (b :: ((encExprM seen f).1 ++ (encExprM (encExprM seen f).2 x).1), (encExprM (encExprM seen f).2 x).2 ++ [C f x]))
    (hin9 : ∀ seen, C f x ∈ seen → encExprM seen (C f x) = (9 :: u64B (seen.idxOf (C f x)), seen))
    (hc : ∀ i, C f x ≠ .bvar i ∧ (∀ u, C f x ≠ .sort u) ∧ (∀ n us, C f x ≠ .const n us) ∧ ∀ l, C f x ≠ .lit l)
    (hsf : sizeOf f < sizeOf (C f x)) (hsx : sizeOf x < sizeOf (C f x))
    (he : exprFits (C f x) = true) (ihf : exprFits f = true → ExprStmt rom f)
    (ihx : exprFits x = true → ExprStmt rom x) : ExprStmt rom (C f x) := by
  intro n mem a pos rest seen m h q mem' hA hmo hM hd hst hcs hW
  rw [hfit, Bool.and_eq_true] at he
  by_cases hin : C f x ∈ seen
  · exact ref_case rom hr _ hc (hin9) n mem a pos rest seen m h q mem' hA hM hin hd hW
  unfold ExprPost
  rw [henc seen hin] at hd ⊢
  have h0 : romB rom pos = b.toUInt64 := romB_head rom hr pos b _ rest hd
  cases n with
  | zero => simp [romExprW] at hW
  | succ n =>
  rw [romExprW_two rom n mem pos (by rcases hb with rfl | rfl | rfl <;> simp [h0])
    (by rcases hb with rfl | rfl | rfl <;> simp [h0]) (by rcases hb with rfl | rfl | rfl <;> simp [h0]), h0] at hW
  cases n with
  | zero => simp [romTwoW] at hW
  | succ n =>
  rw [romTwoW_eq] at hW
  obtain ⟨hd1, hp1⟩ := drop_tag rom hr (by simpa using hd)
  cases hF : romExprW rom n mem (pos + 1) with
  | none => rw [hF] at hW; simp [exOneK] at hW
  | some r =>
  obtain ⟨hf, q₁, m₁⟩ := r
  rw [hF, exOneK_two (ht := by rcases hb with rfl | rfl | rfl <;> decide)] at hW
  obtain ⟨mf, a₁, r1, hR1, hM1, hlt1, hq1, hf1, hs1, hz1⟩ :=
    ihf he.1 n mem a (pos + 1) ((encExprM (encExprM seen f).2 x).1 ++ rest) seen m hf q₁ m₁ hA hmo hM
      hd1 hst hcs hF
  have hd2 := drop_shift rom hr (pos + 1) _ _ rest (by rw [hd1, List.append_assoc]) q₁ hq1
  cases hX : romExprW rom n m₁ q₁ with
  | none => rw [hX] at hW; simp [exTwoK] at hW
  | some r =>
  obtain ⟨hx, q₂, m₂⟩ := r
  rw [hX, htwo] at hW
  obtain ⟨mx, a₂, r2, hR2, hM2, hlt2, hq2, hf2, hs2, hz2⟩ := ihx he.2 n m₁ a₁ q₁ rest _ mf hx q₂ m₂ hR1
    (((romExprW_topK rom n).1 _ _ _ _ _ hF).mode hA.1.lit.1 hmo) hM1 hd2
    (by rw [hs1]; exact hst) (by rw [hf1.2.2.1]; exact hcs) hX
  obtain ⟨m₃, hI, hlt, rfl, hsz, hpw, rfl⟩ := exNodeK_inv hW
  obtain ⟨ok3, hR3, res3⟩ := hok m₂ a₂ hR2 hf hx h m₃ hI
  have hf3 := hsto hI
  have hfresh : C f x ∉ (encExprM (encExprM seen f).2 x).2 := by
    intro hm
    rcases encExprM_seen x _ _ hm with hm | hm
    · rcases encExprM_seen f _ _ hm with hm | hm
      · exact hin hm
      · omega
    · omega
  refine ⟨_, _, hiEG m mf mx a a₁ a₂ _ (decI hf) (decI hx) (decI h) (hM.miss hin) r1 r2
      (by rw [show (decI h : EIdx) = _ from res3.symm]; exact AM.run_of_ok _ _ ok3),
    ArenaD.frameHi (mpushMem_frame1 m₃ h) (by simp [RMEMO, RSET]) (by simp) hR3,
    (hM2.frame (frame_romA hf3)).push hfresh h hlt hsz, hlt, ?_, ?_, ?_, ?_⟩
  · rw [hq2, hq1, hp1]; simp; omega
  · exact hf1.trans (hf2.trans ((frame_storeE hf3).trans (mpushMem_frame m₃ h)))
  · rw [mpushMem_stk, frame_exprA_stk hf3, hs2, hs1]
  · exact fun hz => RsetR.push ((hz2 (hz1 hz)).frameS hf3) hlt hpw

set_option linter.constructorNameAsVariable false in
/-- **The model of `rom_expr` refines `internExprGo`.** -/
theorem romExprW_ok (e : ConLeche.Expr) (he : exprFits e = true) :
    ∀ (n : Nat) (mem : Mem) (a : AState) (pos : Word) (rest : List UInt8) (seen : List ConLeche.Expr)
      (m : EMemo) (h q : Word) (mem' : Mem), ArenaD mem a → ModeOK mem → MemoR mem seen m →
      rom.drop pos.toNat = (encExprM seen e).1 ++ rest → (stkTop mem).toNat < 2 ^ 61 →
      131 < (mem.arr64 CTL).size → romExprW rom n mem pos = some (h, q, mem') →
      ExprPost e seen mem a m pos h q mem' := by
  induction e with
  | bvar i =>
    intro n mem a pos rest seen m h q mem' hA hmo hM hd hst hc hW
    simp only [exprFits, decide_eq_true_eq] at he
    unfold ExprPost
    simp only [encExprM] at hd ⊢
    have h0 : romB rom pos = 0 := romB_head rom hr pos 0 _ rest hd
    cases n with
    | zero => simp [romExprW] at hW
    | succ n =>
    rw [romExprW_leaf rom n mem pos (by simp [h0]) (by simp [h0]), h0] at hW
    cases n with
    | zero => simp [romLeafW] at hW
    | succ n =>
    have hd1 : rom.drop (pos + 1).toNat = u64B i ++ rest := by
      simpa using (drop_tag (bs := (u64B i)) rom hr (by simpa using hd)).1
    rw [romLeafW_bvar rom n mem pos 0 rfl (u64OK_of_drop rom _ _ _ hd1 hr)] at hW
    rw [u64W_of_drop rom (pos + 1) _ _ hd1 he hr] at hW
    obtain ⟨hI, hlt, rfl⟩ := exLeafK_inv hW
    obtain ⟨ok, hR, res⟩ := internBVar_D mem a hA _ h mem' hI
    have hiN : (UInt64.ofNat i).toNat = i := by rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt he
    rw [hiN] at ok hR res
    have hf := binternW_store hI
    refine ⟨m, _, iEG_bvar m a _ (decE h) i (by rw [← res]; exact AM.run_of_ok _ _ ok), hR,
      hM.frame (frame_romA hf), hlt, ?_, frame_storeE hf, frame_exprA_stk hf, fun hz => hz.frameS hf⟩
    have hp := drop_pos rom hr pos _ rest hd 9 (by simp [u64B])
    simp only [show UInt64.ofNat 9 = (9 : Word) from rfl] at hp
    rw [hp]; simp [u64B]
  | sort u =>
    intro n mem a pos rest seen m h q mem' hA hmo hM hd hst hc hW
    simp only [exprFits] at he
    unfold ExprPost
    simp only [encExprM] at hd ⊢
    have h0 : romB rom pos = 1 := romB_head rom hr pos 1 _ rest hd
    cases n with
    | zero => simp [romExprW] at hW
    | succ n =>
    rw [romExprW_leaf rom n mem pos (by simp [h0]) (by simp [h0]), h0] at hW
    cases n with
    | zero => simp [romLeafW] at hW
    | succ n =>
    rw [romLeafW_sort rom n mem pos 1 (by simp) rfl] at hW
    have hd1 : rom.drop (pos + 1).toNat = encLevel u ++ rest := by
      simpa using (drop_tag (bs := (encLevel u)) rom hr (by simpa using hd)).1
    cases hU : romLevelW rom n mem (pos + 1) with
    | none => rw [hU] at hW; simp [exSortK] at hW
    | some r =>
    obtain ⟨hu, q₁, m₁⟩ := r
    rw [hU, exSortK_some] at hW
    obtain ⟨ok1, hR1, res1, hlt1, hq1, hf1⟩ := romLevelW_ok rom hr u he n mem a (pos + 1) rest hu q₁ m₁ hA hmo hd1 hU
    obtain ⟨hI, hlt, rfl⟩ := exLeafK_inv hW
    obtain ⟨ok2, hR2, res2, hf2⟩ := L.Front.internSort_D m₁ _ hR1 h mem' hu hlt1 hI
    rw [← res1] at ok2 hR2 res2
    refine ⟨m, _, iEG_sort m a _ _ (decI h) u _ (AM.run_of_ok _ _ ok1)
      (by rw [show (decI h : EIdx) = AM.res (internE (.sort (AM.res (internLevel u) a))) (AM.st (internLevel u) a)
            from res2.symm]; exact AM.run_of_ok _ _ ok2), hR2,
      (hM.frame (frame_romA hf1)).frame (frame_romA (frame_store hf2 (by simp [sortSch, SOREC, SOSLOT, SOLP])
        (by simp [sortSch]))), hlt, ?_, ?_, ?_, ?_⟩
    · rw [hq1, (drop_tag rom hr hd).2]; simp; omega
    · exact frame_storeE (hf1.trans (frame_store hf2 (by simp [sortSch, SOREC, SOSLOT, SOLP]) (by simp [sortSch])))
    · exact frame_exprA_stk (hf1.trans (frame_store hf2 (by simp [sortSch, SOREC, SOSLOT, SOLP]) (by simp [sortSch])))
    · exact fun hz => hz.frameS (hf1.trans (frame_store hf2 (by simp [sortSch, SOREC, SOSLOT, SOLP]) (by simp [sortSch])))
  | const nm us =>
    intro n mem a pos rest seen m h q mem' hA hmo hM hd hst hc hW
    simp only [exprFits, Bool.and_eq_true, decide_eq_true_eq] at he
    obtain ⟨⟨hn, hus⟩, hlen⟩ := he
    unfold ExprPost
    simp only [encExprM] at hd ⊢
    have h0 : romB rom pos = 2 := romB_head rom hr pos 2 _ rest hd
    cases n with
    | zero => simp [romExprW] at hW
    | succ n =>
    rw [romExprW_leaf rom n mem pos (by simp [h0]) (by simp [h0]), h0] at hW
    cases n with
    | zero => simp [romLeafW] at hW
    | succ n =>
    rw [romLeafW_const rom n mem pos 2 (by simp) (by simp) rfl] at hW
    have hd1 : rom.drop (pos + 1).toNat = encName nm ++ (encLevels us ++ rest) := by
      simpa using (drop_tag (bs := (encName nm ++ encLevels us)) rom hr (by simpa using hd)).1
    cases hN : romNameW rom n mem (pos + 1) with
    | none => rw [hN] at hW; simp [exConst2KN] at hW
    | some r =>
    obtain ⟨hnm, q₁, m₁⟩ := r
    rw [hN, exConst2KN_some] at hW
    obtain ⟨ok1, hR1, res1, hlt1, hq1, hf1⟩ := romNameW_ok rom hr nm hn n mem a (pos + 1) _ hnm q₁ m₁ hA hmo hd1 hN
    have hd2 : rom.drop q₁.toNat = encLevels us ++ rest :=
      drop_shift rom hr (pos + 1) (encName nm) (encLevels us) rest (by rw [hd1, List.append_assoc]) q₁ hq1
    have hst1 : stkTop m₁ = stkTop mem := frame_exprA_stk hf1
    cases hL : romLevelsW rom n m₁ q₁ with
    | none => rw [hL] at hW; simp [exConst2K] at hW
    | some r =>
    obtain ⟨hl, q₂, m₂⟩ := r
    rw [hL, exConst2K_some] at hW
    obtain ⟨ok2, hR2, res2, hlt2, hq2, hf2, hst2⟩ := romLevelsW_ok rom hr us hus n m₁ _ q₁ rest hl q₂ m₂ hR1
      ((romNameW_topK hN).mode hA.1.lit.1 hmo) hd2
      (by rw [hst1]; omega) (by rw [hf1.2.2.1]; exact hc) hL
    obtain ⟨hI, hlt, rfl⟩ := exLeafK_inv hW
    obtain ⟨ok3, hR3, res3, hf3⟩ := L.Front.internConst_D m₂ _ hR2 h mem' hnm hl hlt1 hlt2 hI
    rw [← res1, ← res2] at ok3 hR3 res3
    have hf3' := frame_store hf3 (by simp [constSch, CREC, CSLOT, CLP]) (by simp [constSch])
    refine ⟨m, _, iEG_const m a _ _ _ (decI h) nm us _ _ (AM.run_of_ok _ _ ok1) (AM.run_of_ok _ _ ok2)
      (by rw [show (decI h : EIdx) = _ from res3.symm]; exact AM.run_of_ok _ _ ok3), hR3,
      ((hM.frame (frame_romA hf1)).frame hf2).frame (frame_romA hf3'), hlt, ?_, ?_, ?_, ?_⟩
    · rw [hq2, hq1, (drop_tag rom hr hd).2]; simp; omega
    · exact (frame_storeE hf1).trans ((frame_exprA hf2).trans (frame_storeE hf3'))
    · rw [frame_exprA_stk hf3', hst2, hst1]
    · exact fun hz => ((hz.frameS hf1).frameR hf2).frameS hf3'
  | lit l =>
    intro n mem a pos rest seen m h q mem' hA hmo hM hd hst hc hW
    cases l with
    | strVal _ => simp [exprFits] at he
    | natVal k =>
    simp only [exprFits, decide_eq_true_eq] at he
    unfold ExprPost
    simp only [encExprM] at hd ⊢
    have h0 : romB rom pos = 3 := romB_head rom hr pos 3 _ rest hd
    cases n with
    | zero => simp [romExprW] at hW
    | succ n =>
    rw [romExprW_leaf rom n mem pos (by simp [h0]) (by simp [h0]), h0] at hW
    cases n with
    | zero => simp [romLeafW] at hW
    | succ n =>
    have hd1 : rom.drop (pos + 1).toNat = u64B k ++ rest := by
      simpa using (drop_tag (bs := (u64B k)) rom hr (by simpa using hd)).1
    rw [romLeafW_lit rom n mem pos 3 (by simp) (by simp) (by simp) rfl (u64OK_of_drop rom _ _ _ hd1 hr)] at hW
    rw [u64W_of_drop rom (pos + 1) _ _ hd1 he hr] at hW
    obtain ⟨hI, hlt, rfl⟩ := exLeafK_inv hW
    have hkN : (UInt64.ofNat k).toNat = k := by rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt he
    have hpool : PoolOK mem := hA.1.lit.1
    have hq9 : (pos + 9).toNat = pos.toNat + (3 :: u64B k).length := by
      have hp := drop_pos rom hr pos _ rest hd 9 (by simp [u64B])
      simp only [show UInt64.ofNat 9 = (9 : Word) from rfl] at hp
      rw [hp]; simp [u64B]
    simp only [romLitW] at hI
    split at hI
    · cases hI
    rename_i hroom
    split at hI
    · rename_i hk0
      have hk : k = 0 := by have := congrArg UInt64.toNat hk0; rw [hkN] at this; simpa using this
      subst hk
      have hsl0 : SliceOK mem mem.top 0 := by simp only [SliceOK, UInt64.toNat_zero, Nat.add_zero]; omega
      obtain ⟨ok, hR, res, hf⟩ := L.Front.internLit_D mem a hA h mem' mem.top 0
        hsl0 (by simp [Norm]) (ModeOK.slice0 hmo hsl0) hI
      simp only [UInt64.toNat_zero, pv] at ok hR res
      have hf' := frame_store hf (by simp [litSch, REC, SLOT]) (by simp [litSch])
      refine ⟨m, _, iEG_lit m a _ (decE h) _ (by rw [← res]; exact AM.run_of_ok _ _ ok), hR,
        hM.frame (frame_romA hf'), hlt, hq9, frame_storeE hf', frame_exprA_stk hf', fun hz => hz.frameS hf'⟩
    · rename_i hk0
      obtain ⟨hg, hsl, hP1v⟩ := litWordMem_facts mem (UInt64.ofNat k) hpool hroom
      have hA1 := ArenaD.grow _ _ hg _ hA
      obtain ⟨ok, hR, res, hf⟩ := L.Front.internLit_D (litWordMem mem (UInt64.ofNat k)) a hA1 h mem' mem.top 1
        hsl (by intro _; simp [hP1v]; exact hk0) (ModeOK.slice0 (ModeOK.grows hmo hg) hsl) hI
      have hpv : pv (vpool (litWordMem mem (UInt64.ofNat k))) mem.top.toNat (UInt64.toNat 1) = k := by
        simp [pv, hP1v, wt, hkN]
      rw [hpv] at ok hR res
      have hf' := frame_store hf (by simp [litSch, REC, SLOT]) (by simp [litSch])
      have hg' := frame_grows hg
      refine ⟨m, _, iEG_lit m a _ (decE h) _ (by rw [← res]; exact AM.run_of_ok _ _ ok), hR,
        (hM.frame (frame_romA hg')).frame (frame_romA hf'), hlt, hq9,
        (frame_storeE hg').trans (frame_storeE hf'), by rw [frame_exprA_stk hf', frame_exprA_stk hg'],
        fun hz => (hz.frameS hg').frameS hf'⟩
  | app f x ihf ihx =>
    exact two_case rom hr .app .app 5 (by decide) mkAppW (fun _ _ _ _ => by simp [exTwoK]) mkApp_ok
      mkAppW_store f x (iEG_two · · · · · · · · · · .app .app f x fun _ => rfl) rfl (fun seen h => by simp [encExprM, h])
      (fun seen h => by simp [encExprM, h]) (fun _ => ⟨by simp, by simp, by simp, by simp⟩)
      (by simp; omega) (by simp; omega) he ihf ihx
  | lam f x ihf ihx =>
    exact two_case rom hr .lam .lam 6 (by decide) mkLamW (fun _ _ _ _ => by simp [exTwoK]) mkLam_ok
      mkLamW_store f x (iEG_two · · · · · · · · · · .lam .lam f x fun _ => rfl) rfl (fun seen h => by simp [encExprM, h])
      (fun seen h => by simp [encExprM, h]) (fun _ => ⟨by simp, by simp, by simp, by simp⟩)
      (by simp; omega) (by simp; omega) he ihf ihx
  | forallE f x ihf ihx =>
    exact two_case rom hr .forallE .forallE 7 (by decide) mkForallW (fun _ _ _ _ => by simp [exTwoK]) mkForall_ok
      mkForallW_store f x (iEG_two · · · · · · · · · · .forallE .forallE f x fun _ => rfl) rfl (fun seen h => by simp [encExprM, h])
      (fun seen h => by simp [encExprM, h]) (fun _ => ⟨by simp, by simp, by simp, by simp⟩)
      (by simp; omega) (by simp; omega) he ihf ihx
  | letE t v x iht ihv ihx =>
    intro n mem a pos rest seen m h q mem' hA hmo hM hd hst hc hW
    simp only [exprFits, Bool.and_eq_true] at he
    by_cases hin : ConLeche.Expr.letE t v x ∈ seen
    · exact ref_case rom hr _ (fun _ => ⟨by simp, by simp, by simp, by simp⟩)
        (fun seen h => by simp [encExprM, h]) n mem a pos rest seen m h q mem' hA hM hin hd hW
    unfold ExprPost
    have henc : encExprM seen (.letE t v x) = (8 :: ((encExprM seen t).1 ++ (encExprM (encExprM seen t).2 v).1 ++
        (encExprM (encExprM (encExprM seen t).2 v).2 x).1),
        (encExprM (encExprM (encExprM seen t).2 v).2 x).2 ++ [.letE t v x]) := by simp [encExprM, hin]
    rw [henc] at hd ⊢
    have h0 : romB rom pos = 8 := romB_head rom hr pos 8 _ rest hd
    cases n with
    | zero => simp [romExprW] at hW
    | succ n =>
    rw [romExprW_two rom n mem pos (by simp [h0]) (by simp [h0]) (by simp [h0]), h0] at hW
    cases n with
    | zero => simp [romTwoW] at hW
    | succ n =>
    rw [romTwoW_eq] at hW
    have hd1 : rom.drop (pos + 1).toNat = (encExprM seen t).1 ++ ((encExprM (encExprM seen t).2 v).1 ++
        ((encExprM (encExprM (encExprM seen t).2 v).2 x).1 ++ rest)) := by
      simpa using (drop_tag (bs := ((encExprM seen t).1 ++ (encExprM (encExprM seen t).2 v).1 ++
        (encExprM (encExprM (encExprM seen t).2 v).2 x).1)) rom hr (by simpa using hd)).1
    cases hT : romExprW rom n mem (pos + 1) with
    | none => rw [hT] at hW; simp [exOneK] at hW
    | some r =>
    obtain ⟨ht, q₁, m₁⟩ := r
    rw [hT, exOneK_let (ht := rfl)] at hW
    obtain ⟨mt, a₁, r1, hR1, hM1, hlt1, hq1, hf1, hs1, hz1⟩ := iht he.1.1 n mem a (pos + 1) _ seen m ht q₁ m₁ hA hmo hM hd1 hst hc hT
    have hd2 : rom.drop q₁.toNat = (encExprM (encExprM seen t).2 v).1 ++
        ((encExprM (encExprM (encExprM seen t).2 v).2 x).1 ++ rest) :=
      drop_shift rom hr (pos + 1) _ _ _ (by rw [hd1, List.append_assoc]) q₁ hq1
    cases hV : romExprW rom n m₁ q₁ with
    | none => rw [hV] at hW; simp [exLet2K] at hW
    | some r =>
    obtain ⟨hv, q₂, m₂⟩ := r
    rw [hV, exLet2K_some] at hW
    obtain ⟨mv, a₂, r2, hR2, hM2, hlt2, hq2, hf2, hs2, hz2⟩ := ihv he.1.2 n m₁ a₁ q₁ _ _ mt hv q₂ m₂ hR1
      (((romExprW_topK rom n).1 _ _ _ _ _ hT).mode hA.1.lit.1 hmo) hM1 hd2
      (by rw [hs1]; exact hst) (by rw [hf1.2.2.1]; exact hc) hV
    have hd3 : rom.drop q₂.toNat = (encExprM (encExprM (encExprM seen t).2 v).2 x).1 ++ rest :=
      drop_shift rom hr q₁ _ _ rest (by rw [hd2, List.append_assoc]) q₂ hq2
    cases hX : romExprW rom n m₂ q₂ with
    | none => rw [hX] at hW; simp [exLet3K] at hW
    | some r =>
    obtain ⟨hx, q₃, m₃⟩ := r
    rw [hX, exLet3K_some] at hW
    obtain ⟨mx, a₃, r3, hR3, hM3, hlt3, hq3, hf3, hs3, hz3⟩ := ihx he.2 n m₂ a₂ q₂ rest _ mv hx q₃ m₃ hR2
      ((((romExprW_topK rom n).1 _ _ _ _ _ hT).trans ((romExprW_topK rom n).1 _ _ _ _ _ hV)).mode hA.1.lit.1 hmo)
      hM2 hd3
      (by rw [hs2, hs1]; exact hst) (by rw [hf2.2.2.1, hf1.2.2.1]; exact hc) hX
    obtain ⟨m₄, hI, hlt, rfl, hsz, hpw, rfl⟩ := exNodeK_inv hW
    obtain ⟨ok4, hR4, res4⟩ := mkLet_ok m₃ a₃ hR3 ht hv hx h m₄ hI
    have hf4 := mkLetW_store hI
    have hfresh : ConLeche.Expr.letE t v x ∉ (encExprM (encExprM (encExprM seen t).2 v).2 x).2 := by
      intro hm
      rcases encExprM_seen x _ _ hm with hm | hm
      · rcases encExprM_seen v _ _ hm with hm | hm
        · rcases encExprM_seen t _ _ hm with hm | hm
          · exact hin hm
          · simp at hm; omega
        · simp at hm; omega
      · simp at hm; omega
    have hM4 := (hM3.frame (frame_romA hf4)).push hfresh h hlt hsz
    refine ⟨_, _, iEG_let m mt mv mx a a₁ a₂ a₃ _ (decI ht) (decI hv) (decI hx) (decI h) t v x (hM.miss hin)
      r1 r2 r3 (by rw [show (decI h : EIdx) = _ from res4.symm]; exact AM.run_of_ok _ _ ok4),
      ArenaD.frameHi (mpushMem_frame1 m₄ h) (by simp [RMEMO, RSET]) (by simp) hR4, hM4, hlt, ?_, ?_, ?_, ?_⟩
    · rw [hq3, hq2, hq1, (drop_tag rom hr hd).2]; simp; omega
    · exact hf1.trans (hf2.trans (hf3.trans ((frame_storeE hf4).trans (mpushMem_frame m₄ h))))
    · rw [mpushMem_stk, frame_exprA_stk hf4, hs3, hs2, hs1]
    · exact fun hz => RsetR.push ((hz3 (hz2 (hz1 hz))).frameS hf4) hlt hpw
  | fvar i ty ih =>
    intro n mem a pos rest seen m h q mem' hA hmo hM hd hst hc hW
    simp only [exprFits, Bool.and_eq_true, decide_eq_true_eq] at he
    by_cases hin : ConLeche.Expr.fvar i ty ∈ seen
    · exact ref_case rom hr _ (fun _ => ⟨by simp, by simp, by simp, by simp⟩)
        (fun seen h => by simp [encExprM, h]) n mem a pos rest seen m h q mem' hA hM hin hd hW
    unfold ExprPost
    have henc : encExprM seen (.fvar i ty) = (4 :: (u64B i ++ (encExprM seen ty).1),
        (encExprM seen ty).2 ++ [.fvar i ty]) := by simp [encExprM, hin]
    rw [henc] at hd ⊢
    have h0 : romB rom pos = 4 := romB_head rom hr pos 4 _ rest hd
    cases n with
    | zero => simp [romExprW] at hW
    | succ n =>
    rw [romExprW_one rom n mem pos (by simp [h0]) (by simp [h0]) (by simp [h0]), h0] at hW
    cases n with
    | zero => simp [romOneW] at hW
    | succ n =>
    have hd1 : rom.drop (pos + 1).toNat = u64B i ++ ((encExprM seen ty).1 ++ rest) := by
      simpa using (drop_tag (bs := (u64B i ++ (encExprM seen ty).1)) rom hr (by simpa using hd)).1
    rw [romOneW_fvar rom n mem pos 4 rfl (u64OK_of_drop rom _ _ _ hd1 hr)] at hW
    rw [u64W_of_drop rom (pos + 1) _ _ hd1 he.1 hr] at hW
    have hp9 := drop_pos rom hr pos _ rest hd 9 (by simp [u64B])
    simp only [show UInt64.ofNat 9 = (9 : Word) from rfl] at hp9
    have hd9 : rom.drop (pos + 9).toNat = (encExprM seen ty).1 ++ rest := by
      rw [hp9, ← List.drop_drop, hd]; simp [u64B]
    cases hT : romExprW rom n mem (pos + 9) with
    | none => rw [hT] at hW; simp [exFvarK] at hW
    | some r =>
    obtain ⟨ht, q₁, m₁⟩ := r
    rw [hT, exFvarK_some] at hW
    obtain ⟨mt, a₁, r1, hR1, hM1, hlt1, hq1, hf1, hs1, hz1⟩ := ih he.2 n mem a (pos + 9) rest seen m ht q₁ m₁ hA hmo hM hd9 hst hc hT
    obtain ⟨m₂, hI, hlt, rfl, hsz, hpw, rfl⟩ := exNodeK_inv hW
    obtain ⟨ok2, hR2, res2⟩ := internFVar_D m₁ a₁ hR1 _ ht h hlt1 m₂ hI
    have hiN : (UInt64.ofNat i).toNat = i := by rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt he.1
    rw [hiN] at ok2 hR2 res2
    have hf2 := fvinternW_store hI
    have hfresh : ConLeche.Expr.fvar i ty ∉ (encExprM seen ty).2 := by
      intro hm
      rcases encExprM_seen ty _ _ hm with hm | hm
      · exact hin hm
      · simp at hm; omega
    have hM2 := (hM1.frame (frame_romA hf2)).push hfresh h hlt hsz
    refine ⟨_, _, iEG_fvar m mt a a₁ _ (decI ht) (decI h) i ty (hM.miss hin) r1
      (by rw [show (decI h : EIdx) = _ from res2.symm]; exact AM.run_of_ok _ _ ok2),
      ArenaD.frameHi (mpushMem_frame1 m₂ h) (by simp [RMEMO, RSET]) (by simp) hR2, hM2, hlt, ?_, ?_, ?_, ?_⟩
    · rw [hq1, hp9]; simp [u64B]; omega
    · exact hf1.trans ((frame_storeE hf2).trans (mpushMem_frame m₂ h))
    · rw [mpushMem_stk, frame_exprA_stk hf2, hs1]
    · exact fun hz => RsetR.push ((hz1 hz).frameS hf2) hlt hpw
  | proj nm i sub ih =>
    intro n mem a pos rest seen m h q mem' hA hmo hM hd hst hc hW
    simp only [exprFits, Bool.and_eq_true, decide_eq_true_eq] at he
    by_cases hin : ConLeche.Expr.proj nm i sub ∈ seen
    · exact ref_case rom hr _ (fun _ => ⟨by simp, by simp, by simp, by simp⟩)
        (fun seen h => by simp [encExprM, h]) n mem a pos rest seen m h q mem' hA hM hin hd hW
    unfold ExprPost
    have henc : encExprM seen (.proj nm i sub) = (10 :: (encName nm ++ u64B i ++ (encExprM seen sub).1),
        (encExprM seen sub).2 ++ [.proj nm i sub]) := by simp [encExprM, hin]
    rw [henc] at hd ⊢
    have h0 : romB rom pos = 10 := romB_head rom hr pos 10 _ rest hd
    cases n with
    | zero => simp [romExprW] at hW
    | succ n =>
    rw [romExprW_one rom n mem pos (by simp [h0]) (by simp [h0]) (by simp [h0]), h0] at hW
    cases n with
    | zero => simp [romOneW] at hW
    | succ n =>
    rw [romOneW_proj rom n mem pos 10 (by simp) rfl] at hW
    have hd1 : rom.drop (pos + 1).toNat = encName nm ++ (u64B i ++ ((encExprM seen sub).1 ++ rest)) := by
      simpa using (drop_tag (bs := (encName nm ++ u64B i ++ (encExprM seen sub).1)) rom hr (by simpa using hd)).1
    cases hN : romNameW rom n mem (pos + 1) with
    | none => rw [hN] at hW; simp [exProjK] at hW
    | some r =>
    obtain ⟨hn, q₁, m₁⟩ := r
    rw [hN] at hW
    obtain ⟨ok1, hR1, res1, hlt1, hq1, hf1⟩ := romNameW_ok rom hr nm he.1.1 n mem a (pos + 1) _ hn q₁ m₁ hA hmo hd1 hN
    have hdq : rom.drop q₁.toNat = u64B i ++ ((encExprM seen sub).1 ++ rest) :=
      drop_shift rom hr (pos + 1) (encName nm) _ _ (by rw [hd1, List.append_assoc]) q₁ hq1
    rw [exProjK_some (hu := u64OK_of_drop rom _ _ _ hdq hr)] at hW
    rw [u64W_of_drop rom q₁ _ _ hdq he.1.2 hr] at hW
    have hlenq := drop_len rom _ _ _ hdq (by simp [u64B])
    simp only [RomOK] at hr
    have hq8 : (q₁ + 8).toNat = q₁.toNat + 8 := by
      rw [UInt64.toNat_add]; simp [u64B] at hlenq ⊢; omega
    have hd8 : rom.drop (q₁ + 8).toNat = (encExprM seen sub).1 ++ rest := by
      rw [hq8, ← List.drop_drop, hdq]; simp [u64B]
    cases hS : romExprW rom n m₁ (q₁ + 8) with
    | none => rw [hS] at hW; simp [exProj2K] at hW
    | some r =>
    obtain ⟨hs, q₂, m₂⟩ := r
    rw [hS, exProj2K_some] at hW
    obtain ⟨ms, a₂, r2, hR2, hM2, hlt2, hq2, hf2, hs2, hz2⟩ := ih he.2 n m₁ _ (q₁ + 8) rest seen m hs q₂ m₂ hR1
      ((romNameW_topK hN).mode hA.1.lit.1 hmo) (hM.frame (frame_romA hf1)) hd8 (by rw [frame_exprA_stk hf1]; exact hst) (by rw [hf1.2.2.1]; exact hc) hS
    obtain ⟨m₃, hI, hlt, rfl, hsz, hpw, rfl⟩ := exNodeK_inv hW
    obtain ⟨ok3, hR3, res3⟩ := mkProj_ok m₂ a₂ hR2 hn _ hs h m₃ hI
    have hiN : (UInt64.ofNat i).toNat = i := by rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt he.1.2
    rw [hiN] at ok3 hR3 res3
    have hf3 := mkProjW_store hI
    have hfresh : ConLeche.Expr.proj nm i sub ∉ (encExprM seen sub).2 := by
      intro hm
      rcases encExprM_seen sub _ _ hm with hm | hm
      · exact hin hm
      · simp at hm; omega
    have hM3 := (hM2.frame (frame_romA hf3)).push hfresh h hlt hsz
    refine ⟨_, _, iEG_proj m ms a _ a₂ _ (decI hs) (decI h) nm i sub (decI hn) (hM.miss hin)
      (by rw [← res1]; exact AM.run_of_ok _ _ ok1) r2
      (by rw [show (decI h : EIdx) = _ from res3.symm]; exact AM.run_of_ok _ _ ok3),
      ArenaD.frameHi (mpushMem_frame1 m₃ h) (by simp [RMEMO, RSET]) (by simp) hR3, hM3, hlt, ?_, ?_, ?_, ?_⟩
    · rw [hq2, hq8, hq1, (drop_tag rom hr hd).2]; simp [u64B]; omega
    · exact (frame_storeE hf1).trans (hf2.trans ((frame_storeE hf3).trans (mpushMem_frame m₃ h)))
    · rw [mpushMem_stk, frame_exprA_stk hf3, hs2, frame_exprA_stk hf1]
    · exact fun hz => RsetR.push ((hz2 (hz.frameS hf1)).frameS hf3) hlt hpw

end main

/-- **`rom_expr` refines `internExprGo`**: at a position holding the expression's encoding for the
memo's `seen`, under `ArenaD` and `MemoR`; the memo relation holds after at the encoder's `seen`. -/
@[refines ConRon.Arena.Frontend.internExprGo]
theorem romExpr_refines (rom : List UInt8) (p : Prog) (hL : ExprProg rom p) (hr : RomOK rom)
    (e : ConLeche.Expr) (he : exprFits e = true) (n : Nat) (s₀ : St) (a₀ : AState) (pos : Word)
    (rest : List UInt8) (seen : List ConLeche.Expr) (m : EMemo) (hA : ArenaD s₀.mem a₀) (hmo : ModeOK s₀.mem)
    (hM : MemoR s₀.mem seen m) (hd : rom.drop pos.toNat = (encExprM seen e).1 ++ rest)
    (hst : (stkTop s₀.mem).toNat < 2 ^ 61) (hc : 131 < (s₀.mem.arr64 CTL).size) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "rom_expr" [pos]
    ⦃fun r s' => LocEq s' s₀ ∧ ExprPost e seen s₀.mem a₀ m pos (r.headD 0) (r.tail.headD 0) s'.mem; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hW⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    ((romExpr_specsW rom p hL n).1 s₀ pos ⟨hA.1.lit.1.2.2.1, hA.1.lit.1.top41⟩)
  subst hs
  exact ⟨hloc, romExprW_ok rom hr e he n _ a₀ pos rest seen m _ _ _ hA hmo hM hd hst hc hW⟩

end L.Rom
