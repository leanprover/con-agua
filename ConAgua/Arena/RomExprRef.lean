import ConAgua.Arena.RomExpr
import ConAgua.Census.Attr

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

/-- The expression interner's frame: the store tier, the stack, the memo. -/
def ExprA : List ArrId := RMEMO :: RomA
def ExprC : List Word := 132 :: RomC

theorem frame_exprA {m m' : Mem} (h : MemFrame RomA RomC m m') : MemFrame ExprA ExprC m m' :=
  h.mono (fun b hb => List.mem_cons_of_mem _ hb) (fun x hx => List.mem_cons_of_mem _ hx)

theorem frame_storeE {m m' : Mem} (h : MemFrame StoreA StoreC m m') : MemFrame ExprA ExprC m m' :=
  frame_exprA (frame_romA h)

theorem mkK_store (A : ArrId) (hA : A < 64) (hC : A ≠ CTL) (c s d r : Word) (m m' : Mem)
    (x : Option (Word × Mem)) (hx : ∀ r₁ m₁, x = some (r₁, m₁) → MemFrame StoreA StoreC m m₁)
    (h : mkK A c s d x = some (r, m')) : MemFrame StoreA StoreC m m' := by
  match x, hx, h with
  | some (r₁, m₁), hx, h =>
    rw [mkK_some] at h
    split at h
    · cases h
    · rename_i m₂ hP
      cases h
      exact (hx _ _ rfl).trans (frame_store (derPutW_frame A hC _ _ _ _ _ _ hP) (by simpa using hA)
        (by simp))

theorem mkAppW_store {m m' : Mem} {f x r : Word} (h : mkAppW m f x = some (r, m')) :
    MemFrame StoreA StoreC m m' := by
  unfold mkAppW at h; split at h; · cases h
  exact mkK_store ADER (by decide) (by decide) _ _ _ _ _ _ _ (fun r₁ m₁ hx => by
    rw [ainternW_eq] at hx
    exact frame_store (internM_frame _ appSch_wf _ _ _ _ _ _ _ _ hx) (by simp [appSch, AREC, ASLOT])
      (by simp [appSch])) h
theorem mkLamW_store {m m' : Mem} {f x r : Word} (h : mkLamW m f x = some (r, m')) :
    MemFrame StoreA StoreC m m' := by
  unfold mkLamW at h; split at h; · cases h
  exact mkK_store LADER (by decide) (by decide) _ _ _ _ _ _ _ (fun r₁ m₁ hx => by
    rw [lainternW_eq] at hx
    exact frame_store (internM_frame _ lamSch_wf _ _ _ _ _ _ _ _ hx) (by simp [lamSch, LAREC, LASLOT])
      (by simp [lamSch])) h
theorem mkForallW_store {m m' : Mem} {f x r : Word} (h : mkForallW m f x = some (r, m')) :
    MemFrame StoreA StoreC m m' := by
  unfold mkForallW at h; split at h; · cases h
  exact mkK_store FADER (by decide) (by decide) _ _ _ _ _ _ _ (fun r₁ m₁ hx => by
    rw [fainternW_eq] at hx
    exact frame_store (internM_frame _ forallSch_wf _ _ _ _ _ _ _ _ hx)
      (by simp [forallSch, FAREC, FASLOT]) (by simp [forallSch])) h
theorem mkLetW_store {m m' : Mem} {t v x r : Word} (h : mkLetW m t v x = some (r, m')) :
    MemFrame StoreA StoreC m m' := by
  unfold mkLetW at h; split at h; · cases h
  exact mkK_store LEDER (by decide) (by decide) _ _ _ _ _ _ _ (fun r₁ m₁ hx => by
    rw [leinternW_eq] at hx
    exact frame_store (internM_frame _ letSch_wf _ _ _ _ _ _ _ _ hx) (by simp [letSch, LEREC, LESLOT])
      (by simp [letSch])) h
theorem mkProjW_store {m m' : Mem} {n i e r : Word} (h : mkProjW m n i e = some (r, m')) :
    MemFrame StoreA StoreC m m' := by
  unfold mkProjW at h; split at h; · cases h
  exact mkK_store PJDER (by decide) (by decide) _ _ _ _ _ _ _ (fun r₁ m₁ hx => by
    rw [pjinternW_eq] at hx
    exact frame_store (internM_frame _ projSch_wf _ _ _ _ _ _ _ _ hx) (by simp [projSch, PJREC, PJSLOT])
      (by simp [projSch])) h
theorem binternW_store {m m' : Mem} {u r : Word} (h : binternW m u = some (r, m')) :
    MemFrame StoreA StoreC m m' := by
  rw [binternW_eq] at h
  exact frame_store (internM_frame _ bvarSch_wf _ _ _ _ _ _ _ _ h) (by simp [bvarSch, BREC, BSLOT])
    (by simp [bvarSch])
theorem fvinternW_store {m m' : Mem} {u t r : Word} (h : fvinternW m u t = some (r, m')) :
    MemFrame StoreA StoreC m m' := by
  rw [fvinternW_eq] at h
  exact frame_store (internM_frame _ fvarSch_wf _ _ _ _ _ _ _ _ h) (by simp [fvarSch, FVREC, FVSLOT])
    (by simp [fvarSch])

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
  have hR : mem'.arr64 RMEMO = mem.arr64 RMEMO := hf.1 RMEMO (by simp [RomA, StoreA, RMEMO, RSTK]) (by decide)
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

theorem MemoR.push {mem : Mem} {seen : List ConLeche.Expr} {m : EMemo} (h : MemoR mem seen m)
    {e : ConLeche.Expr} (he : e ∉ seen) (x : Word)
    (hx : x.toNat < 2 ^ 32) (hsz' : memoCnt mem < mem.len64 RMEMO) :
    MemoR (mpushMem mem x) (seen ++ [e]) (m.insert e (decI x)) := by
  have hcn := h.cnt
  have hl := UInt64.lt_iff_toNat_lt.mp hsz'
  simp only [Mem.len64, UInt64.toNat_ofNat'] at hl
  have hsz : (memoCnt mem).toNat < (mem.arr64 RMEMO).size :=
    Nat.lt_of_lt_of_le hl (Nat.mod_le _ _)
  have hroom : (memoCnt mem).toNat + 1 < 2 ^ 64 := by
    have := Nat.mod_lt (mem.arr64 RMEMO).size (show 2 ^ 64 > 0 by decide); omega
  have hR : ∀ k : Word, rdW ((mpushMem mem x).arr64 RMEMO) k =
      if k = memoCnt mem then x else rdW (mem.arr64 RMEMO) k := by
    intro k
    simp only [mpushMem, Mem.arr64_set64_ne _ _ _ _ _ (show RMEMO ≠ CTL by decide), Mem.arr64_set64_same,
      rdW_set!]
    by_cases e' : k = memoCnt mem
    · subst e'; simp [hsz]
    · have : ¬ (memoCnt mem).toNat = k.toNat := fun h' => e' (UInt64.toNat_inj.mp h'.symm)
      simp [e', this]
  have hcnt' : memoCnt (mpushMem mem x) = memoCnt mem + 1 := by
    have hs : 132 < ((mem.set64 RMEMO (memoCnt mem) x).arr64 CTL).size := by
      rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]; exact h.csz
    simp only [memoCnt] at hs ⊢
    simp only [mpushMem, memoCnt, Mem.arr64_set64_same, rdW_set!]
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
  · simp only [mpushMem, Mem.size_arr64_set64, Mem.arr64_set64_ne _ _ _ _ _ (show CTL ≠ RMEMO by decide)]
    exact h.csz

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

theorem iEG_app (f x : ConLeche.Expr) (hm : m[ConLeche.Expr.app f x]? = none)
    (r1 : (internExprGo m f).run a₀ = .ok ((m₁, hf), a₁))
    (r2 : (internExprGo m₁ x).run a₁ = .ok ((m₂, ha), a₂))
    (r3 : (internE (.app hf ha)).run a₂ = .ok (h, a₃)) :
    (internExprGo m (.app f x)).run a₀ = .ok ((m₂.insert (.app f x) h, h), a₃) := by
  simp only [internExprGo, hm, StateT.run_bind, r1]
  simp only [bind, Except.bind]
  rw [r2]; simp only
  rw [r3]; rfl

theorem iEG_lam (f x : ConLeche.Expr) (hm : m[ConLeche.Expr.lam f x]? = none)
    (r1 : (internExprGo m f).run a₀ = .ok ((m₁, hf), a₁))
    (r2 : (internExprGo m₁ x).run a₁ = .ok ((m₂, ha), a₂))
    (r3 : (internE (.lam hf ha)).run a₂ = .ok (h, a₃)) :
    (internExprGo m (.lam f x)).run a₀ = .ok ((m₂.insert (.lam f x) h, h), a₃) := by
  simp only [internExprGo, hm, StateT.run_bind, r1]
  simp only [bind, Except.bind]
  rw [r2]; simp only
  rw [r3]; rfl

theorem iEG_forall (f x : ConLeche.Expr) (hm : m[ConLeche.Expr.forallE f x]? = none)
    (r1 : (internExprGo m f).run a₀ = .ok ((m₁, hf), a₁))
    (r2 : (internExprGo m₁ x).run a₁ = .ok ((m₂, ha), a₂))
    (r3 : (internE (.forallE hf ha)).run a₂ = .ok (h, a₃)) :
    (internExprGo m (.forallE f x)).run a₀ = .ok ((m₂.insert (.forallE f x) h, h), a₃) := by
  simp only [internExprGo, hm, StateT.run_bind, r1]
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

/-- Every datum of the expression fits its encoding; no literal. -/
def exprFits : ConLeche.Expr → Bool
  | .bvar i => decide (i < 2 ^ 64)
  | .sort u => levelFits u
  | .const n us => nameFits n && us.all levelFits && decide (us.length < 2 ^ 60)
  | .lit _ => false
  | .fvar i ty => decide (i < 2 ^ 64) && exprFits ty
  | .app f a | .lam f a | .forallE f a => exprFits f && exprFits a
  | .letE t v b => exprFits t && exprFits v && exprFits b
  | .proj n i e => nameFits n && decide (i < 2 ^ 64) && exprFits e

theorem exNodeK_inv {q h q' : Word} {mem' : Mem} {x : Option (Word × Mem)}
    (hW : exNodeK q x = some (h, q', mem')) :
    ∃ m₃, x = some (h, m₃) ∧ h.toNat < 2 ^ 32 ∧ q' = q ∧
      memoCnt m₃ < m₃.len64 RMEMO ∧ mem' = mpushMem m₃ h := by
  match x, hW with
  | some (r, m₃), hW =>
    simp only [exNodeK] at hW
    split at hW
    · simp at hW
    rename_i hlt
    split at hW
    · rename_i hsz
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨rfl, rfl, rfl⟩ := hW
      exact ⟨m₃, rfl, by simp at hlt; exact UInt64.lt_iff_toNat_lt.mp hlt, rfl, hsz, rfl⟩
    · simp at hW

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

theorem mpushMem_frame1 (m : Mem) (h : Word) : MemFrame [RMEMO] [132] m (mpushMem m h) := by
  simp only [mpushMem]
  exact ((MemFrame.set64 _ RMEMO (by decide) _ _).mono (by simp) (by simp)).trans
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
    stkTop mem' = stkTop mem

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
    have := drop_shift rom hr pos [9] (u64B (seen.idxOf e)) rest (by simpa using hd)
      (pos + 1) (drop_pos rom hr pos _ rest hd 1 (by simp))
    simpa using this
  have hu := u64W_of_drop rom (pos + 1) _ _ hd1 (by omega) hr
  simp only [romRefW, hu] at hW
  split at hW
  case isFalse => simp at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨rfl, rfl, rfl⟩ := hW
  obtain ⟨hlt, hm⟩ := hM.hit hin
  refine ⟨m, a, iEG_hit m a _ e hc hm, hA, hM, hlt, ?_, MemFrame.refl _ _ _, rfl⟩
  have hp := drop_pos rom hr pos _ rest hd 9 (by simp [u64B])
  simp only [show UInt64.ofNat 9 = (9 : Word) from rfl] at hp
  rw [hp]; simp [u64B]

set_option linter.constructorNameAsVariable false in
/-- **The model of `rom_expr` refines `internExprGo`.** -/
theorem romExprW_ok (e : ConLeche.Expr) (he : exprFits e = true) :
    ∀ (n : Nat) (mem : Mem) (a : AState) (pos : Word) (rest : List UInt8) (seen : List ConLeche.Expr)
      (m : EMemo) (h q : Word) (mem' : Mem), ArenaD mem a → MemoR mem seen m →
      rom.drop pos.toNat = (encExprM seen e).1 ++ rest → (stkTop mem).toNat < 2 ^ 61 →
      131 < (mem.arr64 CTL).size → romExprW rom n mem pos = some (h, q, mem') →
      ExprPost e seen mem a m pos h q mem' := by
  induction e with
  | bvar i =>
    intro n mem a pos rest seen m h q mem' hA hM hd hst hc hW
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
    rw [romLeafW_bvar rom n mem pos 0 rfl] at hW
    have hd1 : rom.drop (pos + 1).toNat = u64B i ++ rest := by
      have := drop_shift rom hr pos [0] (u64B i) rest (by simpa using hd)
        (pos + 1) (drop_pos rom hr pos _ rest hd 1 (by simp))
      simpa using this
    rw [u64W_of_drop rom (pos + 1) _ _ hd1 he hr] at hW
    obtain ⟨hI, hlt, rfl⟩ := exLeafK_inv hW
    obtain ⟨ok, hR, res⟩ := internBVar_D mem a hA _ h mem' hI
    have hiN : (UInt64.ofNat i).toNat = i := by rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt he
    rw [hiN] at ok hR res
    have hf := binternW_store hI
    refine ⟨m, _, iEG_bvar m a _ (decE h) i (by rw [← res]; exact AM.run_of_ok _ _ ok), hR,
      hM.frame (frame_romA hf), hlt, ?_, frame_storeE hf, frame_exprA_stk hf⟩
    have hp := drop_pos rom hr pos _ rest hd 9 (by simp [u64B])
    simp only [show UInt64.ofNat 9 = (9 : Word) from rfl] at hp
    rw [hp]; simp [u64B]
  | sort u =>
    intro n mem a pos rest seen m h q mem' hA hM hd hst hc hW
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
      have := drop_shift rom hr pos [1] (encLevel u) rest (by simpa using hd)
        (pos + 1) (drop_pos rom hr pos _ rest hd 1 (by simp))
      simpa using this
    cases hU : romLevelW rom n mem (pos + 1) with
    | none => rw [hU] at hW; simp [exSortK] at hW
    | some r =>
    obtain ⟨hu, q₁, m₁⟩ := r
    rw [hU, exSortK_some] at hW
    obtain ⟨ok1, hR1, res1, hlt1, hq1, hf1⟩ := romLevelW_ok rom hr u he n mem a (pos + 1) rest hu q₁ m₁ hA hd1 hU
    obtain ⟨hI, hlt, rfl⟩ := exLeafK_inv hW
    obtain ⟨ok2, hR2, res2, hf2⟩ := L.Front.internSort_D m₁ _ hR1 h mem' hu hlt1 hI
    rw [← res1] at ok2 hR2 res2
    refine ⟨m, _, iEG_sort m a _ _ (decI h) u _ (AM.run_of_ok _ _ ok1)
      (by rw [show (decI h : EIdx) = AM.res (internE (.sort (AM.res (internLevel u) a))) (AM.st (internLevel u) a)
            from res2.symm]; exact AM.run_of_ok _ _ ok2), hR2,
      (hM.frame (frame_romA hf1)).frame (frame_romA (frame_store hf2 (by simp [sortSch, SOREC, SOSLOT])
        (by simp [sortSch]))), hlt, ?_, ?_, ?_⟩
    · have hp1 := drop_pos rom hr pos _ rest hd 1 (by simp)
      simp only [UInt64.ofNat_one] at hp1
      rw [hq1, hp1]; simp; omega
    · exact frame_storeE (hf1.trans (frame_store hf2 (by simp [sortSch, SOREC, SOSLOT]) (by simp [sortSch])))
    · exact frame_exprA_stk (hf1.trans (frame_store hf2 (by simp [sortSch, SOREC, SOSLOT]) (by simp [sortSch])))
  | const nm us =>
    intro n mem a pos rest seen m h q mem' hA hM hd hst hc hW
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
      have := drop_shift rom hr pos [2] (encName nm ++ encLevels us) rest (by simpa using hd)
        (pos + 1) (drop_pos rom hr pos _ rest hd 1 (by simp))
      simpa using this
    cases hN : romNameW rom n mem (pos + 1) with
    | none => rw [hN] at hW; simp [exConst2KN] at hW
    | some r =>
    obtain ⟨hnm, q₁, m₁⟩ := r
    rw [hN, exConst2KN_some] at hW
    obtain ⟨ok1, hR1, res1, hlt1, hq1, hf1⟩ := romNameW_ok rom hr nm hn n mem a (pos + 1) _ hnm q₁ m₁ hA hd1 hN
    have hd2 : rom.drop q₁.toNat = encLevels us ++ rest :=
      drop_shift rom hr (pos + 1) (encName nm) (encLevels us) rest (by rw [hd1, List.append_assoc]) q₁ hq1
    have hst1 : stkTop m₁ = stkTop mem := frame_exprA_stk hf1
    cases hL : romLevelsW rom n m₁ q₁ with
    | none => rw [hL] at hW; simp [exConst2K] at hW
    | some r =>
    obtain ⟨hl, q₂, m₂⟩ := r
    rw [hL, exConst2K_some] at hW
    obtain ⟨ok2, hR2, res2, hlt2, hq2, hf2, hst2⟩ := romLevelsW_ok rom hr us hus n m₁ _ q₁ rest hl q₂ m₂ hR1 hd2
      (by rw [hst1]; omega) (by rw [hf1.2.2.1]; exact hc) hL
    obtain ⟨hI, hlt, rfl⟩ := exLeafK_inv hW
    obtain ⟨ok3, hR3, res3, hf3⟩ := L.Front.internConst_D m₂ _ hR2 h mem' hnm hl hlt1 hlt2 hI
    rw [← res1, ← res2] at ok3 hR3 res3
    have hf3' := frame_store hf3 (by simp [constSch, CREC, CSLOT]) (by simp [constSch])
    refine ⟨m, _, iEG_const m a _ _ _ (decI h) nm us _ _ (AM.run_of_ok _ _ ok1) (AM.run_of_ok _ _ ok2)
      (by rw [show (decI h : EIdx) = _ from res3.symm]; exact AM.run_of_ok _ _ ok3), hR3,
      ((hM.frame (frame_romA hf1)).frame hf2).frame (frame_romA hf3'), hlt, ?_, ?_, ?_⟩
    · have hp1 := drop_pos rom hr pos _ rest hd 1 (by simp)
      simp only [UInt64.ofNat_one] at hp1
      rw [hq2, hq1, hp1]; simp; omega
    · exact (frame_storeE hf1).trans ((frame_exprA hf2).trans (frame_storeE hf3'))
    · rw [frame_exprA_stk hf3', hst2, hst1]
  | lit l => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _; simp [exprFits] at he
  | app f x ihf ihx =>
    intro n mem a pos rest seen m h q mem' hA hM hd hst hc hW
    simp only [exprFits, Bool.and_eq_true] at he
    by_cases hin : ConLeche.Expr.app f x ∈ seen
    · exact ref_case rom hr _ (fun _ => ⟨by simp, by simp, by simp, by simp⟩)
        (fun seen h => by simp [encExprM, h]) n mem a pos rest seen m h q mem' hA hM hin hd hW
    unfold ExprPost
    have henc : encExprM seen (.app f x) = (5 :: ((encExprM seen f).1 ++ (encExprM (encExprM seen f).2 x).1),
        (encExprM (encExprM seen f).2 x).2 ++ [.app f x]) := by simp [encExprM, hin]
    rw [henc] at hd ⊢
    have h0 : romB rom pos = 5 := romB_head rom hr pos 5 _ rest hd
    cases n with
    | zero => simp [romExprW] at hW
    | succ n =>
    rw [romExprW_two rom n mem pos (by simp [h0]) (by simp [h0]) (by simp [h0]), h0] at hW
    cases n with
    | zero => simp [romTwoW] at hW
    | succ n =>
    rw [romTwoW_eq] at hW
    have hd1 : rom.drop (pos + 1).toNat = (encExprM seen f).1 ++ ((encExprM (encExprM seen f).2 x).1 ++ rest) := by
      have := drop_shift rom hr pos [5] ((encExprM seen f).1 ++ (encExprM (encExprM seen f).2 x).1) rest
        (by simpa using hd) (pos + 1) (drop_pos rom hr pos _ rest hd 1 (by simp))
      simpa using this
    cases hF : romExprW rom n mem (pos + 1) with
    | none => rw [hF] at hW; simp [exOneK] at hW
    | some r =>
    obtain ⟨hf, q₁, m₁⟩ := r
    rw [hF, exOneK_two (ht := by simp)] at hW
    obtain ⟨mf, a₁, r1, hR1, hM1, hlt1, hq1, hf1, hs1⟩ := ihf he.1 n mem a (pos + 1) _ seen m hf q₁ m₁ hA hM hd1 hst hc hF
    have hd2 : rom.drop q₁.toNat = (encExprM (encExprM seen f).2 x).1 ++ rest :=
      drop_shift rom hr (pos + 1) _ _ rest (by rw [hd1, List.append_assoc]) q₁ hq1
    cases hX : romExprW rom n m₁ q₁ with
    | none => rw [hX] at hW; simp [exTwoK] at hW
    | some r =>
    obtain ⟨hx, q₂, m₂⟩ := r
    rw [hX, exTwoK_app (ht := rfl)] at hW
    obtain ⟨mx, a₂, r2, hR2, hM2, hlt2, hq2, hf2, hs2⟩ := ihx he.2 n m₁ a₁ q₁ rest _ mf hx q₂ m₂ hR1 hM1 hd2
      (by rw [hs1]; exact hst) (by rw [hf1.2.2.1]; exact hc) hX
    obtain ⟨m₃, hI, hlt, rfl, hsz, rfl⟩ := exNodeK_inv hW
    obtain ⟨ok3, hR3, res3⟩ := mkApp_ok m₂ a₂ hR2 hf hx h m₃ hI
    have hf3 := mkAppW_store hI
    have hfresh : ConLeche.Expr.app f x ∉ (encExprM (encExprM seen f).2 x).2 := by
      intro hm
      rcases encExprM_seen x _ _ hm with hm | hm
      · rcases encExprM_seen f _ _ hm with hm | hm
        · exact hin hm
        · simp at hm; omega
      · simp at hm; omega
    have hM3 := (hM2.frame (frame_romA hf3)).push hfresh h hlt hsz
    refine ⟨_, _, iEG_app m mf mx a a₁ a₂ _ (decI hf) (decI hx) (decI h) f x (hM.miss hin) r1 r2
      (by rw [show (decI h : EIdx) = _ from res3.symm]; exact AM.run_of_ok _ _ ok3),
      ArenaD.frameHi (mpushMem_frame1 m₃ h) (by simp [RMEMO]) (by simp) hR3, hM3, hlt, ?_, ?_, ?_⟩
    · have hp1 := drop_pos rom hr pos _ rest hd 1 (by simp)
      simp only [UInt64.ofNat_one] at hp1
      rw [hq2, hq1, hp1]; simp; omega
    · exact hf1.trans (hf2.trans ((frame_storeE hf3).trans (mpushMem_frame m₃ h)))
    · rw [mpushMem_stk, frame_exprA_stk hf3, hs2, hs1]
  | lam f x ihf ihx =>
    intro n mem a pos rest seen m h q mem' hA hM hd hst hc hW
    simp only [exprFits, Bool.and_eq_true] at he
    by_cases hin : ConLeche.Expr.lam f x ∈ seen
    · exact ref_case rom hr _ (fun _ => ⟨by simp, by simp, by simp, by simp⟩)
        (fun seen h => by simp [encExprM, h]) n mem a pos rest seen m h q mem' hA hM hin hd hW
    unfold ExprPost
    have henc : encExprM seen (.lam f x) = (6 :: ((encExprM seen f).1 ++ (encExprM (encExprM seen f).2 x).1),
        (encExprM (encExprM seen f).2 x).2 ++ [.lam f x]) := by simp [encExprM, hin]
    rw [henc] at hd ⊢
    have h0 : romB rom pos = 6 := romB_head rom hr pos 6 _ rest hd
    cases n with
    | zero => simp [romExprW] at hW
    | succ n =>
    rw [romExprW_two rom n mem pos (by simp [h0]) (by simp [h0]) (by simp [h0]), h0] at hW
    cases n with
    | zero => simp [romTwoW] at hW
    | succ n =>
    rw [romTwoW_eq] at hW
    have hd1 : rom.drop (pos + 1).toNat = (encExprM seen f).1 ++ ((encExprM (encExprM seen f).2 x).1 ++ rest) := by
      have := drop_shift rom hr pos [6] ((encExprM seen f).1 ++ (encExprM (encExprM seen f).2 x).1) rest
        (by simpa using hd) (pos + 1) (drop_pos rom hr pos _ rest hd 1 (by simp))
      simpa using this
    cases hF : romExprW rom n mem (pos + 1) with
    | none => rw [hF] at hW; simp [exOneK] at hW
    | some r =>
    obtain ⟨hf, q₁, m₁⟩ := r
    rw [hF, exOneK_two (ht := by simp)] at hW
    obtain ⟨mf, a₁, r1, hR1, hM1, hlt1, hq1, hf1, hs1⟩ := ihf he.1 n mem a (pos + 1) _ seen m hf q₁ m₁ hA hM hd1 hst hc hF
    have hd2 : rom.drop q₁.toNat = (encExprM (encExprM seen f).2 x).1 ++ rest :=
      drop_shift rom hr (pos + 1) _ _ rest (by rw [hd1, List.append_assoc]) q₁ hq1
    cases hX : romExprW rom n m₁ q₁ with
    | none => rw [hX] at hW; simp [exTwoK] at hW
    | some r =>
    obtain ⟨hx, q₂, m₂⟩ := r
    rw [hX, exTwoK_lam (ht := rfl)] at hW
    obtain ⟨mx, a₂, r2, hR2, hM2, hlt2, hq2, hf2, hs2⟩ := ihx he.2 n m₁ a₁ q₁ rest _ mf hx q₂ m₂ hR1 hM1 hd2
      (by rw [hs1]; exact hst) (by rw [hf1.2.2.1]; exact hc) hX
    obtain ⟨m₃, hI, hlt, rfl, hsz, rfl⟩ := exNodeK_inv hW
    obtain ⟨ok3, hR3, res3⟩ := mkLam_ok m₂ a₂ hR2 hf hx h m₃ hI
    have hf3 := mkLamW_store hI
    have hfresh : ConLeche.Expr.lam f x ∉ (encExprM (encExprM seen f).2 x).2 := by
      intro hm
      rcases encExprM_seen x _ _ hm with hm | hm
      · rcases encExprM_seen f _ _ hm with hm | hm
        · exact hin hm
        · simp at hm; omega
      · simp at hm; omega
    have hM3 := (hM2.frame (frame_romA hf3)).push hfresh h hlt hsz
    refine ⟨_, _, iEG_lam m mf mx a a₁ a₂ _ (decI hf) (decI hx) (decI h) f x (hM.miss hin) r1 r2
      (by rw [show (decI h : EIdx) = _ from res3.symm]; exact AM.run_of_ok _ _ ok3),
      ArenaD.frameHi (mpushMem_frame1 m₃ h) (by simp [RMEMO]) (by simp) hR3, hM3, hlt, ?_, ?_, ?_⟩
    · have hp1 := drop_pos rom hr pos _ rest hd 1 (by simp)
      simp only [UInt64.ofNat_one] at hp1
      rw [hq2, hq1, hp1]; simp; omega
    · exact hf1.trans (hf2.trans ((frame_storeE hf3).trans (mpushMem_frame m₃ h)))
    · rw [mpushMem_stk, frame_exprA_stk hf3, hs2, hs1]
  | forallE f x ihf ihx =>
    intro n mem a pos rest seen m h q mem' hA hM hd hst hc hW
    simp only [exprFits, Bool.and_eq_true] at he
    by_cases hin : ConLeche.Expr.forallE f x ∈ seen
    · exact ref_case rom hr _ (fun _ => ⟨by simp, by simp, by simp, by simp⟩)
        (fun seen h => by simp [encExprM, h]) n mem a pos rest seen m h q mem' hA hM hin hd hW
    unfold ExprPost
    have henc : encExprM seen (.forallE f x) = (7 :: ((encExprM seen f).1 ++ (encExprM (encExprM seen f).2 x).1),
        (encExprM (encExprM seen f).2 x).2 ++ [.forallE f x]) := by simp [encExprM, hin]
    rw [henc] at hd ⊢
    have h0 : romB rom pos = 7 := romB_head rom hr pos 7 _ rest hd
    cases n with
    | zero => simp [romExprW] at hW
    | succ n =>
    rw [romExprW_two rom n mem pos (by simp [h0]) (by simp [h0]) (by simp [h0]), h0] at hW
    cases n with
    | zero => simp [romTwoW] at hW
    | succ n =>
    rw [romTwoW_eq] at hW
    have hd1 : rom.drop (pos + 1).toNat = (encExprM seen f).1 ++ ((encExprM (encExprM seen f).2 x).1 ++ rest) := by
      have := drop_shift rom hr pos [7] ((encExprM seen f).1 ++ (encExprM (encExprM seen f).2 x).1) rest
        (by simpa using hd) (pos + 1) (drop_pos rom hr pos _ rest hd 1 (by simp))
      simpa using this
    cases hF : romExprW rom n mem (pos + 1) with
    | none => rw [hF] at hW; simp [exOneK] at hW
    | some r =>
    obtain ⟨hf, q₁, m₁⟩ := r
    rw [hF, exOneK_two (ht := by simp)] at hW
    obtain ⟨mf, a₁, r1, hR1, hM1, hlt1, hq1, hf1, hs1⟩ := ihf he.1 n mem a (pos + 1) _ seen m hf q₁ m₁ hA hM hd1 hst hc hF
    have hd2 : rom.drop q₁.toNat = (encExprM (encExprM seen f).2 x).1 ++ rest :=
      drop_shift rom hr (pos + 1) _ _ rest (by rw [hd1, List.append_assoc]) q₁ hq1
    cases hX : romExprW rom n m₁ q₁ with
    | none => rw [hX] at hW; simp [exTwoK] at hW
    | some r =>
    obtain ⟨hx, q₂, m₂⟩ := r
    rw [hX, exTwoK_forall (ht := rfl)] at hW
    obtain ⟨mx, a₂, r2, hR2, hM2, hlt2, hq2, hf2, hs2⟩ := ihx he.2 n m₁ a₁ q₁ rest _ mf hx q₂ m₂ hR1 hM1 hd2
      (by rw [hs1]; exact hst) (by rw [hf1.2.2.1]; exact hc) hX
    obtain ⟨m₃, hI, hlt, rfl, hsz, rfl⟩ := exNodeK_inv hW
    obtain ⟨ok3, hR3, res3⟩ := mkForall_ok m₂ a₂ hR2 hf hx h m₃ hI
    have hf3 := mkForallW_store hI
    have hfresh : ConLeche.Expr.forallE f x ∉ (encExprM (encExprM seen f).2 x).2 := by
      intro hm
      rcases encExprM_seen x _ _ hm with hm | hm
      · rcases encExprM_seen f _ _ hm with hm | hm
        · exact hin hm
        · simp at hm; omega
      · simp at hm; omega
    have hM3 := (hM2.frame (frame_romA hf3)).push hfresh h hlt hsz
    refine ⟨_, _, iEG_forall m mf mx a a₁ a₂ _ (decI hf) (decI hx) (decI h) f x (hM.miss hin) r1 r2
      (by rw [show (decI h : EIdx) = _ from res3.symm]; exact AM.run_of_ok _ _ ok3),
      ArenaD.frameHi (mpushMem_frame1 m₃ h) (by simp [RMEMO]) (by simp) hR3, hM3, hlt, ?_, ?_, ?_⟩
    · have hp1 := drop_pos rom hr pos _ rest hd 1 (by simp)
      simp only [UInt64.ofNat_one] at hp1
      rw [hq2, hq1, hp1]; simp; omega
    · exact hf1.trans (hf2.trans ((frame_storeE hf3).trans (mpushMem_frame m₃ h)))
    · rw [mpushMem_stk, frame_exprA_stk hf3, hs2, hs1]
  | letE t v x iht ihv ihx =>
    intro n mem a pos rest seen m h q mem' hA hM hd hst hc hW
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
      have := drop_shift rom hr pos [8] ((encExprM seen t).1 ++ (encExprM (encExprM seen t).2 v).1 ++
        (encExprM (encExprM (encExprM seen t).2 v).2 x).1) rest
        (by simpa using hd) (pos + 1) (drop_pos rom hr pos _ rest hd 1 (by simp))
      simpa using this
    cases hT : romExprW rom n mem (pos + 1) with
    | none => rw [hT] at hW; simp [exOneK] at hW
    | some r =>
    obtain ⟨ht, q₁, m₁⟩ := r
    rw [hT, exOneK_let (ht := rfl)] at hW
    obtain ⟨mt, a₁, r1, hR1, hM1, hlt1, hq1, hf1, hs1⟩ := iht he.1.1 n mem a (pos + 1) _ seen m ht q₁ m₁ hA hM hd1 hst hc hT
    have hd2 : rom.drop q₁.toNat = (encExprM (encExprM seen t).2 v).1 ++
        ((encExprM (encExprM (encExprM seen t).2 v).2 x).1 ++ rest) :=
      drop_shift rom hr (pos + 1) _ _ _ (by rw [hd1, List.append_assoc]) q₁ hq1
    cases hV : romExprW rom n m₁ q₁ with
    | none => rw [hV] at hW; simp [exLet2K] at hW
    | some r =>
    obtain ⟨hv, q₂, m₂⟩ := r
    rw [hV, exLet2K_some] at hW
    obtain ⟨mv, a₂, r2, hR2, hM2, hlt2, hq2, hf2, hs2⟩ := ihv he.1.2 n m₁ a₁ q₁ _ _ mt hv q₂ m₂ hR1 hM1 hd2
      (by rw [hs1]; exact hst) (by rw [hf1.2.2.1]; exact hc) hV
    have hd3 : rom.drop q₂.toNat = (encExprM (encExprM (encExprM seen t).2 v).2 x).1 ++ rest :=
      drop_shift rom hr q₁ _ _ rest (by rw [hd2, List.append_assoc]) q₂ hq2
    cases hX : romExprW rom n m₂ q₂ with
    | none => rw [hX] at hW; simp [exLet3K] at hW
    | some r =>
    obtain ⟨hx, q₃, m₃⟩ := r
    rw [hX, exLet3K_some] at hW
    obtain ⟨mx, a₃, r3, hR3, hM3, hlt3, hq3, hf3, hs3⟩ := ihx he.2 n m₂ a₂ q₂ rest _ mv hx q₃ m₃ hR2 hM2 hd3
      (by rw [hs2, hs1]; exact hst) (by rw [hf2.2.2.1, hf1.2.2.1]; exact hc) hX
    obtain ⟨m₄, hI, hlt, rfl, hsz, rfl⟩ := exNodeK_inv hW
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
      ArenaD.frameHi (mpushMem_frame1 m₄ h) (by simp [RMEMO]) (by simp) hR4, hM4, hlt, ?_, ?_, ?_⟩
    · have hp1 := drop_pos rom hr pos _ rest hd 1 (by simp)
      simp only [UInt64.ofNat_one] at hp1
      rw [hq3, hq2, hq1, hp1]; simp; omega
    · exact hf1.trans (hf2.trans (hf3.trans ((frame_storeE hf4).trans (mpushMem_frame m₄ h))))
    · rw [mpushMem_stk, frame_exprA_stk hf4, hs3, hs2, hs1]
  | fvar i ty ih =>
    intro n mem a pos rest seen m h q mem' hA hM hd hst hc hW
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
    rw [romOneW_fvar rom n mem pos 4 rfl] at hW
    have hd1 : rom.drop (pos + 1).toNat = u64B i ++ ((encExprM seen ty).1 ++ rest) := by
      have := drop_shift rom hr pos [4] (u64B i ++ (encExprM seen ty).1) rest (by simpa using hd)
        (pos + 1) (drop_pos rom hr pos _ rest hd 1 (by simp))
      simpa using this
    rw [u64W_of_drop rom (pos + 1) _ _ hd1 he.1 hr] at hW
    have hp1 := drop_pos rom hr pos _ rest hd 1 (by simp)
    simp only [UInt64.ofNat_one] at hp1
    have hp9 := drop_pos rom hr pos _ rest hd 9 (by simp [u64B])
    simp only [show UInt64.ofNat 9 = (9 : Word) from rfl] at hp9
    have hd9 : rom.drop (pos + 9).toNat = (encExprM seen ty).1 ++ rest := by
      rw [hp9, ← List.drop_drop, hd]; simp [u64B]
    cases hT : romExprW rom n mem (pos + 9) with
    | none => rw [hT] at hW; simp [exFvarK] at hW
    | some r =>
    obtain ⟨ht, q₁, m₁⟩ := r
    rw [hT, exFvarK_some] at hW
    obtain ⟨mt, a₁, r1, hR1, hM1, hlt1, hq1, hf1, hs1⟩ := ih he.2 n mem a (pos + 9) rest seen m ht q₁ m₁ hA hM hd9 hst hc hT
    obtain ⟨m₂, hI, hlt, rfl, hsz, rfl⟩ := exNodeK_inv hW
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
      ArenaD.frameHi (mpushMem_frame1 m₂ h) (by simp [RMEMO]) (by simp) hR2, hM2, hlt, ?_, ?_, ?_⟩
    · rw [hq1, hp9]; simp [u64B]; omega
    · exact hf1.trans ((frame_storeE hf2).trans (mpushMem_frame m₂ h))
    · rw [mpushMem_stk, frame_exprA_stk hf2, hs1]
  | proj nm i sub ih =>
    intro n mem a pos rest seen m h q mem' hA hM hd hst hc hW
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
      have := drop_shift rom hr pos [10] (encName nm ++ u64B i ++ (encExprM seen sub).1) rest (by simpa using hd)
        (pos + 1) (drop_pos rom hr pos _ rest hd 1 (by simp))
      simpa using this
    cases hN : romNameW rom n mem (pos + 1) with
    | none => rw [hN] at hW; simp [exProjK] at hW
    | some r =>
    obtain ⟨hn, q₁, m₁⟩ := r
    rw [hN, exProjK_some] at hW
    obtain ⟨ok1, hR1, res1, hlt1, hq1, hf1⟩ := romNameW_ok rom hr nm he.1.1 n mem a (pos + 1) _ hn q₁ m₁ hA hd1 hN
    have hdq : rom.drop q₁.toNat = u64B i ++ ((encExprM seen sub).1 ++ rest) :=
      drop_shift rom hr (pos + 1) (encName nm) _ _ (by rw [hd1, List.append_assoc]) q₁ hq1
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
    obtain ⟨ms, a₂, r2, hR2, hM2, hlt2, hq2, hf2, hs2⟩ := ih he.2 n m₁ _ (q₁ + 8) rest seen m hs q₂ m₂ hR1
      (hM.frame (frame_romA hf1)) hd8 (by rw [frame_exprA_stk hf1]; exact hst) (by rw [hf1.2.2.1]; exact hc) hS
    obtain ⟨m₃, hI, hlt, rfl, hsz, rfl⟩ := exNodeK_inv hW
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
      ArenaD.frameHi (mpushMem_frame1 m₃ h) (by simp [RMEMO]) (by simp) hR3, hM3, hlt, ?_, ?_, ?_⟩
    · have hp1 := drop_pos rom (by simpa [RomOK] using hr) pos _ rest hd 1 (by simp)
      simp only [UInt64.ofNat_one] at hp1
      rw [hq2, hq8, hq1, hp1]; simp [u64B]; omega
    · exact (frame_storeE hf1).trans (hf2.trans ((frame_storeE hf3).trans (mpushMem_frame m₃ h)))
    · rw [mpushMem_stk, frame_exprA_stk hf3, hs2, frame_exprA_stk hf1]

end main

/-- **`rom_expr` refines `internExprGo`**: at a position holding the expression's encoding for the
memo's `seen`, under `ArenaD` and `MemoR`; the memo relation holds after at the encoder's `seen`. -/
@[refines ConRon.Arena.Frontend.internExprGo]
theorem romExpr_refines (rom : List UInt8) (p : Prog) (hL : ExprProg rom p) (hr : RomOK rom)
    (e : ConLeche.Expr) (he : exprFits e = true) (n : Nat) (s₀ : St) (a₀ : AState) (pos : Word)
    (rest : List UInt8) (seen : List ConLeche.Expr) (m : EMemo) (hA : ArenaD s₀.mem a₀)
    (hM : MemoR s₀.mem seen m) (hd : rom.drop pos.toNat = (encExprM seen e).1 ++ rest)
    (hst : (stkTop s₀.mem).toNat < 2 ^ 61) (hc : 131 < (s₀.mem.arr64 CTL).size) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "rom_expr" [pos]
    ⦃fun r s' => LocEq s' s₀ ∧ ExprPost e seen s₀.mem a₀ m pos (r.headD 0) (r.tail.headD 0) s'.mem; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hW⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    ((romExpr_specsW rom p hL n).1 s₀ pos hA.1.lit.1.2.2.1)
  subst hs
  exact ⟨hloc, romExprW_ok rom hr e he n _ a₀ pos rest seen m _ _ _ hA hM hd hst hc hW⟩

end L.Rom
