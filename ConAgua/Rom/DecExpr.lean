import ConAgua.Rom.Dec
import ConRon.Bridge.Frontend.Shared
import ConAgua.Arena.RomExprRef

/-!
# The expression reader in the decoder direction (lane `romload`)

`romExprW_ok` (`ConAgua/Arena/RomExprRef.lean`) is the encoder direction: at bytes that are
`encExprM seen e`, a model run that returns is the twin's `internExprGo` on `e`. On the pin data
(untrusted) we need the converse: **a model run that returns read `encExprM seen e` for some `e`**
(`romExprW_dec`). Two run-time checks make that true for every byte string:

* every byte the model consumed is in the ROM (`romB` reads `255`, no tag, past the end; `u64OK`);
* an explicitly encoded compound node is not in `seen`: `memo_push` aborts when the node's handle is
  in `RSET` (`RsetR`), and two handles of one tree are equal (con-ron's `denoteE_inj`), so the
  node's tree is no memo entry (`canon_miss`). That is what makes the bytes the *canonical*
  encoding, the one `romExprW_ok` takes.
-/

open ConRon.Arena ConRon.Arena.Frontend ConRon.Bridge ConRon.Bridge.Frontend

namespace L.Rom

open L.Arena

/-- The compound expressions (the ones the twin's memo holds). -/
def IsComp : ConLeche.Expr → Prop
  | .bvar _ | .sort _ | .const _ _ | .lit _ => False
  | _ => True

/-! ## The encoder's `seen` -/

theorem encExprM_prefix (e : ConLeche.Expr) : ∀ seen, seen <+: (encExprM seen e).2 := by
  induction e with
  | bvar | sort | const => intro seen; simp [encExprM]
  | lit l => intro seen; cases l <;> simp [encExprM]
  | fvar i ty ih =>
    intro seen; simp only [encExprM]; split
    · exact List.prefix_refl _
    · exact (ih seen).trans (List.prefix_append _ _)
  | app f x ihf ihx | lam f x ihf ihx | forallE f x ihf ihx =>
    intro seen; simp only [encExprM]; split
    · exact List.prefix_refl _
    · exact ((ihf seen).trans (ihx _)).trans (List.prefix_append _ _)
  | letE t v x iht ihv ihx =>
    intro seen; simp only [encExprM]; split
    · exact List.prefix_refl _
    · exact (((iht seen).trans (ihv _)).trans (ihx _)).trans (List.prefix_append _ _)
  | proj n i s ih =>
    intro seen; simp only [encExprM]; split
    · exact List.prefix_refl _
    · exact (ih seen).trans (List.prefix_append _ _)

theorem encExprM_comp (e : ConLeche.Expr) : ∀ seen, (∀ x ∈ seen, IsComp x) →
    ∀ x ∈ (encExprM seen e).2, IsComp x := by
  induction e with
  | bvar | sort | const => intro seen h; simpa [encExprM] using h
  | lit l => intro seen h; cases l <;> simpa [encExprM] using h
  | fvar i ty ih =>
    intro seen h; simp only [encExprM]; split
    · exact h
    · intro x hx; simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact ih seen h x hx
      · trivial
  | app f a ihf iha | lam f a ihf iha | forallE f a ihf iha =>
    intro seen h; simp only [encExprM]; split
    · exact h
    · intro x hx; simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact iha _ (ihf seen h) x hx
      · trivial
  | letE t v b iht ihv ihb =>
    intro seen h; simp only [encExprM]; split
    · exact h
    · intro x hx; simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact ihb _ (ihv _ (iht seen h)) x hx
      · trivial
  | proj n i s ih =>
    intro seen h; simp only [encExprM]; split
    · exact h
    · intro x hx; simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact ih seen h x hx
      · trivial

theorem encExprM_nodup (e : ConLeche.Expr) : ∀ seen, seen.Nodup → (encExprM seen e).2.Nodup := by
  induction e with
  | bvar | sort | const => intro seen h; simpa [encExprM] using h
  | lit l => intro seen h; cases l <;> simpa [encExprM] using h
  | fvar i ty ih =>
    intro seen h; simp only [encExprM]; split
    · exact h
    · rename_i hin
      refine List.nodup_append.mpr ⟨ih seen h, by simp, ?_⟩
      intro x hx y hy; simp only [List.mem_singleton] at hy; subst hy
      rintro rfl
      rcases encExprM_seen ty _ _ hx with hm | hm
      · exact hin hm
      · simp at hm; omega
  | app f a ihf iha | lam f a ihf iha | forallE f a ihf iha =>
    intro seen h; simp only [encExprM]; split
    · exact h
    · rename_i hin
      refine List.nodup_append.mpr ⟨iha _ (ihf seen h), by simp, ?_⟩
      intro x hx y hy; simp only [List.mem_singleton] at hy; subst hy
      rintro rfl
      rcases encExprM_seen a _ _ hx with hm | hm
      · rcases encExprM_seen f _ _ hm with hm | hm
        · exact hin hm
        · simp at hm; omega
      · simp at hm; omega
  | letE t v b iht ihv ihb =>
    intro seen h; simp only [encExprM]; split
    · exact h
    · rename_i hin
      refine List.nodup_append.mpr ⟨ihb _ (ihv _ (iht seen h)), by simp, ?_⟩
      intro x hx y hy; simp only [List.mem_singleton] at hy; subst hy
      rintro rfl
      rcases encExprM_seen b _ _ hx with hm | hm
      · rcases encExprM_seen v _ _ hm with hm | hm
        · rcases encExprM_seen t _ _ hm with hm | hm
          · exact hin hm
          · simp at hm; omega
        · simp at hm; omega
      · simp at hm; omega
  | proj n i s ih =>
    intro seen h; simp only [encExprM]; split
    · exact h
    · rename_i hin
      refine List.nodup_append.mpr ⟨ih seen h, by simp, ?_⟩
      intro x hx y hy; simp only [List.mem_singleton] at hy; subst hy
      rintro rfl
      rcases encExprM_seen s _ _ hx with hm | hm
      · exact hin hm
      · simp at hm; omega

theorem encExprM_ref (e : ConLeche.Expr) (seen : List ConLeche.Expr) (hc : IsComp e) (he : e ∈ seen) :
    encExprM seen e = (9 :: u64B (seen.idxOf e), seen) := by
  cases e <;> simp_all [IsComp, encExprM]

/-! ## Bytes -/

section bytes
variable (rom : List UInt8)

theorem drop_after {p : Nat} {A R : List UInt8} (h : rom.drop p = A ++ R) : rom.drop (p + A.length) = R := by
  rw [← List.drop_drop, h]; simp

end bytes

theorem encExprM_fits (e : ConLeche.Expr) (he : exprFits e = true) : ∀ seen,
    (∀ x ∈ seen, exprFits x = true) → ∀ x ∈ (encExprM seen e).2, exprFits x = true := by
  induction e with
  | bvar | sort | const => intro seen h; simpa [encExprM] using h
  | lit l => intro seen h; cases l <;> simpa [encExprM] using h
  | fvar i ty ih =>
    simp only [exprFits, Bool.and_eq_true] at he
    intro seen h; simp only [encExprM]; split
    · exact h
    · intro x hx; simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact ih he.2 seen h x hx
      · simp [exprFits, he.1, he.2]
  | app f a ihf iha | lam f a ihf iha | forallE f a ihf iha =>
    simp only [exprFits, Bool.and_eq_true] at he
    intro seen h; simp only [encExprM]; split
    · exact h
    · intro x hx; simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact iha he.2 _ (ihf he.1 seen h) x hx
      · simp [exprFits, he.1, he.2]
  | letE t v b iht ihv ihb =>
    simp only [exprFits, Bool.and_eq_true] at he
    intro seen h; simp only [encExprM]; split
    · exact h
    · intro x hx; simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact ihb he.2 _ (ihv he.1.2 _ (iht he.1.1 seen h)) x hx
      · simp [exprFits, he.1.1, he.1.2, he.2]
  | proj n i s ih =>
    simp only [exprFits, Bool.and_eq_true] at he
    intro seen h; simp only [encExprM]; split
    · exact h
    · intro x hx; simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact ih he.2 seen h x hx
      · simp [exprFits, he.1.1, he.1.2, he.2]

/-! ## The invariant and the canonicity argument -/

/-- What the decoder carries from node to node. -/
structure DecInv (mem : Mem) (a : AState) (seen : List ConLeche.Expr) (m : EMemo) : Prop where
  arena : ArenaD mem a
  memo : MemoR mem seen m
  nodup : seen.Nodup
  comp : ∀ x ∈ seen, IsComp x
  fits : ∀ x ∈ seen, exprFits x = true
  rset : RsetR mem
  ok : StateOK a
  emok : EMemoOK a.store m
  stk : (stkTop mem).toNat < 2 ^ 61
  ctl : 131 < (mem.arr64 CTL).size
  /-- The pool's mode (lane tierpool). -/
  mode : ModeOK mem

theorem decI_word_inj {v w : Word} (hv : v.toNat < 2 ^ 32) (hw : w.toNat < 2 ^ 32)
    (h : (decI v : EIdx) = decI w) : v = w := by
  have e1 := word_decE v hv
  have e2 := word_decE w hw
  rw [decE_eq] at e1 e2
  rw [← e1, ← e2, h]

/-- **The canonicity argument**: L interned a compound node to `h` and found `h` in no memo entry
(`rsetOK`, under `RsetR`); the node denotes `e`; so `e` is no key of the memo, and in particular not
in any prefix `seen` of the memo's list. -/
theorem canon_miss {mem : Mem} {a₂ a₃ : AState} {seen seen2 : List ConLeche.Expr} {m2 : EMemo}
    {e : ConLeche.Expr} {h : Word}
    (hM : MemoR mem seen2 m2) (hE : EMemoOK a₂.store m2) (hx : Ext a₂.store a₃.store)
    (hok : StateOK a₃) (hden : denoteE a₃.store (decI h) = some e) (hh : h.toNat < 2 ^ 32)
    (hR : RsetR mem) (hc : rsetOK mem h) (hsub : seen <+: seen2) : e ∉ seen := by
  intro he
  have he2 : e ∈ seen2 := hsub.subset he
  obtain ⟨hlt, hm⟩ := hM.hit he2
  have hd := denote_ext (hE _ _ hm) hx
  have heq := denoteE_inj hok.wf hden hd
  have hw := decI_word_inj hh hlt heq
  exact RsetR.miss hR hh hc (seen2.idxOf e)
    (by rw [hM.cnt]; exact List.idxOf_lt_length_iff.mpr he2) hw.symm

section dec
variable (rom : List UInt8) (hr : RomOK rom)

/-- The decoder claim at L fuel `n`. -/
def DecClaim (n : Nat) : Prop :=
  ∀ (mem : Mem) (a : AState) (pos : Word) (seen : List ConLeche.Expr) (m : EMemo) (h q : Word)
    (mem' : Mem), DecInv mem a seen m → romExprW rom n mem pos = some (h, q, mem') →
    ∃ e rest, rom.drop pos.toNat = (encExprM seen e).1 ++ rest ∧ exprFits e = true

include hr in
/-- A child of a compound node: decoded, the twin's run on it, the invariant after. -/
theorem dec_child {n : Nat} (hD : DecClaim rom n) {mem : Mem} {a : AState} {pos : Word}
    {seen : List ConLeche.Expr} {m : EMemo} {h q : Word} {mem' : Mem} (inv : DecInv mem a seen m)
    (hW : romExprW rom n mem pos = some (h, q, mem')) :
    ∃ e rest m' a', rom.drop pos.toNat = (encExprM seen e).1 ++ rest ∧ exprFits e = true ∧
      (internExprGo m e).run a = .ok ((m', decI h), a') ∧ DecInv mem' a' (encExprM seen e).2 m' ∧
      denoteE a'.store (decI h) = some e ∧ Ext a.store a'.store ∧ h.toNat < 2 ^ 32 ∧
      q.toNat = pos.toNat + (encExprM seen e).1.length ∧ MemFrame ExprA ExprC mem mem' := by
  obtain ⟨e, rest, hd, hfit⟩ := hD mem a pos seen m h q mem' inv hW
  obtain ⟨m', a', r, hR, hM, hlt, hq, hf, hs, hz⟩ :=
    romExprW_ok rom hr e hfit n mem a pos rest seen m h q mem' inv.arena inv.mode inv.memo hd inv.stk inv.ctl hW
  obtain ⟨hst, hden, hem⟩ := internExprGo_sstep e inv.ok inv.emok r
  exact ⟨e, rest, m', a', hd, hfit, r,
    ⟨hR, hM, encExprM_nodup e seen inv.nodup, encExprM_comp e seen inv.comp,
      encExprM_fits e hfit seen inv.fits, hz inv.rset, hst.ok, hem, by rw [hs]; exact inv.stk,
      by rw [hf.2.2.1]; exact inv.ctl, ((romExprW_topK rom n).1 _ _ _ _ _ hW).mode inv.arena.1.lit.1 inv.mode⟩,
    hden, hst.ext, hlt, hq, hf⟩

include hr in
/-- **The expression reader in the decoder direction**: a model run of `rom_expr` that returns,
from the decoder's invariant, read the canonical encoding (`encExprM seen e`) of a fitting
expression. -/
theorem romExprW_dec : ∀ n, DecClaim rom n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro mem a pos seen m h q mem' inv hW
  have hr' : rom.length < 2 ^ 63 := hr
  cases n with
  | zero => simp [romExprW] at hW
  | succ k =>
  by_cases h9 : romB rom pos = 9
  · -- a back reference
    rw [romExprW_ref rom k mem pos h9] at hW
    simp only [romRefW] at hW
    split at hW
    case isFalse => cases hW
    rename_i hok
    obtain ⟨hu, hmo⟩ := hok
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl, rfl⟩ := hW
    obtain ⟨hpos, hdrop⟩ := romB_tag rom pos 9 (by decide) (by rw [h9]; rfl)
    have hpos1 : (pos + 1).toNat = pos.toNat + 1 := by
      rw [UInt64.toNat_add]; simp; omega
    obtain ⟨-, -, hd1⟩ := u64_dec rom hr (pos + 1) hu
    have hk : (u64W rom (pos + 1)).toNat < seen.length := by
      rw [← inv.memo.cnt]; exact UInt64.lt_iff_toNat_lt.mp hmo
    have hmem : seen[(u64W rom (pos + 1)).toNat] ∈ seen := List.getElem_mem hk
    refine ⟨seen[(u64W rom (pos + 1)).toNat], rom.drop (pos.toNat + 1 + 8), ?_, inv.fits _ hmem⟩
    rw [encExprM_ref _ seen (inv.comp _ hmem) hmem, List.Nodup.idxOf_getElem inv.nodup, hdrop, ← hpos1, hd1,
      hpos1]
    simp
  have hpos1 : pos.toNat < rom.length → (pos + 1).toNat = pos.toNat + 1 := fun hp => by
    rw [UInt64.toNat_add]; simp; omega
  by_cases h2 : romB rom pos = 0 ∨ romB rom pos = 1 ∨ romB rom pos = 2 ∨ romB rom pos = 3
  · -- a leaf
    rw [romExprW_leaf rom k mem pos h9 h2] at hW
    cases k with
    | zero => simp [romLeafW] at hW
    | succ j =>
    rcases h2 with h0 | h0 | h0 | h0
    · -- bvar
      obtain ⟨hpos, hdrop⟩ := romB_tag rom pos 0 (by decide) (by rw [h0]; rfl)
      by_cases hu : u64OK rom (pos + 1)
      case neg => rw [h0, romLeafW_u64 rom j mem pos 0 (.inl rfl) hu] at hW; cases hW
      obtain ⟨-, -, hd1⟩ := u64_dec rom hr (pos + 1) hu
      refine ⟨.bvar (u64W rom (pos + 1)).toNat, rom.drop ((pos + 1).toNat + 8), ?_,
        by simp only [exprFits, decide_eq_true_eq]; exact UInt64.toNat_lt _⟩
      simp only [encExprM]
      rw [hdrop, ← hpos1 hpos, hd1]; simp
    · -- sort
      obtain ⟨hpos, hdrop⟩ := romB_tag rom pos 1 (by decide) (by rw [h0]; rfl)
      rw [h0, romLeafW_sort rom j mem pos 1 (by decide) rfl] at hW
      cases hU : romLevelW rom j mem (pos + 1) with
      | none => rw [hU] at hW; simp [exSortK] at hW
      | some r =>
      obtain ⟨hu, q₁, m₁⟩ := r
      obtain ⟨u, rest, hd1, fit, -⟩ := romLevelW_dec rom hr j mem (pos + 1) hu q₁ m₁ hU
      refine ⟨.sort u, rest, ?_, by simp [exprFits, fit]⟩
      simp only [encExprM]
      rw [hdrop, ← hpos1 hpos, hd1]; simp
    · -- const
      obtain ⟨hpos, hdrop⟩ := romB_tag rom pos 2 (by decide) (by rw [h0]; rfl)
      rw [h0, romLeafW_const rom j mem pos 2 (by decide) (by decide) rfl] at hW
      rcases hN : romNameW rom j mem (pos + 1) with _ | ⟨hn, q₁, m₁⟩ <;> rw [hN] at hW
      · simp [exConst2KN] at hW
      rw [exConst2KN_some] at hW
      cases hL : romLevelsW rom j m₁ q₁ with
      | none => rw [hL] at hW; simp [exConst2K] at hW
      | some r =>
      obtain ⟨hl, q₂, m₂⟩ := r
      obtain ⟨nm, restA, hdA, fitN, hq1⟩ := romNameW_dec rom hr j mem (pos + 1) hn q₁ m₁ hN
      obtain ⟨us, restB, hdB, fitL, hlen, -⟩ := romLevelsW_dec rom hr j m₁ q₁ hl q₂ m₂ hL
      refine ⟨.const nm us, restB, ?_, by simp [exprFits, fitN, fitL, hlen]⟩
      have hA := drop_after rom hdA
      rw [← hq1, hdB] at hA
      simp only [encExprM]
      rw [hdrop, ← hpos1 hpos, hdA, ← hA]; simp
    · -- a natVal literal
      obtain ⟨hpos, hdrop⟩ := romB_tag rom pos 3 (by decide) (by rw [h0]; rfl)
      by_cases hu : u64OK rom (pos + 1)
      case neg => rw [h0, romLeafW_u64 rom j mem pos 3 (.inr rfl) hu] at hW; cases hW
      obtain ⟨-, -, hd1⟩ := u64_dec rom hr (pos + 1) hu
      refine ⟨.lit (.natVal (u64W rom (pos + 1)).toNat), rom.drop ((pos + 1).toNat + 8), ?_,
        by simp only [exprFits, decide_eq_true_eq]; exact UInt64.toNat_lt _⟩
      simp only [encExprM]
      rw [hdrop, ← hpos1 hpos, hd1]; simp
  by_cases h4 : romB rom pos = 4 ∨ romB rom pos = 10
  · rw [romExprW_one rom k mem pos h9 h2 h4] at hW
    cases k with
    | zero => simp [romOneW] at hW
    | succ j =>
    rcases h4 with h0 | h0
    · -- fvar
      obtain ⟨hpos, hdrop⟩ := romB_tag rom pos 4 (by decide) (by rw [h0]; rfl)
      by_cases hu : u64OK rom (pos + 1)
      case neg => rw [h0] at hW; simp [romOneW, hu] at hW
      obtain ⟨-, hp9, hd1⟩ := u64_dec rom hr (pos + 1) hu
      rw [h0, romOneW_fvar rom j mem pos 4 rfl hu] at hW
      rcases hT : romExprW rom j mem (pos + 9) with _ | ⟨ht, q₁, m₁⟩ <;> rw [hT] at hW
      · simp [exFvarK] at hW
      rw [exFvarK_some] at hW
      obtain ⟨m₂, hI, hlt, rfl, -, hpw, rfl⟩ := exNodeK_inv hW
      obtain ⟨et, rest1, mt, a₁, hdt, fit1, r1, inv1, hden1, hx1, hlt1, hq1, hf1⟩ :=
        dec_child rom hr (ih j (by omega)) inv hT
      obtain ⟨ok2, -, res2⟩ := internFVar_D m₁ a₁ inv1.arena _ ht h hlt1 m₂ hI
      have hrun := AM.run_of_ok _ _ ok2
      obtain ⟨hst2, hdv⟩ := internE_sstep inv1.ok (viewOK_fvar (by simp [decE_eq, hden1])) hrun
      have hde : denoteE (AM.st (internE (.fvar (u64W rom (pos + 1)).toNat (decE ht))) a₁).store (decI h) =
          some (.fvar (u64W rom (pos + 1)).toNat et) := by
        rw [← decE_eq, ← res2, hdv]
        have hd' := denote_ext hden1 hst2.ext
        simp only [denoteEView, decE_eq] at hd' ⊢
        rw [hd']; rfl
      have hstore := fvinternW_store hI
      have hin := canon_miss (inv1.memo.frame (frame_romA hstore)) inv1.emok hst2.ext hst2.ok hde hlt
        (inv1.rset.frameS hstore) (mpushW_eq hpw).2.1 (encExprM_prefix et seen)
      refine ⟨.fvar (u64W rom (pos + 1)).toNat et, rest1, ?_, by
        simp only [exprFits, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨UInt64.toNat_lt _, fit1⟩⟩
      have henc : encExprM seen (.fvar (u64W rom (pos + 1)).toNat et) =
          (4 :: (u64B (u64W rom (pos + 1)).toNat ++ (encExprM seen et).1),
            (encExprM seen et).2 ++ [.fvar (u64W rom (pos + 1)).toNat et]) := by simp [encExprM, hin]
      rw [henc, hdrop, ← hpos1 hpos, hd1]
      have h9' : (pos + 1).toNat + 8 = (pos + 9).toNat := by
        rw [hpos1 hpos]; rw [UInt64.toNat_add]; simp; omega
      rw [h9', hdt]; simp
    · -- proj
      obtain ⟨hpos, hdrop⟩ := romB_tag rom pos 10 (by decide) (by rw [h0]; rfl)
      rw [h0, romOneW_proj rom j mem pos 10 (by decide) rfl] at hW
      cases hN : romNameW rom j mem (pos + 1) with
      | none => rw [hN] at hW; simp [exProjK] at hW
      | some r =>
      obtain ⟨hn, q₁, m₁⟩ := r
      by_cases hu : u64OK rom q₁
      case neg => rw [hN] at hW; simp [exProjK, hu] at hW
      rw [hN, exProjK_some (hu := hu)] at hW
      rcases hS : romExprW rom j m₁ (q₁ + 8) with _ | ⟨hs, q₂, m₂⟩ <;> rw [hS] at hW
      · simp [exProj2K] at hW
      rw [exProj2K_some] at hW
      obtain ⟨m₃, hI, hlt, rfl, -, hpw, rfl⟩ := exNodeK_inv hW
      obtain ⟨nm, restA, hdA, fitN, hqA⟩ := romNameW_dec rom hr j mem (pos + 1) hn q₁ m₁ hN
      obtain ⟨ok1, hR1, res1, -, -, hfn⟩ :=
        romNameW_ok rom hr nm fitN j mem a (pos + 1) restA hn q₁ m₁ inv.arena inv.mode hdA hN
      have run1 := AM.run_of_ok _ _ ok1
      obtain ⟨hstn, hdn⟩ := internName_sstep inv.ok run1
      rw [res1] at hdn
      have inv1 : DecInv m₁ (AM.st (internName nm) a) seen m :=
        ⟨hR1, inv.memo.frame (frame_romA hfn), inv.nodup, inv.comp, inv.fits, inv.rset.frameS hfn, hstn.ok,
          inv.emok.mono hstn.ext, by rw [frame_exprA_stk hfn]; exact inv.stk, by rw [hfn.2.2.1]; exact inv.ctl,
          (romNameW_topK hN).mode inv.arena.1.lit.1 inv.mode⟩
      obtain ⟨es, rest2, ms, a₂, hd2, fit2, r2, inv2, hden2, hx2, hlt2, hq2, hf2⟩ :=
        dec_child rom hr (ih j (by omega)) inv1 hS
      obtain ⟨ok3, -, res3⟩ := mkProj_ok m₂ a₂ inv2.arena hn (u64W rom q₁) hs h m₃ hI
      have hrun := AM.run_of_ok _ _ ok3
      obtain ⟨hst3, hdv⟩ := internE_sstep inv2.ok
        (viewOK_proj (nview_isSome_of_denote (denoteN_ext hdn hx2)) (by simp [decE_eq, hden2])) hrun
      have hde : denoteE (AM.st (internE (.proj (decI hn) (u64W rom q₁).toNat (decE hs))) a₂).store (decI h) =
          some (.proj nm (u64W rom q₁).toNat es) := by
        rw [← decE_eq, ← res3, hdv]
        simp only [denoteEView, opt2_eq_some_iff]
        have hd' := denote_ext hden2 hst3.ext
        simp only [decE_eq] at hd' ⊢
        exact ⟨nm, es, denoteN_ext hdn (hx2.trans hst3.ext), hd', rfl⟩
      have hstore := mkProjW_store hI
      have hin := canon_miss (inv2.memo.frame (frame_romA hstore)) inv2.emok hst3.ext hst3.ok hde hlt
        (inv2.rset.frameS hstore) (mpushW_eq hpw).2.1 (encExprM_prefix es seen)
      refine ⟨.proj nm (u64W rom q₁).toNat es, rest2, ?_, by
        simp only [exprFits, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨fitN, UInt64.toNat_lt _⟩, fit2⟩⟩
      have henc : encExprM seen (.proj nm (u64W rom q₁).toNat es) =
          (10 :: (encName nm ++ u64B (u64W rom q₁).toNat ++ (encExprM seen es).1),
            (encExprM seen es).2 ++ [.proj nm (u64W rom q₁).toNat es]) := by simp [encExprM, hin]
      obtain ⟨-, hq8, hdq⟩ := u64_dec rom hr q₁ hu
      have hA := drop_after rom hdA
      rw [← hqA, hdq, ← hq8, hd2] at hA
      rw [henc, hdrop, ← hpos1 hpos, hdA, ← hA]; simp
  · -- app, lam, forallE, letE
    rw [romExprW_two rom k mem pos h9 h2 h4] at hW
    cases k with
    | zero => simp [romTwoW] at hW
    | succ j =>
    rw [romTwoW_eq] at hW
    cases hF : romExprW rom j mem (pos + 1) with
    | none => rw [hF] at hW; simp [exOneK] at hW
    | some r =>
    obtain ⟨hf, q₁, m₁⟩ := r
    by_cases hb8 : romB rom pos = 8
    · -- letE
      obtain ⟨hpos, hdrop⟩ := romB_tag rom pos 8 (by decide) (by rw [hb8]; rfl)
      rw [hF, exOneK_let (ht := hb8)] at hW
      rcases hV : romExprW rom j m₁ q₁ with _ | ⟨hv, q₂, m₂⟩ <;> rw [hV] at hW
      · simp [exLet2K] at hW
      rw [exLet2K_some] at hW
      rcases hX : romExprW rom j m₂ q₂ with _ | ⟨hx, q₃, m₃⟩ <;> rw [hX] at hW
      · simp [exLet3K] at hW
      rw [exLet3K_some] at hW
      obtain ⟨m₄, hI, hlt, rfl, -, hpw, rfl⟩ := exNodeK_inv hW
      obtain ⟨et, rest1, mt, a₁, hd1, fit1, r1, inv1, hden1, hx1, hlt1, hq1, hf1⟩ :=
        dec_child rom hr (ih j (by omega)) inv hF
      obtain ⟨ev, rest2, mv, a₂, hd2, fit2, r2, inv2, hden2, hx2, hlt2, hq2, hf2⟩ :=
        dec_child rom hr (ih j (by omega)) inv1 hV
      obtain ⟨ex, rest3, mx, a₃, hd3, fit3, r3, inv3, hden3, hx3, hlt3, hq3, hf3⟩ :=
        dec_child rom hr (ih j (by omega)) inv2 hX
      obtain ⟨ok4, -, res4⟩ := mkLet_ok m₃ a₃ inv3.arena hf hv hx h m₄ hI
      have hrun := AM.run_of_ok _ _ ok4
      obtain ⟨hst4, hdv⟩ := internE_sstep inv3.ok
        (viewOK_letE (by simp [decE_eq, denote_ext hden1 (hx2.trans hx3)])
          (by simp [decE_eq, denote_ext hden2 hx3]) (by simp [decE_eq, hden3])) hrun
      have hde : denoteE (AM.st (internE (.letE (decE hf) (decE hv) (decE hx))) a₃).store (decI h) =
          some (.letE et ev ex) := by
        rw [← decE_eq, ← res4, hdv]
        simp only [denoteEView, opt3_eq_some_iff]
        have d1 := denote_ext hden1 ((hx2.trans hx3).trans hst4.ext)
        have d2 := denote_ext hden2 (hx3.trans hst4.ext)
        have d3 := denote_ext hden3 hst4.ext
        simp only [decE_eq] at d1 d2 d3 ⊢
        exact ⟨et, ev, ex, d1, d2, d3, rfl⟩
      have hstore := mkLetW_store hI
      have hin := canon_miss (inv3.memo.frame (frame_romA hstore)) inv3.emok hst4.ext hst4.ok hde hlt
        (inv3.rset.frameS hstore) (mpushW_eq hpw).2.1
        (((encExprM_prefix et seen).trans (encExprM_prefix ev _)).trans (encExprM_prefix ex _))
      refine ⟨.letE et ev ex, rest3, ?_, by simp [exprFits, fit1, fit2, fit3]⟩
      have henc : encExprM seen (.letE et ev ex) =
          (8 :: ((encExprM seen et).1 ++ (encExprM (encExprM seen et).2 ev).1 ++
            (encExprM (encExprM (encExprM seen et).2 ev).2 ex).1),
            (encExprM (encExprM (encExprM seen et).2 ev).2 ex).2 ++ [.letE et ev ex]) := by
        simp [encExprM, hin]
      have hr1 := drop_after rom hd1
      rw [← hq1, hd2] at hr1
      have hr2 := drop_after rom hd2
      rw [← hq2, hd3] at hr2
      rw [henc, hdrop, ← hpos1 hpos, hd1, ← hr1, ← hr2]
      simp
    rw [hF, exOneK_two (ht := hb8)] at hW
    rcases hX : romExprW rom j m₁ q₁ with _ | ⟨hx, q₂, m₂⟩ <;> rw [hX] at hW
    · simp [exTwoK] at hW
    by_cases hb5 : romB rom pos = 5
    · -- app
      rw [exTwoK_app (ht := hb5)] at hW
      obtain ⟨m₃, hI, hlt, rfl, -, hpw, rfl⟩ := exNodeK_inv hW
      obtain ⟨ef, rest1, mf, a₁, hd1, fit1, r1, inv1, hden1, hx1, hlt1, hq1, hf1⟩ :=
        dec_child rom hr (ih j (by omega)) inv hF
      obtain ⟨ex, rest2, mx, a₂, hd2, fit2, r2, inv2, hden2, hx2, hlt2, hq2, hf2⟩ :=
        dec_child rom hr (ih j (by omega)) inv1 hX
      obtain ⟨ok3, -, res3⟩ := mkApp_ok m₂ a₂ inv2.arena hf hx h m₃ hI
      have hrun := AM.run_of_ok _ _ ok3
      obtain ⟨hst3, hdv⟩ := internE_sstep inv2.ok
        (viewOK_app (by simp [decE_eq, denote_ext hden1 hx2]) (by simp [decE_eq, hden2])) hrun
      have hde : denoteE (AM.st (internE (.app (decE hf) (decE hx))) a₂).store (decI h) =
          some (.app ef ex) := by
        rw [← decE_eq, ← res3, hdv]
        simp only [denoteEView, opt2_eq_some_iff]
        exact ⟨ef, ex, denote_ext (denote_ext hden1 hx2) hst3.ext, denote_ext hden2 hst3.ext, rfl⟩
      have hstore := mkAppW_store hI
      have hin := canon_miss (inv2.memo.frame (frame_romA hstore)) inv2.emok hst3.ext hst3.ok hde hlt
        (inv2.rset.frameS hstore) (mpushW_eq hpw).2.1
        ((encExprM_prefix ef seen).trans (encExprM_prefix ex _))
      refine ⟨.app ef ex, rest2, ?_, by simp [exprFits, fit1, fit2]⟩
      have henc : encExprM seen (.app ef ex) = (5 :: ((encExprM seen ef).1 ++ (encExprM (encExprM seen ef).2 ex).1),
          (encExprM (encExprM seen ef).2 ex).2 ++ [.app ef ex]) := by simp [encExprM, hin]
      rw [henc]
      obtain ⟨hpos, hdrop⟩ := romB_tag rom pos 5 (by decide) (by rw [hb5]; rfl)
      have hr1 := drop_after rom hd1
      rw [← hq1, hd2] at hr1
      rw [hdrop, ← hpos1 hpos, hd1, ← hr1]
      simp
    by_cases hb6 : romB rom pos = 6
    · -- lam
      rw [exTwoK_lam (ht := hb6)] at hW
      obtain ⟨m₃, hI, hlt, rfl, -, hpw, rfl⟩ := exNodeK_inv hW
      obtain ⟨ef, rest1, mf, a₁, hd1, fit1, r1, inv1, hden1, hx1, hlt1, hq1, hf1⟩ :=
        dec_child rom hr (ih j (by omega)) inv hF
      obtain ⟨ex, rest2, mx, a₂, hd2, fit2, r2, inv2, hden2, hx2, hlt2, hq2, hf2⟩ :=
        dec_child rom hr (ih j (by omega)) inv1 hX
      obtain ⟨ok3, -, res3⟩ := mkLam_ok m₂ a₂ inv2.arena hf hx h m₃ hI
      have hrun := AM.run_of_ok _ _ ok3
      obtain ⟨hst3, hdv⟩ := internE_sstep inv2.ok
        (viewOK_lam (by simp [decE_eq, denote_ext hden1 hx2]) (by simp [decE_eq, hden2])) hrun
      have hde : denoteE (AM.st (internE (.lam (decE hf) (decE hx))) a₂).store (decI h) =
          some (.lam ef ex) := by
        rw [← decE_eq, ← res3, hdv]
        simp only [denoteEView, opt2_eq_some_iff]
        exact ⟨ef, ex, denote_ext (denote_ext hden1 hx2) hst3.ext, denote_ext hden2 hst3.ext, rfl⟩
      have hstore := mkLamW_store hI
      have hin := canon_miss (inv2.memo.frame (frame_romA hstore)) inv2.emok hst3.ext hst3.ok hde hlt
        (inv2.rset.frameS hstore) (mpushW_eq hpw).2.1
        ((encExprM_prefix ef seen).trans (encExprM_prefix ex _))
      refine ⟨.lam ef ex, rest2, ?_, by simp [exprFits, fit1, fit2]⟩
      have henc : encExprM seen (.lam ef ex) = (6 :: ((encExprM seen ef).1 ++ (encExprM (encExprM seen ef).2 ex).1),
          (encExprM (encExprM seen ef).2 ex).2 ++ [.lam ef ex]) := by simp [encExprM, hin]
      rw [henc]
      obtain ⟨hpos, hdrop⟩ := romB_tag rom pos 6 (by decide) (by rw [hb6]; rfl)
      have hr1 := drop_after rom hd1
      rw [← hq1, hd2] at hr1
      rw [hdrop, ← hpos1 hpos, hd1, ← hr1]
      simp
    by_cases hb7 : romB rom pos = 7
    · -- forallE
      rw [exTwoK_forall (ht := hb7)] at hW
      obtain ⟨m₃, hI, hlt, rfl, -, hpw, rfl⟩ := exNodeK_inv hW
      obtain ⟨ef, rest1, mf, a₁, hd1, fit1, r1, inv1, hden1, hx1, hlt1, hq1, hf1⟩ :=
        dec_child rom hr (ih j (by omega)) inv hF
      obtain ⟨ex, rest2, mx, a₂, hd2, fit2, r2, inv2, hden2, hx2, hlt2, hq2, hf2⟩ :=
        dec_child rom hr (ih j (by omega)) inv1 hX
      obtain ⟨ok3, -, res3⟩ := mkForall_ok m₂ a₂ inv2.arena hf hx h m₃ hI
      have hrun := AM.run_of_ok _ _ ok3
      obtain ⟨hst3, hdv⟩ := internE_sstep inv2.ok
        (viewOK_forallE (by simp [decE_eq, denote_ext hden1 hx2]) (by simp [decE_eq, hden2])) hrun
      have hde : denoteE (AM.st (internE (.forallE (decE hf) (decE hx))) a₂).store (decI h) =
          some (.forallE ef ex) := by
        rw [← decE_eq, ← res3, hdv]
        simp only [denoteEView, opt2_eq_some_iff]
        exact ⟨ef, ex, denote_ext (denote_ext hden1 hx2) hst3.ext, denote_ext hden2 hst3.ext, rfl⟩
      have hstore := mkForallW_store hI
      have hin := canon_miss (inv2.memo.frame (frame_romA hstore)) inv2.emok hst3.ext hst3.ok hde hlt
        (inv2.rset.frameS hstore) (mpushW_eq hpw).2.1
        ((encExprM_prefix ef seen).trans (encExprM_prefix ex _))
      refine ⟨.forallE ef ex, rest2, ?_, by simp [exprFits, fit1, fit2]⟩
      have henc : encExprM seen (.forallE ef ex) = (7 :: ((encExprM seen ef).1 ++ (encExprM (encExprM seen ef).2 ex).1),
          (encExprM (encExprM seen ef).2 ex).2 ++ [.forallE ef ex]) := by simp [encExprM, hin]
      rw [henc]
      obtain ⟨hpos, hdrop⟩ := romB_tag rom pos 7 (by decide) (by rw [hb7]; rfl)
      have hr1 := drop_after rom hd1
      rw [← hq1, hd2] at hr1
      rw [hdrop, ← hpos1 hpos, hd1, ← hr1]
      simp
    simp [exTwoK, hb5, hb6, hb7] at hW

end dec

end L.Rom
