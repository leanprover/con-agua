import ConAgua.Rom.Dec
import ConRon.Bridge.Frontend.Shared

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

open ConRon.Arena ConRon.Bridge ConRon.Bridge.Frontend

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

end L.Rom
