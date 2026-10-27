import ConAgua.Arena.IndPos2SpecQ

/-! # `IndPos2`, the `nestPos` block (lane `indproofs2`, helper `pos2`): the relational steps,
`nest_fields` and `nest_ctors_walk`. -/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- A `Π` handle's view: its domain and body, decoded. -/
theorem pos2_forall_view {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem} {a : AState}
    {w : Word} (hS : StageR dn vis fe m a) (hw : H w) (h6 : w >>> 28 = 6) (hne : eViewW m w ≠ []) :
    ∃ d b, eViewW m w = [6, d, b, 0] ∧ H d ∧ H b ∧
      (viewBind (decI w)).run a = .ok (some (decI d, decI b), a) ∧ (decI w : EIdx).tag = ETag.forallE := by
  obtain ⟨hvok, hew⟩ := eViewW_forall m w h6 hne
  obtain ⟨-, hty, hb⟩ := view_forall m a hS.1.arena.1 w hw hvok h6
  have hvb := viewBind_forall m a hS.1.arena.1 w hw hvok h6
  exact ⟨_, _, hew, hty, hb, by rw [viewBind_run']; simp only [← decE_eq]; rw [hvb],
    (decE_tag_forall w hw).mpr h6⟩

theorem pos2_word_add {x y : Word} (h : ¬ x + y < x) : (x + y).toNat = x.toNat + y.toNat := by
  rcases Nat.lt_or_ge (x.toNat + y.toNat) (2 ^ 64) with hl | hl
  · exact word_add_toNat hl
  · exfalso; apply h; apply UInt64.lt_iff_toNat_lt.mpr; rw [UInt64.toNat_add]
    have := x.toNat_lt; have := y.toNat_lt; omega

theorem pos2_word_succ {x : Word} (h : ¬ x + 1 = 0) : (x + 1).toNat = x.toNat + 1 := by
  rcases Nat.lt_or_ge (x.toNat + 1) (2 ^ 64) with hl | hl
  · exact word_add_toNat (by simpa using hl)
  · exfalso; apply h; apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; have := x.toNat_lt; simp; omega

theorem pos2_word_pred {x : Word} (h : x ≠ 0) : (x - 1).toNat = x.toNat - 1 := by
  have : x.toNat ≠ 0 := fun e => h (UInt64.toNat_inj.mp (by simpa using e))
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp

theorem pos2_rd_grow {m m' : Mem} (hg : IWGrow m m') {x : Word} (hx : x.toNat < iwTop m) :
    rdW (m'.arr64 IW) x = rdW (m.arr64 IW) x := by simp only [rdW]; rw [hg.2.2.1 _ hx]

/-- The words of a `NestState` record, read after the pool grew. -/
theorem pos2_ns_rd {m m' : Mem} (hg : IWGrow m m') {p : Word} (hp : p.toNat + 6 ≤ iwTop m)
    (htop : iwTop m < 2 ^ 64) (i : Word) (hi : i.toNat < 6) : rdW (m'.arr64 IW) (p + i) = rdW (m.arr64 IW) (p + i) :=
  pos2_rd_grow hg (by rw [word_add_toNat (by omega)]; omega)

/-- A handle slice split at `k`. -/
theorem pos2_decHL_split {k : IdxKind} {m : Mem} {o l n : Nat} {xs : List (Idx k)} (h : decHL m o l = some xs)
    (hn : n ≤ l) : decHL m o n = some (xs.take n) ∧ decHL m (o + n) (l - n) = some (xs.drop n) := by
  obtain ⟨hl, hg⟩ := pos2_hslice_get h
  have get : ∀ j (hj : j < xs.length), iwH m (o + j) = some xs[j] := fun j hj => by
    have := mapM_opt_get (fun j => (hd? (iwA m) (o + j) : Option (Idx k))) (List.range l) xs h j
      (by simp; omega)
    simpa [iwH] using this
  constructor
  · have := decHL_of_get m (xs.take n) o (fun j hj => by
      simp only [List.length_take] at hj; rw [List.getElem_take]; exact get j (by omega))
    simpa [List.length_take, hl, Nat.min_eq_left hn] using this
  · have := decHL_of_get m (xs.drop n) (o + n) (fun j hj => by
      simp only [List.length_drop] at hj; rw [List.getElem_drop, show o + n + j = o + (n + j) by omega]
      exact get (n + j) (by omega))
    simpa [List.length_drop, hl] using this

/-- `aL == nPc + nI` on words is the twin's comparison, `nPc ≤ aL`. -/
theorem pos2_len_eq {aL nPc nI : Word} (h : nPc.toNat ≤ aL.toNat) :
    (aL = nPc + nI) ↔ aL.toNat = nPc.toNat + nI.toNat := by
  constructor
  · intro e
    rcases Nat.lt_or_ge (nPc.toNat + nI.toNat) (2 ^ 64) with hl | hl
    · rw [e, word_add_toNat hl]
    · exfalso
      have := congrArg UInt64.toNat e; rw [UInt64.toNat_add] at this
      have := nI.toNat_lt; have := nPc.toNat_lt
      omega
  · intro e
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add, ← e]; exact (Nat.mod_eq_of_lt aL.toNat_lt).symm

theorem pos2_contains_map (ws : List Word) (hw : ∀ w ∈ ws, H w) (x : Word) (hx : H x) :
    (ws.map (decI : Word → NIdx)).contains (decI x) = ws.contains x := by
  rw [Bool.eq_iff_iff]
  simp only [List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨v, hv, e⟩
    rw [decI_inj (hw v hv) hx e] at hv; exact hv
  · intro h; exact ⟨x, h, rfl⟩

theorem pos2_getD2 (vl : List Word) : vl.getD 2 0 = vl.tail.tail.headD 0 := by
  rcases vl with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> rfl

section steps
variable (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)

end steps

end L.Ind
