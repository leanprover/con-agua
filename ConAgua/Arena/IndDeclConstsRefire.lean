module

public import ConAgua.Arena.IndSumSpec.ConsBlockRecsTF
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import all ConAgua.Arena.IndDeclConsts

@[expose] public section

/-!
# A declaration's constants: the recursor rules refired (lane `ronsync2`, stage 3)

`rules_refire(d, s, cnt, kind, lo, ll, po, pl)` writes `cnt` rule records at `d`, each the
record at `s + Rule.size * j` with the fire `(kind, lo, ll, po, pl)` (`{ · with fire := f }`, con-ron's
`blockRecs`): the memory is `wrERo` of the records' images (`rrW_mem`), and each record decodes as
the rule refired (`decRule_refire`).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The memory after one record's eight field stores (each copy reads the memory of its time). -/
def rrMem (m1 : Mem) (q old k flo fll fpo fpl : Word) : Mem :=
  let m2 := erecPutMem m1 q (erRd m1 old)
  let m3 := erecPutMem m2 (q + Rule.nfields) (erRd m2 (old + Rule.nfields))
  let m8 := erecPutMem (erecPutMem (erecPutMem (erecPutMem (erecPutMem m3 (q + Rule.fire) k)
    (q + Rule.lvlsOff) flo) (q + Rule.lvlsLen) fll) (q + Rule.pinsOff) fpo) (q + Rule.pinsLen) fpl
  erecPutMem m8 (q + Rule.rhs) (erRd m8 (old + Rule.rhs))

/-- **The model of `rules_refire(d, s, cnt, k, lo, ll, po, pl)`** at exec fuel `n`. -/
l_model rr_spec (p : Prog) (hpu : p.lookup "erec_put" = some erecPut)
    (hp : p.lookup "rules_refire" = some rulesRefire)
  fns [hp ↦ rrW list]
  specs [erecPut_specM p hpu n]
  grind [arena_grind]

/-- `rrW`'s recursive arm by its memory `rrMem`. -/
theorem rrW_cons {n : Nat} {m : Mem} {d s cnt k lo ll po pl : Word} (h : cnt ≠ 0) :
    rrW (n + 1) m d s cnt k lo ll po pl =
      rrW.k_rules_refire (rrW n (rrMem m d s k lo ll po pl) (d + Rule.size) (s + Rule.size) (cnt - 1)
        k lo ll po pl) := by
  rw [rrW.arm2 (hc1 := h)]; rfl

/-! ## The written words -/

theorem add_ruleCtor (s : Word) : s + Rule.ctor = s := by simp [Rule.ctor]

/-- The fields a refired record copies from its source: the constructor, the field count, the
right-hand side. -/
def copiedF : List Word := [Rule.ctor, Rule.nfields, Rule.rhs]

theorem copiedF_lt : ∀ f ∈ copiedF, f.toNat < Rule.size.toNat := by
  intro f hf
  simp only [copiedF, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact Rule.ctor_lt
  · exact Rule.nfields_lt
  · exact Rule.rhs_lt

/-- One refired record's image: the copied fields, the given fire. -/
def refireImg1 (m : Mem) (s k lo ll po pl : Word) : List (Option Word) :=
  Rule.img (erRd m s) (erRd m (s + Rule.nfields)) k lo ll po pl (erRd m (s + Rule.rhs))

theorem rrMem_eq {m1 : Mem} {q old k flo fll fpo fpl : Word}
    (hfr : ∀ f ∈ copiedF, ErApart q Rule.size.toNat (old + f)) :
    rrMem m1 q old k flo fll fpo fpl = wrERo m1 q (refireImg1 m1 old k flo fll fpo fpl) := by
  have fA : ∀ f ∈ copiedF, ∀ g : Word, g.toNat < Rule.size.toNat →
      erTier (old + f) ≠ erTier (q + g) ∨ erOff (old + f) ≠ erOff (q + g) := fun f hf g hg => by
    have := hfr f hf g.toNat hg
    rwa [UInt64.ofNat_toNat] at this
  have a1 := fA Rule.nfields (by simp [copiedF])
  have a8 := fA Rule.rhs (by simp [copiedF])
  have q0 : ∀ x : Word, (erTier x ≠ erTier (q + Rule.ctor) ∨ erOff x ≠ erOff (q + Rule.ctor)) →
      erTier x ≠ erTier q ∨ erOff x ≠ erOff q := fun x h => by rwa [add_ruleCtor] at h
  simp only [rrMem]
  simp (disch := first
    | exact q0 _ (a1 _ Rule.ctor_lt) | exact q0 _ (a8 _ Rule.ctor_lt)
    | exact a1 _ (by decide) | exact a8 _ (by decide))
    only [erRd_erecPutMem_ne]
  -- the image's entries in order (the layout's numbers: a whole-record writer)
  simp [refireImg1, wrERo, Rule.img, recImg, Rule.ctor, Rule.nfields, Rule.fire, Rule.lvlsOff,
    Rule.lvlsLen, Rule.pinsOff, Rule.pinsLen, Rule.rhs, Rule.size, List.replicate, UInt64.add_assoc]

/-- The image `rules_refire` writes: each source record refired. -/
def refireImg (m : Mem) (k lo ll po pl : Word) : Word → Nat → List (Option Word)
  | _, 0 => []
  | s, c + 1 => refireImg1 m s k lo ll po pl ++ refireImg m k lo ll po pl (s + Rule.size) c

theorem refireImg1_length (m : Mem) (s k lo ll po pl : Word) :
    (refireImg1 m s k lo ll po pl).length = Rule.size.toNat := Rule.img_length ..

theorem refireImg_length (m : Mem) (k lo ll po pl : Word) :
    ∀ (s : Word) (c : Nat), (refireImg m k lo ll po pl s c).length = Rule.size.toNat * c
  | _, 0 => rfl
  | s, c + 1 => by
    simp only [refireImg, List.length_append, refireImg1_length, refireImg_length m k lo ll po pl _ c,
      Nat.mul_succ]
    omega

/-- The `j`-th record of a run of rules at `s`. -/
def rpos (s : Word) (j : Nat) : Word := s + UInt64.ofNat (Rule.size.toNat * j)

theorem rpos_zero (s : Word) : rpos s 0 = s := by simp [rpos]

theorem rpos_succ (s : Word) (j : Nat) : rpos (s + Rule.size) j = rpos s (j + 1) := by
  simp only [rpos]
  rw [Nat.mul_succ, UInt64.ofNat_add, UInt64.ofNat_toNat]; ac_rfl

/-- The source words read the same: the written image agrees. -/
theorem refireImg_congr {m m' : Mem} (k lo ll po pl : Word) :
    ∀ (s : Word) (c : Nat), (∀ j < c, ∀ f ∈ copiedF, erRd m' (rpos s j + f) = erRd m (rpos s j + f)) →
      refireImg m' k lo ll po pl s c = refireImg m k lo ll po pl s c
  | _, 0, _ => rfl
  | s, c + 1, h => by
    simp only [refireImg, refireImg1]
    have h0 := h 0 (by omega) Rule.ctor (by simp [copiedF])
    have h1 := h 0 (by omega) Rule.nfields (by simp [copiedF])
    have h8 := h 0 (by omega) Rule.rhs (by simp [copiedF])
    rw [rpos_zero, add_ruleCtor] at h0
    rw [rpos_zero] at h1 h8
    rw [h0, h1, h8, refireImg_congr (m := m) (m' := m') k lo ll po pl (s + Rule.size) c (fun j hj f hf => by
      rw [rpos_succ]; exact h (j + 1) (by omega) f hf)]

/-- **`rules_refire` writes the refired records**: the memory is `wrERo` of their images. -/
theorem rrW_mem (k lo ll po pl : Word) : ∀ (n : Nat) (m m' : Mem) (d s cnt : Word) (r : List Word),
    rrW n m d s cnt k lo ll po pl = some (r, m') →
    (∀ j < cnt.toNat, ∀ f ∈ copiedF, ErApart d (Rule.size.toNat * cnt.toNat) (rpos s j + f)) →
    m' = wrERo m d (refireImg m k lo ll po pl s cnt.toNat)
  | 0, _, _, _, _, _, _, h, _ => by simp [rrW] at h
  | n + 1, m, m', d, s, cnt, r, h, hfr => by
    by_cases h0 : cnt = 0
    · rw [rrW.arm1 (hc1 := h0)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      subst h0; rw [← h.2]; simp [refireImg, wrERo]
    rw [rrW_cons h0] at h
    have hl0 : cnt.toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.mp (by simpa using e))
    have hl1 : (cnt - 1).toNat = cnt.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp
    have hS := Rule.size_pos
    have hSc : Rule.size.toNat * cnt.toNat = Rule.size.toNat + Rule.size.toNat * (cnt.toNat - 1) := by
      rw [Nat.add_comm, ← Nat.mul_succ]; congr 1; omega
    rcases h2 : rrW n (rrMem m d s k lo ll po pl) (d + Rule.size) (s + Rule.size) (cnt - 1) k lo ll po pl
      with _ | ⟨r2, m2⟩ <;> simp only [h2, rrW.k_rules_refire, reduceCtorEq] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
    have hfr0 : ∀ f ∈ copiedF, ErApart d Rule.size.toNat (s + f) := fun f hf => by
      have := hfr 0 (by omega) f hf
      rw [rpos_zero] at this
      exact this.mono (by rw [hSc]; omega)
    rw [rrMem_eq hfr0] at h2
    have hdS : d + Rule.size = d + UInt64.ofNat Rule.size.toNat := by rw [UInt64.ofNat_toNat]
    have ih := rrW_mem k lo ll po pl n _ m2 (d + Rule.size) (s + Rule.size) (cnt - 1) r2 h2
      (fun j hj f hf => by
        rw [hl1] at hj ⊢
        rw [hdS, rpos_succ]
        have := hfr (j + 1) (by omega) f hf
        rw [hSc] at this
        exact ErApart.shift this)
    rw [ih, hl1, refireImg_congr (m := m) k lo ll po pl (s + Rule.size) (cnt.toNat - 1) (fun j hj f hf => by
      rw [rpos_succ]
      exact erRd_wrERo_ne _ _ _ _ ((hfr (j + 1) (by omega) f hf).mono
        (by rw [refireImg1_length, hSc]; omega)))]
    conv => rhs; rw [show cnt.toNat = (cnt.toNat - 1) + 1 by omega]
    simp only [refireImg]
    rw [wrERo_append, refireImg1_length, ← hdS]

theorem refireImg_get (m : Mem) (k lo ll po pl : Word) : ∀ (s : Word) (c j i : Nat), j < c →
    i < Rule.size.toNat →
    (refireImg m k lo ll po pl s c)[Rule.size.toNat * j + i]? =
      (refireImg1 m (rpos s j) k lo ll po pl)[i]?
  | _, 0, _, _, hj, _ => absurd hj (by omega)
  | s, c + 1, 0, i, _, hi => by
    simp only [refireImg, Nat.mul_zero, Nat.zero_add, rpos_zero]
    rw [List.getElem?_append_left (by rw [refireImg1_length]; omega)]
  | s, c + 1, j + 1, i, hj, hi => by
    simp only [refireImg]
    rw [List.getElem?_append_right (by rw [refireImg1_length, Nat.mul_succ]; omega)]
    have e : Rule.size.toNat * (j + 1) + i - (refireImg1 m s k lo ll po pl).length =
        Rule.size.toNat * j + i := by
      rw [refireImg1_length, Nat.mul_succ]; omega
    rw [e, refireImg_get m k lo ll po pl (s + Rule.size) c j i (by omega) hi, rpos_succ]

/-! ## The refired records decode -/

/-- A fire `(kind, lo, ll, po, pl)` (slices in the record pool) decoding as `f`. -/
def FireAt (R : Nat → Option Word) (k lo ll po pl : Word) : IRecRuleFire → Prop
  | .plain => k = 0
  | .nested lv ps => k = 1 ∧ hslice? R lo.toNat ll.toNat = some lv ∧ hslice? R po.toNat pl.toNat = some ps
  | .levels _ => False

theorem FireAt.ext {R R' : Nat → Option Word} (hx : ArrExt R R') {k lo ll po pl : Word} {f : IRecRuleFire}
    (h : FireAt R k lo ll po pl f) : FireAt R' k lo ll po pl f := by
  cases f with
  | plain => exact h
  | nested lv ps => exact ⟨h.1, hx.hslice? h.2.1, hx.hslice? h.2.2⟩
  | levels _ => exact h.elim

/-- A rule record whose plain fields are copied and whose fire is `f`, its words at `q'`. -/
theorem decRule_refireAt {R R' : Nat → Option Word} {q q' : Nat} {rl : IRecRule} {k lo ll po pl : Word}
    {f : IRecRuleFire} (h : decRule R q = some rl)
    (h0 : R' q' = R q) (h1 : R' (q' + Rule.nfields.toNat) = R (q + Rule.nfields.toNat))
    (h8 : R' (q' + Rule.rhs.toNat) = R (q + Rule.rhs.toNat))
    (h3 : R' (q' + Rule.fire.toNat) = some k) (h4 : R' (q' + Rule.lvlsOff.toNat) = some lo)
    (h5 : R' (q' + Rule.lvlsLen.toNat) = some ll) (h6 : R' (q' + Rule.pinsOff.toNat) = some po)
    (h7 : R' (q' + Rule.pinsLen.toNat) = some pl) (hf : FireAt R' k lo ll po pl f) :
    decRule R' q' = some { rl with fire := f } := by
  cases f with
  | nested lv ps =>
    obtain ⟨rfl, hl, hp⟩ := hf
    exact decRule_nested h h0 h1 h8 h3 h4 h5 h6 h7 hl hp
  | levels _ => exact hf.elim
  | plain =>
    have hk : k = 0 := hf
    subst hk
    exact L.Arena.decRule_refire h h0 h1 h8 (show nat? R' _ = some 0 by simp [nat?, h3])

/-- **`rules_refire` into a fresh run, under the stage relation**: the run decodes as the source
rules, each refired. -/
theorem rrW_ok {vis : Word} {fe : IFEnv} {a : AState} {n : Nat} {m m1 m' : Mem}
    {run o cnt k lo ll po pl : Word} {r : List Word} {rules : List IRecRule} {f : IRecRuleFire}
    (ha : erAllocW m (Rule.size * cnt) = some (run, m1)) (hS : StageR vis fe m a) (hc : cnt.toNat < 2 ^ 32)
    (hd : decRules (erecP m) o.toNat cnt.toNat = some rules)
    (hf : FireAt (erecP m) k lo ll po pl f)
    (h : rrW n m1 run o cnt k lo ll po pl = some (r, m')) :
    StageR vis fe m' a ∧ IWGrow m m' ∧
      decRules (erecP m') run.toNat cnt.toNat = some (rules.map fun rl => { rl with fire := f }) := by
  have hS0 := Rule.size_pos
  have hk : (Rule.size * cnt).toNat = Rule.size.toNat * cnt.toNat := by
    have : Rule.size.toNat * cnt.toNat ≤ 64 * cnt.toNat := Nat.mul_le_mul_right _ Rule.size_le
    rw [UInt64.toNat_mul, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨-, hf1, -⟩ := erAllocW_spec ha hS.iw
  have hr1 : ∀ x, erRd m1 x = erRd m x := fun x => by
    unfold erRd; rw [hf1.arr _ (by simp) (by rw [tierA_EREC]; split <;> decide)]
  obtain ⟨hlen, hget⟩ := L.Arena.decRules_get hd
  -- the copied source fields read
  have hword : ∀ j < cnt.toNat, ∀ f ∈ copiedF, ∃ w,
      erecP m (o.toNat + Rule.size.toNat * j + f.toNat) = some w ∧ erRd m (rpos o j + f) = w ∧
      (rpos o j + f).toNat = o.toNat + Rule.size.toNat * j + f.toNat := by
    intro j hj f hf
    have hrj := hget j hj
    rw [List.getElem?_eq_getElem (by omega)] at hrj
    obtain ⟨hc0, hn0, hr0⟩ := decRule_fields hrj
    have hw : ∃ w, erecP m (o.toNat + Rule.size.toNat * j + f.toNat) = some w := by
      simp only [copiedF, List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl
      · obtain ⟨w, hw, -⟩ := hd?_some hc0; exact ⟨w, hw⟩
      · obtain ⟨w, hw, -⟩ := nat?_word hn0; exact ⟨w, hw⟩
      · obtain ⟨w, hw, -⟩ := hd?_some hr0; exact ⟨w, hw⟩
    obtain ⟨w, hw⟩ := hw
    have hlt := erecP_lt64 hw
    have hp : (rpos o j + f).toNat = o.toNat + Rule.size.toNat * j + f.toNat := by
      unfold rpos
      rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_ofNat']; omega
    exact ⟨w, hw, erRd_of _ _ (by rw [hp]; exact hw), hp⟩
  have hfr : ∀ j < cnt.toNat, ∀ f ∈ copiedF,
      ErApart run (Rule.size.toNat * cnt.toNat) (rpos o j + f) := by
    intro j hj f hf t ht
    obtain ⟨w, hw, -, he⟩ := hword j hj f hf
    exact erFresh ha hS.iw (x := rpos o j + f) (by rw [he]; exact hw) (by rw [hk]; exact ht)
  have hm' := rrW_mem k lo ll po pl n m1 m' run o cnt r h hfr
  subst hm'
  rw [refireImg_congr (m := m) (m' := m1) k lo ll po pl o cnt.toNat (fun _ _ _ _ => hr1 _)]
  obtain ⟨hS1, hg1, -, -, -, -, hget1⟩ := erRecO_stage ha hS (refireImg m k lo ll po pl o cnt.toNat)
    (by rw [refireImg_length, hk])
  refine ⟨hS1, hg1, ?_⟩
  generalize hM : wrERo m1 run (refireImg m k lo ll po pl o cnt.toNat) = M at hS1 hg1 hget1 ⊢
  have hext := IWGrow.ext hg1
  unfold decRules
  rw [← hlen, ← List.length_map (f := fun rl => { rl with fire := f })]
  apply mapM_range_some
  intro j hj
  simp only [List.length_map] at hj
  rw [hlen] at hj
  have hrj := hget j hj
  rw [List.getElem?_eq_getElem (by omega)] at hrj
  simp only [List.getElem_map]
  -- record `j`'s fields, as the image holds them
  have g : ∀ (i : Nat) (x : Word), i < Rule.size.toNat →
      (refireImg1 m (rpos o j) k lo ll po pl)[i]? = some (some x) →
      erecP M (run.toNat + Rule.size.toNat * j + i) = some x := fun i x hi hx => by
    rw [Nat.add_assoc]
    exact hget1 _ _ (by rw [refireImg_get m k lo ll po pl o cnt.toNat j i hj hi]; exact hx)
  have gw : ∀ f ∈ copiedF, ∀ x, (refireImg1 m (rpos o j) k lo ll po pl)[f.toNat]? = some (some x) →
      x = erRd m (rpos o j + f) →
      erecP M (run.toNat + Rule.size.toNat * j + f.toNat) = erecP m (o.toNat + Rule.size.toNat * j + f.toNat) := by
    intro f hf x hx hxe
    obtain ⟨w, hw, hrd, -⟩ := hword j hj f hf
    rw [hw, g _ _ (copiedF_lt f hf) hx, hxe, hrd]
  have i0 := Rule.img_ctor (erRd m (rpos o j)) (erRd m (rpos o j + Rule.nfields)) k lo ll po pl
    (erRd m (rpos o j + Rule.rhs))
  refine decRule_refireAt hrj
    (gw Rule.ctor (by simp [copiedF]) _ i0 (by rw [add_ruleCtor]))
    (gw Rule.nfields (by simp [copiedF]) _ (Rule.img_nf ..) rfl)
    (gw Rule.rhs (by simp [copiedF]) _ (Rule.img_rhs ..) rfl)
    (g _ _ Rule.fire_lt (Rule.img_fk ..)) (g _ _ Rule.lvlsOff_lt (Rule.img_lo ..))
    (g _ _ Rule.lvlsLen_lt (Rule.img_ll ..)) (g _ _ Rule.pinsOff_lt (Rule.img_po ..))
    (g _ _ Rule.pinsLen_lt (Rule.img_pl ..)) (hf.ext hext)

end L.Ind

end
