module

import ConAgua.L.WordOff
import ConAgua.Rom.CIReadRefNames
public import ConAgua.Rom.CIReadRefBase
public import ConAgua.Rom.CIReadRefW
import ConAgua.Rom.ReadScr
import ConAgua.Arena.DeclNatCv

@[expose] public section

/-!
# The ROM constant readers: an inductive's capabilities (helper `decls4-rom`)

`rci_caps(q, c)` refines `Frontend.internCaps` into the 15 words at `c` (`decCaps`). The twin keeps
the `sortZ` names as values and interns none; the reader interns them (`rci_name_sl`) and `decPW`
reads them back through `dn`. Both agree when every such name already has a handle that `dn` and
the store decode to it (`NamesDn`) in a well-formed store (`ZOK`): re-interning finds the handle
and changes nothing (`internNameList_dn`, by `internName_denote_run`). Every pinned constant but
`Quot` (whose `sortZ` is `.ifAllZero [u]`) has no `sortZ` names, and `ZOK` holds trivially.
-/


open ConRon.Arena ConRon.Arena.Frontend
open Std.WP
open scoped Lean.Order

namespace L.Rom

open L.Arena L.Ind

/-! ## Reading numbers -/

/-- A `rom_u64` call in a model's `ntBW` chain: the continuation at the word read. -/
theorem u64_some {rom : List UInt8} {p : Prog} (hL : RomCIProg rom p) {n : Nat} {m : Mem} {i : Word}
    {k : List Word → Mem → Option (List Word × Mem)} {v : List Word × Mem}
    (h : ntBW (callW p n "rom_u64_c" [i] m) k = some v) : k [u64W rom i] m = some v := by
  cases hc : callW p n "rom_u64_c" [i] m with
  | none => rw [hc] at h; simp at h
  | some t =>
    obtain ⟨r, m'⟩ := t
    rw [hc, bW_some] at h
    obtain ⟨rfl, rfl⟩ := u64Call hL hc
    exact h

theorem u64_at {rom : List UInt8} (hr : RomOK rom) (q k : Word) (pre : List UInt8) (n : Nat)
    (rest : List UInt8) (hd : rom.drop q.toNat = pre ++ (u64B n ++ rest)) (hk : k.toNat = pre.length)
    (hn : n < 2 ^ 64) : u64W rom (q + k) = UInt64.ofNat n := by
  have hl := drop_len rom _ (pre ++ u64B n) rest (by rw [hd, List.append_assoc]) (by simp [u64B])
  simp only [List.length_append, u64B, List.length_cons, List.length_nil] at hl
  have hr' := hr; simp only [RomOK] at hr'
  have hq : (q + k).toNat = q.toNat + pre.length := by rw [UInt64.toNat_add, hk]; omega
  refine u64W_of_drop rom _ n rest ?_ hn hr
  rw [hq, ← List.drop_drop, hd, List.drop_left]

/-! ## Several `EREC` words written -/

/-- The words `ws` written with `erec_put`, in order. -/
def putERs (m : Mem) : List (Word × Word) → Mem
  | [] => m
  | (j, w) :: t => putERs (erecPutMem m j w) t

theorem putE_some {rom : List UInt8} {p : Prog} (hL : RomCIProg rom p) {n : Nat} {m : Mem} {i v : Word}
    {k : Mem → Option (List Word × Mem)} {x : List Word × Mem} (h : putE p n m i v k = some x) :
    k (erecPutMem m i v) = some x := by
  change ntBW (callW p n "erec_put" [i, v] m) (fun _ m' => k m') = some x at h
  cases hc : callW p n "erec_put" [i, v] m with
  | none => rw [hc] at h; simp at h
  | some t =>
    obtain ⟨r, m'⟩ := t
    rw [hc, bW_some] at h
    rw [← putCall hL hc]; exact h

theorem putERs_ne : ∀ (ws : List (Word × Word)) (m : Mem) (i : Nat), (∀ jw ∈ ws, i ≠ jw.1.toNat) →
    i < 2 ^ 41 → (∀ jw ∈ ws, jw.1.toNat < 2 ^ 41) → erA (putERs m ws) i = erA m i
  | [], _, _, _, _, _ => rfl
  | (j, w) :: t, m, i, h, h41, hj => by
    simp only [putERs]
    rw [putERs_ne t _ i (fun jw hjw => h jw (by simp [hjw])) h41 (fun jw hjw => hj jw (by simp [hjw])),
      er_put_ne _ _ _ _ (h (j, w) (by simp)) h41 (hj (j, w) (by simp))]

theorem putERs_facts {m₀ : Mem} {a₀ a : AState} {T : Nat} {seen : List ConLeche.Expr} {memo : EMemo} :
    ∀ (ws : List (Word × Word)) (m : Mem), RInv m₀ a₀ T m a → MemoR m seen memo →
      (∀ jw ∈ ws, erT m₀ ≤ jw.1.toNat ∧ jw.1.toNat < erT m) →
      RInv m₀ a₀ T (putERs m ws) a ∧ MemoR (putERs m ws) seen memo ∧ stkTop (putERs m ws) = stkTop m ∧
        erT (putERs m ws) = erT m ∧ (putERs m ws).arr64 IW = m.arr64 IW
  | [], m, hI, hM, _ => ⟨hI, hM, rfl, rfl, rfl⟩
  | (j, w) :: t, m, hI, hM, hj => by
    obtain ⟨hI1, hM1, hs1, ht1, hw1, -, -⟩ := putER_facts hI hM j w (hj (j, w) (by simp)).1
      (hj (j, w) (by simp)).2
    obtain ⟨hI2, hM2, hs2, ht2, hw2⟩ :=
      putERs_facts t _ hI1 hM1 (fun jw h => ⟨(hj jw (by simp [h])).1, by rw [ht1]; exact (hj jw (by simp [h])).2⟩)
    exact ⟨hI2, hM2, hs2.trans hs1, ht2.trans ht1, hw2.trans hw1⟩

theorem putERs_get {m₀ : Mem} {a₀ a : AState} {T : Nat} :
    ∀ (ws : List (Word × Word)) (m : Mem) (j w : Word), RInv m₀ a₀ T m a →
      (∀ jw ∈ ws, erT m₀ ≤ jw.1.toNat ∧ jw.1.toNat < erT m) →
      (ws.map (·.1.toNat)).Nodup → (j, w) ∈ ws → erA (putERs m ws) j.toNat = some w
  | [], _, _, _, _, _, _, h => by simp at h
  | (j', w') :: t, m, j, w, hI, hj, hnd, hmem => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    obtain ⟨hI1, hg1, -, ht1, -, -⟩ := hI.putER j' w' (hj (j', w') (by simp)).1 (hj (j', w') (by simp)).2
    have hj' : ∀ jw ∈ t, erT m₀ ≤ jw.1.toNat ∧ jw.1.toNat < erT (erecPutMem m j' w') :=
      fun jw h => ⟨(hj jw (by simp [h])).1, by rw [ht1]; exact (hj jw (by simp [h])).2⟩
    have hlt := hI.er_lt
    simp only [putERs]
    rcases List.mem_cons.mp hmem with e | e
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
      rw [putERs_ne t _ _ (fun jw hjw e' => hnd.1 ⟨jw, hjw, e'.symm⟩) (by have := (hj (j, w) (by simp)).2; simp only at this; omega)
        (fun jw hjw => by have := (hj jw (by simp [hjw])).2; omega)]
      exact hg1
    · exact putERs_get t _ j w hI1 hj' hnd.2 e

/-! ## `decCaps` from its words -/

theorem nat?_of {a : Nat → Option Word} {i : Nat} {w : Word} (h : a i = some w) : nat? a i = some w.toNat := by
  simp [nat?, h]

theorem bool?_of {a : Nat → Option Word} {i : Nat} {w : Word} (h : a i = some w) : bool? a i = some (w != 0) := by
  simp [bool?, h]

theorem bw_ne (b : Bool) : (UInt64.ofNat (if b then 1 else 0) != 0) = b := by cases b <;> decide

theorem holds_decCaps {m : Mem} {c : Nat} {SA SC : Nat → Prop}
    (ic : IIndCaps) (we wct wep wef wul wup wix wnp : Word)
    (h0 : erA m c = some we) (h1 : erA m (c + 1) = some wct) (h2 : erA m (c + 2) = some wep)
    (h3 : erA m (c + 3) = some wef) (h4 : erA m (c + 4) = some wul)
    (h5 : erA m (c + 5) = some wup) (h6 : erA m (c + 6) = some wix) (h12 : erA m (c + 12) = some wnp)
    (hct : wct.toNat < 2 ^ 32)
    (he : ic.eta = (we != 0)) (hc : ic.etaCtor = decI wct) (hep : ic.etaParams = wep.toNat)
    (hef : ic.etaFields = wef.toNat) (hul : ic.unitlike = (wul != 0)) (hup : ic.unitParams = wup.toNat)
    (hix : ic.nIdx = wix.toNat) (hnp : ic.nparams = wnp.toNat)
    (hA : Holds SA (fun _ => False) (fun m => (hlist? (erA m) (c + 10) : Option (List NIdx))) m ic.all)
    (hC : Holds SC (fun _ => False) (fun m => (hlist? (erA m) (c + 13) : Option (List NIdx))) m
      ic.ctors) :
    Holds (fun i => (c ≤ i ∧ i < c + 7) ∨ i = c + 12 ∨ SA i ∨ SC i)
      (fun _ => False) (fun m => decCaps (erA m) c) m ic := by
  intro m' hE hI
  have g : ∀ i, (c ≤ i ∧ i < c + 7) → erA m' i = erA m i := fun i hi => hE i (.inl hi)
  have e0 := (g c (by omega)).trans h0
  have e1 := (g (c + 1) (by omega)).trans h1
  have e2 := (g (c + 2) (by omega)).trans h2
  have e3 := (g (c + 3) (by omega)).trans h3
  have e4 := (g (c + 4) (by omega)).trans h4
  have e5 := (g (c + 5) (by omega)).trans h5
  have e6 := (g (c + 6) (by omega)).trans h6
  have e12 := (hE (c + 12) (.inr (.inl rfl))).trans h12
  have eA := hA m' (fun i hi => hE i (.inr (.inr (.inl hi)))) (fun _ h => h.elim)
  have eC := hC m' (fun i hi => hE i (.inr (.inr (.inr hi)))) (fun _ h => h.elim)
  have : ic = ⟨we != 0, decI wct, wep.toNat, wef.toNat, wul != 0, wup.toNat, ic.all, wnp.toNat,
      wix.toNat, ic.ctors⟩ := by
    cases ic; simp_all
  rw [this]
  simp [decCaps, bool?_of e0, hd?, e1, hct, nat?_of e2, nat?_of e3, bool?_of e4, nat?_of e5,
    nat?_of e6, eA, nat?_of e12, eC]

/-! ## `rci_caps` -/

/-- The capabilities fit their encoding. -/
def capsFits (c : ConLeche.IndCaps) : Bool :=
  nameFits c.etaCtor && c.all.all nameFits && c.ctors.all nameFits && decide (c.etaParams < 2 ^ 64) &&
    decide (c.etaFields < 2 ^ 64) && decide (c.unitParams < 2 ^ 64) && decide (c.nparams < 2 ^ 64) &&
    decide (c.nIdx < 2 ^ 64)

theorem encCaps_eq (c : ConLeche.IndCaps) (rest : List UInt8) :
    encCaps c ++ rest = bw c.eta ++ (u64B c.etaParams ++ (u64B c.etaFields ++ (bw c.unitlike ++
      (u64B c.unitParams ++ (u64B c.nIdx ++ (u64B c.nparams ++
      (encName c.etaCtor ++ (encNameL c.all ++ (encNameL c.ctors ++ rest))))))))) := by
  simp [encCaps, List.append_assoc]

theorem encCaps_len (c : ConLeche.IndCaps) :
    (encCaps c).length = 56 + (encName c.etaCtor).length + (encNameL c.all).length +
      (encNameL c.ctors).length := by
  have h := congrArg List.length (encCaps_eq c [])
  simp only [List.append_nil, List.length_append, bw, u64B, List.length_cons, List.length_nil] at h
  omega

section caps
variable {rom : List UInt8} {p : Prog} (hL : RomCIProg rom p) (hr : RomOK rom)
include hL hr

/-- **`rci_caps` refines `Frontend.internCaps`**, into the 15 words at `c`. -/
@[refines_part ConRon.Arena.Frontend.internCaps "capabilities that fit the ROM encoding"]
theorem caps_rel {m₀ : Mem} {a₀ : AState} {T : Nat}
    (seen : List ConLeche.Expr) (memo : EMemo)
    (caps : ConLeche.IndCaps) (hfit : capsFits caps = true) (k : Nat) (m : Mem) (a : AState)
    (q c : Word) (rest : List UInt8) (r : List Word) (m' : Mem) (hI : RInv m₀ a₀ T m a)
    (hM : MemoR m seen memo) (hst : stkTop m = 0) (hd : rom.drop q.toNat = encCaps caps ++ rest)
    (hc0 : erT m₀ ≤ c.toNat) (hc15 : c.toNat + 15 ≤ erT m)
    (hc : callW p (k + 1) "rci_caps" [q, c] m = some (r, m')) :
    ∃ (ic : IIndCaps) (a' : AState), (Frontend.internCaps caps).run a = .ok (ic, a') ∧
      RInv m₀ a₀ T m' a' ∧ MemoR m' seen memo ∧ stkTop m' = 0 ∧
      (r.headD 0).toNat = q.toNat + (encCaps caps).length ∧
      EKeep (fun i => c.toNat ≤ i ∧ i < c.toNat + 15) m m' ∧ erT m ≤ erT m' ∧
      m'.arr64 IW = m.arr64 IW ∧
      Holds (fun i => (c.toNat ≤ i ∧ i < c.toNat + 15) ∨ (erT m ≤ i ∧ i < erT m'))
        (fun _ => False) (fun m => decCaps (erA m) c.toNat) m' ic := by
  simp only [capsFits, Bool.and_eq_true, decide_eq_true_eq] at hfit
  obtain ⟨⟨⟨⟨⟨⟨⟨hfn, hfa⟩, hfc⟩, hep⟩, hef⟩, hup⟩, hnp⟩, hix⟩ := hfit
  have hd' := hd.trans (encCaps_eq caps rest)
  simp only [bw] at hd'
  have hlt := hI.er_lt
  have hgo := hI.erT_mono
  have hrom := hr; simp only [RomOK] at hrom
  have hlen := drop_len rom q.toNat (u64B (if caps.eta then 1 else 0)) _ hd' (by simp [u64B])
  simp only [u64B, List.length_cons, List.length_nil] at hlen
  have hw := callW_model (M := fun mq => capsW p k mq q c) (caps_specW rom p hL k · q c) hc
  unfold capsW at hw
  replace hw := putE_some hL (u64_some hL hw); replace hw := putE_some hL (u64_some hL hw)
  replace hw := putE_some hL (u64_some hL hw); replace hw := putE_some hL (u64_some hL hw)
  replace hw := putE_some hL (u64_some hL hw); replace hw := putE_some hL (u64_some hL hw)
  replace hw := putE_some hL (u64_some hL hw)
  have hb : ∀ b : Bool, (if b then 1 else 0) < 2 ^ 64 := fun b => by cases b <;> decide
  have e0 := u64_at hr q 0 [] _ _ (by rw [hd']; rfl) (by simp) (hb caps.eta)
  simp only [UInt64.add_zero] at e0
  have e1 := u64_at hr q 8 (u64B (if caps.eta then 1 else 0)) caps.etaParams _ (by rw [hd']) (by simp [u64B]) hep
  have e2 := u64_at hr q 16 (u64B (if caps.eta then 1 else 0) ++ u64B caps.etaParams) caps.etaFields _
    (by rw [hd', List.append_assoc]) (by simp [u64B]) hef
  have e3 := u64_at hr q 24 (u64B (if caps.eta then 1 else 0) ++ u64B caps.etaParams ++ u64B caps.etaFields) (if caps.unitlike then 1 else 0) _
    (by rw [hd']; repeat rw [List.append_assoc]) (by simp [u64B]) (hb caps.unitlike)
  have e4 := u64_at hr q 32 (u64B (if caps.eta then 1 else 0) ++ u64B caps.etaParams ++ u64B caps.etaFields ++
    u64B (if caps.unitlike then 1 else 0)) caps.unitParams _ (by rw [hd']; repeat rw [List.append_assoc])
    (by simp [u64B]) hup
  have e5 := u64_at hr q 40 (u64B (if caps.eta then 1 else 0) ++ u64B caps.etaParams ++ u64B caps.etaFields ++
    u64B (if caps.unitlike then 1 else 0) ++ u64B caps.unitParams) caps.nIdx _ (by rw [hd']; repeat rw [List.append_assoc])
    (by simp [u64B]) hix
  have e6 := u64_at hr q 48 (u64B (if caps.eta then 1 else 0) ++ u64B caps.etaParams ++ u64B caps.etaFields ++
    u64B (if caps.unitlike then 1 else 0) ++ u64B caps.unitParams ++ u64B caps.nIdx) caps.nparams _
    (by rw [hd']; repeat rw [List.append_assoc]) (by simp [u64B]) hnp
  rw [e0, e1, e2, e3, e4, e5, e6] at hw
  clear e0 e1 e2 e3 e4 e5 e6
  generalize hv0 : UInt64.ofNat (if caps.eta then 1 else 0) = v0 at hw
  generalize hv3 : UInt64.ofNat (if caps.unitlike then 1 else 0) = v3 at hw
  change ntBW (callW p k "rom_name_c" [q + 56] (putERs m [(c, v0), (c + 2, UInt64.ofNat caps.etaParams),
    (c + 3, UInt64.ofNat caps.etaFields), (c + 4, v3), (c + 5, UInt64.ofNat caps.unitParams),
    (c + 6, UInt64.ofNat caps.nIdx), (c + 12, UInt64.ofNat caps.nparams)])) _ = some (r, m') at hw
  generalize hws : [(c, v0), (c + 2, UInt64.ofNat caps.etaParams),
    (c + 3, UInt64.ofNat caps.etaFields), (c + 4, v3), (c + 5, UInt64.ofNat caps.unitParams),
    (c + 6, UInt64.ofNat caps.nIdx), (c + 12, UInt64.ofNat caps.nparams)] = ws
    at hw
  have hwsB : ∀ jw ∈ ws, erT m₀ ≤ jw.1.toNat ∧ jw.1.toNat < erT m := by
    intro jw hjw; rw [← hws] at hjw
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hjw
    rcases hjw with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> constructor <;> off_omega
  have hws41 : ∀ jw ∈ ws, jw.1.toNat < 2 ^ 41 := fun jw h => by have := (hwsB jw h).2; omega
  obtain ⟨hI1, hM1, hs1, ht1, hIW1⟩ := putERs_facts ws m hI hM hwsB
  have hget : ∀ j w, (j, w) ∈ ws → erA (putERs m ws) j.toNat = some w := by
    intro j w hjw
    refine putERs_get ws m j w hI hwsB ?_ hjw
    rw [← hws]; simp (disch := omega) only [off_toNat, List.map_cons, List.map_nil]; simp
  -- the eta constructor
  have hq56 : (q + 56).toNat = q.toNat + 56 := by rw [UInt64.toNat_add]; simp; off_omega
  obtain ⟨r1, m8, h1, hw⟩ := L.Ind.ntBW_some hw
  have hdn : rom.drop (q + 56).toNat = encName caps.etaCtor ++ (encNameL caps.all ++
      (encNameL caps.ctors ++ rest)) := by
    rw [hq56, ← List.drop_drop, hd']; simp [u64B]
  obtain ⟨a1, hrun1, hA1, hk1, hlt1, hq1, hf1, hmo1⟩ := nameCall hL hr _ hfn hI1.arena hI1.mode hdn h1
  clear hd hd'
  obtain ⟨hI8, -, -, hIW8, ht8, -, hE8⟩ := hI1.expr hA1 hmo1 (hf1.mono (fun b hb => by simp [ExprA, RomA, hb])
    (fun x hx => by simp [ExprC, RomC, hx])) hk1 (L.Arena.internName_ks _ _ _ _ hrun1)
  have hM8 := hM1.frameG hf1 (by decide) (by decide)
  have hs8 : stkTop m8 = stkTop (putERs m ws) := hf1.ctl 131 (by decide)
  obtain ⟨rp, m9, hp, hw⟩ := L.Ind.ntBW_some hw
  rw [putCall hL hp] at hw
  obtain ⟨hI9, hM9, hs9, ht9, hIW9, hg9, hn9⟩ := putER_facts hI8 hM8 (c + 1) (r1.headD 0) (by off_omega)
    (by off_omega)
  -- the two name lists
  cases k with
  | zero => rw [callW_zero] at hw; simp at hw
  | succ k =>
  obtain ⟨r2, m10, h2, hw⟩ := L.Ind.ntBW_some hw
  have hd2 : rom.drop (r1.tail.headD 0).toNat = encNameL caps.all ++ (encNameL caps.ctors ++ rest) :=
    drop_shift rom _ (encName caps.etaCtor) _ _ (by rw [hdn, List.append_assoc]) _ hq1
  obtain ⟨wsA, a2, hrun2, hltA, hI10, hM10, hs10, hq2, hek10, ht10, hIW10, hH10⟩ :=
    nameSl_rel hL hr seen memo caps.all hfa k _ a1 _ (c + 10) _ _ m10 hI9 hM9 hd2
      (by off_omega) (by off_omega) h2
  obtain ⟨r3, m11, h3, hw⟩ := L.Ind.ntBW_some hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  have hd3 : rom.drop (r2.headD 0).toNat = encNameL caps.ctors ++ rest :=
    drop_shift rom _ (encNameL caps.all) _ _ (by rw [hd2, List.append_assoc]) _ hq2
  obtain ⟨wsC, a3, hrun3, hltC, hI11, hM11, hs11, hq3, hek11, ht11, hIW11, hH11⟩ :=
    nameSl_rel hL hr seen memo caps.ctors hfc k _ a2 _ (c + 13) _ _ m11 hI10 hM10 hd3
      (by off_omega) (by off_omega) h3
  -- the facts
  have hk11 : ∀ i, i < erT m → ¬ (c.toNat + 10 ≤ i ∧ i < c.toNat + 12) →
      ¬ (c.toNat + 13 ≤ i ∧ i < c.toNat + 15) →
      erA m11 i = erA (erecPutMem m8 (c + 1) (r1.headD 0)) i := by
    intro i hi hn hn'
    rw [hek11.2 i (by off_omega) (by off_omega), hek10.2 i (by off_omega) (by off_omega)]
  have hword : ∀ (j w : Word) (i : Nat), (j, w) ∈ ws → j.toNat = c.toNat + i → i < 13 → i ≠ 1 →
      ¬ (10 ≤ i ∧ i < 12) → erA m11 (c.toNat + i) = some w := by
    intro j w i hjw hj h13 h1' h8
    rw [hk11 _ (by off_omega) (by off_omega) (by off_omega), hn9 _ (by off_omega) (by off_omega), hE8, ← hj]
    exact hget j w hjw
  have hW0 := hword c v0 0 (by rw [← hws]; simp) (by simp) (by decide) (by decide) (by decide)
  have hW2 := hword (c + 2) (UInt64.ofNat caps.etaParams) 2 (by rw [← hws]; simp) (off_toNat (by omega)) (by decide) (by decide) (by decide)
  have hW3 := hword (c + 3) (UInt64.ofNat caps.etaFields) 3 (by rw [← hws]; simp) (off_toNat (by omega)) (by decide) (by decide) (by decide)
  have hW4 := hword (c + 4) v3 4 (by rw [← hws]; simp) (off_toNat (by omega)) (by decide) (by decide) (by decide)
  have hW5 := hword (c + 5) (UInt64.ofNat caps.unitParams) 5 (by rw [← hws]; simp) (off_toNat (by omega)) (by decide) (by decide) (by decide)
  have hW6 := hword (c + 6) (UInt64.ofNat caps.nIdx) 6 (by rw [← hws]; simp) (off_toNat (by omega)) (by decide) (by decide) (by decide)
  have hW12 := hword (c + 12) (UInt64.ofNat caps.nparams) 12 (by rw [← hws]; simp) (off_toNat (by omega)) (by decide) (by decide) (by decide)
  simp only [Nat.add_zero] at hW0
  have hW1 : erA m11 (c.toNat + 1) = some (r1.headD 0) := by
    rw [hk11 _ (by off_omega) (by off_omega) (by off_omega), ← off_toNat (by omega)]
    exact hg9
  simp (disch := omega) only [off_toNat] at hH10 hH11
  have hA' := hH10.ekeep hek11 (fun i hi => ⟨by off_omega, by off_omega⟩) hIW11
  refine ⟨⟨caps.eta, decI (r1.headD 0), caps.etaParams, caps.etaFields, caps.unitlike, caps.unitParams,
    wsA.map decI, caps.nparams, caps.nIdx, wsC.map decI⟩, a3, ?_, hI11, hM11,
    by rw [hs11, hs10, hs9, hs8, hs1, hst], ?_, ⟨by off_omega, fun i hi hR => ?_⟩, by off_omega,
    by rw [hIW11, hIW10, hIW9, hIW8, hIW1], ?_⟩
  · simp only [Frontend.internCaps]
    rw [run_bind_of _ _ _ _ _ hrun1, run_bind_of _ _ _ _ _ hrun2, run_bind_of _ _ _ _ _ hrun3]
    rfl
  · simp only [List.headD_cons]; rw [hq3, hq2, hq1, hq56, encCaps_len caps]; simp [encNameL, u64B]
    off_omega
  · rw [hk11 _ (by off_omega) (by off_omega) (by off_omega), hn9 _ (by off_omega) (by off_omega), hE8,
      putERs_ne ws m i (by
        intro jw hjw; rw [← hws] at hjw
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hjw
        rcases hjw with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> off_omega) (by omega) hws41]
  · have hH := holds_decCaps (c := c.toNat)
      ⟨caps.eta, decI (r1.headD 0), caps.etaParams, caps.etaFields, caps.unitlike, caps.unitParams,
        wsA.map decI, caps.nparams, caps.nIdx, wsC.map decI⟩
      v0 (r1.headD 0) _ _ v3 _ _ _ hW0 hW1 hW2 hW3 hW4 hW5 hW6 hW12 hlt1
      (by rw [← hv0]; exact (bw_ne _).symm) rfl (L.toNat_ofNat_of_lt hep).symm (L.toNat_ofNat_of_lt hef).symm
      (by rw [← hv3]; exact (bw_ne _).symm) (L.toNat_ofNat_of_lt hup).symm
      (L.toNat_ofNat_of_lt hix).symm (L.toNat_ofNat_of_lt hnp).symm hA' hH11
    refine hH.mono (fun i hi => ?_) (fun _ h => h)
    rcases hi with hi | hi | hi | hi
    · left; off_omega
    · left; off_omega
    · rcases hi with hi | hi
      · left; off_omega
      · right; off_omega
    · rcases hi with hi | hi
      · left; off_omega
      · right; off_omega

end caps

end L.Rom
