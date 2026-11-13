module

import ConAgua.Arena.RecLayout.CapsDec
import ConAgua.L.WordOff
import ConAgua.Rom.CIReadRefNames
public import ConAgua.Rom.CIReadRefBase
public import ConAgua.Rom.CIReadRefW
import ConAgua.Arena.DeclNatCv

@[expose] public section

/-!
# The ROM constant readers: an inductive's capabilities (helper `decls4-rom`)

`rci_caps(q, c)` refines `Frontend.internCaps` into the record at `c` (`decCaps`). The twin keeps
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
    (ic : IIndCaps) (we wix wnz wnp : Word)
    (h0 : erA m (c + Caps.eta.toNat) = some we) (h6 : erA m (c + Caps.nIdx.toNat) = some wix)
    (h7 : erA m (c + Caps.neverZero.toNat) = some wnz)
    (h12 : erA m (c + Caps.nparams.toNat) = some wnp)
    (he : ic.eta = (we != 0)) (hix : ic.nIdx = wix.toNat) (hnz : ic.neverZero = (wnz != 0))
    (hnp : ic.nparams = wnp.toNat)
    (hA : Holds SA (fun _ => False) (fun m => (hlist? (erA m) (c + Caps.allOff.toNat) : Option (List NIdx))) m
      ic.all)
    (hC : Holds SC (fun _ => False) (fun m => (hlist? (erA m) (c + Caps.ctorsOff.toNat) : Option (List NIdx))) m
      ic.ctors) :
    Holds (fun i => i = c + Caps.eta.toNat ∨ i = c + Caps.nIdx.toNat ∨ i = c + Caps.neverZero.toNat ∨
        i = c + Caps.nparams.toNat ∨ SA i ∨ SC i)
      (fun _ => False) (fun m => decCaps (erA m) c) m ic := by
  intro m' hE hI
  have e0 := (hE _ (.inl rfl)).trans h0
  have e6 := (hE _ (.inr (.inl rfl))).trans h6
  have e7 := (hE _ (.inr (.inr (.inl rfl)))).trans h7
  have e12 := (hE _ (.inr (.inr (.inr (.inl rfl))))).trans h12
  have eA := hA m' (fun i hi => hE i (.inr (.inr (.inr (.inr (.inl hi)))))) (fun _ h => h.elim)
  have eC := hC m' (fun i hi => hE i (.inr (.inr (.inr (.inr (.inr hi)))))) (fun _ h => h.elim)
  exact decCaps_of (by rw [bool?_of e0, he]) (by rw [nat?_of e6, hix]) eA (by rw [nat?_of e12, hnp]) eC
    (by rw [bool?_of e7, hnz])

/-! ## `rci_caps` -/

/-- The capabilities fit their encoding. -/
def capsFits (c : ConLeche.IndCaps) : Bool :=
  c.all.all nameFits && c.ctors.all nameFits && decide (c.nparams < 2 ^ 64) && decide (c.nIdx < 2 ^ 64)

theorem encCaps_eq (c : ConLeche.IndCaps) (rest : List UInt8) :
    encCaps c ++ rest = bw c.eta ++ (u64B c.nIdx ++ (u64B c.nparams ++
      (encNameL c.all ++ (encNameL c.ctors ++ (bw c.neverZero ++ rest))))) := by
  simp [encCaps, List.append_assoc]

theorem encCaps_len (c : ConLeche.IndCaps) :
    (encCaps c).length = 32 + (encNameL c.all).length + (encNameL c.ctors).length := by
  have h := congrArg List.length (encCaps_eq c [])
  simp only [List.append_nil, List.length_append, bw, u64B, List.length_cons, List.length_nil] at h
  omega

section caps
variable {rom : List UInt8} {p : Prog} (hL : RomCIProg rom p) (hr : RomOK rom)
include hL hr

/-- **`rci_caps` refines `Frontend.internCaps`**, into the record at `c`. -/
@[refines_part ConRon.Arena.Frontend.internCaps "capabilities that fit the ROM encoding"]
theorem caps_rel {m₀ : Mem} {a₀ : AState} {T : Nat}
    (seen : List ConLeche.Expr) (memo : EMemo)
    (caps : ConLeche.IndCaps) (hfit : capsFits caps = true) (k : Nat) (m : Mem) (a : AState)
    (q c : Word) (rest : List UInt8) (r : List Word) (m' : Mem) (hI : RInv m₀ a₀ T m a)
    (hM : MemoR m seen memo) (hst : stkTop m = 0) (hd : rom.drop q.toNat = encCaps caps ++ rest)
    (hc0 : erT m₀ ≤ c.toNat) (hc15 : c.toNat + Caps.size.toNat ≤ erT m)
    (hc : callW p (k + 1) "rci_caps" [q, c] m = some (r, m')) :
    ∃ (ic : IIndCaps) (a' : AState), (Frontend.internCaps caps).run a = .ok (ic, a') ∧
      RInv m₀ a₀ T m' a' ∧ MemoR m' seen memo ∧ stkTop m' = 0 ∧
      (r.headD 0).toNat = q.toNat + (encCaps caps).length ∧
      EKeep (fun i => c.toNat ≤ i ∧ i < c.toNat + Caps.size.toNat) m m' ∧ erT m ≤ erT m' ∧
      m'.arr64 IW = m.arr64 IW ∧
      Holds (fun i => (c.toNat ≤ i ∧ i < c.toNat + Caps.size.toNat) ∨ (erT m ≤ i ∧ i < erT m'))
        (fun _ => False) (fun m => decCaps (erA m) c.toNat) m' ic := by
  simp only [capsFits, Bool.and_eq_true, decide_eq_true_eq] at hfit
  obtain ⟨⟨⟨hfa, hfc⟩, hnp⟩, hix⟩ := hfit
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
  replace hw := putE_some hL (u64_some hL hw)
  have hb : ∀ b : Bool, (if b then 1 else 0) < 2 ^ 64 := fun b => by cases b <;> decide
  have e0 := u64_at hr q 0 [] _ _ (by rw [hd']; rfl) (by simp) (hb caps.eta)
  simp only [UInt64.add_zero] at e0
  have e1 := u64_at hr q 8 (u64B (if caps.eta then 1 else 0)) caps.nIdx _ (by rw [hd']) (by simp [u64B]) hix
  have e2 := u64_at hr q 16 (u64B (if caps.eta then 1 else 0) ++ u64B caps.nIdx) caps.nparams _
    (by rw [hd', List.append_assoc]) (by simp [u64B]) hnp
  rw [e0, e1, e2] at hw
  clear e0 e1 e2
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8⟩ := Caps.order
  have hoff : ∀ f : Word, f.toNat < Caps.size.toNat → (c + f).toNat = c.toNat + f.toNat :=
    fun f hf => by rw [UInt64.toNat_add]; omega
  have fE := hoff _ Caps.eta_lt; have fI := hoff _ Caps.nIdx_lt
  have fZ := hoff _ Caps.neverZero_lt; have fA := hoff _ Caps.allOff_lt
  have fP := hoff _ Caps.nparams_lt; have fC := hoff _ Caps.ctorsOff_lt
  generalize hv0 : UInt64.ofNat (if caps.eta then 1 else 0) = v0 at hw
  change ntBW (callW p k "rci_name_sl" [q + 24, c + Caps.allOff] (putERs m [(c + Caps.eta, v0),
    (c + Caps.nIdx, UInt64.ofNat caps.nIdx), (c + Caps.nparams, UInt64.ofNat caps.nparams)])) _ =
    some (r, m') at hw
  generalize hws : [(c + Caps.eta, v0), (c + Caps.nIdx, UInt64.ofNat caps.nIdx),
    (c + Caps.nparams, UInt64.ofNat caps.nparams)] = ws at hw
  have hwsB : ∀ jw ∈ ws, erT m₀ ≤ jw.1.toNat ∧ jw.1.toNat < erT m := by
    intro jw hjw; rw [← hws] at hjw
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hjw
    rcases hjw with rfl | rfl | rfl <;> simp only [fE, fI, fP] <;> omega
  have hws41 : ∀ jw ∈ ws, jw.1.toNat < 2 ^ 41 := fun jw h => by have := (hwsB jw h).2; omega
  obtain ⟨hI1, hM1, hs1, ht1, hIW1⟩ := putERs_facts ws m hI hM hwsB
  have hget : ∀ j w, (j, w) ∈ ws → erA (putERs m ws) j.toNat = some w := by
    intro j w hjw
    refine putERs_get ws m j w hI hwsB ?_ hjw
    rw [← hws]; simp only [List.map_cons, List.map_nil, fE, fI, fP]; simp; omega
  have hq24 : (q + 24).toNat = q.toNat + 24 := by rw [UInt64.toNat_add]; simp; off_omega
  clear hd
  -- the two name lists
  cases k with
  | zero => rw [callW_zero] at hw; simp at hw
  | succ k =>
  obtain ⟨r2, m10, h2, hw⟩ := L.Ind.ntBW_some hw
  have hd2 : rom.drop (q + 24).toNat = encNameL caps.all ++ (encNameL caps.ctors ++ (bw caps.neverZero ++ rest)) := by
    rw [hq24, ← List.drop_drop, hd']; simp [u64B, bw]
  obtain ⟨wsA, a2, hrun2, hltA, hI10, hM10, hs10, hq2, hek10, ht10, hIW10, hH10⟩ :=
    nameSl_rel hL hr seen memo caps.all hfa k _ a _ (c + Caps.allOff) _ _ m10 hI1 hM1 hd2
      (by rw [fA]; omega) (by rw [fA]; omega) h2
  obtain ⟨r3, m11, h3, hw⟩ := L.Ind.ntBW_some hw
  have hd3 : rom.drop (r2.headD 0).toNat = encNameL caps.ctors ++ (bw caps.neverZero ++ rest) :=
    drop_shift rom _ (encNameL caps.all) _ _ (by rw [hd2, List.append_assoc]) _ hq2
  obtain ⟨wsC, a3, hrun3, hltC, hI11, hM11, hs11, hq3, hek11, ht11, hIW11, hH11⟩ :=
    nameSl_rel hL hr seen memo caps.ctors hfc k _ a2 _ (c + Caps.ctorsOff) _ _ m11 hI10 hM10 hd3
      (by rw [fC]; omega) (by rw [fC]; omega) h3
  -- `neverZero`
  replace hw := putE_some hL (u64_some hL hw)
  have hd4 : rom.drop (r3.headD 0).toNat = bw caps.neverZero ++ rest :=
    drop_shift rom _ (encNameL caps.ctors) _ _ (by rw [hd3, List.append_assoc]) _ hq3
  have e7 := u64_at hr (r3.headD 0) 0 [] _ rest (by rw [hd4]; rfl) (by simp) (hb caps.neverZero)
  simp only [UInt64.add_zero] at e7
  rw [e7] at hw
  simp only [Option.some.injEq, Prod.mk.injEq, List.headD_cons] at hw
  obtain ⟨rfl, rfl⟩ := hw
  have hc7lt : (c + Caps.neverZero).toNat < erT m11 := by rw [fZ]; omega
  have hc7ge : erT m₀ ≤ (c + Caps.neverZero).toNat := by rw [fZ]; omega
  obtain ⟨hI12, hM12, hs12, ht12, hIW12, hget7, hne7⟩ :=
    putER_facts hI11 hM11 (c + Caps.neverZero) (UInt64.ofNat (if caps.neverZero then 1 else 0)) hc7ge hc7lt
  generalize hm12 : erecPutMem m11 (c + Caps.neverZero) (UInt64.ofNat (if caps.neverZero then 1 else 0)) = m12 at *
  have hek12 : EKeep (fun i => i = (c + Caps.neverZero).toNat) m11 m12 :=
    ⟨by omega, fun i hi hn => hne7 i hn (by have := hI11.er_lt; omega)⟩
  rw [fA] at hek10 hH10; rw [fC] at hek11 hH11; rw [fZ] at hek12 hget7 hne7
  -- the facts
  have hk11 : ∀ i, i < erT m → ¬ (c.toNat + Caps.allOff.toNat ≤ i ∧ i < c.toNat + Caps.allOff.toNat + 2) →
      ¬ (c.toNat + Caps.ctorsOff.toNat ≤ i ∧ i < c.toNat + Caps.ctorsOff.toNat + 2) →
      erA m11 i = erA (putERs m ws) i := by
    intro i hi hn hn'
    rw [hek11.2 i (by omega) hn', hek10.2 i (by omega) hn]
  have hword : ∀ (j w : Word) (f : Word), (j, w) ∈ ws → j = c + f → f.toNat < Caps.size.toNat →
      ¬ (Caps.allOff.toNat ≤ f.toNat ∧ f.toNat < Caps.allOff.toNat + 2) →
      ¬ (Caps.ctorsOff.toNat ≤ f.toNat ∧ f.toNat < Caps.ctorsOff.toNat + 2) →
      erA m11 (c.toNat + f.toNat) = some w := by
    intro j w f hjw hj hf h1 h2
    rw [hk11 _ (by omega) (by omega) (by omega), ← hoff f hf, ← hj]
    exact hget j w hjw
  have hW0' := hword _ v0 Caps.eta (by rw [← hws]; simp) rfl Caps.eta_lt (by omega) (by omega)
  have hW6' := hword _ (UInt64.ofNat caps.nIdx) Caps.nIdx (by rw [← hws]; simp) rfl Caps.nIdx_lt
    (by omega) (by omega)
  have hW12' := hword _ (UInt64.ofNat caps.nparams) Caps.nparams (by rw [← hws]; simp) rfl
    Caps.nparams_lt (by omega) (by omega)
  have hW0 : erA m12 (c.toNat + Caps.eta.toNat) = some v0 := by
    rw [hne7 _ (by omega) (by omega)]; exact hW0'
  have hW6 : erA m12 (c.toNat + Caps.nIdx.toNat) = some (UInt64.ofNat caps.nIdx) := by
    rw [hne7 _ (by omega) (by omega)]; exact hW6'
  have hW12 : erA m12 (c.toNat + Caps.nparams.toNat) = some (UInt64.ofNat caps.nparams) := by
    rw [hne7 _ (by omega) (by omega)]; exact hW12'
  have hW7 : erA m12 (c.toNat + Caps.neverZero.toNat) =
      some (UInt64.ofNat (if caps.neverZero then 1 else 0)) := hget7
  have hA' := (hH10.ekeep hek11 (fun i hi => ⟨by omega, by omega⟩) hIW11).ekeep hek12
    (fun i hi => ⟨by omega, by omega⟩) hIW12
  have hC' := hH11.ekeep hek12 (fun i hi => ⟨by omega, by omega⟩) hIW12
  refine ⟨(⟨caps.eta, wsA.map decI, caps.nparams, caps.nIdx, wsC.map decI, caps.neverZero⟩ : IIndCaps), a3, ?_, hI12, hM12,
    by rw [hs12, hs11, hs10, hs1, hst], ?_, ⟨by omega, fun i hi hR => ?_⟩, by omega,
    by rw [hIW12, hIW11, hIW10, hIW1], ?_⟩
  · simp only [Frontend.internCaps]
    rw [run_bind_of _ _ _ _ _ hrun2, run_bind_of _ _ _ _ _ hrun3]
    rfl
  · have hl4 := drop_len rom (r3.headD 0).toNat (bw caps.neverZero) rest hd4 (by simp [bw, u64B])
    simp only [bw, u64B, List.length_cons, List.length_nil] at hl4
    have hrom' : rom.length < 2 ^ 63 := hr
    have h8 : (r3.headD 0 + 8).toNat = (r3.headD 0).toNat + 8 := by
      rw [UInt64.toNat_add, show (8 : Word).toNat = 8 from rfl, Nat.mod_eq_of_lt (show _ < 2 ^ 64 by omega)]
    simp only [List.headD_cons]; rw [h8, hq3, hq2, hq24, encCaps_len caps]
    omega
  · rw [hne7 _ (by omega) (by omega), hk11 _ (by omega) (by omega) (by omega),
      putERs_ne ws m i (by
        intro jw hjw; rw [← hws] at hjw
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hjw
        rcases hjw with rfl | rfl | rfl <;> simp only [fE, fI, fP] <;> omega) (by omega) hws41]
  · have hH := holds_decCaps (c := c.toNat)
      (⟨caps.eta, wsA.map decI, caps.nparams, caps.nIdx, wsC.map decI, caps.neverZero⟩ : IIndCaps)
      v0 _ _ _ hW0 hW6 hW7 hW12
      (by rw [← hv0]; exact (bw_ne _).symm)
      (L.toNat_ofNat_of_lt hix).symm (bw_ne _).symm (L.toNat_ofNat_of_lt hnp).symm hA' hC'
    refine hH.mono (fun i hi => ?_) (fun _ h => h)
    rcases hi with hi | hi | hi | hi | hi | hi
    · left; omega
    · left; omega
    · left; omega
    · left; omega
    · rcases hi with hi | hi
      · left; omega
      · right; omega
    · rcases hi with hi | hi
      · left; omega
      · right; omega

end caps

end L.Rom
