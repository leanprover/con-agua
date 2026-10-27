import ConAgua.Rom.CIReadRefCV
import ConAgua.Arena.LevelInternRef

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

theorem rdU_some {rom : List UInt8} {p : Prog} (hL : RomCIProg rom p) {n : Nat} {m : Mem} {i : Word}
    {k : Word → Mem → Option (List Word × Mem)} {v : List Word × Mem} (h : rdU p n m i k = some v) :
    k (u64W rom i) m = some v := by
  change ntBW (callW p n "rom_u64" [i] m) (fun r m' => k (r.headD 0) m') = some v at h
  cases hc : callW p n "rom_u64" [i] m with
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

/-- The words `ws` written to `EREC`, in order. -/
def setERs (m : Mem) : List (Word × Word) → Mem
  | [] => m
  | (j, w) :: t => setERs (m.set64 EREC j w) t

theorem setERs_facts {m₀ : Mem} {a₀ a : AState} {T : Nat} {seen : List ConLeche.Expr} {memo : EMemo} :
    ∀ (ws : List (Word × Word)) (m : Mem), RInv m₀ a₀ T m a → MemoR m seen memo →
      (∀ jw ∈ ws, erTop m₀ ≤ jw.1.toNat) →
      RInv m₀ a₀ T (setERs m ws) a ∧ MemoR (setERs m ws) seen memo ∧ stkTop (setERs m ws) = stkTop m ∧
        erTop (setERs m ws) = erTop m ∧ (setERs m ws).arr64 IW = m.arr64 IW ∧
        (setERs m ws).arr64 CTL = m.arr64 CTL ∧
        ((setERs m ws).arr64 EREC).size = (m.arr64 EREC).size
  | [], m, hI, hM, _ => ⟨hI, hM, rfl, rfl, rfl, rfl, rfl⟩
  | (j, w) :: t, m, hI, hM, hj => by
    obtain ⟨hI1, hM1, hs1, ht1, hw1⟩ := setER_facts hI hM j w (hj (j, w) (by simp))
    obtain ⟨hI2, hM2, hs2, ht2, hw2, hc2, hz2⟩ :=
      setERs_facts t _ hI1 hM1 (fun jw h => hj jw (by simp [h]))
    refine ⟨hI2, hM2, hs2.trans hs1, ht2.trans ht1, hw2.trans hw1, ?_, ?_⟩
    · simp only [setERs]; rw [hc2]; exact Mem.arr64_set64_ne _ _ _ _ _ (by decide)
    · simp only [setERs]; rw [hz2]; exact size_set64 _ _ _ _ _

theorem setERs_ne : ∀ (ws : List (Word × Word)) (m : Mem) (i : Nat), (∀ jw ∈ ws, i ≠ jw.1.toNat) →
    (erA (setERs m ws))[i]? = (erA m)[i]?
  | [], _, _, _ => rfl
  | (j, w) :: t, m, i, h => by
    simp only [setERs]
    rw [setERs_ne t _ i (fun jw hj => h jw (by simp [hj])), er_set_ne _ _ _ _ (h (j, w) (by simp))]

theorem setERs_get : ∀ (ws : List (Word × Word)) (m : Mem) (j w : Word),
    (ws.map (·.1.toNat)).Nodup → (j, w) ∈ ws → j.toNat < (m.arr64 EREC).size →
    (erA (setERs m ws))[j.toNat]? = some w
  | [], _, _, _, _, h, _ => by simp at h
  | (j', w') :: t, m, j, w, hnd, hmem, hj => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    simp only [setERs]
    rcases List.mem_cons.mp hmem with e | e
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
      rw [setERs_ne t _ _ (fun jw hjw e' => hnd.1 ⟨jw, hjw, e'.symm⟩)]
      exact er_set_get m j w hj
    · exact setERs_get t _ j w hnd.2 e (by rw [size_set64]; exact hj)

/-! ## `sortZ` names the store already holds -/

/-- The names of a `sortZ`. -/
def pwNames : ConLeche.PropWhen → List ConLeche.Name
  | .never => []
  | .ifAllZero ns => ns

/-- **What re-interning the names `zs` needs**: none, or a well-formed state naming them through
`dn` (`NamesDn`). -/
def ZOK (dn : NIdx → Option ConLeche.Name) (zs : List ConLeche.Name) (a : AState) : Prop :=
  zs = [] ∨ (ConRon.Bridge.StateOK a ∧ NamesDn dn a zs)

theorem ZOK.step {dn : NIdx → Option ConLeche.Name} {zs : List ConLeche.Name} {a a' : AState}
    (h : ZOK dn zs a) (hs : ConRon.Bridge.StateOK a → ConRon.Bridge.Frontend.IStepS a a') :
    ZOK dn zs a' := by
  rcases h with h | ⟨hok, hn⟩
  · exact .inl h
  · have st := hs hok
    exact .inr ⟨st.ok, hn.ext st.ext⟩

/-- **Re-interning stored names is a no-op**, and `dn` reads their handles back. -/
theorem internNameList_dn (dn : NIdx → Option ConLeche.Name) :
    ∀ (zs : List ConLeche.Name) (a : AState), ZOK dn zs a →
      ∃ ks : List NIdx, (Frontend.internNameList zs).run a = .ok (ks, a) ∧ ks.mapM dn = some zs
  | [], a, _ => ⟨[], rfl, rfl⟩
  | x :: zs, a, h => by
    rcases h with h | ⟨hok, hn⟩
    · cases h
    have hwf : NStoreWF a.store.lss.ls.ns := by
      obtain ⟨rk, w⟩ := hok.wf
      obtain ⟨rk', w'⟩ := w.lss.ls
      exact w'.ns
    obtain ⟨k, hk, hd⟩ := hn x (by simp)
    have h1 := internName_denote_run a hwf _ k x hd
    obtain ⟨ks, h2, hks⟩ := internNameList_dn dn zs a
      (.inr ⟨hok, hn.mono (fun y hy => by simp [hy])⟩)
    refine ⟨k :: ks, ?_, ?_⟩
    · simp only [Frontend.internNameList]
      rw [run_bind_of _ _ _ _ _ h1, run_bind_of _ _ _ _ _ h2]; rfl
    · simp [hk, hks]

/-! ## `decCaps` from its words -/

/-- A number word. -/
theorem nat?_of {a : Array Word} {i : Nat} {w : Word} (h : a[i]? = some w) : nat? a i = some w.toNat := by
  simp [nat?, h]

theorem bool?_of {a : Array Word} {i : Nat} {w : Word} (h : a[i]? = some w) : bool? a i = some (w != 0) := by
  simp [bool?, h]

theorem bw_ne (b : Bool) : (UInt64.ofNat (if b then 1 else 0) != 0) = b := by cases b <;> decide

/-- `sortZ` without names, as its words. -/
def szTag : ConLeche.PropWhen → Nat
  | .never => 0
  | .ifAllZero _ => 1

theorem holds_decCaps {dn : NIdx → Option ConLeche.Name} {m : Mem} {c : Nat} {SA SC SZ : Nat → Prop}
    (ic : IIndCaps) (ks : List NIdx) (we wct wep wef wul wup wrk wtag wnp : Word)
    (h0 : (erA m)[c]? = some we) (h1 : (erA m)[c + 1]? = some wct) (h2 : (erA m)[c + 2]? = some wep)
    (h3 : (erA m)[c + 3]? = some wef) (h4 : (erA m)[c + 4]? = some wul)
    (h5 : (erA m)[c + 5]? = some wup) (h6 : (erA m)[c + 6]? = some wrk)
    (h7 : (erA m)[c + 7]? = some wtag) (h12 : (erA m)[c + 12]? = some wnp)
    (hct : wct.toNat < 2 ^ 32)
    (he : ic.eta = (we != 0)) (hc : ic.etaCtor = decI wct) (hep : ic.etaParams = wep.toNat)
    (hef : ic.etaFields = wef.toNat) (hul : ic.unitlike = (wul != 0)) (hup : ic.unitParams = wup.toNat)
    (hrk : ic.ruleK = (wrk != 0)) (hnp : ic.nparams = wnp.toNat)
    (hsz : (wtag.toNat = 0 ∧ ic.sortZ = .never) ∨
      (wtag.toNat = 1 ∧ ic.sortZ = .ifAllZero (pwNames ic.sortZ) ∧ ks.mapM dn = some (pwNames ic.sortZ)))
    (hZ : wtag.toNat = 1 → Holds SZ (fun _ => False)
      (fun m => (hlist? (erA m) (c + 8) : Option (List NIdx))) m ks)
    (hA : Holds SA (fun _ => False) (fun m => (hlist? (erA m) (c + 10) : Option (List NIdx))) m ic.all)
    (hC : Holds SC (fun _ => False) (fun m => (hlist? (erA m) (c + 13) : Option (List NIdx))) m
      ic.ctors) :
    Holds (fun i => (c ≤ i ∧ i < c + 8) ∨ i = c + 12 ∨ SA i ∨ SC i ∨ (wtag.toNat = 1 ∧ SZ i))
      (fun _ => False) (fun m => decCaps (erA m) dn c) m ic := by
  intro m' hE hI
  have g : ∀ i, (c ≤ i ∧ i < c + 8) → (erA m')[i]? = (erA m)[i]? := fun i hi => hE i (.inl hi)
  have e0 := (g c (by omega)).trans h0
  have e1 := (g (c + 1) (by omega)).trans h1
  have e2 := (g (c + 2) (by omega)).trans h2
  have e3 := (g (c + 3) (by omega)).trans h3
  have e4 := (g (c + 4) (by omega)).trans h4
  have e5 := (g (c + 5) (by omega)).trans h5
  have e6 := (g (c + 6) (by omega)).trans h6
  have e7 := (g (c + 7) (by omega)).trans h7
  have e12 := (hE (c + 12) (.inr (.inl rfl))).trans h12
  have eA := hA m' (fun i hi => hE i (.inr (.inr (.inl hi)))) (fun _ h => h.elim)
  have eC := hC m' (fun i hi => hE i (.inr (.inr (.inr (.inl hi))))) (fun _ h => h.elim)
  have ePW : decPW (erA m') dn (c + 7) = some ic.sortZ := by
    rcases hsz with ⟨ht, hs⟩ | ⟨ht, hs, hks⟩
    · simp [decPW, nat?_of e7, ht, hs]
    · rw [hs]
      have eZ := hZ ht m' (fun i hi => hE i (.inr (.inr (.inr (.inr ⟨ht, hi⟩))))) (fun _ h => h.elim)
      have : c + 7 + 1 = c + 8 := by omega
      simp [decPW, nat?_of e7, ht, this, eZ, hks]
  have : ic = ⟨we != 0, decI wct, wep.toNat, wef.toNat, wul != 0, wup.toNat, wrk != 0, ic.sortZ,
      ic.all, wnp.toNat, ic.ctors⟩ := by
    cases ic; simp_all
  rw [this]
  simp [decCaps, bool?_of e0, hd?, e1, hct, nat?_of e2, nat?_of e3, bool?_of e4, nat?_of e5,
    bool?_of e6, ePW, eA, nat?_of e12, eC]

/-! ## `rci_caps` -/

/-- The capabilities fit their encoding. -/
def capsFits (c : ConLeche.IndCaps) : Bool :=
  nameFits c.etaCtor && c.all.all nameFits && c.ctors.all nameFits && decide (c.etaParams < 2 ^ 64) &&
    decide (c.etaFields < 2 ^ 64) && decide (c.unitParams < 2 ^ 64) && decide (c.nparams < 2 ^ 64) &&
    (pwNames c.sortZ).all nameFits

theorem encCaps_eq (c : ConLeche.IndCaps) (rest : List UInt8) :
    encCaps c ++ rest = bw c.eta ++ (u64B c.etaParams ++ (u64B c.etaFields ++ (bw c.unitlike ++
      (u64B c.unitParams ++ (bw c.ruleK ++ (u64B c.nparams ++ (u64B (szTag c.sortZ) ++
      (encName c.etaCtor ++ (encNameL c.all ++ (encNameL c.ctors ++ (encNameL (pwNames c.sortZ) ++
      rest))))))))))) := by
  cases h : c.sortZ <;> simp [encCaps, h, szTag, pwNames, List.append_assoc]

theorem encCaps_len (c : ConLeche.IndCaps) :
    (encCaps c).length = 64 + (encName c.etaCtor).length + (encNameL c.all).length +
      (encNameL c.ctors).length + (encNameL (pwNames c.sortZ)).length := by
  have h := congrArg List.length (encCaps_eq c [])
  simp only [List.append_nil, List.length_append, bw, u64B, List.length_cons, List.length_nil] at h
  omega

theorem ofNat_toNat_lt {n : Nat} (h : n < 2 ^ 64) : (UInt64.ofNat n).toNat = n := by
  rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt h

section caps
variable {rom : List UInt8} {p : Prog} (hL : RomCIProg rom p) (hr : RomOK rom)
include hL hr

set_option hygiene false in
/-- `omega` for `caps_rel`: first rewrite with the `(c + k).toNat = c.toNat + k` equalities, then clear
them. With all of them in context, `omega`'s equality elimination chains through them and builds a
justification (and proof term) exponential in their number: ~130 MB and ~0.5 s per call, > 15 GB for
the whole proof (romfix). -/
local macro "comega" : tactic => `(tactic| ((try simp only [hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc10, hc12,
    hc13, hq64] at *) <;> (try clear hc1) <;> (try clear hc2) <;> (try clear hc3) <;>
  (try clear hc4) <;> (try clear hc5) <;> (try clear hc6) <;> (try clear hc7) <;> (try clear hc8) <;>
  (try clear hc10) <;> (try clear hc12) <;> (try clear hc13) <;> (try clear hcN) <;> omega))

/-- **`rci_caps` refines `Frontend.internCaps`**, into the 15 words at `c`. -/
@[refines_part ConRon.Arena.Frontend.internCaps "sortZ names the store holds"]
theorem caps_rel {m₀ : Mem} {a₀ : AState} {T : Nat} (dn : NIdx → Option ConLeche.Name)
    (seen : List ConLeche.Expr) (memo : EMemo)
    (caps : ConLeche.IndCaps) (hfit : capsFits caps = true) (k : Nat) (m : Mem) (a : AState)
    (hz : ZOK dn (pwNames caps.sortZ) a)
    (q c : Word) (rest : List UInt8) (r : List Word) (m' : Mem) (hI : RInv m₀ a₀ T m a)
    (hM : MemoR m seen memo) (hst : stkTop m = 0) (hd : rom.drop q.toNat = encCaps caps ++ rest)
    (hc0 : erTop m₀ ≤ c.toNat) (hc15 : c.toNat + 15 ≤ erTop m)
    (hc : callW p (k + 1) "rci_caps" [q, c] m = some (r, m')) :
    ∃ (ic : IIndCaps) (a' : AState), (Frontend.internCaps caps).run a = .ok (ic, a') ∧
      RInv m₀ a₀ T m' a' ∧ MemoR m' seen memo ∧ stkTop m' = 0 ∧
      (r.headD 0).toNat = q.toNat + (encCaps caps).length ∧
      EKeep (fun i => c.toNat ≤ i ∧ i < c.toNat + 15) m m' ∧ erTop m ≤ erTop m' ∧
      m'.arr64 IW = m.arr64 IW ∧
      Holds (fun i => (c.toNat ≤ i ∧ i < c.toNat + 15) ∨ (erTop m ≤ i ∧ i < erTop m'))
        (fun _ => False) (fun m => decCaps (erA m) dn c.toNat) m' ic := by
  simp only [capsFits, Bool.and_eq_true, decide_eq_true_eq] at hfit
  obtain ⟨⟨⟨⟨⟨⟨⟨hfn, hfa⟩, hfc⟩, hep⟩, hef⟩, hup⟩, hnp⟩, hfz⟩ := hfit
  have hd' := hd.trans (encCaps_eq caps rest)
  simp only [bw] at hd'
  have hlt := hI.er_lt
  have hgo := hI.grow.2.1
  have hrom := hr; simp only [RomOK] at hrom
  have hlen := drop_len rom q.toNat (u64B (if caps.eta then 1 else 0)) _ hd' (by simp [u64B])
  simp only [u64B, List.length_cons, List.length_nil] at hlen
  have hw := callW_model (M := fun mq => capsW p k mq q c) (caps_specW rom p hL k · q c) hc
  unfold capsW at hw
  replace hw := rdU_some hL hw; replace hw := rdU_some hL hw; replace hw := rdU_some hL hw
  replace hw := rdU_some hL hw; replace hw := rdU_some hL hw; replace hw := rdU_some hL hw
  replace hw := rdU_some hL hw; replace hw := rdU_some hL hw
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
    u64B (if caps.unitlike then 1 else 0) ++ u64B caps.unitParams) (if caps.ruleK then 1 else 0) _ (by rw [hd']; repeat rw [List.append_assoc])
    (by simp [u64B]) (hb caps.ruleK)
  have e6 := u64_at hr q 48 (u64B (if caps.eta then 1 else 0) ++ u64B caps.etaParams ++ u64B caps.etaFields ++
    u64B (if caps.unitlike then 1 else 0) ++ u64B caps.unitParams ++ u64B (if caps.ruleK then 1 else 0)) caps.nparams _
    (by rw [hd']; repeat rw [List.append_assoc]) (by simp [u64B]) hnp
  have htag : szTag caps.sortZ < 2 ^ 64 := by cases caps.sortZ <;> simp [szTag]
  have e7 := u64_at hr q 56 (u64B (if caps.eta then 1 else 0) ++ u64B caps.etaParams ++ u64B caps.etaFields ++
    u64B (if caps.unitlike then 1 else 0) ++ u64B caps.unitParams ++ u64B (if caps.ruleK then 1 else 0) ++ u64B caps.nparams) (szTag caps.sortZ) _
    (by rw [hd']; repeat rw [List.append_assoc]) (by simp [u64B]) htag
  rw [e0, e1, e2, e3, e4, e5, e6, e7] at hw
  clear e0 e1 e2 e3 e4 e5 e6 e7
  generalize hv0 : UInt64.ofNat (if caps.eta then 1 else 0) = v0 at hw
  generalize hv3 : UInt64.ofNat (if caps.unitlike then 1 else 0) = v3 at hw
  generalize hv5 : UInt64.ofNat (if caps.ruleK then 1 else 0) = v5 at hw
  have hcN : ∀ i : Nat, i < 16 → (c + UInt64.ofNat i).toNat = c.toNat + i := fun i hi => by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat']; simp; omega
  have hW : List (Word × Word) := []
  change capsW.capsTailW p k (setERs m [(c, v0), (c + 2, UInt64.ofNat caps.etaParams),
    (c + 3, UInt64.ofNat caps.etaFields), (c + 4, v3), (c + 5, UInt64.ofNat caps.unitParams),
    (c + 6, v5), (c + 12, UInt64.ofNat caps.nparams), (c + 7, UInt64.ofNat (szTag caps.sortZ))])
    q c = some (r, m') at hw
  generalize hws : [(c, v0), (c + 2, UInt64.ofNat caps.etaParams),
    (c + 3, UInt64.ofNat caps.etaFields), (c + 4, v3), (c + 5, UInt64.ofNat caps.unitParams),
    (c + 6, v5), (c + 12, UInt64.ofNat caps.nparams), (c + 7, UInt64.ofNat (szTag caps.sortZ))] = ws
    at hw
  have hc1 : (c + 1).toNat = c.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hc2 : (c + 2).toNat = c.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  have hc3 : (c + 3).toNat = c.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
  have hc4 : (c + 4).toNat = c.toNat + 4 := by rw [UInt64.toNat_add]; simp; omega
  have hc5 : (c + 5).toNat = c.toNat + 5 := by rw [UInt64.toNat_add]; simp; omega
  have hc6 : (c + 6).toNat = c.toNat + 6 := by rw [UInt64.toNat_add]; simp; omega
  have hc7 : (c + 7).toNat = c.toNat + 7 := by rw [UInt64.toNat_add]; simp; omega
  have hc8 : (c + 8).toNat = c.toNat + 8 := by rw [UInt64.toNat_add]; simp; omega
  have hc10 : (c + 10).toNat = c.toNat + 10 := by rw [UInt64.toNat_add]; simp; omega
  have hc12 : (c + 12).toNat = c.toNat + 12 := by rw [UInt64.toNat_add]; simp; omega
  have hc13 : (c + 13).toNat = c.toNat + 13 := by rw [UInt64.toNat_add]; simp; omega
  obtain ⟨hI1, hM1, hs1, ht1, hIW1, -, hsz1⟩ := setERs_facts ws m hI hM (by
    intro jw hjw; rw [← hws] at hjw
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hjw
    rcases hjw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [hc2, hc3, hc4, hc5, hc6, hc7, hc12] <;> comega)
  have hsz : erTop m ≤ (m.arr64 EREC).size := hI.ok.2.1
  have hget : ∀ j w, (j, w) ∈ ws → (erA (setERs m ws))[j.toNat]? = some w := by
    intro j w hjw
    refine setERs_get ws m j w ?_ hjw ?_
    · rw [← hws]; simp [hc2, hc3, hc4, hc5, hc6, hc7, hc12]
    · rw [← hws] at hjw
      simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hjw
      rcases hjw with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
        first | comega | (simp only [hc2, hc3, hc4, hc5, hc6, hc7, hc12]; comega)
  -- the eta constructor
  unfold capsW.capsTailW at hw
  have hq64 : (q + 64).toNat = q.toNat + 64 := by rw [UInt64.toNat_add]; simp; comega
  obtain ⟨r1, m8, h1, hw⟩ := ntBW_inv hw
  have hdn : rom.drop (q + 64).toNat = encName caps.etaCtor ++ (encNameL caps.all ++
      (encNameL caps.ctors ++ (encNameL (pwNames caps.sortZ) ++ rest))) := by
    rw [hq64, ← List.drop_drop, hd']; simp [u64B]
  obtain ⟨a1, hrun1, hA1, hk1, hlt1, hq1, hf1, hmo1⟩ := nameCall hL hr _ hfn hI1.arena hI1.mode hdn h1
  clear hd hd'
  obtain ⟨hI8, hE8, hIW8, ht8, -⟩ := hI1.expr hA1 hmo1 (hf1.mono (fun b hb => by simp [ExprA, RomA, hb])
    (fun x hx => by simp [ExprC, RomC, hx])) hk1
  have hM8 := hM1.frameG hf1 (by decide) (by decide)
  have hs8 : stkTop m8 = stkTop (setERs m ws) := hf1.2.1 131 (by decide)
  obtain ⟨hI9, hM9, hs9, ht9, hIW9⟩ := setER_facts hI8 hM8 (c + 1) (r1.headD 0) (by comega)
  -- the three name lists
  cases k with
  | zero => rw [callW_zero] at hw; simp at hw
  | succ k =>
  obtain ⟨r2, m10, h2, hw⟩ := ntBW_inv hw
  have hd2 : rom.drop (r1.tail.headD 0).toNat = encNameL caps.all ++ (encNameL caps.ctors ++
      (encNameL (pwNames caps.sortZ) ++ rest)) := drop_shift rom _ (encName caps.etaCtor) _ _ (by rw [hdn, List.append_assoc]) _ hq1
  obtain ⟨wsA, a2, hrun2, hltA, hI10, hM10, hs10, hq2, hek10, ht10, hIW10, hH10⟩ :=
    nameSl_rel hL hr seen memo caps.all hfa k _ a1 _ (c + 10) _ _ m10 hI9 hM9 hd2
      (by comega) (by comega) h2
  obtain ⟨r3, m11, h3, hw⟩ := ntBW_inv hw
  have hd3 : rom.drop (r2.headD 0).toNat = encNameL caps.ctors ++ (encNameL (pwNames caps.sortZ) ++ rest) :=
    drop_shift rom _ (encNameL caps.all) _ _ (by rw [hd2, List.append_assoc]) _ hq2
  obtain ⟨wsC, a3, hrun3, hltC, hI11, hM11, hs11, hq3, hek11, ht11, hIW11, hH11⟩ :=
    nameSl_rel hL hr seen memo caps.ctors hfc k _ a2 _ (c + 13) _ _ m11 hI10 hM10 hd3
      (by comega) (by comega) h3
  obtain ⟨r4, m12, h4, hw⟩ := ntBW_inv hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  have hd4 : rom.drop (r3.headD 0).toNat = encNameL (pwNames caps.sortZ) ++ rest :=
    drop_shift rom _ (encNameL caps.ctors) _ _ (by rw [hd3, List.append_assoc]) _ hq3
  obtain ⟨wsZ, a4, hrun4, -, hI12, hM12, hs12, hq4, hek12, ht12, hIW12, hH12⟩ :=
    nameSl_rel hL hr seen memo (pwNames caps.sortZ) hfz k _ a3 _ (c + 8) _ _ m12 hI11 hM11 hd4
      (by comega) (by comega) h4
  -- the `sortZ` names: re-interned at no cost
  have hz3 : ZOK dn (pwNames caps.sortZ) a3 :=
    ((hz.step fun hok => (ConRon.Bridge.Frontend.internName_sstep hok hrun1).1).step fun hok =>
      (ConRon.Bridge.Frontend.internNameList_sstep _ hok hrun2).1).step fun hok =>
      (ConRon.Bridge.Frontend.internNameList_sstep _ hok hrun3).1
  obtain ⟨ks, hks, hdk⟩ := internNameList_dn dn _ a3 hz3
  have hz4 : (wsZ.map decI : List NIdx) = ks ∧ a4 = a3 := by
    rw [hks] at hrun4
    simp only [Except.ok.injEq, Prod.mk.injEq] at hrun4
    exact ⟨hrun4.1.symm, hrun4.2.symm⟩
  obtain ⟨hzw, rfl⟩ := hz4
  -- the facts
  have hE8' : ∀ i : Nat, (erA m8)[i]? = (erA (setERs m ws))[i]? := fun i => by unfold erA; rw [hE8]
  have hk12 : ∀ i, i < erTop m → ¬ (c.toNat + 8 ≤ i ∧ i < c.toNat + 12) →
      ¬ (c.toNat + 13 ≤ i ∧ i < c.toNat + 15) →
      (erA m12)[i]? = (erA (m8.set64 EREC (c + 1) (r1.headD 0)))[i]? := by
    intro i hi hn hn'
    rw [hek12.2 i (by comega) (by comega), hek11.2 i (by comega) (by comega),
      hek10.2 i (by comega) (by comega)]
  have hword : ∀ (j w : Word) (i : Nat), (j, w) ∈ ws → j.toNat = c.toNat + i → i < 15 → i ≠ 1 →
      ¬ (8 ≤ i ∧ i < 12) → i < 13 → (erA m12)[c.toNat + i]? = some w := by
    intro j w i hjw hj h15 h1' h8 h13
    rw [hk12 _ (by comega) (by comega) (by comega), er_set_ne _ _ _ _ (by rw [hc1]; comega), hE8', ← hj]
    exact hget j w hjw
  have hW0 := hword c v0 0 (by rw [← hws]; simp) (by simp) (by decide) (by decide) (by decide) (by decide)
  have hW2 := hword (c + 2) (UInt64.ofNat caps.etaParams) 2 (by rw [← hws]; simp) hc2 (by decide) (by decide) (by decide) (by decide)
  have hW3 := hword (c + 3) (UInt64.ofNat caps.etaFields) 3 (by rw [← hws]; simp) hc3 (by decide) (by decide) (by decide) (by decide)
  have hW4 := hword (c + 4) v3 4 (by rw [← hws]; simp) hc4 (by decide) (by decide) (by decide) (by decide)
  have hW5 := hword (c + 5) (UInt64.ofNat caps.unitParams) 5 (by rw [← hws]; simp) hc5 (by decide) (by decide) (by decide) (by decide)
  have hW6 := hword (c + 6) v5 6 (by rw [← hws]; simp) hc6 (by decide) (by decide) (by decide) (by decide)
  have hW7 := hword (c + 7) (UInt64.ofNat (szTag caps.sortZ)) 7 (by rw [← hws]; simp) hc7 (by decide) (by decide) (by decide) (by decide)
  have hW12 := hword (c + 12) (UInt64.ofNat caps.nparams) 12 (by rw [← hws]; simp) hc12 (by decide) (by decide) (by decide) (by decide)
  simp only [Nat.add_zero] at hW0
  have hsz9 : erTop m ≤ (m8.arr64 EREC).size := by rw [hE8, hsz1]; exact hsz
  have hW1 : (erA m12)[c.toNat + 1]? = some (r1.headD 0) := by
    rw [hk12 _ (by comega) (by comega) (by comega), ← hc1]
    exact er_set_get m8 _ _ (by rw [hc1]; comega)
  rw [hc8] at hH12; rw [hc10] at hH10; rw [hc13] at hH11
  rw [hzw] at hH12
  have hA' := (hH10.ekeep hek11 (fun i hi => ⟨by comega, by comega⟩) hIW11).ekeep hek12
    (fun i hi => ⟨by comega, by comega⟩) hIW12
  have hC' := hH11.ekeep hek12 (fun i hi => ⟨by comega, by comega⟩) hIW12
  refine ⟨⟨caps.eta, decI (r1.headD 0), caps.etaParams, caps.etaFields, caps.unitlike, caps.unitParams,
    caps.ruleK, caps.sortZ, wsA.map decI, caps.nparams, wsC.map decI⟩, a4, ?_, hI12, hM12,
    by rw [hs12, hs11, hs10, hs9, hs8, hs1, hst], ?_, ⟨by comega, fun i hi hR => ?_⟩, by comega,
    by rw [hIW12, hIW11, hIW10, hIW9, hIW8, hIW1], ?_⟩
  · simp only [Frontend.internCaps]
    rw [run_bind_of _ _ _ _ _ hrun1, run_bind_of _ _ _ _ _ hrun2, run_bind_of _ _ _ _ _ hrun3]
    rfl
  · simp only [List.headD_cons]; rw [hq4, hq3, hq2, hq1, hq64, encCaps_len caps]; simp [encNameL, u64B]
    comega
  · rw [hk12 _ (by comega) (by comega) (by comega), er_set_ne _ _ _ _ (by rw [hc1]; comega), hE8',
      setERs_ne ws m i (by
        intro jw hjw; rw [← hws] at hjw
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hjw
        rcases hjw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [hc2, hc3, hc4, hc5, hc6, hc7, hc12] <;> comega)]
  · have hH := holds_decCaps (dn := dn) (c := c.toNat)
      ⟨caps.eta, decI (r1.headD 0), caps.etaParams, caps.etaFields, caps.unitlike, caps.unitParams,
        caps.ruleK, caps.sortZ, wsA.map decI, caps.nparams, wsC.map decI⟩ ks
      v0 (r1.headD 0) _ _ v3 _ v5 _ _ hW0 hW1 hW2 hW3 hW4 hW5 hW6 hW7 hW12 hlt1
      (by rw [← hv0]; exact (bw_ne _).symm) rfl (ofNat_toNat_lt hep).symm (ofNat_toNat_lt hef).symm
      (by rw [← hv3]; exact (bw_ne _).symm) (ofNat_toNat_lt hup).symm
      (by rw [← hv5]; exact (bw_ne _).symm) (ofNat_toNat_lt hnp).symm
      (by rw [ofNat_toNat_lt htag]; revert hdk; cases caps.sortZ <;> simp [szTag, pwNames])
      (fun _ => hH12) hA' hC'
    refine hH.mono (fun i hi => ?_) (fun _ h => h)
    rcases hi with hi | hi | hi | hi | ⟨-, hi⟩
    · left; comega
    · left; comega
    · rcases hi with hi | hi
      · left; comega
      · right; comega
    · rcases hi with hi | hi
      · left; comega
      · right; comega
    · rcases hi with hi | hi
      · left; comega
      · right; comega

end caps

end L.Rom
