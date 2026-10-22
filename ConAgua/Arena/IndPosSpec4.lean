import ConAgua.Arena.IndPosSpec3

/-! # `replaceFVars` and its maps, continued (lane `indproofs2`, helper `pos`): the frame, the
`ds` loop, the walk, the entry. -/

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem decNK_fields {m : Mem} {k : Nat} {key : NestKey} (h : decNK m k = some key) :
    iwH m k = some key.cname ∧ iwH m (k + 1) = some key.lvls ∧ decAt m (decHL m) (k + 2) = some key.ds := by
  simp only [decNK, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨c, hc, l, hl, ds, hds, h'⟩ := h
  obtain rfl := Option.some.inj h'
  exact ⟨hc, hl, hds⟩

theorem decNH_fields {m : Mem} {w : Nat} {hl : NestHole} (h : decNH m w = some hl) :
    ∃ k, iwN m w = some k ∧ decNK m k = some hl.key := by
  simp only [decNH, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨k, hk, key, hkey, b, hb, h'⟩ := h
  obtain rfl := Option.some.inj h'
  exact ⟨k, hk, hkey⟩

theorem iwN_of_get {m : Mem} {i : Nat} {w : Word} (h : (m.arr64 IW)[i]? = some w) : iwN m i = some w.toNat := by
  simp [iwN, nat?, iwA, h]

theorem RxPost.of_fr {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} {vis : Word} {m m1 m2 : Mem}
    {a2 : AState} {M : Std.HashMap (EIdx × Word) EIdx} {G g : Word} (hR : RfInv m M G g)
    (hf : RfFr m m1) (hg : IWGrow m m1) (h : RxPost dn fe vis m1 m2 a2 M G g) : RxPost dn fe vis m m2 a2 M G g := by
  obtain ⟨M2, G2, hS2, hg2, hR2, hk2, hG2⟩ := h
  exact ⟨M2, G2, hS2, hg.trans hg2, hR2, hk2, hG2⟩

theorem RxPost.then {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} {vis : Word} {m m1 m2 : Mem}
    {a1 a2 : AState} {M : Std.HashMap (EIdx × Word) EIdx} {G g : Word} (h : RxPost dn fe vis m m1 a1 M G g)
    (hS : StageR dn vis fe m2 a2) (hg : IWGrow m1 m2) (hf : RfFr m1 m2) : RxPost dn fe vis m m2 a2 M G g := by
  obtain ⟨M1, G1, -, hg1, hR1, hk1, hG1⟩ := h
  exact ⟨M1, G1, hS, hg1.trans hg, hR1.frame hf, hk1, hG1⟩

section steps
variable (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)

/-- **A frame's hole read back, from its hole record on**. -/
theorem frameTail (n : Nat) (hDs : DsOK dn fe vis n) (mh m' : Mem) (a : AState) (ctx po pl n1 h : Word)
    (c : NestCtx) (prog : List NestHole) (H0 : NestHole) (r0 r1 : Word)
    (M : Std.HashMap (EIdx × Word) EIdx) (G g : Word)
    (hk : frK2 n (rdW (mh.arr64 IW) h) (posRecW mh [0, ctx, po, pl, n1]) = some (r0, r1, m'))
    (hS : StageR dn vis fe mh a) (hc : decCtx mh ctx.toNat = some c) (hin : CtxIn mh ctx.toNat (· < iwTop mh))
    (hs : HSl mh po.toNat pl.toNat prog) (hb : c.nP + c.names.length + n1.toNat + 1 < 2 ^ 64)
    (hh : decNH mh h.toNat = some H0) (hhin : NHIn mh h.toNat (· < iwTop mh)) (hR : RfInv mh M G g) :
    ∃ x a', (do
        let ds ← H0.key.ds.mapM fun x => ConRon.Arena.replaceFVars (.holeImg c prog n1.toNat) x
        let hd ← internConstE H0.key.cname H0.key.lvls
        let r ← mkAppN hd ds
        pure (some r) : AM (Option EIdx)).run a = .ok (x, a') ∧ OptE r0 r1 x ∧
      RxPost dn fe vis mh m' a' M G g := by
  have htop : iwTop mh < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  obtain ⟨k, hk0, hkey⟩ := decNH_fields hh
  have hrk : (rdW (mh.arr64 IW) h).toNat = k := rdIW0 hk0
  have hNK := hhin.2.2 k hk0
  cases hrec : posRecW mh [0, ctx, po, pl, n1] with
  | none => rw [hrec] at hk; simp [frK2] at hk
  | some pr =>
  obtain ⟨f, m2⟩ := pr
  rw [hrec, frK2_some] at hk
  obtain ⟨hS2, hg2, hf2, ht2, hget2⟩ := posRecW_stage hrec hS (by simp)
  simp only [List.length_cons, List.length_nil] at ht2
  have hR2 := hR.frame (posRecW_fr hrec)
  -- the new map record
  have g0 := iwN_of_get (by simpa using hget2 0 (by simp))
  have g1 := iwN_of_get (by simpa using hget2 1 (by simp))
  have g2 := iwN_of_get (by simpa using hget2 2 (by simp))
  have g3 := iwN_of_get (by simpa using hget2 3 (by simp))
  have g4 := iwN_of_get (by simpa using hget2 4 (by simp))
  obtain ⟨ec, hci2⟩ := hin.grow hg2
  have hfm : FMOk m2 f.toNat (.holeImg c prog n1.toNat) :=
    ⟨by simpa using g0, by omega, ⟨ctx.toNat, g1, by rw [ec]; exact hc, hci2⟩,
      ⟨po.toNat, pl.toNat, g2, g3, hs.grow hg2⟩, g4, by omega⟩
  -- the key, in `m2`
  obtain ⟨ekey, hNK2⟩ := hNK.agree (RdS.of_grow hg2)
  rw [hkey] at ekey
  obtain ⟨hcn, hlv, hds⟩ := decNK_fields ekey
  obtain ⟨o, l, ho, hl, hdsl⟩ := decAt_some hds
  have htop2 : iwTop m2 < 2 ^ 64 := Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1
  have hkb : k + 4 ≤ iwTop m2 := by have := hNK2.1 3 (by omega); have := hg2.1; omega
  have ro := rdIW (m := m2) (f := rdW (mh.arr64 IW) h) (i := 2) (by rw [hrk]; exact ho) (by omega) (by decide)
  have rl := rdIW (m := m2) (f := rdW (mh.arr64 IW) h) (i := 3) (by rw [hrk]; simpa using hl) (by omega) (by decide)
  simp only [show UInt64.ofNat 2 = (2 : Word) from rfl, show UInt64.ofNat 3 = (3 : Word) from rfl] at ro rl
  have hsl : ∀ j < l, o + j < iwTop m2 := fun j hj =>
    Nat.lt_of_lt_of_le (hNK2.2 o l ho (by simpa using hl) j hj) hg2.1
  cases hdsr : rxDsW n m2 f (rdW (m2.arr64 IW) (rdW (mh.arr64 IW) h + 2)) (rdW (m2.arr64 IW) (rdW (mh.arr64 IW) h + 3)) with
  | none => rw [hdsr] at hk; simp [frK3] at hk
  | some pr3 =>
  obtain ⟨q, l3, m3⟩ := pr3
  rw [hdsr, frK3_some] at hk
  obtain ⟨ys, a3, hrun3, hdec3, hq3, hpost3⟩ := hDs m2 m3 a f _ _ q l3 _ H0.key.ds M G g hdsr hS2 hfm
    (by rw [ro, rl]; exact hdsl) (by rw [ro, rl]; exact hsl) hR2
  obtain ⟨M3, G3, hS3, hg3, hR3, hk3, hG3⟩ := hpost3
  have htop3 : iwTop m3 < 2 ^ 64 := Nat.lt_of_le_of_lt hS3.2.1 hS3.2.2.2.1
  have := hg3.1
  -- the container's head, in `m3`
  have hg23 := hg3
  obtain ⟨hcnH, hcnd⟩ := rd_iwH (m := m3) (p := rdW (mh.arr64 IW) h) (i := 0)
    (by rw [hrk]; simp only [UInt64.toNat_zero, Nat.add_zero]; rw [iwH_agree (RdS.of_grow hg3) (by omega)]; exact hcn)
    (by simp; omega)
  obtain ⟨hlvH, hlvd⟩ := rd_iwH (m := m3) (p := rdW (mh.arr64 IW) h) (i := 1)
    (by rw [hrk]; rw [iwH_agree (RdS.of_grow hg3) (by simp; omega)]; simpa using hlv) (by simp; omega)
  simp only [UInt64.add_zero, show UInt64.ofNat 1 = (1 : Word) from rfl] at hcnH hcnd hlvH hlvd
  cases hci : ceinternW m3 (rdW (m3.arr64 IW) (rdW (mh.arr64 IW) h)) (rdW (m3.arr64 IW) (rdW (mh.arr64 IW) h + 1)) with
  | none => rw [hci] at hk; simp [frK4] at hk
  | some pr4 =>
  obtain ⟨hd, m4⟩ := pr4
  rw [hci] at hk
  by_cases hdb : 4294967296 ≤ hd
  · rw [frK4_big (hb := hdb)] at hk; simp at hk
  rw [frK4_ok (hb := hdb)] at hk
  obtain ⟨a4, hr4, hS4, hg4⟩ := internConst_stage hS3 _ _ hcnH hlvH hci
  have hiw4 : m4.arr64 IW = m3.arr64 IW := lowFr_iw (ceinternW_low hci)
  cases hst : stubM "mk_app_n" m4 [hd, q, l3] with
  | none => rw [hst] at hk; simp [frK5] at hk
  | some pr5 =>
  obtain ⟨rr, m5⟩ := pr5
  rw [hst, frK5_some] at hk
  simp only [Option.some.injEq, Prod.mk.injEq] at hk
  obtain ⟨rfl, rfl, rfl⟩ := hk
  obtain ⟨x, a5, hr5, hS5, hg5, hx1, hx2⟩ := mkAppN_spec dn vis fe hd q l3 (lt_of_notbig hdb) ys m4 m5 a4 rr hst
    ⟨hS4, by simp only [decHL, iwA, hiw4]; exact hdec3⟩
  refine ⟨some x, a5, ?_, ⟨by simp, by rw [← hx2]; rfl⟩, ?_⟩
  · simp only [StateT.run_bind]
    rw [hrun3]
    simp only [except_ok_bind, ConRon.Arena.internConstE, StateT.run_bind]
    rw [← hcnd, ← hlvd, hr4]
    simp only [except_ok_bind, StateT.run_bind]
    rw [show (decE hd : EIdx) = decI hd from rfl, hr5]
    rfl
  · exact ⟨M3, G3, hS5, ((hg2.trans hg3).trans hg4).trans hg5,
      (hR3.frame (RfFr.of_low (ceinternW_low hci))).frame (RfFr.stub (by decide) hst), hk3, hG3⟩

end steps

end L.Ind
