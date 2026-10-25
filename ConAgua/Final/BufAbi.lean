import ConAgua.Final.BufLayout

/-!
# `ca_check_b` on the machine (lane parmode)

`abiB_outcome`: the harness's thread calls `ca_check_b(buf, buf_len, j, region, region_len)`
(`BufCall`: the buffer holds the words `B`, the region holds an L memory `r` in the sense of
`RegionRel`); the stub writes the table (`sim_desc`, `sim_imm`: every table word `bufVal`, as
`qwrs`), the globals `plo := j`, `phi := j + 1`, `mode := 2`, and enters the trampoline; the
machine returns with the caller's registers and `rdx = 1` or the outcome of `check` from
`bufMemG … B r j` in `bufLayout`.
-/

namespace ConAgua.Final

open L L.Compiler L.Arena

set_option linter.unusedSimpArgs false

/-- The register-file simp set: writes as literals, reads as projections. -/
local macro "rsimp" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic| simp only [Reg64s.set64_rax,
  Reg64s.set64_rcx, Reg64s.set64_rdx, Reg64s.set64_rsi, Reg64s.set64_rdi, Reg64s.set64_rsp, Reg64s.set64_rbp,
  Reg64s.set64_r8, Reg64s.set64_r9, Reg64s.set64_r11, Reg64s.set64_r14, Reg64s.set64_r15, Reg64s.get64_rax,
  Reg64s.get64_rcx, Reg64s.get64_rdx, Reg64s.get64_rsi, Reg64s.get64_rdi, Reg64s.get64_rsp, Reg64s.get64_r8,
  Reg64s.get64_r9, Reg64s.get64_r11, Reg64s.get64_r14, Reg64s.get64_r15, Reg64s.get64_rbp, Reg64s.rax_mk,
  Reg64s.rcx_mk, Reg64s.rdx_mk, Reg64s.rsi_mk, Reg64s.rdi_mk, Reg64s.rsp_mk, Reg64s.rbp_mk, Reg64s.r8_mk,
  Reg64s.r9_mk, Reg64s.r10_mk, Reg64s.r11_mk, Reg64s.r12_mk, Reg64s.r13_mk, Reg64s.r14_mk, Reg64s.r15_mk,
  Reg64s.rbx_mk, UInt64.toNat_toBitVec, UInt64.ofBitVec_toBitVec, UInt64.toBitVec_ofBitVec] $[$loc]?)

theorem romVals_imm : ∀ (bs : List UInt8), ∀ v ∈ romVals bs, ∃ w, v = .imm w := by
  intro bs
  induction bs using romVals.induct with
  | case1 _ _ _ _ _ _ _ _ _ ih =>
    intro v hv; simp only [romVals, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact ⟨_, rfl⟩
    · exact ih v hv
  | case2 => intro v hv; simp [romVals] at hv
  | case3 bs h1 h2 =>
    intro v hv
    rw [romVals.eq_3 bs h1 h2] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    exact ⟨_, hv⟩

/-- `w · 8 + buf`, as the stub computes a frozen base. -/
theorem shl3_add (w : Word) (buf : Nat) :
    (w <<< (UInt64.ofNat 3)) + UInt64.ofNat buf = UInt64.ofNat (buf + 8 * w.toNat) := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_add, UInt64.toNat_shiftLeft, UInt64.toNat_ofNat', Nat.shiftLeft_eq, Nat.reduceMod,
    Nat.reducePow]
  omega

section
variable [Host] {tab : Tab} {fz own : List ArrId} {B : Array Word} {buf base blen : Nat}

/-- A table store: `[rcx + 8q] := r` with `r` holding table word `q`. -/
theorem ev_storeQ {Q : MachineState → Prop} {k : Nat} {s : MachineData} {r : Reg64} {off : Int}
    (hk : Host.prog[k]? = some (movMR (mb .rcx off) r)) (val : Nat → BitVec 64) (d0 : DataMem)
    (qs : List Nat) (q : Nat) (hoff : off = ((8 * q : Nat) : Int)) (hq : 8 * q + 8 ≤ 2 ^ 31)
    (hrcx : (s.regs.get64 .rcx).toNat = base)
    (hv : s.regs.get64 r = val q) (hmem : s.dmem = qwrs base val d0 qs)
    (hmap : (rdW s.dmem (A (base + 8 * q))).isSome)
    (h : Ev Q { s with dmem := qwrs base val d0 (qs ++ [q]) } (at_ (k + 1))) : Ev Q s (at_ k) := by
  subst hoff
  refine ev_movMR hk ⟨by omega, by omega⟩ (by rw [hrcx, Int.toNat_natCast]; exact hmap) ?_
  rw [qwrs_append, hrcx] at *
  simp only [Int.toNat_natCast, hv, ← hmem] at h ⊢
  exact h

/-- The memory facts the stub's stores keep: the buffer's words, and the table's cells mapped. -/
theorem qwrs_facts (hok : abiTabOk tab = true) (hg : BufGeom tab fz own B buf base blen)
    (val : Nat → BitVec 64) (d0 : DataMem)
    (hB0 : ∀ i (h : i < B.size), rdW d0 (A (buf + 8 * i)) = some B[i])
    (hmap0 : ∀ x, base ≤ x → x < base + blen → (d0.get? (A x)).isSome)
    (qs : List Nat) (hqs : ∀ q ∈ qs, q < bufN tab) :
    (∀ i (h : i < B.size), rdW (qwrs base val d0 qs) (A (buf + 8 * i)) = some B[i]) ∧
    (∀ q < bufN tab, (rdW (qwrs base val d0 qs) (A (base + 8 * q))).isSome) ∧
    (∀ x, base ≤ x → x < base + blen → ((qwrs base val d0 qs).get? (A x)).isSome) := by
  obtain ⟨hnb, htab, -⟩ := abiTabOk_spec hok
  have hn := hg.need
  have hf := hg.fits
  have hbe := hg.bend
  unfold workerNeed at hn
  have hN : 8 * bufN tab ≤ 2 ^ 31 := by simp only [bufN]; omega
  have hO := qwrs_only (T := base) (val := val) qs d0 (bufN tab) (by simp only [abiSlot] at hn; omega) hqs
  refine ⟨fun i h => ?_, fun q hq => ?_, fun x h1 h2 => qwrs_grows qs d0 _ (hmap0 x h1 h2)⟩
  · rw [hO.rdW_eq (by omega) (by
      rcases hg.apart (buf + 8 * i + 7) (by omega) (by omega) with h' | h'
      · left; omega
      · right; simp only [abiSlot] at hn; omega)]
    exact hB0 i h
  · exact isSome_rdW fun j hj => by
      rw [A_add]; exact qwrs_grows qs d0 _ (hmap0 _ (by omega) (by simp only [abiSlot] at hn; omega))

/-- **The descriptor stores** (`parDescB` for the positions `ps`): word array `wposInv p`'s base
and length, table words `6 + p` and `6 + nw + p`. -/
theorem sim_desc (Q : MachineState → Prop) (hok : abiTabOk tab = true) (hg : BufGeom tab fz own B buf base blen)
    (hfzl : fz.length < 2 ^ 20) (R : Reg64s) (hrcx : R.rcx.toNat = base) (hrdi : R.rdi.toNat = buf)
    (d0 : DataMem) (hB0 : ∀ i (h : i < B.size), rdW d0 (A (buf + 8 * i)) = some B[i])
    (hmap0 : ∀ x, base ≤ x → x < base + blen → (d0.get? (A x)).isSome) :
    ∀ (ps qs : List Nat) (k : Nat) (s : MachineData),
      Code (ps.flatMap fun p => parDescB tab fz own (tab.wposInv p)) k →
      (∀ p ∈ ps, p < tab.nw) → (∀ q ∈ qs, q < bufN tab) →
      (∀ r, r ≠ .rax → s.regs.get64 r = R.get64 r) → s.dmem = qwrs base (bufVal tab buf B base fz own) d0 qs →
      (∀ s' : MachineData,
        s'.dmem = qwrs base (bufVal tab buf B base fz own) d0 (qs ++ ps.flatMap fun p => [6 + p, 6 + tab.nw + p]) →
        (∀ r, r ≠ .rax → s'.regs.get64 r = R.get64 r) →
        Ev Q s' (at_ (k + (ps.flatMap fun p => parDescB tab fz own (tab.wposInv p)).length))) →
      Ev Q s (at_ k) := by
  obtain ⟨hnb, htab, -⟩ := abiTabOk_spec hok
  have hn := hg.need
  have hf := hg.fits
  have hbe := hg.bend
  unfold workerNeed at hn
  intro ps
  induction ps with
  | nil =>
    intro qs k s _ _ _ hR hmem hK
    exact ev_congr (hK s (by simpa using hmem) hR) (by simp)
  | cons p ps ih =>
    intro qs k s hc hps hqs hR hmem hK
    simp only [List.flatMap_cons] at hc hK
    have hp := hps p List.mem_cons_self
    have hps' : ∀ p ∈ ps, p < tab.nw := fun p h => hps p (List.mem_cons_of_mem _ h)
    have ha := tab.wposInv_lt hp
    have hwp := tab.wpos_wposInv hp
    have hq1 : 6 + p < bufN tab := by simp only [bufN]; omega
    have hq2 : 6 + tab.nw + p < bufN tab := by simp only [bufN]; omega
    have hN : 8 * bufN tab ≤ 2 ^ 31 := by simp only [bufN]; omega
    have hoB : tab.base64 (tab.wposInv p) = ((8 * (6 + p) : Nat) : Int) := by
      simp only [Tab.base64, hnb, hwp]; omega
    have hoL : tab.len64 (tab.wposInv p) = ((8 * (6 + tab.nw + p) : Nat) : Int) := by
      simp only [Tab.len64, hnb, hwp]; omega
    have hrc : ∀ s : MachineData, (∀ r, r ≠ .rax → s.regs.get64 r = R.get64 r) → (s.regs.get64 .rcx).toNat = base :=
      fun s h => by rw [h .rcx (by decide)]; simpa using hrcx
    have hvB : bufVal tab buf B base fz own (6 + p) = (UInt64.ofNat (bufB B buf base fz own (tab.wposInv p))).toBitVec := by
      simp only [bufVal, show 6 + p ≠ 0 by omega, show 6 + p ≠ 1 by omega, show ¬ 6 + p < 6 by omega,
        show 6 + p < 6 + tab.nw by omega, if_false, if_true, show 6 + p - 6 = p by omega]
    have hvL : bufVal tab buf B base fz own (6 + tab.nw + p) = (UInt64.ofNat (bufL B fz own (tab.wposInv p))).toBitVec := by
      simp only [bufVal, show 6 + tab.nw + p ≠ 0 by omega, show 6 + tab.nw + p ≠ 1 by omega,
        show ¬ 6 + tab.nw + p < 6 by omega, show ¬ 6 + tab.nw + p < 6 + tab.nw by omega,
        show 6 + tab.nw + p < 6 + 2 * tab.nw by omega, if_false, if_true, show 6 + tab.nw + p - 6 - tab.nw = p by omega]
    -- after the two stores: the rest
    have hrest : ∀ k' s', k' = k + (parDescB tab fz own (tab.wposInv p)).length →
        s'.dmem = qwrs base (bufVal tab buf B base fz own) d0 (qs ++ [6 + p] ++ [6 + tab.nw + p]) →
        (∀ r, r ≠ .rax → s'.regs.get64 r = R.get64 r) → Ev Q s' (at_ k') := by
      intro k' s' hk' hm' hR'
      subst hk'
      refine ih (qs ++ [6 + p] ++ [6 + tab.nw + p]) _ s' hc.right hps' ?_ hR' hm' ?_
      · intro q hq; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with (h | h) | h
        · exact hqs q h
        · omega
        · omega
      · intro s'' hm'' hR''
        refine ev_congr (hK s'' (by rw [hm'']; simp) hR'') (by simp; omega)
    obtain ⟨-, hcell, -⟩ := qwrs_facts hok hg (bufVal tab buf B base fz own) d0 hB0 hmap0 qs hqs
    obtain ⟨-, hcell1, -⟩ := qwrs_facts hok hg (bufVal tab buf B base fz own) d0 hB0 hmap0 (qs ++ [6 + p])
      (by intro q hq; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with h | h
          · exact hqs q h
          · omega)
    obtain ⟨hbuf, -, -⟩ := qwrs_facts hok hg (bufVal tab buf B base fz own) d0 hB0 hmap0 qs hqs
    have hc0 := hc.left
    rcases hfz : fz.idxOf? (tab.wposInv p) with _ | i
    · rcases hown : own.idxOf? (tab.wposInv p) with _ | k'
      · -- neither frozen nor owned: `(0, 0)`
        simp only [parDescB, hfz, hown] at hc0
        refine ev_movRI (Code.get (i := 0) hc0 rfl) ?_
        refine ev_storeQ (Code.get (i := 1) hc0 rfl) _ d0 qs (6 + p) hoB (by omega)
          (by rsimp; exact hrc s hR) (by rsimp; rw [hvB]; simp [bufB, hfz, hown]) hmem
          (by rw [hmem]; exact hcell _ hq1) ?_
        refine ev_storeQ (Code.get (i := 2) hc0 rfl) _ d0 (qs ++ [6 + p]) (6 + tab.nw + p) hoL (by omega)
          (by rsimp; exact hrc s hR) (by rsimp; rw [hvL]; simp [bufL, hfz, hown]) rfl
          (hcell1 _ hq2) ?_
        refine hrest _ _ (by simp [parDescB, hfz, hown]) rfl ?_
        intro r hr; rsimp; rw [← hR r hr]; cases r <;> first | exact absurd rfl hr | rfl
      · -- owned: slot `2 + k'`
        simp only [parDescB, hfz, hown] at hc0
        have hk' := idxOf?_lt hown
        have hle : abiSlot * (2 + k') + abiSlot ≤ abiSlot * (2 + own.length) := by
          rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
        refine ev_movRI (Code.get (i := 0) hc0 rfl) ?_
        refine ev_binO (op := .add) (o := oR .rcx) rfl (Code.get (i := 1) hc0 rfl)
          (Or.inr (Or.inr ⟨.rcx, rfl, rfl⟩)) fun st => ?_
        refine ev_storeQ (Code.get (i := 2) hc0 rfl) _ d0 qs (6 + p) hoB (by omega)
          (by rsimp; exact hrc s hR) ?_ hmem (by rw [hmem]; exact hcell _ hq1) ?_
        · rsimp; rw [hvB]; simp only [bufB, hfz, hown, BinOp.eval]
          have e1 := hR .rcx (by decide)
          simp only [Reg64s.get64_rcx] at e1
          have heq : (abiSlot * (2 + k')).toUInt64 + s.regs.rcx = UInt64.ofNat (base + abiSlot * (2 + k')) := by
            apply UInt64.toNat_inj.mp
            rw [UInt64.toNat_add, UInt64.toBitVec_inj.mp e1, hrcx, Nat.toUInt64,
              UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size, abiSlot] at hle hn ⊢; omega),
              UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size, abiSlot] at hle hn ⊢; omega)]
            simp only [abiSlot] at hle hn ⊢; omega
          rw [heq]
        refine ev_movRI (Code.get (i := 3) hc0 rfl) ?_
        refine ev_storeQ (Code.get (i := 4) hc0 rfl) _ d0 (qs ++ [6 + p]) (6 + tab.nw + p) hoL (by omega)
          (by rsimp; exact hrc s hR) (by rsimp; rw [hvL]; simp [bufL, hfz, hown]) rfl
          (hcell1 _ hq2) ?_
        refine hrest _ _ (by simp [parDescB, hfz, hown]) rfl ?_
        intro r hr; rsimp; rw [← hR r hr]; cases r <;> first | exact absurd rfl hr | rfl
    · -- frozen: the buffer's entry `i`
      simp only [parDescB, hfz] at hc0
      have hi := idxOf?_lt hfz
      have hh := hg.hdr i hi
      have hent := hg.ent i hi
      have hrdiR : ∀ s : MachineData, (∀ r, r ≠ .rax → s.regs.get64 r = R.get64 r) → (s.regs.get64 .rdi).toNat = buf :=
        fun s h => by rw [h .rdi (by decide)]; simpa using hrdi
      have hs8 : SmallOff (8 * (8 + 2 * (i : Int))) := by
        have : 8 * (8 + 2 * i) < 2 ^ 31 := by omega
        constructor <;> omega
      have hs9 : SmallOff (8 * (9 + 2 * (i : Int))) := by
        have : 8 * (9 + 2 * i) < 2 ^ 31 := by omega
        constructor <;> omega
      have hb8 : 8 + 2 * i < B.size := by omega
      have hb9 : 9 + 2 * i < B.size := by omega
      refine ev_movRM (Code.get (i := 0) hc0 rfl) hs8 (v := B[8 + 2 * i]'hb8) ?_ ?_
      · rw [hrdiR s hR, hmem, show (8 * (8 + 2 * (i : Int))).toNat = 8 * (8 + 2 * i) by omega]
        exact hbuf _ (by omega)
      refine ev_shlRI (n := 3) (by decide) (Code.get (i := 1) hc0 rfl) fun st => ?_
      refine ev_binO (op := .add) (o := oR .rdi) rfl (Code.get (i := 2) hc0 rfl)
        (Or.inr (Or.inr ⟨.rdi, rfl, rfl⟩)) fun st' => ?_
      refine ev_storeQ (Code.get (i := 3) hc0 rfl) _ d0 qs (6 + p) hoB (by omega)
        (by rsimp; exact hrc s hR) ?_ hmem (by rw [hmem]; exact hcell _ hq1) ?_
      · rsimp; rw [hvB]; simp only [bufB, hfz, BinOp.eval]
        have e1 := hR .rdi (by decide)
        simp only [Reg64s.get64_rdi] at e1
        rw [UInt64.toBitVec_inj.mp e1,
          show R.rdi = UInt64.ofNat buf by rw [← hrdi]; simp, shl3_add]
        simp [bufEntry, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (show 8 + 2 * i < B.size by omega)]
      refine ev_movRM (Code.get (i := 4) hc0 rfl) hs9 (v := B[9 + 2 * i]'hb9) ?_ ?_
      · rsimp
        rw [show s.regs.rdi.toNat = (s.regs.get64 .rdi).toNat from rfl, hrdiR s hR,
          show (8 * (9 + 2 * (i : Int))).toNat = 8 * (9 + 2 * i) by omega]
        obtain ⟨hbuf1, -, -⟩ := qwrs_facts hok hg (bufVal tab buf B base fz own) d0 hB0 hmap0 (qs ++ [6 + p])
          (by intro q hq; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
              rcases hq with h | h
              · exact hqs q h
              · omega)
        exact hbuf1 _ hb9
      refine ev_storeQ (Code.get (i := 5) hc0 rfl) _ d0 (qs ++ [6 + p]) (6 + tab.nw + p) hoL (by omega)
        (by rsimp; exact hrc s hR) ?_ rfl (hcell1 _ hq2) ?_
      · rsimp; rw [hvL]; simp only [bufL, hfz]
        simp [bufEntry, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (show 9 + 2 * i < B.size by omega)]
      refine hrest _ _ (by simp [parDescB, hfz]) rfl ?_
      intro r hr; rsimp; rw [← hR r hr]; cases r <;> first | exact absurd rfl hr | rfl

/-- **The constant data's stores** (`immStores` from table word `q0`). -/
theorem sim_imm (Q : MachineState → Prop) (hok : abiTabOk tab = true) (hg : BufGeom tab fz own B buf base blen)
    (R : Reg64s) (hrcx : R.rcx.toNat = base) (d0 : DataMem)
    (hB0 : ∀ i (h : i < B.size), rdW d0 (A (buf + 8 * i)) = some B[i])
    (hmap0 : ∀ x, base ≤ x → x < base + blen → (d0.get? (A x)).isSome) :
    ∀ (vs : List SVal) (q0 : Nat) (qs : List Nat) (k : Nat) (s : MachineData),
      Code (immStores .rcx (8 * q0) vs) k → q0 + vs.length ≤ bufN tab →
      (∀ i (w : Word), vs[i]? = some (.imm w) → bufVal tab buf B base fz own (q0 + i) = w.toBitVec) →
      (∀ v ∈ vs, ∃ w, v = .imm w) → (∀ q ∈ qs, q < bufN tab) →
      (∀ r, r ≠ .rax → s.regs.get64 r = R.get64 r) → s.dmem = qwrs base (bufVal tab buf B base fz own) d0 qs →
      (∀ s' : MachineData,
        s'.dmem = qwrs base (bufVal tab buf B base fz own) d0 (qs ++ (List.range vs.length).map (q0 + ·)) →
        (∀ r, r ≠ .rax → s'.regs.get64 r = R.get64 r) →
        Ev Q s' (at_ (k + (immStores .rcx (8 * q0) vs).length))) →
      Ev Q s (at_ k) := by
  obtain ⟨hnb, htab, -⟩ := abiTabOk_spec hok
  have hN : 8 * bufN tab ≤ 2 ^ 31 := by simp only [bufN]; omega
  intro vs
  induction vs with
  | nil =>
    intro q0 qs k s _ _ _ _ _ hR hmem hK
    exact ev_congr (hK s (by simpa using hmem) hR) (by simp [immStores])
  | cons v vs ih =>
    intro q0 qs k s hc hlen hval hall hqs hR hmem hK
    obtain ⟨w, rfl⟩ := hall v List.mem_cons_self
    simp only [List.length_cons] at hlen
    simp only [immStores] at hc hK
    have hc0 := hc.left
    obtain ⟨-, hcell, -⟩ := qwrs_facts hok hg (bufVal tab buf B base fz own) d0 hB0 hmap0 qs hqs
    refine ev_movRI (Code.get (i := 0) hc0 rfl) ?_
    refine ev_storeQ (Code.get (i := 1) hc0 rfl) _ d0 qs q0 rfl (by omega)
      (by rsimp; have e := hR .rcx (by decide); rsimp at e; rw [UInt64.toBitVec_inj.mp e, hrcx]) (by rsimp; rw [← hval 0 w rfl, Nat.add_zero]) hmem
      (by rw [hmem]; exact hcell _ (by omega)) ?_
    have hc1 := hc.right
    rw [show 8 * q0 + 8 = 8 * (q0 + 1) by omega] at hc1 hK
    refine ev_congr (ih (q0 + 1) (qs ++ [q0]) _ _ hc1 (by omega)
      (fun i w' h => by rw [show q0 + 1 + i = q0 + (i + 1) by omega]; exact hval (i + 1) w' (by simpa using h))
      (fun v hv => hall v (List.mem_cons_of_mem _ hv))
      (fun q hq => by
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with h | h
        · exact hqs q h
        · omega)
      (by intro r hr; rsimp; rw [← hR r hr]; cases r <;> first | exact absurd rfl hr | rfl) rfl ?_) (by simp)
    intro s' hm' hR'
    refine ev_congr (hK s' ?_ hR') (by simp; omega)
    rw [hm', List.length_cons, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, List.append_assoc, List.singleton_append, Nat.add_zero]
    congr 2
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp]; omega

end

end ConAgua.Final
