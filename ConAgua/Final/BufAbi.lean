import ConAgua.Final.BufLayout
set_option linter.unusedSectionVars false

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

theorem Code.right' [Host] {a b : Program} {k n : Nat} (h : Code (a ++ b) k) (hn : a.length = n) :
    Code b (k + n) := hn ▸ h.right

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
        show 6 + p < 6 + tab.nw by omega, ite_false, ite_true, show 6 + p - 6 = p by omega]
    have hvL : bufVal tab buf B base fz own (6 + tab.nw + p) = (UInt64.ofNat (bufL B fz own (tab.wposInv p))).toBitVec := by
      simp only [bufVal, show 6 + tab.nw + p ≠ 0 by omega, show 6 + tab.nw + p ≠ 1 by omega,
        show ¬ 6 + tab.nw + p < 6 by omega, show ¬ 6 + tab.nw + p < 6 + tab.nw by omega,
        show 6 + tab.nw + p < 6 + 2 * tab.nw by omega, ite_false, ite_true, show 6 + tab.nw + p - 6 - tab.nw = p by omega]
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

/-- **How a thread calls `ca_check_b(buf, buf_len, j, region, region_len)`**: `rdi` = the buffer,
holding the words `B`; `rdx` = `j`; `rcx`, `r8` = the region and its length, mapped; the geometry
of `BufGeom` (the buffer's header and entries inside it, the buffer apart from the region); the
return address on the machine stack, whose 32 bytes around `rsp` are mapped and apart from the
region and the buffer. -/
structure BufCall (tab : Tab) (fz own : List ArrId) (B : Array Word) (dm : MachineData) (ra : Word) : Prop where
  geom : BufGeom tab fz own B dm.regs.rdi.toNat dm.regs.rcx.toNat dm.regs.r8.toNat
  hB : ∀ i (h : i < B.size), rdW dm.dmem (A (dm.regs.rdi.toNat + 8 * i)) = some B[i]
  hmap : ∀ x, dm.regs.rcx.toNat ≤ x → x < dm.regs.rcx.toNat + dm.regs.r8.toNat → (dm.dmem.get? (A x)).isSome
  hra : rdW dm.dmem (A dm.regs.rsp.toNat) = some ra
  hcs : ∀ x, dm.regs.rsp.toNat - 24 ≤ x → x < dm.regs.rsp.toNat + 8 →
    (dm.dmem.get? (A x)).isSome ∧ (x < dm.regs.rcx.toNat ∨ dm.regs.rcx.toNat + dm.regs.r8.toNat ≤ x) ∧
    ¬ (dm.regs.rdi.toNat ≤ x ∧ x < dm.regs.rdi.toNat + 8 * B.size)
  hcs24 : 24 ≤ dm.regs.rsp.toNat
  hcs8 : dm.regs.rsp.toNat + 8 < 2 ^ 64

/-- **From `ca_check_b`**: on a region that holds `r` (`RegionRel`) and a buffer that holds `B`,
the run of `check` from `bufMemG … B r j` (`j` from `rdx`) in `ca_check_b`'s layout. -/
theorem abiB_outcome [Host] (p : Prog) (tab : Tab) (hok : abiTabOk tab = true)
    (hwf : Prog.wf tab p = true) (mode plo phi : GVar) (out hdrf ctlf : ArrId) (hw : Nat)
    (fz own : List ArrId) (hngm : mode.id < tab.ng) (hngl : plo.id < tab.ng) (hngh : phi.id < tab.ng)
    (h12 : plo ≠ phi) (h13 : plo ≠ mode) (h23 : phi ≠ mode) (hfzl : fz.length < 2 ^ 20) (k0 : Nat)
    (hcode : Code (parStub tab mode plo phi out hdrf ctlf hw fz own ++ (abiStub tab ++ compileProg tab p "check")) k0)
    (fd : FunDecl) (hentry : p.lookup "check" = some fd) (hnp : fd.nparams = 0)
    (B : Array Word) (r : Mem) (dm : MachineData) (ra : Word) (hc : BufCall tab fz own B dm ra)
    (hr : RegionRel tab dm.regs.rcx.toNat own r dm.dmem) :
    Ev (EntryPost (bufLayout tab dm.regs.rdi.toNat B dm.regs.rcx.toNat fz own) dm ra
        (L.run p abiFuel "check" [] (bufMemG fz own plo phi mode B r dm.regs.rdx)))
      dm (label abiCheckBL) := by
  obtain ⟨hnb, htab, hneed64⟩ := abiTabOk_spec hok
  have hg := hc.geom
  obtain ⟨buf, hbuf⟩ : ∃ buf, dm.regs.rdi.toNat = buf := ⟨_, rfl⟩
  obtain ⟨base, hbase⟩ : ∃ base, dm.regs.rcx.toNat = base := ⟨_, rfl⟩
  obtain ⟨blen, hblen⟩ : ∃ blen, dm.regs.r8.toNat = blen := ⟨_, rfl⟩
  rw [hbuf, hbase, hblen] at hg
  rw [hbase] at hr
  have hB0 : ∀ i (h : i < B.size), rdW dm.dmem (A (buf + 8 * i)) = some B[i] := by rw [← hbuf]; exact hc.hB
  have hmap0 : ∀ x, base ≤ x → x < base + blen → (dm.dmem.get? (A x)).isSome := by
    rw [← hbase, ← hblen]; exact hc.hmap
  have hn := hg.need
  have hf := hg.fits
  have hbe := hg.bend
  unfold workerNeed at hn
  have hN : 8 * bufN tab ≤ 2 ^ 31 := by simp only [bufN]; omega
  have hb31 : 2 ^ 31 ≤ blen := by simp only [abiSlot] at hn; omega
  have hTE2 : (bufLayout tab buf B base fz own).tabEnd ≤ base + 2 ^ 31 := by
    simp only [Layout.tabEnd, bufLayout_T, bufLayout_tab, bufLayout_nargs]; omega
  have hcP := hcode.left
  have hcC := hcode.right.right
  simp only [parStub] at hcP
  have hL1 := hcP.left.left.left.left.left.left
  have hF1 := hcP.left.left.left.left.left.right
  have hF2 := hcP.left.left.left.left.right
  have hI := hcP.left.left.left.right
  have hL2 := hcP.left.left.right
  rw [Code.label (i := 14) hL1 rfl]
  refine ev_label (Code.get (i := 14) hL1 rfl) ?_
  refine ev_movRI (Code.get (i := 15) hL1 rfl) ?_
  refine ev_cmpRO (r := .r8) (o := oR .rax) (v := (workerNeed own).toUInt64) (Code.get (i := 16) hL1 rfl)
    (Or.inr (Or.inr ⟨.rax, rfl, rfl⟩)) ?_
  refine ev_jcc (Code.get (i := 17) hL1 rfl) (fun hlt => ?_) (fun _ => ?_)
  · -- a region smaller than `workerNeed`: excluded by `BufGeom`
    exfalso
    simp only [CondCode.interp, cmpFlags_cf, decide_eq_true_eq, Reg64s.get64_r8, Reg64s.set64_rax,
      UInt64.toNat_toBitVec] at hlt
    rw [Nat.toUInt64, UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size, workerNeed]; omega), hblen] at hlt
    simp only [workerNeed] at hlt; omega
  have hrcx0 : (dm.regs.get64 .rcx).toNat = base := by simpa using hbase
  have hfit0 : ∀ q < bufN tab, (rdW (qwrs base (bufVal tab buf B base fz own) dm.dmem []) (A (base + 8 * q))).isSome :=
    (qwrs_facts hok hg (bufVal tab buf B base fz own) dm.dmem hB0 hmap0 [] (by simp)).2.1
  refine ev_movRR (Code.get (i := 18) hL1 rfl) ?_
  refine ev_addRI (Code.get (i := 19) hL1 rfl) fun st1 => ?_
  refine ev_movRI (Code.get (i := 20) hL1 rfl) ?_
  refine ev_binO (op := .add) (o := oR .rcx) rfl (Code.get (i := 21) hL1 rfl)
    (Or.inr (Or.inr ⟨.rcx, rfl, rfl⟩)) fun st2 => ?_
  have hsum : ∀ c : Nat, c + base < 2 ^ 64 → (BinOp.add.eval (c.toUInt64) dm.regs.rcx).toBitVec =
      (UInt64.ofNat (base + c)).toBitVec := fun c hc => by
    congr 1; apply UInt64.toNat_inj.mp
    simp only [BinOp.eval, UInt64.toNat_add, Nat.toUInt64, hbase,
      UInt64.toNat_ofNat_of_lt' (show c < UInt64.size by simp only [UInt64.size]; omega),
      UInt64.toNat_ofNat_of_lt' (show base + c < UInt64.size by simp only [UInt64.size]; omega)]
    omega
  refine ev_storeQ (Code.get (i := 22) hL1 rfl) (bufVal tab buf B base fz own) dm.dmem [] 0 rfl (by omega)
    (by rsimp; simpa using hbase) ?_ rfl (hfit0 0 (by simp only [bufN]; omega)) ?_
  · rsimp; rw [hsum _ (by simp only [abiSlot, abiStack] at hn ⊢; omega),
      show base + (abiSlot + abiStack) = base + abiSlot + abiStack by omega]
    simp only [bufVal, ↓reduceIte]
  refine ev_movRI (Code.get (i := 23) hL1 rfl) ?_
  refine ev_binO (op := .add) (o := oR .rcx) rfl (Code.get (i := 24) hL1 rfl)
    (Or.inr (Or.inr ⟨.rcx, rfl, rfl⟩)) fun st3 => ?_
  refine ev_storeQ (Code.get (i := 25) hL1 rfl) (bufVal tab buf B base fz own) dm.dmem [0] 1 rfl (by omega)
    (by rsimp; simpa using hbase) ?_ rfl ?_ ?_
  · rsimp; rw [hsum _ (by simp only [abiSlot] at hn ⊢; omega)]
    simp only [bufVal, show (1 : Nat) ≠ 0 by decide, ↓reduceIte]
  · exact (qwrs_facts hok hg (bufVal tab buf B base fz own) dm.dmem hB0 hmap0 [0]
      (by intro q h; simp only [List.mem_singleton] at h; subst h; simp only [bufN]; omega)).2.1 1
      (by simp only [bufN]; omega)
  refine ev_movRI (Code.get (i := 26) hL1 rfl) ?_
  have hcell : ∀ qs : List Nat, (∀ q ∈ qs, q < bufN tab) → ∀ q < bufN tab,
      (rdW (qwrs base (bufVal tab buf B base fz own) dm.dmem qs) (A (base + 8 * q))).isSome :=
    fun qs h => (qwrs_facts hok hg (bufVal tab buf B base fz own) dm.dmem hB0 hmap0 qs h).2.1
  have hv0 : ∀ q, 2 ≤ q → q < 6 → bufVal tab buf B base fz own q = 0 := fun q h1 h2 => by
    simp only [bufVal, show q ≠ 0 by omega, show q ≠ 1 by omega, h2, ↓reduceIte]
  have hF1' := Code.right' hcP.left.left.left.left.left (n := 27) (by simp only [List.length_cons, List.length_nil])
  rw [hnb] at hF1'
  refine ev_congr (j := k0 + 27) ?_ (by omega)
  have hqb : ∀ q, q < 6 → q < bufN tab := fun q h => by simp only [bufN]; omega
  refine ev_storeQ (Code.get (i := 0) hF1' rfl) (bufVal tab buf B base fz own) dm.dmem ([] ++ [0] ++ [1]) 2
    (by simp [Tab.base8]) (by omega) (by rsimp; simpa using hbase) (by rsimp; rw [hv0 2 (by omega) (by omega)]; rfl)
    rfl (hcell _ (by intro q hq; simp at hq; simp only [bufN]; omega) _ (hqb 2 (by omega))) ?_
  refine ev_storeQ (Code.get (i := 1) hF1' rfl) (bufVal tab buf B base fz own) dm.dmem ([] ++ [0] ++ [1] ++ [2]) 3
    (by simp [Tab.len8]) (by omega) (by rsimp; simpa using hbase) (by rsimp; rw [hv0 3 (by omega) (by omega)]; rfl)
    rfl (hcell _ (by intro q hq; simp at hq; simp only [bufN]; omega) _ (hqb 3 (by omega))) ?_
  refine ev_storeQ (Code.get (i := 2) hF1' rfl) (bufVal tab buf B base fz own) dm.dmem ([] ++ [0] ++ [1] ++ [2] ++ [3]) 4
    (by simp [Tab.base8]) (by omega) (by rsimp; simpa using hbase) (by rsimp; rw [hv0 4 (by omega) (by omega)]; rfl)
    rfl (hcell _ (by intro q hq; simp at hq; simp only [bufN]; omega) _ (hqb 4 (by omega))) ?_
  refine ev_storeQ (Code.get (i := 3) hF1' rfl) (bufVal tab buf B base fz own) dm.dmem ([] ++ [0] ++ [1] ++ [2] ++ [3] ++ [4]) 5
    (by simp [Tab.len8]) (by omega) (by rsimp; simpa using hbase) (by rsimp; rw [hv0 5 (by omega) (by omega)]; rfl)
    rfl (hcell _ (by intro q hq; simp at hq; simp only [bufN]; omega) _ (hqb 5 (by omega))) ?_
  have hF2' := Code.right' hcP.left.left.left.left (n := 31)
    (by simp only [List.length_append, List.length_cons, List.length_nil, flatMap_pair_length, hnb])
  refine ev_congr (j := k0 + 31) ?_ (by omega)
  have hqs6 : ∀ q ∈ ([] ++ [0] ++ [1] ++ [2] ++ [3] ++ [4] ++ [5] : List Nat), q < bufN tab := by
    intro q hq; simp at hq; simp only [bufN]; omega
  refine sim_desc _ hok hg hfzl _ (by rsimp; simpa using hbase) (by rsimp; simpa using hbuf) dm.dmem hB0 hmap0
    (List.range tab.nw) _ _ _ hF2' (fun p h => List.mem_range.mp h) hqs6 (fun _ _ => rfl) rfl ?_
  intro s1 hm1 hR1
  have hI' := Code.right' hcP.left.left.left
    (n := 31 + (List.flatMap (fun p => parDescB tab fz own (tab.wposInv p)) (List.range tab.nw)).length)
    (by simp only [List.length_append, List.length_cons, List.length_nil, flatMap_pair_length, hnb])
  rw [show tab.romBase.toNat = 8 * (6 + 2 * tab.nw) by simp only [Tab.romBase, hnb]; omega] at hI'
  refine ev_congr (j := k0 + (31 + (List.flatMap (fun p => parDescB tab fz own (tab.wposInv p)) (List.range tab.nw)).length)) ?_ (by omega)
  have hqs7 : ∀ q ∈ ([] ++ [0] ++ [1] ++ [2] ++ [3] ++ [4] ++ [5] ++
      (List.range tab.nw).flatMap fun p => [6 + p, 6 + tab.nw + p] : List Nat), q < bufN tab := by
    intro q hq
    rw [List.mem_append] at hq
    rcases hq with h | h
    · exact hqs6 q h
    · obtain ⟨p, hp, hq'⟩ := List.mem_flatMap.mp h
      simp only [List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hp hq'
      simp only [bufN]; omega
  have hrl := romVals_length tab.rom
  rw [← tab.romLen_eq] at hrl
  refine sim_imm _ hok hg _ (by rsimp; simpa using hbase) dm.dmem hB0 hmap0 (romVals tab.rom) (6 + 2 * tab.nw)
    _ _ s1 hI' (by rw [hrl]; simp only [bufN, Tab.romWords]; omega) ?_ (romVals_imm tab.rom) hqs7 hR1 hm1 ?_
  · intro i w hw
    simp only [bufVal, show 6 + 2 * tab.nw + i ≠ 0 by omega, show 6 + 2 * tab.nw + i ≠ 1 by omega,
      show ¬ 6 + 2 * tab.nw + i < 6 by omega, show ¬ 6 + 2 * tab.nw + i < 6 + tab.nw by omega,
      show ¬ 6 + 2 * tab.nw + i < 6 + 2 * tab.nw by omega, ↓reduceIte,
      show 6 + 2 * tab.nw + i - 6 - 2 * tab.nw = i by omega, romBits, hw]
  intro s2 hm2 hR2
  -- the registers after the table stores
  have hS : ∀ r, r ≠ .rax → r ≠ .r9 → s2.regs.get64 r = dm.regs.get64 r := by
    intro r h1 h2
    rw [hR2 r h1]
    cases r <;> first | exact absurd rfl h1 | exact absurd rfl h2 | rfl
  have hu : ∀ r, r ≠ .rax → r ≠ .r9 → ∀ (f : Reg64s → UInt64), (∀ R : Reg64s, R.get64 r = (f R).toBitVec) →
      f s2.regs = f dm.regs := fun r h1 h2 f hf => UInt64.toBitVec_inj.mp (by rw [← hf, ← hf, hS r h1 h2])
  have e8 : s2.regs.rcx = dm.regs.rcx := hu .rcx (by decide) (by decide) Reg64s.rcx (fun _ => rfl)
  have edi : s2.regs.rdi = dm.regs.rdi := hu .rdi (by decide) (by decide) Reg64s.rdi (fun _ => rfl)
  have edx : s2.regs.rdx = dm.regs.rdx := hu .rdx (by decide) (by decide) Reg64s.rdx (fun _ => rfl)
  have esp : s2.regs.rsp = dm.regs.rsp := hu .rsp (by decide) (by decide) Reg64s.rsp (fun _ => rfl)
  have ebp : s2.regs.rbp = dm.regs.rbp := hu .rbp (by decide) (by decide) Reg64s.rbp (fun _ => rfl)
  have e14 : s2.regs.r14 = dm.regs.r14 := hu .r14 (by decide) (by decide) Reg64s.r14 (fun _ => rfl)
  have e15 : s2.regs.r15 = dm.regs.r15 := hu .r15 (by decide) (by decide) Reg64s.r15 (fun _ => rfl)
  have e9 : s2.regs.r9 = dm.regs.rdx + 1 := by
    have := hR2 .r9 (by decide)
    rsimp at this
    exact UInt64.toBitVec_inj.mp (by rw [this]; rfl)
  -- the table words: every one written
  obtain ⟨qsT, hqsT⟩ : ∃ qsT : List Nat, qsT = [] ++ [0] ++ [1] ++ [2] ++ [3] ++ [4] ++ [5] ++
      ((List.range tab.nw).flatMap fun p => [6 + p, 6 + tab.nw + p]) ++
      (List.range (romVals tab.rom).length).map (6 + 2 * tab.nw + ·) := ⟨_, rfl⟩
  rw [← hqsT] at hm2
  have hqT : ∀ q < bufN tab, q ∈ qsT := by
    intro q hq
    rw [hqsT]
    simp only [bufN] at hq
    by_cases h6 : q < 6
    · exact List.mem_append_left _ (List.mem_append_left _ (by simp; omega))
    · by_cases h7 : q < 6 + 2 * tab.nw
      · refine List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ?_))
        by_cases h8 : q < 6 + tab.nw
        · exact ⟨q - 6, List.mem_range.mpr (by omega), by simp; omega⟩
        · exact ⟨q - 6 - tab.nw, List.mem_range.mpr (by omega), by simp; omega⟩
      · refine List.mem_append_right _ (List.mem_map.mpr ⟨q - 6 - 2 * tab.nw, List.mem_range.mpr ?_, by omega⟩)
        rw [hrl]; simp only [Tab.romWords] at hq; omega
  have hqT' : ∀ q ∈ qsT, q < bufN tab := by
    intro q hq
    rw [hqsT, List.mem_append] at hq
    rcases hq with h | h
    · exact hqs7 q h
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
      rw [List.mem_range, hrl] at hi
      simp only [bufN, Tab.romWords]; omega
  have hG := bufLayout_ok hok hg
  have hm0 := buf_memRel hok hg r dm.dmem hr hB0 hmap0 qsT hqT hqT'
  obtain ⟨-, hcellT, hmapT⟩ := qwrs_facts hok hg (bufVal tab buf B base fz own) dm.dmem hB0 hmap0 qsT hqT'
  -- the globals
  have hgA : ∀ g : GVar, base + (tab.globOff g).toNat = (bufLayout tab buf B base fz own).globAddr g :=
    fun g => Layout.globAddr_toNat (bufLayout tab buf B base fz own) g
  have hgS : ∀ g : GVar, g.id < tab.ng → base + 8 * bufN tab ≤ (bufLayout tab buf B base fz own).globAddr g ∧
      (bufLayout tab buf B base fz own).globAddr g + 8 ≤ (bufLayout tab buf B base fz own).tabEnd := fun g hg' => by
    simp only [Layout.globAddr, Layout.globStart, Layout.tabEnd, bufLayout_T, bufLayout_tab, bufLayout_nargs, bufN, hnb]
    omega
  have hoffG : ∀ g : GVar, g.id < tab.ng → SmallOff (tab.globOff g) := fun g hg' => by
    simp only [Tab.globOff, Tab.globBase]; constructor <;> omega
  have hc2 : (s2.regs.get64 .rcx).toNat = base := by simp [e8, hbase]
  have hgb : ∀ g : GVar, g.id < tab.ng → ∀ j < 8, (s2.dmem.get? (A (base + (tab.globOff g).toNat + j))).isSome :=
    fun g hg' j hj => by
      rw [hm2, hgA g]
      obtain ⟨h1, h2⟩ := hgS g hg'
      exact hmapT _ (by simp only [Layout.globAddr, Layout.globStart, bufLayout_T] at h1 ⊢; omega)
        (by omega)
  have hL2' := Code.right' hcP.left.left
    (n := 31 + (List.flatMap (fun p => parDescB tab fz own (tab.wposInv p)) (List.range tab.nw)).length +
      (immStores .rcx (8 * (6 + 2 * tab.nw)) (romVals tab.rom)).length)
    (by simp only [List.length_append, List.length_cons, List.length_nil, flatMap_pair_length, hnb,
          show tab.romBase.toNat = 8 * (6 + 2 * tab.nw) by simp only [Tab.romBase, hnb]; omega] <;> omega)
  refine ev_congr (j := k0 + (31 + (List.flatMap (fun p => parDescB tab fz own (tab.wposInv p)) (List.range tab.nw)).length +
      (immStores .rcx (8 * (6 + 2 * tab.nw)) (romVals tab.rom)).length)) ?_ (by omega)
  refine ev_movMR (Code.get (i := 0) hL2' rfl) (hoffG plo hngl)
    (isSome_rdW fun j hj => by rw [A_add, hc2]; exact hgb plo hngl j hj) ?_
  refine ev_movMR (Code.get (i := 1) hL2' rfl) (hoffG phi hngh)
    (isSome_rdW fun j hj => by rw [A_add, hc2]; exact isSome_get?_storeInt (hgb phi hngh j hj)) ?_
  refine ev_movRI (Code.get (i := 2) hL2' rfl) ?_
  refine ev_movMR (Code.get (i := 3) hL2' rfl) (hoffG mode hngm)
    (isSome_rdW fun j hj => by
      rsimp; rw [A_add, show s2.regs.rcx.toNat = base by rw [e8, hbase]]
      exact isSome_get?_storeInt (isSome_get?_storeInt (hgb mode hngm j hj))) ?_
  refine ev_movRR (Code.get (i := 4) hL2' rfl) ?_
  refine ev_movRI (Code.get (i := 5) hL2' rfl) ?_
  refine ev_jmp (Code.get (i := 6) hL2' rfl) ?_
  rsimp
  rw [show s2.regs.rcx.toNat = base by rw [e8, hbase], hgA plo, hgA phi, hgA mode]
  -- the memory relation, and the trampoline's premises
  have hOw : ∀ (d : DataMem) (g : GVar) (v : BitVec 64), g.id < tab.ng →
      Only (base + 8 * bufN tab) (bufLayout tab buf B base fz own).tabEnd d
        (wrW d (A ((bufLayout tab buf B base fz own).globAddr g)) v) := fun d g v hg' => by
    obtain ⟨h1, h2⟩ := hgS g hg'
    exact (Only.wrW (by omega)).mono h1 h2
  have hOg := ((hOw s2.dmem plo s2.regs.rdx.toBitVec hngl).union (hOw _ phi s2.regs.r9.toBitVec hngh)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)).union (hOw _ mode (UInt64.toBitVec 2) hngm)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
  have hTE : base + 8 * bufN tab ≤ (bufLayout tab buf B base fz own).tabEnd := by
    simp only [Layout.tabEnd, bufLayout_T, bufLayout_tab, bufLayout_nargs, bufN, hnb]; omega
  have hO1 : Only base (base + 8 * bufN tab) dm.dmem s2.dmem := by
    rw [hm2]; exact qwrs_only qsT dm.dmem (bufN tab) (by simp only [abiSlot] at hn; omega) hqT'
  have hOall := hO1.union (a := base) (b := (bufLayout tab buf B base fz own).tabEnd) hOg
    (Nat.le_refl _) (by omega) hTE (Nat.le_refl _)
  have hcs := hc.hcs
  rw [hbase, hblen, hbuf] at hcs
  refine eventually_weaken _ _ _ _ ?_ (compile_correct_frame p "check" _ hG hwf _ hcC fd hentry []
    (by simp [hnp]) rfl (bufMemG fz own plo phi mode B r dm.regs.rdx) abiFuel _ ra ?_ ?_ ?_ ?_ ?_
    (fun i h => absurd h (by simp)) ?_ ?_ ?_ ?_ ?_ ?_)
  · intro st ⟨hpc, hsp, hbp, h14, h15, ⟨hbx, hr12, hr13⟩, hfr, hout⟩
    refine ⟨hpc, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [hsp]; show s2.regs.rsp.toNat + 8 = _; rw [esp]
    · rw [hbp]; exact ebp
    · rw [h14]; exact e14
    · rw [h15]; exact e15
    · rw [hbx]; exact hu .rbx (by decide) (by decide) Reg64s.rbx (fun _ => rfl)
    · rw [hr12]; exact hu .r12 (by decide) (by decide) Reg64s.r12 (fun _ => rfl)
    · rw [hr13]; exact hu .r13 (by decide) (by decide) Reg64s.r13 (fun _ => rfl)
    · rw [hbuf, hbase]
      exact MemFrame.only_tab (show MemFrame _ dm.regs.rsp.toNat _ _ by rw [← esp]; exact hfr) hOall
    · rw [hbuf, hbase]; exact hout
  · show s2.regs.rcx.toNat = base; rw [e8, hbase]
  · show (abiFuel.toUInt64).toNat = abiFuel
    simp [abiFuel]
  · show MemRel _ _ (wrW (wrW (wrW s2.dmem _ s2.regs.rdx.toBitVec) _ s2.regs.r9.toBitVec) _ (UInt64.toBitVec 2))
    rw [hm2, edx, e9, bufMemG_eq_setG h12 h13 h23]
    exact ((hm0.storeG hG (g := plo) hngl dm.regs.rdx).storeG hG (g := phi) hngh (dm.regs.rdx + 1)).storeG hG
      (g := mode) hngm 2
  · simp only [bufLayout_lo, bufLayout_hi, abiStack]; omega
  · show rdW (wrW (wrW (wrW s2.dmem _ _) _ _) _ _) (A base) = some (UInt64.ofNat (base + abiSlot + abiStack))
    rw [hOg.rdW_eq (by omega) (Or.inl (by simp only [bufN]; omega)), hm2]
    have := qwrs_rdW (T := base) (val := bufVal tab buf B base fz own) qsT dm.dmem 0 (hqT 0 (by simp only [bufN]; omega))
      (fun q h => by have := hqT' q h; simp only [abiSlot] at hn; omega)
    simp only [Nat.mul_zero, Nat.add_zero] at this
    rw [this]
    simp [bufVal]
  · show rdW (wrW (wrW (wrW s2.dmem _ _) _ _) _ _) (A s2.regs.rsp.toNat) = some ra
    rw [esp, ← hc.hra]
    refine rdW_congr fun j hj => ?_
    rw [A_add, hOall.same _ (by have := hc.hcs8; omega) ?_]
    rcases (hcs (dm.regs.rsp.toNat + j) (by omega) (by have := hc.hcs8; omega)).2.1 with h | h
    · left; omega
    · right; omega
  · intro x h1 h2
    change s2.regs.rsp.toNat - 24 ≤ x at h1
    change x < s2.regs.rsp.toNat + 8 at h2
    rw [esp] at h1 h2
    obtain ⟨hmx, hreg, hnb'⟩ := hcs x h1 h2
    refine ⟨hOall.grows _ hmx, ?_⟩
    have hp := fun h => buf_part hok hg (x := x) h
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    · rcases hp (by simp only [h, true_or, or_true]) with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · omega
      · exact hnb' ⟨h3, h4⟩
  · show 24 ≤ s2.regs.rsp.toNat
    rw [esp]; exact hc.hcs24
  · show s2.regs.rsp.toNat + 8 < 2 ^ 64
    rw [esp]; exact hc.hcs8
  · intro x h1 h2
    obtain ⟨q0, q1, q2, q3⟩ := buf_save hok hg h1 h2
    refine ⟨hOall.grows _ (hmap0 x q0 q1), q2, q3, ?_⟩
    show x < s2.regs.rsp.toNat - 24 ∨ s2.regs.rsp.toNat + 8 ≤ x
    rw [esp]
    refine Classical.byContradiction fun hn' => ?_
    simp only [not_or, Nat.not_lt, Nat.not_le] at hn'
    rcases (hcs x (by omega) (by omega)).2.1 with h | h <;> omega
  · have := buf_save (x := (bufLayout tab buf B base fz own).tabEnd + 31) hok hg (by omega) (by omega)
    have := hg.fits
    omega

end ConAgua.Final
