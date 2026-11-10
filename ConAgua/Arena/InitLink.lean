module

import ConAgua.Arena.DerRel
public import ConAgua.Arena.Tiers
public import ConAgua.Arena.IndexRel

@[expose] public section

/-!
# The initial store (lane `front3`)

The twin's checker starts from `AState.init EStore.empty`; L starts from the harness's memory,
every array zeroed (`initMem`). `arenaD_init` relates the two: the L "code" for `EStore.empty` is
the zeroed memory. (Only the store: `ArenaD` says nothing about the memos, so `AState.init` and
`Memos.empty` stay with their callers.)
-/

namespace L.Arena

open ConRon.Arena

/-- **The zeroed L memory is the twin's empty store** (`arenaD_init`). -/
@[refines ConRon.Arena.EStore.empty]
theorem estoreEmpty_refines (sz : TieredArray → Nat)
    (hctl : 64 ≤ sz CTL) (hpool : sz POOL < 2 ^ 40)
    (hpool1 : sz POOL1 < 2 ^ 40)
    (hsz : ∀ b, InStoreTier b →
      consMinWords ≤ sz b ∧ sz b < 2 ^ 61) :
    ArenaD (initMem sz) (AState.init EStore.empty) :=
  arenaD_init sz hctl hpool hpool1 hsz

/-! ## The rest of the initial state (lane `inits`)

The harness hands L zeroed memory; the twin starts from `AState.init EStore.empty`, `mkIFEnv
IEnv.empty` and `Caches.empty`. Each initial value gets the relation of its tier, at `initMem`. -/

/-- The core-tier schemas' control words fit: `CTL` reaches `120` (the last memo's stamp is `119`). -/
private theorem initMem_ctl (sz : TieredArray → Nat) (h : 120 ≤ sz CTL) :
    120 ≤ ((initMem sz).arr64 CTL).size := by
  rw [initMem_arr]; simpa using h

private theorem initMem_tcnt (sz : TieredArray → Nat) : rdW ((initMem sz).arr64 CTL) 133 = 0 :=
  initMem_rd sz _ _

/-- **The walk memos are empty in zeroed memory** (`Memos.empty`, `inst1Clear` and its siblings
start from it): the four represented tables are the empty map. -/
@[refines ConRon.Arena.Memos.empty]
theorem memosEmpty_refines (sz : TieredArray → Nat)
    (hctl : 64 ≤ sz CTL) (_hpool : sz POOL < 2 ^ 40)
    (_hpool1 : sz POOL1 < 2 ^ 40) :
    MemosR (initMem sz) Memos.empty :=
  memosR_init sz hctl

/-- **The mode memos are empty in zeroed memory**: all six tables are the empty map, the plain
tower's bank `0` and the eager set (`ModeMemos.empty` is both) bank `1`, at eager bit `0`. -/
@[refines ConRon.Arena.ModeMemos.empty]
theorem modeMemosEmpty_refines (sz : TieredArray → Nat) (hctl : 120 ≤ sz CTL) :
    ∃ M : ModeMaps, M = ModeMaps.empty ∧
      ModeR wcSch eKeyG VH (initMem sz) M.wc 0 ModeMemos.empty.whnfCoreC ModeMemos.empty.whnfCoreC ∧
      ModeR wkSch eKeyG VH (initMem sz) M.wk 0 ModeMemos.empty.whnfCoreCheapC ModeMemos.empty.whnfCoreCheapC ∧
      ModeR whSch eKeyG VH (initMem sz) M.wh 0 ModeMemos.empty.whnfC ModeMemos.empty.whnfC ∧
      ModeR inSch eKeyG VH (initMem sz) M.inf 0 ModeMemos.empty.inferC ModeMemos.empty.inferC ∧
      ModeR ioSch eKeyG VH (initMem sz) M.io 0 ModeMemos.empty.inferIOC ModeMemos.empty.inferIOC ∧
      ModeR deSch dKeyG VB (initMem sz) M.de 0 ModeMemos.empty.defeqC ModeMemos.empty.defeqC := by
  have hz := initMem_rd sz
  have hc := initMem_ctl sz hctl
  have wf := coreSch_wf
  have md : ∀ {κ ν : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] [LawfulHashable κ]
      {S : MemoSch} {K : MemoKey (κ × Word)} {VR : Mem → Word → ν → Prop},
      S.cs.toNat + 2 ≤ ((initMem sz).arr64 CTL).size →
      ModeR S K VR (initMem sz) ∅ 0 ∅ ∅ :=
    fun h => ⟨memoRV_zero _ _ _ _ hz h, bank_empty 0, fun _ => bank_empty 1, fun h => absurd rfl h⟩
  exact ⟨ModeMaps.empty, rfl, md (by simp; omega), md (by simp; omega),
    md (by simp; omega), md (by simp; omega), md (by simp; omega),
    md (by simp; omega)⟩

/-- **The per-declaration caches are empty in zeroed memory** (`Caches.empty`, what `flushCaches`
installs and a run starts from): the core tier relates them. -/
@[refines ConRon.Arena.Caches.empty]
theorem cachesEmpty_refines (sz : TieredArray → Nat) (hctl : 120 ≤ sz CTL) :
    CoreR (initMem sz) Caches.empty := by
  have hz := initMem_rd sz
  have hc := initMem_ctl sz hctl
  have md : ∀ {κ ν : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] [LawfulHashable κ]
      {S : MemoSch} {K : MemoKey (κ × Word)} {VR : Mem → Word → ν → Prop},
      S.cs.toNat + 2 ≤ ((initMem sz).arr64 CTL).size →
      ModeR S K VR (initMem sz) ∅ 0 ∅ ∅ :=
    fun h => ⟨memoRV_zero _ _ _ _ hz h, bank_empty 0, fun _ => bank_empty 1, fun h => absurd rfl h⟩
  refine ⟨ModeMaps.empty, ⟨md (by simp; omega), md (by simp; omega),
    md (by simp; omega), md (by simp; omega), md (by simp; omega),
    md (by simp; omega), by decide, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact memoRV_zero _ _ _ _ hz (by simp; omega)
  · exact memoRV_zero _ _ _ _ hz (by simp; omega)
  · exact memoRV_zero _ _ _ _ hz (by simp; omega)
  · exact memoRV_zero _ _ _ _ hz (by simp; omega)
  · exact memoRV_zero _ _ _ _ hz (by simp; omega)

/-- **The pin table is unfilled in zeroed memory** (`Pins.empty`): the flag word is `0`, which
`PinsR` relates to every table (so to the twin's empty one, which `pinAt` refuses). -/
@[refines ConRon.Arena.Pins.empty]
theorem pinsEmpty_refines (sz : TieredArray → Nat) :
    pinW (initMem sz) 0 = 0 ∧ PinsR (initMem sz) Pins.empty := by
  have h : pinW (initMem sz) 0 = 0 := by simp [pinW, initMem_arr, Array.getElem?_replicate]; split <;> rfl
  exact ⟨h, PinsR.of_flag h⟩

/-- **The initial checker state** (`AState.init`): zeroed memory relates the arena, the walk memos
(`ArenaD`), the per-declaration caches (`CoreR`) and the pins (`PinsR`) of `AState.init
EStore.empty` at once; with the store `st` arbitrary the other three parts are `.empty`. -/
@[refines ConRon.Arena.AState.init]
theorem aStateInit_refines (sz : TieredArray → Nat)
    (hctl : 120 ≤ sz CTL) (hpool : sz POOL < 2 ^ 40)
    (hpool1 : sz POOL1 < 2 ^ 40)
    (hsz : ∀ b, InStoreTier b →
      consMinWords ≤ sz b ∧ sz b < 2 ^ 61) :
    ArenaD (initMem sz) (AState.init EStore.empty) ∧
    CoreR (initMem sz) (AState.init EStore.empty).caches ∧
    PinsR (initMem sz) (AState.init EStore.empty).pins ∧
    (∀ st, (AState.init st).store = st ∧ (AState.init st).memos = Memos.empty ∧
      (AState.init st).caches = Caches.empty ∧ (AState.init st).pins = Pins.empty) :=
  ⟨arenaD_init sz (by omega) hpool hpool1 hsz, cachesEmpty_refines sz hctl,
    (pinsEmpty_refines sz).2, fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩

/-- **A constant's name is the handle in word `1` of its record**: the key `env_push` files the
record under, and what `decCI` reads (`IConstantInfo.name`, pure on the twin's side). -/
@[refines ConRon.Arena.IConstantInfo.name]
theorem iConstantInfo_name_refines {a : Array Word} {p : Nat}
    {ci : IConstantInfo} (h : decCI (aread a) p = some ci) :
    ∃ w, a[p + 1]? = some w ∧ w.toNat < 2 ^ 32 ∧ ci.name = decI w := by
  simp only [decCI, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨t, -, h⟩ := h
  have hcv : ∀ {q : Nat} {v : IConstantVal}, decCV (aread a) q = some v →
      ∃ w, a[q]? = some w ∧ w.toNat < 2 ^ 32 ∧ v.name = decI w := fun {q v} hv => by
    simp only [decCV, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hv
    obtain ⟨n, hn, l, -, t, -, rfl⟩ := hv
    simp only [hd?, aread_apply, Option.bind_eq_bind, Option.bind_eq_some_iff] at hn
    obtain ⟨w, hw, hn⟩ := hn
    split at hn
    · cases hn; exact ⟨w, hw, by assumption, rfl⟩
    · cases hn
  split at h <;>
    simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
      reduceCtorEq] at h
  · obtain ⟨v, hv, rfl⟩ := h; exact hcv hv
  · obtain ⟨v, hv, _, _, _, _, rfl⟩ := h; exact hcv hv
  · obtain ⟨v, hv, rfl⟩ := h; exact hcv hv
  · obtain ⟨v, hv, _, _, rfl⟩ := h; exact hcv hv
  · obtain ⟨v, hv, _, _, _, _, rfl⟩ := h; exact hcv hv
  · obtain ⟨v, hv, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := h; exact hcv hv

end L.Arena
