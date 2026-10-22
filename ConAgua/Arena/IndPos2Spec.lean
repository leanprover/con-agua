import ConAgua.Arena.IndPos2
import ConAgua.Arena.IndLibSpec
import ConAgua.Arena.Env

/-!
# Refinements of `IndPos2` (lane `induct`, worker E, round 2)

`nest_block_of` refines `nestBlockOf`, through `envFind_refines` (`ConAgua/Arena/Env.lean`) and a
decoding lemma for `decCI`'s `indInfo` arm at a known kind word (`decCI_kind3`, in the shape of
`Env.lean`'s `decCI_name`). `IndCaps.all` (like `IndCaps.ctors`, per `IndInstall.lean`'s own note)
is an `EREC` slice, read directly off the found constant's record (as module `IndPos`'s
`nest_container_ctors` already does for `caps.ctors`): `decCaps`'s `all` field is `hlist?` over the
SAME array `decCI` was given, which for a row found through `env_find` is `erA m` — so the twin's
`nestBlockOf fe C` decodes at `hslice? (erA m) (EREC.u64[q + 15]) (EREC.u64[q + 16])` where `q` is
the found row's record pointer, via `IndIface.lean`'s generic `hslice?`.

**A round-1 bug found while proving this**: the original `nestFrameMates.go` read its input slice
(`nestBlockOf`'s result) off `IW`, but it is `EREC`-resident. Fixed in `IndPos2.lean` (now reading
`EREC.u64[off + j]`), together with its `#guard` (now building its test block in `EREC`). Not
reproved this round: see the report (blocked on `sl_snoc`'s and `iw_copy`'s word models, not yet
in `IndLibSpec.lean`, and — for `nestWalkStack` — on `nest_ctx_hi_at`'s refinement, not yet proved
by module `IndPos`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `decCI`'s `indInfo` arm, at a known kind word -/

/-- **A decoded record at kind word `3` is `indInfo`**, with its caps: `decCI`'s match only
reaches the `.indInfo` arm from `nat? a p = some 3` (`Env.lean`'s `decCI_name` destructures the
same match generically, for the name field). -/
theorem decCI_kind3 {a : Array Word} {dn : NIdx → Option ConLeche.Name} {p : Nat}
    {ci : IConstantInfo} (h : decCI a dn p = some ci) (hk : nat? a p = some 3) :
    ∃ cv caps, ci = .indInfo cv caps ∧ decCaps a dn (p + 5) = some caps := by
  simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨k, hk', h⟩ := h
  have hk3 : k = 3 := Option.some.inj (hk'.symm.trans hk)
  subst hk3
  simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨cv, hcv, caps, hcaps, rfl⟩ := h
  exact ⟨cv, caps, rfl, hcaps⟩

/-- The contrapositive: an `indInfo` record's kind word is `3`. -/
theorem decCI_indInfo_kind {a : Array Word} {dn : NIdx → Option ConLeche.Name} {p : Nat}
    {cv : IConstantVal} {caps : IIndCaps} (h : decCI a dn p = some (.indInfo cv caps)) :
    nat? a p = some 3 := by
  simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨k, hk, h⟩ := h
  rw [hk]
  congr 1
  match k, h with
  | 0, h => simp_all [Option.bind_eq_some_iff, Option.some.injEq]
  | 1, h => simp_all [Option.bind_eq_some_iff, Option.some.injEq]
  | 2, h => simp_all [Option.bind_eq_some_iff, Option.some.injEq]
  | 3, h => rfl
  | 4, h => simp_all [Option.bind_eq_some_iff, Option.some.injEq]
  | 5, h => simp_all [Option.bind_eq_some_iff, Option.some.injEq]
  | 6, h => simp_all [Option.bind_eq_some_iff, Option.some.injEq]
  | (_ + 7), h => simp_all

/-- A word read off `EREC` at a `Nat` position, as `nat?` decodes it. -/
theorem erN_rdW {m : Mem} {q : Nat} {k : Nat} (h : nat? (erA m) q = some k) (hq : q < 2 ^ 64) :
    rdW (m.arr64 EREC) (UInt64.ofNat q) = UInt64.ofNat k := by
  simp only [nat?, erA, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h
  have hqq : (UInt64.ofNat q).toNat = q := by simp; omega
  simp only [rdW, hqq, hw, Option.getD_some, UInt64.ofNat_toNat]

/-- A `nat?`-decoded value is below `2 ^ 64` (it is some word's `toNat`). -/
theorem nat?_lt {a : Array Word} {i k : Nat} (h : nat? a i = some k) : k < 2 ^ 64 := by
  simp only [nat?, Option.map_eq_some_iff] at h
  obtain ⟨w, -, rfl⟩ := h
  exact w.toNat_lt

/-- `hlist?`'s two-word header, unfolded. -/
theorem hlist?_some {k : IdxKind} {a : Array Word} {i : Nat} {xs : List (Idx k)}
    (h : hlist? a i = some xs) :
    ∃ o l, nat? a i = some o ∧ nat? a (i + 1) = some l ∧ hslice? a o l = some xs := by
  simp only [hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨o, ho, l, hl, h⟩ := h
  exact ⟨o, l, ho, hl, h⟩

/-- `UInt64.ofNat` of a sum, when the `Nat` is small. -/
theorem ofNat_add_small (q k : Nat) (hq : q + k < 2 ^ 64) :
    (UInt64.ofNat q + UInt64.ofNat k : Word) = UInt64.ofNat (q + k) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_add]
  have h1 : (UInt64.ofNat q).toNat = q := by simp; omega
  have h2 : (UInt64.ofNat k).toNat = k := by simp; omega
  have h3 : (UInt64.ofNat (q + k)).toNat = q + k := by simp; omega
  rw [h1, h2, h3]
  omega

/-! ## `nest_block_of` refines `nestBlockOf`: the pure fact -/

/-- **What `nest_block_of` computes, as a function of `env_find`'s result**: the key lemma,
proved purely over `Mem`/`Word`, outside the L execution.

Two extra hypotheses, beyond `hfound`, are needed and not discharged this round (see the
report): `hwf` — the found record, if its kind word is `3`, fully decodes as `indInfo` (true for
any row actually installed through `IFEnv.push`, by `EnvR`'s own `consts` invariant — relating
that to a *found* row's pointer needs more of `Env.lean`'s machinery than this round reaches) —
and `hqb`, a slack bound on pointers so `q + 15`/`q + 16` do not wrap (true for any real `EREC`,
whose size is nowhere near `2 ^ 64`). -/
theorem nestBlockOf_key {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} {c : Word} {m : Mem}
    (found q : Word) (hfound : fe.find? (decI c) = decFound dn m found q)
    (hwf : rdW (m.arr64 EREC) q = (3 : Word) →
      ∃ cv caps, decCI (erecP m) dn q.toNat = some (.indInfo cv caps))
    (hqb : q.toNat + 16 < 2 ^ 64) :
    hslice? (erA m)
        (if found = 0 then (0 : Word) else if rdW (m.arr64 EREC) q = 3 then
          rdW (m.arr64 EREC) (q + 15) else 0).toNat
        (if found = 0 then (0 : Word) else if rdW (m.arr64 EREC) q = 3 then
          rdW (m.arr64 EREC) (q + 16) else 0).toNat
      = some (nestBlockOf fe (decI c)) := by
  rw [nestBlockOf]
  unfold decFound at hfound
  by_cases h0 : found = 0
  · simp only [h0, hfound, ite_true]
    simp [hslice?]
  · simp only [h0, ite_false] at hfound ⊢
    have hqlt : q.toNat < 2 ^ 64 := q.toNat_lt
    have hsize : UInt64.size = 2 ^ 64 := rfl
    by_cases hk3 : rdW (m.arr64 EREC) q = (3 : Word)
    · obtain ⟨cv, caps, hci0⟩ := hwf hk3
      rw [hci0] at hfound
      have hci := (erecP_ext m).decCI hci0
      rw [hfound]
      simp only [if_pos hk3]
      obtain ⟨cv', caps', he, hcaps⟩ := decCI_kind3 hci (decCI_indInfo_kind hci)
      obtain rfl : caps = caps' := by
        have := he.symm; simp only [IConstantInfo.indInfo.injEq] at this; exact this.2.symm
      rw [decCaps] at hcaps
      simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at hcaps
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, vall, hvall, _, _, hcapseq⟩ := hcaps
      obtain ⟨actors, -, heq⟩ := hcapseq
      have hallcaps : caps.all = vall := by
        have h' := Option.some.inj heq; rw [← h']
      obtain ⟨o, l, ho, hl, hslc⟩ := hlist?_some hvall
      have ho' : nat? (erA m) (q.toNat + 15) = some o := by
        have heq2 : q.toNat + 5 + 10 = q.toNat + 15 := by omega
        rwa [heq2] at ho
      have hl' : nat? (erA m) (q.toNat + 16) = some l := by
        have heq2 : q.toNat + 5 + 10 + 1 = q.toNat + 16 := by omega
        rwa [heq2] at hl
      have hwo : rdW (m.arr64 EREC) (q + 15) = UInt64.ofNat o := by
        have e15 : (q + 15 : Word) = UInt64.ofNat (q.toNat + 15) := by
          apply UInt64.toNat_inj.mp
          rw [UInt64.toNat_add]
          have hA : (UInt64.ofNat (q.toNat + 15)).toNat = q.toNat + 15 :=
            UInt64.toNat_ofNat_of_lt' (by omega)
          have hB : (15 : Word).toNat = 15 := by decide
          rw [hA, hB]
          omega
        rw [e15]; exact erN_rdW ho' (by omega)
      have hwl : rdW (m.arr64 EREC) (q + 16) = UInt64.ofNat l := by
        have e16 : (q + 16 : Word) = UInt64.ofNat (q.toNat + 16) := by
          apply UInt64.toNat_inj.mp
          rw [UInt64.toNat_add]
          have hA : (UInt64.ofNat (q.toNat + 16)).toNat = q.toNat + 16 :=
            UInt64.toNat_ofNat_of_lt' (by omega)
          have hB : (16 : Word).toNat = 16 := by decide
          rw [hA, hB]
          omega
        rw [e16]; exact erN_rdW hl' (by omega)
      rw [hwo, hwl]
      have hoo : (UInt64.ofNat o).toNat = o := UInt64.toNat_ofNat_of_lt' (nat?_lt ho')
      have hll : (UInt64.ofNat l).toNat = l := UInt64.toNat_ofNat_of_lt' (nat?_lt hl')
      rw [hoo, hll, hallcaps]
      exact hslc
    · simp only [if_neg hk3]
      have hnind : ∀ cv caps, fe.find? (decI c) ≠ some (.indInfo cv caps) := by
        intro cv caps hfc
        rw [hfound] at hfc
        have hfc := (erecP_ext m).decCI hfc
        exact hk3 (by
          have hk := decCI_indInfo_kind hfc
          have := erN_rdW hk hqlt
          rwa [UInt64.ofNat_toNat] at this)
      cases hm : fe.find? (decI c) with
      | none => simp [hslice?]
      | some ci =>
        cases ci with
        | indInfo cv caps => exact absurd hm (hnind cv caps)
        | axiomInfo _ => simp [hslice?]
        | defnInfo _ _ _ => simp [hslice?]
        | thmInfo _ => simp [hslice?]
        | ctorInfo _ _ _ => simp [hslice?]
        | recInfo _ _ _ _ => simp [hslice?]
        | projInfo _ => simp [hslice?]

/-! ## `nest_block_of` refines `nestBlockOf`: not closed this round

`nestBlockOf_key` above is the mathematical content (what `nest_block_of` computes, as a pure
fact about `Mem`); threading it through the L execution (`invoke p (exec p n) "nest_block_of"
[vis, c]`, composing `envFind_refines` as a callee spec) built far enough that `vcgen` locates
`envFind_refines` as the callee spec for the `env_find` call (citing it as `envFind_refines p hx
hg hf n`, *not* applying its further arguments — vis/w/hE/hw are then unified and discharged by
`finish` itself, as `Env.lean`'s own `envPush_refines` does for `envRowSet_spec`; supplying them
explicitly made `vcgen` fail to find the spec at all, for reasons not tracked down this round),
but the final `finish (gen := 20) [nestBlockOf_key]` leaves one verification condition open (its
context has an unexplained extra `a✝ : Idx IdxKind.name` and reduces to `⊢ False`, with `grind`'s
diagnostics showing `hwf`/`hqb`/`nestBlockOf_key` all E-matched — not a missing fact so much as a
pattern the automation doesn't close). Left for the next round; see the report. -/

end L.Ind
