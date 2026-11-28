module

public import ConAgua.Checker.ParDriverTwin
public import ConAgua.Final.CompareTwinSeq
public import ConAgua.Final.CmpSeqTwin
public import ConAgua.Checker.CmpSeqProg
import ConAgua.Checker.BlockRefsProg
import ConAgua.Checker.DefnArmT
import ConAgua.Checker.IndArm

@[expose] public section

/-!
# Target-independent L-level final theorems for flat and compared sequential drivers

Target-independent port of `ConAgua/Final/{DrvFinal,Compare}.lean`:
* `checkerCd_proved`: `check_decl`'s program facts (`CheckerCd`) at every run of entry 1's stages.
* Flat sequential driver (`MODE = 3` → `MODE = 2`):
  `checkerProg_drv_twinAccepts`, `checkerProg_drv_model`, `checkerProg_drv_no_False`.
* Comparator sequential driver (`MODE = 4` → `5` → `6` → `8` → `9`):
  `checkerProg_cmpSeq_twinAccepts`, `checkerProg_cmpSeq_model`, `checkerProg_cmpSeq_no_False`
  (parametric in word-array sizes `sz`, covering both `abiSz checkerTab` and uniform `abiWords`).
-/

namespace ConAgua.Final

open L L.Checker L.Arena ConRon.Arena ConLeche

universe w

/-! ## Flat Sequential Driver (`MODE = 3` → `MODE = 2`) -/

/-- **`check_decl`'s program facts at every run of entry 1's stages** (`CheckerCd`, at every
`PhaseA`: the stages and the stream index): the definition arm's
(`checkerProg_defnLoopPB`) and the inductive arm's (`indArmSpec_checker`). -/
theorem checkerCd_proved : L.Checker.CheckerCd := fun _ pb PA hpb hpre =>
  have hr : L.Rom.RomOK pb.data.toList := by simpa [L.Rom.RomOK] using hpb
  ⟨L.Checker.checkerProg_defnLoopPB _ hr hpre,
    L.Checker.indArmSpec_checker _ hr hpre
      (L.Checker.cbRefs_checker _ hr hpre (L.Checker.snoSim_checker _)) _ PA.dnInj⟩

/-- **The sequential L driver's two runs accept ⇒ the twin accepts** (`drv_twinAccepts` with
`checkerCd_proved` discharged). -/
theorem checkerProg_drv_twinAccepts (b pb : ByteArray)
    (sz : TieredArray → Nat) (hin : InputsOK b pb sz)
    (N₁ : Nat) (hN₁ : N₁ < 2 ^ 62) (rs₁ : List Word) (m₁ : Mem)
    (h₁ : L.run checkerProg N₁ "check" [] (loadMemM b pb sz 3) = .ok (rs₁, m₁))
    (hge : 9223372036854775808 ≤ (rs₁.headD 0).toNat)
    (N₂ : Nat) (hN₂ : N₂ ≤ 2 ^ 62) (w : Mem) (rs₂ : List Word) (m₂ : Mem)
    (hw : ∀ a, phaseBS a = true → w.arr64 a = m₁.arr64 a) (hmode : w.glob MODE = 2)
    (hlo : w.glob PLO = 0) (hhi : w.glob PHI = rs₁.headD 0 - 9223372036854775808)
    (hctlf : (w.arr64 CTLF).size = 0)
    (h₂ : L.run checkerProg N₂ "check" [] w = .ok (rs₂, m₂)) (hacc : rs₂.headD 0 = ACCEPT) :
    TwinAccepts [b] :=
  drv_twinAccepts checkerCd_proved b pb sz hin N₁ hN₁ rs₁ m₁ h₁ hge N₂ hN₂ w rs₂ m₂
    hw hmode hlo hhi hctlf h₂ hacc

/-- **Model existence from an accepting flat L driver run**. -/
theorem checkerProg_drv_model (V : Type w) [SetTheory V] (b pb : ByteArray)
    (sz : TieredArray → Nat) (hin : InputsOK b pb sz)
    (N₁ : Nat) (hN₁ : N₁ < 2 ^ 62) (rs₁ : List Word) (m₁ : Mem)
    (h₁ : L.run checkerProg N₁ "check" [] (loadMemM b pb sz 3) = .ok (rs₁, m₁))
    (hge : 9223372036854775808 ≤ (rs₁.headD 0).toNat)
    (N₂ : Nat) (hN₂ : N₂ ≤ 2 ^ 62) (w : Mem) (rs₂ : List Word) (m₂ : Mem)
    (hw : ∀ a, phaseBS a = true → w.arr64 a = m₁.arr64 a) (hmode : w.glob MODE = 2)
    (hlo : w.glob PLO = 0) (hhi : w.glob PHI = rs₁.headD 0 - 9223372036854775808)
    (hctlf : (w.arr64 CTLF).size = 0)
    (h₂ : L.run checkerProg N₂ "check" [] w = .ok (rs₂, m₂)) (hacc : rs₂.headD 0 = ACCEPT) :
    ∃ (pins : List NatOpPinSet) (preC : ConLeche.Frontend.PreludeIx)
      (rc : ConLeche.Frontend.ParseResultD) (F : Nat) (env : Env),
      ConLeche.Frontend.parseChunks [b] = .ok rc ∧
      checkDeclsPure .verified (fueledOps .verified F) pins
        (ConLeche.Frontend.preparePrelude preC rc.decls).toList = .ok env ∧
      Nonempty (Model V env) :=
  twinAccepts_model V
    (checkerProg_drv_twinAccepts b pb sz hin N₁ hN₁ rs₁ m₁ h₁ hge N₂ hN₂ w rs₂ m₂
      hw hmode hlo hhi hctlf h₂ hacc)

/-- **Soundness (`no_False`) from an accepting flat L driver run**. -/
theorem checkerProg_drv_no_False (V : Type w) [SetTheory V] (b pb : ByteArray)
    (sz : TieredArray → Nat) (hin : InputsOK b pb sz)
    (hfalse : jsonWithTheoremFalse [b])
    (N₁ : Nat) (hN₁ : N₁ < 2 ^ 62) (rs₁ : List Word) (m₁ : Mem)
    (h₁ : L.run checkerProg N₁ "check" [] (loadMemM b pb sz 3) = .ok (rs₁, m₁))
    (hge : 9223372036854775808 ≤ (rs₁.headD 0).toNat)
    (N₂ : Nat) (hN₂ : N₂ ≤ 2 ^ 62) (w : Mem) (rs₂ : List Word) (m₂ : Mem)
    (hw : ∀ a, phaseBS a = true → w.arr64 a = m₁.arr64 a) (hmode : w.glob MODE = 2)
    (hlo : w.glob PLO = 0) (hhi : w.glob PHI = rs₁.headD 0 - 9223372036854775808)
    (hctlf : (w.arr64 CTLF).size = 0)
    (h₂ : L.run checkerProg N₂ "check" [] w = .ok (rs₂, m₂)) (hacc : rs₂.headD 0 = ACCEPT) :
    False :=
  twinAccepts_no_False V hfalse
    (checkerProg_drv_twinAccepts b pb sz hin N₁ hN₁ rs₁ m₁ h₁ hge N₂ hN₂ w rs₂ m₂
      hw hmode hlo hhi hctlf h₂ hacc)

/-! ## Comparator Sequential Driver (`MODE = 4` → `5` → `6` → `8` → `9`) -/

/-- **The sequential compared L driver's run accepts ⇒ the twin accepts (`TwinComparesAccepts bC bS`)**. -/
theorem checkerProg_cmpSeq_twinAccepts (sz : TieredArray → Nat) (hsz : ∀ s, sz s < 2 ^ 64)
    (hsz6 : ∀ g ≤ 2, sz (sixArr g) = sz (eixArr g) ∧ sz (stxArr g) = sz (tixArr g))
    (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (h : CmpAccSSz sz checkerProg MODE PLO PHI OUT HDRF CTLF hdrHw bC bS pb) :
    TwinComparesAccepts bC bS :=
  cmpAccSSz_twin sz hsz hsz6 bC bS pb h64 checkerProg_cqSeq h

/-- **An accepted comparison's challenge has a model** (independent of `bS` and `pb`):
`ConLeche.Frontend.parseChunks [bC]` succeeds and its prepared records (with each hole/sorry read
as the axiom of its statement via `ConLeche.Cached.sideRecord`) admit a `ConLeche.Model V` in every
set theory `V`. -/
theorem checkerProg_cmpSeq_model (V : Type w) [SetTheory V]
    (sz : TieredArray → Nat) (hsz : ∀ s, sz s < 2 ^ 64)
    (hsz6 : ∀ g ≤ 2, sz (sixArr g) = sz (eixArr g) ∧ sz (stxArr g) = sz (tixArr g))
    (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (h : CmpAccSSz sz checkerProg MODE PLO PHI OUT HDRF CTLF hdrHw bC bS pb) :
    ∃ (rcC : ConLeche.Frontend.ParseResultD) (preC : ConLeche.Frontend.PreludeIx),
      ConLeche.Frontend.parseChunks [bC] = .ok rcC ∧
      Nonempty (Model V (ConLeche.streamEnv
        ((ConLeche.Frontend.preparePrelude preC rcC.decls).toList.map ConLeche.Cached.sideRecord))) :=
  twinComparesAccepts_model V (checkerProg_cmpSeq_twinAccepts sz hsz hsz6 bC bS pb h64 h)

/-- **No `False` in an accepted comparison's challenge**, whatever the solution `bS` and pins `pb`. -/
theorem checkerProg_cmpSeq_no_False (V : Type w) [SetTheory V]
    (sz : TieredArray → Nat) (hsz : ∀ s, sz s < 2 ^ 64)
    (hsz6 : ∀ g ≤ 2, sz (sixArr g) = sz (eixArr g) ∧ sz (stxArr g) = sz (tixArr g))
    (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (hfalse : jsonWithTheoremFalse [bC])
    (h : CmpAccSSz sz checkerProg MODE PLO PHI OUT HDRF CTLF hdrHw bC bS pb) :
    False :=
  twinComparesAccepts_no_False V hfalse (checkerProg_cmpSeq_twinAccepts sz hsz hsz6 bC bS pb h64 h)

/-- info: 'ConAgua.Final.checkerCd_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerCd_proved

/-- info: 'ConAgua.Final.checkerProg_drv_twinAccepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerProg_drv_twinAccepts

/-- info: 'ConAgua.Final.checkerProg_drv_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerProg_drv_model

/-- info: 'ConAgua.Final.checkerProg_drv_no_False' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerProg_drv_no_False

/-- info: 'ConAgua.Final.checkerProg_cmpSeq_twinAccepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerProg_cmpSeq_twinAccepts

/-- info: 'ConAgua.Final.checkerProg_cmpSeq_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerProg_cmpSeq_model

/-- info: 'ConAgua.Final.checkerProg_cmpSeq_no_False' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerProg_cmpSeq_no_False

end ConAgua.Final
