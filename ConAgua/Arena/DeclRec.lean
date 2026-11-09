module

public import ConAgua.Arena.DeclStep
public import ConAgua.Arena.IndMaster
public import ConAgua.Front.StateDR
public import Std.Tactic.BVDecide.Normalize.Prop
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConRon.Bridge.Grind
public import ConAgua.Arena.Env
import all ConAgua.Arena.DeclStep
import all ConAgua.Arena.Env

@[expose] public section

/-!
# Phase A's record builders: `erec_ci`, `erec_vg`, `env_push` (lane `decls2`, helper `decls2-rec`)

`install_step_go` builds, for a definition, theorem or opaque record `i` of `DECL`, its constant
record in `EREC` (`erec_ci(i, ck)`: kind `ck`, the constant value with a fresh universe-parameter
slice copied from `DLP`, the value, the hint, the height), pushes it (`env_push(vis, q)`), and
builds the value group (`erec_vg(p, vk)`). On lane `indproofs`' template (`DeclCvg.lean`): word
models with continuations and `rfl` arm lemmas, `vcgen` specs against the callee models, and
relational lemmas (`erecCiW_ok`, `envPushW_ok`): from the stage relation a model
run keeps it, only grows the pool, and leaves the records decoding as the twin's values
(`stepCI`: the constant `installStepGo` pushes).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind
open L.Front (DECL DLP)

/-! ## The program -/

/-- The lookups the three builders need. -/
structure RecProg (p : Prog) : Prop where
  alloc : p.lookup "erec_alloc" = some erecAlloc
  dlp : p.lookup "dlp_copy" = some dlpCopy
  ci : p.lookup "erec_ci" = some erecCi
  put : p.lookup "erec_put" = some erecPut
  rs : p.lookup "env_row_set" = some envRowSetL
  push : p.lookup "env_push" = some envPushL

/-! ## Word models and their `vcgen` specs -/

/-- The low 32 bits (`dlp_copy`'s and `erec_ci`'s mask). -/
def mask32 (w : Word) : Word := w &&& 4294967295

/-- The model of `dlp_copy(d, s, l)`. -/
def dlpCopyW : Nat → Mem → Word → Word → Word → Option Mem
  | 0, _, _, _, _ => none
  | n + 1, m, d, s, l =>
    if l = 0 then some m
    else dlpCopyW n (erecPutMem m d (mask32 (rdW (m.arr64 DLP) s))) (d + 1) (s + 1) (l - 1)

section arms
variable (n : Nat) (m : Mem) (d s l : Word)
theorem dlpCopyW_nil (hl : l = 0) : dlpCopyW (n + 1) m d s l = some m := by simp [dlpCopyW, hl]
theorem dlpCopyW_step (hl : l ≠ 0) :
    dlpCopyW (n + 1) m d s l =
      dlpCopyW n (erecPutMem m d (mask32 (rdW (m.arr64 DLP) s))) (d + 1) (s + 1) (l - 1) := by
  simp [dlpCopyW, hl]
end arms

grind_pattern [ind_grind] dlpCopyW_nil => dlpCopyW (n + 1) m d s l
grind_pattern [ind_grind] dlpCopyW_step => dlpCopyW (n + 1) m d s l

theorem dlpCopy_specW (p : Prog) (hp : p.lookup "dlp_copy" = some dlpCopy)
    (hpu : p.lookup "erec_put" = some erecPut) (n : Nat) :
    ∀ (s₀ : St) (d s l : Word),
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "dlp_copy" [d, s, l]
    ⦃fun _ s' => LocEq s' s₀ ∧ dlpCopyW n s₀.mem d s l = some s'.mem; ⊤⦄ := by
  induction n with
  | zero => intro s₀ d s l; rw [invoke_eq _ hp]; simp only [callFn, dlpCopy]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ d s l
    rw [invoke_eq _ hp]
    simp only [callFn, dlpCopy]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih,
        erecPut_specW p hpu n] <;>
      finish (gen := 20) [mask32]

/-- The hint word of a front hint kind `hq` (`1` abbrev, `2` opaque, else regular): `decHint`'s
`1`, `0`, `2`. -/
def hintCode (hq : Word) : Word := if hq = 1 then 1 else if hq = 2 then 0 else 2

/-- The constant record's eight words (`D` read in `m3`). -/
def eciWords (D : Array Word) (i kind s ll : Word) : List Word :=
  [kind, mask32 (rdW D (2 + 8 * i)), s, ll, mask32 (rdW D (5 + 8 * i)), mask32 (rdW D (6 + 8 * i)),
   hintCode (rdW D (7 + 8 * i)), rdW D (8 + 8 * i)]

/-- The memory after `erec_ci`'s eight `erec_put`s. -/
def eciMem (m3 : Mem) (p i kind s ll : Word) : Mem :=
  let D := m3.arr64 DECL
  erecPutMem (erecPutMem (erecPutMem (erecPutMem (erecPutMem (erecPutMem (erecPutMem (erecPutMem m3
    p kind) (p + 1) (mask32 (rdW D (2 + 8 * i)))) (p + 2) s) (p + 3) ll) (p + 4)
    (mask32 (rdW D (5 + 8 * i)))) (p + 5) (mask32 (rdW D (6 + 8 * i)))) (p + 6)
    (hintCode (rdW D (7 + 8 * i)))) (p + 7) (rdW D (8 + 8 * i))

mutual
/-- **The model of `erec_ci(i, kind)`** (the copy runs at `n`). -/
def erecCiW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, i, kind =>
    eciK1 n i kind (rdW (m.arr64 DECL) (3 + 8 * i)) (rdW (m.arr64 DECL) (4 + 8 * i))
      (erAllocW m (rdW (m.arr64 DECL) (4 + 8 * i)))

def eciK1 (n : Nat) (i kind lo ll : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (s, m1) => eciK2 i kind s ll (dlpCopyW n m1 s (1 + lo) ll)

def eciK2 (i kind s ll : Word) : Option Mem → Option (List Word × Mem)
  | none => none
  | some m2 => eciK3 i kind s ll (erAllocW m2 8)

def eciK3 (i kind s ll : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (p, m3) => some ([p], eciMem m3 p i kind s ll)
end

section arms
variable (n : Nat) (m m1 m2 m3 : Mem) (i kind lo ll s p : Word)
theorem erecCiW_step : erecCiW (n + 1) m i kind =
    eciK1 n i kind (rdW (m.arr64 DECL) (3 + 8 * i)) (rdW (m.arr64 DECL) (4 + 8 * i))
      (erAllocW m (rdW (m.arr64 DECL) (4 + 8 * i))) := rfl
theorem eciK1_some : eciK1 n i kind lo ll (some (s, m1)) =
    eciK2 i kind s ll (dlpCopyW n m1 s (1 + lo) ll) := rfl
theorem eciK2_some : eciK2 i kind s ll (some m2) = eciK3 i kind s ll (erAllocW m2 8) := rfl
theorem eciK3_some : eciK3 i kind s ll (some (p, m3)) = some ([p], eciMem m3 p i kind s ll) := rfl
end arms

grind_pattern [ind_grind] erecCiW_step => erecCiW (n + 1) m i kind
grind_pattern [ind_grind] eciK1_some => eciK1 n i kind lo ll (some (s, m1))
grind_pattern [ind_grind] eciK2_some => eciK2 i kind s ll (some m2)
grind_pattern [ind_grind] eciK3_some => eciK3 i kind s ll (some (p, m3))

theorem erecPutMem_decl (m : Mem) (a v : Word) : (erecPutMem m a v).arr64 DECL = m.arr64 DECL := by
  rw [erecPutMem_arr, if_neg (by unfold erTier; split <;> decide)]

theorem erecCi_specW (p : Prog) (h : RecProg p) (n : Nat) (s₀ : St) (i kind : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "erec_ci" [i, kind]
    ⦃fun r s' => LocEq s' s₀ ∧ erecCiW n s₀.mem i kind = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.ci]
  simp only [callFn, erecCi]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        erecAlloc_specW p h.alloc n, dlpCopy_specW p h.dlp h.put n, erecPut_specW p h.put n] <;>
      finish (gen := 20) [eciMem, hintCode, mask32, erecPutMem_decl]

end L.Arena

/-! ## The relational lemmas -/

namespace L.Arena

open L.Ind
open L.Front (DECL DLP DeclsF DeclAt CVAt dw hintW)

/-! ### The twin's values -/

/-- The constant `installStepGo` pushes for record `d` under `erec_ci`'s kind `c` (`1`
definition, `2` theorem, `0` an opaque as an axiom). -/
def stepCI : Nat → IDeclaration → Option IConstantInfo
  | 1, .defnDecl cv v h => some (.defnInfo cv v h)
  | 2, .thmDecl cv _ => some (.thmInfo cv)
  | 0, .opaqueDecl cv _ => some (.axiomInfo cv)
  | _, _ => none

/-- The value of a definition, theorem or opaque. -/
def stepVal : IDeclaration → EIdx
  | .defnDecl _ v _ | .thmDecl _ v | .opaqueDecl _ v => v
  | _ => default

/-- The constant value of a definition, theorem or opaque. -/
def stepCV : IDeclaration → IConstantVal
  | .defnDecl cv _ _ | .thmDecl cv _ | .opaqueDecl cv _ => cv
  | _ => default

/-! ### Words -/

theorem mask32_lt (w : Word) : (mask32 w).toNat < 2 ^ 32 := by
  simp only [mask32, UInt64.toNat_and]
  rw [show (UInt64.toNat 4294967295) = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by decide)

theorem decI_mask32 {k : IdxKind} (w : Word) : (decI (mask32 w) : Idx k) = decI w := by
  simp only [decI, mask32]
  congr 1
  apply UInt32.toNat_inj.mp
  simp only [UInt64.toNat_toUInt32, UInt64.toNat_and]
  rw [show (UInt64.toNat 4294967295) = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp

theorem hd?_mask {k : IdxKind} {a : Nat → Option Word} {i : Nat} {w : Word}
    (h : a i = some (mask32 w)) : (hd? a i : Option (Idx k)) = some (decI w) := by
  simp [hd?, h, decI_mask32, show (mask32 w).toNat < 4294967296 from mask32_lt w]

theorem mapM_some_of {α β : Type} (f : α → Option β) (g : α → β) :
    ∀ l : List α, (∀ x ∈ l, f x = some (g x)) → l.mapM f = some (l.map g)
  | [], _ => rfl
  | x :: xs, h => by
    simp [List.mapM_cons, h x (by simp), mapM_some_of f g xs (fun y hy => h y (by simp [hy]))]

theorem hslice?_mask {k : IdxKind} {a : Nat → Option Word} {o l : Nat} {f : Nat → Word}
    (h : ∀ j < l, a (o + j) = some (mask32 (f j))) :
    (hslice? a o l : Option (List (Idx k))) = some ((List.range l).map fun j => decI (f j)) :=
  mapM_some_of _ _ _ (fun j hj => hd?_mask (h j (List.mem_range.mp hj)))

/-- A constant value from its words: the name and type masked, the slice of masked words. -/
theorem decCV_of_words {a : Nat → Option Word} {q : Nat} {wn wt s ll : Word} {f : Nat → Word}
    (h0 : a q = some (mask32 wn)) (h1 : a (q + 1) = some s) (h2 : a (q + 2) = some ll)
    (h3 : a (q + 3) = some (mask32 wt))
    (hs : ∀ j < ll.toNat, a (s.toNat + j) = some (mask32 (f j))) :
    decCV a q = some ⟨decI wn, (List.range ll.toNat).map (fun j => decI (f j)), decI wt⟩ := by
  have h2' : a (q + 1 + 1) = some ll := h2
  simp [decCV, hlist?, nat?, hd?_mask h0, hd?_mask h3, h1, h2', hslice?_mask hs]

/-- **A constant value moved**: its four words copied, the slice read in an extension. -/
theorem decCV_move {a b : Nat → Option Word} {q cq : Nat} {cv : IConstantVal} (hext : ArrExt a b)
    (h0 : b q = a cq) (h1 : b (q + 1) = a (cq + 1)) (h2 : b (q + 2) = a (cq + 2))
    (h3 : b (q + 3) = a (cq + 3)) (h : decCV a cq = some cv) : decCV b q = some cv := by
  simp only [decCV, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h ⊢
  obtain ⟨nm, hn, lps, hl, ty, ht, e⟩ := h
  refine ⟨nm, ?_, lps, ?_, ty, ?_, e⟩
  · simp only [hd?, h0]; exact hn
  · simp only [hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hl ⊢
    obtain ⟨lo, hlo, ll, hll, hs⟩ := hl
    refine ⟨lo, ?_, ll, ?_, hext.hslice? hs⟩
    · simp only [nat?] at hlo ⊢; rw [h1]; exact hlo
    · simp only [nat?] at hll ⊢
      rw [show q + 1 + 1 = q + 2 from rfl, h2]; rw [show cq + 1 + 1 = cq + 2 from rfl] at hll
      exact hll
  · simp only [hd?, h3]; exact ht

theorem getElem?_rdW' {a : Array Word} {x : Word} {k : Nat} (hk : x.toNat = k) (h : k < a.size) :
    a[k]? = some (rdW a x) := by
  subst hk; simp [rdW, h]

theorem rdW_dw (D : Array Word) {i c : Word} {k : Nat} (hi : 8 * i.toNat + 9 < 2 ^ 64)
    (hc : c.toNat = k + 1) (hk : k < 8) : rdW D (c + 8 * i) = dw D i.toNat k := by
  have : (c + 8 * i).toNat = 1 + 8 * i.toNat + k := by
    rw [UInt64.toNat_add, UInt64.toNat_mul, hc, show (8 : Word).toNat = 8 from rfl]; omega
  simp only [rdW, dw, this]

/-! ### The pool below its top -/

/-- Below the tier-0 top (and below `2^40`, the tier bit clear), the record pool is `EREC`. -/
theorem erecP_getE {m : Mem} {j : Nat} (h : j < erTop m) (h40 : j < 2 ^ 40) :
    erecP m j = (m.arr64 EREC)[j]? := by
  have h64 : j < 2 ^ 64 := by omega
  have hd : j / 2 ^ 40 % 2 = 0 := by rw [Nat.div_eq_of_lt h40]
  have hm : j % 2 ^ 40 = j := Nat.mod_eq_of_lt h40
  simp only [erecP, h64, hd, hm, ite_true]
  rw [if_pos (by simpa [erecTop, erTop] using h)]

/-- A tier-0 address the record pool decodes is below the tier-0 top. -/
theorem erecP_lt {m : Mem} {j : Nat} {v : Word} (h : erecP m j = some v) (h40 : j < 2 ^ 40) :
    j < erTop m := by
  have hd : j / 2 ^ 40 % 2 = 0 := by rw [Nat.div_eq_of_lt h40]
  have hm : j % 2 ^ 40 = j := Nat.mod_eq_of_lt h40
  unfold erecP at h
  simp only [hd, hm, ite_true] at h
  split at h
  · split at h
    · rename_i hlt; simpa [erecTop, erTop] using hlt
    · cases h
  · cases h

theorem IWGrow.erecPExtR {m m' : Mem} (h : IWGrow m m') : ArrExt (erecP m) (erecP m') := h.ext

/-! ### Memories -/

theorem erAllocW_mem {m m1 : Mem} {k q : Word} (h : erAllocW m k = some (q, m1)) :
    m1 = erAllocMem m k := by
  unfold erAllocW at h
  split at h <;> grind

theorem erAllocMem_arr (m : Mem) (k : Word) {b : TieredArray} (hb : b ≠ ↑CTL) :
    (erAllocMem m k).arr64 b = m.arr64 b := by
  unfold erAllocMem; split <;> exact Mem.arr64_set64_ne _ _ _ _ _ hb

theorem wrER_arr (m : Mem) (q : Word) (ws : List Word) {b : TieredArray} (h1 : b ≠ ↑EREC)
    (h1' : b ≠ tier1 EREC) (h2 : b ≠ ↑CTL) :
    (wrER m q ws).arr64 b = m.arr64 b := (wrER_frame ws m q).1 b (by simp [h1, h1']) h2

/-- The words `dlp_copy` writes. -/
def dlpWords (P : Array Word) (s : Word) : Nat → List Word
  | 0 => []
  | k + 1 => mask32 (rdW P s) :: dlpWords P (s + 1) k

theorem dlpWords_length (P : Array Word) : ∀ (k : Nat) (s : Word), (dlpWords P s k).length = k
  | 0, _ => rfl
  | k + 1, s => by simp [dlpWords, dlpWords_length P k]

theorem dlpWords_get (P : Array Word) : ∀ (k : Nat) (s : Word) (j : Nat), j < k →
    s.toNat + k < 2 ^ 64 → (dlpWords P s k)[j]? = some (mask32 (P[s.toNat + j]?.getD 0))
  | 0, _, _, hj, _ => absurd hj (Nat.not_lt_zero _)
  | k + 1, s, 0, _, _ => by simp [dlpWords, rdW]
  | k + 1, s, j + 1, hj, hs => by
    have hs1 : (s + 1).toNat = s.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    simp only [dlpWords, List.getElem?_cons_succ]
    rw [dlpWords_get P k (s + 1) j (by omega) (by rw [hs1]; omega), hs1,
      show s.toNat + 1 + j = s.toNat + (j + 1) by omega]

theorem dlpCopyW_eq : ∀ (n : Nat) (m m' : Mem) (d s l : Word), dlpCopyW n m d s l = some m' →
    m' = wrER m d (dlpWords (m.arr64 DLP) s l.toNat)
  | 0, m, m', d, s, l, h => by simp [dlpCopyW] at h
  | n + 1, m, m', d, s, l, h => by
    by_cases hl : l = 0
    · rw [dlpCopyW_nil n m d s l hl] at h; cases h; subst hl; rfl
    · rw [dlpCopyW_step n m d s l hl] at h
      have hl1 : l.toNat = (l - 1).toNat + 1 := by
        have : l.toNat ≠ 0 := fun h0 => hl (UInt64.toNat_inj.mp (by simpa using h0))
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
      have hD : (erecPutMem m d (mask32 (rdW (m.arr64 DLP) s))).arr64 DLP = m.arr64 DLP := by
        rw [erecPutMem_arr, if_neg (by unfold erTier; split <;> decide)]
      rw [dlpCopyW_eq n _ m' _ _ _ h, hl1, hD]
      rfl

theorem eciMem_eq (m3 : Mem) (p i kind s ll : Word) :
    eciMem m3 p i kind s ll = wrER m3 p (eciWords (m3.arr64 DECL) i kind s ll) := by
  simp only [eciMem, eciWords, wrER, UInt64.add_assoc, UInt64.reduceAdd]

/-! ### `erec_vg` -/

/-! ### `env_push` -/

/-! ### `erec_ci` -/

theorem sliceL_map_decI {k : IdxKind} (P : Array Word) (o l : Nat) :
    (List.range l).map (fun j => (decI (P[o + j]?.getD 0) : Idx k)) = (sliceL P o l).map decI := by
  apply List.ext_getElem <;> simp [sliceL]

/-- **What `erec_ci(i, ck)` builds**, for any record kind: the stage relation kept, the pool
grown, the kind word `ck`, the record's constant value (whenever the declaration's record has
one, `CVAt`), its value word, its hint, all of it below the top. -/
theorem erecCiW_core {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {i ck : Word} {r : List Word} {ds : Array IDeclaration}
    (h : erecCiW n m i ck = some (r, m')) (hS : StageR vis fe m a)
    (hD : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds) (hi : i.toNat < ds.size) :
    StageR vis fe m' a ∧ IWGrow m m' ∧ nat? (erecP m') (r.headD 0).toNat = some ck.toNat ∧
      (∀ cv, CVAt (m.arr64 DECL) (m.arr64 DLP) i.toNat cv →
        decCV (erecP m') ((r.headD 0).toNat + 1) = some cv) ∧
      (hd? (erecP m') ((r.headD 0).toNat + 5) : Option EIdx) =
        some (decI (dw (m.arr64 DECL) i.toNat 5)) ∧
      decHint (erecP m') ((r.headD 0).toNat + 6) =
        some (hintW (dw (m.arr64 DECL) i.toNat 6) (dw (m.arr64 DECL) i.toNat 7)) ∧
      erOff (r.headD 0) + 8 ≤ erTopOf m' (r.headD 0) := by
  cases n with
  | zero => simp [erecCiW] at h
  | succ n =>
  have hdsz := hD.dsize
  have hroom := hD.room
  have hi8 : 8 * i.toNat + 9 < 2 ^ 64 := by omega
  rw [erecCiW_step, rdW_dw _ (c := 3) (k := 2) hi8 (by decide) (by decide),
    rdW_dw _ (c := 4) (k := 3) hi8 (by decide) (by decide)] at h
  cases h1 : erAllocW m (dw (m.arr64 DECL) i.toNat 3) with
  | none => rw [h1] at h; cases h
  | some x =>
  obtain ⟨s, m1⟩ := x
  rw [h1, eciK1_some] at h
  cases h2 : dlpCopyW n m1 s (1 + dw (m.arr64 DECL) i.toNat 2) (dw (m.arr64 DECL) i.toNat 3) with
  | none => rw [h2] at h; cases h
  | some m2 =>
  rw [h2, eciK2_some] at h
  cases h3 : erAllocW m2 8 with
  | none => rw [h3] at h; cases h
  | some x =>
  obtain ⟨p, m3⟩ := x
  rw [h3, eciK3_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have e2 := dlpCopyW_eq _ _ _ _ _ _ h2
  subst e2
  have hP1 : m1.arr64 DLP = m.arr64 DLP := by
    rw [erAllocW_mem h1]; exact erAllocMem_arr _ _ (by decide)
  have hD3 : m3.arr64 DECL = m.arr64 DECL := by
    rw [erAllocW_mem h3, erAllocMem_arr _ _ (by decide),
      wrER_arr _ _ _ (by decide) (by decide) (by decide),
      erAllocW_mem h1, erAllocMem_arr _ _ (by decide)]
  rw [hP1] at h3
  generalize hW1 : dlpWords (m.arr64 DLP) (1 + dw (m.arr64 DECL) i.toNat 2)
    (dw (m.arr64 DECL) i.toNat 3).toNat = ws1 at h3
  obtain ⟨hS2, hG2, -, -, -, -, hget1⟩ := erRec_stage h1 hS ws1 (by rw [← hW1, dlpWords_length])
  rw [eciMem_eq, hD3]
  have hws : eciWords (m.arr64 DECL) i ck s (dw (m.arr64 DECL) i.toNat 3) =
      [ck, mask32 (dw (m.arr64 DECL) i.toNat 1), s, dw (m.arr64 DECL) i.toNat 3,
       mask32 (dw (m.arr64 DECL) i.toNat 4), mask32 (dw (m.arr64 DECL) i.toNat 5),
       hintCode (dw (m.arr64 DECL) i.toNat 6), dw (m.arr64 DECL) i.toNat 7] := by
    simp only [eciWords]
    rw [rdW_dw _ (c := 2) (k := 1) hi8 (by decide) (by decide),
      rdW_dw _ (c := 5) (k := 4) hi8 (by decide) (by decide),
      rdW_dw _ (c := 6) (k := 5) hi8 (by decide) (by decide),
      rdW_dw _ (c := 7) (k := 6) hi8 (by decide) (by decide),
      rdW_dw _ (c := 8) (k := 7) hi8 (by decide) (by decide)]
  rw [hws]
  obtain ⟨hS', hG', hoff, htop', -, -, hget2⟩ := erRec_stage h3 hS2
    [ck, mask32 (dw (m.arr64 DECL) i.toNat 1), s, dw (m.arr64 DECL) i.toNat 3,
       mask32 (dw (m.arr64 DECL) i.toNat 4), mask32 (dw (m.arr64 DECL) i.toNat 5),
       hintCode (dw (m.arr64 DECL) i.toNat 6), dw (m.arr64 DECL) i.toNat 7] rfl
  generalize wrER m3 p _ = M at hS' hG' htop' hget2
  simp only [List.length_cons, List.length_nil] at htop' hget2
  have hl1 : ws1.length = (dw (m.arr64 DECL) i.toNat 3).toNat := by rw [← hW1, dlpWords_length]
  rw [hl1] at hget1
  have w0 : erecP M p.toNat = some ck := by simpa using hget2 0 (by decide)
  have w1 : erecP M (p.toNat + 1) = some (mask32 (dw (m.arr64 DECL) i.toNat 1)) := by
    simpa using hget2 1 (by decide)
  have w2 : erecP M (p.toNat + 1 + 1) = some s := by simpa using hget2 2 (by decide)
  have w3 : erecP M (p.toNat + 1 + 2) = some (dw (m.arr64 DECL) i.toNat 3) := by
    simpa using hget2 3 (by decide)
  have w4 : erecP M (p.toNat + 1 + 3) = some (mask32 (dw (m.arr64 DECL) i.toNat 4)) := by
    simpa using hget2 4 (by decide)
  have w5 : erecP M (p.toNat + 5) = some (mask32 (dw (m.arr64 DECL) i.toNat 5)) := by
    simpa using hget2 5 (by decide)
  have w6 : erecP M (p.toNat + 6) = some (hintCode (dw (m.arr64 DECL) i.toNat 6)) := by
    simpa using hget2 6 (by decide)
  have w7 : erecP M (p.toNat + 6 + 1) = some (dw (m.arr64 DECL) i.toNat 7) := by
    simpa using hget2 7 (by decide)
  have hcvG : ∀ cv, CVAt (m.arr64 DECL) (m.arr64 DLP) i.toNat cv →
      decCV (erecP M) (p.toNat + 1) = some cv := by
    intro cv hcv
    obtain ⟨hn, ht, hb, hl⟩ := hcv
    have hptop := hD.ptop
    have hpsz := hD.psize
    have hP0 := ((m.arr64 DLP)[0]?.getD 0).toNat_lt
    have hlo1 : (1 + dw (m.arr64 DECL) i.toNat 2).toNat = 1 + (dw (m.arr64 DECL) i.toNat 2).toNat := by
      rw [UInt64.toNat_add]; simp; omega
    have hsl : ∀ j < (dw (m.arr64 DECL) i.toNat 3).toNat, erecP M (s.toNat + j) =
        some (mask32 ((m.arr64 DLP)[1 + (dw (m.arr64 DECL) i.toNat 2).toNat + j]?.getD 0)) := by
      intro j hj
      refine hG'.ext _ _ ?_
      rw [hget1 j hj, ← hW1, dlpWords_get _ _ _ _ hj (by rw [hlo1]; omega), hlo1]
    rw [decCV_of_words w1 w2 w3 w4 hsl, sliceL_map_decI, hl, hn, ht]
  have hvM : (hd? (erecP M) (p.toNat + 5) : Option EIdx) =
      some (decI (dw (m.arr64 DECL) i.toNat 5)) := hd?_mask w5
  have hhint : decHint (erecP M) (p.toNat + 6) =
      some (hintW (dw (m.arr64 DECL) i.toNat 6) (dw (m.arr64 DECL) i.toNat 7)) := by
    unfold decHint hintW
    simp only [nat?, w6, w7, hintCode]
    by_cases e1 : dw (m.arr64 DECL) i.toNat 6 = 1
    · simp [e1]
    by_cases e2 : dw (m.arr64 DECL) i.toNat 6 = 2
    · simp [e2]
    · simp [e1, e2]
  have hk : nat? (erecP M) p.toNat = some ck.toNat := by simp [nat?, w0]
  simp only [List.headD_cons]
  exact ⟨hS', hG2.trans hG', hk, hcvG, hvM, hhint, by omega⟩

/-- **`erec_ci(i, ck)` builds the constant record of declaration `i`**: the stage relation kept,
the pool grown, the record decoding as the constant `installStepGo` pushes (`stepCI`), its
constant value at `q + 1`, its value at `q + 5`, all of it below the top. -/
theorem erecCiW_ok {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {i ck : Word} {r : List Word} {ds : Array IDeclaration}
    {ci : IConstantInfo}
    (h : erecCiW n m i ck = some (r, m')) (hS : StageR vis fe m a)
    (hD : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds) (hi : i.toNat < ds.size)
    (hci : stepCI ck.toNat ds[i.toNat] = some ci) :
    StageR vis fe m' a ∧ IWGrow m m' ∧ decCI (erecP m') (r.headD 0).toNat = some ci ∧
      decCV (erecP m') ((r.headD 0).toNat + 1) = some (stepCV ds[i.toNat]) ∧
      hd? (erecP m') ((r.headD 0).toNat + 5) = some (stepVal ds[i.toNat]) ∧
      erOff (r.headD 0) + 8 ≤ erTopOf m' (r.headD 0) := by
  obtain ⟨hS', hG', hk, hcvG, hvM, hhint, htop⟩ := erecCiW_core h hS hD hi
  have hdecl := hD.recs i.toNat hi
  generalize (r.headD 0).toNat = p at hk hcvG hvM hhint htop ⊢
  generalize ds[i.toNat] = d at hci hdecl ⊢
  generalize ck.toNat = c at hci hk
  refine ⟨hS', hG', ?_, ?_, ?_, htop⟩ <;>
    cases d <;> rcases c with _ | _ | _ | c <;> simp [stepCI] at hci <;> subst hci
  · obtain ⟨-, hcv, hv5, hh⟩ := hdecl
    simp [decCI, hk, hcvG _ hcv, hvM, hv5, hhint, hh]
  · obtain ⟨-, hcv, -⟩ := hdecl
    simp [decCI, hk, hcvG _ hcv]
  · obtain ⟨-, hcv, -⟩ := hdecl
    simp [decCI, hk, hcvG _ hcv]
  · exact hcvG _ hdecl.2.1
  · exact hcvG _ hdecl.2.1
  · exact hcvG _ hdecl.2.1
  · rw [hvM, hdecl.2.2.1]; rfl
  · rw [hvM, hdecl.2.2]; rfl
  · rw [hvM, hdecl.2.2]; rfl

/-- **`erec_ci(i, 0)` on an axiom or a quotient record** builds `axiomInfo cv` (the checkDecl
arms' constant record of those kinds). -/
theorem erecCiW_okA {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {i : Word} {r : List Word} {ds : Array IDeclaration}
    {cv : IConstantVal}
    (h : erecCiW n m i 0 = some (r, m')) (hS : StageR vis fe m a)
    (hD : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds) (hi : i.toNat < ds.size)
    (hcv : CVAt (m.arr64 DECL) (m.arr64 DLP) i.toNat cv) :
    StageR vis fe m' a ∧ IWGrow m m' ∧
      decCI (erecP m') (r.headD 0).toNat = some (.axiomInfo cv) ∧
      decCV (erecP m') ((r.headD 0).toNat + 1) = some cv ∧
      erOff (r.headD 0) + 8 ≤ erTopOf m' (r.headD 0) := by
  obtain ⟨hS', hG', hk, hcvG, -, -, htop⟩ := erecCiW_core h hS hD hi
  refine ⟨hS', hG', ?_, hcvG _ hcv, htop⟩
  have hk0 : nat? (erecP m') (r.headD 0).toNat = some 0 := by simpa using hk
  have hc1 := hcvG _ hcv
  generalize (r.headD 0).toNat = q at hk0 hc1 ⊢
  simp [decCI, hk0, hc1]

end L.Arena
