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
relational lemmas (`erecCiW_ok`, `erecVgW_ok`, `envPushW_ok`): from the stage relation a model
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
    else dlpCopyW n (m.set64 EREC d (mask32 (rdW (m.arr64 DLP) s))) (d + 1) (s + 1) (l - 1)

section arms
variable (n : Nat) (m : Mem) (d s l : Word)
theorem dlpCopyW_nil (hl : l = 0) : dlpCopyW (n + 1) m d s l = some m := by simp [dlpCopyW, hl]
theorem dlpCopyW_step (hl : l ≠ 0) :
    dlpCopyW (n + 1) m d s l =
      dlpCopyW n (m.set64 EREC d (mask32 (rdW (m.arr64 DLP) s))) (d + 1) (s + 1) (l - 1) := by
  simp [dlpCopyW, hl]
end arms

grind_pattern [ind_grind] dlpCopyW_nil => dlpCopyW (n + 1) m d s l
grind_pattern [ind_grind] dlpCopyW_step => dlpCopyW (n + 1) m d s l

theorem dlpCopy_specW (p : Prog) (hp : p.lookup "dlp_copy" = some dlpCopy) (n : Nat) :
    ∀ (s₀ : St) (d s l : Word),
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "dlp_copy" [d, s, l]
    ⦃fun _ s' => LocEq s' s₀ ∧ dlpCopyW n s₀.mem d s l = some s'.mem; ⊤⦄ := by
  sorry

/-- The hint word of a front hint kind `hq` (`1` abbrev, `2` opaque, else regular): `decHint`'s
`1`, `0`, `2`. -/
def hintCode (hq : Word) : Word := if hq = 1 then 1 else if hq = 2 then 0 else 2

/-- The eight words of the constant record, written at `p` of `m3` (`D` read in `m3`). -/
def eciMem (m3 : Mem) (p i kind s ll : Word) : Mem :=
  (((((((m3.set64 EREC p kind).set64 EREC (p + 1) (mask32 (rdW (m3.arr64 DECL) (2 + 8 * i)))).set64
    EREC (p + 2) s).set64 EREC (p + 3) ll).set64 EREC (p + 4)
    (mask32 (rdW (m3.arr64 DECL) (5 + 8 * i)))).set64 EREC (p + 5)
    (mask32 (rdW (m3.arr64 DECL) (6 + 8 * i)))).set64 EREC (p + 6)
    (hintCode (rdW (m3.arr64 DECL) (7 + 8 * i)))).set64 EREC (p + 7) (rdW (m3.arr64 DECL) (8 + 8 * i))

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

/-- One copied word of `erec_vg`: `EREC[g + j] := EREC[p + j]`. -/
def vgSet (m : Mem) (g p j : Word) : Mem := m.set64 EREC (g + j) (rdW (m.arr64 EREC) (p + j))

/-- The memory after `erec_vg`'s writes. -/
def vgMem (m1 : Mem) (g p vk : Word) : Mem :=
  vgSet (vgSet (vgSet (vgSet (vgSet (m1.set64 EREC g vk) g p 1) g p 2) g p 3) g p 4) g p 5

/-- **The model of `erec_vg(p, vk)`.** -/
def erecVgW (m : Mem) (p vk : Word) : Option (List Word × Mem) :=
  match erAllocW m 6 with
  | none => none
  | some (g, m1) => some ([g], vgMem m1 g p vk)

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
  sorry

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

theorem erecP_getE {m : Mem} {j : Nat} (h : j < erTop m) : erecP m j = (m.arr64 EREC)[j]? := by
  sorry

theorem erecP_lt {m : Mem} {j : Nat} {v : Word} (h : erecP m j = some v) : j < erTop m := by
  sorry

theorem IWGrow.erecPExtR {m m' : Mem} (h : IWGrow m m') : ArrExt (erecP m) (erecP m') := by
  intro j v hv
  have hj := erecP_lt hv
  rw [erecP_getE (by have := h.er; omega), h.erGet j hj, ← erecP_getE hj]
  exact hv

/-! ### Memories -/

theorem erAllocW_mem {m m1 : Mem} {k q : Word} (h : erAllocW m k = some (q, m1)) :
    m1 = erAllocMem m k := by
  simp only [erAllocW] at h
  split at h
  · cases h
  split at h
  · cases h
  cases h; rfl

theorem erAllocMem_arr (m : Mem) (k : Word) {b : TieredArray} (hb : b ≠ ↑CTL) :
    (erAllocMem m k).arr64 b = m.arr64 b := Mem.arr64_set64_ne _ _ _ _ _ hb

theorem wrER_arr (m : Mem) (q : Word) (ws : List Word) {b : TieredArray} (h1 : b ≠ ↑EREC) (h2 : b ≠ ↑CTL) :
    (wrER m q ws).arr64 b = m.arr64 b := (wrER_frame ws m q).1 b (by simp [h1]) h2

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
      rw [dlpCopyW_eq n _ m' _ _ _ h, hl1, Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
      rfl

/-- The constant record's words. -/
def eciWords (D : Array Word) (i kind s ll : Word) : List Word :=
  [kind, mask32 (rdW D (2 + 8 * i)), s, ll, mask32 (rdW D (5 + 8 * i)), mask32 (rdW D (6 + 8 * i)),
   hintCode (rdW D (7 + 8 * i)), rdW D (8 + 8 * i)]

theorem eciMem_eq (m3 : Mem) (p i kind s ll : Word) :
    eciMem m3 p i kind s ll = wrER m3 p (eciWords (m3.arr64 DECL) i kind s ll) := by
  simp only [eciMem, eciWords, wrER, UInt64.add_assoc, UInt64.reduceAdd]

theorem vgMem_eq (m1 : Mem) (g p vk : Word) (hp : p.toNat + 8 ≤ g.toNat)
    (hg : g.toNat + 6 < 2 ^ 64) :
    vgMem m1 g p vk = wrER m1 g [vk, rdW (m1.arr64 EREC) (p + 1), rdW (m1.arr64 EREC) (p + 2),
      rdW (m1.arr64 EREC) (p + 3), rdW (m1.arr64 EREC) (p + 4), rdW (m1.arr64 EREC) (p + 5)] := by
  have key : ∀ (M : Mem) (c j v : Word), c.toNat < 6 → j.toNat < 6 →
      rdW ((M.set64 EREC (g + c) v).arr64 EREC) (p + j) = rdW (M.arr64 EREC) (p + j) := by
    intro M c j v hc hj
    rw [rdW_set64, ite_eq_right]
    rintro ⟨-, he, -⟩
    have := congrArg UInt64.toNat he
    rw [UInt64.toNat_add, UInt64.toNat_add] at this
    have := g.toNat_lt; omega
  have key0 : ∀ (M : Mem) (j v : Word), j.toNat < 6 →
      rdW ((M.set64 EREC g v).arr64 EREC) (p + j) = rdW (M.arr64 EREC) (p + j) := by
    intro M j v hj
    rw [rdW_set64, ite_eq_right]
    rintro ⟨-, he, -⟩
    have := congrArg UInt64.toNat he
    rw [UInt64.toNat_add] at this
    have := g.toNat_lt; omega
  simp (disch := decide) only [vgMem, vgSet, wrER, key, key0, UInt64.add_assoc, UInt64.reduceAdd]


/-! ### `erec_vg` -/

/-! ### `env_push` -/

/-! ### `erec_ci` -/

theorem sliceL_map_decI {k : IdxKind} (P : Array Word) (o l : Nat) :
    (List.range l).map (fun j => (decI (P[o + j]?.getD 0) : Idx k)) = (sliceL P o l).map decI := by
  apply List.ext_getElem <;> simp [sliceL]

/-- **What `erec_ci(i, ck)` builds**, for any record kind: the stage relation kept, the pool
grown, the kind word `ck`, the record's constant value (whenever the declaration's record has
one, `CVAt`), its value word, its hint, all of it below the top. -/
theorem erecCiW_core {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
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
      (r.headD 0).toNat + 8 ≤ erTop m' := by
  sorry

/-- **`erec_ci(i, ck)` builds the constant record of declaration `i`**: the stage relation kept,
the pool grown, the record decoding as the constant `installStepGo` pushes (`stepCI`), its
constant value at `q + 1`, its value at `q + 5`, all of it below the top. -/
theorem erecCiW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {i ck : Word} {r : List Word} {ds : Array IDeclaration}
    {ci : IConstantInfo}
    (h : erecCiW n m i ck = some (r, m')) (hS : StageR vis fe m a)
    (hD : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds) (hi : i.toNat < ds.size)
    (hci : stepCI ck.toNat ds[i.toNat] = some ci) :
    StageR vis fe m' a ∧ IWGrow m m' ∧ decCI (erecP m') (r.headD 0).toNat = some ci ∧
      decCV (erecP m') ((r.headD 0).toNat + 1) = some (stepCV ds[i.toNat]) ∧
      hd? (erecP m') ((r.headD 0).toNat + 5) = some (stepVal ds[i.toNat]) ∧
      (r.headD 0).toNat + 8 ≤ erTop m' := by
  sorry

/-- **`erec_ci(i, 0)` on an axiom or a quotient record** builds `axiomInfo cv` (the checkDecl
arms' constant record of those kinds). -/
theorem erecCiW_okA {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {i : Word} {r : List Word} {ds : Array IDeclaration}
    {cv : IConstantVal}
    (h : erecCiW n m i 0 = some (r, m')) (hS : StageR vis fe m a)
    (hD : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds) (hi : i.toNat < ds.size)
    (hcv : CVAt (m.arr64 DECL) (m.arr64 DLP) i.toNat cv) :
    StageR vis fe m' a ∧ IWGrow m m' ∧
      decCI (erecP m') (r.headD 0).toNat = some (.axiomInfo cv) ∧
      decCV (erecP m') ((r.headD 0).toNat + 1) = some cv ∧
      (r.headD 0).toNat + 8 ≤ erTop m' := by
  sorry

end L.Arena
