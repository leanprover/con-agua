module

public import ConAgua.Compiler.SimFun
public import ConAgua.Compiler.SimStore

@[expose] public section

/-!
# The compiler is correct

`execSim_all`: for a well-formed program, every statement simulates `exec p n` and every
function simulates its calls, for every fuel `n` (induction on `n`, then on the statement).
-/

namespace L.Compiler

open L

theorem code_of_lookup [Host] {tab : Tab} {f : FnName} {fd : FunDecl} :
    ∀ (p : Prog) (k : Nat), Code (p.flatMap fun (f, fd) => compileFn tab f fd) k → p.lookup f = some fd →
    ∃ kf, Code (compileFn tab f fd) kf := by
  intro p
  induction p with
  | nil => intro k _ h; simp at h
  | cons q p ih =>
    obtain ⟨f', fd'⟩ := q
    intro k hc hl
    simp only [List.flatMap_cons] at hc
    simp only [List.lookup_cons] at hl
    split at hl
    · rename_i heq
      cases hl
      have : f = f' := by simpa using heq
      subst this
      exact ⟨k, hc.left⟩
    · exact ih _ hc.right hl

section
variable [Host] {G : Layout} (hG : G.Ok) (hTab : 16 + 16 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords + 8 * G.tab.nxres + 8 * G.tab.ng < maxOff) (p : Prog)
include hG hTab

theorem stepSim (hProg : ∀ f fd, p.lookup f = some fd → ∃ kf, Code (compileFn G.tab f fd) kf)
    (n : Nat) (hE : ExecSim p G n) (hF : FunSim p G n) : StepSim p G n := by
  have hPm : ∀ a b, a ≤ b → b ≤ n → a ≤ n := fun a b h1 h2 => Nat.le_trans h1 h2
  intro s
  induction s with
  | skip => exact sim_skip p _ _
  | set x e => exact sim_set hG hTab p _ _ x e
  | st8 a i e => exact sim_st8 hG hTab p _ _ a i e
  | st64 a i e => exact sim_st64 hG hTab p _ _ a i e
  | seq s t ihs iht => exact sim_seq p _ _ hPm s t ihs iht
  | ite c s t ihs iht => exact sim_ite hG hTab p _ _ c s t ihs iht
  | «while» c s ih => exact sim_while hG hTab p n hE c s ih
  | brk => exact sim_brk p _ _
  | ret e => exact sim_ret hG hTab p _ _ e
  | call x f args => exact sim_call hG hTab p n hF hProg x f args
  | abort => exact sim_abort p _ _
  | gset g e => exact sim_gset hG hTab p _ _ g e

theorem execSim_all (hwfp : ∀ f fd, p.lookup f = some fd → FunDecl.wf p G.tab fd = true)
    (hProg : ∀ f fd, p.lookup f = some fd → ∃ kf, Code (compileFn G.tab f fd) kf) :
    ∀ n, ExecSim p G n ∧ FunSim p G n := by
  intro n
  induction n with
  | zero => exact ⟨execSim_zero p G, funSim hG hTab p hwfp 0 (execSim_zero p G)⟩
  | succ n ih =>
    have hE := execSim_succ (stepSim hG hTab p hProg n ih.1 ih.2)
    exact ⟨hE, funSim hG hTab p hwfp (n + 1) hE⟩

end

end L.Compiler
