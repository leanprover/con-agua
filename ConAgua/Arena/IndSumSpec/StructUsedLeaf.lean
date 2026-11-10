module

public import ConAgua.Arena.LoopT
public import ConAgua.Arena.IndSumSpec.StructUsedHb
import ConAgua.Arena.CrOKFrame
public import ConAgua.Arena.IndPosSpec.NestCrest
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.IndSum
import all ConAgua.Arena.StripTele
import all ConAgua.Arena.IndIface
import all ConAgua.Arena.BvarB
import all ConAgua.Arena.ExprMk
import all ConAgua.Arena.Walk
import all ConAgua.Arena.MemoLib

@[expose] public section

/-!
# `struct_used_later` as a leaf: it keeps the inductive memos

`struct_used_later` is reached from the core (the twin's `infer_proj`), so the write-set checks of
`imFns` (and of the core stage) stop at it as a *leaf*; its own lemma says what it does to memory,
at any arguments and fuel: its call closure writes only `IW`, `HBM`, `BMEMO` and their control
words (`usP_closed`), and it keeps the `hb` memo well formed (`ustW_keep`, `StructUsedHb.lean`),
so `IndMemos` survives (`indMemos_ustW`, `indMemos_usLeaf`), which discharges `IndLeaves` for
`struct_used_later`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `IndMemos` across `struct_used_later` -/

/-- **`IndMemos` across a run of `struct_used_later`'s model** with its write set. -/
theorem indMemos_ustW {n : Nat} {m m' : Mem} {cty nP j r : Word} (h : ustW n m cty nP j = some (r, m'))
    (hf : MemFrame usA usC m m') (hI : IndMemos m) : IndMemos m' := by
  obtain ⟨⟨hp, ⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩, hi1, hcr⟩ := hI
  exact ⟨⟨hp.setHb (ustW_mfr h) (ustW_keep h hp.hb),
    ⟨a, memoRG_frame _ maSch_wf _ _ usA usC (by decide) (by decide) m m' hf a ha⟩,
    ⟨b, memoRG_frame _ mcSch_wf _ _ usA usC (by decide) (by decide) m m' hf b hb⟩,
    ⟨c, memoRG_frame _ taSch_wf _ _ usA usC (by decide) (by decide) m m' hf c hc⟩⟩,
    I1Memo.frame hi1 hf (by decide) (by decide), L.Arena.CrOK.frame hcr hf (by decide) (by decide)⟩

/-- **`struct_used_later` keeps `IndMemos`**, at any arguments and fuel: the leaf lemma that
`IndLeaves` asks of it. -/
theorem indMemos_usLeaf {p : Prog} (hp : UsF p) (n : Nat) (m₀ : Mem) (vs : List Word) :
    ⦃fun s => IndMemos m₀ → IndMemos s.mem⦄ invoke p (exec p n) "struct_used_later" vs
    ⦃fun _ s => IndMemos m₀ → IndMemos s.mem; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨-, hc⟩ := M.of_run (P := fun t => t = s) rfl hrun (callW_spec p n "struct_used_later" vs s)
  have hfr := (run_memFrame hp.closed (by decide) (run_of_callW hc)).1
  obtain ⟨s'', hm, -, hu⟩ := triple_of_callW (s₀ := ⟨s.mem, Locals.init []⟩)
    (structUsedLater_specV hp n _ vs) (callW_mono hc (Nat.le_add_right n 2))
  rw [hm] at hu
  exact fun h0 => indMemos_ustW hu hfr (hs h0)

end L.Ind

end
