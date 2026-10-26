import ConAgua.Arena.PromoteCIRef10

/-!
# `erec_alloc` as a relation; `promote_proj_table` refines `promoteProjTable`
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

theorem decTbl_move {a b : Array Word} {q d : Nat} {tbl : IProjTable} {sn c : NIdx} {ss : LIdx}
    {lp : List NIdx} {gs : List LIdx} {bs : List EIdx}
    (hA : decTbl a q = some tbl)
    (hw5 : b[d + 5]? = a[q + 5]?) (hw7 : b[d + 7]? = a[q + 7]?)
    (hsn : hd? b (d + 2) = some sn)
    (hlp : hlist? b (d + 3) = some lp) (hc : hd? b (d + 6) = some c)
    (hss : hd? b (d + 8) = some ss) (hbs : hlist? b (d + 9) = some bs)
    (hgs : hlist? b (d + 11) = some gs) :
    decTbl b d = some ⟨sn, lp, tbl.numParams, c, tbl.numFields, ss, bs.toArray, gs⟩ := by
  unfold decTbl at hA ⊢
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hA ⊢
  obtain ⟨e2, h2, e3, h3, e4, h4, e5, h5, e6, h6, e7, h7, e8, h8, e9, h9, rfl⟩ := hA
  exact ⟨sn, hsn, lp, hlp, e4, nat?_move hw5 h4, c, hc, e6, nat?_move hw7 h6, ss, hss,
    bs, hbs, gs, hgs, rfl⟩

theorem pmDecTbl_words {a : Array Word} {q : Nat} {tbl : IProjTable} (h : decTbl a q = some tbl) :
    hd? a (q + 2) = some tbl.structName ∧
    hlist? a (q + 3) = some tbl.levelParams ∧ hd? a (q + 6) = some tbl.ctor ∧
    hd? a (q + 8) = some tbl.structSort ∧ hlist? a (q + 9) = some tbl.bodies.toList ∧
    hlist? a (q + 11) = some tbl.guards := by
  unfold decTbl at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨e2, h2, e3, h3, e4, h4, e5, h5, e6, h6, e7, h7, e8, h8, e9, h9, rfl⟩ := h
  exact ⟨h2, h3, h5, h7, by simpa using h8, h9⟩

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

/-- **`erec_alloc(k)`**: the old top is returned, the top raised; the rest is untouched. -/
theorem alloc_rel {n : Nat} {k : Word} {m m' : Mem} {r : List Word}
    (hc : callW p (n + 1) "erec_alloc" [k] m = some (r, m')) :
    (r.headD 0).toNat = erecTop m ∧ erecTop m' = erecTop m + k.toNat ∧
    erecTop m + k.toNat ≤ (m.arr64 EREC).size ∧ MemFrame [] [129] m m' ∧
    m'.arr64 EREC = m.arr64 EREC := by
  obtain ⟨s₁, hs₁, -, hW₁⟩ := callW_triple (erecAlloc_spec p (hp.get "erec_alloc") n ⟨m, Locals.init []⟩ k) hc
  rw [hs₁] at hW₁
  obtain ⟨hdq, rfl, hd6, hroom, hctl⟩ := erAlloc_facts hW₁
  have hdv : (r.headD 0).toNat = erecTop m := by rw [hdq]; rfl
  refine ⟨hdv, ?_, by have h := hroom; simp only at h; omega, MemFrame.setCtl m 129 _, Mem.arr64_set64_ne _ _ _ _ _ (by decide)⟩
  simp only [erecTop]
  rw [rdW_set64, ite_eq_left ⟨rfl, rfl, by simpa using hctl⟩, hd6, hdv]; rfl

end rel

end L.Arena
