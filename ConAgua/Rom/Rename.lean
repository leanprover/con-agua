module

public import ConAgua.Rom.CIConst
public import ConAgua.L.Logic
public import ConAgua.L.ProgHas

@[expose] public section

/-!
# The renaming lemma (lane `ronsync2`)

A function whose calls are renamed by `ρ` runs, in a program `p` that binds each renamed name to
the renamed body, exactly as the original runs in a program `q` that binds the original names to
the original bodies: `invoke p k' (ρ g) = invoke q k g` for every name `g` of a set `N` that `q`
binds and that is closed under `q`'s calls (`invoke_renameCalls`, `triple_renameCalls`). The ROM
readers' copies over the constant data (`CIConst.lean`) are the instance `ρ = romC`.
-/

namespace L

open Std.WP
open scoped Lean.Order

/-- The functions a statement calls. -/
def Stmt.calls : Stmt → List FnName
  | .seq s t => s.calls ++ t.calls
  | .ite _ s t => s.calls ++ t.calls
  | .while _ s => s.calls
  | .call _ f _ => [f]
  | _ => []

section rename
variable {ρ : FnName → FnName} {p q : Prog} {N : List FnName}

/-- **The renaming hypotheses**: every name of `N` is bound in `q`, its body calls names of `N`
only, and `p` binds its renamed name to the renamed body. -/
structure RenameOK (ρ : FnName → FnName) (p q : Prog) (N : List FnName) : Prop where
  bound : ∀ g ∈ N, (q.lookup g).isSome = true
  closed : ∀ g ∈ N, ∀ fd, q.lookup g = some fd → ∀ h ∈ fd.body.calls, h ∈ N
  lookup : ∀ g ∈ N, p.lookup (ρ g) = (q.lookup g).map (FunDecl.renameCalls ρ)

theorem invoke_renameCalls (h : RenameOK ρ p q N) {k k' : Stmt → M Sig}
    (hk : ∀ st : Stmt, (∀ f ∈ st.calls, f ∈ N) → k' (st.renameCalls ρ) = k st) {g : FnName}
    (hg : g ∈ N) (vs : List Word) : invoke p k' (ρ g) vs = invoke q k g vs := by
  obtain ⟨fd, hfd⟩ := Option.isSome_iff_exists.mp (h.bound g hg)
  have hp : p.lookup (ρ g) = some (fd.renameCalls ρ) := by rw [h.lookup g hg, hfd]; rfl
  simp only [invoke, lookupFn, hp, hfd, pure_bind, callFn, FunDecl.renameCalls]
  rw [hk fd.body (h.closed g hg fd hfd)]

theorem step_renameCalls (h : RenameOK ρ p q N) {k k' : Stmt → M Sig}
    (hk : ∀ st : Stmt, (∀ f ∈ st.calls, f ∈ N) → k' (st.renameCalls ρ) = k st) :
    ∀ st : Stmt, (∀ f ∈ st.calls, f ∈ N) → step p k' (st.renameCalls ρ) = step q k st := by
  intro st hst
  induction st with
  | seq s t ihs iht =>
    simp only [Stmt.calls, List.mem_append] at hst
    simp only [Stmt.renameCalls, step]
    rw [ihs (fun f hf => hst f (.inl hf)), iht (fun f hf => hst f (.inr hf))]
  | ite c s t ihs iht =>
    simp only [Stmt.calls, List.mem_append] at hst
    simp only [Stmt.renameCalls, step]
    rw [ihs (fun f hf => hst f (.inl hf)), iht (fun f hf => hst f (.inr hf))]
  | «while» c s ih =>
    simp only [Stmt.calls] at hst
    have e : k' (.while c (s.renameCalls ρ)) = k (.while c s) := hk (.while c s) hst
    simp only [Stmt.renameCalls, step]
    rw [ih hst, e]
  | «call» xs f args =>
    simp only [Stmt.calls, List.mem_singleton, forall_eq] at hst
    simp only [Stmt.renameCalls, step]
    simp only [invoke_renameCalls h hk hst]
  | _ => rfl

theorem exec_renameCalls (h : RenameOK ρ p q N) (n : Nat) :
    ∀ st : Stmt, (∀ f ∈ st.calls, f ∈ N) → exec p n (st.renameCalls ρ) = exec q n st := by
  induction n with
  | zero => intro _ _; rfl
  | succ n ih => exact step_renameCalls h ih

/-- A statement none of whose calls `ρ` moves is its own renaming. -/
theorem Stmt.renameCalls_of_calls {ρ : FnName → FnName} :
    ∀ s : Stmt, (∀ f ∈ s.calls, ρ f = f) → s.renameCalls ρ = s
  | .seq s t, h => by
    simp only [Stmt.calls, List.mem_append] at h
    simp only [Stmt.renameCalls, Stmt.renameCalls_of_calls s (fun f hf => h f (.inl hf)),
      Stmt.renameCalls_of_calls t (fun f hf => h f (.inr hf))]
  | .ite c s t, h => by
    simp only [Stmt.calls, List.mem_append] at h
    simp only [Stmt.renameCalls, Stmt.renameCalls_of_calls s (fun f hf => h f (.inl hf)),
      Stmt.renameCalls_of_calls t (fun f hf => h f (.inr hf))]
  | .while c s, h => by
    simp only [Stmt.calls] at h
    simp only [Stmt.renameCalls, Stmt.renameCalls_of_calls s h]
  | .call xs f args, h => by
    simp only [Stmt.calls, List.mem_singleton, forall_eq] at h
    simp only [Stmt.renameCalls, h]
  | .skip, _ | .set .., _ | .st8 .., _ | .st64 .., _ | .brk, _ | .ret .., _ | .abort .., _
  | .gset .., _ | .st64t .., _ | .copy64 .., _ | .copy8w .., _ | .scan8 .., _ | .st32t .., _ => rfl

/-- **`RenameOK` from tables**: `T` binds the names of `N` (`q` has `T`), its bodies call names of
`N` only, and `p` binds each renamed name to the renamed body. -/
theorem RenameOK.of_tab (T : Prog) (hN : ∀ g ∈ N, (T.lookup g).isSome = true) (hq : ProgHas q T)
    (hc : ∀ g ∈ N, ∀ B, T.lookup g = some B → ∀ h ∈ B.body.calls, h ∈ N)
    (hp : ∀ g ∈ N, ∀ B, T.lookup g = some B → p.lookup (ρ g) = some (B.renameCalls ρ)) :
    RenameOK ρ p q N := by
  refine ⟨fun g hg => ?_, fun g hg fd hfd => ?_, fun g hg => ?_⟩
  · obtain ⟨B, hB⟩ := Option.isSome_iff_exists.mp (hN g hg)
    rw [hq g B hB]; rfl
  · obtain ⟨B, hB⟩ := Option.isSome_iff_exists.mp (hN g hg)
    rw [hq g B hB] at hfd; cases hfd; exact hc g hg _ hB
  · obtain ⟨B, hB⟩ := Option.isSome_iff_exists.mp (hN g hg)
    rw [hp g hg B hB, hq g B hB]; rfl

/-- Triple transfer: a spec of the original is a spec of the renamed function. -/
theorem triple_renameCalls (h : RenameOK ρ p q N) {n : Nat} {g : FnName} (hg : g ∈ N)
    {vs : List Word} {P : St → Prop} {Q : List Word → St → Prop}
    (ht : ⦃fun s => P s⦄ invoke q (exec q n) g vs ⦃fun r s' => Q r s'; ⊤⦄) :
    ⦃fun s => P s⦄ invoke p (exec p n) (ρ g) vs ⦃fun r s' => Q r s'; ⊤⦄ := by
  rw [invoke_renameCalls h (exec_renameCalls h n) hg vs]; exact ht

end rename

end L
