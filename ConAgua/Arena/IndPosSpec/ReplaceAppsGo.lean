import ConAgua.Arena.IndPosSpec.RpGoStep

/-!
# ReplaceAppsGo: `ConRon.Arena.appHole`, `ConRon.Arena.replaceAppsGo`, `ConRon.Arena.replaceApps`

The refinement theorems `appHole_refines`, `replaceAppsGo_refines`, `replaceApps_refines` and the lemmas only they use.
-/


noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

section census
variable (p : Prog) (hv : p.lookup "e_view" = some eView) (hph : p.lookup "ph_app" = some phApp)
  (hf : p.lookup "sl_find" = some slFind) (hpw : p.lookup "pin_word" = some pinWordL)
  (hsf : p.lookup "sort_find" = some sortFind) (hsp : p.lookup "sort_push" = some sortPush)
  (his : p.lookup "intern_sort" = some internSort)
  (hff : p.lookup "fvar_find" = some fvarFind) (hfp : p.lookup "fvar_push" = some fvarPush)
  (hif : p.lookup "intern_fvar" = some internFVar)
  (hcs : p.lookup "nest_canon_sub" = some nestCanonSub)
  (hp : p.lookup "app_hole" = some appHole)
include hv hph hf hpw hsf hsp his hff hfp hif hcs hp

/-- **`app_hole` refines `appHole?`**. -/
@[refines ConRon.Arena.appHole?]
theorem appHole_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis no nl us b nn e : Word) (N : Nat) (names : List NIdx) (hN : nn.toNat = N)
    (he : H e) (hus : H us) (hb : b.toNat + N < 2 ^ 64) (hS : StageR dn vis fe s₀.mem a₀)
    (hdec : decHL s₀.mem no.toNat nl.toNat = some names) (hno : no.toNat + nl.toNat < 2 ^ 64)
    (hnn : nn.toNat + names.length < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "app_hole" [no, nl, us, b, nn, e]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.appHole? names (decI us) b.toNat N (decI e)) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.appHole? names (decI us) b.toNat N (decI e)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      decOE s'.mem r (AM.res (ConRon.Arena.appHole? names (decI us) b.toNat N (decI e)) a₀); ⊤⦄ := by
  refine triple_post (appHole_spec p hv hph hf hpw hsf hsp his hff hfp hif hcs hp (n + 1) s₀ no nl us b nn e) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hS', hg, hout⟩ := ahW_ok n dn fe vis _ _ a₀ no nl us b nn e N names r hm hS hN he hus hb
    hdec hno hnn
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, by rw [hres]; exact hout⟩

end census

section census
variable (p : Prog) (hl : AhLook p) (hk : MkLook p)
  (hf : p.lookup "ra_find" = some (memoFindG raSch)) (hput : p.lookup "ra_put" = some (memoPutG raSch))
  (hgo : p.lookup "replace_apps_go" = some replaceAppsGo)
  (hnode : p.lookup "replace_apps_node" = some replaceAppsNode)
include hl hk hf hput hgo hnode

/-- **`replace_apps_go` (with `replace_apps_node`) refines `replaceAppsGo`**, from a memo related to
the twin's. -/
@[refines ConRon.Arena.replaceAppsGo]
theorem replaceAppsGo_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis no nl us b nn f h : Word) (N : Nat) (names : List NIdx)
    (mp : Std.HashMap EIdx EIdx) (hh : H h) (hus : H us) (hS : StageR dn vis fe s₀.mem a₀)
    (hdec : decHL s₀.mem no.toNat nl.toNat = some names) (hno : no.toNat + nl.toNat < 2 ^ 64)
    (hit : no.toNat + nl.toNat ≤ iwTop s₀.mem) (hN : nn.toNat = N)
    (hnn : nn.toNat + names.length < 2 ^ 64) (hbN : b.toNat + N < 2 ^ 64) (hM : rpMR s₀.mem mp) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "replace_apps_go" [no, nl, us, b, nn, f, h]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.replaceAppsGo names (decI us) b.toNat N mp f.toNat (decE h)) a₀ ∧
      decE (r.headD 0) =
        (AM.res (ConRon.Arena.replaceAppsGo names (decI us) b.toNat N mp f.toNat (decE h)) a₀).1 ∧
      rpMR s'.mem
        (AM.res (ConRon.Arena.replaceAppsGo names (decI us) b.toNat N mp f.toNat (decE h)) a₀).2 ∧
      StageR dn vis fe s'.mem
        (AM.st (ConRon.Arena.replaceAppsGo names (decI us) b.toNat N mp f.toNat (decE h)) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post ((rpGo_spec p hl hk hf hput hgo hnode n).1 s₀ no nl us b nn f h) ?_
  rintro r s' ⟨hlc, hm⟩
  obtain ⟨a', mp', hrun, hS', hg, hM'⟩ := rpGoOK dn fe vis n _ _ a₀ no nl us b nn f h _ N names mp hm hS hh hus hdec
    hno hit hN hnn hbN hM
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hlc, hok, by rw [hres], by rw [hres]; exact hM', by rw [hst]; exact hS', hg⟩

end census

section census2
variable (p : Prog) (hl : AhLook p) (hk : MkLook p)
  (hf : p.lookup "ra_find" = some (memoFindG raSch)) (hput : p.lookup "ra_put" = some (memoPutG raSch))
  (hgo : p.lookup "replace_apps_go" = some replaceAppsGo)
  (hnode : p.lookup "replace_apps_node" = some replaceAppsNode)
  (hcl : p.lookup "ra_clear" = some (memoClearG raSch))
  (hp : p.lookup "replace_apps" = some replaceApps)
include hl hk hf hput hgo hnode hcl hp

/-- **`replace_apps` refines `replaceApps`**: one memoised DAG walk between two clears. -/
@[refines ConRon.Arena.replaceApps]
theorem replaceApps_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis no nl us b nn e : Word) (N : Nat) (names : List NIdx)
    (mp0 : Std.HashMap EIdx EIdx) (he : H e) (hus : H us) (hS : StageR dn vis fe s₀.mem a₀)
    (hdec : decHL s₀.mem no.toNat nl.toNat = some names) (hno : no.toNat + nl.toNat < 2 ^ 64)
    (hit : no.toNat + nl.toNat ≤ iwTop s₀.mem) (hN : nn.toNat = N)
    (hnn : nn.toNat + names.length < 2 ^ 64) (hbN : b.toNat + N < 2 ^ 64) (hM : rpMR s₀.mem mp0) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "replace_apps" [no, nl, us, b, nn, e]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.replaceApps names (decI us) b.toNat N (decE e)) a₀ ∧
      decE (r.headD 0) = AM.res (ConRon.Arena.replaceApps names (decI us) b.toNat N (decE e)) a₀ ∧
      rpMR s'.mem ∅ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.replaceApps names (decI us) b.toNat N (decE e)) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (replaceApps_spec p hl hk hf hput hgo hnode hcl hp n s₀ no nl us b nn e) ?_
  rintro r s' ⟨hlc, hm⟩
  obtain ⟨a', hrun, hM', hS', hg⟩ := rpConstW_ok n dn fe vis _ _ a₀ no nl us b nn e _ N names mp0 hm hS he hus hdec hno
    hit hN hnn hbN hM
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hlc, hok, by rw [hres], hM', by rw [hst]; exact hS', hg⟩

end census2

end L.Ind

end
