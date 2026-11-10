module

public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConRon.Bridge.Grind
import ConAgua.L.ModelGen
import Std.Tactic.BVDecide.Normalize.BitVec
import all ConAgua.Arena.WhnfIota
public import ConAgua.Arena.WhnfIota

@[expose] public section

/-!
# ι-reduction: proofs of `WhnfIota.lean`'s specs, part 6 (`const_name_of`, record readers)

(ronsync2: `iota_case3`, `iota_ctor_never_prop`, `e_rec_get` and `ind_caps_check` left the twin and
the program with the sync; their models and refinements are deleted.)
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## The small L functions -/

l_model constNameOf_spec (p : Prog) (hp : p.lookup "const_name_of" = some constNameOfL)
  fns [hp ↦ cnoW ro]
  grind [arena_grind] fold [tierW, idxW]
  extra [evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  finish [tierW, idxW]

/-! ## The record of an inductive -/

theorem nat?_some {a : Array Word} {i k : Nat} (h : nat? (aread a) i = some k) :
    ∃ w, a[i]? = some w ∧ w.toNat = k := by
  simp only [nat?, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, hk⟩ := h
  exact ⟨w, hw, hk⟩

theorem nat?_of {a : Array Word} {i : Nat} {w : Word} (h : a[i]? = some w) : nat? (aread a) i = some w.toNat := by
  simp [nat?, h]

theorem hlist?_slice {a : Array Word} {i : Nat} {l : List NIdx} (h : hlist? (aread a) i = some l) :
    ∃ o c : Word, a[i]? = some o ∧ a[i+1]? = some c ∧ hslice? (aread a) o.toNat c.toNat = some l := by
  simp only [hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨o, ho, c, hc, hs⟩ := h
  obtain ⟨wo, hwo, rfl⟩ := nat?_some ho
  obtain ⟨wc, hwc, rfl⟩ := nat?_some hc
  exact ⟨wo, wc, hwo, hwc, hs⟩

/-! ## The head name of a `const` handle -/

theorem viewConstName_f (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hh : h.toNat < 2 ^ 32)
    (hv : viewOK m h CONST) (_hg : tagW h = 3) :
    a.store.viewConstName (decE h) = some (decI (tfld m CONST (tierW h) (idxW h) 0)) := by
  obtain ⟨k, hk, hn, hu⟩ := node_of m a h constCS CeRecRel (·.consts) _ hR.const hv.2
  have hfl := ConsR.flag hR.app
  have e : a.store.viewConstName (decE h) =
      ((if tierW h = 0 then a.store.pers else a.store.scr).consts.node? (idxW h).toNat).map
        (fun r => r.n) := by
    unfold EStore.viewConstName EStore.persGetConstName
    rw [decE_pers h hh]
    by_cases ht : tierW h = 0
    · simp [ht, ETables.getConstName, decE_idx h (narrow_of_cnt m h hR.const rfl hv.2)]
    · have hon : a.store.scratchOn = true := by
        rw [← hfl]; simp only [bne_iff_ne, ne_eq]; exact fun h1 => hv.1 ⟨ht, h1⟩
      simp [ht, hon, ETables.getConstName, decE_idx h (narrow_of_cnt m h hR.const rfl hv.2)]
  rw [e, Tbl.node?, hk]
  simp [hn, decI_word]


theorem viewConstName_run (a : AState) (h : EIdx) :
    (viewConstName h).run a = .ok (a.store.viewConstName h, a) := rfl

end L.Arena
