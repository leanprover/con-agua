module

public import ConRon.Bridge.Compare.Mates
public import ConRon.Bridge.Checker.Inv
import ConRon.Bridge.Checker.Basis

@[expose] public section

/-!
# The record mates denote, handle by handle (lane compare2, helper compare2-verdict)

con-ron's `MatesRel`/`MatesDen` (`Bridge/Compare/Mates.lean`, `Needs.lean`) say that the twin's
record mates cover con-leche's. The verdict of a compared run needs the other direction: every
handle the mates list denotes (`CvMatesDen`), so the cone walk, which puts a constant's mates on
its work list, only meets names that the twin's rejection message can read back (`readNameM`).
The mates of `solutionOf I ds` are the block-member names of `ds`'s inductive records
(`cvMatesDen_solutionOf`); each is persistent, so the fact survives every persistent extension of
the store (`CvMatesDen.pmono`).
-/

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena

/-- con-leche: none — **every handle the mates list is persistent and denotes**. -/
def CvMatesDen (st : EStore) (mates : Std.HashMap NIdx (List NIdx)) : Prop :=
  ∀ (n : NIdx) (ms : List NIdx), mates[n]? = some ms → ∀ h ∈ ms, PersN h ∧ ∃ nm, denoteN st.ns h = some nm

theorem CvMatesDen.pmono {st st' : EStore} {mates : Std.HashMap NIdx (List NIdx)}
    (h : CvMatesDen st mates) (hx : PExt st st') : CvMatesDen st' mates := by
  intro n ms hn k hk
  obtain ⟨hp, nm, hd⟩ := h n ms hn k hk
  exact ⟨hp, nm, denoteN_pext hx hp hd⟩

theorem CvMatesDen.ext {st st' : EStore} {mates : Std.HashMap NIdx (List NIdx)}
    (h : CvMatesDen st mates) (hx : Ext st st') : CvMatesDen st' mates := by
  intro n ms hn k hk
  obtain ⟨hp, nm, hd⟩ := h n ms hn k hk
  exact ⟨hp, nm, denoteN_ext hd hx⟩

theorem denoteNList_mem {st : NStore} :
    ∀ {hs : List NIdx} {L : List ConLeche.Name}, Frontend.denoteNList st hs = some L →
      ∀ h ∈ hs, ∃ nm, denoteN st h = some nm
  | [], _, _, _, hh => nomatch hh
  | h :: hs, L, e, k, hk => by
    simp only [Frontend.denoteNList] at e
    split at e
    · next x xs hx hxs =>
      rcases List.mem_cons.mp hk with rfl | hk
      · exact ⟨x, hx⟩
      · exact denoteNList_mem hxs k hk
    · exact nomatch e

theorem cvMatesDen_empty (st : EStore) : CvMatesDen st ∅ := by
  intro n ms hn; simp at hn

theorem cvMatesDen_matesInsert {st : EStore} {ns : List NIdx}
    (hns : ∀ h ∈ ns, PersN h ∧ ∃ nm, denoteN st.ns h = some nm) :
    ∀ (block : List IConstantInfo) (m : Std.HashMap NIdx (List NIdx)),
      CvMatesDen st m → CvMatesDen st (matesInsert m ns block) := by
  intro block
  induction block with
  | nil => intro m hm; exact hm
  | cons b bs ih =>
    intro m hm
    simp only [matesInsert]
    refine ih _ ?_
    have happ : nidxAppend (m.getD b.name []) ns 0 ns.length = m.getD b.name [] ++ ns := by
      simp [nidxAppend]
    rw [happ]
    intro n ms hn k hk
    rw [Std.HashMap.getElem?_insert] at hn
    split at hn
    · obtain rfl := Option.some.inj hn
      rcases List.mem_append.mp hk with hk | hk
      · cases hg : m[b.name]? with
        | none => rw [Std.HashMap.getD_eq_getD_getElem?, hg] at hk; exact nomatch hk
        | some ms₀ =>
          rw [Std.HashMap.getD_eq_getD_getElem?, hg] at hk
          exact hm _ ms₀ hg k hk
      · exact hns k hk
    · exact hm n ms hn k hk

theorem cvMatesDen_recordMatesGo {st : EStore} :
    ∀ (ds : List IDeclaration) (dsU : List Declaration) (m : Std.HashMap NIdx (List NIdx)),
      denoteDecls st ds = some dsU → (∀ x ∈ ds, PersDecl x) → CvMatesDen st m →
      CvMatesDen st (recordMatesGo m ds) := by
  intro ds
  induction ds with
  | nil => intro _ m _ _ hm; exact hm
  | cons d ds ih =>
    intro dsU m hd hp hm
    simp only [denoteDecls] at hd
    split at hd
    · next x xs hx hxs =>
      have hps : ∀ y ∈ ds, PersDecl y := fun y hy => hp y (List.mem_cons_of_mem _ hy)
      cases d with
      | indDecl block nP =>
        simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hx
        obtain ⟨bU, hbU, -⟩ := hx
        simp only [recordMatesGo]
        refine ih xs _ hxs hps (cvMatesDen_matesInsert (fun h hh => ?_) block m hm)
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hh
        have hpd := hp _ List.mem_cons_self
        refine ⟨PersCI.name (hpd b hb), denoteNList_mem (denoteCIList_names block bU hbU) _ ?_⟩
        exact List.mem_map.mpr ⟨b, hb, rfl⟩
      | axiomDecl v | defnDecl v e hh | thmDecl v e | opaqueDecl v e | quotDecl k v =>
        simp only [recordMatesGo]
        exact ih xs _ hxs hps hm
    · exact nomatch hd

/-- con-leche: ConLeche/Cached/Justify.lean:144-146 solutionOf — **the mates of the solution the
twin builds denote, handle by handle**. -/
theorem cvMatesDen_solutionOf {st : EStore} {I : IStreamIndex} {ds : List IDeclaration}
    {dsU : List Declaration} (hd : denoteDecls st ds = some dsU) (hp : ∀ x ∈ ds, PersDecl x) :
    CvMatesDen st (solutionOf I ds).mates :=
  cvMatesDen_recordMatesGo ds dsU ∅ hd hp (cvMatesDen_empty st)

end ConRon.Bridge
