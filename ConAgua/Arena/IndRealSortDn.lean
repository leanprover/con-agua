import ConAgua.Arena.IndRealCapsC

/-!
# `SortDn` of member 0's former sort (lane `indproofs4`, helper `sdn`)

`LzFacts.of_stageC` (`IndRealCapsC.lean`) needs `SortDn dn pP.resSort`, where `pP` is the twin's
shape completed with member 0's former sort `s0P` (`BlockShape.withSort`, so `pP.resSort = s0P`).
`s0P` is what con-leche's `checkBlockTele` answers: by `checkBlockTele_shape` it is the result sort
of a constant record that passed `checkConstantVal`, with member 0's level parameters, so every
level parameter of `s0P` is one of them (`allLevelParamsDefined`); the zero-ness datum's names are
level parameters of the level (`zeronessOf_paramsDefined`). So `SortDn` holds as soon as member
0's level-parameter NAMES have `dn` handles.

* `sortDn_of_lps`: from the level parameters' names (`∀ x ∈ lps, ∃ k, dn k = some x`).
* `sortDn_of_checkBlockTele`: from con-leche's `checkBlockTele` succeeding (the `FOk` that
  `checkBlockTele_specF` returns) and member 0's level-parameter names having `dn` handles.
* `sortDn_of_member`: the same with the premise on member 0's HANDLES (`ms.cvT.levelParams`, every
  one with a `dn` name), via the member's denotation and `dn`'s agreement with the name store.
-/

namespace L.Ind

open ConLeche

theorem denoteNList_mem {st : ConRon.Arena.NStore} :
    ∀ {l : List ConRon.Arena.NIdx} {xs : List Name}, ConRon.Arena.Frontend.denoteNList st l = some xs →
      ∀ x ∈ xs, ∃ k ∈ l, ConRon.Arena.denoteN st k = some x
  | [], xs, h, x, hx => by
    simp only [ConRon.Arena.Frontend.denoteNList, Option.some.injEq] at h
    subst h; simp at hx
  | c :: cs, xs, h, x, hx => by
    simp only [ConRon.Arena.Frontend.denoteNList] at h
    split at h
    · rename_i y ys h1 h2
      simp only [Option.some.injEq] at h
      subst h
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨c, List.mem_cons_self .., h1⟩
      · obtain ⟨k, hk, hk'⟩ := denoteNList_mem h2 x hx
        exact ⟨k, List.mem_cons_of_mem _ hk, hk'⟩
    · cases h

theorem allLevelParamsDefined_stripPis {ps : List Name} :
    ∀ (n : Nat) {e : ConLeche.Expr} {bs : List ConLeche.Expr} {b : ConLeche.Expr}, e.allLevelParamsDefined ps = true →
      e.stripPis n = some (bs, b) → b.allLevelParamsDefined ps = true
  | 0, e, bs, b, h, hs => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨-, rfl⟩ := hs; exact h
  | n + 1, e, bs, b, h, hs => by
    cases e with
    | forallE ty body =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at hs
      obtain ⟨⟨bs', b'⟩, hs', he⟩ := hs
      simp only [Prod.mk.injEq] at he
      obtain ⟨-, rfl⟩ := he
      simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
      exact allLevelParamsDefined_stripPis n h.2 hs'
    | _ => simp [Expr.stripPis] at hs

/-- **`SortDn` from the level parameters**: a level whose parameters are among `lps`, each of
`lps`' names with a `dn` handle. -/
theorem sortDn_of_lps {dn : ConRon.Arena.NIdx → Option Name} {lps : List Name} {s : Level}
    (hs : s.allParamsDefined lps = true) (hlp : ∀ x ∈ lps, ∃ k, dn k = some x) : SortDn dn s := by
  intro ps hz x hx
  have h := Level.zeronessOf_paramsDefined hs
  rw [hz, PropWhen.paramsDefined_ifAllZero, List.all_eq_true] at h
  exact hlp x (by simpa [List.contains_iff_mem] using h x hx)

/-- **Member 0's former sort's zero-ness names have `dn` handles** when its level parameters'
names do: con-leche's `checkBlockTele` answers a sort `s` of a checked record with the member's
level parameters. -/
theorem sortDn_of_checkBlockTele {dn : ConRon.Arena.NIdx → Option Name} {μ : CheckMode} {env : Env}
    {nP : Nat} {msP : MemberShape} {cv : ConstantVal} {s : Level}
    (h : ConRon.Bridge.Inductives.FOk (ConLeche.checkBlockTele (fueledOpsM μ) env nP msP) (cv, s))
    (hlp : ∀ x ∈ msP.cvT.levelParams, ∃ k, dn k = some x) : SortDn dn s := by
  obtain ⟨F, hF⟩ := h
  rw [checkBlockTele_datF] at hF
  obtain ⟨cvT, -, hlps, rfl, hcc, bs, hstrip⟩ := checkBlockTele_shape hF
  have hty := (checkConstantVal_typeWF hcc).2.1
  have hsrt := allLevelParamsDefined_stripPis (nP + msP.nIdx) hty hstrip
  simp only [Expr.allLevelParamsDefined] at hsrt
  exact sortDn_of_lps hsrt (hlps ▸ hlp)

/-- **The same from member 0's handles**: every level-parameter handle of the twin's member
record has a `dn` name (`dn` agreeing with the name store, `TwinMem.dnN`). -/
theorem sortDn_of_member {dn : ConRon.Arena.NIdx → Option Name} {μ : CheckMode} {env : Env}
    {st : ConRon.Arena.EStore} {nP : Nat} {ms : ConRon.Arena.MemberShape} {msP : MemberShape}
    {cv : ConstantVal} {s : Level}
    (hm : ConRon.Bridge.Inductives.dMember st ms = some msP)
    (hdnN : ∀ (k : ConRon.Arena.NIdx) (x : Name), dn k = some x → ConRon.Arena.denoteN st.ns k = some x)
    (hk : ∀ k ∈ ms.cvT.levelParams, (dn k).isSome)
    (h : ConRon.Bridge.Inductives.FOk (ConLeche.checkBlockTele (fueledOpsM μ) env nP msP) (cv, s)) :
    SortDn dn s := by
  refine sortDn_of_checkBlockTele h fun x hx => ?_
  obtain ⟨hcv, -, -⟩ := ConRon.Bridge.Inductives.dMember_inv hm
  unfold ConRon.Arena.Frontend.denoteCV at hcv
  split at hcv
  · rename_i n lps ty h1 h2 h3
    simp only [Option.some.injEq] at hcv
    rw [← hcv] at hx
    obtain ⟨k, hkm, hkx⟩ := denoteNList_mem h2 x hx
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (hk k hkm)
    have := hdnN k y hy
    rw [hkx, Option.some.injEq] at this
    exact ⟨k, this ▸ hy⟩
  · cases hcv

end L.Ind
