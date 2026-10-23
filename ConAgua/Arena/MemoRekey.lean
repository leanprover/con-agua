import ConAgua.Arena.MemoLibRel

/-!
# A memo read under another key codec (lane `indproofs4`, helper `wkt`)

Two walks can share one memo array (`all_level_params_defined`'s `apdSch` is the core's
`coreWsSch`: array 151, `CTL[152]`), each relating it to its own map under its own key codec and
value relation. A memo related under one codec is related under another that reads the same slot
words as a renaming of the keys (`φ`) and the values (`ψ`): `memoRV_rekey`; an empty memo under any
codec: `memoRV_empty_rekey`.
-/

open ConRon.Arena

namespace L.Arena

section
variable {κ κ' ν ν' : Type} (S : MemoSch) (K : MemoKey κ) (K' : MemoKey κ')
  (VR : Mem → Word → ν → Prop) (VR' : Mem → Word → ν' → Prop)

/-- **The slots represent the renamed lookup function** under the codec `K'`. -/
theorem memoAt_rekey (φ : κ → κ') (ψ : ν → ν')
    (hok : ∀ k1 k2, K.ok k1 k2 → K'.ok k1 k2 ∧ K'.dk k1 k2 = φ (K.dk k1 k2))
    (hek : ∀ x, K'.ek (φ x) = K.ek x)
    (hdk : ∀ x, K'.dk (K.ek x).1 (K.ek x).2 = φ (K.dk (K.ek x).1 (K.ek x).2))
    {e b n : Word} {m : Mem} {f : κ → Option ν} {g : κ' → Option ν'}
    (hV : ∀ w v, VR m w v → VR' m w (ψ v))
    (hg1 : ∀ x, g (φ x) = (f x).map ψ)
    (hg2 : ∀ y v', g y = some v' → ∃ x, φ x = y ∧ (f x).isSome)
    (h : MemoAt S K VR e b n m f) : MemoAt S K' VR' e b n m g := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun j hj hs ht => ?_, h2, fun y v' hy => ?_⟩
  · obtain ⟨hk, v, hv, hvr⟩ := h1 j hj hs ht
    obtain ⟨hk', hd⟩ := hok _ _ hk
    exact ⟨hk', ψ v, by rw [hd, hg1, hv]; rfl, hV _ _ hvr⟩
  · obtain ⟨x, rfl, hx⟩ := hg2 y v' hy
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hx
    obtain ⟨hdx, htomb, d, hd⟩ := h3 x v hv
    rw [hek]
    exact ⟨by rw [hdk, hdx], htomb, d, hd⟩

/-- The empty map's slots represent the empty map under any codec (no slot is live). -/
theorem memoAt_empty_rekey {e b n : Word} {m : Mem} (h : MemoAt S K VR e b n m (fun _ => none)) :
    MemoAt S K' VR' e b n m (fun _ => none) := by
  obtain ⟨h1, h2, -⟩ := h
  refine ⟨fun j hj hs ht => ?_, h2, fun _ _ hx => by cases hx⟩
  obtain ⟨-, v, hv, -⟩ := h1 j hj hs ht
  cases hv

end

/-- **A map renamed along an injection of keys**, as a `Std.HashMap`. -/
theorem hashMap_rekey {κ κ' ν ν' : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] [LawfulHashable κ]
    [BEq κ'] [Hashable κ'] [LawfulBEq κ'] [LawfulHashable κ']
    (φ : κ → κ') (hφ : Function.Injective φ) (ψ : ν → ν') (mp : Std.HashMap κ ν) :
    ∃ mp' : Std.HashMap κ' ν', (∀ x, mp'[φ x]? = mp[x]?.map ψ) ∧
      (∀ y v', mp'[y]? = some v' → ∃ x, φ x = y ∧ (mp[x]?).isSome) := by
  let l := mp.toList.map fun q => (φ q.1, ψ q.2)
  have hd : l.Pairwise (fun a b => (a.1 == b.1) = false) := by
    refine List.Pairwise.map _ (fun a b h => ?_) mp.distinct_keys_toList
    simp only [beq_eq_false_iff_ne, ne_eq] at h ⊢
    exact fun e => h (hφ e)
  have hmem : ∀ y, (l.map Prod.fst).contains y = true → ∃ x, φ x = y ∧ (mp[x]?).isSome := by
    intro y hy
    simp only [l, List.map_map, List.contains_eq_any_beq, List.any_eq_true, List.mem_map,
      Function.comp_apply, beq_iff_eq] at hy
    obtain ⟨_, ⟨⟨x, v⟩, hxv, rfl⟩, rfl⟩ := hy
    exact ⟨x, rfl, by rw [Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hxv]; rfl⟩
  refine ⟨Std.HashMap.ofList l, fun x => ?_, fun y v' hy => ?_⟩
  · cases hx : mp[x]? with
    | some v =>
      exact Std.HashMap.getElem?_ofList_of_mem (k := φ x) (beq_self_eq_true _) hd
        (List.mem_map.mpr ⟨(x, v), Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hx, rfl⟩)
    | none =>
      apply Std.HashMap.getElem?_ofList_of_contains_eq_false
      cases hc : (l.map Prod.fst).contains (φ x)
      · rfl
      · obtain ⟨x', he, hs⟩ := hmem _ hc
        rw [hφ he, hx] at hs; cases hs
  · cases hc : (l.map Prod.fst).contains y
    · rw [Std.HashMap.getElem?_ofList_of_contains_eq_false hc] at hy; cases hy
    · exact hmem y hc

section
variable {κ κ' ν ν' : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] [LawfulHashable κ]
  [BEq κ'] [Hashable κ'] [LawfulBEq κ'] [LawfulHashable κ']
  (S : MemoSch) (K : MemoKey κ) (K' : MemoKey κ')
  (VR : Mem → Word → ν → Prop) (VR' : Mem → Word → ν' → Prop)

/-- **A memo related under the codec `K` is related under `K'`**, when `K'` reads the same slot
words as the keys renamed by the injection `φ` and the values renamed by `ψ`. -/
theorem memoRV_rekey (φ : κ → κ') (hφ : Function.Injective φ) (ψ : ν → ν')
    (hok : ∀ k1 k2, K.ok k1 k2 → K'.ok k1 k2 ∧ K'.dk k1 k2 = φ (K.dk k1 k2))
    (hek : ∀ x, K'.ek (φ x) = K.ek x)
    (hdk : ∀ x, K'.dk (K.ek x).1 (K.ek x).2 = φ (K.dk (K.ek x).1 (K.ek x).2))
    {m : Mem} (hV : ∀ w v, VR m w v → VR' m w (ψ v)) {mp : Std.HashMap κ ν}
    (h : MemoRV S K VR m mp) : ∃ mp' : Std.HashMap κ' ν', MemoRV S K' VR' m mp' := by
  obtain ⟨mp', hg1, hg2⟩ := hashMap_rekey φ hφ ψ mp
  exact ⟨mp', h.1, h.2.1, h.2.2.1,
    memoAt_rekey S K K' VR VR' φ ψ hok hek hdk hV hg1 hg2 h.2.2.2⟩

/-- **An empty memo is an empty memo under any codec.** -/
theorem memoRV_empty_rekey {m : Mem} (h : MemoRV S K VR m ∅) : MemoRV S K' VR' m ∅ :=
  ⟨h.1, h.2.1, h.2.2.1, by
    have := memoAt_empty_rekey S K K' VR VR' (m := m) (e := epG S m) (b := mbG S m) (n := nG S m)
      (by simpa using h.2.2.2)
    simpa using this⟩

end

end L.Arena
