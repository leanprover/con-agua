module

public import ConAgua.Arena.Tiers
public import ConAgua.Arena.Refine
public import ConRon.Arena.Core

@[expose] public section

/-!
# A major premise's view in L (`MajorView`)

The twin's `MajorView` (`ConRon/Arena/Core.lean`) is the ι step's classification of a major
premise: a spine headed by a stored constructor, with the constructor's name, levels and record,
or any other term. In L a view is five words `[t, e, c, us, q]`:

* `t = 0`: `.stuck e`;
* `t ≠ 0`: `.ctor e c us cv nP nF induct`, where `q` is the constructor's record in `EREC`
  (`decCI` decodes it to `.ctorInfo cv nP nF induct`).

The record is passed by its address, not copied: L's records are immutable once written, and the
reader of the view reads the counts and the family off it. (The twin copies the
`IConstantVal` into the view, as con-ron's Rust does; con-leche shares it by reference.)

The decoder reads the record at a fixed memory, the call's entry memory: a constructor's record
is the environment's, written before the call, and `EREC` only grows (`ErecGrow`).
-/

namespace L.Arena
open ConRon.Arena

/-- **The view the words `r` stand for**, its record decoded in `m`. A `t ≠ 0` view whose record
does not decode to a constructor has no meaning; it decodes to `.stuck e`. -/
def decMV (m : Mem) (r : List Word) : MajorView :=
  let t := r.headD 0
  let e : EIdx := decE (r.getD 1 0)
  if t = 0 then .stuck e
  else match decCI (erecP m) (r.getD 4 0).toNat with
    | some (.ctorInfo cv nP nF ind) => .ctor e (decI (r.getD 2 0)) (decI (r.getD 3 0)) cv nP nF ind
    | _ => .stuck e

/-- The words of a well-formed view: five words, the term a handle (below `2 ^ 32`), a `.ctor` view's record
decoding to a constructor record. -/
def MVOk (m : Mem) (r : List Word) : Prop :=
  r.length = 5 ∧ (r.getD 1 0).toNat < 2 ^ 32 ∧ (r.headD 0 ≠ 0 →
    ∃ cv nP nF ind, decCI (erecP m) (r.getD 4 0).toNat = some (.ctorInfo cv nP nF ind))

@[simp] theorem decMV_stuck (m : Mem) (e c us q : Word) :
    decMV m [0, e, c, us, q] = .stuck (decE e) := by simp [decMV]

theorem decMV_ctor {m : Mem} {t e c us q : Word} (ht : t ≠ 0) {cv : IConstantVal} {nP nF : Nat}
    {ind : NIdx} (hq : decCI (erecP m) q.toNat = some (.ctorInfo cv nP nF ind)) :
    decMV m [t, e, c, us, q] = .ctor (decE e) (decI c) (decI us) cv nP nF ind := by
  simp [decMV, ht, hq]

/-- The view's term (`MajorView.expr`) is the second word. -/
theorem decMV_expr (m : Mem) (r : List Word) : (decMV m r).expr = decE (r.getD 1 0) := by
  unfold decMV; dsimp only; split
  · rfl
  · split <;> rfl

/-- **The view decodes alike in a grown record pool.** -/
theorem decMV_ext {m m' : Mem} (hx : ArrExt (erecP m) (erecP m')) {r : List Word}
    (hok : MVOk m r) : decMV m' r = decMV m r := by
  unfold decMV; dsimp only
  split
  · rfl
  · rename_i ht
    obtain ⟨cv, nP, nF, ind, hq⟩ := hok.2.2 ht
    rw [hq, hx.decCI hq]

end L.Arena
