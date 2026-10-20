import Mettapedia.Logic.DDLPlus.Theorems

/-!
# Controls for DDL+ frames

Every theorem of `DDLPlus.Theorems` quantifies over a frame satisfying the semantic
conditions `sem_3a`–`sem_5e` of Carmo and Jones. This file gives a frame that satisfies
them: in an inhabited context `X`, a proposition `Y` is obligatory exactly when `X ⊆ Y`.

Positive: the frame exists for every world type (`inclusionFrame`); over `Bool` the
theorems `CJ_3`, `CJ_4`, `C_6` and `CJ_7` apply to it (`boolFrame_CJ_3`, …).

Negative: obligation in this frame is not trivial: `⊤` is obligatory in context `⊤`, while
`v = true` is not (`boolFrame_ob_top`, `boolFrame_not_ob_true`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.DDLPlus.FrameControls

open Mettapedia.Logic.DDLPlus.Core Mettapedia.Logic.DDLPlus.Theorems

/-- Obligation by inclusion: `Y` is obligatory in context `X` when `X` is inhabited and
contained in `Y`; both accessibility relations are total. -/
def inclusionFrame (w : Type*) : DDLPlusFrame w where
  av := fun _ _ => True
  pv := fun _ _ => True
  ob := fun X Y => (∃ v, X v) ∧ ∀ v, X v → Y v
  sem_3a := fun v => ⟨v, trivial⟩
  sem_4a := fun _ _ _ => trivial
  sem_4b := fun _ => trivial
  sem_5a := fun _ ⟨⟨v, hv⟩, h⟩ => h v hv
  sem_5b := fun _ _ _ h =>
    ⟨fun ⟨hne, hXY⟩ => ⟨hne, fun v hv => ((h v).mp ⟨hv, hXY v hv⟩).2⟩,
      fun ⟨hne, hXZ⟩ => ⟨hne, fun v hv => ((h v).mpr ⟨hv, hXZ v hv⟩).2⟩⟩
  sem_5c := fun _ _ _ ⟨v, hx, _, _⟩ ⟨_, hXY⟩ ⟨_, hXZ⟩ =>
    ⟨⟨v, hx⟩, fun u hu => ⟨hXY u hu, hXZ u hu⟩⟩
  sem_5d := fun X _ _ _ ⟨⟨v, hv⟩, hXY⟩ hXZ =>
    ⟨⟨v, hXZ v hv⟩, fun u hu => (Classical.em (X u)).elim (fun hx => Or.inr (hXY u hx))
      (fun hx => Or.inl ⟨hu, hx⟩)⟩
  sem_5e := fun _ _ _ hYX ⟨_, hXZ⟩ ⟨v, hy, _⟩ => ⟨⟨v, hy⟩, fun u hu => hXZ u (hYX u hu)⟩

/-- The inclusion frame over two worlds. -/
def boolFrame : DDLPlusFrame Bool := inclusionFrame Bool

/-- **Positive control.** `⊤` is obligatory in context `⊤`. -/
theorem boolFrame_ob_top : boolFrame.ob (fun _ => True) (fun _ => True) :=
  ⟨⟨true, trivial⟩, fun _ _ => trivial⟩

/-- **Negative control.** `v = true` is not obligatory in context `⊤`. -/
theorem boolFrame_not_ob_true : ¬ boolFrame.ob (fun _ => True) (fun v => v = true) :=
  fun ⟨_, h⟩ => Bool.false_ne_true (h false trivial)

/-- The meaning "the world is `true`", in every context. -/
def isTrue : Meaning Unit Bool := fun _ v => v = true

/-- **Positive control** for `CJ_3`. -/
theorem boolFrame_CJ_3 : type_of% (CJ_3 boolFrame isTrue) := CJ_3 boolFrame isTrue

/-- **Positive control** for `CJ_4`. -/
theorem boolFrame_CJ_4 : type_of% (CJ_4 boolFrame isTrue) := CJ_4 boolFrame isTrue

/-- **Positive control** for `C_6`. -/
theorem boolFrame_C_6 : type_of% (C_6 boolFrame isTrue isTrue isTrue) :=
  C_6 boolFrame isTrue isTrue isTrue

/-- **Positive control** for `CJ_7`: equivalent meanings are interchangeable under
obligation. -/
theorem boolFrame_CJ_7 :
    type_of% (CJ_7 boolFrame isTrue isTrue isTrue (fun _ _ => Iff.rfl)) :=
  CJ_7 boolFrame isTrue isTrue isTrue (fun _ _ => Iff.rfl)

#print axioms boolFrame_CJ_3
#print axioms boolFrame_CJ_7
#print axioms boolFrame_not_ob_true

end Mettapedia.Logic.DDLPlus.FrameControls
