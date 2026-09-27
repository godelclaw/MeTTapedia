import Mettapedia.GraphTheory.FourColor.GoertzelV24PortTangleGluing

/-!
# Zero Count is preserved by a support-equal replacement

A closed instance cut along one noose is an outside piece and an inside piece
glued along the crossed edges.  The gluing bijection says a colouring of the
whole is a middle word together with a colouring of each side realizing it, so
the whole is colourable exactly when some word lies in both sides' supports.

Hence the inside piece matters only through its support.  Replacing it by any
other piece with the *same* support — in particular by a strictly smaller one
from deeper in a decomposition tree — leaves colourability, and so zero Count,
exactly where it was.  This is the single fact the tree descent's replacement
step needs from the colouring side; the rest of that step is the physical
splice.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedCountReplacement

open GoertzelV24PortTangleGluing
open GoertzelV24PortTangleGluing.PortTangle

universe u

variable {V W W' I K K' J : Type u}

/-- The words an inside piece realizes on its seam. -/
def innerSupport (T : PortTangle W K (J ⊕ PEmpty.{u + 1})) : Set (J → Color) :=
  {y | Nonempty (Col T (Sum.elim y PEmpty.elim))}

/-- The words an outside piece realizes on its seam. -/
def outerSupport (T : PortTangle V I (PEmpty.{u + 1} ⊕ J)) : Set (J → Color) :=
  {y | Nonempty (Col T (Sum.elim PEmpty.elim y))}

/-- A closed instance: outside glued to inside, with no ports left. -/
def ClosedColorable (T₁ : PortTangle V I (PEmpty.{u + 1} ⊕ J))
    (T₂ : PortTangle W K (J ⊕ PEmpty.{u + 1})) : Prop :=
  Nonempty (Col (series T₁ T₂) (Sum.elim PEmpty.elim PEmpty.elim))

/-- **A closed instance is colourable iff the two supports meet.** -/
theorem closedColorable_iff (T₁ : PortTangle V I (PEmpty.{u + 1} ⊕ J))
    (T₂ : PortTangle W K (J ⊕ PEmpty.{u + 1})) :
    ClosedColorable T₁ T₂ ↔ ∃ y : J → Color, y ∈ outerSupport T₁ ∧ y ∈ innerSupport T₂ := by
  constructor
  · rintro ⟨c⟩
    obtain ⟨y, c₁, c₂⟩ := gluingEquiv T₁ T₂ PEmpty.elim PEmpty.elim c
    exact ⟨y, ⟨c₁⟩, ⟨c₂⟩⟩
  · rintro ⟨y, ⟨c₁⟩, ⟨c₂⟩⟩
    exact ⟨(gluingEquiv T₁ T₂ PEmpty.elim PEmpty.elim).symm ⟨y, c₁, c₂⟩⟩

/-- **Support-equal replacement preserves colourability.** -/
theorem closedColorable_iff_of_innerSupport_eq
    (T₁ : PortTangle V I (PEmpty.{u + 1} ⊕ J))
    (T₂ : PortTangle W K (J ⊕ PEmpty.{u + 1}))
    (T₂' : PortTangle W' K' (J ⊕ PEmpty.{u + 1}))
    (h : innerSupport T₂ = innerSupport T₂') :
    ClosedColorable T₁ T₂ ↔ ClosedColorable T₁ T₂' := by
  rw [closedColorable_iff, closedColorable_iff, h]

/-- **Zero Count is preserved.**  The form the descent consumes. -/
theorem not_closedColorable_of_innerSupport_eq
    (T₁ : PortTangle V I (PEmpty.{u + 1} ⊕ J))
    (T₂ : PortTangle W K (J ⊕ PEmpty.{u + 1}))
    (T₂' : PortTangle W' K' (J ⊕ PEmpty.{u + 1}))
    (h : innerSupport T₂ = innerSupport T₂')
    (hzero : ¬ ClosedColorable T₁ T₂) : ¬ ClosedColorable T₁ T₂' :=
  fun hc => hzero ((closedColorable_iff_of_innerSupport_eq T₁ T₂ T₂' h).2 hc)

end GoertzelV24ClosedCountReplacement

end Mettapedia.GraphTheory.FourColor
