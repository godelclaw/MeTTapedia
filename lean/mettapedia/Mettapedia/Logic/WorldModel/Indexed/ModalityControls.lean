import Mettapedia.OSLF.Framework.DerivedModalities
import Mettapedia.Logic.WorldModel.Indexed.Quantifiers
import Mettapedia.Logic.WorldModel.Indexed.Modalities

/-!
# The step modalities are not extension necessity

The set-level change of base used for the step modalities of a reduction span
is the quantifier pair of the doctrine at propositional evidence
(`existsAlong_eq_di`, `forallAlong_eq_ui`).

The backward box of a reduction span, "every predecessor satisfies", is not
extension necessity, "every extension satisfies".  On the one-step span
`false ⇝ true`, with extension the order `false ≤ true`, the predicate "is
`false`" is backward-necessary at `true` and not extension-necessary there
(`backwardBox_ne_extensionBox`).  The one-step diamond is not the extension
diamond either: at `true`, which has no step, the step diamond of "is `true`"
fails while the extension diamond holds (`stepDiamond_ne_extensionDiamond`).
-/

set_option autoImplicit false

open CategoryTheory

namespace Mettapedia.Logic.WorldModel.Indexed.ModalityControls

open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.Logic.WorldModel.Indexed.Quantifiers
open Mettapedia.Logic.WorldModel.Indexed.Modal

/-- The existential image of the step modalities is the doctrine's existential
quantifier at propositional evidence. -/
theorem existsAlong_eq_di {E X : Type} (f : E → X) (ψ : E → Prop) :
    existsAlong f ψ = di f ψ := by
  funext x
  simp [existsAlong, di]

/-- The universal image of the step modalities is the doctrine's universal
quantifier at propositional evidence. -/
theorem forallAlong_eq_ui {E X : Type} (f : E → X) (ψ : E → Prop) :
    forallAlong f ψ = ui f ψ := by
  funext x
  simp [forallAlong, ui]

/-- The one-step span `false ⇝ true`. -/
def oneStep : ReductionSpan Bool where
  Edge := Unit
  source _ := false
  target _ := true

/-- **The backward box is not extension necessity.** -/
theorem backwardBox_ne_extensionBox :
    derivedBox oneStep (fun b => b = false) true ∧ ¬ extBox (fun b : Bool => b = false) true := by
  constructor
  · intro e _
    rfl
  · intro h
    exact absurd (h true (𝟙 true)) (by decide)

/-- **The step diamond is not the extension diamond.** -/
theorem stepDiamond_ne_extensionDiamond :
    ¬ derivedDiamond oneStep (fun b => b = true) true ∧ extDiamond (fun b : Bool => b = true) true := by
  constructor
  · rintro ⟨e, he, _⟩
    have : false = true := he
    exact absurd this (by decide)
  · exact ⟨true, 𝟙 true, rfl⟩

end Mettapedia.Logic.WorldModel.Indexed.ModalityControls
