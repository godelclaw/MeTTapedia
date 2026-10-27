import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PresentedContexts
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.StaticDecider
import Mettapedia.GSLT.LanguageDef.Contexts.Controls.ReductionBisimilarity

/-!
# Controls: the contact theory's presented transitions at the front door

The law-free contact theory has processes `Nil`, `A`, `B`, `In p`, `Out p` and `Join p q`, and the rule
`Join(In(x), Out(y)) ⟶ Join(x, y)`. Its presented labels `Join(In([-]), Out(Nil))` and `Join([-], Nil)` are contexts
of occurrences. Through `transition_iff_closed`, their transitions are read by the front door's modal decider.

- **`A` placed in `Join(In([-]), Out(Nil))` moves to `Join(A, Nil)`** (`a_moves_in_prefix`), a presented transition
  established at the front door.
- **`A` placed in `Join([-], Nil)` does not move there** (`a_stays_in_contact`), refuted at the front door.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.PresentedContextControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep (ReferenceProfile)
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory Term apply_labelOfOccurrence)
open Mettapedia.GSLT.LanguageDef.Contexts.Controls (bareValidated proc constantA prefixContext prefixLabel
  contactContext contactLabel bare_equationFree bare_reduct_sorted)
open Mettapedia.GSLT.LanguageDef.Interaction.Controls.EquationalContact (base join termA termNil)

theorem contact_profile : ReferenceProfile bareValidated.language := by
  unfold ReferenceProfile
  decide

/-- The modal decider of the contact theory. -/
def decider : Decider RelationEnv.empty bareValidated.language :=
  modalDecider (equationFreeSuccessors 3 bare_equationFree) (staticDecider bare_equationFree)

/-- `Join(A, Nil)`, the result of the meeting, as a closed process. -/
def joined : Term bareValidated.language proc :=
  ⟨join termA termNil, bare_reduct_sorted ((contextTheory base bareValidated).apply prefixLabel constantA).2⟩

/-- **Placed in `Join(In([-]), Out(Nil))`, `A` moves to `Join(A, Nil)`.** -/
theorem a_moves_in_prefix : (contextTheory base bareValidated).Transition constantA prefixLabel joined := by
  refine (PresentedContexts.transition_iff_closed bare_equationFree contact_profile rfl rfl prefixLabel
    (hole := "x") (by decide) (fun term => apply_labelOfOccurrence base _ _ _ _ term) constantA joined).mpr ?_
  have holds := (decider.exact (formula := .possibly (.context "x" (prefixContext.fill (.fvar "x")) .any)
    (.is (join termA termNil))) (term := termA) (by decide +kernel)).mpr rfl
  obtain ⟨next, step, -, named⟩ := holds
  rw [objectEquivalent_iff_eq_of_isEquationFree bare_equationFree] at named
  subst named
  exact step

/-- **Placed in `Join([-], Nil)`, `A` does not move to `Join(A, Nil)`.** -/
theorem a_stays_in_contact : ¬ (contextTheory base bareValidated).Transition constantA contactLabel joined := by
  rw [PresentedContexts.transition_iff_closed bare_equationFree contact_profile rfl rfl contactLabel (hole := "x")
    (by decide) (fun term => apply_labelOfOccurrence base _ _ _ _ term) constantA joined]
  intro step
  have refuted := (decider.exact (formula := .possibly (.context "x" (contactContext.fill (.fvar "x")) .any) .top)
    (term := termA) (answer := false) (by decide +kernel)).mp ⟨_, step, trivial⟩
  cases refuted

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.PresentedContextControls
