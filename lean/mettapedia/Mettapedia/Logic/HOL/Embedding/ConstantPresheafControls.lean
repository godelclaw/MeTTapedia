import Mettapedia.Logic.HOL.Embedding.ConstantPresheafInterpretation
import Mettapedia.Logic.HOL.Embedding.HypersetHenkinInterpretation
import Mettapedia.TypeTheory.HostChoiceContextualPresheafControls

/-!
# A classical hyperset HOL fragment in a nonclassical presheaf host

The actual full hyperset HOL model is interpreted in constant presheaves over
the existing advancing-world category. Its closed propositions are pulled back
to the host terminal context. They satisfy excluded middle, and the source
sorts carry total Hilbert choice. The same host has a stable predicate with no
such constant reading and fails internal double-negation elimination.

The separation concerns the internal logic of one specified presheaf host.
Its construction in Lean uses classical metatheory; it does not claim to remove
that metatheoretic dependency or to prove the consistency of arbitrary Prime
assemblies. An empty ambient presheaf also remains outside the inhabited HOL
sorts on which the supplied choice operates.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Logic.HOL.Embedding.ConstantPresheafControls

open CategoryTheory
open Mettapedia.TypeTheory
open ContextualWitnessCover ContextualPresheafExactness
open MaterialSets.Hypersets
open CoveredFuturePowerClassifier PowerClassPresheafDescent.Controls
open CoveredFuturePowerControls
open ConstantPresheafInterpretation

noncomputable def guest : HenkinModel.{0, 0, 1} Unit ZFSetHenkinInterpretation.Symbol :=
  HypersetHenkinInterpretation.model HSet.Presentation.choice

/-- A one-world comparison uses the same substantive hyperset guest model. -/
def oneWorldPoint : (context (D := Discrete PUnit) guest []).Elements :=
  ⟨⟨PUnit.unit⟩, fun index => nomatch index⟩

theorem oneWorld_points_equal
    (point : (context (D := Discrete PUnit) guest []).Elements) : point = oneWorldPoint := by
  apply Sigma.ext (Subsingleton.elim _ _)
  apply heq_of_eq
  funext type index
  nomatch index

/-- On one world every predicate of the closed context is represented by
truth or falsity. Thus the coverage hypothesis has a concrete positive instance. -/
theorem oneWorld_predicate_coverage :
    Function.Surjective (predicate (D := Discrete PUnit) guest (Γ := [])) := by
  classical
  intro proposition
  by_cases holds : proposition.holds oneWorldPoint
  · refine ⟨.top, ?_⟩
    apply StablePredicate.ext
    intro point
    rw [oneWorld_points_equal point]
    change True ↔ proposition.holds oneWorldPoint
    simp [holds]
  · refine ⟨.bot, ?_⟩
    apply StablePredicate.ext
    intro point
    rw [oneWorld_points_equal point]
    change False ↔ proposition.holds oneWorldPoint
    simp [holds]

theorem oneWorld_excludedMiddle
    (proposition : StablePredicate (context (D := Discrete PUnit) guest []))
    (point : (context (D := Discrete PUnit) guest []).Elements) :
    proposition.holds point ∨
      (implication proposition (predicate guest (.bot : ClosedFormula ZFSetHenkinInterpretation.Symbol))).holds point :=
  excludedMiddle_of_predicate_coverage guest
    (HypersetHenkinInterpretation.fullDomains HSet.Presentation.choice)
    oneWorld_predicate_coverage proposition point

theorem oneWorld_cyclic_excludedMiddle :
    (predicate (D := Discrete PUnit) guest HypersetHenkinInterpretation.selfMember).holds oneWorldPoint ∨
      (implication (predicate guest HypersetHenkinInterpretation.selfMember)
        (predicate guest (.bot : ClosedFormula ZFSetHenkinInterpretation.Symbol))).holds oneWorldPoint :=
  oneWorld_excludedMiddle (predicate guest HypersetHenkinInterpretation.selfMember) oneWorldPoint

abbrev ambient := HostChoiceContextualPresheafControls.Logic.ambient

def emptyValuation : NaturalHom ambient (context (D := Stagesᵒᵖ) guest []) where
  app _ _ := fun index => nomatch index
  naturality _ _ := by
    funext A index
    nomatch index

def closedMeaning (formula : ClosedFormula ZFSetHenkinInterpretation.Symbol) : StablePredicate ambient :=
  inverseImage emptyValuation (predicate guest formula)

theorem closedMeaning_iff (formula : ClosedFormula ZFSetHenkinInterpretation.Symbol)
    (point : ambient.Elements) : (closedMeaning formula).holds point ↔ guest.models formula := by
  apply Iff.of_eq
  apply congrArg (fun valuation : guest.Valuation [] => (guest.denote formula valuation).down)
  funext A index
  nomatch index

/-- A world-independent source proposition has an internal complement. -/
theorem excludedMiddle_in_fragment (formula : ClosedFormula ZFSetHenkinInterpretation.Symbol)
    (point : ambient.Elements) :
    (closedMeaning formula).holds point ∨
      (implication (closedMeaning formula) HostChoiceContextualPresheafControls.Logic.falsity).holds point := by
  have classicality : guest.models formula ∨ ¬ guest.models formula :=
    Classical.em (guest.models formula)
  rcases classicality with positive | negative
  · exact Or.inl ((closedMeaning_iff formula point).mpr positive)
  · refine Or.inr ?_
    intro future arrival available
    exact negative ((closedMeaning_iff formula _).mp available)

/-- The explicit later-world predicate cannot be represented by a closed
proposition of this constant fragment. -/
theorem laterTruth_not_in_image (formula : ClosedFormula ZFSetHenkinInterpretation.Symbol) :
    ¬ ∀ point : ambient.Elements,
      (closedMeaning formula).holds point ↔ HostChoiceContextualPresheafControls.Logic.laterTruth.holds point := by
  intro represented
  let later : ambient.Elements := ⟨world 1, PUnit.unit⟩
  have laterTrue : HostChoiceContextualPresheafControls.Logic.laterTruth.holds later := by
    change 1 ≤ 1
    exact Nat.le_refl _
  have sourceTrue := (closedMeaning_iff formula later).mp ((represented later).mpr laterTrue)
  exact HostChoiceContextualPresheafControls.Logic.laterTruth_absent_now
    ((represented HostChoiceContextualPresheafControls.Logic.initial).mp
      ((closedMeaning_iff formula _).mpr sourceTrue))

/-- This actual classical guest does not cover the host's predicate object. -/
theorem closedMeaning_not_surjective : ¬ Function.Surjective closedMeaning := by
  intro covers
  obtain ⟨formula, represented⟩ := covers HostChoiceContextualPresheafControls.Logic.laterTruth
  apply laterTruth_not_in_image formula
  intro point
  rw [represented]

theorem ambient_doubleNegation_fails :
    ¬ Included
      (HostChoiceContextualPresheafControls.Logic.negative
        (HostChoiceContextualPresheafControls.Logic.negative
          HostChoiceContextualPresheafControls.Logic.laterTruth))
      HostChoiceContextualPresheafControls.Logic.laterTruth :=
  HostChoiceContextualPresheafControls.Logic.internal_doubleNegation_fails

noncomputable def guestChoice : guest.HilbertChoice :=
  HypersetHenkinInterpretation.holChoice HSet.Presentation.choice

def emptyObject : Stagesᵒᵖ ⥤ Type 1 := constant PEmpty.{2}

theorem emptyObject_has_no_section : IsEmpty emptyObject.sections :=
  ⟨fun witness => PEmpty.elim (witness.val (world 0))⟩

/-- Cyclic membership is interpreted in the same constant fragment; it is
not being asserted of the host's well-founded set membership. -/
theorem cyclic_guest (point : ambient.Elements) :
    (closedMeaning HypersetHenkinInterpretation.selfMember).holds point :=
  (closedMeaning_iff _ point).mpr
    (HypersetHenkinInterpretation.selfMember_valid HSet.Presentation.choice)

end Mettapedia.Logic.HOL.Embedding.ConstantPresheafControls
