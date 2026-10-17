import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.PrincipalAlpha
import Mettapedia.Languages.MeTTa.HE.LeaTTaTypeConformance

/-!
# Alpha-exact observation of LeaTTa type presentations

This module instantiates finite-presentation alpha uniqueness with repaired
LeaTTa's canonical runtime binding invariant.  The spec presentation and the
runtime binding list are related only by their complete solution theories;
no equality-class representative or binding-list order is exposed.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationPrincipalAlpha

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation
open Spec.Type.Presentation.Theory
open Spec.Type.Presentation.MatchSolutionTheory
open Spec.Type.RuntimeRefinement
open Spec.Type.Presentation.Alpha
open Spec.Type.Presentation.PrincipalAlpha
open LeaTTaBridge
open LeaTTaSpecConformance
open LeaTTaTypeConformance

/-- A normal finite presentation of any spec binding theory agrees with the
actual reachable runtime materialization up to residual-variable renaming.
The presentation is syntax over HE atoms and does not choose runtime equality
representatives or decode arbitrary native payloads back into source values. -/
theorem observedTypeAlpha_of_bindingTheory
    {substitution : TypeSubst} (normal : substitution.Normal)
    {spec : Bindings} {bindings : Metta.Bindings}
    (presentation : ∀ valuation,
      TypeSubstSatisfied valuation substitution ↔ TypeBindingSatisfied valuation spec)
    (theory : LeaBindingSolutionTheoryEquiv spec bindings)
    (runtime : LeaRuntimeBindingInvariant bindings)
    (declared : Atom) :
    ObservedTypeAlphaRel
      (substitution.apply declared)
      (fromLeaTTaAtom
        (Metta.instantiate bindings (toLeaTTaAtom declared))) := by
  let leaModel := leaClassSolution bindings
  let nativeModel : String → Atom :=
    fun name => fromLeaTTaAtom (leaModel name)
  have nativeModelSatisfied :
      TypeSubstSatisfied nativeModel substitution := by
    have specModel : HEBindingSatisfied leaModel spec :=
      (theory leaModel).mpr runtime.canonical.1
    have nativeSpecModel :=
      specTypeBindingSatisfied_of_heBindingSatisfied specModel
    exact (presentation nativeModel).mpr nativeSpecModel
  have presentationRefinesModel :
      ∃ post : String → Atom, ∀ name,
        presentedValuation substitution name =
          applyTypeValuation post (nativeModel name) := by
    let presentationModel := presentedValuation substitution
    let leaPresentationModel : String → Metta.Atom :=
      fun name => toLeaTTaAtom (presentationModel name)
    have presentationSatisfied :
        TypeSubstSatisfied presentationModel substitution :=
      normal_presentedValuation_satisfied normal
    have specPresentationSatisfied : TypeBindingSatisfied presentationModel spec :=
      (presentation presentationModel).mp presentationSatisfied
    have heaPresentationSatisfied : HEBindingSatisfied leaPresentationModel spec :=
      heBindingSatisfied_of_specTypeBindingSatisfied
        specPresentationSatisfied
    have leaPresentationSatisfied :
        LeaBindingSatisfied leaPresentationModel bindings :=
      (theory leaPresentationModel).mp heaPresentationSatisfied
    obtain ⟨leaPost, hleaPost⟩ :=
      runtime.canonical.2 leaPresentationModel leaPresentationSatisfied
    refine ⟨fun name => fromLeaTTaAtom (leaPost name), ?_⟩
    intro name
    have decoded := congrArg fromLeaTTaAtom (hleaPost name)
    rw [fromLeaTTaAtom_applyClassSolution_any] at decoded
    simpa [leaPresentationModel, presentationModel,
      nativeModel, leaModel] using decoded
  have alpha := observedTypeAlpha_of_mutuallyPrincipal normal
    nativeModelSatisfied presentationRefinesModel declared
  simpa [nativeModel, leaModel, ← fromLeaTTaAtom_applyClassSolution,
    applyClassSolution_lea_eq_instantiate] using alpha

/-- The assignment-only presentation API specializes the general binding
presentation theorem; its existing guarantee and callers are unchanged. -/
theorem observedTypeAlpha_of_solutionTheory
    {substitution : TypeSubst} (normal : substitution.Normal)
    {bindings : Metta.Bindings}
    (theory : LeaBindingSolutionTheoryEquiv
      (typeSubstAsBindings substitution) bindings)
    (runtime : LeaRuntimeBindingInvariant bindings)
    (declared : Atom) :
    ObservedTypeAlphaRel
      (substitution.apply declared)
      (fromLeaTTaAtom (Metta.instantiate bindings (toLeaTTaAtom declared))) :=
  observedTypeAlpha_of_bindingTheory normal
    (fun valuation => (typeBindingSatisfied_asBindings_iff valuation substitution).symm)
    theory runtime declared

/-! ## Boundary examples -/

/-- Positive: the empty runtime presentation agrees literally, hence also
alpha-exactly, with the empty finite presentation. -/
theorem empty_presentation_alpha (declared : Atom) :
    ObservedTypeAlphaRel
      (TypeSubst.apply ([] : TypeSubst) declared)
      (fromLeaTTaAtom
        (Metta.instantiate Metta.Bindings.empty
          (toLeaTTaAtom declared))) := by
  apply observedTypeAlpha_of_solutionTheory TypeSubst.normal_empty
  · intro valuation
    simp [typeSubstAsBindings, HEBindingSatisfied,
      LeaBindingSatisfied, Metta.Bindings.empty]
  · exact leaRuntimeBindingInvariant_empty

/-- Negative boundary: alpha-exactness does not identify a runtime symbol
with a spec variable merely because both are legal type atoms. -/
theorem variable_symbol_boundary_not_alpha :
    ¬ObservedTypeAlphaRel (.var "x") (.symbol "A") :=
  Spec.Type.Presentation.PrincipalAlpha.variable_symbol_not_alpha

end Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationPrincipalAlpha
