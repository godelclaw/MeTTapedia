import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.FutureResponses
import Mettapedia.GSLT.Topos.PresheafPredicateQuantifierBaseChangeControls

/-!
# Present response coverage and future response coverage differ

The established growing presheaf has no present request and gains one
after restriction. Present coverage therefore holds with no responses,
while universal may membership correctly refuses it. A second control
supplies the actual future response and satisfies the classifier.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.FutureResponseControls

open _root_.CategoryTheory
open Mettapedia.GSLT.Topos
open PresheafPredicateQuantifierBaseChangeControls

def presentCoverage (world : Contextᵒᵖ) : Prop :=
  ∀ request : growing.obj world,
    ∃ response : growing.obj world,
      response ∈ (⊥ : Subfunctor growing).obj world ∧ response = request

theorem present_coverage : presentCoverage spot := by
  intro request
  exact Empty.elim request

theorem future_coverage_fails : ¬ presentCoverage future := by
  intro holds
  obtain ⟨_, impossible, _⟩ := holds ()
  exact impossible

/-- The source-world finite check cannot stand for a stable universal
classifier when future contexts introduce new requests. -/
theorem present_does_not_establish_future_membership :
    presentCoverage spot ∧
      () ∉ (FutureResponses.classifier (𝟙 growing) forgetGrowth
        (⊤ : Subfunctor growing) (⊥ : Subfunctor growing)).obj spot := by
  refine ⟨present_coverage, ?_⟩
  intro held
  have source := (FutureResponses.classifier_iff_source (𝟙 growing) forgetGrowth
    (⊤ : Subfunctor growing) (⊥ : Subfunctor growing) spot ()).mp held
  obtain ⟨_, impossible, _⟩ := source future restriction () rfl trivial
  exact impossible

/-- Actual future response events establish the positive control. -/
theorem future_responses_establish_membership :
    () ∈ (FutureResponses.classifier (𝟙 growing) forgetGrowth
      (⊤ : Subfunctor growing) (⊤ : Subfunctor growing)).obj spot := by
  apply (FutureResponses.classifier_iff_source _ _ _ _ _ _).mpr
  intro next arrow request aligned requested
  exact ⟨request, trivial, rfl⟩

theorem pointwise_coverage_is_not_stable :
    ¬ (presentCoverage spot → presentCoverage future) := by
  intro stable
  exact future_coverage_fails (stable present_coverage)

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.FutureResponseControls
