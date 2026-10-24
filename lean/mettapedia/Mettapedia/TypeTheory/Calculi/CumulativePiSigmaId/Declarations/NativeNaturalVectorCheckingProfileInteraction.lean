import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorCheckingProfiles

/-!
# Interaction evidence for the natural-intensional checking profile

The natural-intensional profile selects the same two Nat iota rows whose
actual declaration-aware rule package already has an exact constructor-schema
presentation.  That presentation proves Church--Rosser for structural beta,
pair projections, universe-head equality and the selected iota roots.  It also
supplies Pi/Sigma conversion boundaries and formed subject reduction.

This module packages those existing results against the checking profile's
exact enabled-row function.  It does not infer interaction evidence from
feature union, prove total normalization, or extend the result to the full
raw vector profile.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies
namespace Programs.CheckingProfiles.Interaction

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.ConversionCoherence
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Declaration.IndexedFamily.Checking
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.TypedEquality.Annotated
open Programs.CheckingProfiles

/-- The actual declaration-aware calculus selected by a checking contract.
Optional identity fields are not silently installed in this rule package. -/
abbrev actualRules (profile : Contract) : Rules Tower.Head :=
  ComputationProfiles.rules profile.enabled

/-- Evidence that the selected structural and root computations interact
coherently at the formation-sensitive judgment.  Normalization is deliberately
not a field. -/
structure Certificate (profile : Contract) : Prop where
  churchRosser : ChurchRosser (actualRules profile)
  piBoundary : PiConversionBoundary (actualRules profile)
  sigmaBoundary : SigmaConversionBoundary (actualRules profile)
  preserves {n : Nat} {context : Tower.Ctx n}
      {source target type : Tower.Tm n} :
    FormationSensitive.Judgment (actualRules profile) context source type →
    StepStar (actualRules profile) source target →
      FormationSensitive.Judgment (actualRules profile) context target type

theorem naturalIntensional_actualRules :
    actualRules naturalIntensional =
      ComputationProfiles.rules ComputationProfiles.naturalOnly := by
  unfold actualRules
  rw [naturalIntensional_enabled_eq]

/-- The profile's roots are exactly the two previously proved constructor
schemas; no row is added by the certificate. -/
theorem naturalIntensional_roots_exact {n : Nat}
    {left right : Tower.Tm n} :
    (actualRules naturalIntensional).computation.step left right ↔
      AlgebraicSchema.SchemaStep ComputationProfiles.NaturalConversion.Schema
        left right := by
  rw [naturalIntensional_actualRules]
  exact ComputationProfiles.NaturalConversion.roots_exact

theorem naturalIntensionalCertificate : Certificate naturalIntensional where
  churchRosser := by
    rw [naturalIntensional_actualRules]
    exact ComputationProfiles.NaturalConversion.churchRosser
  piBoundary := by
    rw [naturalIntensional_actualRules]
    exact ComputationProfiles.NaturalConversion.pi_boundary
  sigmaBoundary := by
    rw [naturalIntensional_actualRules]
    exact ComputationProfiles.NaturalConversion.sigma_boundary
  preserves := by
    intro n context source target type judgment steps
    rw [naturalIntensional_actualRules] at judgment steps ⊢
    exact ComputationProfiles.NaturalConversion.Preservation.steps_preserve
      judgment steps

/-- Concrete positive control: the certified conversion makes the natural
carrier disjoint from every dependent function type, even through paths that
leave the constructor image. -/
theorem naturalIntensional_nat_not_pi {n : Nat}
    (domain : Tower.Tm n) (codomain : Tower.Tm (n + 1)) :
    ¬ Conv (actualRules naturalIntensional).headEq natTm (.pi domain codomain)
      (actualRules naturalIntensional).computation := by
  rw [naturalIntensional_actualRules]
  exact ComputationProfiles.NaturalConversion.natural_not_pi domain codomain

/-- The raw operational sibling is valid profile data but still lacks an
unrestricted lift into annotated vector computation.  This is an interaction
obligation independent of its receipt flags. -/
theorem fullRawOperational_not_annotatedInteraction :
    ¬ ∀ {n : Nat} (left : CTm Tower.Head n) (right : Tower.Tm n),
      (ComputationProfiles.rules (fun _ => true)).computation.step left.erase right →
        ∃ result, (Annotated.church (fun _ => true)).computation.step left result ∧
          result.erase = right :=
  fullRawOperational_not_unrestrictedAnnotatedLift

#print axioms naturalIntensional_actualRules
#print axioms naturalIntensional_roots_exact
#print axioms naturalIntensionalCertificate
#print axioms naturalIntensional_nat_not_pi
#print axioms fullRawOperational_not_annotatedInteraction

end Programs.CheckingProfiles.Interaction
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies
