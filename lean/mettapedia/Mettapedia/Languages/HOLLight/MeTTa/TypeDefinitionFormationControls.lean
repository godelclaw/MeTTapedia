import Mettapedia.Languages.HOLLight.MeTTa.TypeDefinitionFormation
import Mettapedia.Languages.HOLLight.ProofExecution

/-! Concrete registration and missing-declaration controls for the general
source output-formation and derivation construction. -/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.TypeDefinitionFormationControls

open Mettapedia.Languages.OpenTheory
open SignatureFormation DefinitionAdapters
open DefinitionAdapters.ContextControls
open ProofExecution.Registered.Controls

/-- The existence premise comes from an actually replayed reflexivity
command, without any object-theory axiom commitment. -/
theorem identity_existence_earned : TheoryDerives emptyAxiomPolicy coreContext identityExistence := by
  exact withExistence_valid identityExistence (by simp [withExistence])

/-- The general construction establishes both pointwise laws for a new
carrier of Boolean identity functions. It does not reuse the control's
separate output-formation checks. -/
theorem identity_type_laws_earned :
    TheoryDerives emptyAxiomPolicy definedType.context definedType.output.abstractionRepresentationTheorem ∧
      TheoryDerives emptyAxiomPolicy definedType.context definedType.output.representationAbstractionTheorem := by
  apply TypeDefinitionFormation.source_outputs_derived emptyAxiomPolicy coreContext
    ProofExecution.Registered.Controls.certificates identityTypeRequest identityPredicate
    DefinitionAdapters.Controls.identityTerm identityType_application rfl definedType defined_type_admitted
    identity_existence_earned (core_includes.1 _ _ function_registered)
    (boolean_formed.mono core_includes) equalityParameter
  exact baseContext.addConstant_registered Const.equality (Ty.equality (.var equalityParameter))
    equality_schema_formed (by
      simp [baseContext, booleanContext, TheoryContext.addTypeOperator, TheoryContext.empty,
        constantName, Const.equality])

/-- A context with the Boolean and function operators alone cannot form an
equality theorem merely because its operands are well typed. -/
theorem undeclared_equality_refused :
    ¬ AnnotationsFormed baseContext.signature
      (CanonicalTerm.equalityDB Ty.bool (.free ⟨Name.global "p", Ty.bool⟩)
        (.free ⟨Name.global "p", Ty.bool⟩)) := by
  apply TypeDefinitionFormation.absent_equality_refuses_equation
  rfl

end Mettapedia.Languages.HOLLight.MeTTa.TypeDefinitionFormationControls
