import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeCertifiedProjection

/-!
# Generated cube declarations realize the actual free code/kinding model

The original native parser reads every computed declaration header and result
in the independently constructed free code presheaf and kinding fibres.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativePresheafRealization

open _root_.CategoryTheory Opposite
open CubeEnrichment
open Mettapedia.TypeTheory
open ContextualLocalUniverses ContextualModelTelescopes NativeLocalTypeFormers
open Calculi.NativeDependent.Refinement
open CubeNativeDeclarations CubeNativeSemanticFamilies CubeNativeSemanticOperations
open CubeNativeSemanticArguments CubeNativePresheafModel CubeNativePresheafReadout
open CubeNativeSemanticVectors CubeNativeCertifiedProjection

universe u
variable {D : CubeEnrichment.Signature} {W : Type u} [Category.{u} W]
variable (operational : D.Carrier → Wᵒᵖ ⥤ Type u) (vertex : Vertex D)

noncomputable section

theorem former_read {n : Nat} (context : Scope W n) (declaration : D.Former)
    (arguments : Fin (D.arity declaration) → TermExpr (symbols D) n)
    (names : ∀ position, context.1 ⟶ CubePresheafCode.presheaf operational (D.input declaration position))
    (reads : ∀ position, (model operational vertex).evaluateTerm context (arguments position) =
      some (codeValue operational (D.input declaration position) (names position))) :
    (model operational vertex).evaluateTerm context (.primitive (.former declaration) arguments) =
      some (codeValue operational (D.output declaration) (formerName operational declaration names)) := by
  have read := (model operational vertex).evaluate_primitive context (.former declaration) arguments
    (vectorMap operational (D.input declaration) names)
    (fun position => (reads position).trans (congrArg some
      (vectorMap_components operational (D.input declaration) names position).symm))
  exact read.trans (congrArg some (formerValue_vectorMap operational declaration names))

theorem formedCode_read (declaration : D.Former) :
    (model operational vertex).evaluateTerm (formationScope operational vertex declaration)
      (CubeNativeDeclarations.formedCode vertex declaration) =
      some (codeValue operational (D.output declaration) (formationOutputName operational vertex declaration)) :=
  former_read operational vertex _ declaration _ _
    (fun position => codeArgument_read operational vertex declaration position)

theorem formationResult_read (declaration : D.Former) :
    (model operational vertex).evaluateType (formationScope operational vertex declaration)
      (CubeNativeDeclarations.formationResult vertex declaration) =
      some (formationType operational vertex declaration) :=
  typing_read operational vertex _ _ _ _ _ _
    (formedCode_read operational vertex declaration)
    (sort_read operational vertex _ _ _)

theorem starBoxResult_read (carrier : D.Carrier) :
    (model operational vertex).evaluateType CubeNativeSemanticFamilies.emptyScope
      (typingType carrier (sortCode carrier .star 0) (sortCode carrier .box 0)) =
      some (starBoxType operational vertex carrier) :=
  typing_read operational vertex _ _ _ _ _ _
    (sort_read operational vertex _ _ _) (sort_read operational vertex _ _ _)

/-- The actual native declaration model obeys every computed raw header and
result. Its kinding fibre is the independently defined cube judgment. -/
theorem realization : SignatureRealization (model operational vertex) (signature vertex) where
  typeHeader symbol := by
    cases symbol with
    | code => rfl
    | typing carrier => exact typing_context_read operational vertex carrier
  termHeader symbol := by
    cases symbol with
    | sort => rfl
    | starBox => rfl
    | former declaration => exact parameter_context_read operational vertex declaration
    | formation declaration => exact formation_context_read operational vertex declaration
  predicateHeader symbol := nomatch symbol
  termResult symbol := by
    cases symbol with
    | sort carrier _ => exact code_read operational vertex _ carrier
    | former declaration => exact code_read operational vertex _ (D.output declaration)
    | starBox carrier => exact starBoxResult_read operational vertex carrier
    | formation declaration => exact formationResult_read operational vertex declaration

end

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativePresheafRealization
