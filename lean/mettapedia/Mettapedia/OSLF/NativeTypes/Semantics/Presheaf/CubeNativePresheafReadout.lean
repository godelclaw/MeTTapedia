import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativePresheafModel

/-!
# Original native parser reads the independent cube enrichment

The actual raw syntax is evaluated by the existing common native interpreter.
Code and typing-family reads preserve the ordered semantic arguments, and the
closed certified code declarations parse to their constructed Sigma meanings.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativePresheafReadout

open _root_.CategoryTheory Opposite
open CubeEnrichment
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.TypeTheory
open ContextualLocalUniverses ContextualModelTelescopes NativeLocalTypeFormers
open Calculi.NativeDependent.Refinement
open CubeNativeDeclarations CubeNativeSemanticFamilies CubeNativeSemanticOperations
open CubeNativeSemanticArguments CubeNativePresheafModel

universe u
variable {D : CubeEnrichment.Signature} {W : Type u} [Category.{u} W]
variable (operational : D.Carrier → Wᵒᵖ ⥤ Type u) (vertex : Vertex D)

noncomputable section

theorem code_read {n : Nat} (scope : Scope W n) (carrier : D.Carrier) :
    (model operational vertex).evaluateType scope (codeType carrier n) =
      some (codeAt operational carrier scope.1) :=
  (model operational vertex).evaluate_family scope (.code carrier) Fin.elim0
    ((NativeModel W).toEmpty scope.1) (fun position => Fin.elim0 position)

theorem code_empty_read (carrier : D.Carrier) :
    (model operational vertex).evaluateType CubeNativeSemanticFamilies.emptyScope (codeType carrier 0) =
      some (codeMeaning operational carrier) := by
  have read := code_read operational vertex CubeNativeSemanticFamilies.emptyScope carrier
  have identity : (NativeModel W).toEmpty (CubeNativeSemanticFamilies.emptyScope (W := W)).1 =
      (NativeModel W).toCwf.idS CubeNativeSemanticFamilies.emptyScope.1 :=
    ((NativeModel W).toEmpty_unique _ _).symm
  change (model operational vertex).evaluateType _ (codeType carrier 0) =
    some ((codeMeaning operational carrier).reindex _) at read
  exact read.trans (congrArg some
    ((congrArg (fun map => (codeMeaning operational carrier).reindex map) identity).trans
      (LocalType.reindex_id (C := DisplayedPresheafCwf.presheafCwf W) (codeMeaning operational carrier))))

theorem code_context_read (carrier : D.Carrier) :
    (model operational vertex).evaluateContext (.snoc .nil (codeType carrier 0)) =
      some (codeScope operational carrier) :=
  (model operational vertex).evaluateContext_snoc .nil (codeType carrier 0)
    CubeNativeSemanticFamilies.emptyScope (codeMeaning operational carrier) rfl
    (code_empty_read operational vertex carrier)

theorem typing_context_read (carrier : D.Carrier) :
    (model operational vertex).evaluateContext (CubeNativeDeclarations.typingContext carrier) =
      some (typingScope operational carrier) :=
  (model operational vertex).evaluateContext_snoc _ (codeType carrier 1) _ _
    (code_context_read operational vertex carrier) (code_read operational vertex _ carrier)

theorem sort_substitution {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier) (kind : HSort) :
    Value.substitute (K := (NativeModel W).toCwf)
      (⟨codeAt operational carrier CubeNativeSemanticFamilies.emptyScope.1,
        sortValue operational carrier kind⟩ : NativeValue CubeNativeSemanticFamilies.emptyScope.1)
      ((NativeModel W).toEmpty P) = codeValue operational carrier (sortName operational carrier kind) := by
  apply Sigma.ext
  · exact CubeNativeSemanticTelescopes.closed_weaken _ _
  · rfl

theorem sort_read {n : Nat} (scope : Scope W n) (carrier : D.Carrier) (kind : HSort) :
    (model operational vertex).evaluateTerm scope (sortCode carrier kind n) =
      some (codeValue operational carrier (sortName operational carrier kind)) := by
  have read := (model operational vertex).evaluate_primitive scope (.sort carrier kind) Fin.elim0
    ((NativeModel W).toEmpty scope.1) (fun position => Fin.elim0 position)
  exact read.trans (congrArg some (sort_substitution operational carrier kind))

theorem typing_read {n : Nat} (scope : Scope W n) (carrier : D.Carrier)
    (first second : TermExpr (symbols D) n)
    (code type : scope.1 ⟶ CubePresheafCode.presheaf operational carrier)
    (firstRead : (model operational vertex).evaluateTerm scope first = some (codeValue operational carrier code))
    (secondRead : (model operational vertex).evaluateTerm scope second = some (codeValue operational carrier type)) :
    (model operational vertex).evaluateType scope (typingType carrier first second) =
      some (typingAt operational vertex carrier code type) := by
  apply (model operational vertex).evaluate_family scope (.typing carrier)
    (Fin.cases first (fun _ => second)) (pairArguments operational carrier code type)
  intro position
  cases position using Fin.cases with
  | zero => exact firstRead.trans (congrArg some (pair_component_zero operational carrier code type).symm)
  | succ position =>
      have last : position = 0 := Fin.eq_zero position
      cases last
      exact secondRead.trans (congrArg some (pair_component_one operational carrier code type).symm)

theorem code_variable_read (carrier : D.Carrier) :
    (model operational vertex).evaluateTerm (codeScope operational carrier) (.var 0) =
      some (codeValue operational carrier (codeVariableName operational carrier)) := by
  apply congrArg some
  apply Sigma.ext
  · rfl
  · rfl

theorem certified_body_read (carrier : D.Carrier) (kind : HSort) :
    (model operational vertex).evaluateType (codeScope operational carrier)
      (typingType carrier (.var 0) (sortCode carrier kind 1)) =
        some (certifiedBody operational vertex carrier kind) :=
  typing_read operational vertex _ carrier _ _ _ _ (code_variable_read operational vertex carrier)
    (sort_read operational vertex _ carrier kind)

theorem certified_empty_read (carrier : D.Carrier) (kind : HSort) :
    (model operational vertex).evaluateType CubeNativeSemanticFamilies.emptyScope
      (certifiedCode carrier kind 0) = some (certifiedMeaning operational vertex carrier kind) :=
  (model operational vertex).evaluate_sigma CubeNativeSemanticFamilies.emptyScope _ _ _ _
    (code_empty_read operational vertex carrier) (certified_body_read operational vertex carrier kind)

theorem parameter_context_read (declaration : D.Former) :
    (model operational vertex).evaluateContext (CubeNativeDeclarations.parameterContext declaration) =
      some (parameterScope operational declaration) :=
  CubeNativeSemanticTelescopes.vector_read (model operational vertex) _ _
    (fun position => code_empty_read operational vertex (D.input declaration position))

theorem formation_context_read (declaration : D.Former) :
    (model operational vertex).evaluateContext (CubeNativeDeclarations.formationContext vertex declaration) =
      some (formationScope operational vertex declaration) :=
  CubeNativeSemanticTelescopes.vector_read (model operational vertex) _ _
    (fun position => certified_empty_read operational vertex (D.input declaration position)
      (inputSort D vertex declaration position))

end

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativePresheafReadout
