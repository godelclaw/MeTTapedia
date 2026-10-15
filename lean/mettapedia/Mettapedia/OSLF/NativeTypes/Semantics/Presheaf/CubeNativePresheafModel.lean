import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeSemanticArguments

/-!
# Complete cube alphabet interpreted by actual free presheaf enrichment

Every generated native code/kinding declaration is interpreted by its actual
free code object, independent kinding fibre or constructed formation section.
The header/result parser comparison is proved separately.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativePresheafModel

open _root_.CategoryTheory Opposite
open CubeEnrichment
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.TypeTheory
open ContextualLocalUniverses ContextualModelTelescopes NativeLocalTypeFormers
open Calculi.NativeDependent.Refinement
open CubeNativeDeclarations CubeNativeSemanticFamilies CubeNativeSemanticOperations

universe u
variable {D : CubeEnrichment.Signature} {W : Type u} [Category.{u} W]
variable (operational : D.Carrier → Wᵒᵖ ⥤ Type u) (vertex : Vertex D)

noncomputable section

abbrev typeScope (symbol : TypeSymbol D) : Scope W ((symbols D).typeArity symbol) :=
  match symbol with
  | .code _ => CubeNativeSemanticFamilies.emptyScope
  | .typing carrier => typingScope operational carrier

abbrev typeMeaning (symbol : TypeSymbol D) : NativeType (typeScope operational symbol).1 :=
  match symbol with
  | .code carrier => codeMeaning operational carrier
  | .typing carrier => typingMeaning operational vertex carrier

abbrev termScope (symbol : TermSymbol D) : Scope W ((symbols D).termArity symbol) :=
  match symbol with
  | .sort _ _ | .starBox _ => CubeNativeSemanticFamilies.emptyScope
  | .former declaration => parameterScope operational declaration
  | .formation declaration => formationScope operational vertex declaration

abbrev termMeaning (symbol : TermSymbol D) : NativeType (termScope operational vertex symbol).1 :=
  match symbol with
  | .sort carrier _ => codeAt operational carrier CubeNativeSemanticFamilies.emptyScope.1
  | .former declaration => formerType operational declaration
  | .starBox carrier => starBoxType operational vertex carrier
  | .formation declaration => formationType operational vertex declaration

abbrev termSection (symbol : TermSymbol D) : (termMeaning operational vertex symbol).decoded.sections :=
  match symbol with
  | .sort carrier kind => sortValue operational carrier kind
  | .former declaration => formerValue operational declaration
  | .starBox carrier => starBoxValue operational vertex carrier
  | .formation declaration => formationValue operational vertex declaration

/-- No arbitrary sort-domain interpretation or typing-predicate oracle occurs
in this complete model of the generated declarations. -/
def model : ModelData (symbols D) W where
  typeParameters := typeScope operational
  typeFamily := typeMeaning operational vertex
  termParameters := termScope operational vertex
  termType := termMeaning operational vertex
  termValue := termSection operational vertex
  predicateParameters symbol := nomatch symbol
  predicateValue symbol := nomatch symbol

end

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativePresheafModel
