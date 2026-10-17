import Mettapedia.OSLF.NativeTypes.Semantics.Classifier.StructuralImages
import Mettapedia.OSLF.NativeTypes.Semantics.Classifier.CertifiedProjection

/-!
# The generated constructor-classifier signature in the original presheaves

Constructor classifiers are actual images of natural authored operations.
The shared dependent evaluator receives independent code and membership
families, actual parameter telescopes and constructed formation sections.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Classifier.Model

open _root_.CategoryTheory Opposite
open Presheaf CubeEnrichment CubeNativeDeclarations
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.TypeTheory
open ContextualLocalUniverses ContextualModelTelescopes NativeLocalTypeFormers
open Calculi.NativeDependent.Refinement
open Families Operations Arguments Vectors

universe u
variable {D : CubeEnrichment.Signature} {W : Type u} [Category.{u} W]
variable (operational : D.Carrier → Wᵒᵖ ⥤ Type u)
variable (algebra : StructuralImages.Algebra operational) (vertex : Vertex D)

noncomputable section

abbrev parameterTypes (declaration : D.Former) :=
  fun position => codeMeaning operational (D.input declaration position)

abbrev parameterScope (declaration : D.Former) : Scope W (D.arity declaration) :=
  CubeNativeSemanticTelescopes.vectorScope (parameterTypes operational declaration)

def parameterName (declaration : D.Former) (position : Fin (D.arity declaration)) :
    (parameterScope operational declaration).1 ⟶ Carrier.presheaf operational (D.input declaration position) :=
  sectionName operational (D.input declaration position)
    (CubeNativeSemanticTelescopes.lookupSection (parameterTypes operational declaration) position)

abbrev formerType (declaration : D.Former) :=
  codeAt operational (D.output declaration) (parameterScope operational declaration).1

abbrev formerValue (declaration : D.Former) :=
  codeSection operational (D.output declaration)
    (StructuralImages.formerName operational algebra vertex declaration (parameterName operational declaration))

abbrev formationTypes (declaration : D.Former) :=
  fun position => certifiedMeaning operational (D.input declaration position)
    (inputSort D vertex declaration position)

abbrev formationScope (declaration : D.Former) : Scope W (D.arity declaration) :=
  CubeNativeSemanticTelescopes.vectorScope (formationTypes operational vertex declaration)

def formationParameterName (declaration : D.Former) (position : Fin (D.arity declaration)) :
    (formationScope operational vertex declaration).1 ⟶
      validPresheaf operational (D.input declaration position) (inputSort D vertex declaration position) :=
  closedReadSection _ (certifiedRead operational (D.input declaration position)
    (inputSort D vertex declaration position))
    (CubeNativeSemanticTelescopes.lookupSection (formationTypes operational vertex declaration) position)

abbrev formationCodeNames (declaration : D.Former) :=
  fun position => formationParameterName operational vertex declaration position ≫
    validInclusion operational (D.input declaration position) (inputSort D vertex declaration position)

abbrev formationOutputName (declaration : D.Former) :=
  StructuralImages.formerName operational algebra vertex declaration (formationCodeNames operational vertex declaration)

abbrev formationType (declaration : D.Former) :=
  typingAt operational (D.output declaration) (formationOutputName operational algebra vertex declaration)
    (sortName operational (D.output declaration) (outputSort D vertex declaration))

def formationValue (declaration : D.Former) :
    (formationType operational algebra vertex declaration).decoded.sections :=
  memberSection operational (D.output declaration)
    (formationOutputName operational algebra vertex declaration)
    (sortName operational (D.output declaration) (outputSort D vertex declaration)) (fun _ _ => rfl)

abbrev typeScope (symbol : TypeSymbol D) : Scope W ((symbols D).typeArity symbol) :=
  match symbol with
  | .code _ => Families.emptyScope
  | .typing carrier => typingScope operational carrier

abbrev typeMeaning (symbol : TypeSymbol D) : NativeType (typeScope operational symbol).1 :=
  match symbol with
  | .code carrier => codeMeaning operational carrier
  | .typing carrier => typingMeaning operational carrier

abbrev termScope (symbol : TermSymbol D) : Scope W ((symbols D).termArity symbol) :=
  match symbol with
  | .sort _ _ | .starBox _ => Families.emptyScope
  | .former declaration => parameterScope operational declaration
  | .formation declaration => formationScope operational vertex declaration

abbrev termMeaning (symbol : TermSymbol D) : NativeType (termScope operational vertex symbol).1 :=
  match symbol with
  | .sort carrier _ => codeAt operational carrier Families.emptyScope.1
  | .former declaration => formerType operational declaration
  | .starBox carrier => starBoxType operational carrier
  | .formation declaration => formationType operational algebra vertex declaration

abbrev termSection (symbol : TermSymbol D) : (termMeaning operational algebra vertex symbol).decoded.sections :=
  match symbol with
  | .sort carrier kind => sortValue operational carrier kind
  | .former declaration => formerValue operational algebra vertex declaration
  | .starBox carrier => starBoxValue operational carrier
  | .formation declaration => formationValue operational algebra vertex declaration

def model : ModelData (symbols D) W where
  typeParameters := typeScope operational
  typeFamily := typeMeaning operational
  termParameters := termScope operational vertex
  termType := termMeaning operational algebra vertex
  termValue := termSection operational algebra vertex
  predicateParameters symbol := nomatch symbol
  predicateValue symbol := nomatch symbol

end
end Mettapedia.OSLF.NativeTypes.Semantics.Classifier.Model
