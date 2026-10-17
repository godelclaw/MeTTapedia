import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.ContinuationSyntax
import Mettapedia.OSLF.NativeTypes.Semantics.Classifier.Realization
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSoundness
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.IndexSemantics
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.ResponseSemantics

/-!
# Semantic requests and dependent targets from the generated continuation

The actual generated parameter and request contexts are interpreted by the
shared native dependent evaluator. Every rely binds a code value followed
by its membership evidence. Applying the mandatory continuation in that
context yields a certified classifier at the declared target carrier.
No restriction to operational values is imposed on these native requests.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.ContinuationSemantics

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Calculi.NativeDependent.Refinement
open NativeLocalTypeFormers DisplayedPresheafComprehension
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.OSLF.NativeTypes.Semantics
open Presheaf CubeEnrichment CubeNativeDeclarations
open Classifier Families Operations CertifiedProjection

universe u
variable {D : CubeEnrichment.Signature} {W : Type u} [Category.{u} W]
variable (operational : D.Carrier → Wᵒᵖ ⥤ Type u)
    (algebra : StructuralImages.Algebra operational) (vertex : Vertex D)

noncomputable section

abbrev semanticModel := Classifier.Model.model operational algebra vertex
abbrev realization := Classifier.Realization.realization operational algebra vertex

def scopeOf {n : Nat} (context : ContextExpr (symbols D) n)
    (formed : Derivation (Theory vertex) (.context context)) : Scope W n :=
  Classical.choose (formed.native_sound (semanticModel operational algebra vertex)
    (realization operational algebra vertex))

theorem scopeOf_read {n : Nat} (context : ContextExpr (symbols D) n)
    (formed : Derivation (Theory vertex) (.context context)) :
    (semanticModel operational algebra vertex).evaluateContext context =
      some (scopeOf operational algebra vertex context formed) :=
  Classical.choose_spec (formed.native_sound (semanticModel operational algebra vertex)
    (realization operational algebra vertex))

variable (interface : Interface D.Carrier)

def parameterScope : Scope W (arity interface) :=
  scopeOf operational algebra vertex (parameters interface) (parametersFormed vertex interface)

theorem parameters_read :
    (semanticModel operational algebra vertex).evaluateContext (parameters interface) =
      some (parameterScope operational algebra vertex interface) :=
  scopeOf_read operational algebra vertex _ _

abbrev requestSyntax := ContinuationSyntax.generated vertex interface

def requestScope : Scope W (requestSyntax vertex interface).size :=
  scopeOf operational algebra vertex (requestSyntax vertex interface).scope
    (requestSyntax vertex interface).formed

theorem requests_read :
    (semanticModel operational algebra vertex).evaluateContext (requestSyntax vertex interface).scope =
      some (requestScope operational algebra vertex interface) :=
  scopeOf_read operational algebra vertex _ _

def projection : (requestScope operational algebra vertex interface).1 ⟶
    (parameterScope operational algebra vertex interface).1 :=
  Classical.choose
    (((requestSyntax vertex interface).projectionTyped.native_sound
      (semanticModel operational algebra vertex) (realization operational algebra vertex)).substitutionAt
      (requestScope operational algebra vertex interface) (parameterScope operational algebra vertex interface)
      (requests_read operational algebra vertex interface) (parameters_read operational algebra vertex interface))

theorem projection_read :
    (semanticModel operational algebra vertex).evaluateSubstitution
      (requestScope operational algebra vertex interface) (parameterScope operational algebra vertex interface)
      (requestSyntax vertex interface).projection =
        some (projection operational algebra vertex interface) :=
  Classical.choose_spec
    (((requestSyntax vertex interface).projectionTyped.native_sound
      (semanticModel operational algebra vertex) (realization operational algebra vertex)).substitutionAt
      (requestScope operational algebra vertex interface) (parameterScope operational algebra vertex interface)
      (requests_read operational algebra vertex interface) (parameters_read operational algebra vertex interface))

def targetSection :
    (certifiedAt operational interface.target interface.resultSort
      (requestScope operational algebra vertex interface).1).decoded.sections :=
  Classical.choose
    (((requestSyntax vertex interface).outputTyped.native_sound
      (semanticModel operational algebra vertex) (realization operational algebra vertex)).termAt
      (requestScope operational algebra vertex interface)
      (certifiedAt operational interface.target interface.resultSort
        (requestScope operational algebra vertex interface).1)
      (requests_read operational algebra vertex interface)
      (Classifier.Realization.certified_read operational algebra vertex _ _ _))

/-- This is the evaluation of the generated continuation applied to every
bound value and evidence, rather than a separately supplied target oracle. -/
theorem target_evaluates :
    (semanticModel operational algebra vertex).evaluateTerm
      (requestScope operational algebra vertex interface) (requestSyntax vertex interface).output =
      some ⟨certifiedAt operational interface.target interface.resultSort
        (requestScope operational algebra vertex interface).1,
        targetSection operational algebra vertex interface⟩ :=
  Classical.choose_spec
    (((requestSyntax vertex interface).outputTyped.native_sound
      (semanticModel operational algebra vertex) (realization operational algebra vertex)).termAt
      (requestScope operational algebra vertex interface)
      (certifiedAt operational interface.target interface.resultSort
        (requestScope operational algebra vertex interface).1)
      (requests_read operational algebra vertex interface)
      (Classifier.Realization.certified_read operational algebra vertex _ _ _))

def targetCertified : (requestScope operational algebra vertex interface).1 ⟶
    validPresheaf operational interface.target interface.resultSort :=
  sectionLift (certifiedAt operational interface.target interface.resultSort
    (requestScope operational algebra vertex interface).1).decoded
    (targetSection operational algebra vertex interface) ≫
      certifiedGeneric operational interface.target interface.resultSort

def targetCode : (requestScope operational algebra vertex interface).1 ⟶
    Carrier.presheaf operational interface.target :=
  targetCertified operational algebra vertex interface ≫
    validInclusion operational interface.target interface.resultSort

theorem targetCode_valid (world : Wᵒᵖ)
    (request : (requestScope operational algebra vertex interface).1.obj world) :
    Code.Member ((targetCode operational algebra vertex interface).app world request)
      (.sort interface.resultSort) :=
  ((targetCertified operational algebra vertex interface).app world request).property

def codeSectionOf {n : Nat} (scope : Scope W n) (context : ContextExpr (symbols D) n)
    (contextRead : (semanticModel operational algebra vertex).evaluateContext context = some scope)
    (carrier : D.Carrier) (term : TermExpr (symbols D) n)
    (typed : Derivation (Theory vertex) (.term context term (codeType carrier n))) :
    (codeAt operational carrier scope.1).decoded.sections :=
  Classical.choose
    ((typed.native_sound (semanticModel operational algebra vertex)
      (realization operational algebra vertex)).termAt scope (codeAt operational carrier scope.1)
      contextRead (Classifier.Realization.code_read operational algebra vertex scope carrier))

theorem codeSectionOf_evaluates {n : Nat} (scope : Scope W n) (context : ContextExpr (symbols D) n)
    (contextRead : (semanticModel operational algebra vertex).evaluateContext context = some scope)
    (carrier : D.Carrier) (term : TermExpr (symbols D) n)
    (typed : Derivation (Theory vertex) (.term context term (codeType carrier n))) :
    (semanticModel operational algebra vertex).evaluateTerm scope term =
      some ⟨codeAt operational carrier scope.1,
        codeSectionOf operational algebra vertex scope context contextRead carrier term typed⟩ :=
  Classical.choose_spec
    ((typed.native_sound (semanticModel operational algebra vertex)
      (realization operational algebra vertex)).termAt scope (codeAt operational carrier scope.1)
      contextRead (Classifier.Realization.code_read operational algebra vertex scope carrier))

theorem codeSectionName_value {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier)
    (value : (codeAt operational carrier P).decoded.sections) :
    (⟨codeAt operational carrier P, value⟩ : NativeValue P) =
      Classifier.Arguments.codeValue operational carrier (sectionName operational carrier value) := rfl

def relyPosition (position : Fin interface.relies.length) : Fin (relyArguments interface).length :=
  ⟨position.val, by simpa only [relyArguments, List.length_ofFn] using position.isLt⟩

theorem relyEntry (position : Fin interface.relies.length) :
    (relyArguments interface)[relyPosition interface position] =
      (interface.relies[position].1, classifierValue interface.relies[position].1 interface.relies[position].2
        (.var (position.castAdd interface.indices.length))) := by
  change (List.ofFn (fun position : Fin interface.relies.length =>
    (interface.relies[position].1, classifierValue interface.relies[position].1 interface.relies[position].2
      (.var (position.castAdd interface.indices.length))))).get (relyPosition interface position) = _
  rw [List.get_ofFn]
  rfl

def relyValueTerm (position : Fin interface.relies.length) :=
  (requestSyntax vertex interface).values (relyPosition interface position)

def relyValueTyped (position : Fin interface.relies.length) :
    Derivation (Theory vertex) (.term (requestSyntax vertex interface).scope
      (relyValueTerm vertex interface position)
      (codeType interface.relies[position].1 (requestSyntax vertex interface).size)) := by
  have tree := (requestSyntax vertex interface).valueTyped (relyPosition interface position)
  rw [relyEntry] at tree
  exact tree

def relyValueSection (position : Fin interface.relies.length) :
    (codeAt operational interface.relies[position].1
      (requestScope operational algebra vertex interface).1).decoded.sections :=
  codeSectionOf operational algebra vertex (requestScope operational algebra vertex interface)
    (requestSyntax vertex interface).scope (requests_read operational algebra vertex interface)
    interface.relies[position].1 (relyValueTerm vertex interface position) (relyValueTyped vertex interface position)

def relyCode (position : Fin interface.relies.length) :
    (requestScope operational algebra vertex interface).1 ⟶ Carrier.presheaf operational interface.relies[position].1 :=
  sectionName operational interface.relies[position].1
    (relyValueSection operational algebra vertex interface position)

theorem relyValue_evaluates (position : Fin interface.relies.length) :
    (semanticModel operational algebra vertex).evaluateTerm
      (requestScope operational algebra vertex interface) (relyValueTerm vertex interface position) =
      some ⟨codeAt operational interface.relies[position].1
        (requestScope operational algebra vertex interface).1,
        relyValueSection operational algebra vertex interface position⟩ :=
  codeSectionOf_evaluates operational algebra vertex _ _ _ _ _ _

def indexValueTerm (position : Fin interface.indices.length) :=
  IndexSyntax.value interface.indices[position].1 interface.indices[position].2
    (ContinuationSyntax.indexRequestTerm vertex interface position)

def indexValueTyped (position : Fin interface.indices.length) :
    Derivation (Theory vertex) (.term (requestSyntax vertex interface).scope
      (indexValueTerm vertex interface position)
      (codeType interface.indices[position].1 (requestSyntax vertex interface).size)) :=
  IndexSyntax.valueTyped vertex interface.indices[position].1 interface.indices[position].2
    (requestSyntax vertex interface).formed (ContinuationSyntax.indexRequestTyped vertex interface position)

def indexReading (position : Fin interface.indices.length) :
    IndexSemantics.Reading operational algebra vertex
      (requestScope operational algebra vertex interface)
      interface.indices[position].1 interface.indices[position].2
      (ContinuationSyntax.indexRequestTerm vertex interface position) :=
  IndexSemantics.read operational algebra vertex (requestSyntax vertex interface).formed
    (ContinuationSyntax.indexRequestTyped vertex interface position)
    (requestScope operational algebra vertex interface) (requests_read operational algebra vertex interface)

def indexValueSection (position : Fin interface.indices.length) :
    (codeAt operational interface.indices[position].1
      (requestScope operational algebra vertex interface).1).decoded.sections :=
  Classifier.Families.codeSection operational interface.indices[position].1
    (indexReading operational algebra vertex interface position).value

def indexCode (position : Fin interface.indices.length) :
    (requestScope operational algebra vertex interface).1 ⟶ Carrier.presheaf operational interface.indices[position].1 :=
  (indexReading operational algebra vertex interface position).value

theorem indexValue_evaluates (position : Fin interface.indices.length) :
    (semanticModel operational algebra vertex).evaluateTerm
      (requestScope operational algebra vertex interface) (indexValueTerm vertex interface position) =
      some ⟨codeAt operational interface.indices[position].1
        (requestScope operational algebra vertex interface).1,
        indexValueSection operational algebra vertex interface position⟩ :=
  (indexReading operational algebra vertex interface position).valueRead

def indexClassifierTerm (position : Fin interface.indices.length) :=
  IndexSyntax.classifier interface.indices[position].1 interface.indices[position].2
    (ContinuationSyntax.indexRequestTerm vertex interface position)

def indexClassifierCode (position : Fin interface.indices.length) :
    (requestScope operational algebra vertex interface).1 ⟶ Carrier.presheaf operational interface.indices[position].1 :=
  (indexReading operational algebra vertex interface position).classifier

theorem indexClassifier_evaluates (position : Fin interface.indices.length) :
    (semanticModel operational algebra vertex).evaluateTerm
      (requestScope operational algebra vertex interface) (indexClassifierTerm vertex interface position) =
      some (Classifier.Arguments.codeValue operational interface.indices[position].1
        (indexClassifierCode operational algebra vertex interface position)) :=
  (indexReading operational algebra vertex interface position).classifierRead

/-- Index classification uses the actual projected membership witness of
the generated dependent bundle. -/
theorem indexCode_member (position : Fin interface.indices.length) (world : Wᵒᵖ)
    (request : (requestScope operational algebra vertex interface).1.obj world) :
    Code.Member ((indexCode operational algebra vertex interface position).app world request)
      ((indexClassifierCode operational algebra vertex interface position).app world request) :=
  (indexReading operational algebra vertex interface position).member world request

theorem indexClassifierCode_valid (position : Fin interface.indices.length) (world : Wᵒᵖ)
    (request : (requestScope operational algebra vertex interface).1.obj world) :
    Code.Member ((indexClassifierCode operational algebra vertex interface position).app world request)
      (.sort interface.indices[position].2) :=
  (indexReading operational algebra vertex interface position).kinded world request

/-- All maps are obtained from the original parameter and application
syntax through the genuine native interpreter and its soundness theorem. -/
def requests : ResponseSemantics.Requests operational interface where
  parameters := parameterScope operational algebra vertex interface
  values := (requestScope operational algebra vertex interface).1
  project := projection operational algebra vertex interface
  indices := indexCode operational algebra vertex interface
  relies := relyCode operational algebra vertex interface
  target := targetCode operational algebra vertex interface

end
end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.ContinuationSemantics
