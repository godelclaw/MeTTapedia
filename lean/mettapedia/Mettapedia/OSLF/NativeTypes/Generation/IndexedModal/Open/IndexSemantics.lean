import Mettapedia.OSLF.NativeTypes.Semantics.Classifier.Realization
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.IndexSyntax
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSoundness

/-!
# Actual dependent index bundles in the shared native interpreter

The index classifier, its selected code value and membership witness remain
separate dependent components. The semantic construction uses native Sigma
and the independently built membership family; the parser comparison uses
the original generated index syntax and first-projection evaluator.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.IndexSemantics

open _root_.CategoryTheory Opposite
open Mettapedia.OSLF.NativeTypes.Semantics
open Presheaf CubeEnrichment CubeNativeDeclarations Classifier
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.TypeTheory Calculi.NativeDependent.Refinement
open NativeLocalTypeFormers ContextualLocalUniverses ContextualModelTelescopes
open DisplayedPresheafComprehension
open Classifier.Families Classifier.Operations Classifier.Arguments

universe u
variable {D : CubeEnrichment.Signature} {W : Type u} [Category.{u} W]
variable (operational : D.Carrier → Wᵒᵖ ⥤ Type u)
variable (algebra : StructuralImages.Algebra operational) (vertex : Vertex D)

noncomputable section

attribute [local irreducible] Classifier.Model.model

private theorem value_cast {P : Wᵒᵖ ⥤ Type u} {first second : NativeType P}
    (same : first = second) (value : first.decoded.sections) :
    (⟨first, value⟩ : NativeValue P) =
      ⟨second, cast (congrArg ((NativeModel W).toCwf.Tm P) same) value⟩ :=
  Sigma.ext same (cast_heq _ _).symm

abbrev model := Classifier.Model.model operational algebra vertex

def readClassifier {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier) (kind : HSort)
    (value : (CertifiedProjection.certifiedAt operational carrier kind P).decoded.sections) :
    P ⟶ Carrier.presheaf operational carrier :=
  closedReadSection (certifiedMeaning operational carrier kind)
    (certifiedRead operational carrier kind) value ≫ validInclusion operational carrier kind

theorem classifierValue_read {n : Nat} (context : Scope W n) (carrier : D.Carrier) (kind : HSort)
    (expression : TermExpr (symbols D) n)
    (value : (CertifiedProjection.certifiedAt operational carrier kind context.1).decoded.sections)
    (evaluated : (model operational algebra vertex).evaluateTerm context expression =
      some ⟨CertifiedProjection.certifiedAt operational carrier kind context.1, value⟩) :
    (model operational algebra vertex).evaluateTerm context (classifierValue carrier kind expression) =
      some (codeValue operational carrier (readClassifier operational carrier kind value)) := by
  have valueRead : (model operational algebra vertex).evaluateTerm context expression =
      some ⟨NativeLocalTypeFormers.sigma (codeAt operational carrier context.1)
        (Classifier.Realization.bodyAt operational context carrier kind),
          Classifier.Realization.sectionAt operational context carrier kind value⟩ :=
    evaluated.trans (congrArg some (value_cast
      (Classifier.Realization.sigma_at operational context carrier kind) value))
  have read := (model operational algebra vertex).evaluate_first context (codeType carrier n)
    (Classifier.Realization.bodySyntax carrier kind n) (codeAt operational carrier context.1)
    (Classifier.Realization.bodyAt operational context carrier kind)
    (Classifier.Realization.code_read operational algebra vertex context carrier)
    (Classifier.Realization.body_read operational algebra vertex context carrier kind) expression
    (Classifier.Realization.sectionAt operational context carrier kind value) valueRead
  exact read.trans (congrArg some (congrArg
    (fun first => (⟨codeAt operational carrier context.1, first⟩ : NativeValue context.1))
      (Classifier.Realization.first_exact operational context carrier kind value)))

/-- The classifier's sort witness is retained by its actual certified readout. -/
theorem readClassifier_kinded {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier) (kind : HSort)
    (value : (CertifiedProjection.certifiedAt operational carrier kind P).decoded.sections)
    (world : Wᵒᵖ) (parameter : P.obj world) :
    Classifier.Code.Member ((readClassifier operational carrier kind value).app world parameter) (.sort kind) :=
  ((closedReadSection (certifiedMeaning operational carrier kind)
    (certifiedRead operational carrier kind) value).app world parameter).property

private def interpretedTerm {n : Nat} {raw : ContextExpr (symbols D) n}
    {expression : TermExpr (symbols D) n} {type : TypeExpr (symbols D) n}
    (derivation : Derivation (Theory vertex) (.term raw expression type))
    (scope : Scope W n) (A : NativeType scope.1)
    (contextRead : (model operational algebra vertex).evaluateContext raw = some scope)
    (typeRead : (model operational algebra vertex).evaluateType scope type = some A) : A.decoded.sections :=
  Classical.choose (Interprets.termAt
    (derivation.native_sound (model operational algebra vertex)
      (Classifier.Realization.realization operational algebra vertex)) scope A contextRead typeRead)

private theorem interpretedTerm_read {n : Nat} {raw : ContextExpr (symbols D) n}
    {expression : TermExpr (symbols D) n} {type : TypeExpr (symbols D) n}
    (derivation : Derivation (Theory vertex) (.term raw expression type))
    (scope : Scope W n) (A : NativeType scope.1)
    (contextRead : (model operational algebra vertex).evaluateContext raw = some scope)
    (typeRead : (model operational algebra vertex).evaluateType scope type = some A) :
    (model operational algebra vertex).evaluateTerm scope expression =
      some ⟨A, interpretedTerm operational algebra vertex derivation scope A contextRead typeRead⟩ :=
  Classical.choose_spec (Interprets.termAt
    (derivation.native_sound (model operational algebra vertex)
      (Classifier.Realization.realization operational algebra vertex)) scope A contextRead typeRead)

structure Reading {n : Nat} (scope : Scope W n) (carrier : D.Carrier) (kind : HSort)
    (bundle : TermExpr (symbols D) n) where
  classifier : scope.1 ⟶ Carrier.presheaf operational carrier
  value : scope.1 ⟶ Carrier.presheaf operational carrier
  classifierRead : (model operational algebra vertex).evaluateTerm scope
    (IndexSyntax.classifier carrier kind bundle) = some (codeValue operational carrier classifier)
  valueRead : (model operational algebra vertex).evaluateTerm scope
    (IndexSyntax.value carrier kind bundle) = some (codeValue operational carrier value)
  kinded : ∀ world parameter, Classifier.Code.Member (classifier.app world parameter) (.sort kind)
  member : ∀ world parameter, Classifier.Code.Member (value.app world parameter) (classifier.app world parameter)

/-- Every typed index is decoded through the original native projection
rules, not through an independent host-language interpretation of syntax. -/
def read {n : Nat} {raw : ContextExpr (symbols D) n}
    (formed : Derivation (Theory vertex) (.context raw))
    {carrier : D.Carrier} {kind : HSort} {bundle : TermExpr (symbols D) n}
    (typed : Derivation (Theory vertex) (.term raw bundle (indexType carrier kind n)))
    (scope : Scope W n) (contextRead : (model operational algebra vertex).evaluateContext raw = some scope) :
    Reading operational algebra vertex scope carrier kind bundle := by
  let classifierDerivation := IndexSyntax.classifierBundleTyped vertex carrier kind formed typed
  let classifierValue := interpretedTerm operational algebra vertex classifierDerivation scope
    (CertifiedProjection.certifiedAt operational carrier kind scope.1) contextRead
    (Classifier.Realization.certified_read operational algebra vertex scope carrier kind)
  have classifierValueRead := interpretedTerm_read operational algebra vertex classifierDerivation scope
    (CertifiedProjection.certifiedAt operational carrier kind scope.1) contextRead
    (Classifier.Realization.certified_read operational algebra vertex scope carrier kind)
  let classifierName := readClassifier operational carrier kind classifierValue
  have classifierRead := classifierValue_read operational algebra vertex scope carrier kind
    (IndexSyntax.classifierBundle carrier kind bundle) classifierValue classifierValueRead
  let valueDerivation := IndexSyntax.valueTyped vertex carrier kind formed typed
  let valueSection := interpretedTerm operational algebra vertex valueDerivation scope
    (codeAt operational carrier scope.1) contextRead
    (Classifier.Realization.code_read operational algebra vertex scope carrier)
  have valueRead := interpretedTerm_read operational algebra vertex valueDerivation scope
    (codeAt operational carrier scope.1) contextRead
    (Classifier.Realization.code_read operational algebra vertex scope carrier)
  let valueName := sectionName operational carrier valueSection
  have valueCodeRead : (model operational algebra vertex).evaluateTerm scope (IndexSyntax.value carrier kind bundle) =
      some (codeValue operational carrier valueName) := valueRead
  let memberDerivation := IndexSyntax.membershipTyped vertex carrier kind formed typed
  have memberTypeRead := Classifier.Realization.typing_read operational algebra vertex scope carrier
    (IndexSyntax.value carrier kind bundle) (IndexSyntax.classifier carrier kind bundle)
    valueName classifierName valueCodeRead classifierRead
  let memberSection := interpretedTerm operational algebra vertex memberDerivation scope
    (typingAt operational carrier valueName classifierName) contextRead memberTypeRead
  refine ⟨classifierName, valueName, classifierRead, valueCodeRead,
    readClassifier_kinded operational carrier kind classifierValue, ?_⟩
  intro world parameter
  exact (typingAt_inhabited_iff operational carrier valueName classifierName world parameter).mp
    ⟨memberSection.val ⟨world, parameter⟩⟩

end
end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.IndexSemantics
