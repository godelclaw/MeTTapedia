import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Checking
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.ResponseSemantics
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.ContinuationSemantics
import Mettapedia.OSLF.NativeTypes.Semantics.Classifier.Realization
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSignatureSumModel
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSoundness

/-!
# An interpretation of the indexed modal signature

The constructor interpretation retains its structural images and actual
membership fibres. Each additional modal primitive returns the certified
classifier of independent source responses over its dependent request scope.
All expressions use the common native evaluator.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.ModalModel

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open ContextualModelTelescopes NativeLocalTypeFormers
open Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.NativeTypes.Semantics
open Presheaf CubeEnrichment CubeNativeDeclarations

universe u
variable {D : CubeEnrichment.Signature} {I : Type} {W : Type u} [Category.{u} W]
variable (operational : D.Carrier → Wᵒᵖ ⥤ Type u)
    (algebra : Classifier.StructuralImages.Algebra operational) (vertex : Vertex D)
    (interfaces : I → Interface D.Carrier)
    (requests : ∀ index, ResponseSemantics.Requests operational (interfaces index))
    (observed : ∀ index, ResponseSemantics.Observations operational (interfaces index))

noncomputable section

/-- The additional alphabet has no independent type or predicate symbols.
Its primitive values are the constructed response classifiers. -/
def extra : ModelData (Declarations.extraSymbols interfaces) W where
  typeParameters impossible := nomatch impossible
  typeFamily impossible := nomatch impossible
  termParameters index := (requests index).parameters
  termType index := Classifier.CertifiedProjection.certifiedAt operational
    (interfaces index).focus (interfaces index).resultSort (requests index).parameters.1
  termValue index := ResponseSemantics.former (requests index) (observed index)
  predicateParameters impossible := nomatch impossible
  predicateValue impossible := nomatch impossible

/-- This combines actual primitive meanings, rather than replacing the old
constructor signature or defining a second expression evaluator. -/
def fromRequests : ModelData (Declarations.symbols interfaces) W :=
  SignatureSum.model (Classifier.Model.model operational algebra vertex)
    (extra operational interfaces requests observed)

/-- The only local header comparison needed by the additional primitives.
The generated request assembly discharges it for the concrete model below. -/
theorem fromRequests_realization
    (parameterRead : ∀ index,
      (Classifier.Model.model operational algebra vertex).evaluateContext
        (parameters (interfaces index)) = some (requests index).parameters) :
    SignatureRealization (fromRequests operational algebra vertex interfaces requests observed)
      (Declarations.signature vertex interfaces) where
  typeHeader symbol := by
    cases symbol with
    | inl symbol =>
        change (SignatureSum.model _ _).evaluateContext
          (SignatureSum.contextLeft ((Theory vertex).typeParameters symbol)) =
            some ((Classifier.Model.model operational algebra vertex).typeParameters symbol)
        rw [SignatureSum.evaluateContext_left]
        exact (Classifier.Realization.realization operational algebra vertex).typeHeader symbol
    | inr impossible => exact nomatch impossible
  termHeader symbol := by
    cases symbol with
    | inl symbol =>
        change (SignatureSum.model _ _).evaluateContext
          (SignatureSum.contextLeft ((Theory vertex).termParameters symbol)) =
            some ((Classifier.Model.model operational algebra vertex).termParameters symbol)
        rw [SignatureSum.evaluateContext_left]
        exact (Classifier.Realization.realization operational algebra vertex).termHeader symbol
    | inr index =>
        change (SignatureSum.model _ _).evaluateContext
          (SignatureSum.contextLeft (parameters (interfaces index))) = some (requests index).parameters
        rw [SignatureSum.evaluateContext_left]
        exact parameterRead index
  predicateHeader impossible := by
    cases impossible with
    | inl impossible => exact nomatch impossible
    | inr impossible => exact nomatch impossible
  termResult symbol := by
    cases symbol with
    | inl symbol =>
        change (SignatureSum.model _ _).evaluateType
          ((Classifier.Model.model operational algebra vertex).termParameters symbol)
          (SignatureSum.typeLeft ((Theory vertex).termResult symbol)) =
            some ((Classifier.Model.model operational algebra vertex).termType symbol)
        rw [SignatureSum.evaluateType_left]
        exact (Classifier.Realization.realization operational algebra vertex).termResult symbol
    | inr index =>
        change (SignatureSum.model _ _).evaluateType (requests index).parameters
          (SignatureSum.typeLeft (result (interfaces index))) =
            some (Classifier.CertifiedProjection.certifiedAt operational
              (interfaces index).focus (interfaces index).resultSort (requests index).parameters.1)
        rw [SignatureSum.evaluateType_left]
        exact Classifier.Realization.certified_read operational algebra vertex _ _ _

/-- The generated request scopes evaluate the authored parameter telescope,
then open each rely value and its membership evidence in order. -/
def generatedRequests : ∀ index, ResponseSemantics.Requests operational (interfaces index) :=
  fun index => ContinuationSemantics.requests operational algebra vertex (interfaces index)

/-- The interpretation of the existing generated signature uses only the
request telescope computed from its actual native syntax. -/
def model : ModelData (Declarations.symbols interfaces) W :=
  fromRequests operational algebra vertex interfaces
    (generatedRequests operational algebra vertex interfaces) observed

/-- Every declaration is realized without a caller-supplied interpretation
or header-correctness record. The independent events remain operational data. -/
theorem realization :
    SignatureRealization (model operational algebra vertex interfaces observed)
      (Declarations.signature vertex interfaces) :=
  fromRequests_realization operational algebra vertex interfaces
    (generatedRequests operational algebra vertex interfaces) observed
    (fun index => ContinuationSemantics.parameters_read operational algebra vertex (interfaces index))

/-- Evaluating the actual primitive at its own parameter context returns the
constructed response classifier, including its kind evidence. -/
theorem primitive_at_header (index : I) :
    (fromRequests operational algebra vertex interfaces requests observed).evaluateTerm
      (requests index).parameters (.primitive (.inr index) TermExpr.var) =
        some ⟨Classifier.CertifiedProjection.certifiedAt operational
          (interfaces index).focus (interfaces index).resultSort (requests index).parameters.1,
          ResponseSemantics.former (requests index) (observed index)⟩ := by
  let model := fromRequests operational algebra vertex interfaces requests observed
  have identity := model.evaluateSubstitution_identity (requests index).parameters
  have read := model.evaluate_primitive (requests index).parameters (.inr index) TermExpr.var
    (𝟙 (requests index).parameters.1)
    ((model.evaluateSubstitution_eq_some_iff _ _ _ _).mp identity)
  exact read.trans (congrArg some (Value.substitute_identity (K := (NativeModel W).toCwf) _))

/-- The decoded value of the actual primitive has the independent source
meaning, rather than merely the same kind as a generated code. -/
theorem primitive_value_source (index : I) (world : Wᵒᵖ)
    (focus : (operational (interfaces index).focus).obj world)
    (parameter : (requests index).parameters.1.obj world) :
    Classifier.Code.Member (.operational focus)
      (Classifier.CertifiedProjection.certifiedAtEquiv operational
        (interfaces index).focus (interfaces index).resultSort (requests index).parameters.1
        ⟨world, parameter⟩
        (((fromRequests operational algebra vertex interfaces requests observed).termValue (.inr index)).val
          ⟨world, parameter⟩)).val ↔
      ResponseSemantics.SourceMeaning (requests index) (observed index) world focus parameter :=
  ResponseSemantics.former_exact (requests index) (observed index) world focus parameter

/-- An old constructor expression keeps exactly its original interpretation. -/
theorem original_term_meaning {n : Nat} (scope : Scope W n)
    (expression : TermExpr (symbols D) n) :
    (fromRequests operational algebra vertex interfaces requests observed).evaluateTerm
        scope (SignatureSum.termLeft expression) =
      (Classifier.Model.model operational algebra vertex).evaluateTerm scope expression :=
  SignatureSum.evaluateTerm_left _ _ expression scope

/-- Substitutions are read by the existing evaluator, so the type law applies
to arbitrary native terms, including dependent functions and refinements. -/
theorem type_substitute {n k : Nat}
    (type : TypeExpr (Declarations.symbols interfaces) n)
    (source : Scope W k) (target : Scope W n)
    (mapping : Substitution (Declarations.symbols interfaces) n k)
    (arrow : source.1 ⟶ target.1)
    (mappingRead : (model operational algebra vertex interfaces observed).evaluateSubstitution
      source target mapping = some arrow)
    (meaning : NativeType target.1)
    (typeRead : (model operational algebra vertex interfaces observed).evaluateType
      target type = some meaning) :
    (model operational algebra vertex interfaces observed).evaluateType source
      (type.substitute mapping) = some (meaning.reindex arrow) :=
  ModelData.evaluateType_substitute _ (NativeLocalTypeOperations.products_substitution W)
    type source target mapping (ModelSubstitution.ofEvaluated _ _ _ _ _ mappingRead) meaning typeRead

theorem term_substitute {n k : Nat}
    (term : TermExpr (Declarations.symbols interfaces) n)
    (source : Scope W k) (target : Scope W n)
    (mapping : Substitution (Declarations.symbols interfaces) n k)
    (arrow : source.1 ⟶ target.1)
    (mappingRead : (model operational algebra vertex interfaces observed).evaluateSubstitution
      source target mapping = some arrow)
    (meaning : NativeValue target.1)
    (termRead : (model operational algebra vertex interfaces observed).evaluateTerm
      target term = some meaning) :
    (model operational algebra vertex interfaces observed).evaluateTerm source
      (term.substitute mapping) = some (meaning.substitute arrow) :=
  ModelData.evaluateTerm_substitute _ (NativeLocalTypeOperations.products_substitution W)
    term source target mapping (ModelSubstitution.ofEvaluated _ _ _ _ _ mappingRead) meaning termRead

theorem predicate_substitute {n k : Nat}
    (predicate : PropExpr (Declarations.symbols interfaces) n)
    (source : Scope W k) (target : Scope W n)
    (mapping : Substitution (Declarations.symbols interfaces) n k)
    (arrow : source.1 ⟶ target.1)
    (mappingRead : (model operational algebra vertex interfaces observed).evaluateSubstitution
      source target mapping = some arrow)
    (meaning : Subfunctor target.1)
    (predicateRead : (model operational algebra vertex interfaces observed).evaluatePredicate
      target predicate = some meaning) :
    (model operational algebra vertex interfaces observed).evaluatePredicate source
      (predicate.substitute mapping) = some (meaning.preimage arrow) :=
  ModelData.evaluatePredicate_substitute _ (NativeLocalTypeOperations.products_substitution W)
    predicate source target mapping (ModelSubstitution.ofEvaluated _ _ _ _ _ mappingRead) meaning predicateRead

theorem substitution_compose {n k l : Nat}
    (middle : Scope W k) (target : Scope W n) (source : Scope W l)
    (first : Substitution (Declarations.symbols interfaces) n k)
    (second : Substitution (Declarations.symbols interfaces) k l)
    (firstArrow : middle.1 ⟶ target.1) (secondArrow : source.1 ⟶ middle.1)
    (firstRead : (model operational algebra vertex interfaces observed).evaluateSubstitution
      middle target first = some firstArrow)
    (secondRead : (model operational algebra vertex interfaces observed).evaluateSubstitution
      source middle second = some secondArrow) :
    (model operational algebra vertex interfaces observed).evaluateSubstitution source target
      (composeSubstitution first second) = some (secondArrow ≫ firstArrow) :=
  ModelData.evaluateSubstitution_composition _ (NativeLocalTypeOperations.products_substitution W)
    middle target source first second firstArrow secondArrow firstRead secondRead

theorem context_extend {n : Nat}
    (context : ContextExpr (Declarations.symbols interfaces) n)
    (type : TypeExpr (Declarations.symbols interfaces) n)
    (scope : Scope W n) (meaning : NativeType scope.1)
    (contextRead : (model operational algebra vertex interfaces observed).evaluateContext context = some scope)
    (typeRead : (model operational algebra vertex interfaces observed).evaluateType scope type = some meaning) :
    (model operational algebra vertex interfaces observed).evaluateContext
      (.snoc context type) = some (scope.snoc meaning) :=
  ModelData.evaluateContext_snoc _ context type scope meaning contextRead typeRead

theorem context_assume {n : Nat}
    (context : ContextExpr (Declarations.symbols interfaces) n)
    (predicate : PropExpr (Declarations.symbols interfaces) n)
    (scope : Scope W n) (meaning : Subfunctor scope.1)
    (contextRead : (model operational algebra vertex interfaces observed).evaluateContext context = some scope)
    (predicateRead : (model operational algebra vertex interfaces observed).evaluatePredicate scope predicate = some meaning) :
    (model operational algebra vertex interfaces observed).evaluateContext
      (.assume context predicate) = some (scope.assume meaning) :=
  ModelData.evaluateContext_assume _ context predicate scope meaning contextRead predicateRead

theorem derivation_sound
    (parameterRead : ∀ index,
      (Classifier.Model.model operational algebra vertex).evaluateContext
        (parameters (interfaces index)) = some (requests index).parameters)
    {judgment : Judgment (Declarations.symbols interfaces)}
    (tree : Derivation (Declarations.signature vertex interfaces) judgment) :
    Interprets (fromRequests operational algebra vertex interfaces requests observed) judgment :=
  tree.native_sound _ (fromRequests_realization operational algebra vertex interfaces requests observed parameterRead)

theorem checked_sound [DecidableEq D.Carrier] [DecidableEq D.Former] [DecidableEq I]
    (parameterRead : ∀ index,
      (Classifier.Model.model operational algebra vertex).evaluateContext
        (parameters (interfaces index)) = some (requests index).parameters)
    (fragment : NativeLogic.Fragment)
    (certificate : Certificates.Refinement.Certificate (Declarations.signature vertex interfaces))
    (judgment : Judgment (Declarations.symbols interfaces))
    (accepted : Declarations.check vertex interfaces fragment certificate judgment = .accepted) :
    Interprets (fromRequests operational algebra vertex interfaces requests observed) judgment := by
  obtain ⟨_, _, tree, _⟩ := (Declarations.check_exact vertex interfaces fragment certificate judgment).mp accepted
  exact derivation_sound operational algebra vertex interfaces requests observed parameterRead tree

/-- All judgments, including context equations, dependent terms and predicate
entailments, have their meaning in the one common native interpreter. -/
theorem sound {judgment : Judgment (Declarations.symbols interfaces)}
    (tree : Derivation (Declarations.signature vertex interfaces) judgment) :
    Interprets (model operational algebra vertex interfaces observed) judgment :=
  tree.native_sound _ (realization operational algebra vertex interfaces observed)

theorem generated_check_sound [DecidableEq D.Carrier] [DecidableEq D.Former] [DecidableEq I]
    (fragment : NativeLogic.Fragment)
    (certificate : Certificates.Refinement.Certificate (Declarations.signature vertex interfaces))
    (judgment : Judgment (Declarations.symbols interfaces))
    (accepted : Declarations.check vertex interfaces fragment certificate judgment = .accepted) :
    Interprets (model operational algebra vertex interfaces observed) judgment := by
  obtain ⟨_, _, tree, _⟩ := (Declarations.check_exact vertex interfaces fragment certificate judgment).mp accepted
  exact sound operational algebra vertex interfaces observed tree

/-- This is the evaluated primitive of the actual generated signature at
its computed open parameter scope. -/
theorem modal_evaluates (index : I) :
    (model operational algebra vertex interfaces observed).evaluateTerm
      (ContinuationSemantics.parameterScope operational algebra vertex (interfaces index))
      (.primitive (.inr index) TermExpr.var) =
        some ⟨Classifier.CertifiedProjection.certifiedAt operational
          (interfaces index).focus (interfaces index).resultSort
          (ContinuationSemantics.parameterScope operational algebra vertex (interfaces index)).1,
          ResponseSemantics.former
            (ContinuationSemantics.requests operational algebra vertex (interfaces index)) (observed index)⟩ :=
  primitive_at_header operational algebra vertex interfaces
    (generatedRequests operational algebra vertex interfaces) observed index

/-- Decoding the actual modal primitive recovers every specified source
response, over the derived request contexts and substituted continuation. -/
theorem modal_meaning (index : I) (world : Wᵒᵖ)
    (focus : (operational (interfaces index).focus).obj world)
    (parameter : (ContinuationSemantics.parameterScope operational algebra vertex (interfaces index)).1.obj world) :
    Classifier.Code.Member (.operational focus)
      (Classifier.CertifiedProjection.certifiedAtEquiv operational
        (interfaces index).focus (interfaces index).resultSort
        (ContinuationSemantics.parameterScope operational algebra vertex (interfaces index)).1
        ⟨world, parameter⟩
        (((model operational algebra vertex interfaces observed).termValue (.inr index)).val
          ⟨world, parameter⟩)).val ↔
      ResponseSemantics.SourceMeaning
        (ContinuationSemantics.requests operational algebra vertex (interfaces index))
        (observed index) world focus parameter :=
  primitive_value_source operational algebra vertex interfaces
    (generatedRequests operational algebra vertex interfaces) observed index world focus parameter

end
end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.ModalModel
