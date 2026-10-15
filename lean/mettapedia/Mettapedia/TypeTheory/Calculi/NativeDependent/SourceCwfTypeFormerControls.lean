import Mettapedia.TypeTheory.Calculi.NativeDependent.SourceCwfDependentAbstractionComparison
import Mettapedia.TypeTheory.Calculi.NativeDependent.SourceCwfDependentSumSections
import Mettapedia.TypeTheory.CwfYonedaComparisonControls
import Mettapedia.TypeTheory.CwfYonedaEmptyProductControls

/-!
# Generated dependent former and abstraction controls

The generated raw lambda has its own typing tree and native parser. Its
complete decoded function retains every argument after a nonidentity
environment change. Independently formed native sums retain both dependent
witnesses. A different body changes the actual parser result.

The imported controls additionally separate present-only observations from
future functions and exhibit the failure of complete source recovery when
the source function presentation lacks eta.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SourceCwfTypeFormerControls

open _root_.CategoryTheory Opposite
open Mettapedia.GSLT.Core.ContextualLadder
open SourceCwfDeclarations ContextualModelTelescopes NativeLocalTypeFormers
open DisplayedPresheafTransport DisplayedPresheafComprehension

abbrev source := CwfYonedaComparisonControls.represented
abbrev products := CwfYonedaComparisonControls.products
abbrev sums := CwfYonedaComparisonControls.sums
abbrev context := CwfYonedaComparisonControls.context
abbrev domain := CwfYonedaComparisonControls.domain
abbrev codomain := CwfYonedaComparisonControls.codomain
abbrev body := CwfYonedaComparisonControls.body
abbrev function := CwfYonedaComparisonControls.function
abbrev paired := CwfYonedaComparisonControls.paired
abbrev successor := CwfYonedaComparisonControls.successor

def rawLambda : TermExpr (symbols source) 1 := dependentLambdaTerm body

def rawLambdaFormed : Derivation (signature source)
    (.term (objectContext (⟨context⟩ : Base source)) rawLambda
      (generatedProductType domain codomain)) := dependentLambdaFormed body

theorem raw_lambda_complete_readout :
    (model source).evaluateTerm (objectScope (⟨context⟩ : Base source)) rawLambda =
      some ⟨generatedProductMeaning domain codomain,
        sourceProductTermEquiv products domain codomain function⟩ :=
  dependent_lambda_source_read products body

noncomputable def generatedFunction : (generatedProductMeaning domain codomain).decoded.sections :=
  (model source).products.lam (dependentBodyValue body)

theorem generated_function_has_exact_source_origin :
    (sourceProductTermEquiv products domain codomain).symm generatedFunction = function := by
  rw [generatedFunction, ← sourceProductTermEquiv_abstraction products body]
  exact (sourceProductTermEquiv products domain codomain).symm_apply_apply function

noncomputable def decodedFunction :
    (reindexDisplayed (objectName (⟨context⟩ : Base source))
      (CwfYoneda.representedProductFamily source domain codomain)).sections :=
  (Functor.sectionsFunctor _).map (generatedProductMeaning_decode domain codomain).hom
    generatedFunction

theorem decoded_function_future :
    decodedFunction.val ⟨op (⟨context⟩ : Base source), ⟨PUnit.unit, successor⟩⟩ =
      CwfYonedaComparisonControls.nativeCompleteFunction := by
  have decoded := generated_abstraction_decode body
  have original := CwfYoneda.productFamilyIso_abstraction source products domain codomain body
  exact (congrArg (fun sectionValue => sectionValue.val
    ⟨op (⟨context⟩ : Base source), ⟨PUnit.unit, successor⟩⟩) decoded).trans
    (congrArg (fun sectionValue => sectionValue.val
      ⟨op (⟨context⟩ : Base source), successor⟩) original).symm

theorem decoded_lambda_retains_every_future_argument (n : Nat) (argument : Fin (n + 2)) :
    (((CwfYoneda.representedProductGenericIso source domain codomain successor).hom
      (decodedFunction.val ⟨op (⟨context⟩ : Base source), ⟨PUnit.unit, successor⟩⟩)).val.down
        ⟨n, argument⟩).2.val = argument.val := by
  rw [decoded_function_future]
  exact CwfYonedaComparisonControls.native_generic_application n argument

def futureArgument : Fin 2 := ⟨1, by decide⟩

theorem generated_lambda_rejects_wrong_future_witness :
    (((CwfYoneda.representedProductGenericIso source domain codomain successor).hom
      (decodedFunction.val ⟨op (⟨context⟩ : Base source), ⟨PUnit.unit, successor⟩⟩)).val.down
        ⟨0, futureArgument⟩).2.val ≠ 0 := by
  intro wrong
  have reading := decoded_lambda_retains_every_future_argument 0 futureArgument
  exact (by decide : (1 : Nat) ≠ 0) (reading.symm.trans wrong)

noncomputable def generatedPair : (generatedSumMeaning domain codomain).decoded.sections :=
  sourceSumTermEquiv sums domain codomain paired

noncomputable def decodedPair :
    (reindexDisplayed (objectName (⟨context⟩ : Base source))
      (CwfYoneda.representedSumFamily source domain codomain)).sections :=
  (Functor.sectionsFunctor _).map (generatedSumMeaning_decodeIso domain codomain).hom
    generatedPair

theorem decoded_pair_future :
    decodedPair.val ⟨op (⟨context⟩ : Base source), ⟨PUnit.unit, successor⟩⟩ =
      CwfYonedaComparisonControls.nativePair :=
  congrArg (fun sectionValue => sectionValue.val
    ⟨op (⟨context⟩ : Base source), ⟨PUnit.unit, successor⟩⟩)
    (sourceSumTermEquiv_decode sums domain codomain paired)

theorem generated_sum_retains_both_future_witnesses (n : Nat) :
    let receipt := decodedPair.val ⟨op (⟨context⟩ : Base source), ⟨PUnit.unit, successor⟩⟩
    (receipt.1.val.down n).2.val = n + 1 ∧ (receipt.2.val.down n).2.val = n + 1 := by
  change _ ∧ _
  rw [decoded_pair_future]
  exact CwfYonedaComparisonControls.native_pair_retains_both n

def zeroBody : source.Tm (source.ext context domain) codomain :=
  ⟨fun point => ⟨0, Nat.zero_lt_succ (point.1 + point.2.val)⟩⟩

def zeroFunction : source.Tm context (products.operations.pi domain codomain) :=
  products.operations.lam zeroBody

theorem original_functions_differ : function ≠ zeroFunction := by
  intro equal
  have value := congrArg (fun term : source.Tm context (products.operations.pi domain codomain) =>
    (term.down 1 futureArgument).val) equal
  exact (by decide : (1 : Nat) ≠ 0) value

theorem independently_parsed_lambdas_differ :
    (model source).evaluateTerm (objectScope (⟨context⟩ : Base source)) (dependentLambdaTerm body) ≠
      (model source).evaluateTerm (objectScope (⟨context⟩ : Base source)) (dependentLambdaTerm zeroBody) := by
  intro equal
  rw [dependent_lambda_source_read products body,
    dependent_lambda_source_read products zeroBody] at equal
  have values := congrArg
    (fun parsed : Option (NativeValue (objectScope (⟨context⟩ : Base source)).1) =>
      ModelData.check? parsed (generatedProductMeaning domain codomain)) equal
  rw [ModelData.check?_supplied, ModelData.check?_supplied] at values
  exact original_functions_differ
    ((sourceProductTermEquiv products domain codomain).injective (Option.some.inj values))

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SourceCwfTypeFormerControls
