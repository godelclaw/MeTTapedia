import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedFunctionSyntaxRuntime
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedIndexedControls
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingDependentRuntimeControls

/-!
# Parsed functions, distinct origins and actual returning executions

The generated certificate expression is compared with the independently
constructed native compiler specification. Application retains distinct
origins and rejects a wrong dependent witness. Changing the raw lambda body
changes its actual parser result. A real fetch-and-call rho execution has
the complete function certificate, exact public endpoint and work account.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedFunctionSyntaxControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational
open Calculi.NativeDependent.Refinement
open SourceCwfDeclarations ContextualModelTelescopes NativeLocalTypeFormers
open DisplayedPresheafRepresentableEvidence
open NamePassingDependentEvidence NamePassingDependentEvidenceControls
open NamePassingGeneratedFunctionSyntax NamePassingGeneratedFunctionSyntaxRuntime

noncomputable section

theorem generated_origins_remain_distinct (n : Nat) :
    answer sourcePoint sourcePoint immediateOrigin n ≠ answer sourcePoint sourcePoint renamedOrigin n := by
  rw [answer_exact, answer_exact]
  intro same
  exact origins_distinct (originMap_injective compilerMap sourcePoint sourcePoint (congrArg Prod.fst same))

theorem agrees_with_independently_constructed_native_specification
    (origin : insertionFamily.obj sourcePoint) (n : Nat) :
    answer sourcePoint sourcePoint origin n = NamePassingGeneratedIndexedControls.dependentAnswer origin n :=
  (answer_exact sourcePoint sourcePoint origin n).trans
    (NamePassingGeneratedIndexedControls.complete_dependent_answer origin n).symm

theorem wrong_dependent_witness_rejected (origin : insertionFamily.obj sourcePoint) (n : Nat)
    (wrong : Fin (n + 1)) (different : wrong.val ≠ n) :
    (answer sourcePoint sourcePoint origin n).2 ≠ wrong := by
  rw [answer_exact]
  intro same
  exact different (congrArg Fin.val same).symm

theorem returned_program_cannot_select_the_answer_origin (n : Nat) :
    ¬ ∃ recover : compiledPrograms.obj sourcePoint.1 →
        (origins (compilerMap.mapElements.obj sourcePoint)).obj (compilerMap.mapElements.obj sourcePoint) ×
          Fin (n + 1),
      recover (compilerMap.app sourcePoint.1 sourcePoint.2) = answer sourcePoint sourcePoint immediateOrigin n ∧
        recover (compilerMap.app sourcePoint.1 sourcePoint.2) = answer sourcePoint sourcePoint renamedOrigin n := by
  rintro ⟨_, first, second⟩
  exact generated_origins_remain_distinct n (first.symm.trans second)

theorem actual_caller_changes_the_whole_origin (origin : insertionFamily.obj sourcePoint) (n : Nat) :
    answer sourcePoint calledPoint (insertionFamily.map callingArrow origin) n =
      ⟨(origins (compilerMap.mapElements.obj sourcePoint)).map (compilerMap.mapElements.map callingArrow)
        (answer sourcePoint sourcePoint origin n).1, (answer sourcePoint sourcePoint origin n).2⟩ :=
  future_complete_answer callingArrow origin n

def zeroBody (root point : sourcePrograms.Elements) :
    source.Tm (source.ext (context root point) (domain root point)) (codomain root point) :=
  ⟨fun supplied => ⟨compilerMap.mapElements.map supplied.1,
    ⟨0, Nat.zero_lt_succ supplied.2⟩⟩⟩

def zeroFunction (root point : sourcePrograms.Elements) :
    source.Tm (context root point) (products.operations.pi (domain root point) (codomain root point)) :=
  products.operations.lam (zeroBody root point)

theorem original_functions_differ (root point : sourcePrograms.Elements) (origin : (origins root).obj point) :
    originalFunction root point ≠ zeroFunction root point := by
  intro equal
  have value := congrArg (fun functionValue : source.Tm (context root point)
      (products.operations.pi (domain root point) (codomain root point)) =>
    (functionValue.down origin (1 : Nat)).2.val) equal
  exact (by decide : (1 : Nat) ≠ 0) value

theorem independently_parsed_bodies_differ (root point : sourcePrograms.Elements)
    (origin : (origins root).obj point) :
    (model source).evaluateTerm (objectScope (⟨context root point⟩ : Base source)) (rawLambda root point) ≠
      (model source).evaluateTerm (objectScope (⟨context root point⟩ : Base source))
        (dependentLambdaTerm (zeroBody root point)) := by
  intro equal
  rw [parsed_lambda_complete, dependent_lambda_source_read products (zeroBody root point)] at equal
  have values := congrArg
    (fun parsed : Option (NativeValue (objectScope (⟨context root point⟩ : Base source)).1) =>
      ModelData.check? parsed (generatedProductMeaning (domain root point) (codomain root point))) equal
  rw [ModelData.check?_supplied, ModelData.check?_supplied] at values
  exact original_functions_differ root point origin
    ((sourceProductTermEquiv products (domain root point) (codomain root point)).injective
      (Option.some.inj values))

open NamePassingDependentRuntimeControls NamePassingSpineControls
open NamePassingCompilerReadback.Controls NamePassingEnvironmentControls

theorem actual_fetched_execution_keeps_the_complete_parsed_function :
    ∃ final, ∃ actual : ExecutionPath RhoUnaryReadback.Target (process start) final,
      ∃ receipt : FunctionReceipt startPoint startPoint (𝟙 startPoint) (world names) (code start) actual,
        (∀ n, answer startPoint startPoint (𝟙 startPoint) n = runtimeAnswer receipt n) ∧
          (NamePassingValueNative.sourcePredicate names).1 receipt.execution.after ∧
          (RhoUnaryInputObservation.targetPredicate (world names) .zero).1 final ∧
          receipt.execution.rho.credit + actual.length =
            8 * NamePassingRhoReadback.initializationSites start + receipt.execution.charges.sum := by
  obtain ⟨final, ⟨actual⟩, observed⟩ := fetched_function_returns_in_rho
  obtain ⟨receipt, complete, accounts⟩ := retain_function_prefix startPoint startPoint (𝟙 startPoint)
    (world names) (code start) (supplied start) actual
  exact ⟨final, actual, receipt, complete, receipt.public_return_reflected observed, observed, accounts⟩

end

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedFunctionSyntaxControls
