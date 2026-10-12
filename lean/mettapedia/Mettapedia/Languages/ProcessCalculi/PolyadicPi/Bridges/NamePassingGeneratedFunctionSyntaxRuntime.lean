import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedFunctionSyntax
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedIndexedRuntime

/-!
# Parsed dependent function certificates on supplied rho executions

The initial caller origin, its generated dependent lambda and the actual
runtime prefix share one receipt. Applying the independently generated
target specification agrees with applying the decoded lambda, for every
argument. The exact supplied endpoint, reflected path and communication
accounts stay in that receipt.

This retains an initial-program certificate alongside its execution.
Updating a current-state certificate requires its operational evidence
functor, and natural-number evidence is not a rho runtime data extension.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedFunctionSyntaxRuntime

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational
open Mettapedia.TypeTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafPi
open DisplayedPresheafEvidenceApplication DisplayedPresheafRepresentableEvidence
open NamePassingLambda NamePassingUnaryForward NamePassingEnvironmentEquationsNative
open NamePassingDependentEvidence NamePassingDependentRuntimeEvidence
open NamePassingGeneratedIndexedRuntime NamePassingGeneratedFunctionSyntax

noncomputable section

variable (root point : sourcePrograms.Elements) (origin : (origins root).obj point)
variable (world : NamePassingSpine.World (scope point)) (code : RhoUnaryCode.Code 0)
variable {final : RhoUnaryReadback.TargetProcess}
variable (actual : ExecutionPath RhoUnaryReadback.Target
  (RhoUnaryReadback.runtimeProcess code world.available) final)

abbrev FunctionReceipt := Receipt (origins root)
  (piDisplayed CompilerSpecification.input (CompilerSpecification.output root))
  (CompilerSpecification.body root) point origin world code actual

variable {root point origin world code actual}

def runtimeAnswer (receipt : FunctionReceipt root point origin world code actual) (n : Nat) :
    (CompilerSpecification.output root).obj
      ((sectionLift CompilerSpecification.input (CompilerSpecification.argument n)).mapElements.obj
        (compilerMap.mapElements.obj point)) :=
  (applyAt CompilerSpecification.input (CompilerSpecification.output root)
      (CompilerSpecification.argument n)).app (compilerMap.mapElements.obj point)
    (NamePassingGeneratedIndexedSpecifications.specificationEquiv
      (piDisplayed CompilerSpecification.input (CompilerSpecification.output root))
      (compilerMap.mapElements.obj point) (generatedSpecification receipt))

theorem runtime_answer_exact (receipt : FunctionReceipt root point origin world code actual) (n : Nat) :
    runtimeAnswer receipt n =
      ⟨compilerMap.mapElements.map origin, ⟨n, Nat.lt_succ_self n⟩⟩ := by
  rw [runtimeAnswer, generated_specification_read, receipt.computed]
  exact DisplayedPresheafRepresentableFunctionEvidence.functionConstructor_application
    compilerMap root Nat (fun n => Fin (n + 1)) CompilerSpecification.value
    (compilerMap.mapElements.obj point) (compilerMap.mapElements.map origin) n

theorem parsed_answer_matches_actual_receipt
    (receipt : FunctionReceipt root point origin world code actual) (n : Nat) :
    answer root point origin n = runtimeAnswer receipt n :=
  (answer_exact root point origin n).trans (runtime_answer_exact receipt n).symm

theorem whole_origin_and_actual_accounts
    (receipt : FunctionReceipt root point origin world code actual) :
    generatedCertificate receipt =
        NamePassingGeneratedIndexedEvidence.suppliedReceipt (origins root) point origin ∧
      receipt.execution.rho.credit + actual.length =
        8 * NamePassingRhoReadback.initializationSites point.2 + receipt.execution.charges.sum :=
  generated_certificate_and_actual_accounts receipt

theorem retain_function_prefix (root point : sourcePrograms.Elements) (origin : (origins root).obj point)
    (world : NamePassingSpine.World (scope point)) (code : RhoUnaryCode.Code 0)
    (compiled : NamePassingRho.compile point.2 (references (scope point)) .zero world.world = some code)
    {final : RhoUnaryReadback.TargetProcess}
    (actual : ExecutionPath RhoUnaryReadback.Target
      (RhoUnaryReadback.runtimeProcess code world.available) final) :
    ∃ receipt : FunctionReceipt root point origin world code actual,
      (∀ n, answer root point origin n = runtimeAnswer receipt n) ∧
        receipt.execution.rho.credit + actual.length =
          8 * NamePassingRhoReadback.initializationSites point.2 + receipt.execution.charges.sum := by
  obtain ⟨receipt⟩ := retain_prefix (origins root)
    (piDisplayed CompilerSpecification.input (CompilerSpecification.output root))
    (CompilerSpecification.body root) point origin world code compiled actual
  exact ⟨receipt, parsed_answer_matches_actual_receipt receipt, receipt.actual_work_balance⟩

end

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedFunctionSyntaxRuntime
