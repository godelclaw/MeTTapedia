import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingPayloadRuntime
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingDependentRuntimeEvidence
import Mettapedia.GSLT.Core.CoveredExecutionPaths

/-!
# Dependent certificates on independently supplied payload executions

Every target prefix from an actual compiled runtime state lifts to a complete
authored runtime prefix. Its projection recovers the supplied target path,
including intermediate states. The established compiler receipt then retains
the native certificate, source history, specification and communication account.
Current-state certificates additionally use their actual execution functor.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingPayloadCertificates

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.RhoPayloadParameterizedRuntime
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational Mettapedia.GSLT.Ultrainfinite
open Mettapedia.TypeTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open NamePassingLambda NamePassingDependentEvidence NamePassingDependentSpecifications
open NamePassingDependentRuntimeEvidence NamePassingPayloadRuntime

structure Receipt (A : DisplayedFamily sourcePrograms) (B : DisplayedFamily compiledPrograms)
    (body : A ⟶ reindexDisplayed compilerMap B) (point : sourcePrograms.Elements)
    (evidence : A.obj point) (world : NamePassingSpine.World (scope point))
    (code : RhoUnaryCode.Code 0) {final : targetTheory.Term}
    (actual : ExecutionPath targetTheory
      (state (RhoUnaryReadback.runtimeProcess code world.available)) final) where
  endpoint : RhoUnaryReadback.TargetProcess
  runtimePath : ExecutionPath RhoUnaryReadback.Target
    (RhoUnaryReadback.runtimeProcess code world.available) endpoint
  endpointEq : state endpoint = final
  exactPath : HEq (mappedPrefix runtimePath) actual
  instructions : runtimePath.length = actual.length
  native : NamePassingDependentRuntimeEvidence.Receipt A B body point evidence world code runtimePath

/-- The supplied prefix is interpreted in the target's own rule model, then
lifted before invoking compiler readback and universal native specifications. -/
theorem retain_prefix (A : DisplayedFamily sourcePrograms) (B : DisplayedFamily compiledPrograms)
    (body : A ⟶ reindexDisplayed compilerMap B) (point : sourcePrograms.Elements)
    (evidence : A.obj point) (world : NamePassingSpine.World (scope point))
    (code : RhoUnaryCode.Code 0)
    (compiled : NamePassingRho.compile point.2 (NamePassingUnaryForward.references (scope point))
      .zero world.world = some code)
    {final : targetTheory.Term}
    (actual : ExecutionPath targetTheory
      (state (RhoUnaryReadback.runtimeProcess code world.available)) final) :
    Nonempty (Receipt A B body point evidence world code actual) := by
  obtain ⟨endpoint, runtimePath, endpointEq, exactPath, instructions⟩ :=
    NamePassingPayloadRuntime.presentation.cover.liftExecutionPath_exact
      NamePassingPayloadRuntime.presentation.toOperational actual
  obtain ⟨native⟩ := NamePassingDependentRuntimeEvidence.retain_prefix
    A B body point evidence world code compiled runtimePath
  exact ⟨⟨endpoint, runtimePath, endpointEq, exactPath, instructions, native⟩⟩

variable {A : DisplayedFamily sourcePrograms} {B : DisplayedFamily compiledPrograms}
variable {body : A ⟶ reindexDisplayed compilerMap B} {point : sourcePrograms.Elements}
variable {evidence : A.obj point} {world : NamePassingSpine.World (scope point)}
variable {code : RhoUnaryCode.Code 0} {final : targetTheory.Term}
variable {actual : ExecutionPath targetTheory
  (state (RhoUnaryReadback.runtimeProcess code world.available)) final}

theorem Receipt.specification_computes (receipt : Receipt A B body point evidence world code actual) :
    receipt.native.specification = body.app point evidence :=
  receipt.native.computed

theorem Receipt.public_return_reflected (receipt : Receipt A B body point evidence world code actual)
    (observed : (publicInput (world.world .zero).term).1 final) :
    (NamePassingValueNative.sourcePredicate (scope point)).1 receipt.native.execution.after := by
  apply receipt.native.public_return_reflected
  apply (NamePassingPayloadRuntime.public_return_iff world .zero receipt.endpoint).mpr
  exact Eq.mpr (congrArg (publicInput (world.world .zero).term).1 receipt.endpointEq) observed

/-- The independent presentation charges exactly the original primitive rho
instructions, while the established source/administration account is retained. -/
theorem Receipt.work_balance (receipt : Receipt A B body point evidence world code actual) :
    receipt.native.execution.rho.credit + actual.length =
      8 * NamePassingRhoReadback.initializationSites point.2 + receipt.native.execution.charges.sum := by
  calc
    _ = receipt.native.execution.rho.credit + receipt.runtimePath.length :=
      congrArg (fun count => receipt.native.execution.rho.credit + count) receipt.instructions.symm
    _ = _ := receipt.native.actual_work_balance

theorem Receipt.ordered_uses (receipt : Receipt A B body point evidence world code actual)
    {Use : Type} (uses : A.obj point → List Use) :
    uses receipt.native.history.2 = uses evidence :=
  receipt.native.ordered_uses_retained uses

private theorem update_of_exact_path (family : ExecutionObject targetTheory ⥤ Type)
    {initial left right : targetTheory.Term} (initialEvidence : family.obj initial)
    (leftPath : ExecutionPath targetTheory initial left)
    (rightPath : ExecutionPath targetTheory initial right)
    (endpoints : left = right) (paths : HEq leftPath rightPath) :
    HEq (family.map leftPath initialEvidence) (family.map rightPath initialEvidence) := by
  cases endpoints
  cases paths
  rfl

/-- Evidence pulled back along the earned execution functor updates exactly
as evidence on the independently supplied target path, in its dependent fibre. -/
theorem Receipt.current_evidence_comparison
    (receipt : Receipt A B body point evidence world code actual)
    (family : ExecutionObject targetTheory ⥤ Type)
    (initialEvidence : family.obj (state (RhoUnaryReadback.runtimeProcess code world.available))) :
    HEq ((executionFunctor ⋙ family).map receipt.runtimePath initialEvidence)
      (family.map actual initialEvidence) :=
  update_of_exact_path family initialEvidence (mappedPrefix receipt.runtimePath) actual
    receipt.endpointEq receipt.exactPath

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingPayloadCertificates
