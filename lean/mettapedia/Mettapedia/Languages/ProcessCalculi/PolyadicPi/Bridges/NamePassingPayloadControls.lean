import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingPayloadCertificates
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingDependentRuntimeControls
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingPayloadMetrics
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingMetricControls
import Mettapedia.OSLF.Syntax.RhoPayloadIntrinsicCommComparison

/-!
# Runtime and scope controls for the payload compiler comparison

An actual environment fetch and call reaches a public response in the
independent payload presentation with its native origin receipt. A free
reference cannot invent a response. Literal Drop remains outside the strict
reaction profile, and equality of translations alone does not establish
quotation-aware admission of an arbitrary raw representative.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingPayloadControls

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational
open Mettapedia.TypeTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafRepresentableEvidence
open NamePassingLambda NamePassingDependentEvidence NamePassingDependentSpecifications
open NamePassingPayloadRuntime NamePassingPayloadCertificates
open NamePassingCompilerReadback.Controls NamePassingEnvironmentControls NamePassingSpineControls
open NamePassingDependentRuntimeControls

theorem fetched_execution_keeps_origin_in_payload :
    ∃ final, ∃ actual : ExecutionPath RhoPayloadParameterizedRuntime.targetTheory
      (state (process start)) final,
      ∃ receipt : NamePassingPayloadCertificates.Receipt (origins startPoint)
        (origins (compilerMap.mapElements.obj startPoint)) (originMap compilerMap startPoint)
        startPoint (𝟙 startPoint) (world names) (code start) actual,
        receipt.native.specification = compilerMap.mapElements.map (𝟙 startPoint) ∧
        (NamePassingValueNative.sourcePredicate names).1 receipt.native.execution.after ∧
        (RhoPayloadParameterizedRuntime.publicInput ((world names).world .zero).term).1 final := by
  obtain ⟨endpoint, ⟨runtimePath⟩, observed⟩ := fetched_function_returns_in_rho
  let actual := mappedPrefix runtimePath
  have payloadObserved := (public_return_iff (world names) .zero endpoint).mp observed
  obtain ⟨receipt⟩ := NamePassingPayloadCertificates.retain_prefix (origins startPoint)
    (origins (compilerMap.mapElements.obj startPoint)) (originMap compilerMap startPoint)
    startPoint (𝟙 startPoint) (world names) (code start) (supplied start) actual
  exact ⟨state endpoint, actual, receipt, receipt.specification_computes,
    receipt.public_return_reflected payloadObserved, payloadObserved⟩

theorem free_reference_has_no_payload_return :
    ¬ (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.semanticDiamond
      RhoPayloadParameterizedRuntime.targetTheory.closure
      (RhoPayloadParameterizedRuntime.publicInput ((world names).world .zero).term)).1
      (state (process freeReference)) := by
  intro observed
  exact free_reference_has_no_rho_return
    ((native_may_return_iff (world names) .zero (process freeReference)).mpr observed)

namespace ReactionProfile

open RhoPayloadPresentation RhoPayloadParameterizedRuntime

theorem literal_drop_is_inert_in_strict_classes (final : targetTheory.Term) :
    ¬ targetTheory.Step (cls (drpT (quoT
      (nilT : Term RhoPayloadPresentation.sig [] RhoPayloadPresentation.Srt.pr)))) final := by
  intro step
  have represented : classStep (cls (drpT (quoT
      (nilT : Term RhoPayloadPresentation.sig [] RhoPayloadPresentation.Srt.pr))))
      (cls (Quotient.out final)) :=
    Eq.mpr (congrArg (classStep (cls (drpT (quoT
      (nilT : Term RhoPayloadPresentation.sig [] RhoPayloadPresentation.Srt.pr)))))
      (Quotient.out_eq final)) step
  exact drop_inert_strict nilT (Quotient.out final) ((classStep_cls _ _).mp represented)

theorem literal_drop_has_dropExecution_firing :
    Steps dropExecutionRules (drpT (quoT
      (nilT : Term RhoPayloadPresentation.sig [] RhoPayloadPresentation.Srt.pr))) nilT :=
  drop_runs_dropExecution nilT

end ReactionProfile

namespace Metric

open NamePassingObserverControls NamePassingPayloadMetrics NamePassingContexts

theorem actual_payload_function_distance :
    (payloadTests NamePassingObserverControls.names).distance (program identity) (program constant) = (1 / 2 : ℝ) := by
  rw [source_distance_eq]
  exact NamePassingMetricControls.caller_distance_exactly_half

theorem actual_payload_called_distance :
    (payloadTests NamePassingObserverControls.names).distance (program (caller.plug identity))
      (program (caller.plug constant)) = 1 := by
  rw [source_distance_eq]
  exact NamePassingMetricControls.after_caller_distance_one

theorem unpriced_context_nonexpansiveness_fails :
    ¬ (payloadTests NamePassingObserverControls.names).distance (program (caller.plug identity))
      (program (caller.plug constant)) ≤
        (payloadTests NamePassingObserverControls.names).distance (program identity) (program constant) := by
  rw [actual_payload_called_distance, actual_payload_function_distance]
  norm_num

end Metric

namespace QuotationAdmission

open RhoPayloadPresentation

def ordinary : Pattern :=
  .apply "PInput" [.apply "NQuote" [.apply "PZero" []],
    .lambda none (.apply "POutput" [.bvar 0, .apply "PZero" []])]

def unsealedRepresentative : Pattern :=
  .apply "PInput" [.apply "NQuote" [.apply "PZero" []],
    .lambda none (.apply "POutput"
      [.apply "NQuote" [.apply "PDrop" [.bvar 0]], .apply "PZero" []])]

/-- Translation agreement supplies no permission to bypass the quotation
scope judgment when choosing an authored representative. -/
theorem same_translation_different_admission :
    tProc (Env.empty []) ordinary = tProc (Env.empty []) unsealedRepresentative ∧
      binderSafeAt "NQuote" 0 ordinary = true ∧
        binderSafeAt "NQuote" 0 unsealedRepresentative = false :=
  ⟨rfl, by decide, by decide⟩

end QuotationAdmission

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingPayloadControls
