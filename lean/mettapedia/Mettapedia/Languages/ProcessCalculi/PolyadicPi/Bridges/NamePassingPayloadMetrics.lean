import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingPayloadRuntime
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingContextMetric

/-!
# Client distances measured by actual payload executions

The independent payload observer uses the established weighted client
language, retaining each client's source origin. Its distance agrees with the
source and authored-runtime distances. The context budget comparison keeps
the proved scaling factor; it does not equate client weights with funding.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingPayloadMetrics

open Mettapedia.OSLF.Binding Mettapedia.GSLT.Logic
open NamePassingLambda NamePassingContexts NamePassingContextMetric NamePassingPayloadRuntime

def payloadTests (Γ : Ctx sig) : BudgetedObservations (ProtocolContexts.Program Γ) where
  Test := CertifiedClient Γ
  holds test component := PayloadMayReturn (test.client.plug component)
  weight test := testWeight ⟨test.output, test.origin⟩
  positive test := testWeight_positive ⟨test.output, test.origin⟩
  bounded test := testWeight_bounded ⟨test.output, test.origin⟩

theorem source_distance_eq {Γ : Ctx sig} (left right : Expr Γ) :
    (payloadTests Γ).distance (program left) (program right) = (sourceTests Γ).distance left right :=
  (sourceTests Γ).distance_transport (payloadTests Γ) program certify (certify_covers Γ)
    (fun test source => (NamePassingPayloadRuntime.context_may_return_iff test.2 source).symm)
    (fun _ => rfl) left right

theorem runtime_distance_eq {Γ : Ctx sig} (left right : ProtocolContexts.Program Γ) :
    (payloadTests Γ).distance left right = (targetTests Γ).distance left right :=
  (targetTests Γ).distance_transport (payloadTests Γ) id id (fun client => ⟨client, rfl⟩)
    (fun test component => payload_may_return_iff (test.client.plug component))
    (fun _ => rfl) left right

theorem zero_iff {Γ : Ctx sig} (left right : ProtocolContexts.Program Γ) :
    (payloadTests Γ).distance left right = 0 ↔ PayloadEquivalent left right := by
  rw [runtime_distance_eq]
  exact (target_zero_iff left right).trans (payload_equivalent_iff left right).symm

theorem context_budget_bound {Γ Δ : Ctx sig} (context : SourceContext Γ Δ)
    (left right : Expr Γ) :
    (payloadTests Δ).distance (program (context.plug left)) (program (context.plug right)) *
      (1 / 2 : ℝ) ^ context.budget ≤
        (payloadTests Γ).distance (program left) (program right) := by
  rw [source_distance_eq, source_distance_eq]
  exact NamePassingContextMetric.context_budget_bound context left right

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingPayloadMetrics
