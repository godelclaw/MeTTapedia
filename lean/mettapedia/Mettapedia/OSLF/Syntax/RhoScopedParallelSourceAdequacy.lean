import Mettapedia.OSLF.Syntax.RhoScopedParallelReactiveSystem
import Mettapedia.OSLF.Syntax.RhoOperationalClosure

/-!
# Original rho parallel-rule adequacy for least-context transitions

The independently authored closed COMM/Drop/ParCong relation, closed under
the original source equations, agrees with the scoped permitted-path event
system at the empty ambient context. Its steps are exactly the identity
labels of the derived relative-pushout transition system. This comparison
concerns parallel reaction contexts; it does not add reduction permission
under an input binder or in a quoted or output payload.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoScopedParallelSourceAdequacy

open _root_.CategoryTheory RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open RhoScopedParallelEvents RhoScopedParallelContexts RhoScopedParallelReactiveSystem
open Mettapedia.GSLT.RedexRelativeCongruence

/-- Every original closed root instance supplies the displayed source rule. -/
theorem root_parallel_step (root : Root sourceRules withReflection []) :
    ParallelStep root.2.source root.2.target := by
  rcases root with ⟨⟨index, allowed⟩, firing⟩
  cases index with
  | communication =>
      let closed := firing.toClosed
      exact .comm ⟨⟨closed.body, closed.close⟩, closed.source_eq, closed.target_eq⟩
  | reflection =>
      let closed := firing.toClosed
      exact .drop ⟨⟨closed.body, closed.close⟩, closed.source_eq, closed.target_eq⟩

theorem communication_to_event {source target : Term sig [] Srt.pr}
    (step : RootStep comm source target) :
    RhoScopedParallelEvents.Step (rules := sourceRules) (admitted := withReflection)
      (project source) (project target) := by
  obtain ⟨valuation, sourceRead, targetRead⟩ := step
  let closed : UnpositionedRewrite.RootFiring comm.unpositioned source target :=
    ⟨valuation.body, valuation.close, sourceRead, targetRead⟩
  let root : Root sourceRules withReflection [] :=
    ⟨⟨.communication, trivial⟩, ContextualRootEvents.Instance.ofClosed closed⟩
  apply (step_iff_root_surrounding _ _).mpr
  refine ⟨root, zero [], ?_, ?_⟩
  · exact (congrArg project (ContextualRootEvents.Instance.ofClosed_source closed)).symm.trans
      (join_zero_right root.source).symm
  · exact (congrArg project (ContextualRootEvents.Instance.ofClosed_target closed)).symm.trans
      (join_zero_right root.target).symm

theorem reflection_to_event {source target : Term sig [] Srt.pr}
    (step : RootStep dropRule source target) :
    RhoScopedParallelEvents.Step (rules := sourceRules) (admitted := withReflection)
      (project source) (project target) := by
  obtain ⟨valuation, sourceRead, targetRead⟩ := step
  let closed : UnpositionedRewrite.RootFiring dropRule.unpositioned source target :=
    ⟨valuation.body, valuation.close, sourceRead, targetRead⟩
  let root : Root sourceRules withReflection [] :=
    ⟨⟨.reflection, trivial⟩, ContextualRootEvents.Instance.ofClosed closed⟩
  apply (step_iff_root_surrounding _ _).mpr
  refine ⟨root, zero [], ?_, ?_⟩
  · exact (congrArg project (ContextualRootEvents.Instance.ofClosed_source closed)).symm.trans
      (join_zero_right root.source).symm
  · exact (congrArg project (ContextualRootEvents.Instance.ofClosed_target closed)).symm.trans
      (join_zero_right root.target).symm

theorem parallelStep_to_event : ∀ {source target : Term sig [] Srt.pr},
    ParallelStep source target →
      RhoScopedParallelEvents.Step (rules := sourceRules) (admitted := withReflection)
        (project source) (project target)
  | _, _, .comm step => communication_to_event step
  | _, _, .drop step => reflection_to_event step
  | _, _, .parLeft remainder step => by
      simpa only [join_project, parallel, parT] using
        step_join (parallelStep_to_event step) (project remainder)
  | _, _, .parRight remainder step => by
      have under := step_join (parallelStep_to_event step) (project remainder)
      rw [join_commutes _ (project remainder), join_commutes _ (project remainder)] at under
      simpa only [join_project, parallel, parT] using under

/-- Every actual quotient event reconstructs representatives of the printed rules. -/
theorem event_to_parallelStepModE {source target : Term sig [] Srt.pr}
    (step : RhoScopedParallelEvents.Step (rules := sourceRules) (admitted := withReflection)
      (project source) (project target)) : ParallelStepModE source target := by
  obtain ⟨root, surrounding, sourceRead, targetRead⟩ :=
    (step_iff_root_surrounding _ _).mp step
  induction surrounding using Quotient.inductionOn with
  | _ remainder =>
      refine ⟨parT root.2.source remainder, parT root.2.target remainder, ?_,
        .parLeft remainder (root_parallel_step root), ?_⟩
      · exact Quotient.exact sourceRead
      · exact Quotient.exact targetRead.symm

theorem parallelStepModE_to_event {source target : Term sig [] Srt.pr}
    (step : ParallelStepModE source target) :
    RhoScopedParallelEvents.Step (rules := sourceRules) (admitted := withReflection)
      (project source) (project target) := by
  obtain ⟨source', target', before, firing, after⟩ := step
  have sourceRead : project source = project source' := Quotient.sound before
  have targetRead : project target' = project target := Quotient.sound after
  rw [sourceRead, ← targetRead]
  exact parallelStep_to_event firing

theorem parallelStepModE_iff_event (source target : Term sig [] Srt.pr) :
    ParallelStepModE source target ↔
      RhoScopedParallelEvents.Step (rules := sourceRules) (admitted := withReflection)
        (project source) (project target) :=
  ⟨parallelStepModE_to_event, event_to_parallelStepModE⟩

/-- Original source reduction modulo its equations is exactly identity-labelled IPO reduction. -/
theorem parallelStepModE_iff_actIPO_identity (source target : Term sig [] Srt.pr) :
    ParallelStepModE source target ↔
      ActIPO (reactionRules sourceRules withReflection) (𝟙 (interface []))
        (arrow (project source)) (arrow (project target)) :=
  (parallelStepModE_iff_event source target).trans (step_iff_actIPO_identity _ _)

end Mettapedia.OSLF.Binding.RhoScopedParallelSourceAdequacy
