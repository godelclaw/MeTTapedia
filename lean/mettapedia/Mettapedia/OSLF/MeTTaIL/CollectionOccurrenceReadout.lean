import Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceMatcher

/-! # Primitive readout of prepared collection occurrence allocations -/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceBatch

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax CollectionOccurrenceHandoff

variable {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern}

theorem Allocation.static_checked (allocation : Allocation plan bound expected source) :
    RuleBinding.admittedFor allocation.job.origin.declaration.rule
        allocation.job.origin.declaration.binding.spec = true ∧
      Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted
        (GeneralPlanEnvironment.environment plan).language (GeneralPlanEnvironment.environment plan).free
        allocation.job.variant.site.focusBound allocation.job.variant.site.focusType
        allocation.job.variant.site.focus = true := by
  have issued := allocation.issued
  unfold CollectionOccurrenceContinuation.request? at issued
  dsimp only at issued
  split at issued
  · rename_i admitted
    split at issued
    · rename_i checked
      exact ⟨admitted, checked⟩
    · cases issued
  · cases issued

/-- The actual request checker selects these fields from the original typed
occurrence. Its source/target formation and matching proofs stay attached. -/
theorem Allocation.request_fields (allocation : Allocation plan bound expected source) :
    allocation.request.depth = allocation.depth ∧
    allocation.request.bound = allocation.job.variant.site.focusBound ∧
    allocation.request.type = allocation.job.variant.site.focusType ∧
    allocation.request.source = allocation.job.variant.site.focus ∧
    allocation.request.index = allocation.job.origin.ordinal ∧
    allocation.request.rule = allocation.job.origin.declaration.rule ∧
    allocation.request.spec = allocation.job.origin.declaration.binding.spec ∧
    allocation.request.answer = allocation.answer := by
  have issued := allocation.issued
  unfold CollectionOccurrenceContinuation.request? at issued
  dsimp only at issued
  split at issued
  · split at issued
    · rw [← Option.some.inj issued]
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · cases issued
  · cases issued

theorem allocate_readout (job : Job) (licensed : job.Valid plan bound expected source)
    (work depth : Nat) (answer : RecursiveCollectionMachine.Answer)
    (published : CollectionOccurrenceMatcher.Published job work answer)
    {allocation : Allocation plan bound expected source}
    (made : allocate? job licensed work answer published depth = some allocation) :
    allocation.job = job ∧ allocation.answer = answer ∧ allocation.depth = depth ∧
      RecursiveCollectionHandoff.prepare job.request answer = some allocation.prepared := by
  unfold allocate? at made
  split at made
  · cases made
  · rename_i prepared computed
    dsimp only at made
    split at made
    · cases made
    · cases Option.some.inj made
      exact ⟨rfl, rfl, rfl, computed⟩

end Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceBatch
