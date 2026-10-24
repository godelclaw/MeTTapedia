import Mettapedia.Languages.MeTTa.PrimeCandidates.Index.Requirements

/-!
# Quotation and discarded effects: a two-strategy counterexample

The finite expression language below compares precisely eager and by-name
evaluation, recording executed ticks. Both preserve quoted syntax; they differ
on discarded ordinary arguments. The resulting separation refutes the claim
that quotation alone forces non-strict argument evaluation.

The requirement controls concern these two evaluators. They illustrate joint
compatibility and incompatibility without characterizing all Prime systems.
-/

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.QuotationDemand

open Mettapedia.Languages.MeTTa.PrimeCandidates.Requirements



inductive Expr where
  | literal (value : Nat)
  | tick
  | quote (body : Expr)
  | discard (argument body : Expr)
  deriving DecidableEq, Repr

inductive Value where
  | number (value : Nat)
  | syntax (body : Expr)
  deriving DecidableEq, Repr

inductive Strategy where
  | eager
  | byName
  deriving DecidableEq, Repr

/-- The second component records executed ticks. Quotation retains syntax;
ordinary discarded arguments are evaluated only by the eager strategy. -/
def evaluate (strategy : Strategy) : Expr → Value × Nat
  | .literal n => (.number n, 0)
  | .tick => (.number 0, 1)
  | .quote body => (.syntax body, 0)
  | .discard argument body =>
      let result := evaluate strategy body
      match strategy with
      | .eager => (result.1, (evaluate strategy argument).2 + result.2)
      | .byName => result

def QuotesWithoutExecution (strategy : Strategy) : Prop :=
  ∀ body, evaluate strategy (.quote body) = (.syntax body, 0)

def SkipsDiscardedTick (strategy : Strategy) : Prop :=
  evaluate strategy (.discard .tick (.literal 7)) = (.number 7, 0)

theorem eager_quotes_without_execution : QuotesWithoutExecution .eager := by
  intro body
  rfl

theorem byName_quotes_without_execution : QuotesWithoutExecution .byName := by
  intro body
  rfl

theorem eager_executes_discarded_tick :
    evaluate .eager (.discard .tick (.literal 7)) = (.number 7, 1) := rfl

theorem byName_skips_discarded_tick : SkipsDiscardedTick .byName := rfl

theorem quotation_does_not_determine_non_strictness :
    ¬ ((∃ strategy, QuotesWithoutExecution strategy) ∧
      ∀ strategy, QuotesWithoutExecution strategy → SkipsDiscardedTick strategy) := by
  apply counterexample_refutes_consequence eager_quotes_without_execution
  simp [SkipsDiscardedTick, evaluate]

/-- Within this explicit two-strategy comparison, the extra demand property
does distinguish the alternatives. This does not rank all possible machines. -/
theorem demand_property_determines_byName :
    ((∃ strategy, QuotesWithoutExecution strategy ∧ SkipsDiscardedTick strategy) ∧
      ∀ strategy, QuotesWithoutExecution strategy ∧ SkipsDiscardedTick strategy →
        strategy = .byName) := by
  refine ⟨⟨.byName, byName_quotes_without_execution, byName_skips_discarded_tick⟩, ?_⟩
  intro strategy properties
  cases strategy with
  | eager => exact False.elim (by simpa [SkipsDiscardedTick, evaluate] using properties.2)
  | byName => rfl


namespace RequirementControls


inductive Requirement where
  | quotation
  | skipUnused
  | executeUnused
  deriving DecidableEq, Repr

def holds : Requirement → Strategy → Prop
  | .quotation => QuotesWithoutExecution
  | .skipUnused => SkipsDiscardedTick
  | .executeUnused => fun strategy =>
      evaluate strategy (.discard .tick (.literal 7)) = (.number 7, 1)

def quotationSpec : Specification Strategy Requirement :=
  ⟨holds, [.quotation]⟩

def demandSpec : Specification Strategy Requirement :=
  quotationSpec.extend [.skipUnused]

def conflictingSpec : Specification Strategy Requirement :=
  demandSpec.extend [.executeUnused]

def eagerQuotationEvidence : quotationSpec.Evidence .eager where
  supported := [.quotation]
  verifies := by
    intro requirement membership
    have equal : requirement = .quotation := by simpa using membership
    subst requirement
    exact eager_quotes_without_execution

def demandEvidence : demandSpec.Evidence .byName where
  supported := [.quotation, .skipUnused]
  verifies := by
    intro requirement membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl
    · exact byName_quotes_without_execution
    · exact byName_skips_discarded_tick

theorem demandEvidence_complete : demandSpec.Satisfies .byName :=
  demandEvidence.complete (by decide)

theorem quotation_admits_both :
    quotationSpec.Satisfies .eager ∧ quotationSpec.Satisfies .byName := by
  refine ⟨eagerQuotationEvidence.complete (by decide), ?_⟩
  exact ((quotationSpec.satisfies_extend_iff [.skipUnused] .byName).mp
    demandEvidence_complete).1

/-- The new observation, not the old quotation requirement, excludes eagerness. -/
theorem extra_requirement_excludes_eager : ¬ demandSpec.Satisfies .eager := by
  intro satisfies
  have skip := satisfies .skipUnused (by simp [demandSpec, quotationSpec, Specification.extend])
  change SkipsDiscardedTick .eager at skip
  simp [SkipsDiscardedTick, evaluate] at skip

theorem demand_determines_byName_in_this_class :
    ((∃ strategy, demandSpec.Satisfies strategy) ∧
      ∀ strategy, demandSpec.Satisfies strategy → strategy = .byName) := by
  refine ⟨⟨.byName, demandEvidence_complete⟩, ?_⟩
  intro strategy satisfies
  cases strategy with
  | eager => exact (extra_requirement_excludes_eager satisfies).elim
  | byName => rfl

theorem each_requirement_has_a_witness :
    ∀ requirement ∈ conflictingSpec.required, ∃ strategy, holds requirement strategy := by
  intro requirement _
  cases requirement with
  | quotation => exact ⟨.eager, eager_quotes_without_execution⟩
  | skipUnused => exact ⟨.byName, byName_skips_discarded_tick⟩
  | executeUnused => exact ⟨.eager, eager_executes_discarded_tick⟩

/-- Componentwise existence does not assemble a model: the last two demands
disagree on the effect count of the very same closed workload. -/
theorem no_joint_witness : ¬ ∃ strategy, conflictingSpec.Satisfies strategy := by
  rintro ⟨strategy, satisfies⟩
  have skip := satisfies .skipUnused
    (by simp [conflictingSpec, demandSpec, quotationSpec, Specification.extend])
  have execute := satisfies .executeUnused
    (by simp [conflictingSpec, demandSpec, quotationSpec, Specification.extend])
  have impossible : (Value.number 7, 0) = (.number 7, 1) := skip.symm.trans execute
  cases impossible

theorem incompatible_extension_is_not_determined :
    ¬ ((∃ strategy, conflictingSpec.Satisfies strategy) ∧
      ∀ strategy, conflictingSpec.Satisfies strategy → strategy = .byName) :=
  empty_class_excludes_consequence no_joint_witness

/-- Conjunction retains the reusable quotation requirement and the demand
requirement on the same concrete evaluator. -/
def quotationAndDemandEvidence :
    (quotationSpec.conjoin demandSpec).Evidence .byName :=
  (show quotationSpec.Evidence .byName from
    { supported := [.quotation]
      verifies := by
        intro requirement membership
        have equal : requirement = .quotation := by simpa using membership
        subst requirement
        exact byName_quotes_without_execution }).conjoin demandEvidence

theorem quotationAndDemand_complete :
    (quotationSpec.conjoin demandSpec).Satisfies .byName :=
  quotationAndDemandEvidence.complete (by decide)

/-- The componentwise-witness fallacy is still impossible after introducing
assembly conjunction. A good quotation component cannot repair contradictory
effect requirements on the same evaluator. -/
theorem conjoining_does_not_repair_incompatibility :
    ¬ ∃ strategy, (quotationSpec.conjoin conflictingSpec).Satisfies strategy := by
  rintro ⟨strategy, satisfies⟩
  exact no_joint_witness ⟨strategy,
    ((quotationSpec.satisfies_conjoin_iff conflictingSpec strategy).mp satisfies).2⟩

end RequirementControls

#print axioms quotation_does_not_determine_non_strictness
#print axioms demand_property_determines_byName
#print axioms RequirementControls.quotationAndDemand_complete
#print axioms RequirementControls.conjoining_does_not_repair_incompatibility
#print axioms RequirementControls.demand_determines_byName_in_this_class
#print axioms RequirementControls.no_joint_witness

end Mettapedia.Languages.MeTTa.PrimeCandidates.QuotationDemand
