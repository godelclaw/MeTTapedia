import Mettapedia.OSLF.MeTTaIL.GeneralCompletedExecutionProfile
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceReceiptKeys

/-!
# Completed conditional-equation occurrence controls

Independent equation and primitive-firing derivations are compared with the
actual generic completion algorithm. Its checked certificate places both
distinct authored origins in one real finite execution. Duplicate provider
rows remain equation evidence rather than additional physical events.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralCompletedFrontierControls

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open GeneralExecutionAdmission GeneralTypedSites
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence

private theorem two_slots (slot : Fin 2) : slot.val = 0 ∨ slot.val = 1 := by omega

private theorem literal_sorted (enabled : Bool) (value : Pattern)
    (chosen : value = one ∨ value = two ∨ value = done) :
    OpenPatternWellSorted (GeneralPlanEnvironment.environment (request enabled).plan).language
      (snapshot enabled).free [] term value := by
  apply checkOpenPatternWellSorted_sound
  rcases chosen with rfl | rfl | rfl <;>
    change checkOpenPatternWellSorted (GeneralPlanEnvironment.environment
      (compile (snapshot enabled) permissions)).language _ _ _ _ = true
  all_goals rw [runtime_plan_actual]; cases enabled <;> cbv

/-- Independently authored local firing; its occurrence is licensed before
it is compared with the executable frontier. -/
def reductionJob (slot : Fin 2) : GeneralRuleJobs.Job :=
  ⟨slot.val, declaration slot.val, .here [] term two⟩

def reductionReceipt (slot : Fin 2) : GeneralRuleJobs.Receipt :=
  ⟨reductionJob slot, [], [], [], [], done, done⟩

theorem reduction_receipt_valid (slot : Fin 2) :
    (reductionReceipt slot).Valid (request true).plan [] term two := by
  have licensed : (reductionJob slot).Valid (request true).plan [] term two := by
    constructor
    · change (declaration slot.val, slot.val) ∈
        (compile (snapshot true) permissions).rules.zipIdx
      rw [runtime_plan_actual]
      rcases two_slots slot with index | index <;>
        simp [runtimePlan, index]
    · exact .here rfl rfl (literal_sorted true two (Or.inr (Or.inl rfl))).1
  apply GeneralRuleJobs.finish_sound (trace := []) (captured := [])
    (completed := []) (history := []) licensed
  · exact .constructor .nil
  · exact .nil
  · change GeneralRuleJobs.finish? (compile (snapshot true) permissions) [] term
      (reductionJob slot) [] [] [] [] = some (reductionReceipt slot)
    rw [runtime_plan_actual]
    rcases two_slots slot with index | index <;>
      simp only [reductionJob, reductionReceipt, index] <;> cbv

def equationSource : ScopedEquationExecution.Orientation → Pattern
  | .forward => one
  | .reverse => two

def equationTarget : ScopedEquationExecution.Orientation → Pattern
  | .forward => two
  | .reverse => one

def conversionJob (direction : ScopedEquationExecution.Orientation) : GeneralEquationJobs.Job :=
  ⟨if direction = .forward then 0 else 1, oriented direction,
    .here [] term (equationSource direction)⟩

def conversionReceipt (direction : ScopedEquationExecution.Orientation) (row : Fin 2) :
    GeneralEquationJobs.Receipt :=
  ⟨conversionJob direction, [], [], [], [.query 0 0 row.val [(0, [])]],
    equationTarget direction, equationTarget direction⟩

theorem conversion_receipt_valid (direction : ScopedEquationExecution.Orientation) (row : Fin 2) :
    GeneralEquationJobs.Completion (request true).plan [] term (equationSource direction)
      (conversionReceipt direction row) := by
  have licensed : GeneralEquationJobs.LicensedJob (request true).plan [] term
      (equationSource direction) (conversionJob direction) := by
    constructor
    · change (oriented direction, if direction = .forward then 0 else 1) ∈
        (compile (snapshot true) permissions).equations.zipIdx
      rw [runtime_plan_actual]
      cases direction <;> simp [runtimePlan]
    · apply Licensed.here rfl
      · cases direction <;> rfl
      · exact (literal_sorted true _ (by
          cases direction
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl))).1
  apply GeneralEquationJobs.finish_sound (trace := []) (captured := [])
    (completed := []) (history := [.query 0 0 row.val [(0, [])]]) licensed
  · exact literal_sorted true _ (by
      cases direction
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl))
  · cases direction <;>
      simp only [conversionJob, oriented, EquationPlan.rule, ScopedEquationExecution.orientedRule,
        equation, equationSource, SiteData.here] <;>
      rw [Pattern.eraseBinderMetadata_eq_self_of_canonical (by rfl)] <;>
      exact .constructor .nil
  · rw [show (conversionJob direction).equation.rule.premises =
        [.relationQuery "allow" [one]] from by cases direction <;> rfl]
    apply GeneralPremise.PremisesHold.cons
    · apply GeneralPremise.PremiseHolds.query
      apply GeneralPremise.TracedQuery.row
        (row := ⟨"allow", [one]⟩) (signature := ⟨"allow", [term], [.input]⟩)
      · change (snapshot true).provider.rows[row.val]? = _
        rcases two_slots row with index | index <;> simp [snapshot, index]
      · rfl
      · apply GeneralPremise.checkRow_sound
        change GeneralPremise.checkRow (GeneralPlanEnvironment.environment
          (compile (snapshot true) permissions)).language _ _ _ _ = true
        rw [runtime_plan_actual]
        cases direction <;> cbv
      · apply GeneralPremise.TracedArgumentsHold.input
        · cases direction <;> cbv
        · exact .nil
      · apply GeneralPremise.checkTypedAssignment_sound
        change GeneralPremise.checkTypedAssignment (GeneralPlanEnvironment.environment
          (compile (snapshot true) permissions)) _ [] = true
        rw [runtime_plan_actual]
        cases direction <;> cbv
    · exact .nil
  · change GeneralEquationJobs.finish (compile (snapshot true) permissions) [] term
      (conversionJob direction) [] [] [] [.query 0 0 row.val [(0, [])]] =
        some (conversionReceipt direction row)
    rw [runtime_plan_actual]
    cases direction <;> cbv

theorem equation_exposes_two :
    Relation.EqvGen (GeneralOccurrenceSemantics.Equation (request true).plan [] term)
      (request true).root two := by
  rw [request_root]
  exact .rel _ _ ⟨conversionReceipt .forward ⟨0, by decide⟩,
    conversion_receipt_valid .forward ⟨0, by decide⟩, rfl⟩

/-- Both independently specified declaration origins are present in the
completed actual frontier, including the source's equation transport. -/
theorem completed_occurrence_exists (slot : Fin 2) :
    ∃ answer ∈ (completed true).answers,
      answer.val.firing.job.declaration.declarationIndex = slot.val ∧
      answer.val.target = done := by
  obtain ⟨answer, member, _, same⟩ :=
    GeneralOccurrenceFrontier.certified_physical_occurrence (admitted true)
      (completed_certificate true) two equation_exposes_two (reductionReceipt slot)
      (reduction_receipt_valid slot)
  refine ⟨answer, member, ?_, ?_⟩
  · rw [same]
    rfl
  · change answer.val.firing.target = done
    rw [same]
    rfl

theorem distinct_actual_origins :
    ∃ first ∈ (completed true).answers, ∃ second ∈ (completed true).answers,
      first ≠ second ∧ first.val.target = done ∧ second.val.target = done := by
  obtain ⟨first, firstMember, firstOrigin, firstTarget⟩ :=
    completed_occurrence_exists ⟨0, by decide⟩
  obtain ⟨second, secondMember, secondOrigin, secondTarget⟩ :=
    completed_occurrence_exists ⟨1, by decide⟩
  refine ⟨first, firstMember, second, secondMember, ?_, firstTarget, secondTarget⟩
  intro same
  have equal := congrArg
    (fun answer : GeneralOccurrenceFrontier.Answer (request true) =>
      answer.val.firing.job.declaration.declarationIndex) same
  rw [firstOrigin, secondOrigin] at equal
  contradiction

theorem actual_completed_run_contains_both_origins :
    ∃ fuel, GeneralOccurrenceFrontier.complete (request true)
      (GeneralOccurrenceFrontier.run (request true) fuel
        (GeneralOccurrenceFrontier.start (request true))) = true ∧
      ∀ slot : Fin 2, ∃ answer ∈
        (GeneralOccurrenceFrontier.run (request true) fuel
          (GeneralOccurrenceFrontier.start (request true))).answers,
        answer.val.firing.job.declaration.declarationIndex = slot.val ∧
          answer.val.target = done := by
  obtain ⟨fuel, actual⟩ := completed_actual_finite_run true
  refine ⟨fuel, ?_, ?_⟩
  · rw [actual]
    exact completed_complete true
  · rw [actual]
    exact completed_occurrence_exists


private theorem selected_equation_premises {source : Pattern}
    {receipt : GeneralEquationJobs.Receipt}
    (valid : GeneralEquationJobs.Completion (request false).plan [] term source receipt) :
    receipt.job.equation.rule.premises = [.relationQuery "allow" [one]] := by
  have member := List.fst_mem_of_mem_zipIdx valid.job.1
  change receipt.job.equation ∈ (compile (snapshot false) permissions).equations at member
  rw [runtime_plan_actual] at member
  change receipt.job.equation ∈ [oriented .forward, oriented .reverse] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same <;> rw [same] <;> rfl

private theorem no_rows_premises {context : GeneralPremise.Context}
    {initial final : ScopedRuleMatching.Assignment} {history : List GeneralPremise.Event}
    (premises : GeneralPremise.PremisesHold (GeneralPlanEnvironment.environment (request false).plan)
      context [.relationQuery "allow" [one]] initial final history) : False := by
  cases premises with
  | cons head tail =>
    cases head with
    | query query =>
      cases query with
      | row selected signature rowTyped arguments finalTyped =>
        change ([] : List GeneralPremise.ProviderRow)[_]? = some _ at selected
        simp only [List.getElem?_nil] at selected
        cases selected

/-- A provider with no rows cannot justify an equation query, even when its
signature exists and a matching schema has been found. -/
theorem no_rows_equation_impossible {source target : Pattern}
    (edge : GeneralOccurrenceSemantics.Equation (request false).plan [] term source target) : False := by
  obtain ⟨receipt, valid, _⟩ := edge
  have premises := valid.premises
  rw [selected_equation_premises valid] at premises
  exact no_rows_premises premises

private theorem empty_provider_equivalence_eq {source target : Pattern}
    (related : Relation.EqvGen (GeneralOccurrenceSemantics.Equation
      (request false).plan [] term) source target) : source = target := by
  induction related with
  | rel _ _ edge => exact False.elim (no_rows_equation_impossible edge)
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

private theorem one_site_is_root {site : SiteData}
    (licensed : Licensed (GeneralPlanEnvironment.environment (request false).plan).language
      (snapshot false).free permissions.sites [] term one site) :
    site = SiteData.here [] term one := by
  have generated := GeneralTypedSites.generate_complete licensed
  have actual : GeneralTypedSites.generate
      (GeneralPlanEnvironment.environment (request false).plan).language
      (snapshot false).free permissions.sites [] term one = [SiteData.here [] term one] := by
    change GeneralTypedSites.generate (GeneralPlanEnvironment.environment
      (compile (snapshot false) permissions)).language _ _ _ _ _ = _
    rw [runtime_plan_actual]
    cbv
  rw [actual] at generated
  exact List.mem_singleton.mp generated

private theorem no_root_from_one {index : Nat}
    {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event} {target : Pattern}
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (request false).plan)
      [] term one index trace captured completed history target) : False := by
  cases firing with
  | @fire bound type source target index matchingSchema matchingSpec captured completed trace history
      declared specification admitted sourceTyped matching capturedTyped premises reduced targetTyped =>
    have member := List.mem_of_getElem? declared
    change _ ∈ (compile (snapshot false) permissions).rules.map RulePlan.rule at member
    rw [runtime_plan_actual] at member
    change _ ∈ [(declaration 0).rule, (declaration 1).rule] at member
    have lhs : matchingSchema.left = two := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same <;> rw [same] <;> rfl
    have found := matching.matching.complete
    rw [lhs] at found
    have impossible : ScopedRuleMatching.matchAt matchingSchema matchingSpec 0
        RulePatternSite.left [] 0 [] two one = [] := by cbv
    have empty : captured ∈ ([] : List ScopedRuleMatching.Assignment) := by
      simpa only [List.length_nil, impossible] using found
    exact List.not_mem_nil empty

private theorem no_primitive_from_one {receipt : GeneralRuleJobs.Receipt}
    (valid : receipt.Valid (request false).plan [] term one) : False := by
  have site := one_site_is_root valid.1.2
  have firing := valid.2.1
  rw [site] at firing
  exact no_root_from_one firing

/-- Failed conditional conversion cannot expose the independently authored
redex. This semantic absence is then compared with certified execution. -/
theorem no_rows_semantic_absence :
    ¬ ∃ target, (GeneralOccurrenceSemantics.gslt (request false).plan [] term).Step one target := by
  rintro ⟨target, representative, receipt, converted, firing, _⟩
  have same := empty_provider_equivalence_eq converted
  subst representative
  exact no_primitive_from_one firing

theorem no_rows_no_answers : (completed false).answers = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro answer _member
  have step := GeneralOccurrenceSemantics.Receipt.semantic_step (request false).plan [] term answer.property
  have actual : (GeneralOccurrenceSemantics.gslt (request false).plan [] term).Step
      one answer.val.target := by simpa only [request_root] using step
  exact no_rows_semantic_absence ⟨answer.val.target, actual⟩

theorem no_rows_certified_absence :
    ¬ ∃ target, (GeneralOccurrenceSemantics.gslt (request false).plan [] term).Step one target := by
  rw [← request_root false]
  exact (GeneralOccurrenceFrontier.certified_absence (admitted false)
    (completed_certificate false)).mp no_rows_no_answers

theorem equation_exposes_done :
    (GeneralOccurrenceSemantics.gslt (request true).plan [] term).Step one done := by
  obtain ⟨answer, _, _, target⟩ := completed_occurrence_exists ⟨0, by decide⟩
  have step := GeneralOccurrenceSemantics.Receipt.semantic_step (request true).plan [] term answer.property
  simpa only [request_root, target] using step

/-- The completed frontier's outgoing diamond is inhabited. The empty
provider frontier has no outgoing successor; this is not the incoming box. -/
theorem outgoing_modal_separation :
    (GeneralOccurrenceFrontier.targets (request true) (completed true)).any (fun _ => true) = true ∧
    (GeneralOccurrenceFrontier.targets (request false) (completed false)).all (fun _ => false) = true := by
  constructor
  · obtain ⟨answer, member, _, _⟩ := completed_occurrence_exists ⟨0, by decide⟩
    exact List.any_eq_true.mpr ⟨answer.val.target,
      List.mem_map.mpr ⟨answer, member, rfl⟩, rfl⟩
  · simp only [GeneralOccurrenceFrontier.targets, no_rows_no_answers, List.map_nil, List.all_nil]


/-- Every orientation and duplicate query-row origin occurs in the actual
completed equation archive. These are administrative receipts. -/
theorem completed_equation_occurrence (direction : ScopedEquationExecution.Orientation) (row : Fin 2) :
    ∃ edge ∈ (completed true).edges,
      edge.source = equationSource direction ∧
      edge.receipt = conversionReceipt direction row := by
  have related : Relation.EqvGen (GeneralOccurrenceSemantics.Equation
      (request true).plan [] term) (request true).root (equationSource direction) := by
    cases direction
    · rw [request_root]
      exact .refl _
    · exact equation_exposes_two
  have represented := (GeneralOccurrenceFrontier.certified_representatives_exact (admitted true)
    (completed_certificate true) (equationSource direction)).mpr related
  have within := GeneralOccurrenceFrontier.represented_within (admitted true) (completed true)
    (equationSource direction) represented
  exact GeneralOccurrenceFrontier.certified_equation_occurrence (admitted true)
    (completed_certificate true) (equationSource direction) within (conversionReceipt direction row)
    (conversion_receipt_valid direction row)

end Mettapedia.OSLF.MeTTaIL.GeneralCompletedFrontierControls
