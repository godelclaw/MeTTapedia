import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRReferenceCodec
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRExecutableOrigins
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseProviderCongruence
import Mettapedia.OSLF.MeTTaIL.GeneralPlanEnvironment
import Mettapedia.OSLF.MeTTaIL.StructuralDescentAdmission

/-! The actual prepared provider preserves its primitive comparison theory
when fact snapshots change. Input facts reconstruct through the same emitted
reference dictionary used by the runtime observations. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.Executable

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax

theorem fact_relation_ne_comparison (operator : ComparisonOperator) :
    Query.factRelation ≠ Join.comparisonName operator := by
  cases operator <;> decide

private theorem comparison_not_fact_row (known : List Pattern) (operator : ComparisonOperator)
    (first second : Nat) :
    (⟨Join.comparisonName operator,[valueRef first,valueRef second]⟩ : GeneralPremise.ProviderRow)
      ∉ (Query.provider known).rows := by
  intro member
  obtain ⟨fact,_,same⟩ := (Query.provider_rows_exact _ _).mp member
  exact fact_relation_ne_comparison operator (congrArg GeneralPremise.ProviderRow.relation same).symm

theorem snapshot_comparison_row_iff (program : Program) (seeds : List GroundFact) (prepared : Prepared)
    (accepted : prepare program seeds = .ok prepared) (known : List Pattern)
    (operator : ComparisonOperator) (first second : Nat) :
    (⟨Join.comparisonName operator,[valueRef first,valueRef second]⟩ : GeneralPremise.ProviderRow)
      ∈ (snapshot prepared known).provider.rows ↔
    operator ∈ operators program ∧ ∃ left right,
      prepared.vocabulary.literals[first]? = some left ∧
      prepared.vocabulary.literals[second]? = some right ∧ policy.Holds operator left right := by
  change _ ∈ (Query.provider known).rows ++ prepared.staticRows ↔ _
  rw [List.mem_append,prepare_staticRows program seeds prepared accepted]
  simp only [comparison_not_fact_row, false_or]
  exact comparison_row_iff program prepared.vocabulary operator first second

theorem snapshot_source_guard_iff {program : Program} {seeds : List GroundFact} {prepared : Prepared}
    (accepted : prepare program seeds = .ok prepared) {clause : Clause} {comparison : Comparison}
    (source : Statement.rule clause ∈ program.statements)
    (guard : comparison ∈ Comparisons.guards clause) (known : List Pattern)
    (first second : Nat) (left right : Value)
    (leftAt : prepared.vocabulary.literals[first]? = some left)
    (rightAt : prepared.vocabulary.literals[second]? = some right) :
    (⟨Join.comparisonName comparison.operator,[valueRef first,valueRef second]⟩ : GeneralPremise.ProviderRow)
      ∈ (snapshot prepared known).provider.rows ↔ policy.Holds comparison.operator left right := by
  rw [snapshot_comparison_row_iff program seeds prepared accepted]
  simp [source_guard_operator source guard,leftAt,rightAt]

theorem prepared_input_roundtrip (program : Program) (seeds : List GroundFact) (prepared : Prepared)
    (accepted : prepare program seeds = .ok prepared) (fact : GroundFact) (present : fact ∈ seeds) :
    ∃ encoded, fact? prepared.vocabulary fact = some encoded ∧ decodeFact? prepared encoded = some fact := by
  obtain ⟨encoded,formed⟩ := input_fact_encodes program seeds fact present
  have preparedFormed : fact? prepared.vocabulary fact = some encoded := by
    simpa only [prepare_vocabulary program seeds prepared accepted] using formed
  exact ⟨encoded,preparedFormed,decodeFact?_roundtrip prepared fact encoded preparedFormed⟩

theorem snapshot_rules_stable (prepared : Prepared) (before after : List Pattern) :
    (plan prepared before).rules = (plan prepared after).rules :=
  GeneralExecutionAdmission.rules_congr (before := snapshot prepared before)
    (after := snapshot prepared after) rfl rfl permissions

theorem snapshot_equations_stable (prepared : Prepared) (before after : List Pattern) :
    (plan prepared before).equations = (plan prepared after).equations :=
  GeneralExecutionAdmission.equations_congr (before := snapshot prepared before)
    (after := snapshot prepared after) rfl rfl permissions

theorem snapshot_admission_transport (prepared : Prepared) (before after : List Pattern)
    (admitted : (plan prepared before).complete = true)
    (closed : GeneralPremise.checkProviderClosed prepared.compiled (snapshot prepared after).free
      (snapshot prepared after).provider = true) :
    (plan prepared after).complete = true :=
  GeneralExecutionAdmission.complete_replace_provider (before := snapshot prepared before)
    (after := snapshot prepared after) rfl rfl rfl permissions admitted closed

theorem snapshot_environment_transport (prepared : Prepared) (before after : List Pattern) :
    GeneralPlanEnvironment.environment (plan prepared after) =
      {GeneralPlanEnvironment.environment (plan prepared before) with
        provider := (snapshot prepared after).provider} := by
  unfold GeneralPlanEnvironment.environment
  rw [← snapshot_rules_stable prepared before after]
  rfl

theorem snapshot_descent_stable (prepared : Prepared) (before after : List Pattern) :
    StructuralDescent.checkEnvironment (GeneralPlanEnvironment.environment (plan prepared after)) =
      StructuralDescent.checkEnvironment (GeneralPlanEnvironment.environment (plan prepared before)) := by
  rw [snapshot_environment_transport prepared before after]
  unfold StructuralDescent.checkEnvironment GeneralPremise.specification?
  rfl

theorem snapshot_signature_modes (prepared : Prepared) (known : List Pattern) :
    (snapshot prepared known).provider.signatures.all
      (fun signature => signature.argumentTypes.length == signature.modes.length) = true := by
  simp [snapshot,comparisonSignatures,List.all_map]

theorem snapshot_signature_keys_nodup (prepared : Prepared) (known : List Pattern) :
    ((snapshot prepared known).provider.signatures.map
      (fun signature => (signature.relation,signature.argumentTypes.length))).Nodup := by
  have shape : (snapshot prepared known).provider.signatures.map
      (fun signature => (signature.relation,signature.argumentTypes.length)) =
      (Query.factRelation,1) :: (operators prepared.source).map
        (fun operator => (Join.comparisonName operator,2)) := by
    simp [snapshot,comparisonSignatures,List.map_map,Function.comp_def]
  rw [shape]
  apply List.nodup_cons.mpr
  constructor
  · simp
  · apply (operators_nodup prepared.source).map
    intro first second same
    exact comparisonName_injective (congrArg Prod.fst same)

#print axioms snapshot_comparison_row_iff
#print axioms snapshot_source_guard_iff
#print axioms prepared_input_roundtrip
#print axioms snapshot_rules_stable
#print axioms snapshot_admission_transport
#print axioms snapshot_environment_transport
#print axioms snapshot_descent_stable
#print axioms snapshot_signature_keys_nodup

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.Executable
