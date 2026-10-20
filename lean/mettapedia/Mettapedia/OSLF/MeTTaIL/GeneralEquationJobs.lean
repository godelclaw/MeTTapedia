import Mettapedia.OSLF.MeTTaIL.GeneralPlanEnvironment
import Mettapedia.OSLF.MeTTaIL.GeneralEquationContexts
import Mettapedia.OSLF.MeTTaIL.GeneralEquationAnnotations
import Mettapedia.OSLF.Framework.GeneralFiniteTermUniverseSupport
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseSemantics
import Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrenceReplacement

/-!
# Generic equation jobs and checked local completion

Jobs are generated from the actual compiled declaration positions and every
licensed typed site. Equations are congruences: their sites are every well-sorted position
(`OperationalPermissions.all`), whatever reduction contexts the plan's rewrites have. Each job starts its own scoped matcher and ordered
premise work. Completion checks the actual reduct and both local and filled
sorting judgments. The full authored captures, premise history and equation
orientation remain available beside the canonical endpoint.

This module does not label an externally supplied answer list complete.
Eventual batch coverage is earned by draining the actual premise machine.
-/

set_option autoImplicit false
namespace Mettapedia.OSLF.MeTTaIL.GeneralEquationJobs

open Syntax RuleBinding ScopedRuleMatching DerivedContexts GeneralTypedSites
open GeneralExecutionAdmission GeneralEquationAdmission GeneralEquationCanonical GeneralEquationContexts
open GeneralEquationCaptureDomain GeneralEquationSupport GeneralScopedMatch GeneralScopedMatchMeasures PatternTreeSize
open GeneralEquationMeasures
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence
open Mettapedia.OSLF.Framework.GeneralFiniteTermUniverse

structure Job where
  planPosition : Nat
  equation : EquationPlan
  site : SiteData
  deriving Repr

def jobs (plan : Plan) (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern) : List Job :=
  plan.equations.zipIdx.flatMap fun (equation, position) =>
    (generate (GeneralPlanEnvironment.environment plan).language plan.snapshot.free OperationalPermissions.all bound expected source).map
      fun site => ⟨position, equation, site⟩

/-- Declaration position and licensed context are specified independently of
job enumeration and include all successful grammar typing alternatives. -/
def LicensedJob (plan : Plan) (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern) (job : Job) : Prop :=
  (job.equation, job.planPosition) ∈ plan.equations.zipIdx ∧
    Licensed (GeneralPlanEnvironment.environment plan).language plan.snapshot.free OperationalPermissions.all bound expected source job.site

theorem jobs_iff (plan : Plan) (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern) (job : Job) :
    job ∈ jobs plan bound expected source ↔ LicensedJob plan bound expected source job := by
  constructor
  · intro member
    obtain ⟨⟨equation, position⟩, equationMember, mapped⟩ := List.mem_flatMap.mp member
    obtain ⟨site, siteMember, equal⟩ := List.mem_map.mp mapped
    cases equal
    exact ⟨equationMember, generate_sound _ _ _ _ _ _ _ siteMember⟩
  · rintro ⟨equationMember, siteLicensed⟩
    apply List.mem_flatMap.mpr
    refine ⟨(job.equation, job.planPosition), equationMember, ?_⟩
    exact List.mem_map.mpr ⟨job.site, generate_complete siteLicensed, by cases job; rfl⟩

/-- The entire equation history is administrative evidence, not a primitive
physical firing occurrence. The source declaration and typing branch remain. -/
structure Receipt where
  job : Job
  matcherTrace : List GeneralScopedMatchMachine.BagChoice
  captured : ScopedRuleMatching.Assignment
  completed : ScopedRuleMatching.Assignment
  premiseHistory : List GeneralPremise.Event
  rawReduct : Pattern
  target : Pattern
  deriving Repr

def Job.context (job : Job) (plan : Plan) : GeneralPremise.Context where
  ruleIndex := plan.rules.length
  rule := job.equation.rule
  spec := job.equation.binding.spec
  bound := job.site.focusBound
  premiseIndex := 0
  quantifierDepth := 0

/-- Concrete gates check replacement shape and the complete caller typing
contexts; metadata erasure does not hide a changed bound index or sort. -/
def acceptable (plan : Plan) (bound : List TypeExpr) (expected : TypeExpr) (job : Job) (raw : Pattern) : Bool :=
  let canonicalReduct := raw.eraseBinderMetadata
  job.site.acceptsReplacementRepresentation (GeneralPlanEnvironment.environment plan).language canonicalReduct &&
    checkOpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language plan.snapshot.free job.site.focusBound job.site.focusType canonicalReduct &&
    checkOpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language plan.snapshot.free bound expected
      (job.site.context.fill canonicalReduct).eraseBinderMetadata

def Acceptable (plan : Plan) (bound : List TypeExpr) (expected : TypeExpr) (job : Job) (raw : Pattern) : Prop :=
  job.site.acceptsReplacementRepresentation (GeneralPlanEnvironment.environment plan).language raw.eraseBinderMetadata = true ∧
    OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language plan.snapshot.free job.site.focusBound job.site.focusType raw.eraseBinderMetadata ∧
    OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language plan.snapshot.free bound expected
      (job.site.context.fill raw.eraseBinderMetadata).eraseBinderMetadata

theorem acceptable_iff (plan : Plan) (bound : List TypeExpr) (expected : TypeExpr) (job : Job) (raw : Pattern) :
    acceptable plan bound expected job raw = true ↔ Acceptable plan bound expected job raw := by
  simp only [acceptable, Acceptable, Bool.and_eq_true,
    checkOpenPatternWellSorted_eq_true_iff, and_assoc]

/-- Finish one actual completed premise branch, retaining all earlier evidence. -/
def finish (plan : Plan) (bound : List TypeExpr) (expected : TypeExpr) (job : Job)
    (trace : List GeneralScopedMatchMachine.BagChoice) (captured completed : ScopedRuleMatching.Assignment)
    (history : List GeneralPremise.Event) : Option Receipt :=
  if GeneralPremise.checkTypedAssignment (GeneralPlanEnvironment.environment plan) (job.context plan) captured &&
      GeneralPremise.checkTypedAssignment (GeneralPlanEnvironment.environment plan) (job.context plan) completed then do
    let raw ← reduct? job.equation.rule job.equation.binding.spec job.site.focusBound.length completed
    if acceptable plan bound expected job raw then
      some ⟨job, trace, captured, completed, history, raw,
        (job.site.context.fill raw.eraseBinderMetadata).eraseBinderMetadata⟩
    else none
  else none

/-- Full local completion semantics uses independent matching and premise
judgments. It does not identify a returned endpoint with its receipt. -/
structure Completion (plan : Plan)
    (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern) (receipt : Receipt) : Prop where
  job : LicensedJob plan bound expected source receipt.job
  sourceTyped : OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
    plan.snapshot.free bound expected source
  matched : GeneralScopedMatchMachine.TracedMatches receipt.job.equation.rule receipt.job.equation.binding.spec
    receipt.job.site.focusBound.length .left [] 0 [] receipt.job.equation.rule.left
    receipt.job.site.focus.eraseBinderMetadata receipt.matcherTrace receipt.captured
  capturedTyped : GeneralPremise.TypedAssignment (GeneralPlanEnvironment.environment plan) (receipt.job.context plan) receipt.captured
  premises : GeneralPremise.PremisesHold (GeneralPlanEnvironment.environment plan) (receipt.job.context plan)
    receipt.job.equation.rule.premises receipt.captured receipt.completed receipt.premiseHistory
  completedTyped : GeneralPremise.TypedAssignment (GeneralPlanEnvironment.environment plan) (receipt.job.context plan) receipt.completed
  reduct : reduct? receipt.job.equation.rule receipt.job.equation.binding.spec
    receipt.job.site.focusBound.length receipt.completed = some receipt.rawReduct
  accepted : Acceptable plan bound expected receipt.job receipt.rawReduct
  endpoint : receipt.target =
    (receipt.job.site.context.fill receipt.rawReduct.eraseBinderMetadata).eraseBinderMetadata

theorem finish_readout (plan : Plan) (bound : List TypeExpr) (expected : TypeExpr) (job : Job)
    (trace : List GeneralScopedMatchMachine.BagChoice) (captured completed : ScopedRuleMatching.Assignment)
    (history : List GeneralPremise.Event) (receipt : Receipt)
    (finished : finish plan bound expected job trace captured completed history = some receipt) :
    GeneralPremise.TypedAssignment (GeneralPlanEnvironment.environment plan) (job.context plan) captured ∧
      GeneralPremise.TypedAssignment (GeneralPlanEnvironment.environment plan) (job.context plan) completed ∧
    ∃ raw, reduct? job.equation.rule job.equation.binding.spec job.site.focusBound.length completed = some raw ∧
      Acceptable plan bound expected job raw ∧
      receipt = ⟨job, trace, captured, completed, history, raw,
        (job.site.context.fill raw.eraseBinderMetadata).eraseBinderMetadata⟩ := by
  unfold finish at finished
  split at finished
  next assignments =>
    simp only [Bool.and_eq_true] at assignments
    refine ⟨GeneralPremise.checkTypedAssignment_sound assignments.1,
      GeneralPremise.checkTypedAssignment_sound assignments.2, ?_⟩
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at finished
    obtain ⟨raw, found, finished⟩ := finished
    split at finished
    next checked =>
      cases Option.some.inj finished
      exact ⟨raw, found, (acceptable_iff plan bound expected job raw).mp checked, rfl⟩
    next => contradiction
  next => contradiction

theorem finish_sound {plan : Plan}
    {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern} {job : Job}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event} {receipt : Receipt}
    (licensed : LicensedJob plan bound expected source job)
    (sourceTyped : OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
      plan.snapshot.free bound expected source)
    (matched : GeneralScopedMatchMachine.TracedMatches job.equation.rule job.equation.binding.spec
      job.site.focusBound.length .left [] 0 [] job.equation.rule.left job.site.focus.eraseBinderMetadata trace captured)
    (premises : GeneralPremise.PremisesHold (GeneralPlanEnvironment.environment plan) (job.context plan)
      job.equation.rule.premises captured completed history)
    (finished : finish plan bound expected job trace captured completed history = some receipt) :
    Completion plan bound expected source receipt := by
  obtain ⟨capturedTyped, completedTyped, raw, reduct, accepted, equal⟩ := finish_readout _ _ _ _ _ _ _ _ _ finished
  subst receipt
  exact ⟨licensed, sourceTyped, matched, capturedTyped, premises, completedTyped, reduct, accepted, rfl⟩

/-- Every independently valid completion passes the actual local checks. The
premise machine supplies that completion and earns its enumeration coverage. -/
theorem finish_complete {plan : Plan}
    {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern} {receipt : Receipt}
    (complete : Completion plan bound expected source receipt) :
    finish plan bound expected receipt.job receipt.matcherTrace receipt.captured receipt.completed receipt.premiseHistory = some receipt := by
  unfold finish
  rw [if_pos (by simp only [Bool.and_eq_true]; exact ⟨GeneralPremise.checkTypedAssignment_complete complete.capturedTyped,
    GeneralPremise.checkTypedAssignment_complete complete.completedTyped⟩)]
  simp only [complete.reduct, Option.bind_eq_bind, Option.bind_some]
  rw [if_pos ((acceptable_iff plan bound expected receipt.job receipt.rawReduct).mpr complete.accepted)]
  apply congrArg some
  cases receipt
  simp only [Receipt.mk.injEq, true_and]
  exact complete.endpoint.symm

/-- Size and support are consequences of the checked schema and the actual
matching/premise derivations. Extra premise outputs do not enlarge a balanced
equation's target, because its relevant original captures remain unchanged. -/
theorem Completion.preserves {plan : Plan} {bound : List TypeExpr} {expected : TypeExpr}
    {source : Pattern} {receipt : Receipt} {symbols : Alphabet}
    (complete : Completion plan bound expected source receipt)
    (accepted : checkRule receipt.job.equation.rule receipt.job.equation.binding.spec = true)
    (canonical : source.hasCanonicalBinderMetadata = true)
    (supported : Supported symbols source)
    (template : Supported symbols receipt.job.equation.rule.right) :
    nodes receipt.target = nodes source ∧ Supported symbols receipt.target := by
  have selected := complete.job.2.source_eq
  have focusCanonical := canonical_redex receipt.job.site.context receipt.job.site.focus (selected.symm ▸ canonical)
  have matching : receipt.captured ∈ matchRuleAt receipt.job.equation.rule receipt.job.equation.binding.spec
      receipt.job.site.focusBound.length receipt.job.site.focus := by
    apply matchRuleAt_iff.mpr
    simpa only [Pattern.eraseBinderMetadata_eq_self_of_canonical focusCanonical] using complete.matched.matching
  have extension : Extends receipt.captured receipt.completed := complete.premises.extension
  have callerSupport : Supported symbols (receipt.job.site.context.fill receipt.job.site.focus) := selected.symm ▸ supported
  have reductSupport := balanced_reduct_supported accepted (supported_redex callerSupport) template matching extension complete.reduct
  have same := matched_reduct_preserves_nodes accepted matching extension complete.reduct
  constructor
  · rw [complete.endpoint, eraseBinderMetadata_nodes]
    have localSame : nodes receipt.job.site.focus = nodes receipt.rawReduct.eraseBinderMetadata :=
      same.trans (eraseBinderMetadata_nodes receipt.rawReduct).symm
    rw [← fill_preserves_nodes receipt.job.site.context receipt.job.site.focus receipt.rawReduct.eraseBinderMetadata localSame, selected]
  · rw [complete.endpoint]
    exact supported_erase (fill_preserves_support receipt.job.site.context receipt.job.site.focus
      receipt.rawReduct.eraseBinderMetadata callerSupport (supported_erase reductSupport))

/-- Every checked completion from any member of the root-derived universe
returns to that same universe, including arbitrary licensed binder contexts. -/
theorem Completion.universe_closed {plan : Plan} {bound : List TypeExpr} {expected : TypeExpr}
    {root source : Pattern} {providerTerms : List Pattern} {receipt : Receipt}
    (complete : Completion plan bound expected source receipt)
    (accepted : checkRule receipt.job.equation.rule receipt.job.equation.binding.spec = true)
    (template : Supported (alphabet plan.snapshot.language root providerTerms) receipt.job.equation.rule.right)
    (member : source ∈ sourceUniverse plan.snapshot.language plan.snapshot.free bound expected root providerTerms) :
    receipt.target ∈ sourceUniverse plan.snapshot.language plan.snapshot.free bound expected root providerTerms := by
  have sourceChecked := typedUniverse_sound _ _ _ _ _ _ _ _ member
  have sourceSupport := sourceUniverse_supported _ _ _ _ _ _ _ member
  have preserved := complete.preserves accepted sourceChecked.2.2.1 sourceSupport template
  have targetTyped : OpenPatternWellSorted plan.snapshot.language plan.snapshot.free bound expected receipt.target := by
    rw [complete.endpoint]
    exact (GeneralPlanEnvironment.typing_iff plan bound expected _).mp complete.accepted.2.2
  have small : nodes receipt.target ≤ nodes root := preserved.1 ▸ sourceChecked.1
  apply typedUniverse_complete _ _ _ _ _ _ _ _ targetTyped small preserved.2
  exact scoped_indices _ _ bound.length (nodes root) small targetTyped.2.2.2
    (fun arity occurs => arity_le_maximum _ arity (preserved.2.2.2 arity occurs))

/-- A complete compiler plan earns equation balance from every selected
authored declaration and orientation; no closure assertion is supplied. -/
theorem compiled_equation_checked {snapshot : Snapshot} {permissions : Permissions} {equationPlan : EquationPlan}
    (complete : (compile snapshot permissions).complete = true)
    (member : equationPlan ∈ (compile snapshot permissions).equations) :
    checkRule equationPlan.rule equationPlan.binding.spec = true := by
  obtain ⟨equation, index, direction, authored, enabled, allowed, compiled⟩ := compiled_equation_origin member
  obtain ⟨other, _, otherCompiled, finite⟩ := complete_equation_coverage complete authored enabled allowed
  have same : other = equationPlan := Option.some.inj (otherCompiled.symm.trans compiled)
  subst other
  have readout := equationPlan_readout compiled
  exact readout.2.2.2.2.2.2.symm.trans finite

/-- Equation target symbols come from the authored language itself, even
when the binding specification was inferred rather than explicitly authored. -/
theorem compiled_equation_template {snapshot : Snapshot} {permissions : Permissions}
    {equationPlan : EquationPlan} (member : equationPlan ∈ (compile snapshot permissions).equations)
    (root : Pattern) (providerTerms : List Pattern) :
    Supported (alphabet snapshot.language root providerTerms) equationPlan.rule.right := by
  obtain ⟨equation, index, direction, authored, _, _, compiled⟩ := compiled_equation_origin member
  have readout := equationPlan_readout compiled
  have declared : equation ∈ snapshot.language.equations := List.fst_mem_of_mem_zipIdx authored
  rw [EquationPlan.rule, readout.2.1, readout.2.2.1]
  have endpoints : ∀ endpoint ∈ [equation.left, equation.right],
      Supported (alphabet snapshot.language root providerTerms) endpoint := by
    intro endpoint occurs
    apply supported_fromPatterns _ endpoint
    simp only [List.mem_cons, List.mem_append, languagePatterns, List.mem_flatMap]
    exact Or.inr (Or.inl (Or.inl ⟨equation, declared, by simpa only [List.mem_cons] using occurs⟩))
  cases direction with
  | forward => exact endpoints equation.right (by simp)
  | reverse => exact endpoints equation.left (by simp)

/-- Principal closure theorem for every accepted snapshot and every term
in its source-derived carrier. It has no language-specific state decoder. -/
theorem compiled_completion_universe_closed {snapshot : Snapshot} {permissions : Permissions}
    {bound : List TypeExpr} {expected : TypeExpr} {root source : Pattern}
    {providerTerms : List Pattern} {receipt : Receipt}
    (accepted : (compile snapshot permissions).complete = true)
    (complete : Completion (compile snapshot permissions) bound expected source receipt)
    (member : source ∈ sourceUniverse snapshot.language snapshot.free bound expected root providerTerms) :
    receipt.target ∈ sourceUniverse snapshot.language snapshot.free bound expected root providerTerms := by
  have declared : receipt.job.equation ∈ (compile snapshot permissions).equations :=
    List.fst_mem_of_mem_zipIdx complete.job.1
  exact complete.universe_closed (compiled_equation_checked accepted declared)
    (compiled_equation_template declared root providerTerms) member

end Mettapedia.OSLF.MeTTaIL.GeneralEquationJobs
