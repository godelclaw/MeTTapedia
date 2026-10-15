import Mettapedia.OSLF.MeTTaIL.GeneralPlanEnvironment
import Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrenceReplacement

/-!
# Authored rule jobs at all typed occurrences

Each job keeps both its selected execution index and original declaration
index, together with the complete typed zipper. Job enumeration ranges over
the actual compiled declarations and every licensed typing descent.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRuleJobs

open Syntax RuleBinding ScopedRuleMatching GeneralExecutionAdmission GeneralTypedSites
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence

structure Job where
  ordinal : Nat
  declaration : RulePlan
  site : SiteData
  deriving Repr

def jobs (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) (source : Pattern) : List Job :=
  plan.rules.zipIdx.flatMap fun (declaration, ordinal) =>
    (generate (GeneralPlanEnvironment.environment plan).language plan.snapshot.free
      plan.permissions.sites bound type source).map fun site => ⟨ordinal, declaration, site⟩

def Job.Valid (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
    (job : Job) : Prop :=
  (job.declaration, job.ordinal) ∈ plan.rules.zipIdx ∧
    Licensed (GeneralPlanEnvironment.environment plan).language plan.snapshot.free
      plan.permissions.sites bound type source job.site

theorem jobs_spec (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) (source : Pattern) (job : Job) :
    job ∈ jobs plan bound type source ↔ job.Valid plan bound type source := by
  constructor
  · intro present
    obtain ⟨⟨declaration, ordinal⟩, declared, occurrence⟩ := List.mem_flatMap.mp present
    obtain ⟨site, generated, same⟩ := List.mem_map.mp occurrence
    cases same
    exact ⟨declared, (generate_spec _ _ _ _ _ _ _).mp generated⟩
  · rintro ⟨declared, licensed⟩
    exact List.mem_flatMap.mpr ⟨(job.declaration, job.ordinal), declared,
      List.mem_map.mpr ⟨job.site, (generate_spec _ _ _ _ _ _ _).mpr licensed, rfl⟩⟩

def Job.context (job : Job) : GeneralPremise.Context :=
  ⟨job.ordinal, job.declaration.rule, job.declaration.binding.spec, job.site.focusBound, 0, 0⟩

theorem Job.selected_rule {plan : Plan} {bound : List TypeExpr} {type : TypeExpr} {source : Pattern}
    {job : Job} (valid : job.Valid plan bound type source) :
    (GeneralPlanEnvironment.environment plan).language.rewrites[job.ordinal]? = some job.declaration.rule :=
  GeneralPlanEnvironment.selected_rule plan (List.mk_mem_zipIdx_iff_getElem?.mp valid.1)

theorem Job.selected_specification {plan : Plan} {bound : List TypeExpr} {type : TypeExpr} {source : Pattern}
    {job : Job} (valid : job.Valid plan bound type source) :
    GeneralPremise.specification? (GeneralPlanEnvironment.environment plan) job.ordinal =
      some job.declaration.binding.spec :=
  GeneralPlanEnvironment.selected_specification plan (List.mk_mem_zipIdx_iff_getElem?.mp valid.1)

structure Receipt where
  job : Job
  matcherTrace : List GeneralScopedMatchMachine.BagChoice
  captured : Assignment
  completed : Assignment
  premiseHistory : List GeneralPremise.Event
  localTarget : Pattern
  target : Pattern
  deriving Repr

def Receipt.Valid (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
    (receipt : Receipt) : Prop :=
  receipt.job.Valid plan bound type source ∧
    GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan)
      receipt.job.site.focusBound receipt.job.site.focusType receipt.job.site.focus receipt.job.ordinal
      receipt.matcherTrace receipt.captured receipt.completed receipt.premiseHistory receipt.localTarget ∧
    receipt.job.site.acceptsReplacementRepresentation (GeneralPlanEnvironment.environment plan).language
      receipt.localTarget = true ∧
    receipt.target = receipt.job.site.context.fill receipt.localTarget ∧
    OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language plan.snapshot.free
      bound type receipt.target

def finish? (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) (job : Job)
    (trace : List GeneralScopedMatchMachine.BagChoice) (captured completed : Assignment)
    (history : List GeneralPremise.Event) : Option Receipt := do
  let environment := GeneralPlanEnvironment.environment plan
  if admittedFor job.declaration.rule job.declaration.binding.spec &&
      checkOpenPatternWellSorted environment.language environment.free job.site.focusBound
        job.site.focusType job.site.focus &&
      GeneralPremise.checkTypedAssignment environment job.context captured then
    let localTarget ← reductWith? (ScopedReflectiveExecution.binderOperation environment.reflection
      job.declaration.rule) job.declaration.rule job.declaration.binding.spec job.site.focusBound.length completed
    if checkOpenPatternWellSorted environment.language environment.free job.site.focusBound
        job.site.focusType localTarget && job.site.acceptsReplacementRepresentation environment.language localTarget &&
        checkOpenPatternWellSorted environment.language environment.free bound type (job.site.context.fill localTarget) then
      some ⟨job, trace, captured, completed, history, localTarget, job.site.context.fill localTarget⟩
    else none
  else none

theorem finish_sound {plan : Plan} {bound : List TypeExpr} {type : TypeExpr} {source : Pattern}
    {job : Job} {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : Assignment}
    {history : List GeneralPremise.Event} {receipt : Receipt}
    (licensed : job.Valid plan bound type source)
    (matching : GeneralScopedMatchMachine.TracedMatches job.declaration.rule job.declaration.binding.spec
      job.site.focusBound.length .left [] 0 [] job.declaration.rule.left job.site.focus trace captured)
    (premises : GeneralPremise.PremisesHold (GeneralPlanEnvironment.environment plan) job.context
      job.declaration.rule.premises captured completed history)
    (emitted : finish? plan bound type job trace captured completed history = some receipt) :
    receipt.Valid plan bound type source := by
  unfold finish? at emitted
  dsimp only at emitted
  split at emitted
  next ready =>
    simp only [Bool.and_eq_true] at ready
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at emitted
    obtain ⟨localTarget, reduced, emitted⟩ := emitted
    split at emitted
    next checked =>
      simp only [Bool.and_eq_true] at checked
      cases Option.some.inj emitted
      exact ⟨licensed, GeneralPremise.RootFiring.fire (Job.selected_rule licensed) (Job.selected_specification licensed)
        ready.1.1 (checkOpenPatternWellSorted_sound ready.1.2) matching
        (GeneralPremise.checkTypedAssignment_sound ready.2) premises reduced
        (checkOpenPatternWellSorted_sound checked.1.1), checked.1.2, rfl,
        checkOpenPatternWellSorted_sound checked.2⟩
    next => contradiction
  next => contradiction

theorem receipt_root_readout {plan : Plan} {bound : List TypeExpr} {type : TypeExpr} {source : Pattern}
    {receipt : Receipt} (valid : receipt.Valid plan bound type source) :
    admittedFor receipt.job.declaration.rule receipt.job.declaration.binding.spec = true ∧
      OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language plan.snapshot.free
        receipt.job.site.focusBound receipt.job.site.focusType receipt.job.site.focus ∧
      GeneralPremise.TypedAssignment (GeneralPlanEnvironment.environment plan) receipt.job.context receipt.captured ∧
      reductWith? (ScopedReflectiveExecution.binderOperation (GeneralPlanEnvironment.environment plan).reflection
        receipt.job.declaration.rule) receipt.job.declaration.rule receipt.job.declaration.binding.spec
        receipt.job.site.focusBound.length receipt.completed = some receipt.localTarget ∧
      OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language plan.snapshot.free
        receipt.job.site.focusBound receipt.job.site.focusType receipt.localTarget := by
  have selected := Job.selected_rule valid.1
  have specified := Job.selected_specification valid.1
  cases valid.2.1 with
  | @fire bound type source target index rule spec trace captured completed history declared specification
      admitted sourceTyped matching capturedTyped premises reduced targetTyped =>
    have ruleSame : rule = receipt.job.declaration.rule := Option.some.inj (declared.symm.trans selected)
    have specSame : spec = receipt.job.declaration.binding.spec := Option.some.inj (specification.symm.trans specified)
    cases ruleSame
    cases specSame
    exact ⟨admitted, sourceTyped, capturedTyped, reduced, targetTyped⟩

theorem finish_complete {plan : Plan} {bound : List TypeExpr} {type : TypeExpr} {source : Pattern}
    {receipt : Receipt} (valid : receipt.Valid plan bound type source) :
    finish? plan bound type receipt.job receipt.matcherTrace receipt.captured receipt.completed
      receipt.premiseHistory = some receipt := by
  have root := receipt_root_readout valid
  have sourceChecked := checkOpenPatternWellSorted_complete root.2.1
  have captureChecked := GeneralPremise.checkTypedAssignment_complete root.2.2.1
  have localChecked := checkOpenPatternWellSorted_complete root.2.2.2.2
  have globalChecked := checkOpenPatternWellSorted_complete valid.2.2.2.2
  have represented := valid.2.2.1
  have readout := valid.2.2.2.1
  cases receipt with
  | mk job trace captured completed history localTarget target =>
    dsimp only at readout
    subst target
    simp only [finish?, show (GeneralPlanEnvironment.environment plan).free = plan.snapshot.free from rfl,
      root.1, sourceChecked, captureChecked, Bool.true_and, Option.bind_eq_bind, Option.bind_some,
      root.2.2.2.1, localChecked, represented, globalChecked, ↓reduceIte]

end Mettapedia.OSLF.MeTTaIL.GeneralRuleJobs
