import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceSemantics
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseEventEquality

/-!
# Firing identity and complete replay records

Selected declaration positions and exact typed sites recover the authored
declaration from its checked plan. The remaining key retains every matching
choice, assignment, ordered premise event and target. Equation conversion
detours stay in the receipt while the replay record excludes them. Application
identity separately retains the rule, typed site, assignments and premise
citations; matcher permutations remain guidance in the lossless replay record.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceKeys

open GeneralExecutionAdmission GeneralTypedSites

/-- Identity of one rule application under a fixed authored snapshot.
Declaration and provider occurrence citations remain meaningful source data;
matcher-selection positions and computed endpoints are replay information. -/
structure FiringIdentity where
  rule : RulePlan
  site : SiteData
  captured : ScopedRuleMatching.Assignment
  completed : ScopedRuleMatching.Assignment
  premises : List GeneralPremise.Citation
  deriving Repr

def firingIdentity (receipt : GeneralRuleJobs.Receipt) : FiringIdentity :=
  ⟨receipt.job.declaration, receipt.job.site, receipt.captured, receipt.completed,
    GeneralPremise.citations receipt.premiseHistory⟩

/-- Literal rule/site and final assignment determine both replacement results.
The certificate table position is not needed for this equality. -/
theorem same_application_result {plan : Plan} {bound : List Syntax.TypeExpr} {type : Syntax.TypeExpr}
    {source : Syntax.Pattern} {first second : GeneralRuleJobs.Receipt}
    (firstValid : first.Valid plan bound type source)
    (secondValid : second.Valid plan bound type source)
    (sameRule : first.job.declaration = second.job.declaration)
    (sameSite : first.job.site = second.job.site)
    (sameCompleted : first.completed = second.completed) :
    first.localTarget = second.localTarget ∧ first.target = second.target := by
  have firstReduced := (GeneralRuleJobs.receipt_root_readout firstValid).2.2.2.1
  have secondReduced := (GeneralRuleJobs.receipt_root_readout secondValid).2.2.2.1
  rw [sameRule, sameSite, sameCompleted] at firstReduced
  have localSame := Option.some.inj (firstReduced.symm.trans secondReduced)
  exact ⟨localSame, by
    rw [firstValid.2.2.2.1, secondValid.2.2.2.1, sameSite, localSame]⟩

theorem firingIdentity_preserves_result {plan : Plan} {bound : List Syntax.TypeExpr}
    {type : Syntax.TypeExpr} {source : Syntax.Pattern} {first second : GeneralRuleJobs.Receipt}
    (firstValid : first.Valid plan bound type source)
    (secondValid : second.Valid plan bound type source)
    (same : firingIdentity first = firingIdentity second) :
    first.localTarget = second.localTarget ∧ first.target = second.target :=
  same_application_result firstValid secondValid
    (congrArg FiringIdentity.rule same) (congrArg FiringIdentity.site same)
    (congrArg FiringIdentity.completed same)

def equationJob (job : GeneralEquationJobs.Job) : Nat × SiteData := ⟨job.planPosition, job.site⟩

def ruleJob (job : GeneralRuleJobs.Job) : Nat × SiteData := ⟨job.ordinal, job.site⟩

theorem equationJob_injective {plan : Plan} {bound : List Syntax.TypeExpr}
    {type : Syntax.TypeExpr} {source : Syntax.Pattern} {first second : GeneralEquationJobs.Job}
    (firstLicensed : GeneralEquationJobs.LicensedJob plan bound type source first)
    (secondLicensed : GeneralEquationJobs.LicensedJob plan bound type source second)
    (same : equationJob first = equationJob second) : first = second := by
  have position := congrArg Prod.fst same
  have site := congrArg Prod.snd same
  change first.planPosition = second.planPosition at position
  change first.site = second.site at site
  have firstAt := List.mk_mem_zipIdx_iff_getElem?.mp firstLicensed.1
  have secondAt := List.mk_mem_zipIdx_iff_getElem?.mp secondLicensed.1
  have declaration : first.equation = second.equation := by
    rw [← position] at secondAt
    exact Option.some.inj (firstAt.symm.trans secondAt)
  cases first
  cases second
  dsimp only at position site declaration
  subst_vars
  rfl

theorem ruleJob_injective {plan : Plan} {bound : List Syntax.TypeExpr}
    {type : Syntax.TypeExpr} {source : Syntax.Pattern} {first second : GeneralRuleJobs.Job}
    (firstLicensed : first.Valid plan bound type source)
    (secondLicensed : second.Valid plan bound type source)
    (same : ruleJob first = ruleJob second) : first = second := by
  have position := congrArg Prod.fst same
  have site := congrArg Prod.snd same
  change first.ordinal = second.ordinal at position
  change first.site = second.site at site
  have firstAt := List.mk_mem_zipIdx_iff_getElem?.mp firstLicensed.1
  have secondAt := List.mk_mem_zipIdx_iff_getElem?.mp secondLicensed.1
  have declaration : first.declaration = second.declaration := by
    rw [← position] at secondAt
    exact Option.some.inj (firstAt.symm.trans secondAt)
  cases first
  cases second
  dsimp only at position site declaration
  subst_vars
  rfl

structure EquationReplayRecord where
  job : Nat × SiteData
  trace : List GeneralScopedMatchMachine.BagChoice
  captured : ScopedRuleMatching.Assignment
  completed : ScopedRuleMatching.Assignment
  history : List GeneralPremise.Event
  rawReduct : Syntax.Pattern
  target : Syntax.Pattern
  deriving DecidableEq

structure RuleReplayRecord where
  job : Nat × SiteData
  trace : List GeneralScopedMatchMachine.BagChoice
  captured : ScopedRuleMatching.Assignment
  completed : ScopedRuleMatching.Assignment
  history : List GeneralPremise.Event
  localTarget : Syntax.Pattern
  target : Syntax.Pattern
  deriving DecidableEq

def equationReplayRecord (receipt : GeneralEquationJobs.Receipt) : EquationReplayRecord :=
  ⟨equationJob receipt.job, receipt.matcherTrace, receipt.captured, receipt.completed,
    receipt.premiseHistory, receipt.rawReduct, receipt.target⟩

def ruleReplayRecord (receipt : GeneralRuleJobs.Receipt) : RuleReplayRecord :=
  ⟨ruleJob receipt.job, receipt.matcherTrace, receipt.captured, receipt.completed,
    receipt.premiseHistory, receipt.localTarget, receipt.target⟩

theorem equationReplayRecord_injective {plan : Plan} {bound : List Syntax.TypeExpr}
    {type : Syntax.TypeExpr} {source : Syntax.Pattern} {first second : GeneralEquationJobs.Receipt}
    (firstValid : GeneralEquationJobs.Completion plan bound type source first)
    (secondValid : GeneralEquationJobs.Completion plan bound type source second)
    (same : equationReplayRecord first = equationReplayRecord second) : first = second := by
  have jobs := congrArg EquationReplayRecord.job same
  have jobSame := equationJob_injective firstValid.job secondValid.job jobs
  cases first
  cases second
  simp only [equationReplayRecord, EquationReplayRecord.mk.injEq] at same
  rcases same with ⟨_, trace, captured, completed, history, reduct, target⟩
  subst_vars
  rfl

theorem ruleReplayRecord_injective {plan : Plan} {bound : List Syntax.TypeExpr}
    {type : Syntax.TypeExpr} {source : Syntax.Pattern} {first second : GeneralRuleJobs.Receipt}
    (firstValid : first.Valid plan bound type source)
    (secondValid : second.Valid plan bound type source)
    (same : ruleReplayRecord first = ruleReplayRecord second) : first = second := by
  have jobs := congrArg RuleReplayRecord.job same
  have jobSame := ruleJob_injective firstValid.1 secondValid.1 jobs
  cases first
  cases second
  simp only [ruleReplayRecord, RuleReplayRecord.mk.injEq] at same
  rcases same with ⟨_, trace, captured, completed, history, reduct, target⟩
  subst_vars
  rfl

def replayOccurrence (receipt : GeneralOccurrenceSemantics.Receipt) : Syntax.Pattern × RuleReplayRecord :=
  ⟨receipt.representative, ruleReplayRecord receipt.firing⟩

theorem replayOccurrence_ignores_detours (representative : Syntax.Pattern)
    (first second : List GeneralOccurrenceSemantics.Conversion) (firing : GeneralRuleJobs.Receipt) :
    replayOccurrence ⟨representative, first, firing⟩ = replayOccurrence ⟨representative, second, firing⟩ := rfl

theorem replayOccurrence_target {first second : GeneralOccurrenceSemantics.Receipt}
    (same : replayOccurrence first = replayOccurrence second) : first.target = second.target :=
  congrArg (fun key => key.2.target) same

end Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceKeys
