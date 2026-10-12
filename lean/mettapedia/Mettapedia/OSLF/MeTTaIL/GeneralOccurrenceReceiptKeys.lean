import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseEventEquality

/-!
# Complete occurrence keys for retained frontier evidence

Selected declaration positions and exact typed sites recover the authored
declaration from its checked plan. The remaining key retains every matching
choice, assignment, ordered premise event and target. Equation conversion
detours stay in the receipt while the physical occurrence key excludes them.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceKeys

open GeneralExecutionAdmission GeneralTypedSites

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

structure EquationReceipt where
  job : Nat × SiteData
  trace : List GeneralScopedMatchMachine.BagChoice
  captured : ScopedRuleMatching.Assignment
  completed : ScopedRuleMatching.Assignment
  history : List GeneralPremise.Event
  rawReduct : Syntax.Pattern
  target : Syntax.Pattern
  deriving DecidableEq

structure RuleReceipt where
  job : Nat × SiteData
  trace : List GeneralScopedMatchMachine.BagChoice
  captured : ScopedRuleMatching.Assignment
  completed : ScopedRuleMatching.Assignment
  history : List GeneralPremise.Event
  localTarget : Syntax.Pattern
  target : Syntax.Pattern
  deriving DecidableEq

def equationReceipt (receipt : GeneralEquationJobs.Receipt) : EquationReceipt :=
  ⟨equationJob receipt.job, receipt.matcherTrace, receipt.captured, receipt.completed,
    receipt.premiseHistory, receipt.rawReduct, receipt.target⟩

def ruleReceipt (receipt : GeneralRuleJobs.Receipt) : RuleReceipt :=
  ⟨ruleJob receipt.job, receipt.matcherTrace, receipt.captured, receipt.completed,
    receipt.premiseHistory, receipt.localTarget, receipt.target⟩

theorem equationReceipt_injective {plan : Plan} {bound : List Syntax.TypeExpr}
    {type : Syntax.TypeExpr} {source : Syntax.Pattern} {first second : GeneralEquationJobs.Receipt}
    (firstValid : GeneralEquationJobs.Completion plan bound type source first)
    (secondValid : GeneralEquationJobs.Completion plan bound type source second)
    (same : equationReceipt first = equationReceipt second) : first = second := by
  have jobs := congrArg EquationReceipt.job same
  have jobSame := equationJob_injective firstValid.job secondValid.job jobs
  cases first
  cases second
  simp only [equationReceipt, EquationReceipt.mk.injEq] at same
  rcases same with ⟨_, trace, captured, completed, history, reduct, target⟩
  subst_vars
  rfl

theorem ruleReceipt_injective {plan : Plan} {bound : List Syntax.TypeExpr}
    {type : Syntax.TypeExpr} {source : Syntax.Pattern} {first second : GeneralRuleJobs.Receipt}
    (firstValid : first.Valid plan bound type source)
    (secondValid : second.Valid plan bound type source)
    (same : ruleReceipt first = ruleReceipt second) : first = second := by
  have jobs := congrArg RuleReceipt.job same
  have jobSame := ruleJob_injective firstValid.1 secondValid.1 jobs
  cases first
  cases second
  simp only [ruleReceipt, RuleReceipt.mk.injEq] at same
  rcases same with ⟨_, trace, captured, completed, history, reduct, target⟩
  subst_vars
  rfl

def occurrence (receipt : GeneralOccurrenceSemantics.Receipt) : Syntax.Pattern × RuleReceipt :=
  ⟨receipt.representative, ruleReceipt receipt.firing⟩

theorem occurrence_ignores_detours (representative : Syntax.Pattern)
    (first second : List GeneralOccurrenceSemantics.Conversion) (firing : GeneralRuleJobs.Receipt) :
    occurrence ⟨representative, first, firing⟩ = occurrence ⟨representative, second, firing⟩ := rfl

theorem occurrence_target {first second : GeneralOccurrenceSemantics.Receipt}
    (same : occurrence first = occurrence second) : first.target = second.target :=
  congrArg (fun key => key.2.target) same

end Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceKeys
