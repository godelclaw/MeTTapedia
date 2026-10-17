import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceModalReadouts

/-!
# Coverage manifests checked against retained execution evidence

The external manifest is ordinary decidable data. It retains the complete
request, ordered physical occurrence keys, conversion paths and archived
job keys. The checker compares it with an actual retained dependent state
and runs that state's coverage certificate. A manifest cannot create an
illicit proof-bearing receipt or change the snapshot to which it applies.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier.CoverageClaims

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralExecutionAdmission
open GeneralOccurrenceKeys GeneralOccurrenceSemantics GeneralTypedSites

structure AuthoredLaw where
  name : String
  typeContext : List (String × TypeExpr)
  premises : List Premise
  left : Pattern
  right : Pattern
  bindings : Option RuleBindingSpec
  deriving DecidableEq

def rewriteKey (rule : RewriteRule) : AuthoredLaw :=
  ⟨rule.name, rule.typeContext, rule.premises, rule.left, rule.right, rule.bindings⟩

def equationKey (equation : Equation) : AuthoredLaw :=
  ⟨equation.name, equation.typeContext, equation.premises,
    equation.left, equation.right, equation.bindings⟩

def AuthoredLaw.rewrite (law : AuthoredLaw) : RewriteRule :=
  ⟨law.name, law.typeContext, law.premises, law.left, law.right, law.bindings⟩

def AuthoredLaw.equation (law : AuthoredLaw) : Equation :=
  ⟨law.name, law.typeContext, law.premises, law.left, law.right, law.bindings⟩

theorem rewriteKey_decode (rule : RewriteRule) : (rewriteKey rule).rewrite = rule := by
  cases rule
  rfl

theorem equationKey_decode (equation : Equation) : (equationKey equation).equation = equation := by
  cases equation
  rfl

structure AuthoredLanguage where
  name : String
  types : List TypeDecl
  terms : List GrammarRule
  equations : List AuthoredLaw
  rewrites : List AuthoredLaw
  deriving DecidableEq

def languageKey (language : LanguageDef) : AuthoredLanguage :=
  ⟨language.name, language.types, language.terms,
    language.equations.map equationKey, language.rewrites.map rewriteKey⟩

def AuthoredLanguage.decode (language : AuthoredLanguage) : LanguageDef :=
  ⟨language.name, language.types, language.terms,
    language.equations.map AuthoredLaw.equation, language.rewrites.map AuthoredLaw.rewrite⟩

theorem languageKey_decode (language : LanguageDef) : (languageKey language).decode = language := by
  cases language
  simp only [languageKey, AuthoredLanguage.decode, List.map_map]
  simp only [Function.comp_def, equationKey_decode, rewriteKey_decode, List.map_id']

structure SnapshotKey where
  language : AuthoredLanguage
  freeTypes : List (String × TypeExpr)
  provider : GeneralPremise.ProviderSnapshot
  deriving DecidableEq

def snapshotKey (snapshot : Snapshot) : SnapshotKey :=
  ⟨languageKey snapshot.language, snapshot.freeTypes, snapshot.provider⟩

def SnapshotKey.decode (snapshot : SnapshotKey) : Snapshot :=
  ⟨snapshot.language.decode, snapshot.freeTypes, snapshot.provider⟩

theorem snapshotKey_decode (snapshot : Snapshot) : (snapshotKey snapshot).decode = snapshot := by
  cases snapshot
  simp only [snapshotKey, SnapshotKey.decode, languageKey_decode]

structure RulePlanKey where
  declarationIndex : Nat
  authored : AuthoredLaw
  binding : GeneralRuleBindingInference.BindingPlan
  deriving DecidableEq

def rulePlanKey (rule : RulePlan) : RulePlanKey :=
  ⟨rule.declarationIndex, rewriteKey rule.authored, rule.binding⟩

def RulePlanKey.decode (rule : RulePlanKey) : RulePlan :=
  ⟨rule.declarationIndex, rule.authored.rewrite, rule.binding⟩

theorem rulePlanKey_decode (rule : RulePlan) : (rulePlanKey rule).decode = rule := by
  cases rule
  simp only [rulePlanKey, RulePlanKey.decode, rewriteKey_decode]

structure EquationPlanKey where
  declarationIndex : Nat
  authored : AuthoredLaw
  direction : ScopedEquationExecution.Orientation
  binding : GeneralRuleBindingInference.BindingPlan
  coverageReady : Bool
  deriving DecidableEq

def equationPlanKey (equation : EquationPlan) : EquationPlanKey :=
  ⟨equation.declarationIndex, equationKey equation.authored,
    equation.direction, equation.binding, equation.coverageReady⟩

def EquationPlanKey.decode (equation : EquationPlanKey) : EquationPlan :=
  ⟨equation.declarationIndex, equation.authored.equation,
    equation.direction, equation.binding, equation.coverageReady⟩

theorem equationPlanKey_decode (equation : EquationPlan) :
    (equationPlanKey equation).decode = equation := by
  cases equation
  simp only [equationPlanKey, EquationPlanKey.decode, equationKey_decode]

structure PlanKey where
  snapshot : SnapshotKey
  permissions : Permissions
  rules : List RulePlanKey
  equations : List EquationPlanKey
  obligations : List GeneralExecutionAdmission.Obligation
  deriving DecidableEq

def planKey (plan : Plan) : PlanKey :=
  ⟨snapshotKey plan.snapshot, plan.permissions,
    plan.rules.map rulePlanKey, plan.equations.map equationPlanKey, plan.obligations⟩

def PlanKey.decode (plan : PlanKey) : Plan :=
  ⟨plan.snapshot.decode, plan.permissions,
    plan.rules.map RulePlanKey.decode, plan.equations.map EquationPlanKey.decode, plan.obligations⟩

theorem planKey_decode (plan : Plan) : (planKey plan).decode = plan := by
  cases plan
  simp only [planKey, PlanKey.decode, snapshotKey_decode, List.map_map]
  simp only [Function.comp_def, rulePlanKey_decode, equationPlanKey_decode, List.map_id']

structure RequestKey where
  plan : PlanKey
  bound : List TypeExpr
  expected : TypeExpr
  source : Pattern
  deriving DecidableEq

def requestKey (request : Request) : RequestKey :=
  ⟨planKey request.plan, request.bound, request.expected, request.source⟩

def RequestKey.decode (request : RequestKey) : Request :=
  ⟨request.plan.decode, request.bound, request.expected, request.source⟩

theorem requestKey_decode (request : Request) : (requestKey request).decode = request := by
  cases request
  simp only [requestKey, RequestKey.decode, planKey_decode]

theorem requestKey_injective : Function.Injective requestKey := by
  intro first second same
  have decoded := congrArg RequestKey.decode same
  simpa only [requestKey_decode] using decoded

def conversionKey : Conversion → Bool × EquationReplayRecord
  | .forward receipt => (true, equationReplayRecord receipt)
  | .reverse receipt => (false, equationReplayRecord receipt)

structure Manifest where
  request : RequestKey
  representatives : List Pattern
  occurrences : List (Pattern × RuleReplayRecord)
  conversions : List (List (Bool × EquationReplayRecord))
  edges : List (Pattern × EquationReplayRecord)
  ruleArchives : List (Pattern × (Nat × SiteData))
  equationArchives : List (Pattern × (Nat × SiteData))
  deriving DecidableEq

def read (request : Request) (state : State request) : Manifest :=
  ⟨requestKey request, representedPatterns request state, answerKeys request state,
    state.answers.map (fun answer => answer.val.conversions.map conversionKey),
    edgeKeys request state,
    state.checkedRules.map (fun archive =>
      (archive.frame.representative.pattern, ruleJob archive.frame.job)),
    state.checkedEquations.map (fun archive =>
      (archive.frame.source, equationJob archive.frame.job))⟩

def check (request : Request) (state : State request) (manifest : Manifest) : Bool :=
  decide (manifest = read request state) && checkCertificate request state

theorem check_iff (request : Request) (state : State request) (manifest : Manifest) :
    check request state manifest = true ↔
      manifest = read request state ∧ checkCertificate request state = true := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq]

theorem request_agreement {request : Request} {state : State request} {manifest : Manifest}
    (checked : check request state manifest = true) : manifest.request.decode = request := by
  have same := congrArg Manifest.request ((check_iff _ _ _).mp checked).1
  have decoded := congrArg RequestKey.decode same
  exact decoded.trans (requestKey_decode request)

/-- Occurrence coverage retains the full firing key, including authored
declaration, typed site, matcher alternatives and ordered premise evidence. -/
theorem occurrence_coverage {request : Request} {state : State request} {manifest : Manifest}
    (admitted : Admitted request) (checked : check request state manifest = true)
    (source : Pattern) (related : Relation.EqvGen
      (Equation request.plan request.bound request.expected) request.root source)
    (receipt : GeneralRuleJobs.Receipt)
    (valid : receipt.Valid request.plan request.bound request.expected source) :
    (source, ruleReplayRecord receipt) ∈ manifest.occurrences := by
  obtain ⟨same, certified⟩ := (check_iff _ _ _).mp checked
  obtain ⟨answer, member, representative, firing⟩ :=
    certified_physical_occurrence admitted certified source related receipt valid
  rw [same]
  exact List.mem_map.mpr ⟨answer, member, by
    simp only [replayOccurrence, representative, firing]⟩

/-- Endpoint coverage is stated separately and allows only the independently
specified equation equivalence after each retained physical firing. -/
theorem endpoint_coverage {request : Request} {state : State request} {manifest : Manifest}
    (admitted : Admitted request) (checked : check request state manifest = true) (target : Pattern) :
    (∃ key ∈ manifest.occurrences,
      Relation.EqvGen (Equation request.plan request.bound request.expected) key.2.target target) ↔
      (gslt request.plan request.bound request.expected).Step request.root target := by
  obtain ⟨same, certified⟩ := (check_iff _ _ _).mp checked
  rw [same]
  change (∃ key ∈ answerKeys request state, Relation.EqvGen
    (Equation request.plan request.bound request.expected) key.2.target target) ↔ _
  rw [← certified_successor_classes admitted certified target]
  simp only [answerKeys, replayOccurrence, List.mem_map]
  constructor
  · rintro ⟨key, ⟨answer, member, equal⟩, related⟩
    subst key
    exact ⟨answer, member, related⟩
  · rintro ⟨answer, member, related⟩
    exact ⟨replayOccurrence answer.val, ⟨answer, member, rfl⟩, related⟩

end Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier.CoverageClaims
