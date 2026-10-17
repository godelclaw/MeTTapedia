import Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrenceChecking
import Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrenceLocalReplacement
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchReplay
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseRecipeChecking
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceSemantics

/-!
# Rewrite recipes for an authored language

A recipe selects an actual rule occurrence, its scoped matching choices and
premise derivations. Equation conversions may precede and follow that firing.
The independent judgments remain the existing occurrence, premise and
equation semantics. StepTrace validation computes against those judgments;
its coverage theorem concerns every finite derivation in that presentation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipe

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax ScopedRuleMatching GeneralExecutionAdmission GeneralTypedSites
open GeneralOccurrenceSemantics
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence

private local instance : DecidableEq RewriteRule := fun first second => by
  cases first
  cases second
  exact decidable_of_iff' _ (Iff.of_eq (RewriteRule.mk.injEq _ _ _ _ _ _ _ _ _ _ _ _))

private local instance : DecidableEq Syntax.Equation := fun first second => by
  cases first
  cases second
  exact decidable_of_iff' _ (Iff.of_eq (Syntax.Equation.mk.injEq _ _ _ _ _ _ _ _ _ _ _ _))

private local instance : DecidableEq RulePlan := fun first second => by
  cases first
  cases second
  exact decidable_of_iff' _ (Iff.of_eq (RulePlan.mk.injEq _ _ _ _ _ _))

private local instance : DecidableEq EquationPlan := fun first second => by
  cases first
  cases second
  exact decidable_of_iff' _ (Iff.of_eq (EquationPlan.mk.injEq _ _ _ _ _ _ _ _ _ _))

/-- Check the selected declaration by position and replay its supplied typed
site. Other source sites are not generated. -/
def checkRuleJob (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)
    (source : Pattern) (job : GeneralRuleJobs.Job) : Bool :=
  decide (plan.rules[job.ordinal]? = some job.declaration) &&
    Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrenceChecking.check
      (GeneralPlanEnvironment.environment plan).language plan.snapshot.free
      plan.permissions.sites bound type source job.site

theorem checkRuleJob_exact (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)
    (source : Pattern) (job : GeneralRuleJobs.Job) :
    checkRuleJob plan bound type source job = true ↔ job.Valid plan bound type source := by
  simp only [checkRuleJob, GeneralRuleJobs.Job.Valid, Bool.and_eq_true, decide_eq_true_eq,
    Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrenceChecking.check_exact,
    List.mk_mem_zipIdx_iff_getElem?]

def checkEquationJob (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)
    (source : Pattern) (job : GeneralEquationJobs.Job) : Bool :=
  decide (plan.equations[job.planPosition]? = some job.equation) &&
    Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrenceChecking.check
      (GeneralPlanEnvironment.environment plan).language plan.snapshot.free
      plan.permissions.sites bound type source job.site

theorem checkEquationJob_exact (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)
    (source : Pattern) (job : GeneralEquationJobs.Job) :
    checkEquationJob plan bound type source job = true ↔
      GeneralEquationJobs.LicensedJob plan bound type source job := by
  simp only [checkEquationJob, GeneralEquationJobs.LicensedJob, Bool.and_eq_true,
    decide_eq_true_eq, Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrenceChecking.check_exact,
    List.mk_mem_zipIdx_iff_getElem?]

/-- Check every field of the original firing evidence. The selected source
site supplies typing for the enclosing term; local target typing and the
representation gate earn its preservation, without rechecking all target
sorts. Source metadata is checked before this preservation is used. -/
def checkFiring (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)
    (source : Pattern) (value : GeneralRuleJobs.Receipt) : Bool :=
  let environment := GeneralPlanEnvironment.environment plan
  checkRuleJob plan bound type source value.job &&
    GeneralPremise.RecipeChecking.checkRoot environment
      value.job.site.focusBound value.job.site.focusType value.job.site.focus value.job.ordinal
      value.matcherTrace value.captured value.completed value.premiseHistory value.localTarget &&
    value.job.site.acceptsReplacementRepresentation environment.language value.localTarget &&
    decide (value.target = value.job.site.context.fill value.localTarget) &&
    source.hasCanonicalBinderMetadata

theorem checkFiring_exact (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)
    (source : Pattern) (value : GeneralRuleJobs.Receipt) :
    checkFiring plan bound type source value = true ↔ value.Valid plan bound type source := by
  simp only [checkFiring, Bool.and_eq_true, decide_eq_true_eq, checkRuleJob_exact,
    GeneralPremise.RecipeChecking.checkRoot_exact]
  constructor
  · rintro ⟨⟨⟨⟨job, firing⟩, represented⟩, endpoint⟩, canonical⟩
    have sourceTyped := job.2.source_typed
    have sourceAdmitted : OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
        plan.snapshot.free bound type source :=
      ⟨sourceTyped, canonical, job.2.source_object, sourceTyped.isWellScopedAt⟩
    have localAdmitted : OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
        plan.snapshot.free value.job.site.focusBound value.job.site.focusType value.localTarget := by
      cases firing
      assumption
    have targetAdmitted := job.2.replace_locally_openPatternWellSorted
      sourceAdmitted value.localTarget represented localAdmitted
    rw [← endpoint] at targetAdmitted
    exact ⟨job, firing, represented, endpoint, targetAdmitted⟩
  · intro valid
    have localSource := (GeneralRuleJobs.receipt_root_readout valid).2.1
    have targetAdmitted := valid.2.2.2.2
    rw [valid.2.2.2.1] at targetAdmitted
    have sourceCore := Mettapedia.GSLT.LanguageDef.WellSorted.OneHoleContext.admissionCore_fill value.job.site.context
      localSource.2.1 localSource.2.2.1 targetAdmitted.2.1 targetAdmitted.2.2.1
    rw [valid.1.2.source_eq] at sourceCore
    exact ⟨⟨⟨⟨valid.1, valid.2.1⟩, valid.2.2.1⟩, valid.2.2.2.1⟩, sourceCore.1⟩

/-- Replay an original firing with its explicitly installed primitive
provider. The guided checker follows the supplied history and never generates
other matching or provider alternatives. Whole-target admission remains a
deterministic check at this service boundary. -/
def checkFiringWith (dynamic : GeneralPremise.DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
    (value : GeneralRuleJobs.Receipt) : Bool :=
  let environment := GeneralPlanEnvironment.environmentWith plan dynamic
  checkRuleJob plan bound type source value.job &&
    GeneralPremise.RecipeChecking.checkRoot environment
      value.job.site.focusBound value.job.site.focusType value.job.site.focus value.job.ordinal
      value.matcherTrace value.captured value.completed value.premiseHistory value.localTarget &&
    value.job.site.acceptsReplacementRepresentation environment.language value.localTarget &&
    decide (value.target = value.job.site.context.fill value.localTarget) &&
    checkOpenPatternWellSorted environment.language plan.snapshot.free bound type value.target

theorem checkFiringWith_exact (dynamic : GeneralPremise.DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
    (value : GeneralRuleJobs.Receipt) :
    checkFiringWith dynamic plan bound type source value = true ↔
      value.ValidWith dynamic plan bound type source := by
  simp only [checkFiringWith, GeneralRuleJobs.Receipt.ValidWith, Bool.and_eq_true,
    decide_eq_true_eq, checkRuleJob_exact, GeneralPremise.RecipeChecking.checkRoot_exact]
  constructor
  · rintro ⟨⟨⟨⟨job, firing⟩, represented⟩, endpoint⟩, typed⟩
    exact ⟨job, firing, represented, endpoint, checkOpenPatternWellSorted_sound typed⟩
  · rintro ⟨job, firing, represented, endpoint, typed⟩
    exact ⟨⟨⟨⟨job, firing⟩, represented⟩, endpoint⟩, checkOpenPatternWellSorted_complete typed⟩

private theorem typedAssignment_exact (environment : GeneralPremise.Environment)
    (context : GeneralPremise.Context) (assignment : Assignment) :
    GeneralPremise.checkTypedAssignment environment context assignment = true ↔
      GeneralPremise.TypedAssignment environment context assignment :=
  ⟨GeneralPremise.checkTypedAssignment_sound, GeneralPremise.checkTypedAssignment_complete⟩

/-- Validate an original equation instance. Metadata erasure is exactly the
one specified by `GeneralEquationJobs.Completion`; it does not erase scope,
typing, selected declaration, premise history or replacement obligations. -/
def checkEquation (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)
    (source : Pattern) (value : GeneralEquationJobs.Receipt) : Bool :=
  let environment := GeneralPlanEnvironment.environment plan
  let job := value.job
  checkEquationJob plan bound type source job &&
    checkOpenPatternWellSorted environment.language plan.snapshot.free bound type source &&
    GeneralScopedMatchReplay.check
      ⟨job.equation.rule, job.equation.binding.spec, job.site.focusBound.length,
        .left, [], 0, [], job.equation.rule.left, job.site.focus.eraseBinderMetadata⟩
      value.matcherTrace value.captured &&
    GeneralPremise.checkTypedAssignment environment (job.context plan) value.captured &&
    GeneralPremise.RecipeChecking.checkPremises environment (job.context plan)
      job.equation.rule.premises value.captured value.completed value.premiseHistory &&
    GeneralPremise.checkTypedAssignment environment (job.context plan) value.completed &&
    decide (reduct? job.equation.rule job.equation.binding.spec job.site.focusBound.length
      value.completed = some value.rawReduct) &&
    GeneralEquationJobs.acceptable plan bound type job value.rawReduct &&
    decide (value.target = (job.site.context.fill value.rawReduct.eraseBinderMetadata).eraseBinderMetadata)

theorem checkEquation_exact (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)
    (source : Pattern) (value : GeneralEquationJobs.Receipt) :
    checkEquation plan bound type source value = true ↔
      GeneralEquationJobs.Completion plan bound type source value := by
  simp only [checkEquation, Bool.and_eq_true, decide_eq_true_eq, checkEquationJob_exact,
    GeneralScopedMatchReplay.check_exact, checkOpenPatternWellSorted_eq_true_iff,
    typedAssignment_exact, GeneralPremise.RecipeChecking.checkPremises_exact,
    GeneralEquationJobs.acceptable_iff]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨job, sourceTyped⟩, matched⟩, captured⟩, premises⟩, completed⟩, reduct⟩, accepted⟩, endpoint⟩
    exact ⟨job, sourceTyped, matched, captured, premises, completed, reduct, accepted, endpoint⟩
  · intro valid
    exact ⟨⟨⟨⟨⟨⟨⟨⟨valid.job, valid.sourceTyped⟩, valid.matched⟩, valid.capturedTyped⟩,
      valid.premises⟩, valid.completedTyped⟩, valid.reduct⟩, valid.accepted⟩, valid.endpoint⟩

/-- The source of equation evidence is reconstructed from its retained zipper
and focus; a reverse conversion cannot invent a different source. -/
def equationSource (value : GeneralEquationJobs.Receipt) : Pattern :=
  value.job.site.context.fill value.job.site.focus

theorem equationSource_eq {plan : Plan} {bound : List TypeExpr} {type : TypeExpr}
    {source : Pattern} {value : GeneralEquationJobs.Receipt}
    (valid : GeneralEquationJobs.Completion plan bound type source value) :
    equationSource value = source := valid.job.2.source_eq

def replayConversion (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)
    (source : Pattern) (conversion : Conversion) : Option Pattern :=
  match conversion with
  | .forward value =>
      if checkEquation plan bound type source value then some value.target else none
  | .reverse value =>
      if value.target = source ∧ checkEquation plan bound type (equationSource value) value = true
      then some (equationSource value) else none

theorem replayConversion_exact (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)
    (source target : Pattern) (conversion : Conversion) :
    replayConversion plan bound type source conversion = some target ↔
      ConversionPath plan bound type source target [conversion] := by
  cases conversion with
  | forward value =>
    simp only [replayConversion]
    constructor
    · intro accepted
      split at accepted
      · next valid =>
          cases Option.some.inj accepted
          exact .cons ((checkEquation_exact _ _ _ _ _).mp valid) rfl (.nil _)
      · contradiction
    · intro path
      cases path with
      | cons valid endpoint tail =>
        cases tail
        simp [endpoint, (checkEquation_exact _ _ _ _ _).mpr valid]
  | reverse value =>
    simp only [replayConversion]
    constructor
    · intro accepted
      split at accepted
      · next valid =>
          cases Option.some.inj accepted
          exact .back ((checkEquation_exact _ _ _ _ _).mp valid.2) valid.1 (.nil _)
      · contradiction
    · intro path
      cases path with
      | back valid endpoint tail =>
        cases tail
        have sourceEq := equationSource_eq valid
        simp [endpoint, sourceEq, (checkEquation_exact _ _ _ _ _).mpr valid]

/-- A conversion walk computes its endpoints while checking each actual
equation application. No equation closure is enumerated. -/
def replayConversions (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)
    (source : Pattern) (conversions : List Conversion) : Option Pattern :=
  match conversions with
  | [] => some source
  | conversion :: rest => do
      let middle ← replayConversion plan bound type source conversion
      replayConversions plan bound type middle rest

theorem replayConversions_exact (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)
    (source target : Pattern) (conversions : List Conversion) :
    replayConversions plan bound type source conversions = some target ↔
      ConversionPath plan bound type source target conversions := by
  induction conversions generalizing source with
  | nil =>
    constructor
    · intro checked
      cases Option.some.inj checked
      exact .nil _
    · intro path
      cases path
      rfl
  | cons conversion rest ih =>
    simp only [replayConversions, Option.bind_eq_bind, Option.bind_eq_some_iff,
      replayConversion_exact, ih]
    constructor
    · rintro ⟨middle, first, tail⟩
      exact ConversionPath.append plan bound type first tail
    · intro path
      cases path with
      | cons valid endpoint tail =>
        exact ⟨_, .cons valid endpoint (.nil _), tail⟩
      | back valid endpoint tail =>
        exact ⟨_, .back valid endpoint (.nil _), tail⟩

def checkConversions (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)
    (source target : Pattern) (conversions : List Conversion) : Bool :=
  decide (replayConversions plan bound type source conversions = some target)

theorem checkConversions_exact (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)
    (source target : Pattern) (conversions : List Conversion) :
    checkConversions plan bound type source target conversions = true ↔
      ConversionPath plan bound type source target conversions := by
  simp only [checkConversions, decide_eq_true_eq, replayConversions_exact]

def Conversion.reversed : Conversion → Conversion
  | .forward value => .reverse value
  | .reverse value => .forward value

def reverseConversions (conversions : List Conversion) : List Conversion :=
  conversions.reverse.map Conversion.reversed

theorem reverseConversions_valid {plan : Plan} {bound : List TypeExpr} {type : TypeExpr}
    {source target : Pattern} {conversions : List Conversion}
    (valid : ConversionPath plan bound type source target conversions) :
    ConversionPath plan bound type target source (reverseConversions conversions) := by
  induction valid with
  | nil => exact .nil _
  | cons complete endpoint _ ih =>
    simpa [reverseConversions, Conversion.reversed] using
      ConversionPath.append plan bound type ih (.back complete endpoint (.nil _))
  | back complete endpoint _ ih =>
    simpa [reverseConversions, Conversion.reversed] using
      ConversionPath.append plan bound type ih (.cons complete endpoint (.nil _))

theorem exists_conversionPath_iff_equiv (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)
    (source target : Pattern) :
    (∃ conversions, ConversionPath plan bound type source target conversions) ↔
      Relation.EqvGen (GeneralOccurrenceSemantics.Equation plan bound type) source target := by
  constructor
  · rintro ⟨_, valid⟩
    exact valid.equivalent
  · intro equivalent
    induction equivalent with
    | rel source target evidence =>
      obtain ⟨value, valid, endpoint⟩ := evidence
      exact ⟨[.forward value], .cons valid endpoint (.nil _)⟩
    | refl source => exact ⟨[], .nil _⟩
    | symm source target _ ih =>
      obtain ⟨conversions, valid⟩ := ih
      exact ⟨reverseConversions conversions, reverseConversions_valid valid⟩
    | trans source middle target _ _ first second =>
      obtain ⟨front, frontValid⟩ := first
      obtain ⟨back, backValid⟩ := second
      exact ⟨front ++ back, ConversionPath.append plan bound type frontValid backValid⟩

/-- A complete primitive rewrite recipe modulo the declared equations.
The original occurrence evidence is retained, with its original source
representative and pre-conversions. Post-conversions justify the final target. -/
structure StepTrace where
  before : GeneralOccurrenceSemantics.Receipt
  after : List Conversion
  deriving Repr

def StepTrace.Valid (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)
    (source target : Pattern) (recipe : StepTrace) : Prop :=
  recipe.before.Valid plan bound type source ∧
    ConversionPath plan bound type recipe.before.target target recipe.after

def check (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)
    (source target : Pattern) (recipe : StepTrace) : Bool :=
  checkConversions plan bound type source recipe.before.representative recipe.before.conversions &&
    checkFiring plan bound type recipe.before.representative recipe.before.firing &&
    checkConversions plan bound type recipe.before.target target recipe.after

theorem check_exact (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)
    (source target : Pattern) (recipe : StepTrace) :
    check plan bound type source target recipe = true ↔ StepTrace.Valid plan bound type source target recipe := by
  simp only [check, StepTrace.Valid, GeneralOccurrenceSemantics.Receipt.Valid,
    Bool.and_eq_true, checkConversions_exact, checkFiring_exact]

theorem exists_valid_iff_step (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)
    (source target : Pattern) :
    (∃ recipe, StepTrace.Valid plan bound type source target recipe) ↔
      (GeneralOccurrenceSemantics.gslt plan bound type).Step source target := by
  constructor
  · rintro ⟨recipe, before, after⟩
    exact ⟨recipe.before.representative, recipe.before.firing,
      before.1.equivalent, before.2, after.equivalent⟩
  · rintro ⟨representative, firing, before, valid, after⟩
    obtain ⟨pre, preValid⟩ := (exists_conversionPath_iff_equiv plan bound type _ _).mpr before
    obtain ⟨post, postValid⟩ := (exists_conversionPath_iff_equiv plan bound type _ _).mpr after
    exact ⟨⟨⟨representative, pre, firing⟩, post⟩, ⟨preValid, valid⟩, postValid⟩

theorem exists_checked_iff_step (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)
    (source target : Pattern) :
    (∃ recipe, check plan bound type source target recipe = true) ↔
      (GeneralOccurrenceSemantics.gslt plan bound type).Step source target := by
  simp only [check_exact, exists_valid_iff_step]

/-- The authored interface compiles the selected snapshot itself. Submitted
plans cannot replace or extend its admitted declaration set. -/
def checkAuthored (snapshot : Snapshot) (permissions : Permissions) (bound : List TypeExpr)
    (type : TypeExpr) (source target : Pattern) (recipe : StepTrace) : Bool :=
  check (compile snapshot permissions) bound type source target recipe

theorem checkAuthored_exact (snapshot : Snapshot) (permissions : Permissions) (bound : List TypeExpr)
    (type : TypeExpr) (source target : Pattern) (recipe : StepTrace) :
    checkAuthored snapshot permissions bound type source target recipe = true ↔
      StepTrace.Valid (compile snapshot permissions) bound type source target recipe :=
  check_exact _ _ _ _ _ _

theorem checked_source_declaration {snapshot : Snapshot} {permissions : Permissions}
    {bound : List TypeExpr} {type : TypeExpr} {source target : Pattern} {recipe : StepTrace}
    (checked : checkAuthored snapshot permissions bound type source target recipe = true) :
    ∃ rule index, (rule, index) ∈ snapshot.language.rewrites.zipIdx ∧
      selected permissions.ruleIndices index = true ∧
      rulePlan? snapshot index rule = some recipe.before.firing.job.declaration :=
  GeneralOccurrenceSemantics.Receipt.source_declaration
    ((checkAuthored_exact _ _ _ _ _ _ _).mp checked).1

end Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipe
