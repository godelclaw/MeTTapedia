import Mettapedia.OSLF.NativeTypes.Modal.Equations

open Mettapedia.OSLF.Framework

/-!
# Equation conversion through a licensed binder context

The proof constructs contextual equation receipts. Binder descent is governed
by the actual operational permissions and typing context. It is not supplied
as an assumed equation-preservation law for an arbitrary function.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.ContextEquations

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.OSLF.MeTTaIL.GeneralTypedSites
open Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceSemantics
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence
open Mettapedia.OSLF.NativeTypes.Modal.Rules
open Mettapedia.OSLF.NativeTypes.Modal.Equations

private theorem typed_lambda {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {domain codomain : TypeExpr} {body : Pattern}
    (typed : OpenPatternWellSorted language free (domain :: bound) codomain body) :
    OpenPatternWellSorted language free bound (.arrow domain codomain) (.lambda none body) := by
  refine ⟨.lambda typed.1, ?_, ?_, ?_⟩
  · simpa only [Pattern.hasCanonicalBinderMetadata, Option.isNone_none, Bool.true_and] using typed.2.1
  · exact typed.2.2.1
  · simpa only [ScopeSafeAt, Pattern.isWellScopedAt, List.length_cons, Nat.add_comm] using typed.2.2.2

def underLambda (domain : TypeExpr) (receipt : GeneralEquationJobs.Receipt) : GeneralEquationJobs.Receipt :=
  {receipt with
    job := {receipt.job with site := receipt.job.site.wrapLambda none domain}
    target := .lambda none receipt.target}

/-- Wrapping retains the original equation declaration, scoped matcher and
premise witnesses. The local binder context of those witnesses is unchanged. -/
theorem underLambda_complete {plan : Plan} {bound : List TypeExpr} {domain codomain : TypeExpr}
    {source : Pattern} {receipt : GeneralEquationJobs.Receipt}
    (permitted : plan.permissions.sites.underLambda = true)
    (complete : GeneralEquationJobs.Completion plan (domain :: bound) codomain source receipt) :
    GeneralEquationJobs.Completion plan bound (.arrow domain codomain)
      (.lambda none source) (underLambda domain receipt) := by
  refine ⟨⟨complete.job.1, .lambda permitted complete.job.2⟩,
    typed_lambda complete.sourceTyped, complete.matched, complete.capturedTyped,
    complete.premises, complete.completedTyped, complete.reduct, ?_, ?_⟩
  · refine ⟨complete.accepted.1, complete.accepted.2.1, ?_⟩
    simpa only [underLambda, SiteData.wrapLambda, OneHoleContext.fill,
      Pattern.eraseBinderMetadata] using typed_lambda complete.accepted.2.2
  · simp only [underLambda, SiteData.wrapLambda, OneHoleContext.fill,
      Pattern.eraseBinderMetadata, complete.endpoint]

/-- Actual equation events lift under an enabled binder, with its sorted
bound variable included in the original equation's ambient context. -/
theorem equation_under_lambda {plan : Plan} {bound : List TypeExpr} {domain codomain : TypeExpr}
    {source target : Pattern}
    (permitted : plan.permissions.sites.underLambda = true)
    (equation : Equation plan (domain :: bound) codomain source target) :
    Equation plan bound (.arrow domain codomain) (.lambda none source) (.lambda none target) := by
  obtain ⟨receipt, complete, endpoint⟩ := equation
  exact ⟨underLambda domain receipt, underLambda_complete permitted complete,
    congrArg (Pattern.lambda none) endpoint⟩

/-- The complete, arbitrary-length equation conversion law for this
independently licensed nontrivial context. -/
theorem conversion_under_lambda {plan : Plan} {bound : List TypeExpr} {domain codomain : TypeExpr}
    {source target : Pattern}
    (permitted : plan.permissions.sites.underLambda = true)
    (equivalent : Relation.EqvGen (Equation plan (domain :: bound) codomain) source target) :
    Relation.EqvGen (Equation plan bound (.arrow domain codomain))
      (.lambda none source) (.lambda none target) := by
  induction equivalent with
  | rel source target equation => exact .rel _ _ (equation_under_lambda permitted equation)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

/-- Equations preserve carrier typing even on the isolated reflexive classes
whose terms do not satisfy all operational admission predicates. -/
theorem conversion_carrier_iff {plan : Plan} {bound : List TypeExpr} {carrier : TypeExpr}
    {source target : Pattern} (equivalent : Relation.EqvGen (Equation plan bound carrier) source target) :
    HasType plan.snapshot.language plan.snapshot.free bound source carrier ↔
      HasType plan.snapshot.language plan.snapshot.free bound target carrier := by
  induction equivalent with
  | rel source target equation =>
      have typed := equation_sorted equation
      have left := (GeneralPlanEnvironment.typing_iff plan bound carrier source).mp typed.1
      have right := (GeneralPlanEnvironment.typing_iff plan bound carrier target).mp typed.2
      exact ⟨fun _ => right.1, fun _ => left.1⟩
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

theorem root_fill {plan : Plan} (schema : Schema plan) (root : schema.position = [])
    (assignment : ScopedRuleMatching.Assignment) (term : Pattern) :
    schema.fill? assignment term = some term := by
  unfold Schema.fill?
  rw [root]
  cases schema.declaration.rule.left <;> simp only [Mettapedia.OSLF.NativeTypes.Modal.Instantiation.fill?]

/-- At the root slot the former descends along the full actual equation
conversion relation, preserving its anchor and every primitive origin. -/
theorem root_inhabits_equation_iff {plan : Plan} {schema : Schema plan}
    {A : String → RuleBinding.ContextualValue → Prop} {B : Continuation}
    {source target : Pattern} (root : schema.position = [])
    (bound : schema.focusBound = schema.bound) (carrier : schema.focusCarrier = schema.programCarrier)
    (equivalent : Relation.EqvGen (Equation plan schema.bound schema.programCarrier) source target) :
    Inhabits schema A B source ↔ Inhabits schema A B target := by
  suffices forward : ∀ first second, Relation.EqvGen
      (Equation plan schema.bound schema.programCarrier) first second →
      Inhabits schema A B first → Inhabits schema A B second by
    exact ⟨forward source target equivalent,
      forward target source (.symm source target equivalent)⟩
  intro first second converted
  rintro ⟨implementation⟩
  obtain ⟨administration, path⟩ := (conversion_iff_path plan schema.bound schema.programCarrier second first).mp
    (.symm first second converted)
  refine ⟨{ carrier := ?_
            anchor := implementation.anchor
            anchorTyped := implementation.anchorTyped
            anchorPresent := implementation.anchorPresent
            respond := fun assignment request => ?_ }⟩
  · rw [bound, carrier]
    apply (conversion_carrier_iff converted).mp
    simpa only [← bound, ← carrier] using implementation.carrier
  · let outcome := implementation.respond assignment request
    have firstSource : outcome.source = first :=
      Option.some.inj (outcome.filling.symm.trans (root_fill schema root assignment first))
    have sourcePath : ConversionPath plan schema.bound schema.programCarrier second outcome.source administration := by
      rw [firstSource]
      exact path
    exact {source := second
           target := outcome.target
           filling := root_fill schema root assignment second
           rhs := outcome.rhs
           receipt := rebase administration outcome.receipt
           valid := rebase_valid sourcePath outcome.valid
           targetConversion := outcome.targetConversion
           certificate := outcome.certificate}

end Mettapedia.OSLF.NativeTypes.Modal.ContextEquations
