import Mettapedia.OSLF.NativeTypes.Modal.Instantiation
import Mettapedia.OSLF.Framework.ModalHypercube
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceNativeReceipts

open Mettapedia.OSLF.Framework

/-!
# Specified-contractum modal rules with dependent continuations

A modal request fills one authored context and instantiates that declaration's
actual scoped right-hand side. An inhabitant implements every typed rely
request. Its result retains an equation conversion, a primitive receipt and a
certificate in the continuation after the full assignment is substituted.

The matched variables retained in that assignment are essential: the
right-hand side can depend on the chosen inhabitant as well as on the rely
variables. It is not replaced by an arbitrary existential successor.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.Rules

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.OSLF.MeTTaIL.GeneralTypedSites
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence
open Mettapedia.OSLF.Framework.RedexPosition
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)

universe u

/-- A selected authored declaration and an actual focus carrier. Generation
supplies the index from the selected plan and the carriers from typing descent. -/
structure Schema (plan : Plan) where
  ordinal : Nat
  declaration : RulePlan
  declared : (declaration, ordinal) ∈ plan.rules.zipIdx
  position : Position
  bound : List TypeExpr
  programCarrier : TypeExpr
  focusBound : List TypeExpr
  focusCarrier : TypeExpr

def Schema.operation {plan : Plan} (schema : Schema plan) : Pattern → Pattern → Pattern :=
  ScopedReflectiveExecution.binderOperation plan.permissions.reflection schema.declaration.rule

def Schema.context {plan : Plan} (schema : Schema plan) : GeneralPremise.Context :=
  ⟨schema.ordinal, schema.declaration.rule, schema.declaration.binding.spec, schema.bound, 0, 0⟩

/-- All surrounding components use the original declaration's scoped metadata. -/
def Schema.fill? {plan : Plan} (schema : Schema plan) (assignment : Assignment)
    (term : Pattern) : Option Pattern :=
  Mettapedia.OSLF.NativeTypes.Modal.Instantiation.fill? schema.operation schema.declaration.rule
    schema.declaration.binding.spec schema.bound.length .left [] 0 assignment term
    schema.declaration.rule.left schema.position

/-- The specified contractum is the scoped instance of the authored RHS. -/
def Schema.rhs? {plan : Plan} (schema : Schema plan) (assignment : Assignment) : Option Pattern :=
  reductWith? schema.operation schema.declaration.rule schema.declaration.binding.spec
    schema.bound.length assignment

def Schema.relyNames {plan : Plan} (schema : Schema plan) : List String :=
  relyVars schema.declaration.rule.left schema.position

/-- Missing rely values do not silently satisfy a rely request. -/
def RelySatisfied {plan : Plan} (schema : Schema plan)
    (A : String → ContextualValue → Prop) (assignment : Assignment) : Prop :=
  ∀ name ∈ schema.relyNames, ∃ value,
    lookup assignment name = some value ∧ A name value

def Schema.matchedNames {plan : Plan} (schema : Schema plan) : List String :=
  ((subtermAt schema.declaration.rule.left schema.position).map fvarNames).getD []

/-- The chosen inhabitant's matched variables stay in the ambient context.
Only its rely inputs vary; the RHS still reads both sets of values. -/
def TypedRequest {plan : Plan} (schema : Schema plan)
    (A : String → ContextualValue → Prop) (anchor assignment : Assignment) : Prop :=
  RelySatisfied schema A assignment ∧
    GeneralPremise.TypedAssignment (GeneralPlanEnvironment.environment plan) schema.context assignment ∧
    (∀ name ∈ schema.matchedNames, lookup assignment name = lookup anchor name) ∧
    (∀ name ∈ (fvarNames schema.declaration.rule.left ++ fvarNames schema.declaration.rule.right),
      ∃ value, lookup assignment name = some value)

/-- A continuation is a family over assignments, not a predicate fixed before
the rely variables and matched variables are substituted. -/
abbrev Continuation := Assignment → Pattern → Type u

def substituteContinuation (B : Continuation.{u}) (assignment : Assignment) : Pattern → Type u :=
  fun target => B assignment target

/-- The complete response to one rely request. Equation administration stays
separate from its one primitive operational occurrence. -/
structure Outcome {plan : Plan} (schema : Schema plan) (term : Pattern)
    (assignment : Assignment) (B : Continuation.{u}) where
  source : Pattern
  target : Pattern
  filling : schema.fill? assignment term = some source
  rhs : schema.rhs? assignment = some target
  receipt : GeneralOccurrenceSemantics.Receipt
  valid : receipt.Valid plan schema.bound schema.programCarrier source
  targetConversion : Relation.EqvGen (GeneralOccurrenceSemantics.Equation plan
    schema.bound schema.programCarrier) receipt.target target
  certificate : substituteContinuation B assignment target

/-- Dependent inhabitants retain an implementation, including every receipt. -/
structure Evidence {plan : Plan} (schema : Schema plan)
    (A : String → ContextualValue → Prop) (B : Continuation.{u}) (term : Pattern) where
  carrier : HasType plan.snapshot.language plan.snapshot.free schema.focusBound term schema.focusCarrier
  anchor : Assignment
  anchorTyped : GeneralPremise.TypedAssignment (GeneralPlanEnvironment.environment plan) schema.context anchor
  anchorPresent : ∀ name ∈ schema.matchedNames, ∃ value, lookup anchor name = some value
  respond : ∀ assignment, TypedRequest schema A anchor assignment → Outcome schema term assignment B

/-- The modal predicate is the support of that complete family. -/
def Inhabits {plan : Plan} (schema : Schema plan) (A : String → ContextualValue → Prop)
    (B : Continuation.{u}) (term : Pattern) : Prop := Nonempty (Evidence schema A B term)

/-- A semantic type code is carrier bounded. Its universe sort is separate
from the term-language carrier, as in the generated hypercube. -/
structure TypeCode (plan : Plan) (bound : List TypeExpr) (carrier : TypeExpr) (sort : HSort) where
  meaning : Pattern → Prop
  bounded : ∀ term, meaning term → HasType plan.snapshot.language plan.snapshot.free bound term carrier

/-- M-FORM constructs a subobject at the chosen focus carrier. -/
def former {plan : Plan} (schema : Schema plan) (sort : HSort)
    (A : String → ContextualValue → Prop) (B : Continuation.{u}) :
    TypeCode plan schema.focusBound schema.focusCarrier sort where
  meaning := Inhabits schema A B
  bounded _ inhabited := inhabited.elim fun evidence => evidence.carrier

theorem m_form {plan : Plan} (schema : Schema plan) (sort : HSort)
    (A : String → ContextualValue → Prop) (B : Continuation.{u}) (term : Pattern)
    (inhabited : (former schema sort A B).meaning term) :
    HasType plan.snapshot.language plan.snapshot.free schema.focusBound term schema.focusCarrier :=
  (former schema sort A B).bounded term inhabited

/-- The premises of an authored introduction are independent scoped matching,
ordered premise derivations and typing. No modal assumption or step oracle
occurs in this record. -/
structure IntroductionCase {plan : Plan} (schema : Schema plan) (term : Pattern)
    (assignment : Assignment) (B : Continuation.{u}) where
  source : Pattern
  target : Pattern
  trace : List GeneralScopedMatchMachine.BagChoice
  captured : Assignment
  history : List GeneralPremise.Event
  focus : Mettapedia.OSLF.NativeTypes.Modal.Instantiation.FocusInstance schema.operation schema.declaration.rule
    schema.declaration.binding.spec schema.bound.length .left assignment [] 0
    schema.declaration.rule.left schema.position term
  sourceInstance : ScopedRuleMatching.instantiateWith? schema.operation schema.declaration.rule
    schema.declaration.binding.spec schema.bound.length .left [] 0 assignment
    schema.declaration.rule.left = some source
  sourceTyped : OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
    plan.snapshot.free schema.bound schema.programCarrier source
  admitted : admittedFor schema.declaration.rule schema.declaration.binding.spec = true
  matching : GeneralScopedMatchMachine.TracedMatches schema.declaration.rule
    schema.declaration.binding.spec schema.bound.length .left [] 0 []
    schema.declaration.rule.left source trace captured
  capturedTyped : GeneralPremise.TypedAssignment (GeneralPlanEnvironment.environment plan)
    schema.context captured
  premises : GeneralPremise.PremisesHold (GeneralPlanEnvironment.environment plan) schema.context
    schema.declaration.rule.premises captured assignment history
  reduct : schema.rhs? assignment = some target
  targetTyped : OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
    plan.snapshot.free schema.bound schema.programCarrier target
  certificate : substituteContinuation B assignment target

def IntroductionCase.primitive {plan : Plan} {schema : Schema plan} {term : Pattern}
    {assignment : Assignment} {B : Continuation.{u}}
    (introduced : IntroductionCase schema term assignment B) : GeneralRuleJobs.Receipt :=
  { job := ⟨schema.ordinal, schema.declaration,
      SiteData.here schema.bound schema.programCarrier introduced.source⟩
    matcherTrace := introduced.trace
    captured := introduced.captured
    completed := assignment
    premiseHistory := introduced.history
    localTarget := introduced.target
    target := introduced.target }

theorem IntroductionCase.valid {plan : Plan} {schema : Schema plan} {term : Pattern}
    {assignment : Assignment} {B : Continuation.{u}}
    (enabled : plan.permissions.sites.enabled = true)
    (introduced : IntroductionCase schema term assignment B) :
    introduced.primitive.Valid plan schema.bound schema.programCarrier introduced.source := by
  have licensed : introduced.primitive.job.Valid plan schema.bound schema.programCarrier introduced.source :=
    ⟨schema.declared, Licensed.here enabled introduced.sourceTyped.2.2.1 introduced.sourceTyped.1⟩
  refine ⟨licensed, ?_, ?_, rfl, introduced.targetTyped⟩
  · exact GeneralPremise.RootFiring.fire (GeneralRuleJobs.Job.selected_rule licensed)
      (GeneralRuleJobs.Job.selected_specification licensed) introduced.admitted introduced.sourceTyped
      introduced.matching introduced.capturedTyped introduced.premises introduced.reduct introduced.targetTyped
  · rfl

/-- M-INTRO constructs the actual scoped primitive receipt. -/
def m_intro {plan : Plan} {schema : Schema plan}
    {A : String → ContextualValue → Prop} {B : Continuation.{u}} {term : Pattern}
    (enabled : plan.permissions.sites.enabled = true)
    (typed : HasType plan.snapshot.language plan.snapshot.free schema.focusBound term schema.focusCarrier)
    (anchor : Assignment)
    (anchorTyped : GeneralPremise.TypedAssignment (GeneralPlanEnvironment.environment plan) schema.context anchor)
    (anchorPresent : ∀ name ∈ schema.matchedNames, ∃ value, lookup anchor name = some value)
    (cases : ∀ assignment, TypedRequest schema A anchor assignment → IntroductionCase schema term assignment B) :
    Evidence schema A B term where
  carrier := typed
  anchor := anchor
  anchorTyped := anchorTyped
  anchorPresent := anchorPresent
  respond assignment request :=
    let introduced := cases assignment request
    { source := introduced.source
      target := introduced.target
      filling := (Mettapedia.OSLF.NativeTypes.Modal.Instantiation.fill_authored introduced.focus).trans introduced.sourceInstance
      rhs := introduced.reduct
      receipt := ⟨introduced.source, [], introduced.primitive⟩
      valid := ⟨.nil _, introduced.valid enabled⟩
      targetConversion := .refl _
      certificate := introduced.certificate }

/-- M-STEP delivers the specified RHS instance, after all retained equation
conversions. There is no existential replacement of that target. -/
theorem m_step {plan : Plan} {schema : Schema plan}
    {A : String → ContextualValue → Prop} {B : Continuation.{u}} {term : Pattern}
    (implementation : Evidence schema A B term) (assignment : Assignment)
    (request : TypedRequest schema A implementation.anchor assignment) :
    ∃ source target, schema.fill? assignment term = some source ∧
      schema.rhs? assignment = some target ∧
      (GeneralOccurrenceSemantics.gslt plan schema.bound schema.programCarrier).Step source target := by
  let outcome := implementation.respond assignment request
  exact ⟨outcome.source, outcome.target, outcome.filling, outcome.rhs,
    outcome.receipt.representative, outcome.receipt.firing, outcome.valid.1.equivalent,
    outcome.valid.2, outcome.targetConversion⟩

/-- M-ELIM returns the dependent certificate at the specified RHS and at the
substituted continuation. It retains the full response beside the readout. -/
def m_elim {plan : Plan} {schema : Schema plan}
    {A : String → ContextualValue → Prop} {B : Continuation.{u}} {term : Pattern}
    (implementation : Evidence schema A B term) (assignment : Assignment)
    (request : TypedRequest schema A implementation.anchor assignment) :
    Σ target : Pattern, substituteContinuation B assignment target :=
  let outcome := implementation.respond assignment request
  ⟨outcome.target, outcome.certificate⟩

theorem m_elim_specified_rhs {plan : Plan} {schema : Schema plan}
    {A : String → ContextualValue → Prop} {B : Continuation.{u}} {term : Pattern}
    (implementation : Evidence schema A B term) (assignment : Assignment)
    (request : TypedRequest schema A implementation.anchor assignment) :
    schema.rhs? assignment = some (m_elim implementation assignment request).1 :=
  (implementation.respond assignment request).rhs

theorem m_step_predicate {plan : Plan} {schema : Schema plan}
    {A : String → ContextualValue → Prop} {B : Continuation.{u}} {term : Pattern}
    (inhabited : Inhabits schema A B term) :
    ∃ anchor, ∀ assignment, TypedRequest schema A anchor assignment →
      ∃ source target, schema.fill? assignment term = some source ∧
        schema.rhs? assignment = some target ∧
        (GeneralOccurrenceSemantics.gslt plan schema.bound schema.programCarrier).Step source target := by
  obtain ⟨evidence⟩ := inhabited
  exact ⟨evidence.anchor, fun assignment request => m_step evidence assignment request⟩

theorem m_elim_predicate {plan : Plan} {schema : Schema plan}
    {A : String → ContextualValue → Prop} {B : Continuation.{u}} {term : Pattern}
    (inhabited : Inhabits schema A B term) :
    ∃ anchor, ∀ assignment, TypedRequest schema A anchor assignment →
      ∃ target, schema.rhs? assignment = some target ∧
        Nonempty (substituteContinuation B assignment target) := by
  obtain ⟨evidence⟩ := inhabited
  refine ⟨evidence.anchor, ?_⟩
  intro assignment request
  let outcome := evidence.respond assignment request
  exact ⟨outcome.target, outcome.rhs, ⟨outcome.certificate⟩⟩

/-- Empty-context possibility keeps a genuine receipt and a postcondition on
its actual reduct. Unlike the specified former, its target is existential. -/
def Possibility (plan : Plan) (bound : List TypeExpr) (carrier : TypeExpr)
    (B : Pattern → Type u) (term : Pattern) : Prop :=
  ∃ receipt : GeneralOccurrenceSemantics.Receipt,
    receipt.Valid plan bound carrier term ∧ Nonempty (B receipt.target)

theorem possibility_step {plan : Plan} {bound : List TypeExpr} {carrier : TypeExpr}
    {B : Pattern → Type u} {term : Pattern} (possible : Possibility plan bound carrier B term) :
    ∃ target, (GeneralOccurrenceSemantics.gslt plan bound carrier).Step term target ∧ Nonempty (B target) := by
  obtain ⟨receipt, valid, certificate⟩ := possible
  exact ⟨receipt.target, GeneralOccurrenceSemantics.Receipt.semantic_step plan bound carrier valid,
    certificate⟩

theorem possibility_intro {plan : Plan} {bound : List TypeExpr} {carrier : TypeExpr}
    {B : Pattern → Type u} {term : Pattern} {receipt : GeneralOccurrenceSemantics.Receipt}
    (valid : receipt.Valid plan bound carrier term) (certificate : B receipt.target) :
    Possibility plan bound carrier B term := ⟨receipt, valid, ⟨certificate⟩⟩

end Mettapedia.OSLF.NativeTypes.Modal.Rules
