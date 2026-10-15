import Mettapedia.OSLF.NativeTypes.Modal.ContextEquations
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

open Mettapedia.OSLF.Framework

/-!
# Equation-class outputs of dependent generated modalities

The native predicate denotes classes supporting a complete rely-family
implementation. Its dependent family retains the chosen focus representative,
an actual equation-conversion path and the full implementation. At a general
selected focus this does not assert that its surrounding raw context transports
equations. Root-context recovery is proved separately.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Modal

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open GeneralExecutionAdmission GeneralOccurrenceSemantics
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Modal.Rules
open Mettapedia.OSLF.NativeTypes.Modal.Equations
open GSLTTypeSynthesis

universe u

def focusTheory {plan : Plan} (schema : Schema plan) : Mettapedia.GSLT.GSLT :=
  gslt plan schema.focusBound schema.focusCarrier

/-- The canonical native output is the equation-class support of the entire
dependent implementation, rather than of a single successful assignment. -/
def predicate {plan : Plan} (schema : Schema plan)
    (A : String → RuleBinding.ContextualValue → Prop) (B : Continuation.{u}) :
    EquationPredicate (focusTheory schema) :=
  saturatePredicate (focusTheory schema) (Inhabits schema A B)

/-- Retained output data behind native predicate membership. -/
structure Family {plan : Plan} (schema : Schema plan)
    (A : String → RuleBinding.ContextualValue → Prop) (B : Continuation.{u}) (term : Pattern) where
  representative : Pattern
  conversions : List Conversion
  converted : ConversionPath plan schema.focusBound schema.focusCarrier term representative conversions
  implementation : Evidence schema A B representative

/-- Introduction requires a full implementation of every typed rely request. -/
def introduce {plan : Plan} {schema : Schema plan}
    {A : String → RuleBinding.ContextualValue → Prop} {B : Continuation.{u}} {term : Pattern}
    (implementation : Evidence schema A B term) : Family schema A B term :=
  ⟨term, [], .nil term, implementation⟩

/-- The retained family and the canonical predicate have exactly the same
support. The reverse implication constructs a checked conversion path. -/
theorem family_support_iff {plan : Plan} {schema : Schema plan}
    {A : String → RuleBinding.ContextualValue → Prop} {B : Continuation.{u}} {term : Pattern} :
    Nonempty (Family schema A B term) ↔ predicate schema A B term := by
  constructor
  · rintro ⟨family⟩
    exact ⟨family.representative, family.converted.equivalent, ⟨family.implementation⟩⟩
  · rintro ⟨representative, equivalent, ⟨implementation⟩⟩
    obtain ⟨conversions, converted⟩ :=
      (conversion_iff_path plan schema.focusBound schema.focusCarrier term representative).mp equivalent
    exact ⟨⟨representative, conversions, converted, implementation⟩⟩

theorem predicate_equation_invariant {plan : Plan} {schema : Schema plan}
    {A : String → RuleBinding.ContextualValue → Prop} {B : Continuation.{u}}
    {left right : Pattern} (equivalent : (focusTheory schema).Equiv left right) :
    predicate schema A B left ↔ predicate schema A B right :=
  (predicate schema A B).property equivalent

theorem family_equation_iff {plan : Plan} {schema : Schema plan}
    {A : String → RuleBinding.ContextualValue → Prop} {B : Continuation.{u}}
    {left right : Pattern} (equivalent : (focusTheory schema).Equiv left right) :
    Nonempty (Family schema A B left) ↔ Nonempty (Family schema A B right) := by
  rw [family_support_iff, family_support_iff]
  exact predicate_equation_invariant equivalent

def nativeType {plan : Plan} (schema : Schema plan)
    (A : String → RuleBinding.ContextualValue → Prop) (B : Continuation.{u}) :
    GSLTNativeType (focusTheory schema) :=
  ⟨(), predicate schema A B⟩

theorem native_satisfaction_iff_family {plan : Plan} {schema : Schema plan}
    {A : String → RuleBinding.ContextualValue → Prop} {B : Continuation.{u}} (term : Pattern) :
    (gsltOSLF (focusTheory schema)).satisfies (S := ()) term (nativeType schema A B).pred ↔
      Nonempty (Family schema A B term) :=
  family_support_iff.symm

def code {plan : Plan} (schema : Schema plan) (sort : ModalHypercube.HSort)
    (A : String → RuleBinding.ContextualValue → Prop) (B : Continuation.{u}) :
    TypeCode plan schema.focusBound schema.focusCarrier sort where
  meaning := predicate schema A B
  bounded term member := by
    obtain ⟨representative, equivalent, ⟨implementation⟩⟩ := member
    exact (Mettapedia.OSLF.NativeTypes.Modal.ContextEquations.conversion_carrier_iff equivalent).mpr implementation.carrier

def onClasses {plan : Plan} (schema : Schema plan)
    (A : String → RuleBinding.ContextualValue → Prop) (B : Continuation.{u}) :
    Quotient (focusTheory schema).equations → Prop :=
  descendPredicate (focusTheory schema) (predicate schema A B)

theorem quotient_satisfaction_iff_family {plan : Plan} {schema : Schema plan}
    {A : String → RuleBinding.ContextualValue → Prop} {B : Continuation.{u}} (term : Pattern) :
    onClasses schema A B (Quotient.mk (focusTheory schema).equations term) ↔
      Nonempty (Family schema A B term) :=
  family_support_iff.symm

namespace Family

def rebase {plan : Plan} {schema : Schema plan}
    {A : String → RuleBinding.ContextualValue → Prop} {B : Continuation.{u}} {source target : Pattern}
    (administration : List Conversion)
    (path : ConversionPath plan schema.focusBound schema.focusCarrier target source administration)
    (family : Family schema A B source) : Family schema A B target :=
  ⟨family.representative, administration ++ family.conversions,
    ConversionPath.append plan schema.focusBound schema.focusCarrier path family.converted, family.implementation⟩

def response {plan : Plan} {schema : Schema plan}
    {A : String → RuleBinding.ContextualValue → Prop} {B : Continuation.{u}} {term : Pattern}
    (family : Family schema A B term) (assignment : ScopedRuleMatching.Assignment)
    (request : TypedRequest schema A family.implementation.anchor assignment) :
    Outcome schema family.representative assignment B :=
  family.implementation.respond assignment request

theorem response_readout {plan : Plan} {schema : Schema plan}
    {A : String → RuleBinding.ContextualValue → Prop} {B : Continuation.{u}} {term : Pattern}
    (family : Family schema A B term) (assignment : ScopedRuleMatching.Assignment)
    (request : TypedRequest schema A family.implementation.anchor assignment) :
    schema.fill? assignment family.representative = some (family.response assignment request).source ∧
      schema.rhs? assignment = some (family.response assignment request).target ∧
      (gslt plan schema.bound schema.programCarrier).Step
        (family.response assignment request).source (family.response assignment request).target ∧
      Nonempty (substituteContinuation B assignment (family.response assignment request).target) := by
  let outcome := family.response assignment request
  refine ⟨outcome.filling, outcome.rhs, ?_, ⟨outcome.certificate⟩⟩
  exact ⟨outcome.receipt.representative, outcome.receipt.firing,
    outcome.valid.1.equivalent, outcome.valid.2, outcome.targetConversion⟩

/-- Rebasing changes only the retained focus-equation administration.
The full anchor and every actual response receipt remain identical. -/
theorem rebase_preserves_family {plan : Plan} {schema : Schema plan}
    {A : String → RuleBinding.ContextualValue → Prop} {B : Continuation.{u}} {source target : Pattern}
    (administration : List Conversion)
    (path : ConversionPath plan schema.focusBound schema.focusCarrier target source administration)
    (family : Family schema A B source) :
    (family.rebase administration path).representative = family.representative ∧
      (family.rebase administration path).implementation = family.implementation ∧
      (family.rebase administration path).conversions.length = administration.length + family.conversions.length := by
  exact ⟨rfl, rfl, List.length_append⟩

end Family

end Mettapedia.OSLF.NativeTypes.Semantics.Modal
