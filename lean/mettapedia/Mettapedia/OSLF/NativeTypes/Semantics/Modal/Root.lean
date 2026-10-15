import Mettapedia.OSLF.NativeTypes.Semantics.Modal
import Mettapedia.OSLF.NativeTypes.Modal.NativeElimination

open Mettapedia.OSLF.Framework

/-!
# Recovery of full modal implementations at a root equation class

For a root-context schema, focus conversion is conversion of the complete
program. Rebasing therefore constructs an implementation at the requested
representative, preserving the matched anchor and every primitive origin.
This is a data-producing recovery of the complete rely family.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Modal

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open GeneralExecutionAdmission GeneralOccurrenceSemantics
open Mettapedia.OSLF.NativeTypes.Modal.Rules Mettapedia.OSLF.NativeTypes.Modal.Equations Mettapedia.OSLF.NativeTypes.Modal.ContextEquations
open GSLTTypeSynthesis

universe u

/-- A root implementation can be rebased with a concrete equation path.
The response still reaches the specified RHS with the original certificate. -/
def rebaseRoot {plan : Plan} {schema : Schema plan}
    {A : String → RuleBinding.ContextualValue → Prop} {B : Continuation.{u}}
    {source target : Pattern}
    (root : schema.position = [])
    (bound : schema.focusBound = schema.bound)
    (carrier : schema.focusCarrier = schema.programCarrier)
    (administration : List Conversion)
    (path : ConversionPath plan schema.bound schema.programCarrier target source administration)
    (implementation : Evidence schema A B source) : Evidence schema A B target where
  carrier := by
    rw [bound, carrier]
    apply (conversion_carrier_iff path.equivalent).mpr
    simpa only [bound, carrier] using implementation.carrier
  anchor := implementation.anchor
  anchorTyped := implementation.anchorTyped
  anchorPresent := implementation.anchorPresent
  respond assignment request := by
    let outcome := implementation.respond assignment request
    have source_eq : outcome.source = source :=
      Option.some.inj (outcome.filling.symm.trans (root_fill schema root assignment source))
    have path' : ConversionPath plan schema.bound schema.programCarrier target outcome.source administration := by
      rw [source_eq]
      exact path
    exact { source := target
            target := outcome.target
            filling := root_fill schema root assignment target
            rhs := outcome.rhs
            receipt := Mettapedia.OSLF.NativeTypes.Modal.Equations.rebase administration outcome.receipt
            valid := rebase_valid path' outcome.valid
            targetConversion := outcome.targetConversion
            certificate := outcome.certificate }

theorem rebaseRoot_anchor {plan : Plan} {schema : Schema plan}
    {A : String → RuleBinding.ContextualValue → Prop} {B : Continuation.{u}}
    {source target : Pattern}
    (root : schema.position = []) (bound : schema.focusBound = schema.bound)
    (carrier : schema.focusCarrier = schema.programCarrier)
    (administration : List Conversion)
    (path : ConversionPath plan schema.bound schema.programCarrier target source administration)
    (implementation : Evidence schema A B source) :
    (rebaseRoot root bound carrier administration path implementation).anchor = implementation.anchor := rfl

theorem rebaseRoot_response_origins {plan : Plan} {schema : Schema plan}
    {A : String → RuleBinding.ContextualValue → Prop} {B : Continuation.{u}}
    {source target : Pattern}
    (root : schema.position = []) (bound : schema.focusBound = schema.bound)
    (carrier : schema.focusCarrier = schema.programCarrier)
    (administration : List Conversion)
    (path : ConversionPath plan schema.bound schema.programCarrier target source administration)
    (implementation : Evidence schema A B source)
    (assignment : ScopedRuleMatching.Assignment)
    (request : TypedRequest schema A implementation.anchor assignment) :
    ((rebaseRoot root bound carrier administration path implementation).respond assignment request).receipt.firing =
        (implementation.respond assignment request).receipt.firing ∧
      ((rebaseRoot root bound carrier administration path implementation).respond assignment request).target =
        (implementation.respond assignment request).target ∧
      ((rebaseRoot root bound carrier administration path implementation).respond assignment request).receipt.conversions =
        administration ++ (implementation.respond assignment request).receipt.conversions :=
  ⟨rfl, rfl, rfl⟩

namespace Family

/-- Root conversion yields the full raw implementation, not merely one
successful reliance assignment. -/
def rootImplementation {plan : Plan} {schema : Schema plan}
    {A : String → RuleBinding.ContextualValue → Prop} {B : Continuation.{u}} {term : Pattern}
    (root : schema.position = []) (bound : schema.focusBound = schema.bound)
    (carrier : schema.focusCarrier = schema.programCarrier)
    (family : Family schema A B term) : Evidence schema A B term :=
  rebaseRoot root bound carrier family.conversions
    (by simpa only [bound, carrier] using family.converted) family.implementation

theorem rootImplementation_anchor {plan : Plan} {schema : Schema plan}
    {A : String → RuleBinding.ContextualValue → Prop} {B : Continuation.{u}} {term : Pattern}
    (root : schema.position = []) (bound : schema.focusBound = schema.bound)
    (carrier : schema.focusCarrier = schema.programCarrier)
    (family : Family schema A B term) :
    (family.rootImplementation root bound carrier).anchor = family.implementation.anchor := rfl

theorem rootImplementation_origins {plan : Plan} {schema : Schema plan}
    {A : String → RuleBinding.ContextualValue → Prop} {B : Continuation.{u}} {term : Pattern}
    (root : schema.position = []) (bound : schema.focusBound = schema.bound)
    (carrier : schema.focusCarrier = schema.programCarrier)
    (family : Family schema A B term) (assignment : ScopedRuleMatching.Assignment)
    (request : TypedRequest schema A family.implementation.anchor assignment) :
    ((family.rootImplementation root bound carrier).respond assignment request).receipt.firing =
        (family.response assignment request).receipt.firing ∧
      ((family.rootImplementation root bound carrier).respond assignment request).source = term ∧
      ((family.rootImplementation root bound carrier).respond assignment request).target =
        (family.response assignment request).target ∧
      ((family.rootImplementation root bound carrier).respond assignment request).receipt.conversions =
        family.conversions ++ (family.response assignment request).receipt.conversions :=
  ⟨rfl, rfl, rfl, rfl⟩

end Family

/-- At a root slot the canonical equation predicate is exactly the original
specified-RHS dependent former, at every equation representative. -/
theorem root_predicate_iff_inhabits {plan : Plan} {schema : Schema plan}
    {A : String → RuleBinding.ContextualValue → Prop} {B : Continuation.{u}} {term : Pattern}
    (root : schema.position = []) (bound : schema.focusBound = schema.bound)
    (carrier : schema.focusCarrier = schema.programCarrier) :
    predicate schema A B term ↔ Inhabits schema A B term := by
  rw [← family_support_iff]
  constructor
  · rintro ⟨family⟩
    exact ⟨family.rootImplementation root bound carrier⟩
  · rintro ⟨implementation⟩
    exact ⟨introduce implementation⟩

theorem root_native_satisfaction_iff_inhabits {plan : Plan} {schema : Schema plan}
    {A : String → RuleBinding.ContextualValue → Prop} {B : Continuation.{u}} (term : Pattern)
    (root : schema.position = []) (bound : schema.focusBound = schema.bound)
    (carrier : schema.focusCarrier = schema.programCarrier) :
    (gsltOSLF (focusTheory schema)).satisfies (S := ()) term (nativeType schema A B).pred ↔
      Inhabits schema A B term :=
  root_predicate_iff_inhabits root bound carrier

/-- Native elimination preserves the physical occurrence and its exact
specified continuation target after root equation administration. -/
theorem root_native_elimination_origins {plan : Plan} {schema : Schema plan}
    {A : String → RuleBinding.ContextualValue → Prop} {B : Continuation} {term : Pattern}
    (root : schema.position = []) (bound : schema.focusBound = schema.bound)
    (carrier : schema.focusCarrier = schema.programCarrier)
    (family : Family schema A B term) (assignment : ScopedRuleMatching.Assignment)
    (request : TypedRequest schema A family.implementation.anchor assignment) :
    let outcome := (family.rootImplementation root bound carrier).respond assignment request
    outcome.native.1.val.firing = (family.response assignment request).receipt.firing ∧
      outcome.native.2.1 = (family.response assignment request).target ∧
      outcome.native.1.val.conversions = family.conversions ++
        (family.response assignment request).receipt.conversions :=
  ⟨rfl, rfl, rfl⟩

end Mettapedia.OSLF.NativeTypes.Semantics.Modal
