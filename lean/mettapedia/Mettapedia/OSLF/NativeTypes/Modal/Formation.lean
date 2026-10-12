import Mettapedia.OSLF.NativeTypes.Modal.Rules

open Mettapedia.OSLF.Framework

/-!
# Formation from genuinely typed rely and continuation codes

Rely codes are indexed by the names derived from the selected authored
context. Their carriers and dependency contexts are checked against that
declaration. Continuation codes are a family over complete scoped assignments.
The output former is a subobject at the actual focus carrier.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.Formation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Modal.Rules
open ModalHypercube (HSort)

/-- An input type code is bounded by the declared carrier in the complete
dependency and ambient typing contexts. Its universe is a separate input. -/
structure RelyCode {plan : Plan} (schema : Schema plan) (name : String) (sort : HSort) where
  carrier : TypeExpr
  dependencies : List TypeExpr
  declaredCarrier : schema.declaration.rule.typeContext.lookup name = some carrier
  declaredDependencies : dependencies? schema.declaration.binding.spec name = some dependencies
  meaning : ContextualValue → Prop
  bounded : ∀ value, meaning value →
    value.dependencies = dependencies ∧ value.ambient = schema.bound.length ∧
    HasType plan.snapshot.language plan.snapshot.free (dependencies ++ schema.bound) value.body carrier

abbrev RelyIndex {plan : Plan} (schema : Schema plan) := {name : String // name ∈ schema.relyNames}

/-- There is one supplied code at each algorithmically derived rely slot. -/
abbrev RelyCodes {plan : Plan} (schema : Schema plan) (sorts : RelyIndex schema → HSort) :=
  (name : RelyIndex schema) → RelyCode schema name.val (sorts name)

def relyMeaning {plan : Plan} {schema : Schema plan} {sorts : RelyIndex schema → HSort}
    (codes : RelyCodes schema sorts) (name : String) (value : ContextualValue) : Prop :=
  ∃ present : name ∈ schema.relyNames, (codes ⟨name, present⟩).meaning value

def continuationMeaning {plan : Plan} {schema : Schema plan} {sort : HSort}
    (codes : Assignment → TypeCode plan schema.bound schema.programCarrier sort) : Continuation :=
  fun assignment target => PLift ((codes assignment).meaning target)

/-- The single semantic modal constructor consumes the generated input slots
and the dependent output code; no separate meaning is attached to its rules. -/
def generatedFormer {plan : Plan} (schema : Schema plan)
    (sorts : RelyIndex schema → HSort) (outputSort focusSort : HSort)
    (codes : RelyCodes schema sorts)
    (continuations : Assignment → TypeCode plan schema.bound schema.programCarrier outputSort) :
    TypeCode plan schema.focusBound schema.focusCarrier focusSort :=
  former schema focusSort (relyMeaning codes) (continuationMeaning continuations)

/-- M-FORM: the output code is formed in the focus carrier whenever its
inputs are codes in their actual declared dependency contexts. -/
theorem m_form_from_codes {plan : Plan} {schema : Schema plan}
    {sorts : RelyIndex schema → HSort} {outputSort focusSort : HSort}
    (codes : RelyCodes schema sorts)
    (continuations : Assignment → TypeCode plan schema.bound schema.programCarrier outputSort)
    {term : Pattern}
    (inhabited : (generatedFormer schema sorts outputSort focusSort codes continuations).meaning term) :
    HasType plan.snapshot.language plan.snapshot.free schema.focusBound term schema.focusCarrier :=
  (generatedFormer schema sorts outputSort focusSort codes continuations).bounded term inhabited

/-- A rely request really reads a value with its declared carrier; missing
values and a mismatched dependency context cannot enter through formation. -/
theorem rely_request_typed {plan : Plan} {schema : Schema plan}
    {sorts : RelyIndex schema → HSort} (codes : RelyCodes schema sorts)
    {assignment : Assignment} (request : RelySatisfied schema (relyMeaning codes) assignment)
    (name : RelyIndex schema) :
    ∃ value, lookup assignment name.val = some value ∧
      value.dependencies = (codes name).dependencies ∧ value.ambient = schema.bound.length ∧
      HasType plan.snapshot.language plan.snapshot.free
        ((codes name).dependencies ++ schema.bound) value.body (codes name).carrier := by
  obtain ⟨value, found, present, meaningful⟩ := request name.val name.property
  have agrees : (⟨name.val, present⟩ : RelyIndex schema) = name := Subtype.ext rfl
  rw [agrees] at meaningful
  exact ⟨value, found, (codes name).bounded value meaningful⟩

/-- M-ELIM's substituted continuation carries the requested program carrier,
not merely an untyped proposition about an arbitrary endpoint. -/
theorem continuation_readout_typed {plan : Plan} {schema : Schema plan}
    {sorts : RelyIndex schema → HSort} {outputSort : HSort}
    (codes : RelyCodes schema sorts)
    (continuations : Assignment → TypeCode plan schema.bound schema.programCarrier outputSort)
    {term : Pattern}
    (implementation : Evidence schema (relyMeaning codes) (continuationMeaning continuations) term)
    (assignment : Assignment)
    (request : TypedRequest schema (relyMeaning codes) implementation.anchor assignment) :
    HasType plan.snapshot.language plan.snapshot.free schema.bound
      (m_elim implementation assignment request).1 schema.programCarrier :=
  (continuations assignment).bounded _ (m_elim implementation assignment request).2.down

end Mettapedia.OSLF.NativeTypes.Modal.Formation
