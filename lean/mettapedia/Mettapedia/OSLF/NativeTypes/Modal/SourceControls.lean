import Mettapedia.OSLF.NativeTypes.Modal.SourceProfile
import Mettapedia.OSLF.NativeTypes.Modal.Counterexamples

open Mettapedia.OSLF.Framework

/-!
# Typing and executable source admission are distinct

Binder display metadata does not change the sort judgment. The canonical
executable profile nevertheless checks that metadata before firing. A named
identity function therefore gives a genuine separation between RHS typing
alone and an executable base-rule modal introduction. Erasing its display
metadata yields a properly scoped function covered by the whole-family
source-introduction theorem.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.SourceControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.OSLF.MeTTaIL.GeneralTypedSites
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Modal.Rules
open Mettapedia.OSLF.NativeTypes.Modal.SourceIntroduction
open Mettapedia.OSLF.NativeTypes.Modal.SourceProfile (carrier functionCarrier done box declaration language snapshot)

def namedIdentity : Pattern := .lambda (some "display") (.bvar 0)
def canonicalIdentity : Pattern := .lambda none (.bvar 0)

theorem display_erasure : namedIdentity.eraseBinderMetadata = canonicalIdentity := by
  simp only [namedIdentity, canonicalIdentity, Pattern.eraseBinderMetadata]

theorem named_identity_typed : HasType language snapshot.free [] namedIdentity functionCarrier :=
  .lambda (.bvar rfl)

theorem canonical_identity_proper :
    OpenPatternWellSorted language snapshot.free [] functionCarrier canonicalIdentity := by
  apply checkOpenPatternWellSorted_sound
  cbv

theorem canonical_identity_executes :
    Mettapedia.OSLF.NativeTypes.Modal.SourceProfile.result [] canonicalIdentity ∈
      baseIntroductions (Mettapedia.OSLF.NativeTypes.Modal.SourceProfile.schema [])
        (Mettapedia.OSLF.NativeTypes.Modal.SourceProfile.assignment [] canonicalIdentity) [] :=
  Mettapedia.OSLF.NativeTypes.Modal.SourceProfile.all_proper_bodies_execute canonical_identity_proper
    (Mettapedia.OSLF.NativeTypes.Modal.SourceProfile.assignment_lookup [] canonicalIdentity)

def permissions : Permissions := {sites := .rootOnly}
def runtimePlan : Plan := {Mettapedia.OSLF.NativeTypes.Modal.SourceProfile.runtimePlan with permissions := permissions}

theorem actual_plan : compile snapshot permissions = runtimePlan := by cbv

def schema : Schema runtimePlan where
  ordinal := 0
  declaration := declaration
  declared := List.mem_cons_self
  position := (Mettapedia.OSLF.NativeTypes.Modal.SourceProfile.schema []).position
  bound := []
  programCarrier := carrier
  focusBound := []
  focusCarrier := functionCarrier

theorem schema_position : schema.position = [0] :=
  Mettapedia.OSLF.NativeTypes.Modal.SourceProfile.schema_position []

theorem schema_fill (supplied : Assignment) (body : Pattern) :
    schema.fill? supplied body = some (box body) := by
  unfold Schema.fill?
  rw [schema_position]
  have left : schema.declaration.rule.left = box (.fvar "F") := rfl
  rw [left]
  simp only [box, Mettapedia.OSLF.NativeTypes.Modal.Instantiation.fill?, Mettapedia.OSLF.NativeTypes.Modal.Instantiation.fillArgs?,
    instantiateArgsWith?, ↓reduceIte, Option.bind_eq_bind, Option.bind_some]

theorem schema_rhs (supplied : Assignment) : schema.rhs? supplied = some done :=
  Mettapedia.OSLF.NativeTypes.Modal.SourceProfile.rhs_instance [] supplied

theorem named_source_instance :
    instantiateWith? schema.operation schema.declaration.rule schema.declaration.binding.spec
      schema.bound.length .left [] 0 (Mettapedia.OSLF.NativeTypes.Modal.SourceProfile.assignment [] namedIdentity)
      schema.declaration.rule.left = some (box namedIdentity) :=
  Mettapedia.OSLF.NativeTypes.Modal.SourceProfile.source_instance (by cbv)
    (Mettapedia.OSLF.NativeTypes.Modal.SourceProfile.assignment_lookup [] namedIdentity)

theorem named_source_typed : HasType language snapshot.free [] (box namedIdentity) carrier :=
  Mettapedia.OSLF.NativeTypes.Modal.SourceProfile.typed_box named_identity_typed

theorem named_capture_typed :
    GeneralPremise.TypedAssignment (GeneralPlanEnvironment.environment runtimePlan) schema.context
      (Mettapedia.OSLF.NativeTypes.Modal.SourceProfile.assignment [] namedIdentity) :=
  Mettapedia.OSLF.NativeTypes.Modal.SourceProfile.assignment_typed named_identity_typed (by cbv)

theorem named_introduction_refused :
    baseIntroductions schema (Mettapedia.OSLF.NativeTypes.Modal.SourceProfile.assignment [] namedIdentity) [] = [] := by
  unfold baseIntroductions
  rw [named_source_instance, schema_rhs]
  cbv

private theorem no_equation {source target : Pattern} :
    ¬ GeneralOccurrenceSemantics.Equation runtimePlan [] carrier source target := by
  rintro ⟨receipt, complete, _⟩
  have declared := List.fst_mem_of_mem_zipIdx complete.job.1
  exact List.not_mem_nil declared

private theorem conversion_identity {source target : Pattern}
    (equivalent : Relation.EqvGen (GeneralOccurrenceSemantics.Equation runtimePlan [] carrier)
      source target) : source = target := by
  induction equivalent with
  | rel _ _ equated => exact False.elim (no_equation equated)
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

theorem named_source_has_no_step (target : Pattern) :
    ¬ (GeneralOccurrenceSemantics.gslt runtimePlan [] carrier).Step (box namedIdentity) target := by
  rintro ⟨representative, receipt, before, valid, _⟩
  have same : representative = box namedIdentity := (conversion_identity before).symm
  subst representative
  have root := Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.root_only_site valid.1.2
  have sourceTyped := (GeneralRuleJobs.receipt_root_readout valid).2.1
  rw [root] at sourceTyped
  have canonical := sourceTyped.2.1
  change (box namedIdentity).hasCanonicalBinderMetadata = true at canonical
  simp only [box, namedIdentity, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, Option.isNone_some, Bool.and_true] at canonical
  cases canonical

private theorem reflexive_request (implementation : Evidence schema (fun _ _ => False)
    Mettapedia.OSLF.NativeTypes.Modal.SourceProfile.continuation namedIdentity) :
    TypedRequest schema (fun _ _ => False) implementation.anchor implementation.anchor := by
  refine ⟨?_, implementation.anchorTyped, fun _ _ => rfl, ?_⟩
  · have relies : schema.relyNames = [] := by cbv
    intro name present
    rw [relies] at present
    exact False.elim (List.not_mem_nil present)
  · have names : RedexPosition.fvarNames schema.declaration.rule.left ++
        RedexPosition.fvarNames schema.declaration.rule.right = schema.matchedNames := by cbv
    intro name present
    rw [names] at present
    exact implementation.anchorPresent name present

theorem named_focus_has_no_modal_introduction :
    ¬ Inhabits schema (fun _ _ => False) Mettapedia.OSLF.NativeTypes.Modal.SourceProfile.continuation namedIdentity := by
  rintro ⟨implementation⟩
  obtain ⟨source, target, filling, _, step⟩ := m_step implementation implementation.anchor
    (reflexive_request implementation)
  have same : source = box namedIdentity :=
    Option.some.inj (filling.symm.trans (schema_fill implementation.anchor namedIdentity))
  rw [same] at step
  exact named_source_has_no_step target step

/-- Full sort typing of the focus, its original source substitution and the
specified RHS certificate does not imply canonical executable admission. -/
theorem source_typing_alone_insufficient :
    HasType language snapshot.free [] namedIdentity functionCarrier ∧
      HasType language snapshot.free [] (box namedIdentity) carrier ∧
      schema.rhs? (Mettapedia.OSLF.NativeTypes.Modal.SourceProfile.assignment [] namedIdentity) = some done ∧
      Nonempty (Mettapedia.OSLF.NativeTypes.Modal.SourceProfile.continuation
        (Mettapedia.OSLF.NativeTypes.Modal.SourceProfile.assignment [] namedIdentity) done) ∧
      ¬ Inhabits schema (fun _ _ => False) Mettapedia.OSLF.NativeTypes.Modal.SourceProfile.continuation namedIdentity :=
  ⟨named_identity_typed, named_source_typed, schema_rhs _, ⟨⟨rfl⟩⟩, named_focus_has_no_modal_introduction⟩

end Mettapedia.OSLF.NativeTypes.Modal.SourceControls
