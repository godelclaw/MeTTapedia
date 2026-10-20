import Mettapedia.OSLF.NativeTypes.Instances.Normalized.Meaning
import Mettapedia.OSLF.MeTTaIL.Complete.Classes

/-!
# Native observations from retained class-search receipts

A class search runs at the certified normal source. Positive answers use an
actual published firing. Negative answers additionally require certified
settlement of every search lane. The local normalization certificate connects
this operational search to the full chosen model equality; eventual graph
exploration is not a finite-closure premise.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Normalized

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.Framework GSLTTypeSynthesis
open Mettapedia.OSLF.NativeTypes.Generation (Generated)
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core

theorem EqualityPolicy.authored_equation (policy : EqualityPolicy) (generated : Generated)
    (bound : List TypeExpr) (expected : TypeExpr) {first second : Pattern}
    (equation : GeneralOccurrenceSemantics.Equation generated.plan bound expected first second) :
    policy.equation generated bound expected first second := by
  cases policy with
  | authored => exact equation
  | presented => exact .inl equation
  | model _ => exact .inl equation

variable {generated : Generated} {bound : List TypeExpr} {expected : TypeExpr}

theorem Profile.authored_equiv (profile : Profile generated bound expected) {first second : Pattern}
    (related : Relation.EqvGen (GeneralOccurrenceSemantics.Equation generated.plan bound expected) first second) :
    profile.system.Equiv first second :=
  Relation.EqvGen.mono (fun _ _ edge => profile.policy.authored_equation generated bound expected edge) _ _ related

def Profile.classRun (profile : Profile generated bound expected) (source : Pattern) (work : Nat) :
    Complete.Classes.State generated.plan :=
  Complete.Classes.runAt generated.plan bound expected (profile.nf source) work

def Profile.classHit (profile : Profile generated bound expected) (leaf : profile.Leaf)
    (source : Pattern) (work : Nat) : Bool :=
  (profile.classRun source work).log.any fun receipt =>
    profile.observations[leaf].observe (profile.nf receipt.target)

theorem Profile.class_receipt_step (profile : Profile generated bound expected) (source : Pattern)
    (work : Nat) (receipt : GeneralOccurrenceSemantics.Receipt)
    (listed : receipt ∈ (profile.classRun source work).log) :
    profile.system.Step source (profile.nf receipt.target) := by
  have valid := Complete.Classes.sound generated.plan bound expected (profile.nf source) work receipt listed
  exact ⟨receipt.representative, receipt.target,
    .trans _ _ _ (profile.certificate.normalizer.sound source) (profile.authored_equiv valid.1.equivalent),
    ⟨receipt.firing, valid.2, rfl⟩, profile.certificate.normalizer.sound receipt.target⟩

theorem Profile.class_hit_sound (profile : Profile generated bound expected) (leaf : profile.Leaf)
    (source : Pattern) (work : Nat) (hit : profile.classHit leaf source work = true) :
    denotation profile.tests (.possibility (.atom leaf)) (.empty _) source := by
  obtain ⟨receipt, listed, observed⟩ := List.any_eq_true.mp hit
  apply (gsltDiamond_spec profile.system (profile.tests leaf).predicate source).mpr
  refine ⟨profile.nf receipt.target, profile.class_receipt_step source work receipt listed, ?_⟩
  change profile.observations[leaf].observe (profile.nf (profile.nf receipt.target)) = true
  exact Eq.mpr (congrArg (fun term => profile.observations[leaf].observe term = true)
    (profile.certificate.normalizer.idempotent receipt.target)) observed

theorem Profile.class_hit_complete (profile : Profile generated bound expected) (leaf : profile.Leaf)
    (source : Pattern) (work : Nat)
    (closed : Complete.Classes.complete generated.plan (profile.classRun source work) = true)
    (holds : denotation profile.tests (.possibility (.atom leaf)) (.empty _) source) :
    profile.classHit leaf source work = true := by
  obtain ⟨actual, stepped, observed⟩ :=
    (gsltDiamond_spec profile.system (profile.tests leaf).predicate source).mp holds
  obtain ⟨next, fired, equivalent⟩ := profile.certificate.step_at_normal stepped
  obtain ⟨primitive, valid, endpoint⟩ := fired
  have rawStep : (GeneralOccurrenceSemantics.gslt generated.plan bound expected).Step (profile.nf source) next :=
    ⟨profile.nf source, primitive, .refl _, valid, endpoint ▸ Relation.EqvGen.refl primitive.target⟩
  obtain ⟨receipt, listed, related⟩ := Complete.Classes.exact_of_complete generated.plan bound expected
    (profile.nf source) work (Complete.Predecessors.equationsChecked_of_complete profile.foundation) closed rawStep
  have same := profile.certificate.normalizer.eqvGen_eq (profile.authored_equiv related)
  have actualSame := profile.certificate.normalizer.eqvGen_eq equivalent
  apply List.any_eq_true.mpr
  refine ⟨receipt, listed, ?_⟩
  change profile.observations[leaf].observe (profile.nf actual) = true at observed
  rw [same, ← actualSame]
  exact observed

theorem Profile.class_hit_exact (profile : Profile generated bound expected) (leaf : profile.Leaf)
    (source : Pattern) (work : Nat)
    (closed : Complete.Classes.complete generated.plan (profile.classRun source work) = true) :
    profile.classHit leaf source work = true ↔
      denotation profile.tests (.possibility (.atom leaf)) (.empty _) source :=
  ⟨profile.class_hit_sound leaf source work, profile.class_hit_complete leaf source work closed⟩

def Profile.classCheck (profile : Profile generated bound expected) (leaf : profile.Leaf)
    (source : Pattern) (work : Nat) : Outcome (denotation profile.tests (.possibility (.atom leaf)) (.empty _) source) :=
  if hit : profile.classHit leaf source work = true then
    .proved (profile.class_hit_sound leaf source work hit)
  else if closed : Complete.Classes.complete generated.plan (profile.classRun source work) = true then
    .refuted (fun holds => hit (profile.class_hit_complete leaf source work closed holds))
  else .unknown

theorem Profile.classCheck_proved_source (profile : Profile generated bound expected) (leaf : profile.Leaf)
    (source : Pattern) (work : Nat) (typed : Source generated bound expected source)
    (positive : (profile.classCheck leaf source work).answer = some true) :
    (gsltOSLF (profile.policy.sourceSystem generated bound expected)).satisfies source
      (profile.sourceNativeType (.possibility (.atom leaf))).pred :=
  (profile.meaning_iff_source _ source).mp ⟨source, typed, rfl,
    Outcome.positive _ positive⟩ |>.2

theorem Profile.classCheck_refuted_source (profile : Profile generated bound expected) (leaf : profile.Leaf)
    (source : Pattern) (work : Nat)
    (negative : (profile.classCheck leaf source work).answer = some false) :
    ¬ (gsltOSLF (profile.policy.sourceSystem generated bound expected)).satisfies source
      (profile.sourceNativeType (.possibility (.atom leaf))).pred := by
  intro holds
  exact Outcome.negative _ negative ((profile.denotation_iff_source _ source).mpr holds)

end Mettapedia.OSLF.NativeTypes.Instances.Normalized
