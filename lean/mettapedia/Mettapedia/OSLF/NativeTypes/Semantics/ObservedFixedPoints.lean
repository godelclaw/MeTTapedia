import Mettapedia.OSLF.Bridges.TypeTheory.ObservedNativeTypes
import Mettapedia.GSLT.Topos.NativeFixedPointEncodings

/-!
# Fixed-point observations on represented material states

Reachability and predecessor invariance are formed from the existing OSLF
span modalities. Their least and greatest fixed points commute with an
observation that covers the appropriate endpoints. The material instance
uses actual represented observed states and retains the original events.
No finiteness, termination, or completeness of a rooted exploration is
inferred from the existence of this semantic interpretation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.ObservedFixedPoints

open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.GSLT Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.ObservedMaterialization
open Mettapedia.GSLT.ObservationSpans
open Mettapedia.GSLT.Topos.NativeFixedPointEncodings
open Mettapedia.OSLF.Bridges.TypeTheory.ObservedNativeTypes

universe u v e f

variable {X : Type u} {Y : Type v}

/-- The body of `μ P. goal ∨ ◇ P`. -/
def reachOperator (span : ReductionSpan X) (goal : Set X) : Set X →o Set X where
  toFun candidate := {state | goal state ∨ derivedDiamond span candidate state}
  monotone' := by
    intro first second below state holds
    rcases holds with done | ⟨event, starts, later⟩
    · exact Or.inl done
    · exact Or.inr ⟨event, starts, below later⟩

/-- The body of `ν P. safe ∧ □ P`, using OSLF's incoming universal.
This is a property of the past, not universal outgoing safety. -/
def pastOperator (span : ReductionSpan X) (safe : Set X) : Set X →o Set X where
  toFun candidate := {state | safe state ∧ derivedBox span candidate state}
  monotone' := by
    intro first second below state holds
    exact ⟨holds.1, fun event ends => below (holds.2 event ends)⟩

def pull (observe : X → Y) : Set Y →o Set X where
  toFun predicate := observe ⁻¹' predicate
  monotone' := by intro first second below state holds; exact below holds

/-- Reuse the existing native fixed-point transport with both adjoints of
predicate substitution. Operators remain independently supplied. -/
theorem least_preimage (observe : X → Y) (observed : Set Y →o Set Y)
    (source : Set X →o Set X)
    (commutes : ∀ candidate, observe ⁻¹' observed candidate = source (observe ⁻¹' candidate)) :
    observe ⁻¹' observed.lfp = source.lfp := by
  simpa only [leastEncoding_eq_meaning, leastMeaning, pull, OrderHom.coe_mk] using
    least_substitution observed source (pull observe) (ui observe)
      (pb_ui_adj observe) commutes

theorem greatest_preimage (observe : X → Y) (observed : Set Y →o Set Y)
    (source : Set X →o Set X)
    (commutes : ∀ candidate, observe ⁻¹' observed candidate = source (observe ⁻¹' candidate)) :
    observe ⁻¹' observed.gfp = source.gfp := by
  simpa only [greatestEncoding_eq_meaning, greatestMeaning, pull, OrderHom.coe_mk] using
    greatest_substitution observed source (pull observe) (di observe)
      (di_pb_adj observe) commutes

variable {A : ReductionSpan.{u, e} X} {B : ReductionSpan.{v, f} Y}

theorem reach_commutes (observation : SpanMap A B) (coverage : observation.SourceLifts)
    (goal candidate : Set Y) :
    observation.states ⁻¹' reachOperator B goal candidate =
      reachOperator A (observation.states ⁻¹' goal) (observation.states ⁻¹' candidate) := by
  ext state
  exact or_congr Iff.rfl (observation.diamond_pullback coverage candidate state)

theorem past_commutes (observation : SpanMap A B) (coverage : observation.TargetLifts)
    (safe candidate : Set Y) :
    observation.states ⁻¹' pastOperator B safe candidate =
      pastOperator A (observation.states ⁻¹' safe) (observation.states ⁻¹' candidate) := by
  ext state
  exact and_congr Iff.rfl (observation.box_pullback coverage candidate state)

theorem reach_lfp (observation : SpanMap A B) (coverage : observation.SourceLifts)
    (goal : Set Y) :
    observation.states ⁻¹' (reachOperator B goal).lfp =
      (reachOperator A (observation.states ⁻¹' goal)).lfp :=
  least_preimage observation.states _ _ (reach_commutes observation coverage goal)

theorem past_gfp (observation : SpanMap A B) (coverage : observation.TargetLifts)
    (safe : Set Y) :
    observation.states ⁻¹' (pastOperator B safe).gfp =
      (pastOperator A (observation.states ⁻¹' safe)).gfp :=
  greatest_preimage observation.states _ _ (past_commutes observation coverage safe)

section Material

variable {S : GSLT.{u}} {M : System.{u, u} S}
variable (readings : LabelReadings M) (occurrences : ActionOccurrences M)

private theorem action_diamond (complete : ActionsPresentSteps (M := M))
    (predicate : Set S.Term) (source : S.Term) :
    derivedDiamond occurrences.sourceSpan predicate source ↔ gsltDiamond S predicate source := by
  rw [gsltDiamond_spec]
  constructor
  · rintro ⟨event, starts, holds⟩
    exact ⟨_, (actionSpan_step_iff occurrences complete _ _).mp ⟨event, starts, rfl⟩, holds⟩
  · rintro ⟨target, step, holds⟩
    obtain ⟨event, starts, ends⟩ := (actionSpan_step_iff occurrences complete _ _).mpr step
    refine ⟨event, starts, ?_⟩
    change predicate (occurrences.sourceSpan.target event)
    rw [ends]
    exact holds

private theorem action_box (complete : ActionsPresentSteps (M := M))
    (predicate : Set S.Term) (target : S.Term) :
    derivedBox occurrences.sourceSpan predicate target ↔ gsltBox S predicate target := by
  rw [gsltBox_spec]
  constructor
  · intro holds source step
    obtain ⟨event, starts, ends⟩ := (actionSpan_step_iff occurrences complete _ _).mpr step
    exact starts ▸ holds event ends
  · intro holds event ends
    exact holds _ ((actionSpan_step_iff occurrences complete _ _).mp ⟨event, rfl, ends⟩)

/-- Material reachability equals the full authored GSLT reachability when
the retained labelled actions present all source steps. -/
theorem material_reach_lfp (faithful : readings.Faithful)
    (complete : ActionsPresentSteps (M := M)) (goal : Set (MaterialState readings)) :
    ObservedFamilyEnclosure.valueMember readings ⁻¹'
        (reachOperator (ObservedFamilyEnclosure.Events.memberSpan readings occurrences) goal).lfp =
      (reachOperator (gsltSpan S) (ObservedFamilyEnclosure.valueMember readings ⁻¹' goal)).lfp := by
  refine (reach_lfp (ObservedFamilyEnclosure.Events.observation readings occurrences)
    (ObservedFamilyEnclosure.Events.sourceLifts readings faithful occurrences) goal).trans ?_
  apply congrArg (fun operator : Set S.Term →o Set S.Term => operator.lfp)
  apply OrderHom.ext
  funext candidate
  ext source
  exact or_congr Iff.rfl (action_diamond occurrences complete candidate source)

/-- The past fixed point requires incoming coverage independently of future
bisimulation. Faithful future readings alone cannot discharge it. -/
theorem material_past_gfp
    (complete : ActionsPresentSteps (M := M))
    (incoming : (ObservedFamilyEnclosure.Events.observation readings occurrences).TargetLifts)
    (safe : Set (MaterialState readings)) :
    ObservedFamilyEnclosure.valueMember readings ⁻¹'
        (pastOperator (ObservedFamilyEnclosure.Events.memberSpan readings occurrences) safe).gfp =
      (pastOperator (gsltSpan S) (ObservedFamilyEnclosure.valueMember readings ⁻¹' safe)).gfp := by
  refine (past_gfp (ObservedFamilyEnclosure.Events.observation readings occurrences) incoming safe).trans ?_
  apply congrArg (fun operator : Set S.Term →o Set S.Term => operator.gfp)
  apply OrderHom.ext
  funext candidate
  ext target
  exact and_congr Iff.rfl (action_box occurrences complete candidate target)

/-- A native type obtained by pulling back material reachability through
the existing equation-invariant predicate construction. -/
noncomputable def materialReachType (goal : Set (MaterialState readings)) : GSLTNativeType S where
  sort := ()
  pred := pullNative readings
    (reachOperator (ObservedFamilyEnclosure.Events.memberSpan readings occurrences) goal).lfp

noncomputable def materialPastType (safe : Set (MaterialState readings)) : GSLTNativeType S where
  sort := ()
  pred := pullNative readings
    (pastOperator (ObservedFamilyEnclosure.Events.memberSpan readings occurrences) safe).gfp

theorem materialReachType_source (faithful : readings.Faithful)
    (complete : ActionsPresentSteps (M := M)) (goal : Set (MaterialState readings))
    (source : S.Term) :
    (gsltOSLF S).satisfies (S := ()) source (materialReachType readings occurrences goal).pred ↔
      source ∈ (reachOperator (gsltSpan S)
        (ObservedFamilyEnclosure.valueMember readings ⁻¹' goal)).lfp :=
  Set.ext_iff.mp (material_reach_lfp readings occurrences faithful complete goal) source

theorem materialPastType_source (complete : ActionsPresentSteps (M := M))
    (incoming : (ObservedFamilyEnclosure.Events.observation readings occurrences).TargetLifts)
    (safe : Set (MaterialState readings)) (source : S.Term) :
    (gsltOSLF S).satisfies (S := ()) source (materialPastType readings occurrences safe).pred ↔
      source ∈ (pastOperator (gsltSpan S)
        (ObservedFamilyEnclosure.valueMember readings ⁻¹' safe)).gfp :=
  Set.ext_iff.mp (material_past_gfp readings occurrences complete incoming safe) source

end Material

end Mettapedia.OSLF.NativeTypes.Semantics.ObservedFixedPoints
