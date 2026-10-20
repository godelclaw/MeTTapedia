import Mettapedia.OSLF.NativeTypes.Semantics.ObservedFixedPoints
import Mettapedia.Logic.ModalQuantaleSemantics
import Mettapedia.GSLT.LanguageDef.CertificateGSLTMuCalculusBoundary

/-!
# Existing modal fixed-point formulas over operational spans

The modal μ-calculus syntax is reused unchanged. Traversing forward interprets
its diamond as OSLF possibility; traversing backward interprets its universal
box as OSLF's right adjoint. The forward universal box remains a different
observation. Complete endpoint lifting transports all positive fixed-point
formulas, including nested least/greatest fixed points.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula

open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.GSLT.ObservationSpans
open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.Logic.ModalQuantaleSemantics.Boolean
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.MuCalculusBoundary

universe u v e f
variable {X : Type u} {Y : Type v}

inductive Traversal where
  | future
  | past
  deriving DecidableEq, Repr

def transitionSystem (span : ReductionSpan.{u, e} X) : LTS X Traversal where
  trans source direction target := match direction with
    | .future => ∃ event, span.source event = source ∧ span.target event = target
    | .past => ∃ event, span.target event = source ∧ span.source event = target

theorem future_diamond (span : ReductionSpan.{u, e} X) (predicate : Set X) (source : X) :
    satisfies (transitionSystem span) (fun _ : Fin 1 => predicate)
      (.diamond .future (.var 0)) source ↔ derivedDiamond span predicate source := by
  constructor
  · rintro ⟨target, ⟨event, starts, ends⟩, member⟩
    exact ⟨event, starts, by change predicate (span.target event); rw [ends]; exact member⟩
  · rintro ⟨event, starts, member⟩
    exact ⟨span.target event, ⟨event, starts, rfl⟩, member⟩

theorem past_box (span : ReductionSpan.{u, e} X) (predicate : Set X) (target : X) :
    satisfies (transitionSystem span) (fun _ : Fin 1 => predicate)
      (.box .past (.var 0)) target ↔ derivedBox span predicate target := by
  constructor
  · intro holds event ends
    exact holds (span.source event) ⟨event, ends, rfl⟩
  · rintro holds source ⟨event, ends, starts⟩
    exact starts ▸ holds event ends

def pullEnvironment {n : Nat} (observe : X → Y) (environment : Env Y n) : Env X n :=
  fun index => observe ⁻¹' environment index

theorem pullEnvironment_extend {n : Nat} (observe : X → Y) (environment : Env Y n)
    (candidate : Set Y) :
    pullEnvironment observe (environment.extend candidate) =
      (pullEnvironment observe environment).extend (observe ⁻¹' candidate) := by
  funext index
  simp only [pullEnvironment, Env.extend]
  split <;> rfl

variable {A : ReductionSpan.{u, e} X} {B : ReductionSpan.{v, f} Y}

theorem transition_preserved (observation : SpanMap A B) {source target : X}
    (direction : Traversal) (step : (transitionSystem A).trans source direction target) :
    (transitionSystem B).trans (observation.states source) direction (observation.states target) := by
  cases direction <;> obtain ⟨event, first, second⟩ := step
  · exact ⟨observation.events event, (observation.source_comm event).trans
      (congrArg observation.states first), (observation.target_comm event).trans
      (congrArg observation.states second)⟩
  · exact ⟨observation.events event, (observation.target_comm event).trans
      (congrArg observation.states first), (observation.source_comm event).trans
      (congrArg observation.states second)⟩

def CoversDirection (observation : SpanMap A B) : Traversal → Prop
  | .future => observation.SourceLifts
  | .past => observation.TargetLifts

/-- Coverage is required only for the traversals the formula actually uses. -/
def CoversFormula (observation : SpanMap A B) : {n : Nat} → Formula Traversal n → Prop
  | _, .tt | _, .ff | _, .var _ => True
  | _, .neg inner | _, .mu inner | _, .nu inner => CoversFormula observation inner
  | _, .conj left right | _, .disj left right =>
      CoversFormula observation left ∧ CoversFormula observation right
  | _, .diamond direction inner | _, .box direction inner =>
      CoversDirection observation direction ∧ CoversFormula observation inner

theorem transition_lifted (observation : SpanMap A B)
    (source : X) (direction : Traversal) (covered : CoversDirection observation direction) {target : Y}
    (step : (transitionSystem B).trans (observation.states source) direction target) :
    ∃ lifted, (transitionSystem A).trans source direction lifted ∧ observation.states lifted = target := by
  cases direction <;> obtain ⟨event, first, second⟩ := step
  · obtain ⟨lifted, starts, ends⟩ := covered source event first
    exact ⟨A.target lifted, ⟨lifted, starts, rfl⟩, ends.trans second⟩
  · obtain ⟨lifted, ends, starts⟩ := covered source event first
    exact ⟨A.source lifted, ⟨lifted, ends, rfl⟩, starts.trans second⟩

/-- All fixed points are interpreted by the existing μ-calculus semantics.
The lifting assumptions concern endpoint coverage, not receipt multiplicity. -/
theorem satisfies_pullback (observation : SpanMap A B)
    {n : Nat} (formula : Formula Traversal n)
    (coverage : CoversFormula observation formula)
    (positive : fixedPointsPositive formula = true) (environment : Env Y n) (source : X) :
    satisfies (transitionSystem B) environment formula (observation.states source) ↔
      satisfies (transitionSystem A) (pullEnvironment observation.states environment) formula source := by
  induction formula generalizing source with
  | tt | ff | var _ => rfl
  | neg body ih => exact not_congr (ih coverage positive environment source)
  | conj left right il ir =>
    obtain ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp positive
    exact and_congr (il coverage.1 hl environment source) (ir coverage.2 hr environment source)
  | disj left right il ir =>
    obtain ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp positive
    exact or_congr (il coverage.1 hl environment source) (ir coverage.2 hr environment source)
  | diamond direction body ih =>
    constructor
    · rintro ⟨target, step, holds⟩
      obtain ⟨lifted, actual, same⟩ := transition_lifted observation source direction coverage.1 step
      exact ⟨lifted, actual, (ih coverage.2 positive environment lifted).mp (same ▸ holds)⟩
    · rintro ⟨target, step, holds⟩
      exact ⟨observation.states target, transition_preserved observation direction step,
        (ih coverage.2 positive environment target).mpr holds⟩
  | box direction body ih =>
    constructor
    · intro holds target step
      exact (ih coverage.2 positive environment target).mp
        (holds _ (transition_preserved observation direction step))
    · intro holds target step
      obtain ⟨lifted, actual, same⟩ := transition_lifted observation source direction coverage.1 step
      exact same ▸ (ih coverage.2 positive environment lifted).mpr (holds lifted actual)
  | mu body ih =>
    obtain ⟨boundPositive, innerPositive⟩ := Bool.and_eq_true_iff.mp positive
    rw [satisfies_mu_iff_mem_lfp _ _ _ boundPositive,
      satisfies_mu_iff_mem_lfp _ _ _ boundPositive]
    apply Set.ext_iff.mp (ObservedFixedPoints.least_preimage observation.states _ _ ?_) source
    intro candidate
    ext state
    simpa only [bodyOrderHom, OrderHom.coe_mk, sat, Set.mem_preimage, Set.mem_ofPred_eq,
      pullEnvironment_extend] using ih coverage innerPositive (environment.extend candidate) state
  | nu body ih =>
    obtain ⟨boundPositive, innerPositive⟩ := Bool.and_eq_true_iff.mp positive
    rw [satisfies_nu_iff_mem_gfp _ _ _ boundPositive,
      satisfies_nu_iff_mem_gfp _ _ _ boundPositive]
    apply Set.ext_iff.mp (ObservedFixedPoints.greatest_preimage observation.states _ _ ?_) source
    intro candidate
    ext state
    simpa only [bodyOrderHom, OrderHom.coe_mk, sat, Set.mem_preimage, Set.mem_ofPred_eq,
      pullEnvironment_extend] using ih coverage innerPositive (environment.extend candidate) state

end Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula
