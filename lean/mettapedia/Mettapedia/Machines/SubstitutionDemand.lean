import Mettapedia.Logic.LP.UnificationIdempotence

/-!
# Eliding discarded argument images

A computation argument is scheduled using its original source. Substituting
that source first only to reject it as an immediate value builds a discarded
image. A fixed non-carrier head and nonempty variable support establish the
rejection before substitution: carrier fields cannot change that fixed head,
and the closed-normal-data shortcut does not apply to an open source.

This uses the existing finite first-order term and substitution algebra.
`Classifier` makes the representation boundary explicit: fields can decide
whether a potential carrier is valid, but cannot turn another head into one.
Native dynamic heads, internal tags, missing frames, graph summaries, allocation
failure and C correspondence are separate implementation obligations. A native
acyclic graph must supply a total substitution for this algebra to apply.

The second reduction concerns an IF continuation that resumes the stored source
and discards an independently prepared image. The partial-reader control shows
why a possibly failing preparation cannot be erased without admission.

The cost results concern structural image visits and a head-observation decision
model. They are not overall runtime, heap-optimality or instruction guarantees.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SubstitutionDemand

open Mettapedia.Logic.LP

variable {σ : LPSignature} [DecidableEq σ.vars]

structure Classifier (σ : LPSignature) where
  carrierHead : σ.functionSymbols → Bool
  carrierFields : (head : σ.functionSymbols) →
    (Fin (σ.functionArity head) → Term σ) → Bool
  normalData : Term σ → Bool

def Classifier.immediate (classifier : Classifier σ) : Term σ → Bool
  | .var _ | .const _ => true
  | .app head fields => classifier.carrierHead head &&
      classifier.carrierFields head fields

def Classifier.fixedComputation (classifier : Classifier σ) : Term σ → Bool
  | .app head _ => !classifier.carrierHead head
  | _ => false

omit [DecidableEq σ.vars] in
theorem substitution_preserves_nonvalue (classifier : Classifier σ)
    (θ : Subst σ) {source : Term σ}
    (fixed : classifier.fixedComputation source = true) :
    classifier.immediate (θ.applyTerm source) = false := by
  cases source with
  | var cell => simp [Classifier.fixedComputation] at fixed
  | const literal => simp [Classifier.fixedComputation] at fixed
  | app head fields =>
      have excluded : classifier.carrierHead head = false := by
        cases h : classifier.carrierHead head <;>
          simp_all [Classifier.fixedComputation]
      simp [Subst.applyTerm, Classifier.immediate, excluded]

inductive Prepared (σ : LPSignature) where
  | value (image : Term σ)
  | compute (source : Term σ)

def prepare (classifier : Classifier σ) (θ : Subst σ)
    (heldValue : Bool) (source : Term σ) : Prepared σ :=
  let image := θ.applyTerm source
  if heldValue || classifier.immediate image then .value image
  else if source.freeVars = ∅ ∧ classifier.normalData image = true then .value image
  else .compute source

def admitted (classifier : Classifier σ) (heldValue : Bool)
    (source : Term σ) : Bool :=
  decide (heldValue = false ∧ source.freeVars.Nonempty ∧
    classifier.fixedComputation source = true)

def prepareByDemand (classifier : Classifier σ) (θ : Subst σ)
    (heldValue : Bool) (source : Term σ) : Prepared σ :=
  if admitted classifier heldValue source then .compute source
  else prepare classifier θ heldValue source

theorem admitted_preparation (classifier : Classifier σ) (θ : Subst σ)
    {heldValue : Bool} {source : Term σ}
    (accepted : admitted classifier heldValue source = true) :
    prepare classifier θ heldValue source = .compute source := by
  have facts := of_decide_eq_true accepted
  obtain ⟨held, openSource, fixed⟩ := facts
  have notClosed : source.freeVars ≠ ∅ := Finset.nonempty_iff_ne_empty.mp openSource
  simp [prepare, held, notClosed, substitution_preserves_nonvalue classifier θ fixed]

theorem prepareByDemand_eq (classifier : Classifier σ) (θ : Subst σ)
    (heldValue : Bool) (source : Term σ) :
    prepareByDemand classifier θ heldValue source =
      prepare classifier θ heldValue source := by
  unfold prepareByDemand
  split
  · exact (admitted_preparation classifier θ ‹_›).symm
  · rfl

inductive Stamped (σ : LPSignature) where
  | value (image : Term σ)
  | compute (source : Term σ) (destination : Nat)

/-- Each computed argument gets the next destination; source order is retained. -/
def stamp (next : Nat) : List (Prepared σ) → List (Stamped σ)
  | [] => []
  | .value image :: rest => .value image :: stamp next rest
  | .compute source :: rest => .compute source next :: stamp (next + 1) rest

theorem ordered_arguments_and_destinations (classifier : Classifier σ)
    (θ : Subst σ) (arguments : List (Bool × Term σ)) (next : Nat) :
    stamp next (arguments.map (fun (held, source) =>
      prepareByDemand classifier θ held source)) =
    stamp next (arguments.map (fun (held, source) =>
      prepare classifier θ held source)) := by
  simp only [prepareByDemand_eq]

/-- Any subsequent interpretation receives exactly the same stamped goals.
The observer may include fuel, effects, answer order and multiplicity. -/
theorem every_goal_observer_agrees {Observation : Type*}
    (observe : List (Stamped σ) → Observation) (classifier : Classifier σ)
    (θ : Subst σ) (arguments : List (Bool × Term σ)) (next : Nat) :
    observe (stamp next (arguments.map (fun (held, source) =>
      prepareByDemand classifier θ held source))) =
    observe (stamp next (arguments.map (fun (held, source) =>
      prepare classifier θ held source))) := by
  rw [ordered_arguments_and_destinations]

/-- The reader's result is discarded, but its failure is still observable. -/
def prepareDiscarded {Source Image State : Type*}
    (read : Source → Option Image) (source : Source) (resume : State) : Option State :=
  (read source).map (fun _ => resume)

theorem discard_total_preparation {Source Image State : Type*}
    (read : Source → Image) (source : Source) (resume : State) :
    prepareDiscarded (fun source => some (read source)) source resume = some resume := by
  rfl

theorem failing_preparation_must_be_retained {Source Image State : Type*}
    (read : Source → Option Image) (source : Source) (resume : State)
    (failed : read source = none) :
    prepareDiscarded read source resume ≠ some resume := by
  simp [prepareDiscarded, failed]

/-- This counts an unshared structural substitution's node visits. The native
implementation can have its own additional memo and support shortcuts. -/
def preparationVisits (source : Term σ) : Nat := source.size

def demandedVisits (classifier : Classifier σ) (heldValue : Bool)
    (source : Term σ) : Nat :=
  if admitted classifier heldValue source then 0 else preparationVisits source

theorem demanded_visits_le (classifier : Classifier σ) (heldValue : Bool)
    (source : Term σ) :
    demandedVisits classifier heldValue source ≤ preparationVisits source := by
  unfold demandedVisits
  split <;> omega

theorem admitted_visits_strictly_less (classifier : Classifier σ)
    {heldValue : Bool} {source : Term σ}
    (accepted : admitted classifier heldValue source = true) :
    demandedVisits classifier heldValue source < preparationVisits source := by
  simpa [demandedVisits, accepted, preparationVisits] using source.size_pos

/-! A decision program can answer immediately or inspect the immutable head.
Repeated inspections are permitted. A nonconstant head predicate requires at
least one inspection on every input; one inspection therefore meets the bound. -/

inductive HeadProgram (Head : Type*) where
  | answer (decision : Bool)
  | inspect (next : Head → HeadProgram Head)

def HeadProgram.run {Head : Type*} : HeadProgram Head → Head → Bool
  | .answer decision, _ => decision
  | .inspect next, head => (next head).run head

def HeadProgram.visits {Head : Type*} : HeadProgram Head → Head → Nat
  | .answer _, _ => 0
  | .inspect next, head => 1 + (next head).visits head

theorem head_inspection_lower_bound {Head : Type*} (predicate : Head → Bool)
    (ordinary carrier : Head) (ordinaryDecision : predicate ordinary = true)
    (carrierDecision : predicate carrier = false) (program : HeadProgram Head)
    (correct : ∀ head, program.run head = predicate head) (head : Head) :
    1 ≤ program.visits head := by
  cases program with
  | answer decision =>
      have left := correct ordinary
      have right := correct carrier
      simp only [HeadProgram.run, ordinaryDecision, carrierDecision] at left right
      exact False.elim (Bool.noConfusion (left.symm.trans right))
  | inspect next => simp [HeadProgram.visits]

def headDecision {Head : Type*} (predicate : Head → Bool) : HeadProgram Head :=
  .inspect (fun head => .answer (predicate head))

theorem headDecision_correct {Head : Type*} (predicate : Head → Bool) (head : Head) :
    (headDecision predicate).run head = predicate head := rfl

theorem headDecision_minimal {Head : Type*} (predicate : Head → Bool)
    (ordinary carrier : Head) (ordinaryDecision : predicate ordinary = true)
    (carrierDecision : predicate carrier = false) (program : HeadProgram Head)
    (correct : ∀ head, program.run head = predicate head) (head : Head) :
    (headDecision predicate).visits head ≤ program.visits head :=
  head_inspection_lower_bound predicate ordinary carrier ordinaryDecision
    carrierDecision program correct head

namespace Controls

abbrev signature : LPSignature where
  vars := Nat
  constants := Nat
  functionSymbols := Nat
  functionArity := fun _ => 1
  relationSymbols := Empty
  relationArity := Empty.elim

/-- Head zero is a potential carrier whose first field must be constant 42. -/
def classifier : Classifier signature where
  carrierHead head := head == 0
  carrierFields _ fields := match fields 0 with
    | .const value => value == 42
    | _ => false
  normalData _ := true

def ordinary : Term signature := .app 1 (fun _ => .var 0)
def malformedCarrier : Term signature := .app 0 (fun _ => .var 0)
def valueStore : Subst signature := fun _ => .const 42

theorem ordinary_open_source_is_admitted : admitted classifier false ordinary = true := by
  decide

theorem held_value_is_not_admitted : admitted classifier true ordinary = false := by
  rfl

theorem closed_normal_data_is_not_admitted :
    admitted classifier false (.app 1 (fun _ => .const 42)) = false := by decide

theorem malformed_carrier_can_become_a_value :
    classifier.immediate malformedCarrier = false ∧
    classifier.immediate (valueStore.applyTerm malformedCarrier) = true ∧
    admitted classifier false malformedCarrier = false := by
  decide

theorem variable_head_must_defer :
    classifier.fixedComputation (.var 0) = false ∧
    classifier.immediate (valueStore.applyTerm (.var 0)) = true := by
  constructor <;> rfl

end Controls

end Mettapedia.Machines.SubstitutionDemand
