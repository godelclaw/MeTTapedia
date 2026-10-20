import Mettapedia.Languages.MeTTa.PeTTa.SchematicCallTyping
import Mettapedia.Machines.ConstraintPropagation.ResidualChecks
import Mettapedia.Machines.ConstraintPropagation.FirstPending

/-!
# Reified truth for residual schematic questions

A question retains its declaration alternatives and every observable name,
even if its visible result is ground. Partial observations can already refute
the finite joint problem. Positive truth waits for all its observable inputs.
No unification witness escapes. A fixed question is used throughout refinement;
new declaration revisions create new questions rather than mutate old ones.

The observation slots here stand for generated type constraints. Source
term classification and a correspondence for SWI's attributed slots are
separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.ResidualSchemeTruth

open Mettapedia.Machines.ConstraintPropagation.Readiness.Bindings (Extends Refines)
open Mettapedia.Logic.LP
open JointSchemeContracts

variable {σ : LPSignature} [DecidableEq σ.vars] [DecidableEq σ.constants]
  [DecidableEq σ.functionSymbols]

structure Question (σ : LPSignature) where
  revision : Nat
  alternatives : List (Alternative σ)
  observables : List σ.vars

abbrev Partial (σ : LPSignature) := σ.vars → Option (GroundTerm σ)
abbrev Completion (σ : LPSignature) := σ.vars → GroundTerm σ

def observations (slots : List σ.vars) (bindings : Partial σ) : Equations σ :=
  slots.filterMap fun name =>
    (bindings name).map fun value => (Term.var name,value.toTerm)

def completeObservations (slots : List σ.vars) (completion : Completion σ) : Equations σ :=
  slots.map fun name => (Term.var name,(completion name).toTerm)

def Ready (question : Question σ) (bindings : Partial σ) : Bool :=
  question.observables.all fun name => (bindings name).isSome

def Holds (question : Question σ) (completion : Completion σ) : Prop :=
  ∃ row ∈ question.alternatives, ∃ witness : Subst σ,
    Unifies witness row.equations ∧
      ∀ name ∈ question.observables,
        witness name = (completion name).toTerm

def probe (question : Question σ) (bindings : Partial σ) : Option Bool :=
  if guard question.alternatives (observations question.observables bindings) then
    if Ready question bindings then some true else none
  else some false

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
theorem holds_iff_joint (question : Question σ) (completion : Completion σ) :
    Holds question completion ↔
      Joint question.alternatives (completeObservations question.observables completion) := by
  have grounded (witness : Subst σ) (value : GroundTerm σ) :
      witness.applyTerm value.toTerm = value.toTerm := by
    induction value with
    | const _ => rfl
    | app _ _ ih => simp [GroundTerm.toTerm,ih]
  simp only [Holds,Joint,SchematicCallTyping.unifies_append]
  apply exists_congr
  intro row
  apply and_congr_right
  intro _
  apply exists_congr
  intro witness
  apply and_congr_right
  intro _
  constructor
  · intro solved pair present
    obtain ⟨name,member,rfl⟩ := List.mem_map.mp present
    simpa [Subst.applyTerm,grounded] using solved name member
  · intro solved name present
    have equation := solved _ (List.mem_map.mpr ⟨name,present,rfl⟩)
    simpa [Subst.applyTerm,grounded] using equation

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
theorem observations_subset (slots : List σ.vars) (bindings : Partial σ)
    (completion : Completion σ) (extension : Extends bindings completion) :
    ∀ equation ∈ observations slots bindings,
      equation ∈ completeObservations slots completion := by
  intro equation member
  obtain ⟨name,present,found⟩ := List.mem_filterMap.mp member
  cases hv : bindings name with
  | none => simp [hv] at found
  | some value =>
      have same : (Term.var name,value.toTerm) = equation := by simpa [hv] using found
      subst equation
      exact List.mem_map.mpr ⟨name,present,by rw [extension name value hv]⟩

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
theorem ready_observations (question : Question σ) (bindings : Partial σ)
    (completion : Completion σ) (extension : Extends bindings completion)
    (ready : Ready question bindings = true) :
    observations question.observables bindings =
      completeObservations question.observables completion := by
  unfold observations completeObservations
  apply List.filterMap_eq_map_iff_forall_eq_some.mpr
  intro name member
  have present := List.all_eq_true.mp ready name member
  cases h : bindings name with
  | none => simp [h] at present
  | some value => simp [extension name value h]

theorem probe_correct (question : Question σ) (bindings : Partial σ)
    (completion : Completion σ) (extension : Extends bindings completion)
    (verdict : Bool) (decided : probe question bindings = some verdict) :
    Holds question completion ↔ verdict = true := by
  unfold probe at decided
  split at decided
  · rename_i accepted
    split at decided
    · rename_i ready
      simp only [Option.some.injEq] at decided
      subst verdict
      rw [holds_iff_joint,← ready_observations question bindings completion extension ready]
      exact ⟨fun _ => rfl,fun _ => (guard_iff _ _).mp accepted⟩
    · contradiction
  · rename_i rejected
    simp only [Option.some.injEq] at decided
    subst verdict
    simp only [Bool.false_eq_true,iff_false]
    rw [holds_iff_joint]
    intro complete
    obtain ⟨row,member,witness,solves⟩ := complete
    have partialSolved : Joint question.alternatives (observations question.observables bindings) := by
      refine ⟨row,member,witness,?_⟩
      rw [SchematicCallTyping.unifies_append] at solves ⊢
      exact ⟨solves.1,fun pair present => solves.2 pair
        (observations_subset _ bindings completion extension pair present)⟩
    exact rejected ((guard_iff _ _).mpr partialSolved)

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
theorem observations_refine (slots : List σ.vars) (early late : Partial σ)
    (refines : Refines early late) :
    ∀ equation ∈ observations slots early, equation ∈ observations slots late := by
  intro equation member
  obtain ⟨name, present, found⟩ := List.mem_filterMap.mp member
  cases h : early name with
  | none => simp [h] at found
  | some value =>
      apply List.mem_filterMap.mpr
      exact ⟨name, present, by simpa [h, refines name value h] using found⟩

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
theorem ready_refines (question : Question σ) (early late : Partial σ)
    (refines : Refines early late) (ready : Ready question early = true) :
    Ready question late = true ∧
      observations question.observables early = observations question.observables late := by
  have equal : ∀ name ∈ question.observables, early name = late name := by
    intro name member
    have present := List.all_eq_true.mp ready name member
    cases h : early name with
    | none => simp [h] at present
    | some value => exact (refines name value h).symm
  constructor
  · apply List.all_eq_true.mpr
    intro name member
    rw [← equal name member]
    exact List.all_eq_true.mp ready name member
  · unfold observations
    exact List.filterMap_congr fun name member => by rw [equal name member]

theorem rejection_refines (question : Question σ) (early late : Partial σ)
    (refines : Refines early late)
    (rejected : guard question.alternatives (observations question.observables early) ≠ true) :
    guard question.alternatives (observations question.observables late) ≠ true := by
  intro accepted
  obtain ⟨row, present, witness, solves⟩ := (guard_iff _ _).mp accepted
  apply rejected
  apply (guard_iff _ _).mpr
  refine ⟨row, present, witness, ?_⟩
  rw [SchematicCallTyping.unifies_append] at solves ⊢
  exact ⟨solves.1, fun equation member => solves.2 equation
    (observations_refine _ early late refines equation member)⟩

/-- Established Boolean answers remain stable under later observations.
The negative case uses completeness of the finite joint unifier, not failure
or a budget limit of a source search. -/
theorem probe_refines (question : Question σ) (early late : Partial σ)
    (refines : Refines early late) (verdict : Bool)
    (decided : probe question early = some verdict) :
    probe question late = some verdict := by
  unfold probe at decided ⊢
  split at decided
  · rename_i accepted
    split at decided
    · rename_i ready
      obtain ⟨laterReady, same⟩ := ready_refines question early late refines ready
      simpa [← same, accepted, laterReady] using decided
    · contradiction
  · rename_i rejected
    simpa [rejection_refines question early late refines rejected] using decided

/-- Reified truth watches every missing observation: any newly supplied
observation can refute the joint problem before all positions are ready.
This differs from waiting for every producer of an inferred type to finish. -/
def pendingObservations (question : Question σ) (bindings : Partial σ) : List σ.vars :=
  Machines.ConstraintPropagation.FirstPending.active
    (fun name => (bindings name).isSome) question.observables

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
theorem pendingObservations_nil_iff (question : Question σ) (bindings : Partial σ) :
    pendingObservations question bindings = [] ↔ Ready question bindings = true := by
  simp [pendingObservations, Machines.ConstraintPropagation.FirstPending.active,
    Ready, List.all_eq_true, Option.isSome_iff_ne_none]

theorem unfinished_has_watch (question : Question σ) (bindings : Partial σ)
    (unfinished : probe question bindings = none) :
    ∃ name ∈ pendingObservations question bindings,
      name ∈ question.observables ∧ bindings name = none := by
  have unready : Ready question bindings ≠ true := by
    intro ready
    unfold probe at unfinished
    split at unfinished
    · simp at unfinished
    · simp at unfinished
  have nonempty : pendingObservations question bindings ≠ [] :=
    fun empty => unready ((pendingObservations_nil_iff question bindings).mp empty)
  obtain ⟨name, member⟩ := List.exists_mem_of_ne_nil _ nonempty
  have selected := (Machines.ConstraintPropagation.FirstPending.active_exact
    (fun slot => (bindings slot).isSome) question.observables name).mp member
  exact ⟨name, member, selected.1, by simpa using selected.2⟩

open Machines.ConstraintPropagation.ResidualChecks in
theorem incremental_questions_match_final (early late : Partial σ)
    (refines : Refines early late) (questions : List (Question σ)) :
    (discharge (fun question => probe question early) questions).bind
      (discharge (fun question => probe question late)) =
      discharge (fun question => probe question late) questions :=
  discharge_compose _ _ (fun question verdict =>
    probe_refines question early late refines verdict) questions

open Machines.ConstraintPropagation.ResidualChecks in
theorem question_store_preserves_completions (bindings : Partial σ)
    (completion : Completion σ) (extension : Extends bindings completion)
    (questions : List (Question σ)) :
    OutcomeHolds (fun question => Holds question completion)
      (discharge (fun question => probe question bindings) questions) ↔
    Machines.ConstraintPropagation.ResidualChecks.Holds
      (fun question => Holds question completion) questions :=
  discharge_correct _ _ (fun question verdict =>
    probe_correct question bindings completion extension verdict) questions

/-- Consumers preserve a false answer as an answer. Pending truth does not
select either branch and does not become a negative result. -/
def consume {A : Type*} (truth : Option Bool) (yes no : A) : Option A :=
  truth.map fun boolean => if boolean then yes else no

theorem pending_does_not_choose {A : Type*} (yes no : A) :
    consume none yes no = none := rfl

theorem false_selects_else {A : Type*} (yes no : A) :
    consume (some false) yes no = some no := rfl

/-- Export keeps the question as well as the visible value. Projection alone
cannot carry this interpretation when the value has no free slots. -/
structure Evidence (σ : LPSignature) (A : Type*) where
  visible : A
  questions : List (Question σ)

def Evidence.valid {A : Type*} (evidence : Evidence σ A) (completion : Completion σ) : Prop :=
  ∀ question ∈ evidence.questions, Holds question completion

namespace Controls

abbrev sig : LPSignature where
  constants := String
  vars := Nat
  relationSymbols := Unit
  relationArity _ := 0
  functionSymbols := Empty
  functionArity := Empty.elim

def pairQuestion : Question sig := ⟨0, [⟨0,
  [(.var 0,.const "Number"),(.var 1,.const "String")]⟩], [0,1]⟩

def emptyBindings : Partial sig := fun _ => none
def badSecond : Partial sig := fun slot =>
  if slot = 1 then some (.const "Number") else none
def goodFirst : Partial sig := fun slot =>
  if slot = 0 then some (.const "Number") else none
def goodBoth : Partial sig := fun slot =>
  if slot = 0 then some (.const "Number") else some (.const "String")

def completion : Completion sig := fun slot =>
  if slot = 0 then .const "Number" else .const "String"

theorem completion_holds : Holds pairQuestion completion := by
  refine ⟨⟨0,[(.var 0,.const "Number"),(.var 1,.const "String")]⟩,
    by simp [pairQuestion], fun slot => (completion slot).toTerm, ?_, ?_⟩
  · simp [Unifies, completion, Subst.applyTerm, GroundTerm.toTerm]
  · intro name _; rfl

theorem compatible_partial (bindings : Partial sig) (extension : Extends bindings completion) :
    guard pairQuestion.alternatives (observations pairQuestion.observables bindings) = true := by
  obtain ⟨row, present, witness, solves⟩ := (holds_iff_joint _ _).mp completion_holds
  apply (guard_iff (σ := sig) _ _).mpr
  refine ⟨row, present, witness, ?_⟩
  rw [SchematicCallTyping.unifies_append] at solves ⊢
  exact ⟨solves.1, fun equation member => solves.2 equation
    (observations_subset _ bindings completion extension equation member)⟩

theorem incomplete_positive_is_retained :
    probe pairQuestion emptyBindings = none ∧
      probe pairQuestion goodFirst = none := by
  have emptyAccepted := compatible_partial emptyBindings (by
    intro name value found; simp [emptyBindings] at found)
  have firstAccepted := compatible_partial goodFirst (by
    intro name value found
    by_cases zero : name = 0
    · simpa [goodFirst,completion,zero] using found
    · simp [goodFirst,zero] at found)
  simp only [probe,emptyAccepted,firstAccepted,↓reduceIte]
  simp [Ready,pairQuestion,emptyBindings,goodFirst]

theorem early_negative_without_all_inputs :
    probe pairQuestion badSecond = some false ∧
      pendingObservations pairQuestion badSecond = [0] := by
  have rejected : guard pairQuestion.alternatives
      (observations pairQuestion.observables badSecond) ≠ true := by
    intro accepted
    obtain ⟨row, present, witness, solves⟩ := (guard_iff (σ := sig) _ _).mp accepted
    simp only [pairQuestion,List.mem_singleton] at present
    subst row
    have expected := solves (.var 1,.const "String") (by simp)
    have actual := solves (.var 1,.const "Number") (by
      simp [observations,pairQuestion,badSecond,GroundTerm.toTerm])
    have impossible : ("String" : String) = "Number" :=
      Term.const.inj (expected.symm.trans actual)
    exact (by decide : ("String" : String) ≠ "Number") impossible
  constructor
  · simp [probe,rejected]
  · simp [pendingObservations,Machines.ConstraintPropagation.FirstPending.active,
      pairQuestion,badSecond]

theorem finished_positive : probe pairQuestion goodBoth = some true := by
  have accepted := compatible_partial goodBoth (by
    intro name value found
    by_cases zero : name = 0 <;> simpa [goodBoth,completion,zero] using found)
  simp only [probe,accepted,↓reduceIte]
  simp [Ready,pairQuestion,goodBoth]

/-- A watch on just the first missing slot would miss an available refutation. -/
theorem later_position_can_refute_first :
    emptyBindings 0 = badSecond 0 ∧
      probe pairQuestion emptyBindings = none ∧
      probe pairQuestion badSecond = some false :=
  ⟨rfl,incomplete_positive_is_retained.1,early_negative_without_all_inputs.1⟩

theorem consistent_observation_growth : Refines goodFirst goodBoth := by
  intro name value found
  by_cases zero : name = 0
  · simpa [goodFirst,goodBoth,zero] using found
  · simp [goodFirst,zero] at found

end Controls

#print axioms holds_iff_joint
#print axioms probe_correct
#print axioms probe_refines
#print axioms unfinished_has_watch
#print axioms incremental_questions_match_final
#print axioms question_store_preserves_completions
#print axioms Controls.early_negative_without_all_inputs

end Mettapedia.Languages.MeTTa.PeTTa.ResidualSchemeTruth
