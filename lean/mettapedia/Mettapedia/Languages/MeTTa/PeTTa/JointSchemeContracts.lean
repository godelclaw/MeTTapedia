import Mettapedia.Logic.LP.UnificationRenaming
import Mettapedia.Machines.AnswerCardinality

/-!
# Joint existential contracts for schematic calls

Input and result equations share one substitution. Declarations are distinct
alternatives, not execution alternatives. The executable guard uses the total
occurs-checked unifier, against an independent existential specification.

This layer accepts already generated type constraints. It does not assert that
SWI's classifier or constraint generator realizes the source typing rules.
Logical observations and private scheme variables have separate coordinates;
a residual answer retains the full joint problem for later observations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.JointSchemeContracts

open Mettapedia.Logic.LP

inductive Coordinate where
  | observation (slot : Nat)
  | scheme (scope index : Nat)
  | hole (scope : Nat) (path : List Nat)
  deriving DecidableEq, Repr

variable {σ : LPSignature} [DecidableEq σ.vars] [DecidableEq σ.constants]
  [DecidableEq σ.functionSymbols]

abbrev Equations (σ : LPSignature) := List (Term σ × Term σ)

structure Alternative (σ : LPSignature) where
  occurrence : Nat
  equations : Equations σ

/-- A single witness solves every input and result obligation of its row. -/
def Joint (alternatives : List (Alternative σ)) (observations : Equations σ) : Prop :=
  ∃ row ∈ alternatives, ∃ witness : Subst σ,
    Unifies witness (row.equations ++ observations)

def solvable (equations : Equations σ) : Bool := (unifyTotal equations).isSome

theorem solvable_iff (equations : Equations σ) :
    solvable equations = true ↔ ∃ witness : Subst σ, Unifies witness equations := by
  constructor
  · intro accepted
    cases h : unifyTotal equations with
    | none => simp [solvable, h] at accepted
    | some witness => exact ⟨witness, unifyTotal_sound _ _ h⟩
  · intro existsWitness
    obtain ⟨witness, accepted⟩ := unifyTotal_complete existsWitness
    simp [solvable, accepted]

def guard (alternatives : List (Alternative σ)) (observations : Equations σ) : Bool :=
  alternatives.any fun row => solvable (row.equations ++ observations)

theorem guard_iff (alternatives : List (Alternative σ)) (observations : Equations σ) :
    guard alternatives observations = true ↔ Joint alternatives observations := by
  simp only [guard, List.any_eq_true, solvable_iff, Joint]

theorem rejected_iff (alternatives : List (Alternative σ)) (observations : Equations σ) :
    guard alternatives observations = false ↔ ¬ Joint alternatives observations := by
  rw [← guard_iff]
  cases guard alternatives observations <;> simp

theorem guard_perm (alternatives : List (Alternative σ))
    (early late : Equations σ) (permutation : early.Perm late) :
    guard alternatives early = guard alternatives late := by
  have unifies_perm (witness : Subst σ) (row : Alternative σ) :
      Unifies witness (row.equations ++ early) ↔ Unifies witness (row.equations ++ late) := by
    simp only [Unifies, List.mem_append, permutation.mem_iff]
  apply Bool.eq_iff_iff.mpr
  rw [guard_iff, guard_iff]
  exact exists_congr fun row => and_congr_right fun _ => exists_congr fun witness =>
    unifies_perm witness row

/-- A fresh coordinate change preserves satisfiability even when the target
coordinate space contains unused variables. Distinct occurrences stay distinct. -/
def renameRow (f : σ.vars → σ.vars) (row : Alternative σ) : Alternative σ :=
  ⟨row.occurrence, UnificationRenaming.equations f row.equations⟩

theorem freshening_preserves_guard (f g : σ.vars → σ.vars)
    (inverse : Function.LeftInverse g f)
    (alternatives : List (Alternative σ)) (observations : Equations σ) :
    guard (alternatives.map (renameRow f)) (UnificationRenaming.equations f observations) =
      guard alternatives observations := by
  apply Bool.eq_iff_iff.mpr
  simp only [guard_iff, Joint, List.mem_map, renameRow]
  constructor
  · rintro ⟨row, ⟨original, member, rfl⟩, witness, solved⟩
    refine ⟨original, member, ?_⟩
    apply (UnificationRenaming.unifiable_iff f g inverse (original.equations ++ observations)).mp
    exact ⟨witness, by simpa [UnificationRenaming.equations, List.map_append] using solved⟩
  · rintro ⟨row, member, witness, solved⟩
    refine ⟨_, ⟨row, member, rfl⟩, ?_⟩
    obtain ⟨fresh, unifies⟩ :=
      (UnificationRenaming.unifiable_iff f g inverse (row.equations ++ observations)).mpr
        ⟨witness, solved⟩
    exact ⟨fresh, by simpa [UnificationRenaming.equations, List.map_append] using unifies⟩

/-- Subsequent observations use the original joint problem, not a chosen
early witness. This is the retained obligation exported with a result. -/
structure ConditionalAnswer (σ : LPSignature) (A : Type*) where
  value : A
  alternatives : List (Alternative σ)
  observations : Equations σ

def ConditionalAnswer.valid {A : Type*} (answer : ConditionalAnswer σ A)
    (later : Equations σ) : Prop :=
  Joint answer.alternatives (answer.observations ++ later)

def ConditionalAnswer.recheck {A : Type*} (answer : ConditionalAnswer σ A)
    (later : Equations σ) : Bool :=
  guard answer.alternatives (answer.observations ++ later)

theorem recheck_iff {A : Type*} (answer : ConditionalAnswer σ A) (later : Equations σ) :
    answer.recheck later = true ↔ answer.valid later := guard_iff _ _

theorem recheck_refutation_persists {A : Type*} (answer : ConditionalAnswer σ A)
    (early late : Equations σ) (refuted : answer.recheck early = false) :
    answer.recheck (early ++ late) = false := by
  unfold ConditionalAnswer.recheck at refuted ⊢
  rw [rejected_iff] at refuted ⊢
  rintro ⟨row, member, witness, solved⟩
  apply refuted
  refine ⟨row, member, witness, fun pair present => solved pair ?_⟩
  simp only [List.mem_append] at present ⊢
  tauto

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
/-- Checking each position under an unrelated witness is weaker than the
joint call contract. The converse fails for a shared polymorphic variable. -/
theorem joint_implies_separate (inputs output : Equations σ)
    (joint : ∃ witness : Subst σ, Unifies witness (inputs ++ output)) :
    (∃ witness : Subst σ, Unifies witness inputs) ∧
    (∃ witness : Subst σ, Unifies witness output) := by
  obtain ⟨witness, solved⟩ := joint
  exact ⟨⟨witness, fun pair member => solved pair (List.mem_append_left _ member)⟩,
    ⟨witness, fun pair member => solved pair (List.mem_append_right _ member)⟩⟩

/-- Erasing hidden evidence is a filter over the body's original answer
occurrences. It neither reorders nor repeats them, including equal values. -/
def authorize {A : Type*} (answers : List A)
    (contract : A → List (Alternative σ)) (observations : A → Equations σ) : List A :=
  answers.filter fun answer => guard (contract answer) (observations answer)

theorem authorize_sublist {A : Type*} (answers : List A)
    (contract : A → List (Alternative σ)) (observations : A → Equations σ) :
    (authorize answers contract observations).Sublist answers := List.filter_sublist

theorem authorized_iff {A : Type*} (answers : List A)
    (contract : A → List (Alternative σ)) (observations : A → Equations σ) (answer : A) :
    answer ∈ authorize answers contract observations ↔
      answer ∈ answers ∧ Joint (contract answer) (observations answer) := by
  simp [authorize, guard_iff]

theorem witness_erasure_preserves_cardinality_bound {A : Type*}
    (answers : List A) (contract : A → List (Alternative σ)) (observations : A → Equations σ)
    (grade : Mettapedia.Machines.AnswerCardinality.Grade)
    (bounded : Mettapedia.Machines.AnswerCardinality.Allows grade answers.length) :
    Mettapedia.Machines.AnswerCardinality.Allows
      (Mettapedia.Machines.AnswerCardinality.constrained grade)
      (authorize answers contract observations).length :=
  Mettapedia.Machines.AnswerCardinality.filter_sound grade answers _ bounded

/-- Erasure is justified by a proof for every occurrence. It does not depend
on an annotation, and it does not change earlier effects stored in answers. -/
theorem discharge_established_guard {A : Type*} (answers : List A)
    (contract : A → List (Alternative σ)) (observations : A → Equations σ)
    (established : ∀ answer ∈ answers, Joint (contract answer) (observations answer)) :
    authorize answers contract observations = answers := by
  apply List.filter_eq_self.mpr
  intro answer member
  exact (guard_iff _ _).mpr (established answer member)

namespace Controls

abbrev sig : LPSignature where
  constants := String
  vars := Coordinate
  relationSymbols := Unit
  relationArity _ := 0
  functionSymbols := Nat
  functionArity := id

def number : Term sig := .const "Number"
def string : Term sig := .const "String"
def shared : Term sig := .var (.scheme 0 0)
def inputEquations : Equations sig := [(shared, number)]
def outputEquations : Equations sig := [(shared, string)]

theorem shared_witness_conflict :
    solvable inputEquations = true ∧ solvable outputEquations = true ∧
      solvable (inputEquations ++ outputEquations) = false := by
  have solveOne (name : String) :
      Unifies (Subst.single (σ := sig) (.scheme 0 0) (.const name)) [(shared,.const name)] := by
    intro pair member
    simp only [List.mem_singleton] at member
    subst pair
    simp [shared,Subst.applyTerm,Subst.single]
  constructor
  · exact (solvable_iff (σ := sig) _).mpr ⟨_, solveOne "Number"⟩
  constructor
  · exact (solvable_iff (σ := sig) _).mpr ⟨_, solveOne "String"⟩
  · apply Bool.eq_false_iff.mpr
    intro accepted
    obtain ⟨witness, solved⟩ := (solvable_iff (σ := sig) _).mp accepted
    have first := solved (shared,number) (by simp [inputEquations])
    have second := solved (shared,string) (by simp [outputEquations])
    have conflict : number = string := first.symm.trans second
    exact (by decide : ("Number" : String) ≠ "String") (Term.const.inj conflict)

def twoChoices : List (Alternative sig) :=
  [⟨0, [(shared, number)]⟩, ⟨1, [(shared, string)]⟩]

theorem late_observation_can_choose_a_different_witness :
    guard twoChoices [] = true ∧ guard twoChoices [(shared, string)] = true := by
  constructor <;> apply (guard_iff (σ := sig) _ _).mpr
  · refine ⟨⟨0,inputEquations⟩, by simp [twoChoices,inputEquations],
      Subst.single (σ := sig) (.scheme 0 0) number, ?_⟩
    simp [Unifies,inputEquations,shared,number,Subst.applyTerm,Subst.single]
  · refine ⟨⟨1,outputEquations⟩, by simp [twoChoices,outputEquations],
      Subst.single (σ := sig) (.scheme 0 0) string, ?_⟩
    simp [Unifies,outputEquations,shared,string,Subst.applyTerm,Subst.single]

theorem two_witnesses_do_not_duplicate_execution :
    authorize [7,7] (fun _ => twoChoices) (fun _ => []) = [7,7] := by
  simp [authorize,late_observation_can_choose_a_different_witness.1]

def requiresNumber : ConditionalAnswer sig Nat := ⟨7, [⟨0,inputEquations⟩], []⟩
def requiresString : ConditionalAnswer sig Nat := ⟨7, [⟨0,outputEquations⟩], []⟩

theorem ground_projection_is_insufficient :
    requiresNumber.value = requiresString.value ∧
      requiresNumber.recheck [(shared,number)] = true ∧
      requiresString.recheck [(shared,number)] = false := by
  refine ⟨rfl, ?_, ?_⟩
  · apply (recheck_iff (σ := sig) _ _).mpr
    refine ⟨⟨0,inputEquations⟩, by simp [requiresNumber],
      Subst.single (σ := sig) (.scheme 0 0) number, ?_⟩
    simp [requiresNumber,Unifies,inputEquations,shared,number,Subst.applyTerm,Subst.single]
  · unfold ConditionalAnswer.recheck
    apply (rejected_iff (σ := sig) _ _).mpr
    rintro ⟨row, member, witness, solved⟩
    simp only [requiresString, List.mem_singleton] at member
    subst row
    have first := solved (shared,string) (by simp [requiresString,outputEquations])
    have second := solved (shared,number) (by simp [requiresString])
    have conflict : string = number := first.symm.trans second
    exact (by decide : ("String" : String) ≠ "Number") (Term.const.inj conflict)

end Controls

#print axioms guard_iff
#print axioms freshening_preserves_guard
#print axioms recheck_refutation_persists
#print axioms discharge_established_guard
#print axioms Controls.shared_witness_conflict

end Mettapedia.Languages.MeTTa.PeTTa.JointSchemeContracts
