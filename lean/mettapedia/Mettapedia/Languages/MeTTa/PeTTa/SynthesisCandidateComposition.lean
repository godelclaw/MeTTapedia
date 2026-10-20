import Mettapedia.Languages.MeTTa.PeTTa.DeclarationTypeCandidates
import Mettapedia.Logic.LP.ListTerms

/-!
# Composing constrained type candidates

Structural descriptions collect element types; application checks arguments
against a fresh, resolved arrow. Both keep the conditions of their constituent
answers, including when the result type is ground. All positions share one
substitution. Structural products retain order and repeated occurrences.
Application and closure correctness concern admissibility: intermediate type
witnesses are not identified with the public query's answer occurrences.

These are composition laws for candidate synthesis, not a second call checker.
The independent relations below use the existing joint typing judgment. The
generated candidates feed its existing occurs-checked decision procedure.

The supplied arrow domains already distinguish universal contracts from type
patterns. Source head classification, adapter parsing, declaration freshening,
gradual consistency and suspended synthesis remain separate boundaries.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.SynthesisCandidateComposition

open Mettapedia.Logic.LP
open JointSchemeContracts
open SchematicCallTyping (Domain Candidate Candidates Checks ChecksVector)

variable {σ : LPSignature}

structure Selection (σ : LPSignature) where
  types : List (Term σ)
  conditions : Equations σ

/-- The first position varies slowest, as in left-to-right Prolog conjunction.
No equality test removes repeated alternatives. -/
def selections : List (Candidates σ) → List (Selection σ)
  | [] => [⟨[], []⟩]
  | first :: rest => first.flatMap fun head =>
      (selections rest).map fun tail =>
        ⟨head.type :: tail.types, head.conditions ++ tail.conditions⟩

theorem selection_exact (witness : Subst σ) (choices : List (Candidates σ))
    (types : List (Term σ)) :
    (∃ selected ∈ selections choices,
      Unifies witness selected.conditions ∧
      selected.types.map witness.applyTerm = types.map witness.applyTerm) ↔
    ChecksVector witness (types.map Domain.typed) choices := by
  induction choices generalizing types with
  | nil =>
      cases types with
      | nil =>
          constructor
          · intro _; exact .nil
          · intro _; exact ⟨⟨[],[]⟩, by simp [selections], by simp [Unifies], rfl⟩
      | cons first rest =>
          constructor
          · simp [selections]
          · intro impossible; cases impossible
  | cons first rest ih =>
      cases types with
      | nil =>
          constructor
          · rintro ⟨selected, member, _, equal⟩
            obtain ⟨head, _, mapped⟩ := List.mem_flatMap.mp member
            obtain ⟨tail, _, rfl⟩ := List.mem_map.mp mapped
            simp at equal
          · intro impossible; cases impossible
      | cons type types =>
          constructor
          · rintro ⟨selected, member, solved, equal⟩
            obtain ⟨head, present, mapped⟩ := List.mem_flatMap.mp member
            obtain ⟨tail, tailMember, rfl⟩ := List.mem_map.mp mapped
            obtain ⟨headSolved, tailSolved⟩ :=
              (SchematicCallTyping.unifies_append witness _ _).mp solved
            have equalities := List.cons.inj equal
            exact .cons (.typed present headSolved equalities.1)
              ((ih types).mp ⟨tail, tailMember, tailSolved, equalities.2⟩)
          · intro checked
            cases checked with
            | cons headChecked tailChecked =>
                cases headChecked with
                | @typed _ head _ present headSolved equal =>
                    obtain ⟨tail, tailMember, tailSolved, tailEqual⟩ :=
                      (ih types).mpr tailChecked
                    refine ⟨⟨head.type :: tail.types, head.conditions ++ tail.conditions⟩,
                      List.mem_flatMap.mpr ⟨head, present,
                        List.mem_map.mpr ⟨tail, tailMember, rfl⟩⟩,
                      (SchematicCallTyping.unifies_append witness _ _).mpr
                        ⟨headSolved, tailSolved⟩, ?_⟩
                    simp only [List.map_cons, equal, tailEqual]

/-- Intrinsic typing contributes one unconditional answer. -/
theorem intrinsic_exact (witness : Subst σ) (intrinsic expected : Term σ) :
    Checks witness (.typed expected) [.plain intrinsic] ↔
      witness.applyTerm intrinsic = witness.applyTerm expected := by
  constructor
  · intro checked
    cases checked with
    | typed member _ equal =>
        simp only [List.mem_singleton] at member
        subst_vars
        exact equal
  · intro equal
    exact .typed (actual := .plain intrinsic) (by simp) (by simp [Candidate.plain,Unifies]) equal

section Structural

variable {Constant Variable : Type}
local notation "τ" => ListTerms.signature Constant Variable

def tuples (children : List (Candidates τ)) : Candidates τ :=
  (selections children).map fun selected =>
    ⟨ListTerms.ofList selected.types, selected.conditions⟩

/-- Each element has its own type, under the same substitution. This is a
description of data and imposes no callable interpretation on the head. -/
inductive Structural (witness : Subst τ) (children : List (Candidates τ))
    (expected : Term τ) : Prop where
  | tuple (types : List (Term τ)) :
      ChecksVector witness (types.map Domain.typed) children →
      ListTerms.ofList (types.map witness.applyTerm) = witness.applyTerm expected →
      Structural witness children expected

theorem tuples_exact (witness : Subst τ) (children : List (Candidates τ))
    (expected : Term τ) :
    Checks witness (.typed expected) (tuples children) ↔
      Structural witness children expected := by
  constructor
  · intro checked
    cases checked with
    | typed member solved equal =>
        obtain ⟨selected, present, rfl⟩ := List.mem_map.mp member
        exact .tuple selected.types
          ((selection_exact witness children selected.types).mp ⟨selected,present,solved,rfl⟩)
          (by simpa [ListTerms.apply_ofList] using equal)
  · intro described
    cases described with
    | tuple types checked equal =>
        obtain ⟨selected, present, solved, same⟩ :=
          (selection_exact witness children types).mpr checked
        refine Checks.typed (actual := ⟨ListTerms.ofList selected.types, selected.conditions⟩)
          (List.mem_map.mpr ⟨selected, present, rfl⟩) solved ?_
        simpa only [ListTerms.apply_ofList, same] using equal

end Structural

/-- A head's fresh arrow reading, with its own retained subject conditions.
Its domains have already been classified before inference substitutions. -/
structure Arrow (σ : LPSignature) where
  domains : List (Domain σ)
  result : Term σ
  conditions : Equations σ

inductive Application (witness : Subst σ) (arrows : List (Arrow σ))
    (arguments : List (Candidates σ)) (expected : Term σ) : Prop where
  | apply {arrow : Arrow σ} :
      arrow ∈ arrows → Unifies witness arrow.conditions →
      ChecksVector witness arrow.domains arguments →
      witness.applyTerm arrow.result = witness.applyTerm expected →
      Application witness arrows arguments expected

def applications (arrows : List (Arrow σ)) (arguments : List (Candidates σ)) : Candidates σ :=
  arrows.flatMap fun arrow =>
    (SchematicCallTyping.vector arrow.domains arguments).map fun equations =>
      ⟨arrow.result, arrow.conditions ++ equations⟩

theorem applications_exact (witness : Subst σ) (arrows : List (Arrow σ))
    (arguments : List (Candidates σ)) (expected : Term σ) :
    Checks witness (.typed expected) (applications arrows arguments) ↔
      Application witness arrows arguments expected := by
  constructor
  · intro checked
    cases checked with
    | typed member solved equal =>
        obtain ⟨arrow, present, mapped⟩ := List.mem_flatMap.mp member
        obtain ⟨equations, equationsMember, rfl⟩ := List.mem_map.mp mapped
        obtain ⟨headSolved, argumentsSolved⟩ :=
          (SchematicCallTyping.unifies_append witness _ _).mp solved
        exact .apply present headSolved
          ((SchematicCallTyping.vector_iff witness _ _).mp
            ⟨equations, equationsMember, argumentsSolved⟩) equal
  · intro applied
    cases applied with
    | @apply arrow present headSolved argumentsChecked equal =>
        obtain ⟨equations, equationsMember, argumentsSolved⟩ :=
          (SchematicCallTyping.vector_iff witness _ _).mpr argumentsChecked
        exact Checks.typed (actual := ⟨arrow.result, arrow.conditions ++ equations⟩)
          (List.mem_flatMap.mpr ⟨arrow, present,
            List.mem_map.mpr ⟨equations, equationsMember, rfl⟩⟩)
          ((SchematicCallTyping.unifies_append witness _ _).mpr
            ⟨headSolved, argumentsSolved⟩) equal

theorem checksVector_split (witness : Subst σ) (domains : List (Domain σ))
    (bound remaining : List (Candidates σ)) :
    ChecksVector witness domains (bound ++ remaining) ↔
      ChecksVector witness (domains.take bound.length) bound ∧
      ChecksVector witness (domains.drop bound.length) remaining := by
  induction bound generalizing domains with
  | nil =>
      simp only [List.nil_append, List.length_nil, List.take_zero, List.drop_zero]
      exact ⟨fun checked => ⟨.nil,checked⟩, fun checked => checked.2⟩
  | cons first rest ih =>
      cases domains with
      | nil =>
          constructor
          · intro impossible; cases impossible
          · rintro ⟨impossible,_⟩; cases impossible
      | cons domain domains =>
          constructor
          · intro checked
            cases checked with
            | cons head tail =>
                obtain ⟨before,after⟩ := (ih domains).mp tail
                exact ⟨.cons head before,after⟩
          · rintro ⟨before,after⟩
            cases before with
            | cons head tail => exact .cons head ((ih domains).mpr ⟨tail,after⟩)

/-- A closure retains the original scheme coordinates. Only consumed domains
are removed; their equations stay with the remaining contract. -/
def closures (arrows : List (Arrow σ)) (bound : List (Candidates σ)) : List (Arrow σ) :=
  arrows.flatMap fun arrow =>
    if bound.length < arrow.domains.length then
      (SchematicCallTyping.vector (arrow.domains.take bound.length) bound).map fun equations =>
        ⟨arrow.domains.drop bound.length, arrow.result, arrow.conditions ++ equations⟩
    else []

theorem complete_call_is_not_closure (arrow : Arrow σ) (bound : List (Candidates σ))
    (complete : arrow.domains.length ≤ bound.length) :
    closures [arrow] bound = [] := by
  simp [closures, Nat.not_lt.mpr complete]

theorem closure_application_exact (witness : Subst σ) (arrows : List (Arrow σ))
    (bound remaining : List (Candidates σ)) (expected : Term σ) :
    Application witness (closures arrows bound) remaining expected ↔
      ∃ arrow ∈ arrows, bound.length < arrow.domains.length ∧
        Unifies witness arrow.conditions ∧
        ChecksVector witness arrow.domains (bound ++ remaining) ∧
        witness.applyTerm arrow.result = witness.applyTerm expected := by
  constructor
  · intro applied
    cases applied with
    | apply member solved tail equal =>
        obtain ⟨arrow, present, mapped⟩ := List.mem_flatMap.mp member
        split at mapped
        · rename_i incomplete
          obtain ⟨equations, equationsMember, rfl⟩ := List.mem_map.mp mapped
          obtain ⟨headSolved, beforeSolved⟩ :=
            (SchematicCallTyping.unifies_append witness _ _).mp solved
          have before := (SchematicCallTyping.vector_iff witness _ _).mp
            ⟨equations,equationsMember,beforeSolved⟩
          exact ⟨arrow,present,incomplete,headSolved,
            (checksVector_split witness _ bound remaining).mpr ⟨before,tail⟩,equal⟩
        · simp at mapped
  · rintro ⟨arrow,present,incomplete,headSolved,checked,equal⟩
    obtain ⟨before,after⟩ := (checksVector_split witness _ bound remaining).mp checked
    obtain ⟨equations,equationsMember,beforeSolved⟩ :=
      (SchematicCallTyping.vector_iff witness _ _).mpr before
    apply Application.apply (arrow :=
      ⟨arrow.domains.drop bound.length,arrow.result,arrow.conditions ++ equations⟩)
    · apply List.mem_flatMap.mpr
      refine ⟨arrow,present,?_⟩
      simp only [incomplete, ↓reduceIte]
      exact List.mem_map.mpr ⟨equations,equationsMember,rfl⟩
    · exact (SchematicCallTyping.unifies_append witness _ _).mpr ⟨headSolved,beforeSolved⟩
    · exact after
    · exact equal

/-- The existing checker receives the result constraint and any later
observations together. No preliminary witness is committed or exported. -/
def obligations (candidates : Candidates σ) (expected : Term σ) : List (Alternative σ) :=
  ((SchematicCallTyping.position (.typed expected) candidates).zipIdx).map
    fun (equations, occurrence) => ⟨occurrence,equations⟩

theorem obligations_exact (candidates : Candidates σ) (expected : Term σ)
    (observations : Equations σ) :
    Joint (obligations candidates expected) observations ↔
      ∃ witness, Checks witness (.typed expected) candidates ∧ Unifies witness observations := by
  constructor
  · rintro ⟨row, member, witness, solved⟩
    obtain ⟨⟨equations, occurrence⟩, indexed, rfl⟩ := List.mem_map.mp member
    have present : equations ∈ SchematicCallTyping.position (.typed expected) candidates :=
      List.fst_mem_of_mem_zipIdx indexed
    obtain ⟨conditions, observed⟩ := (SchematicCallTyping.unifies_append witness _ _).mp solved
    exact ⟨witness, (SchematicCallTyping.position_iff witness _ _).mp
      ⟨equations,present,conditions⟩, observed⟩
  · rintro ⟨witness, checked, observed⟩
    obtain ⟨equations, present, conditions⟩ :=
      (SchematicCallTyping.position_iff witness _ _).mpr checked
    obtain ⟨occurrence, indexed⟩ := List.mem_iff_getElem?.mp present
    refine ⟨⟨occurrence,equations⟩, ?_, witness,
      (SchematicCallTyping.unifies_append witness _ _).mpr ⟨conditions,observed⟩⟩
    exact List.mem_map.mpr ⟨(equations,occurrence),
      List.mk_mem_zipIdx_iff_getElem?.mpr indexed, rfl⟩

theorem application_checker_exact [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (arrows : List (Arrow σ))
    (arguments : List (Candidates σ)) (expected : Term σ) (observations : Equations σ) :
    guard (obligations (applications arrows arguments) expected) observations = true ↔
      ∃ witness, Application witness arrows arguments expected ∧ Unifies witness observations := by
  rw [guard_iff, obligations_exact]
  exact exists_congr fun witness => and_congr_left fun _ =>
    applications_exact witness arrows arguments expected

namespace Controls

abbrev sig := ListTerms.signature String Coordinate
def number : Term sig := .const "Number"
def string : Term sig := .const "String"
def parameter : Term sig := .var (.scheme 0 0)
def subject : Term sig := .var (.observation 0)
def numeric : Arrow sig := ⟨[.typed number],string,[]⟩
def repeated : Arrow sig := ⟨[.typed parameter,.typed parameter],parameter,[]⟩

theorem valid_application :
    guard (obligations (applications [numeric] [[.plain number]]) string) [] = true := by
  rw [application_checker_exact (σ := sig)]
  refine ⟨Subst.id sig, ?_, by simp [Unifies]⟩
  exact .apply (arrow := numeric) (by simp) (by simp [numeric,Unifies])
    (.cons ((intrinsic_exact _ number number).mpr rfl) .nil) rfl

theorem invalid_application :
    guard (obligations (applications [numeric] [[.plain string]]) string) [] = false := by
  rw [rejected_iff (σ := sig), obligations_exact]
  rintro ⟨witness, checked, _⟩
  have applied := (applications_exact witness _ _ _).mp checked
  cases applied with
  | apply member _ arguments _ =>
      simp only [List.mem_singleton] at member
      subst_vars
      cases arguments with
      | cons head _ =>
          have impossible := (intrinsic_exact witness string number).mp head
          simp [number,string] at impossible

def arrowSyntax : Term sig := ListTerms.ofList [.const "->",number,string]

/-- Invalid application syntax can still have an exact structural type. -/
theorem data_description_does_not_authorize_application :
    Checks (Subst.id sig) (.typed (ListTerms.ofList [arrowSyntax,string]))
      (tuples [[.plain arrowSyntax],[.plain string]]) ∧
    guard (obligations (applications [numeric] [[.plain string]]) string) [] = false := by
  refine ⟨(tuples_exact _ _ _).mpr ?_, invalid_application⟩
  exact .tuple [arrowSyntax,string]
    (.cons ((intrinsic_exact _ _ _).mpr rfl)
      (.cons ((intrinsic_exact _ _ _).mpr rfl) .nil))
    (by simp [Subst.applyTerm_id])

def conditional : Arrow sig := { numeric with conditions := [(subject,.const "a")] }

theorem ground_result_retains_head_condition :
    guard (obligations (applications [conditional] [[.plain number]]) string)
      [(subject,.const "b")] = false := by
  rw [rejected_iff (σ := sig), obligations_exact]
  rintro ⟨witness, checked, observed⟩
  have applied := (applications_exact witness _ _ _).mp checked
  cases applied with
  | apply member conditions _ _ =>
      simp only [List.mem_singleton] at member
      subst_vars
      have earlier := conditions (subject,.const "a") (by simp [conditional])
      have later := observed (subject,.const "b") (by simp)
      have impossible := earlier.symm.trans later
      simp [Subst.applyTerm] at impossible

theorem compatible_head_condition :
    guard (obligations (applications [conditional] [[.plain number]]) string)
      [(subject,.const "a")] = true := by
  rw [application_checker_exact (σ := sig)]
  let witness : Subst sig := Subst.single (.observation 0) (.const "a")
  have solved : Unifies witness [(subject,.const "a")] := by
    simp [Unifies,witness,subject,Subst.applyTerm,Subst.single]
  exact ⟨witness, .apply (arrow := conditional) (by simp) solved
    (.cons ((intrinsic_exact witness number number).mpr rfl) .nil) rfl, solved⟩

theorem erasing_head_conditions_is_unsound :
    guard (obligations (applications [conditional] [[.plain number]]) string)
      [(subject,.const "b")] = false ∧
    guard (obligations (applications [numeric] [[.plain number]]) string)
      [(subject,.const "b")] = true := by
  refine ⟨ground_result_retains_head_condition, ?_⟩
  rw [application_checker_exact (σ := sig)]
  let witness : Subst sig := Subst.single (.observation 0) (.const "b")
  refine ⟨witness, .apply (arrow := numeric) (by simp) (by simp [numeric,Unifies])
    (.cons ((intrinsic_exact witness number number).mpr rfl) .nil) rfl, ?_⟩
  simp [Unifies,witness,subject,Subst.applyTerm,Subst.single]

/-- No substitution can give the two bound occurrences inconsistent types. -/
theorem closure_conflicting_arguments :
    guard (obligations (applications (closures [repeated] [[.plain number]])
      [[.plain string]]) number) [] = false := by
  rw [rejected_iff (σ := sig), obligations_exact]
  rintro ⟨witness, checked, _⟩
  have applied := (applications_exact witness _ _ _).mp checked
  obtain ⟨arrow,member,_,_,arguments,_⟩ :=
    (closure_application_exact _ _ _ _ _).mp applied
  simp only [List.mem_singleton] at member
  subst_vars
  cases arguments with
  | cons first rest =>
      cases rest with
      | cons second _ =>
          have left := (intrinsic_exact witness number parameter).mp first
          have right := (intrinsic_exact witness string parameter).mp second
          have impossible := left.trans right.symm
          simp [number,string] at impossible

theorem closure_compatible_arguments :
    guard (obligations (applications (closures [repeated] [[.plain number]])
      [[.plain number]]) number) [] = true := by
  rw [application_checker_exact (σ := sig)]
  let witness : Subst sig := Subst.single (.scheme 0 0) number
  have typed : Checks witness (.typed parameter) [.plain number] := by
    apply (intrinsic_exact witness number parameter).mpr
    simp [witness,number,parameter,Subst.single]
  refine ⟨witness, (closure_application_exact _ _ _ _ _).mpr
    ⟨repeated,by simp,by decide,by simp [repeated,Unifies],
      .cons typed (.cons typed .nil),?_⟩, by simp [Unifies]⟩
  simp [repeated,witness,parameter,number,Subst.single]

theorem structural_order_and_occurrences :
    (tuples [[.plain number,.plain string,.plain number],
      [.plain (.const "Bool"),.plain (.const "Symbol")]]).map Candidate.type =
    ([ [number,.const "Bool"], [number,.const "Symbol"],
       [string,.const "Bool"], [string,.const "Symbol"],
       [number,.const "Bool"], [number,.const "Symbol"] ].map ListTerms.ofList) := rfl

end Controls

#print axioms selection_exact
#print axioms tuples_exact
#print axioms applications_exact
#print axioms application_checker_exact
#print axioms closure_application_exact
#print axioms Controls.data_description_does_not_authorize_application
#print axioms Controls.ground_result_retains_head_condition
#print axioms Controls.compatible_head_condition
#print axioms Controls.erasing_head_conditions_is_unsound
#print axioms Controls.closure_conflicting_arguments
#print axioms Controls.closure_compatible_arguments

end Mettapedia.Languages.MeTTa.PeTTa.SynthesisCandidateComposition
