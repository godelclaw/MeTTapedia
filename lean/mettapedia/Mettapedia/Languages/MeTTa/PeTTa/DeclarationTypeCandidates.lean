import Mettapedia.Languages.MeTTa.PeTTa.SchematicCallTyping
import Mettapedia.Logic.LP.IndependentOutputUnification

/-!
# Declaration instances as constrained PeTTa type candidates

A declaration's subject and type share one variable scope. Matching the
subject can constrain the program's open terms as well as the declared type.
Those equations remain part of a candidate, including when its type is
ground. Inputs and result are checked with one witness over all candidates.

`Declared`, `ChecksSource` and `CallTypedSource` state the source rules
independently of candidate construction. `checker_exact` connects declarations
directly to the existing joint checker. `resolved_observations_exact` justifies
solving a subject match early while retaining its effect on every observation.

Declarations supplied to a request are freshly scoped instances. This module
does not establish the SWI reader, its allocation of those scopes, intrinsic
classification, application synthesis, closures or gradual-hole readback.
The source controls are also exercised by the SWI typing constraint tests.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.DeclarationTypeCandidates

open Mettapedia.Logic.LP
open JointSchemeContracts
open SchematicCallTyping (Domain Candidate Candidates Scheme Checks ChecksVector)

variable {σ : LPSignature}

structure Declaration (σ : LPSignature) where
  occurrence : Nat
  subject : Term σ
  type : Term σ

structure Request (σ : LPSignature) where
  subject : Term σ
  declarations : List (Declaration σ)

/-- One instantiation satisfies both sides of the source annotation. -/
inductive Declared (witness : Subst σ) (request : Request σ) (expected : Term σ) : Prop where
  | annotation {declaration : Declaration σ} :
      declaration ∈ request.declarations →
      witness.applyTerm request.subject = witness.applyTerm declaration.subject →
      witness.applyTerm declaration.type = witness.applyTerm expected →
      Declared witness request expected

theorem declared_singleton (witness : Subst σ) (subject : Term σ)
    (declaration : Declaration σ) (expected : Term σ) :
    Declared witness ⟨subject, [declaration]⟩ expected ↔
      witness.applyTerm subject = witness.applyTerm declaration.subject ∧
      witness.applyTerm declaration.type = witness.applyTerm expected := by
  constructor
  · intro declared
    cases declared with
    | annotation member subjectEqual typeEqual =>
        simp only [List.mem_singleton] at member
        subst_vars
        exact ⟨subjectEqual, typeEqual⟩
  · rintro ⟨subjectEqual, typeEqual⟩
    exact .annotation (by simp) subjectEqual typeEqual

def candidate (subject : Term σ) (declaration : Declaration σ) : Candidate σ :=
  ⟨declaration.type, [(subject, declaration.subject)]⟩

/-- Source occurrences stay in order, including equal declarations. A later
joint check rejects incompatible subject matches. -/
def candidates (request : Request σ) : Candidates σ :=
  request.declarations.map (candidate request.subject)

theorem candidates_length (request : Request σ) :
    (candidates request).length = request.declarations.length := by
  simp [candidates]

theorem typed_candidate_exact (witness : Subst σ) (request : Request σ)
    (expected : Term σ) :
    Checks witness (.typed expected) (candidates request) ↔ Declared witness request expected := by
  constructor
  · intro checked
    cases checked with
    | typed member conditions equal =>
        obtain ⟨declaration, present, rfl⟩ := List.mem_map.mp member
        exact .annotation present
          (conditions (request.subject,declaration.subject) (by simp [candidate])) equal
  · intro declared
    cases declared with
    | @annotation declaration member subjectEqual typed =>
        refine Checks.typed (actual := candidate request.subject declaration)
          (List.mem_map.mpr ⟨declaration, member, rfl⟩) ?_ typed
        simpa [candidate, Unifies] using subjectEqual

inductive ChecksSource (witness : Subst σ) : Domain σ → Request σ → Prop where
  | universal (request : Request σ) : ChecksSource witness .universal request
  | typed {pattern : Term σ} {request : Request σ} :
      Declared witness request pattern → ChecksSource witness (.typed pattern) request

inductive ChecksSources (witness : Subst σ) : List (Domain σ) → List (Request σ) → Prop where
  | nil : ChecksSources witness [] []
  | cons {domain : Domain σ} {request : Request σ}
      {domains : List (Domain σ)} {requests : List (Request σ)} :
      ChecksSource witness domain request → ChecksSources witness domains requests →
      ChecksSources witness (domain :: domains) (request :: requests)

theorem check_candidate_exact (witness : Subst σ) (domain : Domain σ) (request : Request σ) :
    Checks witness domain (candidates request) ↔ ChecksSource witness domain request := by
  cases domain with
  | universal => exact ⟨fun _ => .universal request, fun _ => .universal _⟩
  | typed pattern =>
      constructor
      · intro checked
        exact .typed ((typed_candidate_exact witness request pattern).mp checked)
      · intro checked
        cases checked with
        | typed declared => exact (typed_candidate_exact witness request pattern).mpr declared

theorem check_candidates_exact (witness : Subst σ)
    (domains : List (Domain σ)) (requests : List (Request σ)) :
    ChecksVector witness domains (requests.map candidates) ↔ ChecksSources witness domains requests := by
  induction domains generalizing requests with
  | nil =>
      cases requests with
      | nil => exact ⟨fun _ => .nil, fun _ => .nil⟩
      | cons request requests =>
          constructor <;> intro impossible <;> cases impossible
  | cons domain domains ih =>
      cases requests with
      | nil => constructor <;> intro impossible <;> cases impossible
      | cons request requests =>
          constructor
          · intro checked
            cases checked with
            | cons head tail =>
                exact .cons ((check_candidate_exact witness domain request).mp head)
                  ((ih requests).mp tail)
          · intro checked
            cases checked with
            | cons head tail =>
                exact .cons ((check_candidate_exact witness domain request).mpr head)
                  ((ih requests).mpr tail)

inductive CallTypedSource (schemes : List (Scheme σ))
    (inputs : List (Request σ)) (result : Request σ)
    (observations : Equations σ := []) : Prop where
  | call {scheme : Scheme σ} (member : scheme ∈ schemes) (witness : Subst σ) :
      ChecksSources witness scheme.domains inputs → ChecksSource witness scheme.result result →
      Unifies witness observations → CallTypedSource schemes inputs result observations

theorem candidate_call_exact (schemes : List (Scheme σ))
    (inputs : List (Request σ)) (result : Request σ) :
    SchematicCallTyping.CallTyped schemes (inputs.map candidates) (candidates result) ↔
      CallTypedSource schemes inputs result := by
  constructor
  · intro typed
    cases typed with
    | call member witness first last =>
        exact .call member witness ((check_candidates_exact witness _ inputs).mp first)
          ((check_candidate_exact witness _ result).mp last) (by simp [Unifies])
  · intro typed
    cases typed with
    | call member witness first last _ =>
        exact .call member witness ((check_candidates_exact witness _ inputs).mpr first)
          ((check_candidate_exact witness _ result).mpr last)

def compile (schemes : List (Scheme σ)) (inputs : List (Request σ))
    (result : Request σ) : List (Alternative σ) :=
  SchematicCallTyping.compile schemes (inputs.map candidates) (candidates result)

theorem checker_with_observations_exact [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (schemes : List (Scheme σ))
    (inputs : List (Request σ)) (result : Request σ) (observations : Equations σ) :
    guard (compile schemes inputs result) observations = true ↔
      CallTypedSource schemes inputs result observations := by
  rw [guard_iff]
  constructor
  · rintro ⟨row, member, witness, solved⟩
    obtain ⟨scheme, schemeMember, compiled⟩ := List.mem_flatMap.mp member
    obtain ⟨equations, equationsMember, rfl⟩ := List.mem_map.mp compiled
    obtain ⟨conditions, observed⟩ := (SchematicCallTyping.unifies_append witness _ _).mp solved
    have checked := (SchematicCallTyping.vector_iff witness _ _).mp
      ⟨equations, equationsMember, conditions⟩
    obtain ⟨first, last⟩ :=
      (SchematicCallTyping.checksVector_append_singleton witness _ _ _ _).mp checked
    exact .call schemeMember witness ((check_candidates_exact witness _ inputs).mp first)
      ((check_candidate_exact witness _ result).mp last) observed
  · intro typed
    cases typed with
    | call member witness first last observed =>
        have checked := (SchematicCallTyping.checksVector_append_singleton witness _ _ _ _).mpr
          ⟨(check_candidates_exact witness _ inputs).mpr first,
           (check_candidate_exact witness _ result).mpr last⟩
        obtain ⟨equations, equationsMember, conditions⟩ :=
          (SchematicCallTyping.vector_iff witness _ _).mpr checked
        refine ⟨_, List.mem_flatMap.mpr ⟨_, member,
          List.mem_map.mpr ⟨equations, equationsMember, rfl⟩⟩, witness, ?_⟩
        exact (SchematicCallTyping.unifies_append witness _ _).mpr ⟨conditions, observed⟩

theorem checker_exact [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (schemes : List (Scheme σ))
    (inputs : List (Request σ)) (result : Request σ) :
    guard (compile schemes inputs result) [] = true ↔ CallTypedSource schemes inputs result :=
  checker_with_observations_exact schemes inputs result []

theorem checker_rejected_exact [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (schemes : List (Scheme σ))
    (inputs : List (Request σ)) (result : Request σ) (observations : Equations σ) :
    guard (compile schemes inputs result) observations = false ↔
      ¬ CallTypedSource schemes inputs result observations := by
  rw [← checker_with_observations_exact]
  cases guard (compile schemes inputs result) observations <;> simp

section Resolution

variable [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

def resolve (subject : Term σ) (declaration : Declaration σ) : Option (Subst σ) :=
  unifyTotal [(subject, declaration.subject)]

theorem resolution_failure_exact (subject : Term σ) (declaration : Declaration σ) :
    resolve subject declaration = none ↔
      ¬ ∃ witness : Subst σ, witness.applyTerm subject = witness.applyTerm declaration.subject := by
  simpa [resolve, Unifies] using
    (unifyTotal_none_iff_not_unifiable [(subject, declaration.subject)])

/-- Solving the match early must transform both the type and the caller's
observations. This is equality of all later solution families, not only
equality of a printed type or agreement on ground examples. -/
theorem resolved_observations_exact (subject : Term σ) (declaration : Declaration σ)
    (theta : Subst σ) (accepted : resolve subject declaration = some theta)
    (later : Equations σ) (visible : List (Term σ)) :
    IndependentOutputUnification.solutions ([(subject, declaration.subject)] ++ later)
      (subject :: declaration.type :: visible) =
    IndependentOutputUnification.solutions (theta.applyEqs later)
      ((subject :: declaration.type :: visible).map theta.applyTerm) :=
  IndependentOutputUnification.solutions_after_unifyTotal _ later theta accepted _

end Resolution

namespace Controls

abbrev sig : LPSignature where
  constants := String
  vars := Coordinate
  relationSymbols := Unit
  relationArity _ := 0
  functionSymbols := Nat
  functionArity := id

def number : Term sig := .const "Number"
def programVariable : Term sig := .var (.observation 0)
def annotatedA : Declaration sig := ⟨0, .const "a", number⟩
def openSubject : Request sig := ⟨programVariable, [annotatedA]⟩
def ignoredResult : Request sig := ⟨.const "unit", []⟩
def numberCall : Scheme sig := ⟨0, [.typed number], .universal⟩

private theorem number_call_iff (request : Request sig) (observations : Equations sig) :
    CallTypedSource [numberCall] [request] ignoredResult observations ↔
      ∃ witness, Declared witness request number ∧ Unifies witness observations := by
  constructor
  · intro typed
    cases typed with
    | call member witness inputs _ observed =>
        simp only [List.mem_singleton] at member
        subst_vars
        cases inputs with
        | cons first _ =>
            cases first with
            | typed declared => exact ⟨witness, declared, observed⟩
  · rintro ⟨witness, declared, observed⟩
    exact .call (scheme := numberCall) (by simp) witness
      (.cons (.typed declared) .nil) (.universal ignoredResult) observed

theorem matching_later_binding :
    guard (compile [numberCall] [openSubject] ignoredResult)
      [(programVariable, .const "a")] = true := by
  rw [checker_with_observations_exact (σ := sig), number_call_iff]
  refine ⟨Subst.single (.observation 0) (.const "a"), ?_, ?_⟩
  · apply (declared_singleton _ _ _ _).mpr
    simp [programVariable,annotatedA,Subst.single]
  · simp [Unifies,programVariable,Subst.applyTerm,Subst.single]

theorem conflicting_later_binding :
    guard (compile [numberCall] [openSubject] ignoredResult)
      [(programVariable, .const "b")] = false := by
  rw [checker_rejected_exact (σ := sig), number_call_iff]
  rintro ⟨witness, declared, observed⟩
  have subjectEqual := ((declared_singleton witness _ _ _).mp declared).1
  have later := observed (programVariable,.const "b") (by simp)
  have impossible := subjectEqual.symm.trans later
  simp [annotatedA,Subst.applyTerm] at impossible

/-- The visible type is Number in both candidates. Only the source condition
distinguishes the invalid subject from an unconditional Number candidate. -/
theorem erasing_source_conditions_is_unsound :
    guard (compile [numberCall] [⟨.const "b", [annotatedA]⟩] ignoredResult) [] = false ∧
    guard (SchematicCallTyping.compile [numberCall] [[.plain number]] []) [] = true := by
  constructor
  · rw [checker_rejected_exact (σ := sig), number_call_iff]
    rintro ⟨witness, declared, _⟩
    have impossible := ((declared_singleton witness _ _ _).mp declared).1
    simp [annotatedA,Subst.applyTerm] at impossible
  · apply (SchematicCallTyping.checker_exact (σ := sig) _ _ _).mpr
    have checked : Checks (Subst.id sig) (.typed number) [.plain number] :=
      .typed (actual := .plain number) (by simp) (by simp [Candidate.plain,Unifies]) rfl
    exact .call (scheme := numberCall) (by simp) (Subst.id sig)
      (.cons checked .nil) (.universal [])

def subjectTypeShared : Declaration sig :=
  ⟨0, .var (.scheme 0 0), .var (.scheme 0 0)⟩

theorem subject_type_sharing_is_retained :
    guard (compile [numberCall] [⟨number, [subjectTypeShared]⟩] ignoredResult) [] = true ∧
    guard (compile [numberCall] [⟨.const "String", [subjectTypeShared]⟩] ignoredResult) [] = false := by
  constructor
  · rw [checker_exact (σ := sig), number_call_iff]
    refine ⟨Subst.single (.scheme 0 0) number, ?_, by simp [Unifies]⟩
    apply (declared_singleton _ _ _ _).mpr
    simp [number,subjectTypeShared,Subst.single]
  · rw [checker_rejected_exact (σ := sig), number_call_iff]
    rintro ⟨witness, declared, _⟩
    obtain ⟨subjectEqual, typeEqual⟩ := (declared_singleton witness _ _ _).mp declared
    have impossible := subjectEqual.trans typeEqual
    simp [number,Subst.applyTerm] at impossible

theorem declaration_occurrences_are_retained :
    (candidates ⟨.const "a", [annotatedA, {annotatedA with occurrence := 1}]⟩).length = 2 :=
  candidates_length _

end Controls

#print axioms typed_candidate_exact
#print axioms candidate_call_exact
#print axioms checker_exact
#print axioms checker_with_observations_exact
#print axioms resolution_failure_exact
#print axioms resolved_observations_exact
#print axioms Controls.matching_later_binding
#print axioms Controls.conflicting_later_binding
#print axioms Controls.erasing_source_conditions_is_unsound
#print axioms Controls.subject_type_sharing_is_retained

end Mettapedia.Languages.MeTTa.PeTTa.DeclarationTypeCandidates
