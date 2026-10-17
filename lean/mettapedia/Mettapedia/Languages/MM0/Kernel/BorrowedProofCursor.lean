import Mettapedia.Languages.MM0.Kernel.ProofChecking
import Mettapedia.Machines.Cursor.ProofChecking

/-!
# Local MM0 inferences on the shared proof cursor

The source judgment is the existing semantic kernel's derivability relation.
Local graph nodes cite a hypothesis index, a theorem index with simultaneous
substitution images, or finite typed conversion evidence. Theorem application
checks the actual ordered cached parents against the instantiated hypotheses;
conversion requires one cached parent equal to its computed left endpoint.
No local rule hides a recursive proof witness in a zero-premise request.

The index contains the actual term signature, definitions, theorem signature,
context and local hypotheses. Their admission as well-formed declarations and
statements remains the existing separate theory-admission obligation. The
shared cursor checks a supplied finite proof graph, without proof search or
binary serialization. This semantic term profile does not replace MMB's
allocation-sensitive Save/Ref equality or qualify every byte proof format.
Conversion, substitution, support and fresh-dummy checks retain their original
computational work; one graph node is not a constant-cost MM0 instruction.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel.BorrowedProofCursor

open Mettapedia.Logic.DerivationGraph
open Mettapedia.Logic.DerivationGraph.BorrowedCursor

structure Scope where
  signature : TermSignature
  definitions : Definition.Signature
  theorems : TheoremSignature
  context : Context
  hypotheses : List Preterm

/-- Original local inference meaning, before choosing any executable witness.
The premise list keeps the theorem declaration's order and repeated entries. -/
inductive Rules (scope : Scope) : List Preterm → Preterm → Prop where
  | hypothesis {index : Nat} {expression : Preterm} :
      scope.hypotheses[index]? = some expression → Rules scope [] expression
  | theoremApp {index : Nat} {declaration : TheoremDecl} {arguments : List Preterm}
      {instantiation : TheoremInstance} :
      scope.theorems index = some declaration →
      TheoremDecl.Instantiates scope.signature scope.context declaration arguments instantiation →
      Rules scope instantiation.hypotheses instantiation.conclusion
  | conversion {left right : Preterm} {sort : Nat} :
      Converts scope.signature scope.definitions scope.context left right sort →
      Rules scope [left] right

inductive Witness where
  | hypothesis (index : Nat)
  | theoremApp (index : Nat) (arguments : List Preterm)
  | conversion (evidence : ConvWitness)
  deriving Repr

def isInstance (scope : Scope) : Witness → List Preterm → Preterm → Bool
  | .hypothesis index, premises, conclusion =>
      decide (premises = [] ∧ scope.hypotheses[index]? = some conclusion)
  | .theoremApp index arguments, premises, conclusion =>
      match scope.theorems index with
      | none => false
      | some declaration => decide (declaration.instantiate? scope.signature scope.context arguments =
          some ⟨premises, conclusion⟩)
  | .conversion evidence, premises, conclusion =>
      match evidence.conversion? scope.signature scope.definitions scope.context with
      | none => false
      | some result => decide (premises = [result.left] ∧ conclusion = result.right)

theorem hypothesis_exact (scope : Scope) (index : Nat) (premises : List Preterm)
    (conclusion : Preterm) :
    isInstance scope (.hypothesis index) premises conclusion = true ↔
      premises = [] ∧ scope.hypotheses[index]? = some conclusion := by
  simp [isInstance]

/-- Admission computes the supplied substitution with the original dependency,
typing and arity checks, then compares the actual ordered premise vector. -/
theorem theoremApp_exact (scope : Scope) (index : Nat) (arguments premises : List Preterm)
    (conclusion : Preterm) :
    isInstance scope (.theoremApp index arguments) premises conclusion = true ↔
      ∃ declaration, scope.theorems index = some declaration ∧
        TheoremDecl.Instantiates scope.signature scope.context declaration arguments
          ⟨premises, conclusion⟩ := by
  cases known : scope.theorems index <;>
    simp [isInstance, known, TheoremDecl.instantiate_eq_some_iff]

/-- The one proof parent must be exactly the computed conversion source.
Typing, unfolding and fresh-dummy obligations remain in the original checker. -/
theorem conversion_exact (scope : Scope) (evidence : ConvWitness) (premises : List Preterm)
    (conclusion : Preterm) :
    isInstance scope (.conversion evidence) premises conclusion = true ↔
      ∃ result, evidence.conversion? scope.signature scope.definitions scope.context = some result ∧
        premises = [result.left] ∧ conclusion = result.right := by
  cases computed : evidence.conversion? scope.signature scope.definitions scope.context <;>
    simp [isInstance, computed]

def interface (scope : Scope) : Mettapedia.Logic.RuleWitness (Rules scope) where
  W := Witness
  isInstance := isInstance scope
  sound witness premises conclusion accepted := by
    cases witness with
    | hypothesis index =>
        obtain ⟨rfl, found⟩ := (hypothesis_exact scope index premises conclusion).mp accepted
        exact .hypothesis found
    | theoremApp index arguments =>
        obtain ⟨declaration, known, instantiated⟩ :=
          (theoremApp_exact scope index arguments premises conclusion).mp accepted
        exact .theoremApp known instantiated
    | conversion evidence =>
        obtain ⟨result, computed, rfl, rfl⟩ :=
          (conversion_exact scope evidence premises conclusion).mp accepted
        exact .conversion (ConvWitness.conversion_sound computed).derives
  complete premises conclusion rule := by
    cases rule with
    | @hypothesis index _expression found =>
        exact ⟨.hypothesis index, (hypothesis_exact scope index [] conclusion).mpr ⟨rfl, found⟩⟩
    | @theoremApp index declaration arguments instantiation known instantiated =>
        exact ⟨.theoremApp index arguments,
          (theoremApp_exact scope index arguments instantiation.hypotheses instantiation.conclusion).mpr
            ⟨declaration, known, instantiated⟩⟩
    | @conversion left _right sort converted =>
        obtain ⟨evidence, checked⟩ := converted.certificate_exists
        exact ⟨.conversion evidence, (conversion_exact scope evidence [left] conclusion).mpr
          ⟨⟨left, conclusion, sort⟩, checked.eval, rfl, rfl⟩⟩

theorem rule_admission_exact (scope : Scope) (premises : List Preterm) (conclusion : Preterm) :
    (∃ witness, isInstance scope witness premises conclusion = true) ↔ Rules scope premises conclusion :=
  ⟨fun ⟨witness, accepted⟩ => (interface scope).sound witness premises conclusion accepted,
    (interface scope).complete premises conclusion⟩

theorem derives_iff_original (scope : Scope) (expression : Preterm) :
    Mettapedia.Logic.Derives (Rules scope) expression ↔
      Kernel.Derives scope.signature scope.definitions scope.theorems scope.context scope.hypotheses
        expression := by
  constructor
  · intro derived
    apply Mettapedia.Logic.Derives.least
      (Kernel.Derives scope.signature scope.definitions scope.theorems scope.context scope.hypotheses)
      _ derived
    intro premises conclusion rule earlier
    cases rule with
    | hypothesis found => exact .hypothesis (List.mem_of_getElem? found)
    | theoremApp known instantiated =>
        exact .theoremApp known instantiated ((derivesList_iff _ _ _ _ _ _).mpr earlier)
    | @conversion left right sort converted =>
        exact .conversion converted (earlier left (by simp))
  · intro derived
    induction derived using Kernel.Derives.rec
        (motive_2 := fun expressions _ =>
          ∀ expression ∈ expressions, Mettapedia.Logic.Derives (Rules scope) expression) with
    | hypothesis present =>
        obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp present
        exact .node [] _ (.hypothesis found) (by simp)
    | theoremApp known instantiated _ earlier =>
        exact .node _ _ (.theoremApp known instantiated) earlier
    | conversion converted _ earlier =>
        exact .node _ _ (.conversion converted) (by
          intro expression present
          have same := List.mem_singleton.mp present
          simpa only [same] using earlier)
    | nil => rename_i expression present; cases present
    | cons _ _ first rest =>
        rename_i expression present
        rcases List.mem_cons.mp present with rfl | later
        · exact first
        · exact rest expression later

abbrev Source := Store Preterm Witness Nat
abbrev SourceNode := StoredNode Preterm Witness Nat
abbrev Cursor (scope : Scope) (source : Source) := CheckedCursor (interface scope) source

def begin (scope : Scope) (source : Source) : Cursor scope source :=
  CheckedCursor.begin (interface scope) source

theorem original_iff_graph (scope : Scope) (expression : Preterm) :
    Kernel.Derives scope.signature scope.definitions scope.theorems scope.context scope.hypotheses
      expression ↔
      ∃ (nodes : List (Node Preterm Witness Nat)) (cache : Array Preterm) (root : Nat),
        replay (interface scope) nodes = some cache ∧ cache[root]? = some expression := by
  rw [← derives_iff_original]
  exact derives_iff_checked_graph (interface scope) (0 : Nat) expression

theorem stored_root_original (scope : Scope) (source : Source) (schedule : List Nat)
    (result : State Preterm)
    (accepted : run (interface scope) source (start source) schedule = some result)
    (address : Nat) (expression : Preterm) (found : rootAt result address = some expression) :
    Kernel.Derives scope.signature scope.definitions scope.theorems scope.context scope.hypotheses
      expression :=
  (derives_iff_original scope expression).mp
    (root_derivable (interface scope) source schedule result accepted address expression found)

theorem checked_root_original (scope : Scope) {source : Source} (cursor : Cursor scope source)
    (address : Nat) (expression : Preterm)
    (found : (cursor.root address).map CheckedJudgment.judgment = some expression) :
    Kernel.Derives scope.signature scope.definitions scope.theorems scope.context scope.hypotheses
      expression := by
  obtain ⟨evidence, _checked, same⟩ := Option.map_eq_some_iff.mp found
  exact same ▸ (derives_iff_original scope evidence.judgment).mp evidence.valid

theorem worker_root_original (scope : Scope) (source : Source) (schedule : List Nat) (fuel : Nat)
    (report : Mettapedia.Machines.Cursor.ProofChecking.Report (interface scope) source)
    (completed : Mettapedia.Machines.OutcomeRunner.run
      (Mettapedia.Machines.Cursor.ProofChecking.machine (interface scope) source) fuel
      (Mettapedia.Machines.Cursor.ProofChecking.start (begin scope source) schedule) = .finished report)
    (accepted : report.accepted = true) (address : Nat) (expression : Preterm)
    (found : (report.work.cursor.root address).map CheckedJudgment.judgment = some expression) :
    Kernel.Derives scope.signature scope.definitions scope.theorems scope.context scope.hypotheses
      expression ∧ report.work.pending = [] ∧ report.work.accepted = schedule.length := by
  have meaning := Mettapedia.Machines.Cursor.ProofChecking.check_only_report_meaning
    (interface scope) source (begin scope source) schedule fuel report completed
  have observed : Mettapedia.Machines.Cursor.ProofChecking.verdict report.work = some true := by
    simpa [accepted] using report.valid
  obtain ⟨empty, count, _executed⟩ := Mettapedia.Machines.Cursor.ProofChecking.completed_run
    (interface scope) source (begin scope source) schedule report.work meaning observed
  exact ⟨checked_root_original scope report.work.cursor address expression found, empty, count⟩

namespace Controls

open Preterm

private def signature : TermSignature
  | 0 => some ⟨[.regular 1 ∅, .regular 1 ∅], 1, ∅⟩
  | 1 => some ⟨[.regular 1 ∅], 1, ∅⟩
  | 2 => some ⟨[], 1, ∅⟩
  | 3 => some ⟨[.bound 0], 1, {0}⟩
  | 4 => some ⟨[.bound 0, .regular 1 {0}], 1, ∅⟩
  | 5 => some ⟨[.bound 0, .regular 1 {0}], 1, ∅⟩
  | _ => none

private def definitions : Definition.Signature
  | 1 => some ⟨[], .var 0⟩
  | 5 => some ⟨[0], applyArgs (.term 4)
      [.var 2, applyArgs (.term 4) [.var 0, .var 1]]⟩
  | _ => none

private def context : Context :=
  [.regular 1 ∅, .regular 1 ∅, .bound 0, .regular 1 {2}, .bound 0]

private def implies (first second : Preterm) : Preterm := applyArgs (.term 0) [first, second]
private def theorems : TheoremSignature
  | 0 => some ⟨[.regular 1 ∅, .regular 1 ∅], [.var 0, implies (.var 0) (.var 1)], .var 1⟩
  | 1 => some ⟨[.regular 1 ∅], [.var 0, .var 0], .var 0⟩
  | 2 => some ⟨[.bound 0, .regular 1 ∅], [], .term 2⟩
  | _ => none

private def scope : Scope :=
  ⟨signature, definitions, theorems, context, [.var 0, implies (.var 0) (.var 1)]⟩

private def dummyCall : Preterm := applyArgs (.term 5) [.var 2, .var 3]
private def dummyResult : Preterm := applyArgs (.term 4)
  [.var 4, applyArgs (.term 4) [.var 2, .var 3]]

private def dummyScope : Scope := { scope with hypotheses := [dummyCall] }

private def dummyStore : Source := ⟨2, fun address => match address with
  | 80 => some ⟨dummyCall, .hypothesis 0, [], 80⟩
  | 90 => some ⟨dummyResult, .conversion (.unfold 5 [.var 2, .var 3] [4]), [80], 90⟩
  | 91 => some ⟨dummyResult, .conversion (.unfold 5 [.var 2, .var 3] [2]), [80], 91⟩
  | _ => none⟩

private def store : Source := ⟨1, fun address => match address with
  | 10 => some ⟨.var 0, .hypothesis 0, [], 10⟩
  | 11 => some ⟨implies (.var 0) (.var 1), .hypothesis 1, [], 11⟩
  | 20 => some ⟨.var 1, .theoremApp 0 [.var 0, .var 1], [10, 11], 20⟩
  | 30 => some ⟨.var 0, .theoremApp 1 [.var 0], [10, 10], 30⟩
  | 40 => some ⟨.app (.term 1) (.var 0), .conversion (.symm (.unfold 1 [.var 0] [])), [10], 40⟩
  | 50 => some ⟨.term 2, .theoremApp 2 [.var 2, .var 0], [], 50⟩
  | 60 => some ⟨.term 2, .theoremApp 2 [.var 2, .var 3], [], 60⟩
  | 70 => some ⟨.var 1, .conversion (.refl (.var 1)), [10], 70⟩
  | _ => none⟩

private def checkedRoot (s : Scope) (source : Source) (schedule : List Nat)
    (address : Nat) : Option Preterm := do
  let cursor ← (begin s source).advance schedule
  let checked ← cursor.root address
  pure checked.judgment

private def workerVerdict (s : Scope) (source : Source) (schedule : List Nat) (fuel : Nat) : Option Bool :=
  Mettapedia.Machines.Cursor.ProofChecking.completedVerdict
    (Mettapedia.Machines.OutcomeRunner.run
      (Mettapedia.Machines.Cursor.ProofChecking.machine (interface s) source) fuel
      (Mettapedia.Machines.Cursor.ProofChecking.start (begin s source) schedule))

theorem modus_ponens_source_graph_accepts :
    checkedRoot scope store [10, 11, 20] 20 = some (.var 1) := by decide +kernel

theorem shared_worker_accepts_the_complete_graph :
    workerVerdict scope store [10, 11, 20, 30, 40, 50] 8 = some true := by decide +kernel

theorem repeated_hypotheses_use_two_actual_edges :
    checkedRoot scope store [10, 30] 30 = some (.var 0) ∧
      isInstance scope (.theoremApp 1 [.var 0]) [.var 0] (.var 0) = false := by decide +kernel

theorem ordered_hypotheses_cannot_be_reversed :
    isInstance scope (.theoremApp 0 [.var 0, .var 1])
      [implies (.var 0) (.var 1), .var 0] (.var 1) = false := by decide +kernel

theorem unproved_parent_refused : checkedRoot scope store [20] 20 = none := by decide +kernel

theorem hypothesis_index_and_empty_parents_are_checked :
    isInstance scope (.hypothesis 0) [] (.var 1) = false ∧
      isInstance scope (.hypothesis 2) [] (.var 0) = false ∧
      isInstance scope (.hypothesis 0) [.var 0] (.var 0) = false := by decide +kernel

theorem independent_substitution_accepts :
    checkedRoot scope store [50] 50 = some (.term 2) := by decide +kernel

theorem dependent_target_substitution_refused :
    checkedRoot scope store [60] 60 = none ∧
      workerVerdict scope store [10, 60, 11] 5 = some false := by decide +kernel

theorem bound_slot_occurrence_is_not_hidden :
    isInstance scope (.theoremApp 2 [.var 2, .app (.term 3) (.var 2)]) [] (.term 2) = false :=
  by decide +kernel

theorem conversion_uses_its_actual_proof_parent :
    checkedRoot scope store [10, 40] 40 = some (.app (.term 1) (.var 0)) ∧
      checkedRoot scope store [10, 70] 70 = none := by decide +kernel

theorem fresh_dummy_conversion_checks_a_stored_proof :
    checkedRoot dummyScope dummyStore [80, 90] 90 = some dummyResult := by decide +kernel

theorem capturing_dummy_cannot_reuse_the_same_proof_parent :
    checkedRoot dummyScope dummyStore [80, 91] 91 = none := by decide +kernel

theorem changed_hypotheses_do_not_relabel_the_graph :
    checkedRoot { scope with hypotheses := [.var 1] } store [10] 10 = none := by decide +kernel

theorem changed_definition_refuses_original_conversion :
    checkedRoot { scope with definitions := fun _ => none } store [10, 40] 40 = none := by decide +kernel

theorem foreign_same_theorem_index_does_not_rescue_original_parents :
    isInstance { scope with theorems := fun _ => some ⟨[], [], .term 2⟩ }
      (.theoremApp 0 [.var 0, .var 1]) [.var 0, implies (.var 0) (.var 1)] (.var 1) = false :=
  by decide +kernel

theorem wrong_context_refuses_theorem_substitution :
    checkedRoot { scope with context := [] } store [50] 50 = none := by decide +kernel

end Controls

#print axioms hypothesis_exact
#print axioms theoremApp_exact
#print axioms conversion_exact
#print axioms rule_admission_exact
#print axioms derives_iff_original
#print axioms original_iff_graph
#print axioms stored_root_original
#print axioms checked_root_original
#print axioms worker_root_original
#print axioms Controls.modus_ponens_source_graph_accepts
#print axioms Controls.repeated_hypotheses_use_two_actual_edges
#print axioms Controls.dependent_target_substitution_refused
#print axioms Controls.bound_slot_occurrence_is_not_hidden
#print axioms Controls.conversion_uses_its_actual_proof_parent
#print axioms Controls.fresh_dummy_conversion_checks_a_stored_proof
#print axioms Controls.capturing_dummy_cannot_reuse_the_same_proof_parent

end Mettapedia.Languages.MM0.Kernel.BorrowedProofCursor
