import Mettapedia.GSLT.LanguageDef.RegexSelectionLowering
import Mettapedia.Computability.RegularLanguages.RegexSelectionCorrespondence

/-!+# The actual symbolic regex program as a finite tagged graph

Owned states are actual emitted definition addresses. The compiler's closed
targets and unique definitions justify instruction interpretation; no parser,
second pattern compiler, or implicit repair of missing targets is involved.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexSelection.Graph

open Mettapedia.Computability.RegularLanguages

theorem emit_entry_present (pattern : Pattern) (continuation address : Address) :
    address ∈ (emit pattern continuation address).map Instruction.address := by
  have member := List.mem_of_find?_eq_some (emit_entry_lookup pattern continuation address)
  apply List.mem_map.mpr
  refine ⟨entryInstruction pattern continuation address, member, ?_⟩
  cases pattern <;> simp [entryInstruction, Instruction.address]
  all_goals rename_i body greedy; cases greedy <;> simp [choice]

/-- Every target is either the fragment's continuation or another actual
definition. Merely belonging to the containing address subtree is insufficient. -/
theorem emit_targets_defined_or_continuation (pattern : Pattern) (continuation address : Address)
    (instruction : Instruction) (member : instruction ∈ emit pattern continuation address)
    (target : Address) (edge : target ∈ instruction.targets) :
    target = continuation ∨ target ∈ (emit pattern continuation address).map Instruction.address := by
  induction pattern generalizing continuation address instruction target with
  | zero | epsilon | literal _ | any | class_ _ | assertion _ =>
      simp only [emit, List.mem_singleton] at member
      subst instruction
      simp_all [Instruction.targets]
  | seq first second ihFirst ihSecond =>
      have firstDefined := emit_entry_present first (.right address) (.left address)
      have secondDefined := emit_entry_present second continuation (.right address)
      simp only [emit, List.mem_cons, List.mem_append] at member
      rcases member with same | member | member
      · subst instruction
        simp only [Instruction.targets, List.mem_singleton] at edge
        subst target
        exact Or.inr (by simp [emit, Instruction.address, firstDefined])
      · rcases ihFirst _ _ _ member _ edge with same | defined
        · subst target; exact Or.inr (by simp [emit, Instruction.address, secondDefined])
        · exact Or.inr (by simp [emit, Instruction.address, defined])
      · rcases ihSecond _ _ _ member _ edge with same | defined
        · exact Or.inl same
        · exact Or.inr (by simp [emit, Instruction.address, defined])
  | alt first second ihFirst ihSecond =>
      have firstDefined := emit_entry_present first continuation (.left address)
      have secondDefined := emit_entry_present second continuation (.right address)
      simp only [emit, List.mem_cons, List.mem_append] at member
      rcases member with same | member | member
      · subst instruction
        simp only [Instruction.targets, List.mem_cons, List.not_mem_nil, or_false] at edge
        rcases edge with same | same <;> subst target
        · exact Or.inr (by simp [emit, Instruction.address, firstDefined])
        · exact Or.inr (by simp [emit, Instruction.address, secondDefined])
      · rcases ihFirst _ _ _ member _ edge with same | defined
        · exact Or.inl same
        · exact Or.inr (by simp [emit, Instruction.address, defined])
      · rcases ihSecond _ _ _ member _ edge with same | defined
        · exact Or.inl same
        · exact Or.inr (by simp [emit, Instruction.address, defined])
  | optional body greedy ih =>
      have bodyDefined := emit_entry_present body continuation (.body address)
      simp only [emit, List.mem_cons] at member
      rcases member with same | member
      · subst instruction
        cases greedy <;> simp only [choice, Bool.false_eq_true, if_false, if_true,
          Instruction.targets, List.mem_cons, List.not_mem_nil, or_false] at edge
        all_goals rcases edge with same | same <;> subst target
        all_goals first | exact Or.inl rfl | exact Or.inr (by simp [emit, Instruction.address, bodyDefined])
      · rcases ih _ _ _ member _ edge with same | defined
        · exact Or.inl same
        · exact Or.inr (by simp [emit, Instruction.address, defined])
  | star body greedy ih =>
      have bodyDefined := emit_entry_present body (.loop address) (.body address)
      simp only [emit, List.mem_cons] at member
      rcases member with same | same | member
      · subst instruction
        cases greedy <;> simp only [choice, Bool.false_eq_true, if_false, if_true,
          Instruction.targets, List.mem_cons, List.not_mem_nil, or_false] at edge
        all_goals rcases edge with same | same <;> subst target
        all_goals first | exact Or.inl rfl | exact Or.inr (by simp [emit, Instruction.address, bodyDefined])
      · subst instruction
        cases greedy <;> simp only [choice, Bool.false_eq_true, if_false, if_true,
          Instruction.targets, List.mem_cons, List.not_mem_nil, or_false] at edge
        all_goals rcases edge with same | same <;> subst target
        all_goals first | exact Or.inl rfl | exact Or.inr (by simp [emit, Instruction.address, bodyDefined])
      · rcases ih _ _ _ member _ edge with same | defined
        · subst target
          exact Or.inr (by cases greedy <;> simp [emit, choice, Instruction.address])
        · exact Or.inr (by simp [emit, Instruction.address, defined])
  | plus body greedy ih =>
      have bodyDefined := emit_entry_present body (.loop address) (.body address)
      simp only [emit, List.mem_cons] at member
      rcases member with same | same | member
      · subst instruction
        simp only [Instruction.targets, List.mem_singleton] at edge
        subst target
        exact Or.inr (by simp [emit, Instruction.address, bodyDefined])
      · subst instruction
        cases greedy <;> simp only [choice, Bool.false_eq_true, if_false, if_true,
          Instruction.targets, List.mem_cons, List.not_mem_nil, or_false] at edge
        all_goals rcases edge with same | same <;> subst target
        all_goals first | exact Or.inl rfl | exact Or.inr (by simp [emit, Instruction.address, bodyDefined])
      · rcases ih _ _ _ member _ edge with same | defined
        · subst target
          exact Or.inr (by cases greedy <;> simp [emit, choice, Instruction.address])
        · exact Or.inr (by simp [emit, Instruction.address, defined])
  | capture group body ih =>
      have bodyDefined := emit_entry_present body (.close address) (.body address)
      simp only [emit, List.mem_cons] at member
      rcases member with same | same | member
      · subst instruction
        simp only [Instruction.targets, List.mem_singleton] at edge
        subst target
        exact Or.inr (by simp [emit, Instruction.address, bodyDefined])
      · subst instruction
        simp only [Instruction.targets, List.mem_singleton] at edge
        exact Or.inl edge
      · rcases ih _ _ _ member _ edge with same | defined
        · subst target
          exact Or.inr (by simp [emit, Instruction.address])
        · exact Or.inr (by simp [emit, Instruction.address, defined])

def addresses (program : Program) : Finset Address := (program.rows.map Instruction.address).toFinset

abbrev Owned (program : Program) := {address // address ∈ addresses program}

instance (program : Program) : Fintype (Owned program) := inferInstance

theorem compile_entry_owned (pattern : Pattern) : (compile pattern).entry ∈ addresses (compile pattern) := by
  simp only [compile, addresses, List.map_cons, Instruction.address, List.mem_toFinset, List.mem_cons]
  exact Or.inr (emit_entry_present pattern .ending .root)

theorem compile_targets_owned (pattern : Pattern) (row : Instruction)
    (member : row ∈ (compile pattern).rows) (target : Address) (edge : target ∈ row.targets) :
    target ∈ addresses (compile pattern) := by
  simp only [compile, List.mem_cons] at member
  rcases member with same | member
  · subst row; simp [Instruction.targets] at edge
  · rcases emit_targets_defined_or_continuation pattern .ending .root row member target edge with same | defined
    · subst target; simp [addresses, compile, Instruction.address]
    · simp [addresses, compile, Instruction.address, defined]

theorem compile_addresses_nodup (pattern : Pattern) :
    ((compile pattern).rows.map Instruction.address).Nodup := by
  have outside : ¬ Within .root .ending := by intro inside; cases inside
  have absent := not_owned_cannot_be_defined pattern .ending .root .ending outside
  simp only [compile, List.map_cons, Instruction.address, List.nodup_cons]
  refine ⟨?_, emit_addresses_nodup pattern .ending .root⟩
  intro member
  obtain ⟨row, member, same⟩ := List.mem_map.mp member
  exact absent ⟨row, member, same⟩

theorem owned_card (program : Program) (unique : (program.rows.map Instruction.address).Nodup) :
    Fintype.card (Owned program) = program.rows.length := by
  change Fintype.card ↥(addresses program) = program.rows.length
  rw [Fintype.card_coe]
  simp only [addresses, List.toFinset_card_of_nodup unique, List.length_map]

structure CheckedProgram where
  program : Program
  unique : (program.rows.map Instruction.address).Nodup
  entryOwned : program.entry ∈ addresses program
  targetsOwned : ∀ row ∈ program.rows, ∀ target ∈ row.targets, target ∈ addresses program

def checkedCompile (pattern : Pattern) : CheckedProgram :=
  ⟨compile pattern, compile_addresses_nodup pattern, compile_entry_owned pattern,
    compile_targets_owned pattern⟩

def lookup (program : Program) (address : Address) : Option Instruction :=
  program.rows.find? (fun row => row.address == address)

theorem lookup_defined (program : Program) (address : Address) (owned : address ∈ addresses program) :
    ∃ row, lookup program address = some row ∧ row ∈ program.rows ∧ row.address = address := by
  have inRows : address ∈ program.rows.map Instruction.address := by simpa [addresses] using owned
  obtain ⟨row, member, same⟩ := List.mem_map.mp inRows
  cases found : lookup program address with
  | none =>
      have absent := List.find?_eq_none.mp found row member
      simp [same] at absent
  | some actual =>
      refine ⟨actual, rfl, List.mem_of_find?_eq_some found, ?_⟩
      have test : (actual.address == address) = true :=
        List.find?_some (p := fun row : Instruction => row.address == address) found
      exact beq_iff_eq.mp test

theorem lookup_of_mem (program : Program) (unique : (program.rows.map Instruction.address).Nodup)
    (row : Instruction) (member : row ∈ program.rows) : lookup program row.address = some row := by
  have owned : row.address ∈ addresses program := by
    simp only [addresses, List.mem_toFinset]
    exact List.mem_map.mpr ⟨row, member, rfl⟩
  obtain ⟨actual, found, actualMember, same⟩ := lookup_defined program row.address owned
  have equal := List.inj_on_of_nodup_map unique actualMember member same
  simpa [equal] using found

inductive CharacterClass where
  | scalar (value : Nat)
  | any
  | ranges (values : List ScalarRange)
  deriving DecidableEq, Repr

def captureSlot (group : Nat) : Boundary → Nat
  | .start => 2 * group
  | .finish => 2 * group + 1

/-- Direct interpretation of one emitted instruction. Captures are the exact
slot writes, and assertions remain assertions rather than erased jumps. -/
def nodeOf {State : Type} (row : Instruction) (target : Address → State) :
    RegexTaggedGraph.Node State CharacterClass String Unit :=
  match row with
  | .fail _ => .dead
  | .accept _ => .accept ()
  | .jump _ next => .jump (target next)
  | .scalar _ scalar next => .consume (.scalar scalar) (target next)
  | .any _ next => .consume .any (target next)
  | .class_ _ ranges next => .consume (.ranges ranges) (target next)
  | .split _ first second => .choice (target first) (target second)
  | .save _ group boundary next => .save (captureSlot group boundary) (target next)
  | .assertion _ name next => .assertion name (target next)

def mapNode {First Second Class Assertion Tag : Type} (f : First → Second) :
    RegexTaggedGraph.Node First Class Assertion Tag → RegexTaggedGraph.Node Second Class Assertion Tag
  | .accept tag => .accept tag
  | .dead => .dead
  | .jump target => .jump (f target)
  | .choice first second => .choice (f first) (f second)
  | .consume class_ target => .consume class_ (f target)
  | .assertion assertion_ target => .assertion assertion_ (f target)
  | .save slot target => .save slot (f target)

def resolve (checked : CheckedProgram) (target : Address) : Owned checked.program :=
  if owned : target ∈ addresses checked.program then ⟨target, owned⟩
  else ⟨checked.program.entry, checked.entryOwned⟩

theorem resolve_val (checked : CheckedProgram) (target : Address)
    (owned : target ∈ addresses checked.program) : (resolve checked target).val = target := by
  simp [resolve, owned]

def graphOf (checked : CheckedProgram) (state : Owned checked.program) :
    RegexTaggedGraph.Node (Owned checked.program) CharacterClass String Unit :=
  nodeOf ((lookup checked.program state.val).getD (.fail state.val)) (resolve checked)

theorem nodeOf_resolve (checked : CheckedProgram) (row : Instruction) (member : row ∈ checked.program.rows) :
    mapNode Subtype.val (nodeOf row (resolve checked)) = nodeOf row id := by
  have targets := checked.targetsOwned row member
  cases row <;> simp_all [nodeOf, mapNode, Instruction.targets, resolve_val]

/-- Every actual row is interpreted exactly at its owned address. Missing or
aliased definitions cannot be hidden behind the resolver's totalization. -/
theorem graphOf_row (checked : CheckedProgram) (row : Instruction) (member : row ∈ checked.program.rows) :
    mapNode Subtype.val (graphOf checked ⟨row.address, by
      simp only [addresses, List.mem_toFinset]
      exact List.mem_map.mpr ⟨row, member, rfl⟩⟩) = nodeOf row id := by
  simp only [graphOf, lookup_of_mem checked.program checked.unique row member, Option.getD_some]
  exact nodeOf_resolve checked row member

theorem graphOf_compiled_row (pattern : Pattern) (row : Instruction)
    (member : row ∈ (compile pattern).rows) :
    mapNode Subtype.val (graphOf (checkedCompile pattern) ⟨row.address, by
      simp only [checkedCompile, addresses, List.mem_toFinset]
      exact List.mem_map.mpr ⟨row, member, rfl⟩⟩) = nodeOf row id :=
  graphOf_row (checkedCompile pattern) row member

theorem compiled_graph_ne_incomplete (pattern : Pattern) {length : Nat}
    (probe : OrderedGraphSearch.Probe CharacterClass String length)
    (eligible : RegexTaggedGraph.Thread (Owned (compile pattern)) length → Bool)
    (first : RegexTaggedGraph.Thread (Owned (compile pattern)) length)
    (closureFuel inputFuel : Nat)
    (closureEnough : 3 * Fintype.card (Owned (compile pattern)) + 1 ≤ closureFuel)
    (inputEnough : length + 1 ≤ inputFuel) :
    RegexPikeVM.run (graphOf (checkedCompile pattern)) probe eligible closureFuel inputFuel [first] ≠
      .incomplete :=
  RegexPikeVM.run_ne_incomplete _ _ _ _ _ _ closureEnough inputEnough

namespace Controls

private def initial (pattern : Pattern) (length : Nat) :
    RegexTaggedGraph.Thread (Owned (compile pattern)) length :=
  ⟨(⟨.root, compile_entry_owned pattern⟩, 0), fun _ => none, []⟩

private def testProbe (length : Nat) (holds : String → Fin (length + 1) → Bool) :
    OrderedGraphSearch.Probe CharacterClass String length :=
  ⟨fun class_ position =>
      if position.val < length then
        match class_ with
        | .any => true
        | .scalar scalar => scalar == 97 + position.val
        | .ranges ranges => (classLetters ranges).contains (97 + position.val)
      else false,
    holds⟩

private def observed {pattern : Pattern} {length : Nat} :
    RegexPikeVM.Result (RegexTaggedGraph.Thread (Owned (compile pattern)) length) Unit →
      Option (Nat × Option Nat × Option Nat)
  | .incomplete | .finished none => none
  | .finished (some (thread, _)) =>
      some (thread.point.2.val, (thread.registers 2).map Fin.val, (thread.registers 3).map Fin.val)

private def captureThenLiteral : Pattern := .seq (.capture 1 (.literal 97)) (.literal 98)

theorem actual_compiled_graph_selects_capture_and_full_span :
    observed (RegexPikeVM.run (graphOf (checkedCompile captureThenLiteral))
      (testProbe 2 (fun _ _ => false)) RegexPikeVM.atInputEnd 100 3 [initial captureThenLiteral 2]) =
      some (2, some 0, some 1) := by decide

private def assertedCapture : Pattern := .seq (.capture 1 .epsilon) (.assertion "input-end")

theorem actual_compiled_graph_executes_successful_assertion :
    observed (RegexPikeVM.run (graphOf (checkedCompile assertedCapture))
      (testProbe 0 (fun name position => name == "input-end" && position.val == 0))
      RegexPikeVM.atInputEnd 100 1 [initial assertedCapture 0]) = some (0, some 0, some 0) := by decide

theorem actual_compiled_graph_does_not_erase_failing_assertion :
    observed (RegexPikeVM.run (graphOf (checkedCompile assertedCapture))
      (testProbe 0 (fun _ _ => false)) RegexPikeVM.atInputEnd 100 1 [initial assertedCapture 0]) = none := by decide

theorem actual_compiled_graph_does_not_invent_wrong_scalar :
    observed (RegexPikeVM.run (graphOf (checkedCompile (.literal 98)))
      (testProbe 1 (fun _ _ => false)) RegexPikeVM.atInputEnd 100 2 [initial (.literal 98) 1]) = none := by decide

end Controls

#print axioms emit_targets_defined_or_continuation
#print axioms graphOf_compiled_row
#print axioms compiled_graph_ne_incomplete
#print axioms Controls.actual_compiled_graph_selects_capture_and_full_span

end Mettapedia.GSLT.LanguageDef.RegexSelection.Graph
