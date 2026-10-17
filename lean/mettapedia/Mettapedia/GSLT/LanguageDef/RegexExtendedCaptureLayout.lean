import Mettapedia.GSLT.LanguageDef.RegexExtendedKernel
import Mettapedia.GSLT.LanguageDef.RegexObservationInvariant

/-!
# Declared capture slots beyond executable writes

Zero repetitions can remove a group's instructions without removing its
declaration. Kernel capacity consequently retains the explicit declaration
count. Every actual open/close operation lies strictly below the independently
derived executable bound; extra layout slots cannot be targeted by decoding.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexExtendedCaptureLayout

open RegexExtendedCompilerSemantics
open RegexExtendedKernel

private theorem member_le_maximum (values : List Nat) (value : Nat) (member : value ∈ values) :
    value ≤ values.foldr max 0 := by
  induction values with
  | nil => cases member
  | cons head tail ih =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact Nat.le_max_left _ _
      · exact (ih member).trans (Nat.le_max_right _ _)

theorem operandGroup_lt_minimum (program : Program) (row : Instruction) (member : row ∈ program.rows) :
    operandGroup row < minimumGroups program :=
  Nat.lt_succ_of_le (member_le_maximum _ _ (List.mem_map.mpr ⟨row, member, rfl⟩))

theorem decode_open_bound (declaredCapacity : Nat) (checked : Graph.CheckedProgram)
    (assertions : String → Nat → Bool) (row : Instruction) (member : row ∈ checked.program.rows)
    (group : Fin (groups checked.program declaredCapacity)) (next : Fin checked.program.rows.length)
    (written : decode declaredCapacity checked assertions row member = .open group next) :
    group.val < minimumGroups checked.program := by
  cases row <;> simp only [decode] at written
  all_goals try contradiction
  rename_i origin actual opening target
  cases opening <;> simp only [Bool.false_eq_true, ↓reduceIte] at written
  · contradiction
  · cases written
    exact operandGroup_lt_minimum checked.program (.save origin actual true target) member

theorem decode_close_bound (declaredCapacity : Nat) (checked : Graph.CheckedProgram)
    (assertions : String → Nat → Bool) (row : Instruction) (member : row ∈ checked.program.rows)
    (group : Fin (groups checked.program declaredCapacity)) (next : Fin checked.program.rows.length)
    (written : decode declaredCapacity checked assertions row member = .close group next) :
    group.val < minimumGroups checked.program := by
  cases row <;> simp only [decode] at written
  all_goals try contradiction
  rename_i origin actual opening target
  cases opening <;> simp only [Bool.false_eq_true, ↓reduceIte] at written
  · cases written
    exact operandGroup_lt_minimum checked.program (.save origin actual false target) member
  · contradiction

theorem extension_slot_never_written (declaredCapacity : Nat) (checked : Graph.CheckedProgram)
    (assertions : String → Nat → Bool) (group : Fin (groups checked.program declaredCapacity))
    (unused : minimumGroups checked.program ≤ group.val) (pc next : Fin checked.program.rows.length) :
    code declaredCapacity checked assertions pc ≠ .open group next ∧
      code declaredCapacity checked assertions pc ≠ .close group next := by
  constructor
  · intro written
    have bound := decode_open_bound declaredCapacity checked assertions _ (List.getElem_mem pc.isLt) group next written
    omega
  · intro written
    have bound := decode_close_bound declaredCapacity checked assertions _ (List.getElem_mem pc.isLt) group next written
    omega

def writes : Pattern → Nat → Bool
  | .zero, _ | .epsilon, _ | .any, _ | .literal _, _ | .class_ _, _ |
    .assertion _, _ | .backref _ _, _ => false
  | .seq first second, group | .alt first second, group => writes first group || writes second group
  | .optional body _, group | .star body _, group | .plus body _, group | .look _ body, group => writes body group
  | .capture actual body, group => (actual == group) || writes body group

def SymbolicallyUnwritten (program : Program) (group : Nat) : Prop :=
  ∀ origin opening next, Instruction.save origin group opening next ∉ program.rows

theorem local_write_is_source_capture {pattern : Pattern} {continuation origin rowOrigin next : Address}
    {group : Nat} {opening : Bool}
    (source : Local pattern continuation origin (.save rowOrigin group opening next)) : writes pattern group = true := by
  generalize shape : Instruction.save rowOrigin group opening next = row at source
  cases source <;> simp_all [choice, writes]
  all_goals split_ifs at shape

theorem write_is_source_capture {pattern : Pattern} {continuation origin rowOrigin next : Address}
    {group : Nat} {opening : Bool}
    (source : At pattern continuation origin (.save rowOrigin group opening next)) : writes pattern group = true := by
  generalize shape : Instruction.save rowOrigin group opening next = row at source
  induction source with
  | «local» localSource => cases shape; exact local_write_is_source_capture localSource
  | seqLeft _ ih | seqRight _ ih | altLeft _ ih | altRight _ ih => simp [writes, ih shape]
  | optional _ ih | star _ ih | plus _ ih | capture _ ih | look _ ih => simp [writes, ih shape]

theorem no_source_write_means_unwritten (pattern : Pattern) (group : Nat) (absent : writes pattern group = false) :
    SymbolicallyUnwritten (compile pattern) group := by
  intro origin opening next member
  simp only [compile, List.mem_cons] at member
  rcases member with impossible | member
  · cases impossible
  · have present := write_is_source_capture (emitted_source pattern .ending .root _ member)
    rw [absent] at present
    contradiction

theorem decode_open_source (declaredCapacity : Nat) (checked : Graph.CheckedProgram)
    (assertions : String → Nat → Bool) (row : Instruction) (member : row ∈ checked.program.rows)
    (group : Fin (groups checked.program declaredCapacity)) (next : Fin checked.program.rows.length)
    (written : decode declaredCapacity checked assertions row member = .open group next) :
    ∃ origin target, row = .save origin group.val true target := by
  cases row <;> simp only [decode] at written
  all_goals try contradiction
  rename_i origin actual opening target
  cases opening <;> simp only [Bool.false_eq_true, ↓reduceIte] at written
  · contradiction
  · cases written
    exact ⟨origin, target, rfl⟩

theorem decode_close_source (declaredCapacity : Nat) (checked : Graph.CheckedProgram)
    (assertions : String → Nat → Bool) (row : Instruction) (member : row ∈ checked.program.rows)
    (group : Fin (groups checked.program declaredCapacity)) (next : Fin checked.program.rows.length)
    (written : decode declaredCapacity checked assertions row member = .close group next) :
    ∃ origin target, row = .save origin group.val false target := by
  cases row <;> simp only [decode] at written
  all_goals try contradiction
  rename_i origin actual opening target
  cases opening <;> simp only [Bool.false_eq_true, ↓reduceIte] at written
  · cases written
    exact ⟨origin, target, rfl⟩
  · contradiction

theorem symbolic_slot_never_written (declaredCapacity : Nat) (checked : Graph.CheckedProgram)
    (assertions : String → Nat → Bool) (group : Fin (groups checked.program declaredCapacity))
    (unused : SymbolicallyUnwritten checked.program group.val) (pc next : Fin checked.program.rows.length) :
    code declaredCapacity checked assertions pc ≠ .open group next ∧
      code declaredCapacity checked assertions pc ≠ .close group next := by
  constructor
  · intro written
    obtain ⟨origin, target, same⟩ := decode_open_source declaredCapacity checked assertions _
      (List.getElem_mem pc.isLt) group next written
    apply unused origin true target
    rw [← same]
    exact List.getElem_mem pc.isLt
  · intro written
    obtain ⟨origin, target, same⟩ := decode_close_source declaredCapacity checked assertions _
      (List.getElem_mem pc.isLt) group next written
    apply unused origin false target
    rw [← same]
    exact List.getElem_mem pc.isLt

theorem compiled_unwritten (declaredCapacity : Nat) (pattern : Pattern) (assertions : String → Nat → Bool)
    (slot : Fin (groups (compile pattern) declaredCapacity)) (absent : writes pattern slot.val = false) :
    RegexObservationInvariant.Unwritten (code declaredCapacity (Graph.checkedCompile pattern) assertions) slot := by
  have unused := no_source_write_means_unwritten pattern slot.val absent
  intro pc
  cases operation : code declaredCapacity (Graph.checkedCompile pattern) assertions pc
  all_goals try trivial
  case «open» group next =>
    intro same
    subst group
    exact (symbolic_slot_never_written declaredCapacity (Graph.checkedCompile pattern) assertions slot
      unused pc next).1 operation
  case close group next =>
    intro same
    subst group
    exact (symbolic_slot_never_written declaredCapacity (Graph.checkedCompile pattern) assertions slot
      unused pc next).2 operation

/-- Extra declarations and erased interior groups keep their original state
through every nested observation, not merely through ordinary operations. -/
theorem compiled_preserves_unwritten_slot (declaredCapacity : Nat) (pattern : Pattern)
    (assertions : String → Nat → Bool) (slot : Fin (groups (compile pattern) declaredCapacity))
    (absent : writes pattern slot.val = false) {length : Nat}
    (interpretation : RegexDependentObservation.Interpretation) (input : Fin length → Nat)
    (root : Fin (compile pattern).rows.length) :
    RegexObservationInvariant.PreservesSlot slot
      (RegexObservationKernel.evaluate interpretation input (code declaredCapacity (Graph.checkedCompile pattern) assertions)
        (certificate declaredCapacity pattern assertions) root) :=
  RegexObservationInvariant.evaluate_preserves_slot interpretation input _ _ slot
    (compiled_unwritten declaredCapacity pattern assertions slot absent) root

theorem source_preserves_unwritten_slot (declaredCapacity : Nat) (pattern : Pattern)
    (assertions : String → Nat → Bool) (slot : Fin (groups (compile pattern) declaredCapacity))
    (absent : writes pattern slot.val = false) {length : Nat}
    (interpretation : RegexDependentObservation.Interpretation) (input : Fin length → Nat)
    (root : Fin (compile pattern).rows.length) :
    RegexObservationInvariant.PreservesSlot slot
      (RegexObservationKernel.evaluate interpretation input (sourceCode declaredCapacity pattern assertions)
        (sourceCertificate declaredCapacity pattern assertions) root) := by
  rw [source_kernel_eq_compiled]
  exact compiled_preserves_unwritten_slot declaredCapacity pattern assertions slot absent interpretation input root

theorem unused_declared_capture_remains_unmatched (declaredCapacity : Nat) (pattern : Pattern)
    (assertions : String → Nat → Bool) (slot : Fin (groups (compile pattern) declaredCapacity))
    (absent : writes pattern slot.val = false) {length : Nat}
    (interpretation : RegexDependentObservation.Interpretation) (input : Fin length → Nat)
    (root : Fin (compile pattern).rows.length) (direction : RegexDependentObservation.Direction)
    (eligible : RegexDependentObservation.Configuration (compile pattern).rows.length
      (groups (compile pattern) declaredCapacity) length → Bool)
    (position : Fin (length + 1)) (captures : RegexDependentObservation.Captures
      (groups (compile pattern) declaredCapacity) length)
    (initially : captures slot = .unmatched)
    (winner : RegexDependentObservation.Winner (compile pattern).rows.length
      (groups (compile pattern) declaredCapacity) length)
    (returned : RegexObservationKernel.evaluate interpretation input
      (code declaredCapacity (Graph.checkedCompile pattern) assertions)
      (certificate declaredCapacity pattern assertions) root direction eligible position captures = some winner) :
    winner.configuration.captures slot = .unmatched :=
  (compiled_preserves_unwritten_slot declaredCapacity pattern assertions slot absent interpretation input root
    direction eligible position captures winner returned).trans initially

namespace Controls

private def catalog : RegexClassMaterialization.Catalog := ⟨"fixture", fun _ => none, []⟩

private def zeroCst : CettaWire.Term := RegexSourceProjection.cst "re-src:exact"
  [RegexSourceProjection.cst "re-src:capture" [RegexSourceProjection.cst "re-src:literal"
    [RegexSourceProjection.cst "re-src:lex-scalar" [RegexSourceProjection.cp 97]]],
   RegexSourceProjection.cst "re-src:digits-one" [RegexSourceProjection.cst "re-src:lex-digit" [RegexSourceProjection.cp 48]]]

private def zeroAnswer : RegexDependentProjection.Output :=
  ⟨.repeat (.exact 0) (.capture 1 (.regular (.literal 97))) true, ⟨{}, 2, [(1, "")]⟩⟩

theorem zero_count_selected_cst_keeps_its_declaration :
    RegexDependentProjection.project (RegexDependentProjection.view? catalog 20 .writtenForward) 20 {} zeroCst =
      some zeroAnswer ∧ RegexDependentProjection.prepare zeroAnswer = some .epsilon := by decide

theorem zero_repeat_layout_has_a_retained_unwritable_slot :
    groups (compile .epsilon) 2 = 2 ∧ minimumGroups (compile .epsilon) = 1 := by decide

theorem retained_empty_slot_cannot_be_a_fictitious_open :
    code 2 (Graph.checkedCompile .epsilon) (fun _ _ => false) ⟨0, by decide⟩ ≠
      .open ⟨1, by decide⟩ ⟨0, by decide⟩ := by
  exact (extension_slot_never_written 2 (Graph.checkedCompile .epsilon) (fun _ _ => false)
    ⟨1, by decide⟩ (by decide) ⟨0, by decide⟩ ⟨0, by decide⟩).1

theorem zero_repeat_hole_stays_unwritten_beside_a_later_capture :
    SymbolicallyUnwritten (compile (.seq .epsilon (.capture 2 (.literal 98)))) 1 ∧
    writes (.seq .epsilon (.capture 2 (.literal 98))) 2 = true :=
  ⟨no_source_write_means_unwritten _ 1 (by decide), by decide⟩

theorem erased_slot_is_preserved_through_complete_observation {length : Nat}
    (interpretation : RegexDependentObservation.Interpretation) (input : Fin length → Nat)
    (assertions : String → Nat → Bool) (root : Fin (compile Pattern.epsilon).rows.length) :
    RegexObservationInvariant.PreservesSlot (⟨1, by decide⟩ : Fin (groups (compile Pattern.epsilon) zeroAnswer.state.nextGroup))
      (RegexObservationKernel.evaluate interpretation input
        (code zeroAnswer.state.nextGroup (Graph.checkedCompile Pattern.epsilon) assertions)
        (certificate zeroAnswer.state.nextGroup Pattern.epsilon assertions) root) :=
  compiled_preserves_unwritten_slot _ .epsilon assertions ⟨1, by decide⟩ (by decide) interpretation input root

private def nestedHole : Pattern := .look .ahead (.seq .epsilon (.capture 2 (.literal 98)))

theorem erased_interior_slot_is_preserved_beside_nested_capture {length : Nat}
    (interpretation : RegexDependentObservation.Interpretation) (input : Fin length → Nat)
    (assertions : String → Nat → Bool)
    (root : Fin (compile nestedHole).rows.length) :
    RegexObservationInvariant.PreservesSlot
      (⟨1, by decide⟩ : Fin (groups (compile nestedHole) 3))
      (RegexObservationKernel.evaluate interpretation input
        (code 3 (Graph.checkedCompile nestedHole) assertions)
        (certificate 3 nestedHole assertions) root) :=
  compiled_preserves_unwritten_slot 3 _ assertions ⟨1, by decide⟩ (by decide) interpretation input root

end Controls

end Mettapedia.GSLT.LanguageDef.RegexExtendedCaptureLayout
