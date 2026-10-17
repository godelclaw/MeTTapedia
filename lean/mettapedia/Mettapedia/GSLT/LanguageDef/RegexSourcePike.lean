import Mettapedia.GSLT.LanguageDef.RegexSourceAuthored
import Mettapedia.Computability.RegularLanguages.RegexPikeCorrespondence

/-!
# Actual authored compiler and Pike execution realize source selected captures

The input artifact is a real result of the extracted module equations,
including counted-source normalization. Its actual Pike execution agrees
with the independent structural source selection judgment. Full thread data,
including every capture register and choice history, is preserved in both
directions. This is not a native C refinement theorem.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexSelection.Source.Pike

open Mettapedia.Computability.RegularLanguages
open RegexTaggedGraph
open OrderedGraphSearch (Point Probe)
open DeterministicEquations EquationExecution

/-- Exact selected-source adequacy of actual Pike execution on any checked
program returned by the authored module compiler. Point eligibility permits
full-match constraints before selection without consulting capture contents. -/
theorem returned_selected_iff {input : Term} {pattern : Pattern} {length : Nat}
    (lowered : RepetitionExecution.Lowers input pattern) (checked : Graph.CheckedProgram)
    (produced : Applies program host "re:compile-authored" [input] (code checked.program))
    (probe : Probe Graph.CharacterClass String length) (eligible : Point Address length → Bool)
    (first last : Thread (Graph.Owned checked.program) length) (closureFuel inputFuel : Nat)
    (closureEnough : 3 * Fintype.card (Graph.Owned checked.program) + 1 ≤ closureFuel)
    (inputEnough : length + 1 ≤ inputFuel) :
    RegexPikeVM.run (Graph.graphOf checked) probe
      (fun thread => eligible (mapPoint Subtype.val thread.point)) closureFuel inputFuel [first] =
      .finished (some (last, ())) ↔
      Selected pattern probe (fun thread => eligible thread.point)
        (mapThread Subtype.val first) (mapThread Subtype.val last) := by
  refine (RegexPikeCorrespondence.run_leastSimple (Graph.graphOf checked) probe
    (fun point => eligible (mapPoint Subtype.val point)) first last () closureFuel inputFuel
    closureEnough inputEnough).trans ?_
  constructor
  · intro result
    exact (Authored.returned_selected_iff_source lowered checked produced probe
      (fun thread => eligible thread.point) first last).mp result.1
  · intro selected
    have least := (Authored.returned_selected_iff_source lowered checked produced probe
      (fun thread => eligible thread.point) first last).mpr selected
    refine ⟨least, ?_⟩
    obtain ⟨choices, points, tag, trace, _, _⟩ := least
    cases tag
    exact trace.sound.2.1

/-- The direct accumulator entry uses the same theorem through its proved
actual program identity, without a second graph compiler or source meaning. -/
theorem accumulator_selected_iff {length : Nat} (pattern : Pattern) (checked : Graph.CheckedProgram)
    (produced : Applies program host "re:compile-acc" [source pattern] (code checked.program))
    (probe : Probe Graph.CharacterClass String length) (eligible : Point Address length → Bool)
    (first last : Thread (Graph.Owned checked.program) length) (closureFuel inputFuel : Nat)
    (closureEnough : 3 * Fintype.card (Graph.Owned checked.program) + 1 ≤ closureFuel)
    (inputEnough : length + 1 ≤ inputFuel) :
    RegexPikeVM.run (Graph.graphOf checked) probe
      (fun thread => eligible (mapPoint Subtype.val thread.point)) closureFuel inputFuel [first] =
      .finished (some (last, ())) ↔
      Selected pattern probe (fun thread => eligible thread.point)
        (mapThread Subtype.val first) (mapThread Subtype.val last) := by
  have actual := (Authored.accumulator_returned_program_iff pattern checked.program).mp produced
  have lowered := RepetitionExecution.canonical_source_lowers pattern
  have authored : Applies program host "re:compile-authored" [source pattern] (code checked.program) :=
    (RepetitionExecution.compile_authored_result_exact lowered (code checked.program)).mpr (congrArg code actual)
  exact returned_selected_iff lowered checked authored probe eligible first last closureFuel inputFuel
    closureEnough inputEnough

namespace Controls

private def initial (pattern : Pattern) (length : Nat) : Thread (Graph.Owned (compile pattern)) length :=
  ⟨(⟨.root, Graph.compile_entry_owned pattern⟩, 0), fun _ => none, []⟩

private def final (pattern : Pattern) (length : Nat) (position : Fin (length + 1))
    (registers : Registers length) (choices : List Bool) : Thread (Graph.Owned (compile pattern)) length :=
  ⟨(⟨.ending, by simp [Graph.addresses, compile, Instruction.address]⟩, position), registers, choices⟩

private def probe (length : Nat) : Probe Graph.CharacterClass String length :=
  ⟨fun class_ position =>
    if position.val < length then
      match class_ with
      | .any => true
      | .scalar value => value == 97 + position.val
      | .ranges values => (classLetters values).contains (97 + position.val)
    else false,
    fun _ _ => false⟩

private def closureBudget (pattern : Pattern) : Nat := 3 * (compile pattern).rows.length + 1

private theorem closureEnough (pattern : Pattern) :
    3 * Fintype.card (Graph.Owned (compile pattern)) + 1 ≤ closureBudget pattern := by
  rw [Graph.owned_card _ (Graph.compile_addresses_nodup pattern)]
  exact Nat.le_refl _

private def emptyCapture : Pattern := .capture 1 .epsilon
private def emptyCaptureLast : Thread (Graph.Owned (compile emptyCapture)) 0 :=
  final emptyCapture 0 0 (write (write (fun _ => none) 2 0) 3 0) []

/-- The actual authored result and actual Pike execution select a participating
empty capture; a different untouched group remains absent. -/
theorem authored_empty_capture_has_its_exact_source_observation :
    Selected emptyCapture (probe 0) (fun _ => true)
      (mapThread Subtype.val (initial emptyCapture 0)) (mapThread Subtype.val emptyCaptureLast) ∧
      emptyCaptureLast.registers 2 = some 0 ∧ emptyCaptureLast.registers 3 = some 0 ∧
      emptyCaptureLast.registers 4 = none := by
  have lowered := RepetitionExecution.canonical_source_lowers emptyCapture
  have selected := (returned_selected_iff lowered (Graph.checkedCompile emptyCapture)
    (RepetitionExecution.compile_authored_computes lowered) (probe 0) (fun _ => true)
    (initial emptyCapture 0) emptyCaptureLast (closureBudget emptyCapture) 1
    (closureEnough emptyCapture) (by decide)).mp (by rfl)
  exact ⟨selected, by decide⟩

private def alternatives : Pattern := .alt (.literal 97) (.seq (.literal 97) (.literal 98))
private def alternativesLast : Thread (Graph.Owned (compile alternatives)) 2 :=
  final alternatives 2 2 (fun _ => none) [true]

/-- Full matching excludes the earlier short prefix before selecting the
later complete source alternative. -/
theorem authored_full_match_constrains_before_selection :
    Selected alternatives (probe 2) (fun thread => thread.point.2.val == 2)
      (mapThread Subtype.val (initial alternatives 2)) (mapThread Subtype.val alternativesLast) := by
  have lowered := RepetitionExecution.canonical_source_lowers alternatives
  exact (returned_selected_iff lowered (Graph.checkedCompile alternatives)
    (RepetitionExecution.compile_authored_computes lowered) (probe 2) (fun point => point.2.val == 2)
    (initial alternatives 2) alternativesLast (closureBudget alternatives) 3
    (closureEnough alternatives) (by decide)).mp (by rfl)

private def failedCapture : Pattern :=
  .alt (.capture 1 (.seq (.literal 97) (.literal 98))) (.literal 97)
private def cleanLast : Thread (Graph.Owned (compile failedCapture)) 1 :=
  final failedCapture 1 1 (fun _ => none) [true]
private def leakedLast : Thread (Graph.Owned (compile failedCapture)) 1 :=
  final failedCapture 1 1 (write (fun _ => none) 2 0) [true]

/-- The failed branch's capture-start write cannot leak into the selected
successful alternative, either in actual execution or source selection. -/
theorem discarded_capture_write_is_not_a_source_observation :
    Selected failedCapture (probe 1) (fun _ => true)
      (mapThread Subtype.val (initial failedCapture 1)) (mapThread Subtype.val cleanLast) ∧
    ¬ Selected failedCapture (probe 1) (fun _ => true)
      (mapThread Subtype.val (initial failedCapture 1)) (mapThread Subtype.val leakedLast) := by
  have lowered := RepetitionExecution.canonical_source_lowers failedCapture
  have produced := RepetitionExecution.compile_authored_computes lowered
  have actual : RegexPikeVM.run (Graph.graphOf (Graph.checkedCompile failedCapture)) (probe 1)
      (fun _ => true) (closureBudget failedCapture) 2 [initial failedCapture 1] =
      .finished (some (cleanLast, ())) := by rfl
  constructor
  · exact (returned_selected_iff lowered (Graph.checkedCompile failedCapture) produced (probe 1) (fun _ => true)
      (initial failedCapture 1) cleanLast (closureBudget failedCapture) 2
      (closureEnough failedCapture) (by decide)).mp actual
  · intro leaked
    have invented := (returned_selected_iff lowered (Graph.checkedCompile failedCapture) produced
      (probe 1) (fun _ => true) (initial failedCapture 1) leakedLast (closureBudget failedCapture) 2
      (closureEnough failedCapture) (by decide)).mpr leaked
    have same : cleanLast = leakedLast :=
      (Prod.mk.inj (Option.some.inj (RegexPikeVM.Result.finished.inj (actual.symm.trans invented)))).1
    have registers := congrArg (fun thread => thread.registers 2) same
    simp [cleanLast, leakedLast, final, write] at registers

end Controls

end Mettapedia.GSLT.LanguageDef.RegexSelection.Source.Pike
