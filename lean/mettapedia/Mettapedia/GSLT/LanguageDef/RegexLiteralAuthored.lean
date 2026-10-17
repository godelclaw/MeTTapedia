import Mettapedia.GSLT.LanguageDef.RegexLiteralOrdinal
import Mettapedia.GSLT.LanguageDef.RegexSourceObservation

/-!
# Authored-source authority for the admitted literal-trie realization

The input artifact is returned by actual execution of the existing authored
compiler equations. A finite local instruction admission earns the literal
realization. Trie selection then agrees with independently selected source
executions, not merely with the recognized language.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexLiteralAuthored

open Mettapedia.Computability.RegularLanguages
open RegexTaggedGraph RegexSelection RegexLiteralGraphPlan RegexLiteralTable RegexLiteralOrdinal
open DeterministicEquations

theorem trie_selected_source_iff {request : Term} {pattern : Pattern}
    (lowered : RepetitionExecution.Lowers request pattern) (checked : Graph.CheckedProgram)
    (produced : Applies EquationExecution.program EquationExecution.host
      "re:compile-authored" [request] (EquationExecution.code checked.program))
    (input : List Nat) (full : Bool) (plan : Plan (Graph.Owned checked.program))
    (valid : Valid (Graph.graphOf checked) plan) (acyclic : Acyclic plan)
    (initial final : Thread (Graph.Owned checked.program) input.length)
    (entry : initial.point.1 = root plan)
    (closureFuel inputFuel : Nat)
    (closureEnough : 3 * Fintype.card (Graph.Owned checked.program) + 1 ≤ closureFuel)
    (inputEnough : input.length + 1 ≤ inputFuel) :
    trieSelect full input initial (extract plan) = some final ↔
      Source.Selected pattern (literalProbe input) (endpointEligible full input.length)
        (Source.mapThread Subtype.val initial) (Source.mapThread Subtype.val final) := by
  have authored := Source.Pike.returned_selected_iff lowered checked produced (literalProbe input)
    (fun point => !full || point.2.val == input.length) initial final closureFuel inputFuel
    closureEnough inputEnough
  change (RegexPikeVM.run (Graph.graphOf checked) (literalProbe input) (endpointEligible full input.length)
      closureFuel inputFuel [initial] = .finished (some (final, ()))) ↔
      Source.Selected pattern (literalProbe input) (endpointEligible full input.length)
        (Source.mapThread Subtype.val initial) (Source.mapThread Subtype.val final) at authored
  rw [pike_eq_trieSelect (Graph.graphOf checked) full input plan valid acyclic initial entry
    closureFuel inputFuel closureEnough inputEnough] at authored
  simpa only [RegexPikeVM.Result.finished.injEq, Option.map_eq_some_iff,
    Prod.mk.injEq, and_true, exists_eq_right] using authored

namespace Controls

private def alternatives : Pattern := .alt (.literal 97) (.seq (.literal 97) (.literal 98))
private def compiled := Graph.checkedCompile alternatives
private def pc (address : Address) : Graph.Owned compiled.program := Graph.resolve compiled address

private def admitted : Plan (Graph.Owned compiled.program) :=
  .branch (pc .root) (.scalar (pc (.left .root)) 97 (.accept (pc .ending)))
    (.jump (pc (.right .root))
      (.scalar (pc (.left (.right .root))) 97
        (.scalar (pc (.right (.right .root))) 98 (.accept (pc .ending)))))

private theorem admitted_valid : Valid (Graph.graphOf compiled) admitted := by
  simp only [admitted, Valid]
  exact ⟨rfl, ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl⟩

private theorem admitted_acyclic : Acyclic admitted := by
  simp only [admitted, Acyclic, states]
  decide

private def initial : Thread (Graph.Owned compiled.program) 2 :=
  ⟨(pc .root, 0), CaptureObservation.initialRegisters 0, []⟩

private def observe (thread : Thread (Graph.Owned compiled.program) 2) :=
  CaptureObservation.observe initial.point.2 thread 1

private def prefixWinner : Thread (Graph.Owned compiled.program) 2 :=
  ⟨(pc .ending, 1), initial.registers, [false]⟩

theorem actual_authored_source_prefers_shorter_first_alternative :
    Source.Selected alternatives (literalProbe [97, 98]) (endpointEligible false 2)
      (Source.mapThread Subtype.val initial) (Source.mapThread Subtype.val prefixWinner) := by
  have lowered := RepetitionExecution.canonical_source_lowers alternatives
  have produced := RepetitionExecution.compile_authored_computes lowered
  exact (trie_selected_source_iff lowered compiled produced [97, 98] false admitted admitted_valid
    admitted_acyclic initial prefixWinner rfl 100 3 (by decide) (by decide)).mp (by rfl)

theorem prefix_keeps_priority_span_and_group_zero :
    (trieSelect false [97, 98] initial (extract admitted)).map observe =
      some ⟨⟨0, 1⟩, [some ⟨0, 1⟩], [false]⟩ := by rfl

theorem full_filters_paths_before_priority :
    (trieSelect true [97, 98] initial (extract admitted)).map observe =
      some ⟨⟨0, 2⟩, [some ⟨0, 2⟩], [true]⟩ := by rfl

theorem actual_pike_and_literal_trie_agree :
    (match RegexPikeVM.run (Graph.graphOf compiled) (literalProbe [97, 98])
        (endpointEligible false 2) 100 3 [initial] with
      | .incomplete => none
      | .finished result => result.map (fun found => observe found.1)) =
      (trieSelect false [97, 98] initial (extract admitted)).map observe := by
  exact pike_observation_eq (Graph.graphOf compiled) false [97, 98] admitted admitted_valid
    admitted_acyclic initial rfl observe 100 3 (by decide) (by decide)

theorem longer_match_cannot_replace_preferred_short_match :
    (trieSelect false [97, 98] initial (extract admitted)).map observe ≠
      some ⟨⟨0, 2⟩, [some ⟨0, 2⟩], [true]⟩ := by
  rw [prefix_keeps_priority_span_and_group_zero]
  decide

theorem unicode_span_uses_original_utf8_bytes :
    RegexPublicSearch.byteObservation ['a', 'λ', 'b'] ⟨⟨1, 2⟩, [some ⟨1, 2⟩], []⟩ =
      ⟨⟨1, 3⟩, [some ⟨1, 3⟩], []⟩ := by decide

end Controls

end Mettapedia.GSLT.LanguageDef.RegexLiteralAuthored
