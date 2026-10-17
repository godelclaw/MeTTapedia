import Mettapedia.GSLT.LanguageDef.RegexUnicodeProjection
import Mettapedia.GSLT.LanguageDef.RegexTextIngress
import Mettapedia.GSLT.LanguageDef.RegexSourceObservation

/-!
# Raw pattern text, Unicode projection and winning source observations

This join uses the verified UTF-8 ingress, complete authored source parser,
explicit tree policy, Unicode class interpretation, actual module compiler
and actual reference Pike driver. It preserves and reflects the selected
source observation, including captures. Pattern bytes and haystack text are
different inputs. Native C refinement and extended-mode source preparation
remain separate boundaries.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexUnicodePipeline

open Mettapedia.Computability.RegularLanguages
open Mettapedia.GSLT.Parsing.PresentationExprSemantics (CST)
open RegexSelection RegexSelection.Source
open RegexTaggedGraph
open OrderedGraphSearch (Point Probe)
open DeterministicEquations EquationExecution
open RegexSourceProjection (State Output project Projects)
open RegexClassMaterialization (Catalog)

theorem text_selected_iff {input : Term} {text : List Char}
    (patternBytes : ByteArray) (policy : CST → Prop) (catalog : Catalog) (payloadDepth : Nat)
    (state : State) (projected : Output)
    (lowered : RepetitionExecution.Lowers input projected.pattern) (checked : Graph.CheckedProgram)
    (produced : Applies program host "re:compile-authored" [input] (code checked.program))
    (probe : Probe Graph.CharacterClass String text.length) (eligible : Point Address text.length → Bool)
    (closureFuel inputFuel : Nat)
    (closureEnough : 3 * Fintype.card (Graph.Owned checked.program) + 1 ≤ closureFuel)
    (inputEnough : text.length + 1 ≤ inputFuel) (first : Thread (Graph.Owned checked.program) text.length)
    (observation : RegexMatchObservations.Observation) :
    ((∃ tree, RegexTextIngress.Parsed patternBytes tree ∧ policy tree ∧
        ∃ depth, project (RegexUnicodeProjection.view? catalog payloadDepth) depth state
          (RegexScalarSyntax.wire tree) = some projected) ∧
      (RegexPikeVM.run (Graph.graphOf checked) probe
        (fun thread => eligible (mapPoint Subtype.val thread.point)) closureFuel inputFuel [first]).map
          (fun last => CaptureObservation.observe first.point.2 last projected.state.nextGroup) =
            .finished (some (observation, ()))) ↔
    ((∃ tree, RegexTextIngress.Source patternBytes tree ∧ policy tree ∧
        Projects (RegexUnicodeProjection.view? catalog payloadDepth) state (RegexScalarSyntax.wire tree) projected) ∧
      Observation.WinnerObserved projected.pattern probe (fun thread => eligible thread.point)
        (mapThread Subtype.val first) projected.state.nextGroup observation) := by
  exact and_congr (RegexTextIngress.selected_projection_iff patternBytes policy
    (RegexUnicodeProjection.view? catalog payloadDepth) state projected)
    (Observation.returned_pike_winner_iff lowered checked produced probe eligible closureFuel inputFuel
      closureEnough inputEnough first projected.state.nextGroup observation)

theorem text_selected_valid {input : Term} {text : List Char}
    (patternBytes : ByteArray) (tree : CST) (catalog : Catalog) (payloadDepth traversalDepth : Nat)
    (state : State) (projected : Output)
    (parsed : RegexTextIngress.Parsed patternBytes tree)
    (projection : project (RegexUnicodeProjection.view? catalog payloadDepth) traversalDepth state
      (RegexScalarSyntax.wire tree) = some projected)
    (lowered : RepetitionExecution.Lowers input projected.pattern) (checked : Graph.CheckedProgram)
    (produced : Applies program host "re:compile-authored" [input] (code checked.program))
    (probe : Probe Graph.CharacterClass String text.length) (eligible : Point Address text.length → Bool)
    (closureFuel inputFuel : Nat)
    (closureEnough : 3 * Fintype.card (Graph.Owned checked.program) + 1 ≤ closureFuel)
    (inputEnough : text.length + 1 ≤ inputFuel) (first : Thread (Graph.Owned checked.program) text.length)
    (initial : first.registers = CaptureObservation.initialRegisters first.point.2)
    (observation : RegexMatchObservations.Observation)
    (finished : (RegexPikeVM.run (Graph.graphOf checked) probe
      (fun thread => eligible (mapPoint Subtype.val thread.point)) closureFuel inputFuel [first]).map
        (fun last => CaptureObservation.observe first.point.2 last projected.state.nextGroup) =
          .finished (some (observation, ()))) :
    RegexTextIngress.Source patternBytes tree ∧
      Projects (RegexUnicodeProjection.view? catalog payloadDepth) state (RegexScalarSyntax.wire tree) projected ∧
      Observation.WinnerObserved projected.pattern probe (fun thread => eligible thread.point)
        (mapThread Subtype.val first) projected.state.nextGroup observation ∧
      observation.Valid text.length ∧
      (RegexPublicSearch.byteObservation text observation).Valid (utf8Length text) := by
  have winner := Observation.returned_pike_winner_valid lowered checked produced probe eligible
    closureFuel inputFuel closureEnough inputEnough first initial projected.state.nextGroup observation finished
  exact ⟨(RegexTextIngress.parsed_iff_source patternBytes tree).1 parsed,
    RegexSourceProjection.project_sound _ traversalDepth state _ projected projection,
    winner.1, winner.2, RegexPublicSearch.byteObservation_valid text observation winner.2⟩

namespace Controls

private def emptyCatalog : Catalog := ⟨"no-properties-needed", fun _ => none, []⟩

theorem raw_unicode_literal_projects_to_its_source_pattern :
    RegexTextIngress.Parsed (['λ'].utf8Encode) (RegexScalarSyntax.Controls.rootLiteral 955) ∧
    project (RegexUnicodeProjection.view? emptyCatalog 20) 20 {}
      (RegexScalarSyntax.wire (RegexScalarSyntax.Controls.rootLiteral 955)) =
        some ⟨.seq (.literal 955) .epsilon, {}⟩ := by
  exact ⟨RegexTextIngress.Controls.multibyte_scalar_reaches_the_complete_parser, by decide⟩

theorem raw_nul_literal_is_not_text_termination :
    RegexTextIngress.Parsed (['\x00'].utf8Encode) (RegexScalarSyntax.Controls.rootLiteral 0) ∧
    project (RegexUnicodeProjection.view? emptyCatalog 20) 20 {}
      (RegexScalarSyntax.wire (RegexScalarSyntax.Controls.rootLiteral 0)) =
        some ⟨.seq (.literal 0) .epsilon, {}⟩ := by
  exact ⟨RegexTextIngress.Controls.embedded_nul_is_a_literal_scalar_not_termination, by decide⟩

theorem malformed_utf8_cannot_reach_a_selected_source_pattern (tree : CST) :
    ¬ RegexTextIngress.Source ⟨#[0x61, 0xff, 0x62]⟩ tree :=
  RegexTextIngress.malformed_input_has_no_source
    RegexTextIngress.Controls.malformed_utf8_retains_the_exact_fault_offset tree

end Controls

#print axioms text_selected_iff
#print axioms text_selected_valid

end Mettapedia.GSLT.LanguageDef.RegexUnicodePipeline
