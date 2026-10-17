import Mettapedia.GSLT.LanguageDef.RegexSourceAuthored
import Mettapedia.GSLT.LanguageDef.RegexSourcePike
import Mettapedia.GSLT.LanguageDef.RegexCaptureObservation
import Mettapedia.GSLT.LanguageDef.RegexSourceProjection

/-!
# Authored compiler execution to public source observations

The artifact premise is actual execution of the extracted module equations.
Successful Pike results yield independent simple source executions and valid
whole-match/user-capture observations. Capture validity is derived from source
control-flow postdomination and replay, not supplied as a boundary premise.

The CST corollary starts with an explicitly selected physical source tree and
its actual attributed projection. It does not claim a raw-byte lexer,
packed-forest ambiguity policy, or native C refinement theorem.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexSelection.Source.Observation

open Mettapedia.Computability.RegularLanguages
open RegexTaggedGraph
open OrderedGraphSearch (Point Probe)
open DeterministicEquations EquationExecution
open RegexMatchObservations (Observation)

/-- The independent simple-source observation includes all declared groups,
their participation, selected priority code and the original-input span. -/
def SimpleObserved {length : Nat} (pattern : Pattern)
    (probe : Probe Graph.CharacterClass String length) (eligible : Thread Address length → Bool)
    (first : Thread Address length) (groupCount : Nat) (observation : Observation) : Prop :=
  ∃ last choices points,
    Source.Trace pattern probe eligible first choices points last ∧ points.Nodup ∧
      CaptureObservation.observe first.point.2 last groupCount = observation

def WinnerObserved {length : Nat} (pattern : Pattern)
    (probe : Probe Graph.CharacterClass String length) (eligible : Thread Address length → Bool)
    (first : Thread Address length) (groupCount : Nat) (observation : Observation) : Prop :=
  ∃ last, Source.Selected pattern probe eligible first last ∧
    CaptureObservation.observe first.point.2 last groupCount = observation

/-- Address relocation changes no field of the public observation. -/
theorem observe_mapThread {First Second : Type} {length : Nat} (map : First → Second)
    (first last : Thread First length) (groupCount : Nat) :
    CaptureObservation.observe (Source.mapThread map first).point.2 (Source.mapThread map last) groupCount =
      CaptureObservation.observe first.point.2 last groupCount := rfl

/-- Any completed independent source execution beginning at an owned source
occurrence has valid captures from the native-style initial snapshot. -/
theorem source_trace_observation_valid {pattern : Pattern} {length : Nat}
    {probe : Probe Graph.CharacterClass String length} {eligible : Thread Address length → Bool}
    {first last : Thread Address length} {choices : List Bool} {points : List (Point Address length)}
    (trace : Source.Trace pattern probe eligible first choices points last)
    (owned : first.point.1 ∈ Graph.addresses (compile pattern))
    (initial : first.registers = CaptureObservation.initialRegisters first.point.2)
    (groupCount : Nat) : (CaptureObservation.observe first.point.2 last groupCount).Valid length := by
  let targetFirst : Thread (Graph.Owned (compile pattern)) length :=
    ⟨(⟨first.point.1, owned⟩, first.point.2), first.registers, first.choices⟩
  have viewed : Source.view targetFirst = first := by cases first; rfl
  obtain ⟨targetLast, targetPoints, targetTrace, lastSame, _⟩ :=
    Source.source_trace_compiled trace targetFirst viewed
  have initialized : targetFirst.registers = CaptureObservation.initialRegisters targetFirst.point.2 := initial
  have valid := CaptureObservation.native_style_observation_valid initialized targetTrace groupCount
  have observationSame := observe_mapThread Subtype.val targetFirst targetLast groupCount
  change CaptureObservation.observe (Source.view targetFirst).point.2 (Source.view targetLast) groupCount =
    CaptureObservation.observe targetFirst.point.2 targetLast groupCount at observationSame
  rw [viewed, lastSame] at observationSame
  exact observationSame ▸ valid

/-- The actual module-produced artifact and an actual completed Pike result
give both independent source evidence and valid public spans/captures. -/
theorem returned_pike_observation {input : Term} {pattern : Pattern} {length : Nat}
    (lowered : RepetitionExecution.Lowers input pattern) (checked : Graph.CheckedProgram)
    (produced : Applies program host "re:compile-authored" [input] (code checked.program))
    (probe : Probe Graph.CharacterClass String length) (eligible : Thread Address length → Bool)
    (closureFuel inputFuel : Nat) (first last : Thread (Graph.Owned checked.program) length)
    (initial : first.registers = CaptureObservation.initialRegisters first.point.2)
    (finished : RegexPikeVM.run (Graph.graphOf checked) probe
      (eligible ∘ mapThread Subtype.val) closureFuel inputFuel [first] = .finished (some (last, ())))
    (groupCount : Nat) :
    SimpleObserved pattern probe eligible (mapThread Subtype.val first) groupCount
        (CaptureObservation.observe first.point.2 last groupCount) ∧
      (CaptureObservation.observe first.point.2 last groupCount).Valid length := by
  obtain ⟨choices, points, sourceTrace, simple⟩ := Authored.returned_pike_success_source lowered checked produced
    probe eligible closureFuel inputFuel first last finished
  refine ⟨⟨mapThread Subtype.val last, choices, points, sourceTrace, simple, rfl⟩, ?_⟩
  have same := Authored.returned_checked_eq lowered checked produced
  subst checked
  have owned : (mapThread Subtype.val first).point.1 ∈ Graph.addresses (compile pattern) := first.point.1.property
  exact source_trace_observation_valid sourceTrace owned initial groupCount

theorem returned_pike_byte_observation {input : Term} {pattern : Pattern} {text : List Char}
    (lowered : RepetitionExecution.Lowers input pattern) (checked : Graph.CheckedProgram)
    (produced : Applies program host "re:compile-authored" [input] (code checked.program))
    (probe : Probe Graph.CharacterClass String text.length) (eligible : Thread Address text.length → Bool)
    (closureFuel inputFuel : Nat) (first last : Thread (Graph.Owned checked.program) text.length)
    (initial : first.registers = CaptureObservation.initialRegisters first.point.2)
    (finished : RegexPikeVM.run (Graph.graphOf checked) probe
      (eligible ∘ mapThread Subtype.val) closureFuel inputFuel [first] = .finished (some (last, ())))
    (groupCount : Nat) :
    (RegexPublicSearch.byteObservation text (CaptureObservation.observe first.point.2 last groupCount)).Valid (utf8Length text) :=
  RegexPublicSearch.byteObservation_valid text _
    (returned_pike_observation lowered checked produced probe eligible closureFuel inputFuel first last initial finished groupCount).2

/-- The public observation is the value actually projected from the finished
Pike result. An incomplete or empty result cannot satisfy this premise. -/
theorem returned_pike_observed_value {input : Term} {pattern : Pattern} {length : Nat}
    (lowered : RepetitionExecution.Lowers input pattern) (checked : Graph.CheckedProgram)
    (produced : Applies program host "re:compile-authored" [input] (code checked.program))
    (probe : Probe Graph.CharacterClass String length) (eligible : Thread Address length → Bool)
    (closureFuel inputFuel : Nat) (first : Thread (Graph.Owned checked.program) length)
    (initial : first.registers = CaptureObservation.initialRegisters first.point.2)
    (groupCount : Nat) (observation : Observation)
    (finished : (RegexPikeVM.run (Graph.graphOf checked) probe
      (eligible ∘ mapThread Subtype.val) closureFuel inputFuel [first]).map
        (fun last => CaptureObservation.observe first.point.2 last groupCount) =
          .finished (some (observation, ()))) :
    SimpleObserved pattern probe eligible (mapThread Subtype.val first) groupCount observation ∧
      observation.Valid length := by
  cases result : RegexPikeVM.run (Graph.graphOf checked) probe
      (eligible ∘ mapThread Subtype.val) closureFuel inputFuel [first] with
  | incomplete => simp [result, RegexPikeVM.Result.map] at finished
  | finished selected =>
      cases selected with
      | none => simp [result, RegexPikeVM.Result.map] at finished
      | some pair =>
          obtain ⟨last, tag⟩ := pair
          cases tag
          have same : CaptureObservation.observe first.point.2 last groupCount = observation := by
            simpa [result, RegexPikeVM.Result.map] using finished
          rw [← same]
          exact returned_pike_observation lowered checked produced probe eligible closureFuel inputFuel
            first last initial result groupCount

/-- Full preservation and reflection of the public winning observation for
the actual artifact and actual Pike driver, including all selected captures. -/
theorem returned_pike_winner_iff {input : Term} {pattern : Pattern} {length : Nat}
    (lowered : RepetitionExecution.Lowers input pattern) (checked : Graph.CheckedProgram)
    (produced : Applies program host "re:compile-authored" [input] (code checked.program))
    (probe : Probe Graph.CharacterClass String length) (eligible : Point Address length → Bool)
    (closureFuel inputFuel : Nat)
    (closureEnough : 3 * Fintype.card (Graph.Owned checked.program) + 1 ≤ closureFuel)
    (inputEnough : length + 1 ≤ inputFuel) (first : Thread (Graph.Owned checked.program) length)
    (groupCount : Nat) (observation : Observation) :
    (RegexPikeVM.run (Graph.graphOf checked) probe
      (fun thread => eligible (mapPoint Subtype.val thread.point)) closureFuel inputFuel [first]).map
        (fun last => CaptureObservation.observe first.point.2 last groupCount) =
          .finished (some (observation, ())) ↔
      WinnerObserved pattern probe (fun thread => eligible thread.point)
        (mapThread Subtype.val first) groupCount observation := by
  constructor
  · intro finished
    cases result : RegexPikeVM.run (Graph.graphOf checked) probe
        (fun thread => eligible (mapPoint Subtype.val thread.point)) closureFuel inputFuel [first] with
    | incomplete => simp [result, RegexPikeVM.Result.map] at finished
    | finished selected =>
        cases selected with
        | none => simp [result, RegexPikeVM.Result.map] at finished
        | some pair =>
            obtain ⟨last, tag⟩ := pair
            cases tag
            have observed : CaptureObservation.observe first.point.2 last groupCount = observation := by
              simpa [result, RegexPikeVM.Result.map] using finished
            have winner := (Source.Pike.returned_selected_iff lowered checked produced probe eligible
              first last closureFuel inputFuel closureEnough inputEnough).mp result
            exact ⟨mapThread Subtype.val last, winner, observed⟩
  · rintro ⟨last, winner, observed⟩
    have same := Authored.returned_checked_eq lowered checked produced
    subst checked
    have witness := winner
    obtain ⟨choices, points, sourceTrace, _, _⟩ := witness
    obtain ⟨targetLast, targetPoints, _, lastSame, _⟩ := Source.source_trace_compiled sourceTrace first rfl
    have targetWinner : Selected pattern probe (fun thread => eligible thread.point)
        (mapThread Subtype.val first) (mapThread Subtype.val targetLast) := by
      change Selected pattern probe (fun thread => eligible thread.point) (view first) (view targetLast)
      rw [lastSame]
      exact winner
    have result := (Source.Pike.returned_selected_iff lowered (Graph.checkedCompile pattern) produced probe eligible
      first targetLast closureFuel inputFuel closureEnough inputEnough).mpr targetWinner
    have publicSame : CaptureObservation.observe first.point.2 targetLast groupCount = observation := by
      have equality := observe_mapThread Subtype.val first targetLast groupCount
      change CaptureObservation.observe (view first).point.2 (view targetLast) groupCount =
        CaptureObservation.observe first.point.2 targetLast groupCount at equality
      rw [lastSame] at equality
      exact equality.symm.trans observed
    rw [result]
    simp only [RegexPikeVM.Result.map, Option.map_some]
    exact congrArg (fun value : Observation =>
      (RegexPikeVM.Result.finished (some (value, ())) : RegexPikeVM.Result Observation Unit)) publicSame

theorem returned_pike_winner_valid {input : Term} {pattern : Pattern} {length : Nat}
    (lowered : RepetitionExecution.Lowers input pattern) (checked : Graph.CheckedProgram)
    (produced : Applies program host "re:compile-authored" [input] (code checked.program))
    (probe : Probe Graph.CharacterClass String length) (eligible : Point Address length → Bool)
    (closureFuel inputFuel : Nat)
    (closureEnough : 3 * Fintype.card (Graph.Owned checked.program) + 1 ≤ closureFuel)
    (inputEnough : length + 1 ≤ inputFuel) (first : Thread (Graph.Owned checked.program) length)
    (initial : first.registers = CaptureObservation.initialRegisters first.point.2)
    (groupCount : Nat) (observation : Observation)
    (finished : (RegexPikeVM.run (Graph.graphOf checked) probe
      (fun thread => eligible (mapPoint Subtype.val thread.point)) closureFuel inputFuel [first]).map
        (fun last => CaptureObservation.observe first.point.2 last groupCount) =
          .finished (some (observation, ()))) :
    WinnerObserved pattern probe (fun thread => eligible thread.point)
        (mapThread Subtype.val first) groupCount observation ∧ observation.Valid length := by
  refine ⟨(returned_pike_winner_iff lowered checked produced probe eligible closureFuel inputFuel
    closureEnough inputEnough first groupCount observation).mp finished, ?_⟩
  exact (returned_pike_observed_value lowered checked produced probe (fun thread => eligible thread.point)
    closureFuel inputFuel first initial groupCount observation finished).2

/-- A successful physical-CST projection feeds the same actual authored
compiler and public observation theorem. Source group layout determines the
output length, even when lowering erased every capture instruction. -/
theorem projected_pike_observation {length : Nat} {input : Term} (helperFuel traversalFuel : Nat)
    (state : RegexSourceProjection.State) (tree : CettaWire.Term) (projected : RegexSourceProjection.Output)
    (projectedExactly : RegexSourceProjection.project (RegexSourceProjection.view? helperFuel)
      traversalFuel state tree = some projected)
    (lowered : RepetitionExecution.Lowers input projected.pattern)
    (checked : Graph.CheckedProgram)
    (produced : Applies program host "re:compile-authored" [input] (code checked.program))
    (probe : Probe Graph.CharacterClass String length) (eligible : Thread Address length → Bool)
    (closureFuel inputFuel : Nat) (first last : Thread (Graph.Owned checked.program) length)
    (initial : first.registers = CaptureObservation.initialRegisters first.point.2)
    (finished : RegexPikeVM.run (Graph.graphOf checked) probe
      (eligible ∘ mapThread Subtype.val) closureFuel inputFuel [first] = .finished (some (last, ()))) :
    RegexSourceProjection.Projects (RegexSourceProjection.view? helperFuel) state tree projected ∧
      SimpleObserved projected.pattern probe eligible (mapThread Subtype.val first) projected.state.nextGroup
        (CaptureObservation.observe first.point.2 last projected.state.nextGroup) ∧
      (CaptureObservation.observe first.point.2 last projected.state.nextGroup).Valid length ∧
      (CaptureObservation.observe first.point.2 last projected.state.nextGroup).captures.length = projected.state.nextGroup := by
  have attributed := RegexSourceProjection.project_sound _ traversalFuel state tree projected projectedExactly
  have observed := returned_pike_observation lowered
    checked produced probe eligible closureFuel inputFuel first last initial finished projected.state.nextGroup
  exact ⟨attributed, observed.1, observed.2, CaptureObservation.observe_layout_length _ _ _⟩

/-- The selected-CST path reaches the independently winning source
observation as well as valid public scalar and original-input byte spans. -/
theorem projected_pike_winner {text : List Char} {input : Term} (helperFuel traversalFuel : Nat)
    (state : RegexSourceProjection.State) (tree : CettaWire.Term) (projected : RegexSourceProjection.Output)
    (projectedExactly : RegexSourceProjection.project (RegexSourceProjection.view? helperFuel)
      traversalFuel state tree = some projected)
    (lowered : RepetitionExecution.Lowers input projected.pattern)
    (checked : Graph.CheckedProgram)
    (produced : Applies program host "re:compile-authored" [input] (code checked.program))
    (probe : Probe Graph.CharacterClass String text.length) (eligible : Point Address text.length → Bool)
    (closureFuel inputFuel : Nat)
    (closureEnough : 3 * Fintype.card (Graph.Owned checked.program) + 1 ≤ closureFuel)
    (inputEnough : text.length + 1 ≤ inputFuel) (first : Thread (Graph.Owned checked.program) text.length)
    (initial : first.registers = CaptureObservation.initialRegisters first.point.2)
    (observation : Observation)
    (finished : (RegexPikeVM.run (Graph.graphOf checked) probe
      (fun thread => eligible (mapPoint Subtype.val thread.point)) closureFuel inputFuel [first]).map
        (fun last => CaptureObservation.observe first.point.2 last projected.state.nextGroup) =
          .finished (some (observation, ()))) :
    RegexSourceProjection.Projects (RegexSourceProjection.view? helperFuel) state tree projected ∧
      WinnerObserved projected.pattern probe (fun thread => eligible thread.point)
        (mapThread Subtype.val first) projected.state.nextGroup observation ∧
      observation.Valid text.length ∧
      (RegexPublicSearch.byteObservation text observation).Valid (utf8Length text) := by
  have winner := returned_pike_winner_valid lowered checked produced probe eligible closureFuel inputFuel
    closureEnough inputEnough first initial projected.state.nextGroup observation finished
  exact ⟨RegexSourceProjection.project_sound _ traversalFuel state tree projected projectedExactly,
    winner.1, winner.2, RegexPublicSearch.byteObservation_valid text observation winner.2⟩

namespace Controls

private def initial (pattern : Pattern) : Thread (Graph.Owned (compile pattern)) 0 :=
  ⟨(⟨.root, by simpa [compile] using Graph.compile_entry_owned pattern⟩, 0), CaptureObservation.initialRegisters 0, []⟩

private def probe : Probe Graph.CharacterClass String 0 := ⟨fun _ _ => false, fun _ _ => false⟩

private def emptyCapture : Observation := ⟨⟨0, 0⟩, [some ⟨0, 0⟩, some ⟨0, 0⟩], []⟩
private def absentCapture : Observation := ⟨⟨0, 0⟩, [some ⟨0, 0⟩, none], [false]⟩

/-- This invokes the actual authored compiler and actual Pike driver before
concluding independent winning source meaning and valid public captures. -/
theorem authored_pike_empty_capture_public_correct :
    WinnerObserved (.capture 1 .epsilon) probe (fun _ => true)
        (mapThread Subtype.val (initial (.capture 1 .epsilon))) 2 emptyCapture ∧ emptyCapture.Valid 0 := by
  exact returned_pike_winner_valid (RepetitionExecution.canonical_source_lowers _)
    (Graph.checkedCompile (.capture 1 .epsilon)) (RepetitionExecution.compile_authored_computes
      (RepetitionExecution.canonical_source_lowers _)) probe (fun _ => true) 100 1 (by decide) (by decide)
      (initial (.capture 1 .epsilon)) rfl 2 emptyCapture (by rfl)

theorem authored_pike_skipped_capture_public_correct :
    let pattern := Pattern.optional (.capture 1 .epsilon) false
    WinnerObserved pattern probe (fun _ => true) (mapThread Subtype.val (initial pattern)) 2 absentCapture ∧
      absentCapture.Valid 0 := by
  exact returned_pike_winner_valid (RepetitionExecution.canonical_source_lowers _)
    (Graph.checkedCompile (.optional (.capture 1 .epsilon) false)) (RepetitionExecution.compile_authored_computes
      (RepetitionExecution.canonical_source_lowers _)) probe (fun _ => true) 100 1 (by decide) (by decide)
      (initial (.optional (.capture 1 .epsilon) false)) rfl 2 absentCapture (by rfl)

/-- A forged inverted public capture is excluded by the proved pipeline,
not removed by an endpoint filter in the observation adapter. -/
theorem authored_pike_cannot_return_inverted_capture :
    let pattern := Pattern.capture 1 .epsilon
    let bad : Observation := ⟨⟨0, 0⟩, [some ⟨0, 0⟩, some ⟨1, 0⟩], []⟩
    ¬ (RegexPikeVM.run (Graph.graphOf (Graph.checkedCompile pattern)) probe
        (fun _ => true) 100 1 [initial pattern]).map
      (fun last => CaptureObservation.observe 0 last 2) = .finished (some (bad, ())) := by
  dsimp only
  intro forged
  have valid := (returned_pike_observed_value (RepetitionExecution.canonical_source_lowers _)
    (Graph.checkedCompile (.capture 1 .epsilon)) (RepetitionExecution.compile_authored_computes
      (RepetitionExecution.canonical_source_lowers _)) probe (fun _ => true) 100 1
      (initial (.capture 1 .epsilon)) rfl 2 _ forged).2
  have inverted := valid.2 (some ⟨1, 0⟩) (by simp) ⟨1, 0⟩ rfl
  simp [RegexMatchObservations.Span.Valid] at inverted

end Controls

end Mettapedia.GSLT.LanguageDef.RegexSelection.Source.Observation
