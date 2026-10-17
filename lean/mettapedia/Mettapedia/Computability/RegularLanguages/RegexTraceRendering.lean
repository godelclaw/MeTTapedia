import Mettapedia.Computability.RegularLanguages.RegexIteration

/-!
# Splitting and replacement from one ordered match trace

The independent `Decomposition` relation partitions original text by concatenation
and absolute span lengths. The executable slicer is proved sound and complete for
that relation on an ordered bounded trace. Splitting returns every gap, including
the final one. Replacement consumes the same observations, not another search.

Replacement insertion is a callback on the original capture-bearing observation.
No parsed replacement-template language is asserted here. The older
`Replacement.lean` language-founded leftmost-longest observer is unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.RegularLanguages.RegexTraceRendering

open RegexMatchObservations (Observation Span)
open RegexIteration (Trace Follows Collection Cursor)

universe u
variable {α : Type u}

def slice (input : List α) (start stop : Nat) : List α :=
  (input.drop start).take (stop - start)

/-- A declarative partition: consecutive original-text pieces have exactly the
lengths and absolute boundaries reported by the observations. -/
inductive Decomposition : Nat → List α → List Observation → List (List α) → List (List α) → Prop
  | nil (offset : Nat) (remaining : List α) : Decomposition offset remaining [] [remaining] []
  | cons (offset : Nat) (gap matched remaining : List α) (observation : Observation)
      (observations : List Observation) (gaps hits : List (List α))
      (starts : observation.span.start = offset + gap.length)
      (stops : observation.span.stop = observation.span.start + matched.length)
      (rest : Decomposition observation.span.stop remaining observations gaps hits) :
      Decomposition offset (gap ++ matched ++ remaining) (observation :: observations)
        (gap :: gaps) (matched :: hits)

/-- The executable partition retains matched pieces as well as split gaps. -/
def partitionFrom (input : List α) : Nat → List Observation → List (List α) × List (List α)
  | offset, [] => ([input.drop offset], [])
  | offset, observation :: observations =>
      let rest := partitionFrom input observation.span.stop observations
      (slice input offset observation.span.start :: rest.1,
        slice input observation.span.start observation.span.stop :: rest.2)

def splitTrace (input : List α) (observations : List Observation) : List (List α) :=
  (partitionFrom input 0 observations).1

def matchedTrace (input : List α) (observations : List Observation) : List (List α) :=
  (partitionFrom input 0 observations).2

/-- Interleave gaps with inserted blocks. Legal decompositions have one more
gap than block; the other branches merely make the operation total. -/
def weave : List (List α) → List (List α) → List α
  | [], _ => []
  | gap :: gaps, [] => gap ++ gaps.flatten
  | gap :: gaps, block :: blocks => gap ++ block ++ weave gaps blocks

def renderTrace (replacement : Observation → List α) (input : List α)
    (observations : List Observation) : List α :=
  weave (splitTrace input observations) (observations.map replacement)

/-- Splitting is specified by the independently decomposed original text. -/
def Splitting (input : List α) (observations : List Observation) (gaps : List (List α)) : Prop :=
  ∃ hits, Decomposition 0 input observations gaps hits

/-- Every replacement callback sees the original observation in trace order.
Replacement text never becomes a new input to the selector. -/
def Rendering (replacement : Observation → List α) (input : List α)
    (observations : List Observation) (output : List α) : Prop :=
  ∃ gaps hits, Decomposition 0 input observations gaps hits ∧
    output = weave gaps (observations.map replacement)

theorem slice_append_drop (input : List α) {start stop : Nat} (ordered : start ≤ stop) :
    slice input start stop ++ input.drop stop = input.drop start := by
  have same : start + (stop - start) = stop := by omega
  simpa only [slice, List.drop_drop, same] using
    (List.take_append_drop (stop - start) (input.drop start))

theorem slice_length (input : List α) {start stop : Nat}
    (ordered : start ≤ stop) (bounded : stop ≤ input.length) :
    (slice input start stop).length = stop - start := by
  simp only [slice, List.length_take, List.length_drop]
  omega

theorem drop_partition (input : List α) {offset start stop : Nat}
    (before : offset ≤ start) (ordered : start ≤ stop) :
    input.drop offset = slice input offset start ++ slice input start stop ++ input.drop stop := by
  rw [List.append_assoc, slice_append_drop input ordered, slice_append_drop input before]

/-- Ordered bounded traces authorize the executable original-text partition. -/
theorem partitionFrom_sound (input : List α) {previous : Option Nat} {observations : List Observation}
    (trace : Trace input.length previous observations) :
    ∀ offset, offset ≤ input.length →
      (∀ observation ∈ observations, offset ≤ observation.span.start) →
      Decomposition offset (input.drop offset) observations
        (partitionFrom input offset observations).1 (partitionFrom input offset observations).2 := by
  induction trace with
  | nil previous => intro offset bounded starts; exact .nil offset _
  | @cons previous observation observations valid follows rest ih =>
      intro offset bounded starts
      have before := starts observation List.mem_cons_self
      have ordered := valid.1
      have remaining := ih observation.span.stop valid.2
        (rest.starts_after_previous observation.span.stop rfl)
      simpa only [partitionFrom, drop_partition input before valid.1] using
        Decomposition.cons offset (slice input offset observation.span.start)
          (slice input observation.span.start observation.span.stop)
          (input.drop observation.span.stop) observation observations
          (partitionFrom input observation.span.stop observations).1
          (partitionFrom input observation.span.stop observations).2
          (by rw [slice_length input before (valid.1.trans valid.2)]; omega)
          (by rw [slice_length input valid.1 valid.2]; omega) remaining

theorem Decomposition.unique {offset : Nat} {input : List α} {observations : List Observation}
    {gaps hits gaps' hits' : List (List α)}
    (first : Decomposition offset input observations gaps hits)
    (second : Decomposition offset input observations gaps' hits') :
    gaps = gaps' ∧ hits = hits' := by
  induction first generalizing gaps' hits' with
  | nil offset remaining => cases second; exact ⟨rfl, rfl⟩
  | cons offset gap matched remaining observation observations gaps hits starts stops rest ih =>
      generalize sourceEq : gap ++ matched ++ remaining = source at second
      cases second with
      | cons _ otherGap otherMatched otherRemaining _ _ otherGaps otherMatches otherStarts otherStops otherRest =>
          have gapLengths : gap.length = otherGap.length := by omega
          have matchLengths : matched.length = otherMatched.length := by omega
          have gapSame : gap = otherGap := by
            have taken := congrArg (List.take gap.length) (show
              gap ++ matched ++ remaining = otherGap ++ otherMatched ++ otherRemaining from sourceEq)
            rw [List.append_assoc, List.append_assoc, List.take_left, gapLengths, List.take_left] at taken
            exact taken
          subst otherGap
          have matchedSame : matched = otherMatched := by
            have taken := congrArg (fun text : List α => (text.drop gap.length).take matched.length)
              (show gap ++ matched ++ remaining = gap ++ otherMatched ++ otherRemaining from sourceEq)
            simp only [List.append_assoc, List.drop_left] at taken
            rw [List.take_left, matchLengths, List.take_left] at taken
            exact taken
          subst otherMatched
          have remainingSame : remaining = otherRemaining := by
            have dropped := congrArg (List.drop (gap.length + matched.length)) (show
              gap ++ matched ++ remaining = gap ++ matched ++ otherRemaining from sourceEq)
            rw [← List.length_append] at dropped
            simpa only [List.drop_left] using dropped
          subst otherRemaining
          obtain ⟨sameGaps, sameMatches⟩ := ih otherRest
          exact ⟨congrArg (List.cons gap) sameGaps, congrArg (List.cons matched) sameMatches⟩

theorem Decomposition.reconstruct {offset : Nat} {input : List α} {observations : List Observation}
    {gaps hits : List (List α)} (decomposition : Decomposition offset input observations gaps hits) :
    weave gaps hits = input := by
  induction decomposition with
  | nil => simp [weave]
  | cons offset gap matched remaining observation observations gaps hits starts stops rest ih =>
      simp only [weave, ih]

theorem Decomposition.gap_count {offset : Nat} {input : List α} {observations : List Observation}
    {gaps hits : List (List α)} (decomposition : Decomposition offset input observations gaps hits) :
    gaps.length = observations.length + 1 ∧ hits.length = observations.length := by
  induction decomposition with
  | nil => simp
  | cons offset gap matched remaining observation observations gaps hits starts stops rest ih =>
      simp only [List.length_cons]; omega

theorem trace_decomposition (input : List α) {observations : List Observation}
    (trace : Trace input.length none observations) :
    Decomposition 0 input observations (splitTrace input observations) (matchedTrace input observations) := by
  simpa only [List.drop_zero, splitTrace, matchedTrace] using
    partitionFrom_sound input trace 0 (Nat.zero_le _) (by intros; exact Nat.zero_le _)

/-- Preservation and reflection: any declarative partition, and only it, is
returned by the slicer on the admitted trace. -/
theorem partition_exact (input : List α) {observations : List Observation}
    (trace : Trace input.length none observations) (gaps hits : List (List α)) :
    Decomposition 0 input observations gaps hits ↔
      splitTrace input observations = gaps ∧ matchedTrace input observations = hits := by
  constructor
  · intro decomposition
    exact (trace_decomposition input trace).unique decomposition
  · rintro ⟨sameGaps, sameMatches⟩
    simpa only [sameGaps, sameMatches] using trace_decomposition input trace

theorem split_eq_gapsTrace (input : List α) {observations : List Observation}
    (trace : Trace input.length none observations) (gaps : List (List α)) :
    Splitting input observations gaps ↔ splitTrace input observations = gaps := by
  constructor
  · rintro ⟨hits, partition⟩
    exact ((partition_exact input trace gaps hits).mp partition).1
  · intro same
    exact ⟨matchedTrace input observations,
      (partition_exact input trace gaps _).mpr ⟨same, rfl⟩⟩

theorem replace_eq_renderTrace (replacement : Observation → List α) (input : List α)
    {observations : List Observation} (trace : Trace input.length none observations) (output : List α) :
    Rendering replacement input observations output ↔ renderTrace replacement input observations = output := by
  constructor
  · rintro ⟨gaps, hits, partition, result⟩
    have same := ((partition_exact input trace gaps hits).mp partition).1
    simp only [renderTrace, same, result]
  · intro result
    exact ⟨splitTrace input observations, matchedTrace input observations,
      trace_decomposition input trace, result.symm⟩

theorem reconstruct_original (input : List α) {observations : List Observation}
    (trace : Trace input.length none observations) :
    weave (splitTrace input observations) (matchedTrace input observations) = input :=
  (trace_decomposition input trace).reconstruct

theorem split_count (input : List α) {observations : List Observation}
    (trace : Trace input.length none observations) :
    (splitTrace input observations).length = observations.length + 1 :=
  (trace_decomposition input trace).gap_count.1

/-- Capture lookup retains the distinction between an absent capture and an
empty captured substring. Indices address the observation's capture slots. -/
def captureText (input : List α) (observation : Observation) (index : Nat) : Option (List α) :=
  (observation.captures[index]?).join.map (fun span => slice input span.start span.stop)

theorem captureText_absent (input : List α) (observation : Observation) (index : Nat)
    (absent : observation.captures[index]? = some none) : captureText input observation index = none := by
  simp [captureText, absent]

theorem captureText_empty (input : List α) (observation : Observation) (index position : Nat)
    (empty : observation.captures[index]? = some (some ⟨position, position⟩)) :
    captureText input observation index = some [] := by
  simp [captureText, empty, slice]

theorem partitionFrom_matches (input : List α) (offset : Nat) (observations : List Observation) :
    (partitionFrom input offset observations).2 =
      observations.map (fun observation => slice input observation.span.start observation.span.stop) := by
  induction observations generalizing offset with
  | nil => rfl
  | cons observation observations ih => simp only [partitionFrom, List.map_cons, ih]

/-- Replacing each occurrence by its own original slice reconstructs the input,
including original text crossed while suppressing an adjacent empty candidate. -/
theorem render_whole_is_identity (input : List α) {observations : List Observation}
    (trace : Trace input.length none observations) :
    renderTrace (fun observation => slice input observation.span.start observation.span.stop)
      input observations = input := by
  simpa only [renderTrace, matchedTrace, partitionFrom_matches] using reconstruct_original input trace

theorem renderTrace_congr (input : List α) (observations : List Observation)
    (first second : Observation → List α)
    (same : ∀ observation ∈ observations, first observation = second observation) :
    renderTrace first input observations = renderTrace second input observations := by
  unfold renderTrace
  congr 1
  exact List.map_congr_left same

/-- Byte slicing at transported scalar boundaries returns exactly the original
UTF-8 encoding. No normalization or per-byte empty-match advancement occurs. -/
theorem slice_utf8Bytes (input : List Char) (span : Span) (valid : span.Valid input.length) :
    slice (utf8Bytes input) (RegexIteration.byteSpan input span).start
      (RegexIteration.byteSpan input span).stop = utf8Bytes (slice input span.start span.stop) := by
  let matchSpan : MatchSpan := ⟨span.start, span.stop - span.start⟩
  have ordered := valid.1
  have endpoint : matchSpan.start + matchSpan.length = span.stop := by
    dsimp [matchSpan]
    omega
  simpa only [slice, RegexIteration.byteSpan, MatchSpan.byteStart, MatchSpan.byteEnd,
    MatchSpan.text, endpoint, matchSpan] using MatchSpan.utf8Bytes_text matchSpan input

def byteObservation (input : List Char) (observation : Observation) : Observation :=
  { span := RegexIteration.byteSpan input observation.span
    captures := observation.captures.map (Option.map (RegexIteration.byteSpan input))
    priority := observation.priority }

theorem utf8Bytes_drop (input : List Char) (offset : Nat) :
    (utf8Bytes input).drop (byteOffset input offset) = utf8Bytes (input.drop offset) := by
  have encoded := congrArg utf8Bytes (List.take_append_drop offset input)
  rw [utf8Bytes_append] at encoded
  rw [← encoded]
  exact List.drop_left' (length_utf8Bytes (input.take offset))

theorem partitionFrom_utf8Bytes (input : List Char) {previous : Option Nat}
    {observations : List Observation} (trace : Trace input.length previous observations) :
    ∀ offset, offset ≤ input.length →
      (∀ observation ∈ observations, offset ≤ observation.span.start) →
      partitionFrom (utf8Bytes input) (byteOffset input offset) (observations.map (byteObservation input)) =
        ((partitionFrom input offset observations).1.map utf8Bytes,
          (partitionFrom input offset observations).2.map utf8Bytes) := by
  induction trace with
  | nil => intros; simp [partitionFrom, utf8Bytes_drop]
  | @cons previous observation observations valid follows rest ih =>
      intro offset bounded starts
      have before := starts observation List.mem_cons_self
      have remaining := ih observation.span.stop valid.2
        (rest.starts_after_previous observation.span.stop rfl)
      have gapBytes := slice_utf8Bytes input ⟨offset, observation.span.start⟩
        ⟨before, valid.1.trans valid.2⟩
      have hitBytes := slice_utf8Bytes input observation.span valid
      simp only [RegexIteration.byteSpan] at gapBytes hitBytes
      simp only [List.map_cons, partitionFrom, byteObservation, RegexIteration.byteSpan]
      rw [remaining, gapBytes, hitBytes]

/-- Scalar splitting and byte splitting are the same original-text partition
under UTF-8 encoding, not two independently selected traces. -/
theorem splitTrace_utf8Bytes (input : List Char) {observations : List Observation}
    (trace : Trace input.length none observations) :
    splitTrace (utf8Bytes input) (observations.map (byteObservation input)) =
      (splitTrace input observations).map utf8Bytes := by
  have same := congrArg Prod.fst (partitionFrom_utf8Bytes input trace 0 (Nat.zero_le _)
    (by intros; exact Nat.zero_le _))
  simpa only [splitTrace, byteOffset, List.take_zero, utf8Length_nil] using same

theorem split_collect_exact (input : List α) (search : RegexIteration.Search input.length)
    (searchFuel fuel : Nat) {observations : List Observation} {after : Cursor}
    (complete : RegexIteration.collect input.length search searchFuel fuel RegexIteration.initial =
      Collection.complete observations after) (gaps : List (List α)) :
    Splitting input observations gaps ↔ splitTrace input observations = gaps := by
  have legal := RegexIteration.collect_legal input.length search searchFuel fuel RegexIteration.initial
    (RegexIteration.initial_valid input.length)
  rw [complete] at legal
  exact split_eq_gapsTrace input legal.1 gaps

theorem replace_collect_exact (replacement : Observation → List α) (input : List α)
    (search : RegexIteration.Search input.length) (searchFuel fuel : Nat)
    {observations : List Observation} {after : Cursor}
    (complete : RegexIteration.collect input.length search searchFuel fuel RegexIteration.initial =
      Collection.complete observations after) (output : List α) :
    Rendering replacement input observations output ↔ renderTrace replacement input observations = output := by
  have legal := RegexIteration.collect_legal input.length search searchFuel fuel RegexIteration.initial
    (RegexIteration.initial_valid input.length)
  rw [complete] at legal
  exact replace_eq_renderTrace replacement input legal.1 output

namespace Controls

private def observation (start stop : Nat) : Observation := ⟨⟨start, stop⟩, [], []⟩

private def aStarOnBaaa : RegexIteration.Search 4 := fun position =>
  if atStart : position = 0 then
    .found (observation 0 0) (by simp [observation, Span.Valid]) (by simp only [observation]; omega)
  else if beforeAs : position ≤ 1 then
    .found (observation 1 4) (by simp [observation, Span.Valid]) (by simp only [observation]; omega)
  else if bounded : position ≤ 4 then
    .found (observation 4 4) (by simp [observation, Span.Valid]) (by simp only [observation]; omega)
  else .closed

private def aStarTrace : List Observation := [observation 0 0, observation 1 4]

theorem aStar_collection_uses_one_adjacency_rule :
    RegexIteration.collect 4 aStarOnBaaa 2 4 RegexIteration.initial =
      .complete aStarTrace ⟨4, some 4, true⟩ := by decide

private theorem aStarTrace_valid : Trace 4 none aStarTrace := by
  have legal := RegexIteration.collect_legal 4 aStarOnBaaa 2 4 RegexIteration.initial
    (RegexIteration.initial_valid 4)
  rw [aStar_collection_uses_one_adjacency_rule] at legal
  exact legal.1

theorem aStar_split_retains_crossed_text_and_final_gap :
    splitTrace "baaa".toList aStarTrace = [[], "b".toList, []] := by decide

theorem aStar_replacement_suppresses_trailing_adjacent_empty :
    renderTrace (fun occurrence => '<' :: slice "baaa".toList occurrence.span.start occurrence.span.stop ++ ['>'])
      "baaa".toList aStarTrace = "<>b<aaa>".toList := by decide

theorem aStar_original_reconstruction :
    weave (splitTrace "baaa".toList aStarTrace) (matchedTrace "baaa".toList aStarTrace) = "baaa".toList :=
  reconstruct_original "baaa".toList aStarTrace_valid

/-- An extra terminal empty match is not authorized merely by being bounded
and nonoverlapping; it violates the shared iterator adjacency observation. -/
theorem trailing_adjacent_empty_is_not_a_trace :
    ¬ Trace 4 none [observation 0 0, observation 1 4, observation 4 4] := by
  intro trace
  cases trace with
  | cons _ _ rest =>
      cases rest with
      | cons _ _ last =>
          cases last with
          | cons _ follows _ =>
              have impossible := follows 4 rfl
              exact impossible.2 rfl rfl

theorem unicode_split_and_byte_spans_are_distinct :
    splitTrace "aλb".toList [observation 1 2] = ["a".toList, "b".toList] ∧
    RegexIteration.byteSpan "aλb".toList ⟨1, 2⟩ = ⟨1, 3⟩ ∧
    slice (utf8Bytes "aλb".toList) 1 3 = utf8Bytes "λ".toList := by decide

theorem unicode_literal_replacement_keeps_original_gaps :
    renderTrace (fun _ => "X".toList) "aλb".toList [observation 1 2] = "aXb".toList := by decide

theorem absent_and_empty_capture_are_not_collapsed :
    let absent : Observation := ⟨⟨0, 0⟩, [none], []⟩
    let empty : Observation := ⟨⟨0, 0⟩, [some ⟨0, 0⟩], []⟩
    captureText "λ".toList absent 0 = none ∧
      captureText "λ".toList empty 0 = some [] ∧
      captureText "λ".toList absent 0 ≠ captureText "λ".toList empty 0 := by decide

theorem inserted_text_is_not_rescanned :
    renderTrace (fun _ => "aa".toList) "a".toList [observation 0 1] = "aa".toList := by decide

end Controls

#print axioms partitionFrom_sound
#print axioms slice_append_drop
#print axioms slice_length
#print axioms drop_partition
#print axioms Decomposition.unique
#print axioms Decomposition.reconstruct
#print axioms Decomposition.gap_count
#print axioms trace_decomposition
#print axioms partition_exact
#print axioms split_eq_gapsTrace
#print axioms replace_eq_renderTrace
#print axioms reconstruct_original
#print axioms split_count
#print axioms captureText_absent
#print axioms captureText_empty
#print axioms partitionFrom_matches
#print axioms render_whole_is_identity
#print axioms renderTrace_congr
#print axioms slice_utf8Bytes
#print axioms utf8Bytes_drop
#print axioms partitionFrom_utf8Bytes
#print axioms splitTrace_utf8Bytes
#print axioms split_collect_exact
#print axioms replace_collect_exact
#print axioms Controls.aStar_collection_uses_one_adjacency_rule
#print axioms Controls.aStar_split_retains_crossed_text_and_final_gap
#print axioms Controls.aStar_replacement_suppresses_trailing_adjacent_empty
#print axioms Controls.aStar_original_reconstruction
#print axioms Controls.trailing_adjacent_empty_is_not_a_trace
#print axioms Controls.unicode_split_and_byte_spans_are_distinct
#print axioms Controls.unicode_literal_replacement_keeps_original_gaps
#print axioms Controls.absent_and_empty_capture_are_not_collapsed
#print axioms Controls.inserted_text_is_not_rescanned

end Mettapedia.Computability.RegularLanguages.RegexTraceRendering
