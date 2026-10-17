import Mettapedia.GSLT.LanguageDef.RegexSelectionGraph

/-!
# Structural operational semantics of selection patterns

The source rules below inspect typed pattern constructors, source occurrences,
and their continuations. They do not run a compiler or inspect emitted rows.
The two decisions of a star have distinct occurrence phases; a capture closes
at its own phase, and repetitions reuse the source capture identity.

The compiler theorem preserves and reflects every authorized control operation,
including priorities, assertions and capture writes. Recognition erasure is
not used in this correspondence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexSelection.Source

open Mettapedia.Computability.RegularLanguages
open RegexTaggedGraph
open Graph (CharacterClass captureSlot nodeOf mapNode)

abbrev Operation := Node Address CharacterClass String Unit

/-- A preferred branch is first, whether the preference is greedy or lazy. -/
def ordered (body continuation : Address) (greedy : Bool) : Operation :=
  if greedy then .choice body continuation else .choice continuation body

/-- Source operational rules at structural occurrences. A continuation is an
explicit destination supplied by the enclosing source construct. -/
inductive At : Pattern → Address → Address → Address → Operation → Prop where
  | zero (continuation occurrence) : At .zero continuation occurrence occurrence .dead
  | epsilon (continuation occurrence) :
      At .epsilon continuation occurrence occurrence (.jump continuation)
  | literal (scalar continuation occurrence) :
      At (.literal scalar) continuation occurrence occurrence (.consume (.scalar scalar) continuation)
  | any (continuation occurrence) :
      At .any continuation occurrence occurrence (.consume .any continuation)
  | class_ (ranges continuation occurrence) :
      At (.class_ ranges) continuation occurrence occurrence (.consume (.ranges ranges) continuation)
  | assertion (name continuation occurrence) :
      At (.assertion name) continuation occurrence occurrence (.assertion name continuation)
  | seqEntry (first second continuation occurrence) :
      At (.seq first second) continuation occurrence occurrence (.jump (.left occurrence))
  | seqLeft {first second continuation occurrence pc operation} :
      At first (.right occurrence) (.left occurrence) pc operation →
      At (.seq first second) continuation occurrence pc operation
  | seqRight {first second continuation occurrence pc operation} :
      At second continuation (.right occurrence) pc operation →
      At (.seq first second) continuation occurrence pc operation
  | altEntry (first second continuation occurrence) :
      At (.alt first second) continuation occurrence occurrence
        (.choice (.left occurrence) (.right occurrence))
  | altLeft {first second continuation occurrence pc operation} :
      At first continuation (.left occurrence) pc operation →
      At (.alt first second) continuation occurrence pc operation
  | altRight {first second continuation occurrence pc operation} :
      At second continuation (.right occurrence) pc operation →
      At (.alt first second) continuation occurrence pc operation
  | optionalEntry (body greedy continuation occurrence) :
      At (.optional body greedy) continuation occurrence occurrence
        (ordered (.body occurrence) continuation greedy)
  | optionalBody {body greedy continuation occurrence pc operation} :
      At body continuation (.body occurrence) pc operation →
      At (.optional body greedy) continuation occurrence pc operation
  | starEntry (body greedy continuation occurrence) :
      At (.star body greedy) continuation occurrence occurrence
        (ordered (.body occurrence) continuation greedy)
  | starRepeat (body greedy continuation occurrence) :
      At (.star body greedy) continuation occurrence (.loop occurrence)
        (ordered (.body occurrence) continuation greedy)
  | starBody {body greedy continuation occurrence pc operation} :
      At body (.loop occurrence) (.body occurrence) pc operation →
      At (.star body greedy) continuation occurrence pc operation
  | plusEntry (body greedy continuation occurrence) :
      At (.plus body greedy) continuation occurrence occurrence (.jump (.body occurrence))
  | plusRepeat (body greedy continuation occurrence) :
      At (.plus body greedy) continuation occurrence (.loop occurrence)
        (ordered (.body occurrence) continuation greedy)
  | plusBody {body greedy continuation occurrence pc operation} :
      At body (.loop occurrence) (.body occurrence) pc operation →
      At (.plus body greedy) continuation occurrence pc operation
  | captureEntry (group body continuation occurrence) :
      At (.capture group body) continuation occurrence occurrence
        (.save (captureSlot group .start) (.body occurrence))
  | captureClose (group body continuation occurrence) :
      At (.capture group body) continuation occurrence (.close occurrence)
        (.save (captureSlot group .finish) continuation)
  | captureBody {group body continuation occurrence pc operation} :
      At body (.close occurrence) (.body occurrence) pc operation →
      At (.capture group body) continuation occurrence pc operation

/-- A complete source pattern finishes only at its supplied outer continuation. -/
inductive Authorizes (pattern : Pattern) : Address → Operation → Prop where
  | finish : Authorizes pattern .ending (.accept ())
  | inside {pc operation} : At pattern .ending .root pc operation → Authorizes pattern pc operation

theorem nodeOf_choice (occurrence body continuation : Address) (greedy : Bool) :
    nodeOf (choice occurrence body continuation greedy) id = ordered body continuation greedy := by
  cases greedy <;> rfl

/-- Every source operation has its actual emitted row. This is preservation of
the source rules, not a definition of those rules using emitted programs. -/
theorem At.emitted {pattern : Pattern} {continuation occurrence pc : Address} {operation : Operation}
    (source : At pattern continuation occurrence pc operation) :
    ∃ row ∈ emit pattern continuation occurrence, row.address = pc ∧ nodeOf row id = operation := by
  induction source with
  | zero continuation occurrence => exact ⟨.fail occurrence, by simp [emit], rfl, rfl⟩
  | epsilon continuation occurrence => exact ⟨.jump occurrence continuation, by simp [emit], rfl, rfl⟩
  | literal scalar continuation occurrence =>
      exact ⟨.scalar occurrence scalar continuation, by simp [emit], rfl, rfl⟩
  | any continuation occurrence => exact ⟨.any occurrence continuation, by simp [emit], rfl, rfl⟩
  | class_ ranges continuation occurrence =>
      exact ⟨.class_ occurrence ranges continuation, by simp [emit], rfl, rfl⟩
  | assertion name continuation occurrence =>
      exact ⟨.assertion occurrence name continuation, by simp [emit], rfl, rfl⟩
  | seqEntry first second continuation occurrence =>
      exact ⟨.jump occurrence (.left occurrence), by simp [emit], rfl, rfl⟩
  | seqLeft _ ih | seqRight _ ih | altLeft _ ih | altRight _ ih =>
      obtain ⟨row, member, same, operation⟩ := ih
      exact ⟨row, by simp [emit, member], same, operation⟩
  | altEntry first second continuation occurrence =>
      exact ⟨.split occurrence (.left occurrence) (.right occurrence), by simp [emit], rfl, rfl⟩
  | optionalEntry body greedy continuation occurrence | starEntry body greedy continuation occurrence =>
      refine ⟨choice occurrence (.body occurrence) continuation greedy, by simp [emit], ?_, ?_⟩
      · cases greedy <;> rfl
      · exact nodeOf_choice _ _ _ _
  | optionalBody _ ih | starBody _ ih | plusBody _ ih | captureBody _ ih =>
      obtain ⟨row, member, same, operation⟩ := ih
      exact ⟨row, by simp [emit, member], same, operation⟩
  | starRepeat body greedy continuation occurrence | plusRepeat body greedy continuation occurrence =>
      refine ⟨choice (.loop occurrence) (.body occurrence) continuation greedy, by simp [emit], ?_, ?_⟩
      · cases greedy <;> rfl
      · exact nodeOf_choice _ _ _ _
  | plusEntry body greedy continuation occurrence =>
      exact ⟨.jump occurrence (.body occurrence), by simp [emit], rfl, rfl⟩
  | captureEntry group body continuation occurrence =>
      exact ⟨.save occurrence group .start (.body occurrence), by simp [emit], rfl, rfl⟩
  | captureClose group body continuation occurrence =>
      exact ⟨.save (.close occurrence) group .finish continuation, by simp [emit], rfl, rfl⟩

/-- No invented operation occurs in a compiled fragment. Both repetition phases
and both capture boundaries reflect to their respective source rules. -/
theorem emitted_source (pattern : Pattern) (continuation occurrence : Address)
    (row : Instruction) (member : row ∈ emit pattern continuation occurrence) :
    At pattern continuation occurrence row.address (nodeOf row id) := by
  induction pattern generalizing continuation occurrence row with
  | zero | epsilon | literal _ | any | class_ _ | assertion _ =>
      simp only [emit, List.mem_singleton] at member
      subst row
      first | exact .zero _ _ | exact .epsilon _ _ | exact .literal _ _ _ |
        exact .any _ _ | exact .class_ _ _ _ | exact .assertion _ _ _
  | seq first second ihFirst ihSecond =>
      simp only [emit, List.mem_cons, List.mem_append] at member
      rcases member with same | member | member
      · subst row; exact .seqEntry _ _ _ _
      · exact .seqLeft (ihFirst _ _ _ member)
      · exact .seqRight (ihSecond _ _ _ member)
  | alt first second ihFirst ihSecond =>
      simp only [emit, List.mem_cons, List.mem_append] at member
      rcases member with same | member | member
      · subst row; exact .altEntry _ _ _ _
      · exact .altLeft (ihFirst _ _ _ member)
      · exact .altRight (ihSecond _ _ _ member)
  | optional body greedy ih =>
      simp only [emit, List.mem_cons] at member
      rcases member with same | member
      · subst row
        cases greedy <;> exact .optionalEntry _ _ _ _
      · exact .optionalBody (ih _ _ _ member)
  | star body greedy ih =>
      simp only [emit, List.mem_cons] at member
      rcases member with same | same | member
      · subst row; cases greedy <;> exact .starEntry _ _ _ _
      · subst row; cases greedy <;> exact .starRepeat _ _ _ _
      · exact .starBody (ih _ _ _ member)
  | plus body greedy ih =>
      simp only [emit, List.mem_cons] at member
      rcases member with same | same | member
      · subst row; exact .plusEntry _ _ _ _
      · subst row; cases greedy <;> exact .plusRepeat _ _ _ _
      · exact .plusBody (ih _ _ _ member)
  | capture group body ih =>
      simp only [emit, List.mem_cons] at member
      rcases member with same | same | member
      · subst row; exact .captureEntry _ _ _ _
      · subst row; exact .captureClose _ _ _ _
      · exact .captureBody (ih _ _ _ member)

theorem at_iff_emitted (pattern : Pattern) (continuation occurrence pc : Address)
    (operation : Operation) :
    At pattern continuation occurrence pc operation ↔
      ∃ row ∈ emit pattern continuation occurrence, row.address = pc ∧ nodeOf row id = operation := by
  constructor
  · exact At.emitted
  · rintro ⟨row, member, rfl, rfl⟩
    exact emitted_source pattern continuation occurrence row member

theorem authorizes_iff_compiled (pattern : Pattern) (pc : Address) (operation : Operation) :
    Authorizes pattern pc operation ↔
      ∃ row ∈ (compile pattern).rows, row.address = pc ∧ nodeOf row id = operation := by
  constructor
  · intro source
    cases source with
    | finish => exact ⟨.accept .ending, by simp [compile], rfl, rfl⟩
    | inside source =>
        obtain ⟨row, member, same, operation⟩ := source.emitted
        exact ⟨row, by simp [compile, member], same, operation⟩
  · rintro ⟨row, member, rfl, rfl⟩
    simp only [compile, List.mem_cons] at member
    rcases member with rfl | member
    · exact .finish
    · exact .inside (emitted_source pattern .ending .root row member)

/-- A source-authorized control point is an actual owned compiled occurrence. -/
theorem Authorizes.owned {pattern : Pattern} {pc : Address} {operation : Operation}
    (source : Authorizes pattern pc operation) : pc ∈ Graph.addresses (compile pattern) := by
  obtain ⟨row, member, same, _⟩ := (authorizes_iff_compiled pattern pc operation).mp source
  simp only [Graph.addresses, List.mem_toFinset]
  exact List.mem_map.mpr ⟨row, member, same⟩

/-- Source rules cannot authorize two different instructions at an occurrence. -/
theorem authorizes_unique (pattern : Pattern) (pc : Address) (first second : Operation)
    (one : Authorizes pattern pc first) (two : Authorizes pattern pc second) : first = second := by
  obtain ⟨row, member, same, operation⟩ := (authorizes_iff_compiled pattern pc first).mp one
  obtain ⟨other, otherMember, otherSame, otherOperation⟩ :=
    (authorizes_iff_compiled pattern pc second).mp two
  have rows := List.inj_on_of_nodup_map (Graph.compile_addresses_nodup pattern)
    member otherMember (same.trans otherSame.symm)
  subst other
  exact operation.symm.trans otherOperation

/-- The actual checked graph and the independent source rules agree on every
owned state; the address resolver's default case is not involved. -/
theorem checkedGraph_source (pattern : Pattern) (pc : Graph.Owned (compile pattern)) :
    Authorizes pattern pc.val
      (mapNode Subtype.val (Graph.graphOf (Graph.checkedCompile pattern) pc)) := by
  obtain ⟨row, found, member, same⟩ := Graph.lookup_defined (compile pattern) pc.val pc.property
  have pcSame : (⟨row.address, by
      simp only [Graph.addresses, List.mem_toFinset]
      exact List.mem_map.mpr ⟨row, member, rfl⟩⟩ : Graph.Owned (compile pattern)) = pc :=
    Subtype.ext same
  have graphSame : mapNode Subtype.val (Graph.graphOf (Graph.checkedCompile pattern) pc) =
      nodeOf row id := by
    have result := Graph.graphOf_compiled_row pattern row member
    convert result using 1
    exact congrArg (fun state => mapNode Subtype.val (Graph.graphOf (Graph.checkedCompile pattern) state))
      pcSame.symm
  rw [graphSame]
  exact (authorizes_iff_compiled pattern pc.val (nodeOf row id)).mpr ⟨row, member, same, rfl⟩

namespace Controls

/-- The nullable star's initial and repeated decisions are different source
occurrences even when they authorize equal operations. -/
theorem nullable_star_phases :
    At (.star .epsilon true) .ending .root .root (.choice (.body .root) .ending) ∧
    At (.star .epsilon true) .ending .root (.loop .root) (.choice (.body .root) .ending) ∧
    Address.root ≠ .loop .root :=
  ⟨.starEntry _ _ _ _, .starRepeat _ _ _ _, by decide⟩

/-- Capture identity survives the body's source execution. Its close phase
targets the enclosing continuation, not a new or freshly numbered capture. -/
theorem capture_boundaries :
    At (.capture 7 .epsilon) .ending .root .root (.save 14 (.body .root)) ∧
    At (.capture 7 .epsilon) .ending .root (.body .root) (.jump (.close .root)) ∧
    At (.capture 7 .epsilon) .ending .root (.close .root) (.save 15 .ending) :=
  ⟨.captureEntry _ _ _ _, .captureBody (.epsilon _ _), .captureClose _ _ _ _⟩

/-- A source assertion cannot acquire the behavior of an unconditional jump. -/
theorem assertion_not_erased :
    ¬ Authorizes (.assertion "word-boundary") .root (.jump .ending) := by
  intro invented
  have actual : Authorizes (.assertion "word-boundary") .root
      (.assertion "word-boundary" .ending) := .inside (.assertion _ _ _)
  have impossible := authorizes_unique _ _ _ _ invented actual
  cases impossible

/-- Forward preservation alone would not rule out this invented acceptance. -/
theorem zero_no_invented_accept : ¬ Authorizes .zero .root (.accept ()) := by
  intro invented
  have actual : Authorizes .zero .root .dead := .inside (.zero _ _)
  have impossible := authorizes_unique _ _ _ _ invented actual
  cases impossible

end Controls

end Mettapedia.GSLT.LanguageDef.RegexSelection.Source
