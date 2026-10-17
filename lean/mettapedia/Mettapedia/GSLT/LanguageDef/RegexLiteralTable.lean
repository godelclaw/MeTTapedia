import Mettapedia.GSLT.LanguageDef.RegexLiteralGraphPlan
import Mettapedia.GSLT.Parsing.TrieLiteralSelection

/-!
# Exact extraction of literal alternatives from an admitted graph

Extraction retains literal scalar words, original branch histories and actual
accepting program counters. Interpreting the extracted table yields exactly
the ordered final threads of the independent admitted-graph interpretation.
This bridges the table used for trie preparation to actual tagged executions;
it does not prove a native admission implementation correct.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexLiteralTable

open Mettapedia.Computability.RegularLanguages
open RegexTaggedGraph
open OrderedGraphSearch (Probe successor)
open RegexLiteralGraphPlan

universe u

structure Entry (State : Type u) where
  word : List Nat
  priority : List Bool
  terminal : State

def prefixScalar {State : Type u} (scalar : Nat) (entry : Entry State) : Entry State :=
  {entry with word := scalar :: entry.word}

def prefixChoice {State : Type u} (choice : Bool) (entry : Entry State) : Entry State :=
  {entry with priority := choice :: entry.priority}

def extract {State : Type u} : Plan State → List (Entry State)
  | .fail _ => []
  | .accept state => [⟨[], [], state⟩]
  | .jump _ child => extract child
  | .scalar _ value child => (extract child).map (prefixScalar value)
  | .branch _ left right =>
      (extract left).map (prefixChoice false) ++ (extract right).map (prefixChoice true)

def consumeWord {length : Nat} (probe : Probe RegexSelection.Graph.CharacterClass String length) :
    Fin (length + 1) → List Nat → Option (Fin (length + 1))
  | position, [] => some position
  | position, scalar :: rest =>
      if probe.contains (.scalar scalar) position then
        (successor position).bind (fun after => consumeWord probe after rest)
      else none

/-- The literal interpretation of an original scalar haystack. Other classes
are irrelevant to this admitted profile and are not silently approximated. -/
def literalProbe (input : List Nat) : Probe RegexSelection.Graph.CharacterClass String input.length :=
  ⟨fun class_ position => match class_ with
    | .scalar scalar => if within : position.val < input.length then input[position.val] == scalar else false
    | _ => false, fun _ _ => false⟩

theorem consumeWord_some_iff (input word : List Nat)
    (first last : Fin (input.length + 1)) :
    consumeWord (literalProbe input) first word = some last ↔
      word <+: input.drop first.val ∧ last.val = first.val + word.length := by
  induction word generalizing first with
  | nil =>
      simp only [consumeWord, Option.some.injEq, List.length_nil, Nat.add_zero, List.nil_prefix, true_and]
      exact ⟨fun equal => by simp [← equal], fun equal => Fin.ext equal.symm⟩
  | cons scalar rest ih =>
      by_cases within : first.val < input.length
      · let next : Fin (input.length + 1) := ⟨first.val + 1, by omega⟩
        have advanced : successor first = some next := by simp [successor, within, next]
        by_cases same : input[first.val] = scalar
        · have contains : (literalProbe input).contains (.scalar scalar) first = true := by
            simp [literalProbe, within, same]
          rw [consumeWord, contains, if_pos rfl, advanced, Option.bind_some, ih]
          rw [List.drop_eq_getElem_cons within]
          simp only [same, List.cons_prefix_cons, List.length_cons, true_and]
          dsimp only [next]
          constructor <;> rintro ⟨accepted, length⟩ <;> exact ⟨accepted, by omega⟩
        · have contains : (literalProbe input).contains (.scalar scalar) first = false := by
            simp [literalProbe, within, same]
          rw [consumeWord, contains, if_neg Bool.false_ne_true]
          simp only [reduceCtorEq, false_iff, not_and]
          intro prefixed
          rw [List.drop_eq_getElem_cons within, List.cons_prefix_cons] at prefixed
          exact False.elim (same prefixed.1.symm)
      · have ended : input.length ≤ first.val := by omega
        simp [consumeWord, literalProbe, within, List.drop_eq_nil_of_le ended]

def finalThread {State : Type u} {length : Nat} (first : Thread State length)
    (entry : Entry State) (position : Fin (length + 1)) : Thread State length :=
  ⟨(entry.terminal, position), first.registers, first.choices ++ entry.priority⟩

def interpret {State : Type u} {length : Nat}
    (probe : Probe RegexSelection.Graph.CharacterClass String length)
    (eligible : Thread State length → Bool) (first : Thread State length) (entry : Entry State) :
    Option (Thread State length) :=
  (consumeWord probe first.point.2 entry.word).bind (fun position =>
    let last := finalThread first entry position
    if eligible last then some last else none)

def endpointEligible {State : Type u} (full : Bool) (length : Nat) : Thread State length → Bool :=
  fun thread => !full || thread.point.2.val == length

theorem interpret_literal_some_iff {State : Type u} (full : Bool) (input : List Nat)
    (first : Thread State input.length) (entry : Entry State) :
    (interpret (literalProbe input) (endpointEligible full input.length) first entry).isSome = true ↔
      entry.word <+: input.drop first.point.2.val ∧
        (full = true → entry.word = input.drop first.point.2.val) := by
  constructor
  · intro found
    cases consumed : consumeWord (literalProbe input) first.point.2 entry.word with
    | none => simp [interpret, consumed] at found
    | some position =>
        obtain ⟨prefixed, endpoint⟩ :=
          (consumeWord_some_iff input entry.word first.point.2 position).mp consumed
        refine ⟨prefixed, ?_⟩
        intro all
        have atEnd : position.val = input.length := by
          simpa [interpret, consumed, endpointEligible, all, finalThread] using found
        apply prefixed.eq_of_length
        simp only [List.length_drop]
        omega
  · rintro ⟨prefixed, fullWord⟩
    have fits := prefixed.length_le
    simp only [List.length_drop] at fits
    have within := first.point.2.isLt
    let position : Fin (input.length + 1) := ⟨first.point.2.val + entry.word.length, by omega⟩
    have consumed : consumeWord (literalProbe input) first.point.2 entry.word = some position :=
      (consumeWord_some_iff input entry.word first.point.2 position).mpr ⟨prefixed, rfl⟩
    have allowed : endpointEligible full input.length (finalThread first entry position) = true := by
      cases full with
      | false => rfl
      | true =>
          have length := congrArg List.length (fullWord rfl)
          simp only [List.length_drop] at length
          simp only [endpointEligible, Bool.not_true, Bool.false_or, finalThread, beq_iff_eq]
          dsimp only [position]
          omega
    simp [interpret, consumed, allowed]

theorem interpret_at {State : Type u} {length : Nat}
    (probe : Probe RegexSelection.Graph.CharacterClass String length)
    (eligible : Thread State length → Bool) (first : Thread State length) (entry : Entry State)
    (state : State) :
    interpret probe eligible (first.at state) entry = interpret probe eligible first entry := rfl

theorem interpret_branch {State : Type u} {length : Nat}
    (probe : Probe RegexSelection.Graph.CharacterClass String length)
    (eligible : Thread State length → Bool) (first : Thread State length) (entry : Entry State)
    (state : State) (bit : Bool) :
    interpret probe eligible first (prefixChoice bit entry) =
      interpret probe eligible (first.branch state bit) entry := by
  simp [interpret, prefixChoice, finalThread, Thread.branch, Thread.at, List.append_assoc]
  rfl

theorem interpret_scalar {State : Type u} {length : Nat}
    (probe : Probe RegexSelection.Graph.CharacterClass String length)
    (eligible : Thread State length → Bool) (first : Thread State length) (entry : Entry State)
    (state : State) (scalar : Nat) :
    interpret probe eligible first (prefixScalar scalar entry) =
      if probe.contains (.scalar scalar) first.point.2 then
        (successor first.point.2).bind (fun after =>
          interpret probe eligible {first with point := (state, after)} entry)
      else none := by
  cases contains : probe.contains (.scalar scalar) first.point.2
  · simp [interpret, prefixScalar, consumeWord, contains]
  · cases advanced : successor first.point.2
    · simp [interpret, prefixScalar, consumeWord, contains, advanced, finalThread]
    · simp [interpret, prefixScalar, consumeWord, contains, advanced, finalThread]
      rfl

theorem evaluate_values {State : Type u} {length : Nat}
    (probe : Probe RegexSelection.Graph.CharacterClass String length)
    (eligible : Thread State length → Bool) (plan : Plan State)
    (first : Thread State length) (entry : first.point.1 = root plan) :
    (evaluate probe eligible plan first).map RegexRelationEnumeration.Occurrence.value =
      (extract plan).filterMap (interpret probe eligible first) := by
  induction plan generalizing first with
  | fail state => simp [evaluate, extract]
  | accept state =>
      have same : finalThread first (⟨[], [], state⟩ : Entry State) first.point.2 = first := by
        cases first with
        | mk point registers choices =>
            cases point with
            | mk pc position => simp [root] at entry; simp [finalThread, ← entry]
      cases allowed : eligible first <;>
        simp only [evaluate, extract, List.filterMap_cons, List.filterMap_nil,
          interpret, consumeWord, Option.bind_some, same, allowed] <;> rfl
  | jump state child ih =>
      have equalAt : interpret probe eligible (first.at (root child)) = interpret probe eligible first :=
        funext (fun row => interpret_at probe eligible first row _)
      simpa [evaluate, extract, List.map_map, Function.comp_def, RegexRelationEnumeration.prepend, equalAt]
        using ih (first.at (root child)) rfl
  | scalar state scalar child ih =>
      have character := fun row => interpret_scalar probe eligible first row (root child) scalar
      cases contains : probe.contains (.scalar scalar) first.point.2
      · simp [evaluate, extract, List.filterMap_map, character, contains]
      · cases advanced : successor first.point.2 with
        | none =>
            simp [evaluate, extract, List.filterMap_map, character, contains, advanced]
        | some position =>
            simpa [evaluate, extract, List.map_map, List.filterMap_map, Function.comp_def,
              RegexRelationEnumeration.prepend, character, contains, advanced] using
              ih {first with point := (root child, position)} rfl
  | branch state left right ihLeft ihRight =>
      simp only [evaluate, extract, List.map_append, List.map_map, List.filterMap_append,
        List.filterMap_map, Function.comp_def, RegexRelationEnumeration.prepend]
      rw [ihLeft _ rfl, ihRight _ rfl]
      have firstBranch := fun row => interpret_branch probe eligible first row (root left) false
      have secondBranch := fun row => interpret_branch probe eligible first row (root right) true
      simp only [firstBranch, secondBranch]

/-- A valid actual graph plan permits neither invented nor omitted final
threads when its literal table is prepared. All capture registers are retained. -/
theorem table_trace_iff {State : Type u} {length : Nat}
    (graph : State → Node State RegexSelection.Graph.CharacterClass String Unit)
    (probe : Probe RegexSelection.Graph.CharacterClass String length)
    (eligible : Thread State length → Bool) (plan : Plan State) (valid : Valid graph plan)
    (first : Thread State length) (entry : first.point.1 = root plan) (last : Thread State length) :
    last ∈ (extract plan).filterMap (interpret probe eligible first) ↔
      ∃ bits points, RegexSelectionCorrespondence.Trace graph probe eligible first bits points last () := by
  rw [← evaluate_values probe eligible plan first entry, List.mem_map]
  constructor
  · rintro ⟨answer, present, rfl⟩
    exact ⟨answer.choices, answer.points,
      evaluate_sound graph probe eligible plan valid first entry answer present⟩
  · rintro ⟨bits, points, trace⟩
    exact ⟨⟨last, bits, points⟩,
      evaluate_complete graph probe eligible plan valid first entry bits points last trace, rfl⟩

end Mettapedia.GSLT.LanguageDef.RegexLiteralTable
