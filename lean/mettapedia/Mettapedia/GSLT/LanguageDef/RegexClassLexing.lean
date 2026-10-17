import Mettapedia.GSLT.LanguageDef.RegexTextIngress

/-!
# Bracketed lexical regions for extended regex text

Nested classes and the historical first-position literal `[` share prefixes.
The lexical observation retains the longest complete bracketed prefix. If
there is no complete prefix, the entire remaining input is retained so that
the syntax grammar, not trivia removal, reports the unfinished class.

This is a bracket/escape lexical language, not another regex parser. Source
rules describe individual alternatives; the executable reference propagates
their finite state set and selects the longest closing position. Native code
compresses depth sets into intervals and is checked separately.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexClassLexing

abbrev Unit := Char × Nat

structure State where
  depth : Nat
  phase : Nat := 0
  escaped : Bool := false
  deriving DecidableEq, Repr

def ordinaryPhase (phase : Nat) (char : Char) : Nat :=
  if char = '&' then (if phase = 3 then 0 else 3)
  else if char = '-' then (if phase = 4 then 0 else 4)
  else if char = '~' then (if phase = 5 then 0 else 5)
  else if char = '^' ∧ phase = 0 then 1 else 2

def Moves (before : State) (char : Char) (after : State) : Prop :=
  (before.escaped = true ∧ after = ⟨before.depth, 2, false⟩) ∨
  (before.escaped = false ∧ char = '\\' ∧ after = ⟨before.depth, 2, true⟩) ∨
  (before.escaped = false ∧ char = '[' ∧
    (after = ⟨before.depth + 1, 0, false⟩ ∨ before.phase < 2 ∧ after = ⟨before.depth, 2, false⟩)) ∨
  (before.escaped = false ∧ char = ']' ∧ 1 < before.depth ∧ after = ⟨before.depth - 1, 2, false⟩) ∨
  (before.escaped = false ∧ char ∉ ['\\','[',']'] ∧ after = ⟨before.depth, ordinaryPhase before.phase char, false⟩)

def moves (before : State) (char : Char) : List State :=
  if before.escaped then [⟨before.depth, 2, false⟩]
  else if char = '\\' then [⟨before.depth, 2, true⟩]
  else if char = '[' then ⟨before.depth + 1, 0, false⟩ ::
    (if before.phase < 2 then [⟨before.depth, 2, false⟩] else [])
  else if char = ']' then (if 1 < before.depth then [⟨before.depth - 1, 2, false⟩] else [])
  else [⟨before.depth, ordinaryPhase before.phase char, false⟩]

theorem moves_iff (before : State) (char : Char) (after : State) :
    after ∈ moves before char ↔ Moves before char after := by
  by_cases escaped : before.escaped = true
  · simp [moves, Moves, escaped, eq_comm]
  · have clear : before.escaped = false := by cases value : before.escaped <;> simp_all
    by_cases slash : char = '\\'
    · simp [moves, Moves, clear, slash, eq_comm]
    · by_cases opening : char = '['
      · by_cases first : before.phase < 2
        · simp [moves, Moves, clear, opening, first]
        · simp [moves, Moves, clear, opening, first]
      · by_cases closing : char = ']'
        · by_cases deeper : 1 < before.depth
          · simp [moves, Moves, clear, closing, deeper, eq_comm]
          · simp [moves, Moves, clear, closing, deeper]
        · simp [moves, Moves, clear, slash, opening, closing]

/-- Escape state is uniform across every live lexical alternative, so it can
be shared rather than stored separately for every possible bracket depth. -/
theorem Moves.escaped_next {before after : State} {char : Char} (source : Moves before char after) :
    after.escaped = (!before.escaped && (char == '\\')) := by
  rcases source with ⟨escaped, rfl⟩ | ⟨clear, slash, rfl⟩ |
    ⟨clear, opening, rfl | ⟨_, rfl⟩⟩ | ⟨clear, closing, _, rfl⟩ | ⟨clear, ordinary, rfl⟩
  all_goals simp_all

theorem Moves.depth_bound {before after : State} {char : Char} (source : Moves before char after) :
    after.depth ≤ before.depth + 1 := by
  rcases source with ⟨_, rfl⟩ | ⟨_, _, rfl⟩ |
    ⟨_, _, rfl | ⟨_, rfl⟩⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩
  all_goals simp <;> omega

def Closes (state : State) (char : Char) : Prop :=
  state.escaped = false ∧ state.depth = 1 ∧ char = ']'

def closes (state : State) (char : Char) : Bool :=
  !state.escaped && decide (state.depth = 1) && (char == ']')

theorem closes_iff (state : State) (char : Char) : closes state char = true ↔ Closes state char := by
  simp [closes, Closes, and_assoc]

inductive Ends : State → List Unit → Nat → Prop where
  | finish {state unit rest} (closing : Closes state unit.1) : Ends state (unit :: rest) 1
  | more {state unit rest after length} (step : Moves state unit.1 after)
      (tail : Ends after rest length) : Ends state (unit :: rest) (length + 1)

theorem Ends.positive {state : State} {input : List Unit} {length : Nat}
    (source : Ends state input length) : 0 < length := by cases source <;> omega

theorem Ends.bound {state : State} {input : List Unit} {length : Nat}
    (source : Ends state input length) : length ≤ input.length := by
  induction source with
  | finish => simp
  | more _ _ ih => simp; omega

def advance (states : List State) (char : Char) : List State :=
  (states.flatMap (moves · char)).eraseDups

theorem advance_iff (states : List State) (char : Char) (after : State) :
    after ∈ advance states char ↔ ∃ before ∈ states, Moves before char after := by
  simp [advance, moves_iff]

theorem advance_escaped_uniform (states : List State) (char : Char) (escaped : Bool)
    (uniform : ∀ before ∈ states, before.escaped = escaped) (after : State)
    (member : after ∈ advance states char) : after.escaped = (!escaped && (char == '\\')) := by
  obtain ⟨before, inside, source⟩ := (advance_iff states char after).1 member
  rw [source.escaped_next, uniform before inside]

def ends : List State → List Unit → List Nat
  | _, [] => []
  | states, unit :: rest =>
      (if states.any (closes · unit.1) then [1] else []) ++
        (ends (advance states unit.1) rest).map (· + 1)

theorem ends_iff (states : List State) (input : List Unit) (length : Nat) :
    length ∈ ends states input ↔ ∃ state ∈ states, Ends state input length := by
  induction input generalizing states length with
  | nil => simp only [ends, List.not_mem_nil, false_iff]; rintro ⟨state, _, impossible⟩; cases impossible
  | cons unit rest ih =>
      simp only [ends, List.mem_append, List.mem_map]
      constructor
      · rintro (here | ⟨before, member, same⟩)
        · split_ifs at here with present
          · simp only [List.mem_singleton] at here
            subst length
            obtain ⟨state, member, closing⟩ := List.any_eq_true.mp present
            exact ⟨state, member, .finish ((closes_iff _ _).1 closing)⟩
          · cases here
        · obtain ⟨after, memberAfter, tail⟩ := (ih _ _).1 member
          obtain ⟨state, member, step⟩ := (advance_iff _ _ _).1 memberAfter
          subst length
          exact ⟨state, member, .more step tail⟩
      · rintro ⟨state, member, source⟩
        cases source with
        | finish closing =>
            left
            have present : states.any (closes · unit.1) = true :=
              List.any_eq_true.mpr ⟨state, member, (closes_iff _ _).2 closing⟩
            simp [present]
        | more step tail =>
            right
            exact ⟨_, (ih _ _).2 ⟨_, (advance_iff _ _ _).2 ⟨state, member, step⟩, tail⟩, rfl⟩

def greatest : List Nat → Nat
  | [] => 0
  | first :: rest => max first (greatest rest)

theorem greatest_spec (values : List Nat) :
    (∀ value ∈ values, value ≤ greatest values) ∧ (greatest values = 0 ∨ greatest values ∈ values) := by
  induction values with
  | nil => simp [greatest]
  | cons first rest ih =>
      constructor
      · intro value member
        rcases List.mem_cons.mp member with same | inside
        · subst value; exact Nat.le_max_left _ _
        · exact (ih.1 value inside).trans (Nat.le_max_right _ _)
      · by_cases bigger : first ≤ greatest rest
        · rw [greatest, max_eq_right bigger]
          exact ih.2.imp_right (List.mem_cons_of_mem first)
        · right
          simp [greatest, max_eq_left (by omega : greatest rest ≤ first)]

def initial : State := ⟨1, 0, false⟩

def RegionLength (input : List Unit) (length : Nat) : Prop :=
  (Ends initial input length ∧ ∀ other, Ends initial input other → other ≤ length) ∨
  ((¬ ∃ other, Ends initial input other) ∧ length = input.length)

def regionLength (input : List Unit) : Nat :=
  let best := greatest (ends [initial] input)
  if best = 0 then input.length else best

theorem regionLength_source (input : List Unit) : RegionLength input (regionLength input) := by
  have greatest := greatest_spec (ends [initial] input)
  by_cases zero : RegexClassLexing.greatest (ends [initial] input) = 0
  · right
    refine ⟨?_, by simp [regionLength, zero]⟩
    rintro ⟨other, source⟩
    have bound := greatest.1 other ((ends_iff _ _ _).2 ⟨initial, by simp, source⟩)
    rw [zero] at bound
    have positive := source.positive
    omega
  · left
    have member := greatest.2.resolve_left zero
    obtain ⟨state, same, source⟩ := (ends_iff _ _ _).1 member
    simp only [List.mem_singleton] at same
    subst state
    refine ⟨by simpa [regionLength, zero] using source, ?_⟩
    intro other source
    simpa [regionLength, zero] using greatest.1 other ((ends_iff _ _ _).2 ⟨initial, by simp, source⟩)

theorem RegionLength.unique {input : List Unit} {left right : Nat}
    (before : RegionLength input left) (after : RegionLength input right) : left = right := by
  rcases before with ⟨source, maximal⟩ | ⟨absent, same⟩
  · rcases after with ⟨other, maximalOther⟩ | ⟨absent, _⟩
    · exact Nat.le_antisymm (maximalOther _ source) (maximal _ other)
    · exact False.elim (absent ⟨left, source⟩)
  · rcases after with ⟨source, _⟩ | ⟨_, other⟩
    · exact False.elim (absent ⟨right, source⟩)
    · exact same.trans other.symm

def Region (input retained remaining : List Unit) : Prop :=
  ∃ length, RegionLength input length ∧ retained = input.take length ∧ remaining = input.drop length

def readRegion (input : List Unit) : List Unit × List Unit :=
  (input.take (regionLength input), input.drop (regionLength input))

theorem readRegion_iff (input retained remaining : List Unit) :
    readRegion input = (retained, remaining) ↔ Region input retained remaining := by
  constructor
  · intro same
    cases same
    exact ⟨regionLength input, regionLength_source input, rfl, rfl⟩
  · rintro ⟨length, source, rfl, rfl⟩
    have same := (regionLength_source input).unique source
    simp [readRegion, same]

theorem Region.partition {input retained remaining : List Unit} (source : Region input retained remaining) :
    retained ++ remaining = input := by
  obtain ⟨length, _, rfl, rfl⟩ := source
  exact List.take_append_drop length input

namespace Controls

private def length (text : String) := regionLength text.toList.zipIdx

theorem literal_open_bracket_keeps_its_historical_close : length "[]" = 2 := by decide +kernel
theorem nested_empty_class_uses_the_later_close : length "[]]" = 3 := by decide +kernel
theorem nested_class_retains_internal_trivia : length "[a] # ] tail" = 7 := by decide +kernel
theorem escaped_close_is_not_a_region_end : length "\\]a] tail" = 4 := by decide +kernel
theorem unfinished_brackets_are_retained_for_the_grammar : length "[a tail" = 7 := by decide +kernel

end Controls

end Mettapedia.GSLT.LanguageDef.RegexClassLexing
