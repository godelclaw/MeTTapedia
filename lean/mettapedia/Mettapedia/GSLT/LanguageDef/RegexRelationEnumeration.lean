import Mettapedia.GSLT.LanguageDef.RegexObservationKernel

/-!
# Occurrence-preserving simple-path regex enumeration

Outer paths are enumerated, not nonoverlapping matches. Nested observations
are atomic actions already interpreted by the intrinsic observation kernel.
The cycle key is explicit: regular and capture-dependent profiles need not
have the same key. Equal projected values remain distinct list occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexRelationEnumeration

open RegexObservationTrace (ObservedAction)

universe u v

inductive Trace {State : Type u} {Key : Type v}
    (step : State → ObservedAction State) (key : State → Key) (eligible : State → Bool) :
    State → List Bool → List Key → State → Prop where
  | done {first} : step first = .accept → eligible first = true →
      Trace step key eligible first [] [key first] first
  | next {first target leading bits points last} : step first = .next target leading →
      Trace step key eligible target bits points last →
      Trace step key eligible first (leading ++ bits) (key first :: points) last
  | left {first left right bits points last} : step first = .branch left right →
      Trace step key eligible left bits points last →
      Trace step key eligible first (false :: bits) (key first :: points) last
  | right {first left right bits points last} : step first = .branch left right →
      Trace step key eligible right bits points last →
      Trace step key eligible first (true :: bits) (key first :: points) last

structure Occurrence (State : Type u) (Key : Type v) where
  value : State
  choices : List Bool
  points : List Key

def prepend {State : Type u} {Key : Type v} (bits : List Bool) (point : Key)
    (occurrence : Occurrence State Key) : Occurrence State Key :=
  ⟨occurrence.value, bits ++ occurrence.choices, point :: occurrence.points⟩

def Fresh {Key : Type v} (seen points : List Key) : Prop :=
  ∀ point ∈ points, point ∉ seen

def Source {State : Type u} {Key : Type v}
    (step : State → ObservedAction State) (key : State → Key) (eligible : State → Bool)
    (seen : List Key) (first : State) (occurrence : Occurrence State Key) : Prop :=
  Trace step key eligible first occurrence.choices occurrence.points occurrence.value ∧
    occurrence.points.Nodup ∧ Fresh seen occurrence.points

/-- Internal finite-depth unfolding. Public completeness below earns its
depth from the number of distinct possible cycle keys. -/
def enumerate {State : Type u} {Key : Type v} [DecidableEq Key]
    (step : State → ObservedAction State) (key : State → Key) (eligible : State → Bool) :
    Nat → List Key → State → List (Occurrence State Key)
  | 0, _, _ => []
  | depth + 1, seen, first =>
      if key first ∈ seen then [] else
        match step first with
        | .dead => []
        | .accept => if eligible first then [⟨first, [], [key first]⟩] else []
        | .next target bits =>
            (enumerate step key eligible depth (key first :: seen) target).map (prepend bits (key first))
        | .branch left right =>
            (enumerate step key eligible depth (key first :: seen) left).map (prepend [false] (key first)) ++
            (enumerate step key eligible depth (key first :: seen) right).map (prepend [true] (key first))

theorem source_prepend {State : Type u} {Key : Type v}
    (step : State → ObservedAction State) (key : State → Key) (eligible : State → Bool)
    (seen : List Key) (first target : State) (bits : List Bool)
    (following : ∀ rest points last, Trace step key eligible target rest points last →
      Trace step key eligible first (bits ++ rest) (key first :: points) last)
    (unseen : key first ∉ seen) (occurrence : Occurrence State Key)
    (source : Source step key eligible (key first :: seen) target occurrence) :
    Source step key eligible seen first (prepend bits (key first) occurrence) := by
  obtain ⟨trace, simple, fresh⟩ := source
  refine ⟨following _ _ _ trace, ?_, ?_⟩
  · exact List.nodup_cons.mpr ⟨fun member => fresh _ member (by simp), simple⟩
  · intro point member
    rcases List.mem_cons.mp member with rfl | member
    · exact unseen
    · exact fun known => fresh _ member (by simp [known])

theorem enumerate_sound {State : Type u} {Key : Type v} [DecidableEq Key]
    (step : State → ObservedAction State) (key : State → Key) (eligible : State → Bool)
    (depth : Nat) : ∀ seen first occurrence,
      occurrence ∈ enumerate step key eligible depth seen first →
        Source step key eligible seen first occurrence ∧ occurrence.points.length ≤ depth := by
  induction depth with
  | zero => simp [enumerate]
  | succ depth ih =>
      intro seen first occurrence member
      by_cases visited : key first ∈ seen
      · simp [enumerate, visited] at member
      · cases operation : step first with
        | dead => simp [enumerate, visited, operation] at member
        | accept =>
            cases allowed : eligible first
            · simp [enumerate, visited, operation, allowed] at member
            · simp [enumerate, visited, operation, allowed] at member
              subst occurrence
              exact ⟨⟨.done operation allowed, by simp, by simpa [Fresh]⟩, by simp⟩
        | next target bits =>
            simp only [enumerate, visited, ↓reduceIte, operation, List.mem_map] at member
            obtain ⟨answer, present, rfl⟩ := member
            obtain ⟨source, bounded⟩ := ih _ _ _ present
            exact ⟨source_prepend step key eligible seen first target bits
              (fun _ _ _ trace => .next operation trace) visited answer source,
              by simp [prepend]; omega⟩
        | branch left right =>
            simp only [enumerate, visited, ↓reduceIte, operation, List.mem_append, List.mem_map] at member
            rcases member with ⟨answer, present, rfl⟩ | ⟨answer, present, rfl⟩
            · obtain ⟨source, bounded⟩ := ih _ _ _ present
              exact ⟨source_prepend step key eligible seen first left [false]
                (fun _ _ _ trace => .left operation trace) visited answer source,
                by simp [prepend]; omega⟩
            · obtain ⟨source, bounded⟩ := ih _ _ _ present
              exact ⟨source_prepend step key eligible seen first right [true]
                (fun _ _ _ trace => .right operation trace) visited answer source,
                by simp [prepend]; omega⟩

theorem trace_nonempty {State : Type u} {Key : Type v}
    {step : State → ObservedAction State} {key : State → Key} {eligible : State → Bool}
    {first last : State} {bits : List Bool} {points : List Key}
    (trace : Trace step key eligible first bits points last) : points ≠ [] := by
  cases trace <;> simp

theorem fresh_tail {Key : Type v} (seen : List Key) (point : Key) (points : List Key)
    (simple : (point :: points).Nodup) (fresh : Fresh seen (point :: points)) :
    Fresh (point :: seen) points := by
  intro following member known
  rcases List.mem_cons.mp known with rfl | known
  · exact (List.nodup_cons.mp simple).1 member
  · exact fresh _ (List.mem_cons_of_mem _ member) known

theorem enumerate_complete {State : Type u} {Key : Type v} [DecidableEq Key]
    {step : State → ObservedAction State} {key : State → Key} {eligible : State → Bool}
    {first last : State} {bits : List Bool} {points : List Key}
    (trace : Trace step key eligible first bits points last) :
    ∀ depth seen, points.Nodup → Fresh seen points → points.length ≤ depth →
      (⟨last,bits,points⟩ : Occurrence State Key) ∈ enumerate step key eligible depth seen first := by
  induction trace with
  | done operation allowed =>
      intro depth seen simple fresh enough
      cases depth with
      | zero => simp at enough
      | succ depth =>
          have unseen := fresh _ (List.mem_singleton_self _)
          simp [enumerate, unseen, operation, allowed]
  | @next first target leading bits points last operation trace ih =>
      intro depth seen simple fresh enough
      cases depth with
      | zero => simp at enough
      | succ depth =>
          have unseen := fresh _ List.mem_cons_self
          have answer := ih depth (key first :: seen) (List.nodup_cons.mp simple).2
            (fresh_tail seen _ _ simple fresh) (by simpa using enough)
          simp only [enumerate, unseen, ↓reduceIte, operation, List.mem_map]
          exact ⟨⟨last,bits,points⟩, answer, rfl⟩
  | @left first left right bits points last operation trace ih =>
      intro depth seen simple fresh enough
      cases depth with
      | zero => simp at enough
      | succ depth =>
          have unseen := fresh _ List.mem_cons_self
          have answer := ih depth (key first :: seen) (List.nodup_cons.mp simple).2
            (fresh_tail seen _ _ simple fresh) (by simpa using enough)
          simp only [enumerate, unseen, ↓reduceIte, operation, List.mem_append, List.mem_map]
          exact Or.inl ⟨⟨last,bits,points⟩, answer, rfl⟩
  | @right first left right bits points last operation trace ih =>
      intro depth seen simple fresh enough
      cases depth with
      | zero => simp at enough
      | succ depth =>
          have unseen := fresh _ List.mem_cons_self
          have answer := ih depth (key first :: seen) (List.nodup_cons.mp simple).2
            (fresh_tail seen _ _ simple fresh) (by simpa using enough)
          simp only [enumerate, unseen, ↓reduceIte, operation, List.mem_append, List.mem_map]
          exact Or.inr ⟨⟨last,bits,points⟩, answer, rfl⟩

def all {State : Type u} {Key : Type v} [DecidableEq Key] [Fintype Key]
    (step : State → ObservedAction State) (key : State → Key) (eligible : State → Bool)
    (first : State) : List (Occurrence State Key) :=
  enumerate step key eligible (Fintype.card Key) [] first

theorem all_exact {State : Type u} {Key : Type v} [DecidableEq Key] [Fintype Key]
    (step : State → ObservedAction State) (key : State → Key) (eligible : State → Bool)
    (first : State) (occurrence : Occurrence State Key) :
    occurrence ∈ all step key eligible first ↔
      Trace step key eligible first occurrence.choices occurrence.points occurrence.value ∧ occurrence.points.Nodup := by
  constructor
  · intro present
    have source := (enumerate_sound step key eligible _ _ _ _ present).1
    exact ⟨source.1, source.2.1⟩
  · rintro ⟨trace, simple⟩
    exact enumerate_complete trace _ [] simple (by simp [Fresh]) simple.length_le_card

def regularKey {states groups length : Nat}
    (configuration : RegexDependentObservation.Configuration states groups length) :=
  (configuration.pc, configuration.position)

def dependentKey {states groups length : Nat}
    (configuration : RegexDependentObservation.Configuration states groups length) := configuration

namespace Controls

private def branching (state : Fin 2) : ObservedAction (Fin 2) :=
  if state = 0 then .branch 1 1 else .accept

theorem equal_answers_retain_both_outer_occurrences :
    (all branching id (fun _ => true) 0).map Occurrence.value = [1,1] ∧
      (all branching id (fun _ => true) 0).map Occurrence.choices = [[false],[true]] := by decide

private def withAtomicBody (state : Fin 2) : ObservedAction (Fin 2) :=
  if state = 0 then .next 1 [true,false] else .accept

theorem selected_atomic_body_word_is_retained_once :
    (all withAtomicBody id (fun _ => true) 0).map Occurrence.choices = [[true,false]] := by decide

theorem repeating_ancestor_is_not_an_accepting_occurrence :
    (all (fun _ : Fin 1 => .next 0 []) id (fun _ => true) 0).length = 0 := by decide

end Controls

end Mettapedia.GSLT.LanguageDef.RegexRelationEnumeration
