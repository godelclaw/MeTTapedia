import Mettapedia.GSLT.LanguageDef.RegexLiteralTable

/-!
# Source-ordinal literal selection preserves the admitted Pike observation

The trie may visit terminals in any storage order. Its minimum source ordinal
indexes the original extracted row, retaining that row's endpoint and priority.
This file proves the connection to the independent actual-graph execution.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexLiteralOrdinal

open Mettapedia.Computability.RegularLanguages
open RegexTaggedGraph
open RegexLiteralGraphPlan RegexLiteralTable
open Mettapedia.GSLT.Parsing.TrieLiteralSelection

universe u v

def numbered {State : Type u} : Nat → List (Entry State) → Table Nat Nat
  | _, [] => []
  | offset, row :: rest => (row.word, offset) :: numbered (offset + 1) rest

def indices {α : Type u} {β : Type v} (run : α → Option β) : Nat → List α → List Nat
  | _, [] => []
  | offset, row :: rest =>
      match run row with
      | none => indices run (offset + 1) rest
      | some _ => offset :: indices run (offset + 1) rest

def first {α : Type u} {β : Type v} (run : α → Option β) : Nat → List α → Option (Nat × β)
  | _, [] => none
  | offset, row :: rest =>
      match run row with
      | none => first run (offset + 1) rest
      | some answer => some (offset, answer)

theorem indices_lower_bound {α : Type u} {β : Type v} (run : α → Option β)
    (rows : List α) (offset : Nat) : ∀ ordinal ∈ indices run offset rows, offset ≤ ordinal := by
  induction rows generalizing offset with
  | nil => simp [indices]
  | cons row rest ih =>
      cases computed : run row <;> simp only [indices, computed]
      · intro ordinal member; have next := ih (offset + 1) ordinal member; omega
      · intro ordinal member
        rcases List.mem_cons.mp member with rfl | member
        · exact Nat.le_refl _
        · have next := ih (offset + 1) ordinal member; omega

theorem indices_minimum {α : Type u} {β : Type v} (run : α → Option β)
    (rows : List α) (offset : Nat) :
    (indices run offset rows).min? = (first run offset rows).map Prod.fst := by
  induction rows generalizing offset with
  | nil => rfl
  | cons row rest ih =>
      cases computed : run row with
      | none => simpa [indices, first, computed] using ih (offset + 1)
      | some answer =>
          simp only [indices, first, computed, Option.map_some]
          apply List.min?_eq_some_iff.mpr
          refine ⟨by simp, ?_⟩
          intro ordinal member
          rcases List.mem_cons.mp member with rfl | member
          · exact Nat.le_refl _
          · have next := indices_lower_bound run rest (offset + 1) ordinal member; omega

theorem first_value {α : Type u} {β : Type v} (run : α → Option β)
    (rows : List α) (offset : Nat) :
    (first run offset rows).map Prod.snd = (rows.filterMap run).head? := by
  induction rows generalizing offset with
  | nil => rfl
  | cons row rest ih =>
      cases computed : run row <;> simp [first, computed, ih]

theorem first_lookup {α : Type u} {β : Type v} (run : α → Option β)
    (rows : List α) (offset ordinal : Nat) (answer : β)
    (found : first run offset rows = some (ordinal, answer)) :
    offset ≤ ordinal ∧ (rows[ordinal - offset]?).bind run = some answer := by
  induction rows generalizing offset with
  | nil => simp [first] at found
  | cons row rest ih =>
      cases computed : run row with
      | none =>
          have following := ih (offset + 1) (by simpa [first, computed] using found)
          have positive : ordinal - offset = (ordinal - (offset + 1)) + 1 := by omega
          exact ⟨by omega, by simpa [positive] using following.2⟩
      | some value =>
          simp only [first, computed, Option.some.injEq, Prod.mk.injEq] at found
          obtain ⟨rfl, rfl⟩ := found
          exact ⟨Nat.le_refl _, by simp [computed]⟩

theorem minimum_ext (left right : List Nat) (same : ∀ ordinal, ordinal ∈ left ↔ ordinal ∈ right) :
    left.min? = right.min? := by
  cases selected : left.min? with
  | none =>
      have empty := List.min?_eq_none_iff.mp selected
      subst left
      have rightEmpty : right = [] := List.eq_nil_iff_forall_not_mem.mpr
        (fun ordinal member => by simpa using (same ordinal).mpr member)
      simp [rightEmpty]
  | some ordinal =>
      obtain ⟨member, least⟩ := List.min?_eq_some_iff.mp selected
      exact ((List.min?_eq_some_iff.mpr
        ⟨(same ordinal).mp member, fun other present => least other ((same other).mpr present)⟩).symm)

theorem candidates_numbered_mem {State : Type u} (full : Bool) (input : List Nat)
    (initial : Thread State input.length) (rows : List (Entry State)) (offset ordinal : Nat) :
    ordinal ∈ candidates full (numbered offset rows) (input.drop initial.point.2.val) ↔
      ordinal ∈ indices (interpret (literalProbe input) (endpointEligible full input.length) initial)
        offset rows := by
  induction rows generalizing offset with
  | nil => simp [candidates_mem, numbered, indices]
  | cons row rest ih =>
      let run := interpret (literalProbe input) (endpointEligible full input.length) initial
      have admits := interpret_literal_some_iff full input initial row
      have reduced :
          (∃ word, (word, ordinal) ∈ (row.word, offset) :: numbered (offset + 1) rest ∧
            word <+: input.drop initial.point.2.val ∧
              (full = true → word = input.drop initial.point.2.val)) ↔
          (ordinal = offset ∧ (run row).isSome = true) ∨
            ordinal ∈ candidates full (numbered (offset + 1) rest) (input.drop initial.point.2.val) := by
        rw [candidates_mem]
        constructor
        · rintro ⟨word, present, prefixed, fullWord⟩
          rcases List.mem_cons.mp present with same | present
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
            exact Or.inl ⟨rfl, admits.mpr ⟨prefixed, fullWord⟩⟩
          · exact Or.inr ⟨word, present, prefixed, fullWord⟩
        · rintro (⟨rfl, accepted⟩ | ⟨word, present, prefixed, fullWord⟩)
          · exact ⟨row.word, by simp, (admits.mp accepted).1, (admits.mp accepted).2⟩
          · exact ⟨word, List.mem_cons_of_mem _ present, prefixed, fullWord⟩
      rw [candidates_mem, numbered, reduced, ih]
      cases computed : run row <;> simp [indices, run, computed] at *

/-- Traversal order may differ from source order. Minimum ordinal nevertheless
selects exactly the first successful original row, not the longest word. -/
theorem trie_winner_first {State : Type u} (full : Bool) (input : List Nat)
    (initial : Thread State input.length) (rows : List (Entry State)) (offset : Nat) :
    winner full (numbered offset rows) (input.drop initial.point.2.val) =
      (first (interpret (literalProbe input) (endpointEligible full input.length) initial) offset rows).map
        Prod.fst := by
  rw [winner, ← indices_minimum]
  exact minimum_ext _ _ (candidates_numbered_mem full input initial rows offset)

def trieSelect {State : Type} (full : Bool) (input : List Nat)
    (initial : Thread State input.length) (rows : List (Entry State)) : Option (Thread State input.length) := do
  let ordinal ← winner full (numbered 0 rows) (input.drop initial.point.2.val)
  let row ← rows[ordinal]?
  interpret (literalProbe input) (endpointEligible full input.length) initial row

theorem trieSelect_eq_head {State : Type} (full : Bool) (input : List Nat)
    (initial : Thread State input.length) (rows : List (Entry State)) :
    trieSelect full input initial rows =
      (rows.filterMap (interpret (literalProbe input) (endpointEligible full input.length) initial)).head? := by
  let run := interpret (literalProbe input) (endpointEligible full input.length) initial
  rw [← first_value run rows 0]
  unfold trieSelect
  rw [trie_winner_first]
  cases selected : first run 0 rows with
  | none => simp [run] at selected ⊢
  | some pair =>
      rcases pair with ⟨ordinal, answer⟩
      have lookup := (first_lookup run rows 0 ordinal answer selected).2
      simpa [run, selected] using lookup

/-- The literal trie observer and actual Pike driver return the same complete
thread for every locally admitted acyclic graph. The winner includes its
original priority history and every untouched capture register. -/
theorem pike_eq_trieSelect {State : Type} [DecidableEq State] [Fintype State]
    (graph : State → Node State RegexSelection.Graph.CharacterClass String Unit)
    (full : Bool) (input : List Nat) (plan : Plan State) (valid : Valid graph plan)
    (acyclic : Acyclic plan) (initial : Thread State input.length) (entry : initial.point.1 = root plan)
    (closureFuel inputFuel : Nat) (closureEnough : 3 * Fintype.card State + 1 ≤ closureFuel)
    (inputEnough : input.length + 1 ≤ inputFuel) :
    RegexPikeVM.run graph (literalProbe input) (endpointEligible full input.length)
      closureFuel inputFuel [initial] =
      .finished ((trieSelect full input initial (extract plan)).map (fun thread => (thread, ()))) := by
  let eligible : OrderedGraphSearch.Point State input.length → Bool :=
    fun point => !full || point.2.val == input.length
  have observation := trieSelect_eq_head full input initial (extract plan)
  rw [← evaluate_values (literalProbe input) (endpointEligible full input.length) plan initial entry] at observation
  cases selected : evaluate (literalProbe input) (endpointEligible full input.length) plan initial with
  | nil =>
      have none : trieSelect full input initial (extract plan) = none := by simpa [selected] using observation
      rw [none]
      apply (RegexPikeCoverage.run_none_iff_no_trace graph (literalProbe input) eligible closureFuel inputFuel
        closureEnough inputEnough initial).mpr
      rintro ⟨bits, points, last, tag, trace⟩
      cases tag
      have invented := evaluate_complete graph (literalProbe input) (endpointEligible full input.length)
        plan valid initial entry bits points last trace
      simp [selected] at invented
  | cons answer rest =>
      have winner : trieSelect full input initial (extract plan) = some answer.value := by
        simpa [selected] using observation
      rw [winner]
      exact pike_of_evaluate_head graph (literalProbe input) eligible plan valid acyclic initial entry
        answer rest selected closureFuel inputFuel closureEnough inputEnough

/-- Mapping to an external span/capture observation is licensed by exact
thread equality; the mapping cannot alter which alternative was selected. -/
theorem pike_observation_eq {State Value : Type} [DecidableEq State] [Fintype State]
    (graph : State → Node State RegexSelection.Graph.CharacterClass String Unit)
    (full : Bool) (input : List Nat) (plan : Plan State) (valid : Valid graph plan)
    (acyclic : Acyclic plan) (initial : Thread State input.length) (entry : initial.point.1 = root plan)
    (observe : Thread State input.length → Value)
    (closureFuel inputFuel : Nat) (closureEnough : 3 * Fintype.card State + 1 ≤ closureFuel)
    (inputEnough : input.length + 1 ≤ inputFuel) :
    (match RegexPikeVM.run graph (literalProbe input) (endpointEligible full input.length)
        closureFuel inputFuel [initial] with
      | .incomplete => none
      | .finished result => result.map (fun found => observe found.1)) =
      (trieSelect full input initial (extract plan)).map observe := by
  rw [pike_eq_trieSelect graph full input plan valid acyclic initial entry closureFuel inputFuel
    closureEnough inputEnough]
  cases trieSelect full input initial (extract plan) <;> rfl

end Mettapedia.GSLT.LanguageDef.RegexLiteralOrdinal
