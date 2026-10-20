import Mettapedia.OSLF.MeTTaIL.CollectionSelectionCanonical

/-!
# Stateful matching of unordered collections modulo their declared equality

Collection decomposition is separate from element matching and final rest
capture. Element matching threads the caller's state in schema order and receives
the exact schema index. Thus scoped callers can retain their existing capture
and repeated-variable checks.

The specification uses the existing `Presents` relation and an independent
ordered row judgment. The finite algorithm is sound and complete relative to
its element and rest handlers. This is a compositional collection operation;
it does not grant an arbitrary handler correctness or admit a language.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CollectionMatching

open Syntax CanonicalBags CollectionSelection

universe u
variable {State : Type u}

/-- Element evidence, with ordered assignment flow and source positions. -/
inductive Rows (Element : Nat → State → Pattern → Pattern → State → Prop) :
    Nat → State → List Pattern → List Pattern → State → Prop where
  | nil {index initial} : Rows Element index initial [] [] initial
  | cons {index initial schema schemas value values middle final} :
      Element index initial schema value middle →
      Rows Element (index + 1) middle schemas values final →
      Rows Element index initial (schema :: schemas) (value :: values) final

theorem Rows.length {Element : Nat → State → Pattern → Pattern → State → Prop}
    {index : Nat} {initial final : State} {schemas values : List Pattern}
    (rows : Rows Element index initial schemas values final) : schemas.length = values.length := by
  induction rows with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- Run the supplied element handler in schema order. -/
def matchRows (element : Nat → State → Pattern → Pattern → List State)
    (index : Nat) (initial : State) : List Pattern → List Pattern → List State
  | [], [] => [initial]
  | schema :: schemas, value :: values =>
      (element index initial schema value).flatMap fun middle =>
        matchRows element (index + 1) middle schemas values
  | _, _ => []

theorem matchRows_exact
    {Element : Nat → State → Pattern → Pattern → State → Prop}
    {element : Nat → State → Pattern → Pattern → List State}
    (elementExact : ∀ index initial schema value final,
      final ∈ element index initial schema value ↔ Element index initial schema value final)
    (index : Nat) (initial final : State) (schemas values : List Pattern) :
    final ∈ matchRows element index initial schemas values ↔
      Rows Element index initial schemas values final := by
  induction schemas generalizing index initial values with
  | nil =>
      cases values with
      | nil =>
          constructor
          · intro member
            have same : final = initial := by simpa [matchRows] using member
            subst final
            exact .nil
          · intro rows
            cases rows
            simp [matchRows]
      | cons value values =>
          constructor
          · simp [matchRows]
          · intro rows
            cases rows
  | cons schema schemas ih =>
      cases values with
      | nil =>
          constructor
          · simp [matchRows]
          · intro rows
            cases rows
      | cons value values =>
          simp only [matchRows, List.mem_flatMap]
          constructor
          · rintro ⟨middle, head, tail⟩
            exact .cons ((elementExact ..).mp head) ((ih ..).mp tail)
          · intro rows
            cases rows with
            | cons head tail => exact ⟨_, (elementExact ..).mpr head, (ih ..).mpr tail⟩

/-- Independent collection matching: the chosen values and residual reconstruct
the source collection under its declared equality. The rest handler observes
the canonical residual. -/
def Matches (Element : Nat → State → Pattern → Pattern → State → Prop)
    (Finish : State → List Pattern → State → Prop)
    (kind : CollType) (index : Nat) (initial : State)
    (schemas targets : List Pattern) (final : State) : Prop :=
  ∃ selected rest middle,
    Presents kind targets (selected ++ rest) ∧
    Rows Element index initial schemas selected middle ∧
    Finish middle (arrange kind rest) final

/-- Enumerate set or bag decompositions, then apply the same element and rest
handlers to each. Vector matching remains positional. -/
def matchCollection (element : Nat → State → Pattern → Pattern → List State)
    (finish : State → List Pattern → List State)
    (kind : CollType) (index : Nat) (initial : State)
    (schemas targets : List Pattern) : List State :=
  (kindAllocations kind schemas.length targets).flatMap fun (selected, rest) =>
    (matchRows element index initial schemas selected).flatMap fun middle =>
      finish middle (arrange kind rest)

theorem matchCollection_exact
    {Element : Nat → State → Pattern → Pattern → State → Prop}
    {Finish : State → List Pattern → State → Prop}
    {element : Nat → State → Pattern → Pattern → List State}
    {finish : State → List Pattern → List State}
    (elementExact : ∀ index initial schema value final,
      final ∈ element index initial schema value ↔ Element index initial schema value final)
    (finishExact : ∀ initial rest final, final ∈ finish initial rest ↔ Finish initial rest final)
    {kind : CollType} (unordered : kind ≠ .vec)
    {targets : List Pattern} (distinct : kind = .hashSet → targets.Nodup)
    (index : Nat) (initial final : State) (schemas : List Pattern) :
    final ∈ matchCollection element finish kind index initial schemas targets ↔
      Matches Element Finish kind index initial schemas targets final := by
  simp only [matchCollection, List.mem_flatMap]
  constructor
  · rintro ⟨⟨selected, rest⟩, allocated, middle, matched, finished⟩
    have rows := (matchRows_exact elementExact ..).mp matched
    have length := rows.length
    have covered : Presents kind targets (selected ++ rest) := by
      apply (allocations_present_exact unordered distinct).mp
      exact ⟨rest, by simpa only [length] using allocated, Presents.of_eq rfl⟩
    exact ⟨selected, rest, middle, covered, rows, (finishExact ..).mp finished⟩
  · rintro ⟨selected, rest, middle, covered, rows, finished⟩
    obtain ⟨actual, allocated, same⟩ :=
      (allocations_present_exact unordered distinct).mpr covered
    have length := rows.length
    have normal := arrange_eq_of_presents same
    refine ⟨(selected, actual), ?_, middle, (matchRows_exact elementExact ..).mpr rows, ?_⟩
    · simpa only [length] using allocated
    · apply (finishExact ..).mpr
      simpa only [normal] using finished

end Mettapedia.OSLF.MeTTaIL.CollectionMatching
