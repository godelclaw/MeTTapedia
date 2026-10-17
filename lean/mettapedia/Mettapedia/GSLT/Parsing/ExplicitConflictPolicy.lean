import Mathlib.Data.List.Basic

/-!
# Explicit finite conflict policies

A conflict cell retains its alternatives. A declared direct preference is an
edge between two alternatives, not an ordering supplied by an engine. Selection
requires one alternative to dominate every other alternative directly. Missing
edges, cycles without a dominating alternative, and two dominating alternatives
are refused. This boundary does not prove a parser sound or complete: those are
separate grammar/forest correspondence obligations.
-/

namespace Mettapedia.GSLT.Parsing.ExplicitConflictPolicy

def dominates (preferences : List (Nat × Nat)) (winner other : Nat) : Bool :=
  preferences.contains (winner, other)

def eligible (alternatives : List Nat) (preferences : List (Nat × Nat))
    (winner : Nat) : Bool :=
  alternatives.all fun other => winner == other || dominates preferences winner other

def winners (alternatives : List Nat) (preferences : List (Nat × Nat)) : List Nat :=
  (alternatives.filter (eligible alternatives preferences)).eraseDups

def select (alternatives : List Nat) (preferences : List (Nat × Nat)) : Option Nat :=
  match winners alternatives preferences with
  | [winner] => some winner
  | _ => none

theorem mem_winners_iff {alternatives : List Nat} {preferences : List (Nat × Nat)}
    {winner : Nat} :
    winner ∈ winners alternatives preferences ↔
      winner ∈ alternatives ∧ ∀ other ∈ alternatives,
        other ≠ winner → (winner, other) ∈ preferences := by
  simp only [winners, List.mem_eraseDups, List.mem_filter, eligible, List.all_eq_true,
    Bool.or_eq_true, beq_iff_eq, dominates, List.contains_iff_mem]
  constructor
  · rintro ⟨member, covers⟩
    exact ⟨member, fun other present distinct => (covers other present).resolve_left (Ne.symm distinct)⟩
  · rintro ⟨member, covers⟩
    refine ⟨member, fun other present => ?_⟩
    by_cases same : winner = other
    · exact Or.inl same
    · exact Or.inr (covers other present (Ne.symm same))

theorem select_winners_singleton {alternatives : List Nat} {preferences : List (Nat × Nat)}
    {winner : Nat} (selected : select alternatives preferences = some winner) :
    winners alternatives preferences = [winner] := by
  unfold select at selected
  cases equation : winners alternatives preferences with
  | nil => simp [equation] at selected
  | cons head tail =>
    cases tail with
    | nil => simpa [equation] using selected
    | cons next rest => simp [equation] at selected

theorem select_no_invention {alternatives : List Nat} {preferences : List (Nat × Nat)}
    {winner : Nat} (selected : select alternatives preferences = some winner) :
    winner ∈ alternatives := by
  have member : winner ∈ winners alternatives preferences := by
    simp [select_winners_singleton selected]
  exact (mem_winners_iff.mp member).1

theorem select_direct_authority {alternatives : List Nat} {preferences : List (Nat × Nat)}
    {winner other : Nat} (selected : select alternatives preferences = some winner)
    (present : other ∈ alternatives) (distinct : other ≠ winner) :
    (winner, other) ∈ preferences := by
  have member : winner ∈ winners alternatives preferences := by
    simp [select_winners_singleton selected]
  exact (mem_winners_iff.mp member).2 other present distinct

theorem select_unique {alternatives : List Nat} {preferences : List (Nat × Nat)}
    {winner other : Nat} (selected : select alternatives preferences = some winner)
    (present : other ∈ winners alternatives preferences) : other = winner := by
  simpa [select_winners_singleton selected] using present

theorem select_inherits_soundness {alternatives : List Nat} {preferences : List (Nat × Nat)}
    {winner : Nat} {sound : Nat → Prop}
    (sourceSound : ∀ candidate ∈ alternatives, sound candidate)
    (selected : select alternatives preferences = some winner) : sound winner :=
  sourceSound winner (select_no_invention selected)

theorem missing_direct_authority {alternatives : List Nat} {preferences : List (Nat × Nat)}
    {winner other : Nat} (present : other ∈ alternatives) (distinct : other ≠ winner)
    (missing : (winner, other) ∉ preferences) :
    select alternatives preferences ≠ some winner := by
  intro selected
  exact missing (select_direct_authority selected present distinct)

theorem multiple_dominators_refused {alternatives : List Nat} {preferences : List (Nat × Nat)}
    {first second : Nat} (a : first ∈ winners alternatives preferences)
    (b : second ∈ winners alternatives preferences) (distinct : first ≠ second) :
    select alternatives preferences = none := by
  cases equation : select alternatives preferences with
  | none => rfl
  | some chosen =>
    exact False.elim (distinct ((select_unique equation a).trans (select_unique equation b).symm))

theorem eraseDups_singleton_of_unique_member {values : List Nat} {winner : Nat}
    (present : winner ∈ values) (unique : ∀ other ∈ values, other = winner) :
    values.eraseDups = [winner] := by
  cases values with
  | nil => simp at present
  | cons head tail =>
    have head_eq := unique head (by simp)
    subst head
    have empty : tail.filter (fun other => !(other == winner)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro other member
      simp [unique other (List.mem_cons_of_mem _ member)]
    simp [List.eraseDups_cons, empty]

theorem select_complete {alternatives : List Nat} {preferences : List (Nat × Nat)}
    {winner : Nat} (present : winner ∈ alternatives)
    (authority : ∀ other ∈ alternatives, other ≠ winner → (winner, other) ∈ preferences)
    (unique : ∀ candidate, candidate ∈ alternatives →
      (∀ other ∈ alternatives, other ≠ candidate → (candidate, other) ∈ preferences) →
      candidate = winner) : select alternatives preferences = some winner := by
  have member : winner ∈ winners alternatives preferences :=
    mem_winners_iff.mpr ⟨present, authority⟩
  have only : ∀ candidate ∈ winners alternatives preferences, candidate = winner := by
    intro candidate eligibleMember
    obtain ⟨candidateMember, candidateAuthority⟩ := mem_winners_iff.mp eligibleMember
    exact unique candidate candidateMember candidateAuthority
  have filteredMember : winner ∈ alternatives.filter (eligible alternatives preferences) := by
    simpa only [winners, List.mem_eraseDups] using member
  have filteredUnique : ∀ candidate ∈ alternatives.filter (eligible alternatives preferences),
      candidate = winner := by
    intro candidate filtered
    exact only candidate (by simpa only [winners, List.mem_eraseDups] using filtered)
  have singleton := eraseDups_singleton_of_unique_member filteredMember filteredUnique
  simp [select, winners, singleton]

theorem select_iff_unique_direct_authority {alternatives : List Nat}
    {preferences : List (Nat × Nat)} {winner : Nat} :
    select alternatives preferences = some winner ↔
      (winner ∈ alternatives ∧ ∀ other ∈ alternatives,
        other ≠ winner → (winner, other) ∈ preferences) ∧
      (∀ candidate, candidate ∈ alternatives →
        (∀ other ∈ alternatives, other ≠ candidate → (candidate, other) ∈ preferences) →
        candidate = winner) := by
  constructor
  · intro selected
    refine ⟨⟨select_no_invention selected, fun _ present distinct =>
      select_direct_authority selected present distinct⟩, ?_⟩
    intro candidate present authority
    exact select_unique selected (mem_winners_iff.mpr ⟨present, authority⟩)
  · rintro ⟨⟨present, authority⟩, unique⟩
    exact select_complete present authority unique

example : select [0, 1, 2] [(0, 1), (0, 2)] = some 0 := by decide
example : select [0, 1, 2] [(0, 1)] = none := by decide
example : select [0, 1, 2] [(0, 1), (1, 2)] = none := by decide
example : select [0, 1, 2] [(0, 1), (1, 2), (2, 0)] = none := by decide
example : select [0, 1] [(0, 1), (1, 0)] = none := by decide
example : select [0, 1] [(7, 0), (7, 1)] = none := by decide
example : select [0, 0, 1] [(0, 1)] = some 0 := by decide

end Mettapedia.GSLT.Parsing.ExplicitConflictPolicy
