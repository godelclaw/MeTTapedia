import Mettapedia.Computability.PNP.PNPv13SwitchingFieldedCore

/-!
# PNP v13 fielded switching: cell-half and matching equivalences

Equivalence between recursive fixed-field switching, residual cell-half obligations, and recursive same-cell failure matching.
-/

namespace Mettapedia.Computability.PNP

open scoped BigOperators

universe u

/-- After the fields are fixed externally, v13 fielded switching is exactly the
recursive list of cellwise half-success inequalities. -/
theorem v13FieldSwitchingInstantiatedFrom_iff_cellHalfFrom
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)} :
    V13FieldSwitchingInstantiatedFrom hist items ↔
      V13FieldSwitchingCellHalfFrom hist items := by
  induction items generalizing hist with
  | nil =>
      constructor <;> intro h <;> trivial
  | cons item rest ih =>
      constructor
      · intro h
        rcases h with ⟨hitem, hrest⟩
        exact ⟨(v13FieldPrefixInstantiation_iff_cellHalf.mp hitem),
          (ih.mp hrest)⟩
      · intro h
        rcases h with ⟨hitem, hrest⟩
        exact ⟨(v13FieldPrefixInstantiation_iff_cellHalf.mpr hitem),
          (ih.mpr hrest)⟩

/-- Empty-history form: fixed-field v13 switching is exactly the residual
recursive cell-half obligation. -/
theorem v13FieldSwitchingInstantiated_iff_cellHalf
    {Ω : Type u} [Fintype Ω] {items : List (V13FieldedStep Ω)} :
    V13FieldSwitchingInstantiated items ↔
      V13FieldSwitchingCellHalf items := by
  exact v13FieldSwitchingInstantiatedFrom_iff_cellHalfFrom

/-- Recursive operational matching obligation: at each fielded step, every
successful point in each current history cell must be injectively matchable to
an unsuccessful point in the same cell. -/
def V13FieldSwitchingFailureMatchingFrom {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) : List (V13FieldedStep Ω) → Prop
  | [] => True
  | item :: rest =>
      V13FieldFailureMatching item.field hist item.step ∧
        V13FieldSwitchingFailureMatchingFrom
          (hist ++ [item.step.successEvent]) rest

/-- Empty-history form of the recursive same-cell success-to-failure matching
obligation. -/
def V13FieldSwitchingFailureMatching {Ω : Type u} [Fintype Ω]
    (items : List (V13FieldedStep Ω)) : Prop :=
  V13FieldSwitchingFailureMatchingFrom ([] : List (FiniteEvent Ω)) items

/-- The whole fixed-field v13 switching interface is exactly the recursive
same-cell success-to-failure matching obligation. -/
theorem v13FieldSwitchingInstantiatedFrom_iff_failureMatchingFrom
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)} :
    V13FieldSwitchingInstantiatedFrom hist items ↔
      V13FieldSwitchingFailureMatchingFrom hist items := by
  induction items generalizing hist with
  | nil =>
      constructor <;> intro h <;> trivial
  | cons item rest ih =>
      constructor
      · intro h
        rcases h with ⟨hitem, hrest⟩
        exact ⟨v13FieldPrefixInstantiation_iff_failureMatching.mp hitem,
          (ih.mp hrest)⟩
      · intro h
        rcases h with ⟨hitem, hrest⟩
        exact ⟨v13FieldPrefixInstantiation_iff_failureMatching.mpr hitem,
          (ih.mpr hrest)⟩

/-- Empty-history form: fixed-field v13 switching is exactly recursive
same-cell success-to-failure matching. -/
theorem v13FieldSwitchingInstantiated_iff_failureMatching
    {Ω : Type u} [Fintype Ω] {items : List (V13FieldedStep Ω)} :
    V13FieldSwitchingInstantiated items ↔
      V13FieldSwitchingFailureMatching items := by
  exact v13FieldSwitchingInstantiatedFrom_iff_failureMatchingFrom

/-- Failure of the recursive same-cell matching obligation blocks fixed-field
v13 switching. -/
theorem not_v13FieldSwitchingInstantiatedFrom_of_not_failureMatchingFrom
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hfail : ¬ V13FieldSwitchingFailureMatchingFrom hist items) :
    ¬ V13FieldSwitchingInstantiatedFrom hist items := by
  intro h
  exact hfail (v13FieldSwitchingInstantiatedFrom_iff_failureMatchingFrom.mp h)

/-- Empty-history blocker from failure of recursive same-cell matching. -/
theorem not_v13FieldSwitchingInstantiated_of_not_failureMatching
    {Ω : Type u} [Fintype Ω] {items : List (V13FieldedStep Ω)}
    (hfail : ¬ V13FieldSwitchingFailureMatching items) :
    ¬ V13FieldSwitchingInstantiated items := by
  exact not_v13FieldSwitchingInstantiatedFrom_of_not_failureMatchingFrom hfail

end Mettapedia.Computability.PNP
