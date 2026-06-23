import Mettapedia.Computability.PNP.PNPv13ForcedStepObstruction
import Mettapedia.Computability.PNP.PNPv13FieldRefinement

/-!
# PNP local route coverage: fielded v13 anchors

Route-coverage propositions and theorem-backed anchors for the fielded v13
ledger entries in the current local PNP crux packet.
-/

namespace Mettapedia.Computability.PNP

/-- The v13 repeated-positive-fielded-pivot ledger entry is covered only by a
real route theorem: a repeated positive fielded pivot blocks both the fixed-field
certificate route and the equivalent same-cell matching route. -/
def V13RepeatedPositiveFieldedPivotCoverage : Prop :=
  ∀ {Ω : Type} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)},
    V13RepeatedPositiveFieldedPivotFrom hist items →
      (¬ V13FieldSwitchingInstantiatedFrom hist items) ∧
        ¬ V13FieldSwitchingFailureMatchingFrom hist items

/-- The v13 forced-positive-fielded-step ledger entry is covered only by the
route result showing that a logically forced next success event on positive
accumulated mass blocks both fixed-field formulations. -/
def V13ForcedPositiveFieldedStepCoverage : Prop :=
  ∀ {Ω : Type} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)},
    V13ForcedPositiveFieldedStepFrom hist items →
      (¬ V13FieldSwitchingInstantiatedFrom hist items) ∧
        ¬ V13FieldSwitchingFailureMatchingFrom hist items

/-- The v13 fixed-field bad-cell ledger entry is covered only by the theorem
that a localized bad cell blocks both fixed-field formulations. -/
def V13FieldedBadCellCoverage : Prop :=
  ∀ {Ω : Type} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)},
    V13FieldedBadCellFrom hist items →
      (¬ V13FieldSwitchingInstantiatedFrom hist items) ∧
        ¬ V13FieldSwitchingFailureMatchingFrom hist items

/-- The field-refinement ledger entry is covered only by the theorem that a bad
coarse cell survives every finite refinement and blocks the refined prefix
certificate. -/
def V13FieldRefinementBadCellCoverage : Prop :=
  ∀ {Ω : Type} [Fintype Ω]
    {fine coarse : V13HistoryField Ω}
    (refn : V13HistoryFieldRefinement fine coarse)
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    {coarseCell : coarse.Cell},
    v13ConcreteFailureCount (Ω := Ω) hist step coarse.cellOf coarseCell <
        v13ConcreteSuccessCount (Ω := Ω) hist step coarse.cellOf coarseCell →
      (∃ fineCell : fine.Cell,
        refn.project fineCell = coarseCell ∧
          v13ConcreteFailureCount (Ω := Ω) hist step fine.cellOf fineCell <
            v13ConcreteSuccessCount (Ω := Ω) hist step fine.cellOf fineCell) ∧
        ¬ V13FieldPrefixInstantiation fine hist step

@[simp] theorem v13RepeatedPositiveFieldedPivotCoverage :
    V13RepeatedPositiveFieldedPivotCoverage := by
  intro Ω _FintypeΩ hist items hrep
  exact v13RepeatedPositiveFieldedPivot_blocks_fixedFieldRoute hrep

@[simp] theorem v13ForcedPositiveFieldedStepCoverage :
    V13ForcedPositiveFieldedStepCoverage := by
  intro Ω _FintypeΩ hist items hforced
  exact v13ForcedPositiveFieldedStep_blocks_fixedFieldRoute hforced

@[simp] theorem v13FieldedBadCellCoverage :
    V13FieldedBadCellCoverage := by
  intro Ω _FintypeΩ hist items hbad
  exact
    ⟨not_v13FieldSwitchingInstantiatedFrom_of_fieldedBadCell hbad,
      not_v13FieldSwitchingFailureMatchingFrom_of_fieldedBadCell hbad⟩

@[simp] theorem v13FieldRefinementBadCellCoverage :
    V13FieldRefinementBadCellCoverage := by
  intro Ω _FintypeΩ fine coarse refn hist step coarseCell hbad
  exact
    ⟨exists_refined_bad_cell_of_bad_coarse_cell refn hbad,
      not_v13FieldPrefixInstantiation_of_refinement_bad_coarse_cell refn hbad⟩

end Mettapedia.Computability.PNP
