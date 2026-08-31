import Mettapedia.GraphTheory.FourColor.Compositional.PhasedNoncrossingSweep
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Finite noncrossing sweeps on selected positions

The ordinary length--depth theorem sweeps every position of a finite linear
order.  Applications often need the same pigeonhole argument only on a chosen
interval or other finite subset.  This file supplies that restriction without
changing the state code: either a selected position has a deep stack, or two
selected positions carry the same literal state.

The result is independent of graphs and planarity.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.RestrictedNoncrossingSweep

open GoertzelV24NoncrossingSweepLifo
open GoertzelV24NoncrossingSweepPigeonhole
open PhasedNoncrossingSweep
open scoped BigOperators

universe u v

namespace SweepData

/-- Encode a shallow sweep state at one member of a selected position set. -/
def codedStateOn {A : Type u} {K : Type v} {r n : Nat}
    (data : SweepData A K r n) (depth : Nat)
    (positions : Finset (Fin n))
    (hbounded : ∀ family cut, cut ∈ positions →
      ((data.family family).stackAt cut).length ≤ depth)
    (cut : positions) : SweepState A K r depth :=
  ⟨data.letter cut, fun family =>
    boundedListEquivStackCode K depth
      ⟨(data.family family).stackAt cut,
        hbounded family cut cut.property⟩⟩

/-- Equality of selected-position codes is literal equality of the raw sweep
states at the underlying positions. -/
theorem rawState_eq_of_codedStateOn_eq
    {A : Type u} {K : Type v} {r n : Nat}
    (data : SweepData A K r n) (depth : Nat)
    (positions : Finset (Fin n))
    (hbounded : ∀ family cut, cut ∈ positions →
      ((data.family family).stackAt cut).length ≤ depth)
    {first second : positions}
    (heq : codedStateOn data depth positions hbounded first =
      codedStateOn data depth positions hbounded second) :
    data.rawState first = data.rawState second := by
  apply Prod.ext
  · exact congrArg (fun state : SweepState A K r depth => state.1) heq
  · funext family
    have hcode := congrFun
      (congrArg (fun state : SweepState A K r depth => state.2) heq) family
    have hinv := congrArg
      (fun code => ((boundedListEquivStackCode K depth).symm code).1) hcode
    exact hinv

/-- **Restricted noncrossing length--depth alternative.**  More selected
positions than bounded stack states force either a deep stack at a selected
position or two distinct selected positions with equal raw states. -/
theorem exists_deep_family_on_or_distinct_eq_rawState
    {A : Type u} {K : Type v} {r n : Nat}
    [Fintype A] [DecidableEq A] [Fintype K] [DecidableEq K]
    (data : SweepData A K r n) (depth : Nat)
    (positions : Finset (Fin n))
    (hmany :
      Fintype.card A *
          (∑ d : Fin (depth + 1), Fintype.card K ^ (d : Nat)) ^ r <
        positions.card) :
    (∃ family cut, cut ∈ positions ∧
        depth < ((data.family family).stackAt cut).length) ∨
      ∃ first second : Fin n,
        first ∈ positions ∧ second ∈ positions ∧ first ≠ second ∧
          data.rawState first = data.rawState second := by
  by_cases hdeep : ∃ family cut, cut ∈ positions ∧
      depth < ((data.family family).stackAt cut).length
  · exact Or.inl hdeep
  · right
    have hbounded : ∀ family cut, cut ∈ positions →
        ((data.family family).stackAt cut).length ≤ depth := by
      intro family cut hcut
      apply Nat.le_of_not_gt
      intro hlt
      exact hdeep ⟨family, cut, hcut, hlt⟩
    let state : positions → SweepState A K r depth :=
      codedStateOn data depth positions hbounded
    have hcard :
        Fintype.card (SweepState A K r depth) < Fintype.card positions := by
      rw [Fintype.card_coe]
      simpa [card_sweepState] using hmany
    obtain ⟨first, second, hne, heq⟩ :=
      Fintype.exists_ne_map_eq_of_card_lt state hcard
    refine ⟨first, second, first.property, second.property, ?_, ?_⟩
    · intro hvalue
      exact hne (Subtype.ext hvalue)
    · exact rawState_eq_of_codedStateOn_eq
        data depth positions hbounded heq

/-- The restricted theorem with a position phase.  Equal phased states can
be oriented so that their underlying positions are separated by at least the
requested period. -/
theorem exists_deep_family_on_or_spaced_eq_rawState
    {A : Type u} {K : Type v} {r n : Nat}
    [Fintype A] [DecidableEq A] [Fintype K] [DecidableEq K]
    (data : SweepData A K r n) (depth spacing : Nat)
    (positions : Finset (Fin n))
    (hmany :
      Fintype.card A * (spacing + 1) *
          (∑ d : Fin (depth + 1), Fintype.card K ^ (d : Nat)) ^ r <
        positions.card) :
    (∃ family cut, cut ∈ positions ∧
        depth < ((data.family family).stackAt cut).length) ∨
      ∃ first second : Fin n,
        first ∈ positions ∧ second ∈ positions ∧ first < second ∧
          spacing + 1 ≤ second.val - first.val ∧
          (PhasedNoncrossingSweep.SweepData.withPositionPhase
              data spacing).rawState first =
            (PhasedNoncrossingSweep.SweepData.withPositionPhase
              data spacing).rawState second := by
  have hmany' :
      Fintype.card (A × Fin (spacing + 1)) *
          (∑ d : Fin (depth + 1), Fintype.card K ^ (d : Nat)) ^ r <
        positions.card := by
    simpa [Fintype.card_prod] using hmany
  rcases
      exists_deep_family_on_or_distinct_eq_rawState
        (PhasedNoncrossingSweep.SweepData.withPositionPhase data spacing)
        depth positions hmany' with
    hdeep | ⟨first, second, hfirst, hsecond, hne, heq⟩
  · left
    simpa [PhasedNoncrossingSweep.SweepData.withPositionPhase] using hdeep
  · right
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨first, second, hfirst, hsecond, hlt,
        SweepData.spacing_add_one_le_sub_of_withPositionPhase_rawState_eq
          data spacing hlt heq,
        heq⟩
    · exact ⟨second, first, hsecond, hfirst, hgt,
        SweepData.spacing_add_one_le_sub_of_withPositionPhase_rawState_eq
          data spacing hgt heq.symm,
        heq.symm⟩

end SweepData

end Mettapedia.GraphTheory.FourColor.Compositional.RestrictedNoncrossingSweep
