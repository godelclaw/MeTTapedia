import Mettapedia.GraphTheory.FourColor.Compositional.RestrictedNoncrossingSweep

/-!
# Shallow bounds retained by the restricted sweep pigeonhole theorem

The ordinary restricted sweep alternative returns either a deep stack or a
spaced repeated state.  In the repeated-state branch, the negation of the
first alternative also bounds every selected stack.  This small strengthening
retains those bounds explicitly for later physical cut-width estimates.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace RestrictedNoncrossingSweepBounded

open GoertzelV24NoncrossingSweepLifo
open PhasedNoncrossingSweep
open scoped BigOperators

universe u v

namespace SweepData

/-- A repeated selected-position state comes with the shallow bound which
made the finite state space applicable. -/
theorem exists_deep_family_on_or_spaced_eq_rawState_with_bounds
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
              data spacing).rawState second ∧
          (∀ family, ((data.family family).stackAt first).length ≤ depth) ∧
          (∀ family, ((data.family family).stackAt second).length ≤ depth) := by
  by_cases hdeep : ∃ family cut, cut ∈ positions ∧
      depth < ((data.family family).stackAt cut).length
  · exact Or.inl hdeep
  · have hbounded : ∀ family cut, cut ∈ positions →
        ((data.family family).stackAt cut).length ≤ depth := by
      intro family cut hcut
      exact Nat.le_of_not_gt (fun hlt => hdeep ⟨family, cut, hcut, hlt⟩)
    rcases
        _root_.Mettapedia.GraphTheory.FourColor.Compositional.RestrictedNoncrossingSweep.SweepData.exists_deep_family_on_or_spaced_eq_rawState
            data depth spacing positions hmany with
      hdeep' | ⟨first, second, hfirst, hsecond, horder, hspacing, heq⟩
    · exact False.elim (hdeep hdeep')
    · exact Or.inr ⟨first, second, hfirst, hsecond, horder, hspacing,
        heq, fun family => hbounded family first hfirst,
        fun family => hbounded family second hsecond⟩

end SweepData

end RestrictedNoncrossingSweepBounded

end Mettapedia.GraphTheory.FourColor.Compositional
