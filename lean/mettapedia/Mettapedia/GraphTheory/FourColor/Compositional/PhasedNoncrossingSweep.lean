import Mettapedia.GraphTheory.FourColor.GoertzelV24NoncrossingSweepLifo
import Mettapedia.GraphTheory.FourColor.GoertzelV24SphereCutMaterial

/-!
# Spaced repetitions in finite noncrossing sweeps

A finite sweep state may repeat at adjacent positions, which by itself need
not enclose any material.  Augmenting its local letter by the position modulo
`spacing + 1` forces two distinct equal states to be separated by at least one
full period.

This construction is independent of planar graphs.  It is the linear-order
counterpart of the phased-state device used for strict material in tree
decompositions.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.PhasedNoncrossingSweep

open GoertzelV24NoncrossingSweepLifo
open GoertzelV24SphereCutMaterial

universe u v

/-- The cyclic phase of one finite sweep position.  Using `spacing + 1`
makes the carrier nonempty even when the requested spacing is zero. -/
def positionPhase {n : Nat} (spacing : Nat) (position : Fin n) :
    Fin (spacing + 1) :=
  ⟨position.val % (spacing + 1), Nat.mod_lt _ (by omega)⟩

/-- Add a position phase to the local letter of a sweep without changing any
of its matching families. -/
def SweepData.withPositionPhase {A : Type u} {K : Type v} {r n : Nat}
    (data : SweepData A K r n) (spacing : Nat) :
    SweepData (A × Fin (spacing + 1)) K r n where
  letter position := ⟨data.letter position, positionPhase spacing position⟩
  family := data.family

namespace SweepData

variable {A : Type u} {K : Type v} {r n : Nat}

/-- Equality of phased states forgets to equality of the underlying sweep
states. -/
theorem rawState_eq_of_withPositionPhase_rawState_eq
    (data : SweepData A K r n) (spacing : Nat)
    {first second : Fin n}
    (heq : (withPositionPhase data spacing).rawState first =
      (withPositionPhase data spacing).rawState second) :
    data.rawState first = data.rawState second := by
  apply Prod.ext
  · exact congrArg (fun state => state.1.1) heq
  · have hstacks := congrArg Prod.snd heq
    simpa [GoertzelV24NoncrossingSweepLifo.SweepData.rawState,
      withPositionPhase] using hstacks

/-- Equality of phased states at two ordered positions forces the requested
linear separation. -/
theorem spacing_add_one_le_sub_of_withPositionPhase_rawState_eq
    (data : SweepData A K r n) (spacing : Nat)
    {first second : Fin n} (hlt : first < second)
    (heq : (withPositionPhase data spacing).rawState first =
      (withPositionPhase data spacing).rawState second) :
    spacing + 1 ≤ second.val - first.val := by
  have hphase := congrArg (fun state => state.1.2.val) heq
  change first.val % (spacing + 1) = second.val % (spacing + 1) at hphase
  exact period_le_sub_of_mod_eq hlt hphase

/-- **Phased noncrossing length--depth alternative.**  If the sweep is
longer than the exact number of bounded stacks, local letters, and phases,
then it has either a deep matching stack or a pair of equal phased states
whose positions differ by at least `spacing + 1`. -/
theorem exists_deep_family_or_spaced_eq_rawState
    [Fintype A] [DecidableEq A] [Fintype K] [DecidableEq K]
    (data : SweepData A K r n) (depth spacing : Nat)
    (hmany :
      Fintype.card A * (spacing + 1) *
          (∑ d : Fin (depth + 1), Fintype.card K ^ (d : Nat)) ^ r < n) :
    (∃ family cut, depth < ((data.family family).stackAt cut).length) ∨
      ∃ first second : Fin n,
        first < second ∧ spacing + 1 ≤ second.val - first.val ∧
          (withPositionPhase data spacing).rawState first =
            (withPositionPhase data spacing).rawState second := by
  have hmany' :
      Fintype.card (A × Fin (spacing + 1)) *
          (∑ d : Fin (depth + 1), Fintype.card K ^ (d : Nat)) ^ r < n := by
    simpa [Fintype.card_prod] using hmany
  rcases
      GoertzelV24NoncrossingSweepLifo.SweepData.exists_deep_family_or_distinct_eq_rawState
          (data := withPositionPhase data spacing) depth hmany' with
    hdeep | ⟨first, second, hne, heq⟩
  · left
    simpa [withPositionPhase] using hdeep
  · right
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨first, second, hlt,
        spacing_add_one_le_sub_of_withPositionPhase_rawState_eq
          data spacing hlt heq,
        heq⟩
    · exact ⟨second, first, hgt,
        spacing_add_one_le_sub_of_withPositionPhase_rawState_eq
          data spacing hgt heq.symm,
        heq.symm⟩

end SweepData

end Mettapedia.GraphTheory.FourColor.Compositional.PhasedNoncrossingSweep
