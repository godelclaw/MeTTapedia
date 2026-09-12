import Mettapedia.Analysis.UnitTorusPeriodization

/-! # Differences of real lifts and the standard integer lattice -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.UnitTorusLattice

open UnitTorusPeriodization

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "Rd" => EuclideanSpace ℝ ι

omit [Fintype ι] [DecidableEq ι] in
theorem torusProjection_add (x y : Rd) :
    torusProjection (x + y) = torusProjection x + torusProjection y := by
  funext i
  change ((x i + y i : ℝ) : UnitAddCircle) = (x i : UnitAddCircle) + (y i : UnitAddCircle)
  exact AddCircle.coe_add (p := (1 : ℝ)) (x i) (y i)

omit [Fintype ι] [DecidableEq ι] in
theorem torusProjection_sub (x y : Rd) :
    torusProjection (x - y) = torusProjection x - torusProjection y := by
  funext i
  change ((x i - y i : ℝ) : UnitAddCircle) = (x i : UnitAddCircle) - (y i : UnitAddCircle)
  exact AddCircle.coe_sub (p := (1 : ℝ)) (x i) (y i)

theorem torusProjection_eq_zero_iff_mem (x : Rd) :
    torusProjection x = 0 ↔ x ∈ LatticeSubmodule (ι := ι) := by
  constructor
  · intro hx
    have hi (i : ι) : ∃ n : ℤ, (n : ℝ) = x i := by
      have h := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp (congrFun hx i)
      simpa only [zsmul_eq_mul, mul_one] using h
    choose z hz using hi
    apply (Submodule.mem_span_range_iff_exists_fun ℤ).mpr
    refine ⟨z, ?_⟩
    ext i
    simpa [standardBasis, EuclideanSpace.basisFun_apply, Pi.single_apply] using hz i
  · intro hx
    have h := torusProjection_vadd (⟨x, hx⟩ : Lattice (ι := ι)) (0 : Rd)
    change torusProjection (x + 0) = torusProjection (0 : Rd) at h
    have hz : torusProjection (0 : Rd) = 0 := by
      funext i
      exact AddCircle.coe_zero (p := (1 : ℝ))
    simpa only [add_zero, hz] using h

theorem sub_mem_lattice_of_projection_eq {x y : Rd} (h : torusProjection x = torusProjection y) :
    x - y ∈ LatticeSubmodule (ι := ι) := by
  apply (torusProjection_eq_zero_iff_mem _).mp
  rw [torusProjection_sub, h, sub_self]

end Mettapedia.Analysis.UnitTorusLattice
