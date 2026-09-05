import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeMovingBlockEvolution
import Mathlib.Topology.PartitionOfUnity

/-!
# Adaptive finite covers for freezing the strain field

A fixed finite spatial grid cannot approximate an arbitrary continuous strain
field to every prescribed tolerance.  The legitimate replacement is an
adaptive cover: for each continuous field and each positive tolerance,
compactness selects finitely many centers whose field-value neighborhoods
cover the domain.

This file proves that statement first for a continuous map from any compact
space into a normed additive group, then specializes it to spatial and
space--time strain fields on the unit three-torus.  The centers and their
neighborhoods may depend on the field and tolerance, as they must.  No
partition of unity or scale-critical estimate is asserted here.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeAdaptiveStrainCover

open PancakeFrameCovariance

local notation "R3" => EuclideanSpace ℝ (Fin 3)

/-- The neighborhood of a center on which a continuous field differs from
its center value by less than `epsilon`. -/
def freezingNeighborhood {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] (A : X → E) (epsilon : ℝ) (center : X) :
    Set X :=
  {x | ‖A x - A center‖ < epsilon}

theorem isOpen_freezingNeighborhood {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] (A : X → E) (hA : Continuous A)
    (epsilon : ℝ) (center : X) :
    IsOpen (freezingNeighborhood A epsilon center) := by
  exact isOpen_lt (hA.sub continuous_const).norm continuous_const

theorem mem_freezingNeighborhood_self {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] (A : X → E) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (center : X) :
    center ∈ freezingNeighborhood A epsilon center := by
  simp [freezingNeighborhood, hepsilon]

/-! ## Cell-count-free aggregation -/

/-- A subordinate partition averages pointwise freezing errors with no loss
depending on the number of cells. -/
theorem sum_weight_mul_freezingError_le
    {X E ι : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
    [Fintype ι]
    (weight : PartitionOfUnity ι X) (A : X → E) (center : ι → X)
    (epsilon : ℝ)
    (hactive : ∀ i x, weight i x ≠ 0 →
      ‖A x - A (center i)‖ ≤ epsilon)
    (x : X) :
    ∑ i : ι, weight i x * ‖A x - A (center i)‖ ≤ epsilon := by
  have hsum : (∑ i : ι, weight i x) = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using
      weight.sum_eq_one (Set.mem_univ x)
  calc
    ∑ i : ι, weight i x * ‖A x - A (center i)‖ ≤
        ∑ i : ι, weight i x * epsilon := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hzero : weight i x = 0
      · simp [hzero]
      · exact mul_le_mul_of_nonneg_left (hactive i x hzero)
          (weight.nonneg i x)
    _ = (∑ i : ι, weight i x) * epsilon := by
      rw [Finset.sum_mul]
    _ = epsilon := by rw [hsum, one_mul]

/-- Quadratic version used by energy estimates. -/
theorem sum_weight_mul_sq_freezingError_le
    {X E ι : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
    [Fintype ι]
    (weight : PartitionOfUnity ι X) (A : X → E) (center : ι → X)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hactive : ∀ i x, weight i x ≠ 0 →
      ‖A x - A (center i)‖ ≤ epsilon)
    (x : X) :
    ∑ i : ι, weight i x * ‖A x - A (center i)‖ ^ 2 ≤
      epsilon ^ 2 := by
  have hsum : (∑ i : ι, weight i x) = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using
      weight.sum_eq_one (Set.mem_univ x)
  calc
    ∑ i : ι, weight i x * ‖A x - A (center i)‖ ^ 2 ≤
        ∑ i : ι, weight i x * epsilon ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hzero : weight i x = 0
      · simp [hzero]
      · have hnorm : 0 ≤ ‖A x - A (center i)‖ := norm_nonneg _
        have hsquare : ‖A x - A (center i)‖ ^ 2 ≤ epsilon ^ 2 := by
          nlinarith [hactive i x hzero]
        exact mul_le_mul_of_nonneg_left hsquare (weight.nonneg i x)
    _ = (∑ i : ι, weight i x) * epsilon ^ 2 := by
      rw [Finset.sum_mul]
    _ = epsilon ^ 2 := by rw [hsum, one_mul]

/-- Applying the strain errors to one vector preserves the same cell-count
free bound, at the expected cost of the vector norm. -/
theorem sum_weight_mul_norm_strainError_apply_le
    {X ι : Type*} [TopologicalSpace X] [Fintype ι]
    (weight : PartitionOfUnity ι X)
    (strain : X → (R3 →L[ℝ] R3)) (center : ι → X)
    (epsilon : ℝ)
    (hactive : ∀ i x, weight i x ≠ 0 →
      ‖strain x - strain (center i)‖ ≤ epsilon)
    (x : X) (v : R3) :
    ∑ i : ι, weight i x *
        ‖(strain x - strain (center i)) v‖ ≤ epsilon * ‖v‖ := by
  have havg := sum_weight_mul_freezingError_le
    weight strain center epsilon hactive x
  calc
    ∑ i : ι, weight i x *
        ‖(strain x - strain (center i)) v‖ ≤
        ∑ i : ι, weight i x *
          (‖strain x - strain (center i)‖ * ‖v‖) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.le_opNorm _ _) (weight.nonneg i x)
    _ = (∑ i : ι, weight i x *
        ‖strain x - strain (center i)‖) * ‖v‖ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ epsilon * ‖v‖ :=
      mul_le_mul_of_nonneg_right havg (norm_nonneg v)

/-- Every continuous normed-group-valued field on a compact space admits a
finite adaptive freezing cover at every positive tolerance. -/
theorem exists_finite_adaptive_freezing_cover
    {X E : Type*} [TopologicalSpace X] [CompactSpace X]
    [NormedAddCommGroup E]
    (A : X → E) (hA : Continuous A) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ centers : Finset X, ∀ x : X, ∃ center ∈ centers,
      ‖A x - A center‖ < epsilon := by
  let U : X → Set X := freezingNeighborhood A epsilon
  have hnhds : ∀ center : X, U center ∈ nhds center := by
    intro center
    exact (isOpen_freezingNeighborhood A hA epsilon center).mem_nhds
      (mem_freezingNeighborhood_self A hepsilon center)
  obtain ⟨centers, hcover⟩ := CompactSpace.elim_nhds_subcover U hnhds
  refine ⟨centers, ?_⟩
  intro x
  have hx : x ∈ ⋃ center ∈ centers, U center := by
    rw [hcover]
    trivial
  rcases Set.mem_iUnion.mp hx with ⟨center, hx⟩
  rcases Set.mem_iUnion.mp hx with ⟨hcenter, hx⟩
  exact ⟨center, hcenter, hx⟩

/-- Spatial specialization: at each positive tolerance, a continuous strain
field on the unit three-torus has finitely many frozen operator values that
approximate it pointwise. -/
theorem exists_finite_adaptive_spatial_strain_cover
    (strain : UnitAddTorus (Fin 3) → (R3 →L[ℝ] R3))
    (hstrain : Continuous strain) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ centers : Finset (UnitAddTorus (Fin 3)),
      ∀ x : UnitAddTorus (Fin 3), ∃ center ∈ centers,
        ‖strain x - strain center‖ < epsilon := by
  exact exists_finite_adaptive_freezing_cover strain hstrain hepsilon

/-- The adaptive spatial cover can be equipped with a continuous partition
of unity subordinate to the same operator-closeness neighborhoods.  Hence a
nonzero weight at `x` certifies the desired local freezing estimate at `x`;
there is no global requirement that one frozen operator approximate the field
outside its own cell. -/
theorem exists_finite_adaptive_spatial_strain_partition
    (strain : UnitAddTorus (Fin 3) → (R3 →L[ℝ] R3))
    (hstrain : Continuous strain) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ (centers : Finset (UnitAddTorus (Fin 3)))
      (weight : PartitionOfUnity (↑centers) (UnitAddTorus (Fin 3))),
      weight.IsSubordinate (fun center ↦
        freezingNeighborhood strain epsilon center.1) ∧
      ∀ (center : ↑centers) (x : UnitAddTorus (Fin 3)),
        weight center x ≠ 0 →
          ‖strain x - strain center.1‖ < epsilon := by
  obtain ⟨centers, hcenters⟩ :=
    exists_finite_adaptive_spatial_strain_cover strain hstrain hepsilon
  let U : (↑centers) → Set (UnitAddTorus (Fin 3)) :=
    fun center ↦ freezingNeighborhood strain epsilon center.1
  have hopen : ∀ center, IsOpen (U center) := by
    intro center
    exact isOpen_freezingNeighborhood strain hstrain epsilon center.1
  have hcover : (Set.univ : Set (UnitAddTorus (Fin 3))) ⊆
      ⋃ center, U center := by
    intro x hx
    obtain ⟨center, hcenter, hclose⟩ := hcenters x
    exact Set.mem_iUnion.mpr ⟨⟨center, hcenter⟩, hclose⟩
  obtain ⟨weight, hsubordinate⟩ :=
    PartitionOfUnity.exists_isSubordinate isClosed_univ U hopen hcover
  refine ⟨centers, weight, hsubordinate, ?_⟩
  intro center x hx
  exact hsubordinate center (subset_closure hx)

/-- Space--time specialization.  A continuous strain field on a compact time
interval times the unit torus admits one finite cover at the requested
tolerance, avoiding any measurable choice of a new spatial grid at each
time. -/
theorem exists_finite_adaptive_spacetime_strain_cover
    (T : ℝ)
    (strain : (Set.Icc (0 : ℝ) T × UnitAddTorus (Fin 3)) →
      (R3 →L[ℝ] R3))
    (hstrain : Continuous strain) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ centers : Finset (Set.Icc (0 : ℝ) T × UnitAddTorus (Fin 3)),
      ∀ z : Set.Icc (0 : ℝ) T × UnitAddTorus (Fin 3),
        ∃ center ∈ centers, ‖strain z - strain center‖ < epsilon := by
  exact exists_finite_adaptive_freezing_cover strain hstrain hepsilon

/-- Continuous partition-of-unity form of the space--time cover.  This is the
version suited to time integration: the finite index set is chosen once on
the compact cylinder, and every active weight carries its own pointwise
strain-freezing certificate. -/
theorem exists_finite_adaptive_spacetime_strain_partition
    (T : ℝ)
    (strain : (Set.Icc (0 : ℝ) T × UnitAddTorus (Fin 3)) →
      (R3 →L[ℝ] R3))
    (hstrain : Continuous strain) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ (centers : Finset
        (Set.Icc (0 : ℝ) T × UnitAddTorus (Fin 3)))
      (weight : PartitionOfUnity (↑centers)
        (Set.Icc (0 : ℝ) T × UnitAddTorus (Fin 3))),
      weight.IsSubordinate (fun center ↦
        freezingNeighborhood strain epsilon center.1) ∧
      ∀ (center : ↑centers)
        (z : Set.Icc (0 : ℝ) T × UnitAddTorus (Fin 3)),
        weight center z ≠ 0 →
          ‖strain z - strain center.1‖ < epsilon := by
  obtain ⟨centers, hcenters⟩ :=
    exists_finite_adaptive_spacetime_strain_cover
      T strain hstrain hepsilon
  let U : (↑centers) →
      Set (Set.Icc (0 : ℝ) T × UnitAddTorus (Fin 3)) :=
    fun center ↦ freezingNeighborhood strain epsilon center.1
  have hopen : ∀ center, IsOpen (U center) := by
    intro center
    exact isOpen_freezingNeighborhood strain hstrain epsilon center.1
  have hcover :
      (Set.univ : Set
        (Set.Icc (0 : ℝ) T × UnitAddTorus (Fin 3))) ⊆
        ⋃ center, U center := by
    intro z hz
    obtain ⟨center, hcenter, hclose⟩ := hcenters z
    exact Set.mem_iUnion.mpr ⟨⟨center, hcenter⟩, hclose⟩
  obtain ⟨weight, hsubordinate⟩ :=
    PartitionOfUnity.exists_isSubordinate isClosed_univ U hopen hcover
  refine ⟨centers, weight, hsubordinate, ?_⟩
  intro center z hz
  exact hsubordinate center (subset_closure hz)

end PancakeAdaptiveStrainCover
end NavierStokes
end FluidDynamics
end Mettapedia
