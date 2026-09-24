import Mettapedia.Analysis.FundamentalDomainPeriodization
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Standard lattice geometry for finite-dimensional unit tori

The canonical coordinate cell, Haar measure and Euclidean Fourier character
are identified explicitly. This dimension-independent geometry supports
both single-input and frequency-pair periodization.
-/

set_option autoImplicit false
noncomputable section
namespace Mettapedia.Analysis.UnitTorusLattice
open MeasureTheory Set
open scoped ENNReal FourierTransform Pointwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "Rd" => EuclideanSpace ℝ ι

def standardBasis :
    Module.Basis ι ℝ Rd :=
  (EuclideanSpace.basisFun ι ℝ).toBasis

abbrev LatticeSubmodule :
    Submodule ℤ Rd :=
  Submodule.span ℤ (Set.range (standardBasis (ι := ι)))

abbrev latticeBasis :
    Module.Basis ι ℤ (LatticeSubmodule (ι := ι)) :=
  (standardBasis (ι := ι)).restrictScalars ℤ

abbrev latticeEquiv :
    (LatticeSubmodule (ι := ι)) ≃ₗ[ℤ] (ι → ℤ) :=
  (latticeBasis (ι := ι)).repr.trans
    (Finsupp.linearEquivFunOnFinite ℤ ℤ ι)

instance : Countable (LatticeSubmodule (ι := ι)) :=
  (latticeEquiv (ι := ι)).injective.countable

abbrev Lattice :=
  (LatticeSubmodule (ι := ι)).toAddSubgroup

instance : Countable (Lattice (ι := ι)) := by
  let f : (Lattice (ι := ι)) →
      (LatticeSubmodule (ι := ι)) := fun x ↦ ⟨x.1, x.2⟩
  have hf : Function.Injective f := fun x y h ↦
    Subtype.ext (congrArg Subtype.val h)
  exact hf.countable

def cell : Set Rd :=
  ZSpan.fundamentalDomain (standardBasis (ι := ι))

omit [DecidableEq ι] in
theorem cell_isAddFundamentalDomain :
    IsAddFundamentalDomain (Lattice (ι := ι))
      (cell (ι := ι))
      (volume : Measure Rd) := by
  exact ZSpan.isAddFundamentalDomain' (standardBasis (ι := ι)) volume

abbrev Wavevector := ι → ℤ

def frequency
    (n : Wavevector (ι := ι)) : Rd :=
  WithLp.toLp 2 (fun i ↦ (n i : ℝ))

def character
    (n : Wavevector (ι := ι)) (x : Rd) : ℂ :=
  Real.fourierChar (-(inner ℝ x (frequency n)))

omit [DecidableEq ι] in
@[fun_prop]
theorem continuous_character
    (n : Wavevector (ι := ι)) :
    Continuous (character n) := by
  unfold character frequency
  fun_prop

omit [DecidableEq ι] in
theorem norm_character
    (n : Wavevector (ι := ι)) (x : Rd) :
    ‖character n x‖ = 1 := by
  unfold character
  exact Circle.norm_coe _

omit [DecidableEq ι] in
theorem inner_frequency
    (x : Rd) (n : Wavevector (ι := ι)) :
    inner ℝ x (frequency n) =
      ∑ i : ι, x i * (n i : ℝ) := by
  simp [frequency, PiLp.inner_apply,
    RCLike.inner_apply, mul_comm]

theorem exists_integerCoordinates
    (g : (Lattice (ι := ι))) :
    ∃ z : ι → ℤ,
      (g : Rd) =
        WithLp.toLp 2 (fun i ↦ (z i : ℝ)) := by
  obtain ⟨z, hz⟩ :=
    (Submodule.mem_span_range_iff_exists_fun ℤ).mp g.property
  refine ⟨z, ?_⟩
  rw [← hz]
  classical
  ext i
  simp [standardBasis, EuclideanSpace.basisFun_apply,
    Pi.single_apply]

theorem character_vadd
    (n : Wavevector (ι := ι)) (g : (Lattice (ι := ι)))
    (x : Rd) :
    character n (g +ᵥ x) =
      character n x := by
  rcases (exists_integerCoordinates (ι := ι)) g with
    ⟨z, hz⟩
  let m : ℤ := ∑ i : ι, z i * n i
  have hginner :
      inner ℝ (g : Rd)
          (frequency n) = (m : ℝ) := by
    rw [hz, (inner_frequency (ι := ι))]
    simp [m]
  have hinner :
      inner ℝ (g +ᵥ x) (frequency n) =
        (m : ℝ) +
          inner ℝ x (frequency n) := by
    rw [show g +ᵥ x = (g : Rd) + x by rfl,
      inner_add_left, hginner]
  have hmchar : Real.fourierChar (-(m : ℝ)) = 1 := by
    rw [Real.fourierChar_apply']
    have harg : 2 * Real.pi * -(m : ℝ) =
        (-m : ℤ) * (2 * Real.pi) := by
      push_cast
      ring
    rw [harg, Circle.exp_intCast_mul, Circle.exp_two_pi, one_zpow]
  unfold character
  rw [hinner, neg_add, Real.fourierChar.map_add_eq_mul, hmchar, Circle.coe_mul,
    Circle.coe_one, one_mul]

omit [DecidableEq ι] in
theorem mFourier_neg_coe_eq_character
    (n : Wavevector (ι := ι)) (x : ι → ℝ) :
    UnitAddTorus.mFourier (-n)
        (fun i ↦ (x i : UnitAddCircle)) =
      character n (WithLp.toLp 2 x) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.neg_apply,
    fourier_coe_apply]
  unfold character
  rw [(inner_frequency (ι := ι)), Real.fourierChar_apply]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  simp only [div_one]
  calc
    (∑ i : ι,
        2 * (Real.pi : ℂ) * Complex.I * -(n i : ℂ) * (x i : ℂ)) =
        ∑ i : ι,
          -(2 * (Real.pi : ℂ) * Complex.I *
            ((x i : ℂ) * (n i : ℂ))) := by
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = -(∑ i : ι,
          2 * (Real.pi : ℂ) * Complex.I *
            ((x i : ℂ) * (n i : ℂ))) := by
      rw [Finset.sum_neg_distrib]
    _ = -(2 * (Real.pi : ℂ) * Complex.I *
          (∑ i : ι, (x i : ℂ) * (n i : ℂ))) := by
      rw [Finset.mul_sum]
    _ = (2 * (Real.pi : ℂ) *
          -(∑ i : ι, (x i : ℂ) * (n i : ℂ))) *
          Complex.I := by
      ring

def rawCellIco : Set (ι → ℝ) :=
  {x | ∀ i, x i ∈ Ico (0 : ℝ) 1}

def rawCellIoc : Set (ι → ℝ) :=
  {x | ∀ i, x i ∈ Ioc (0 : ℝ) 1}

omit [DecidableEq ι] in
theorem preimage_cell_toLp :
    (WithLp.toLp 2 : (ι → ℝ) → Rd) ⁻¹'
        (cell (ι := ι)) = (rawCellIco (ι := ι)) := by
  ext x
  simp [cell, rawCellIco,
    ZSpan.mem_fundamentalDomain, standardBasis,
    EuclideanSpace.basisFun_repr]

omit [DecidableEq ι] in
theorem rawCellIco_ae_eq_Ioc :
    (rawCellIco (ι := ι)) =ᵐ[(volume : Measure (ι → ℝ))]
      (rawCellIoc (ι := ι)) := by
  rw [volume_pi]
  have h :=
    ((Measure.univ_pi_Ico_ae_eq_Icc
      (μ := fun _ : ι ↦ (volume : Measure ℝ))
      (f := fun _ : ι ↦ (0 : ℝ))
      (g := fun _ : ι ↦ (1 : ℝ))).trans
    (Measure.univ_pi_Ioc_ae_eq_Icc
      (μ := fun _ : ι ↦ (volume : Measure ℝ))
      (f := fun _ : ι ↦ (0 : ℝ))
      (g := fun _ : ι ↦ (1 : ℝ))).symm)
  have hIco : (rawCellIco (ι := ι)) =
      Set.pi Set.univ (fun _ : ι ↦ Ico (0 : ℝ) 1) := by
    ext x
    simp only [rawCellIco, Set.mem_setOf_eq, Set.mem_pi,
      Set.mem_univ, forall_true_left]
  have hIoc : (rawCellIoc (ι := ι)) =
      Set.pi Set.univ (fun _ : ι ↦ Ioc (0 : ℝ) 1) := by
    ext x
    simp only [rawCellIoc, Set.mem_setOf_eq, Set.mem_pi,
      Set.mem_univ, forall_true_left]
  rw [hIco, hIoc]
  exact h

def representative
    (q : UnitAddTorus ι) : Rd :=
  WithLp.toLp 2 (fun i ↦ (AddCircle.equivIoc 1 0 (q i)).1)

omit [Fintype ι] [DecidableEq ι] in
theorem measurable_representative :
    Measurable (representative (ι := ι)) := by
  exact (MeasurableEquiv.toLp 2 (ι → ℝ)).measurable.comp
    (measurable_subtype_coe.comp
      (UnitAddTorus.measurableEquivPiIoc
        (fun _ : ι ↦ (0 : ℝ))).measurable)

omit [Fintype ι] [DecidableEq ι] in
theorem representative_coe
    (x : ι → ℝ) (hx : x ∈ (rawCellIoc (ι := ι))) :
    (representative (ι := ι)) (fun i ↦ (x i : UnitAddCircle)) =
      WithLp.toLp 2 x := by
  have hx' : ∀ i, x i ∈ Ioc (0 : ℝ) 1 := by
    simpa [rawCellIoc] using hx
  unfold representative
  apply congrArg (WithLp.toLp 2)
  funext i
  exact congrArg Subtype.val
    (AddCircle.equivIoc_coe_eq (p := (1 : ℝ)) (a := (0 : ℝ))
      (by simpa using hx' i))

end Mettapedia.Analysis.UnitTorusLattice
