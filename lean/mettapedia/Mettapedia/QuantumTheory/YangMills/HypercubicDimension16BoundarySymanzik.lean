import Mettapedia.QuantumTheory.YangMills.HypercubicWilsonSymanzikRestoration
import Mettapedia.QuantumTheory.YangMills.V14BoundaryCochainBootstrap

/-!
# Honest dimension-sixteen Wilson coordinates on the boundary complex

The seventeen certified Cartan-octic coordinates are used as the operator
index of the postponed-IBP two-block complex.  The actual Wilson coefficient
vector is recombined globally, and adding a shared-boundary coboundary is
proved not to change it.  The exact two-block Wilson density also inherits a
quantitative `O(a⁴)` rotation-restoration bound.

The coefficient-sup analysis and synthesis constants are rederived on the
seventeen-element basis.  The resulting scalar bootstrap calculation remains
conditional on the unchanged fluctuation, cumulant, and recombination bounds;
no interacting Wilson-RG estimate is inferred from the Cartan calculation.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16BoundarySymanzik

open SU2LatticeFDCensusNoGo
open HypercubicDimension16CartanCensus
open HypercubicWilsonSymanzikRestoration
open V14BoundaryCochainComplex
open V14BoundaryCochainBootstrap

/-! ## Exact boundary-complex placement -/

abbrev HonestOcticBoundaryH0 := TwoBlockBoundaryH0 (Fin 17)

/-- The boundary-complex quotient retains exactly the seventeen independently
certified octic coordinates. -/
theorem honestOcticBoundaryH0_finrank :
    Module.finrank ℝ HonestOcticBoundaryH0 = 17 := by
  rw [twoBlockBoundaryH0_finrank]
  decide

/-- Actual dimension-sixteen Wilson/Symanzik coordinates on each of two
blocks, allowing their lattice spacings to be recorded separately. -/
def actualWilsonOcticBulkCoordinates (a : Fin 2 → ℝ) :
    TwoBlockBulkCoefficients (Fin 17) :=
  fun block coordinate =>
    actualWilsonDimension16SymanzikCoordinate (a block) coordinate

/-- Global recombination adds the two actual Wilson coefficients. -/
theorem globalRecombine_actualWilsonOcticBulkCoordinates
    (a : Fin 2 → ℝ) (coordinate : Fin 17) :
    globalRecombineLinear (Fin 17)
        (actualWilsonOcticBulkCoordinates a) coordinate =
      if coordinate = 0 then
        -(a 0 ^ 12 + a 1 ^ 12) / 20160
      else 0 := by
  change actualWilsonDimension16SymanzikCoordinate (a 0) coordinate +
      actualWilsonDimension16SymanzikCoordinate (a 1) coordinate = _
  rw [actualWilsonDimension16SymanzikCoordinate_eq,
    actualWilsonDimension16SymanzikCoordinate_eq]
  by_cases hcoordinate : coordinate = 0
  · simp [hcoordinate]
    ring
  · simp [hcoordinate]

/-- Adding any shared-boundary current leaves the global Wilson coordinate
vector unchanged. -/
theorem globalRecombine_actualWilsonOctic_add_sharedBoundary
    (a : Fin 2 → ℝ) (current : CensusCoefficients (Fin 17)) :
    globalRecombineLinear (Fin 17)
        (fun block coordinate =>
          actualWilsonOcticBulkCoordinates a block coordinate +
            sharedBoundaryCoboundary current block coordinate) =
      globalRecombineLinear (Fin 17)
        (actualWilsonOcticBulkCoordinates a) := by
  funext coordinate
  simp [globalRecombineLinear, sharedBoundaryCoboundary]
  ring

/-- The actual bulk coordinate vector defines a degree-zero homology class. -/
def actualWilsonOcticBoundaryClass (a : Fin 2 → ℝ) :
    HonestOcticBoundaryH0 :=
  (LinearMap.range (sharedBoundaryCoboundaryLinear (Fin 17))).mkQ
    (actualWilsonOcticBulkCoordinates a)

/-! ## Real conditioning inherited from the exact signed-orbit basis -/

def honestOcticOrbitBasisReal (coordinate : Fin 17)
    (monomial : OcticMonomial) : ℝ :=
  (octicOrbitBasis coordinate monomial : ℝ)

def honestOcticSynthesisReal (coordinates : Fin 17 → ℝ) :
    OcticMonomial → ℝ :=
  fun monomial => ∑ coordinate : Fin 17,
    coordinates coordinate * honestOcticOrbitBasisReal coordinate monomial

def HasHonestOcticCoordinateSupBound
    (coordinates : Fin 17 → ℝ) (C : ℝ) : Prop :=
  ∀ coordinate, |coordinates coordinate| ≤ C

def HasHonestOcticCoefficientSupBound
    (coefficients : OcticMonomial → ℝ) (C : ℝ) : Prop :=
  ∀ monomial, |coefficients monomial| ≤ C

/-- Synthesis on the real extension of the honest octic basis has
coefficient-sup norm at most one. -/
theorem honestOcticSynthesisReal_coefficientSup_le
    (coordinates : Fin 17 → ℝ) {C : ℝ}
    (hC : 0 ≤ C)
    (hbound : HasHonestOcticCoordinateSupBound coordinates C) :
    HasHonestOcticCoefficientSupBound
      (honestOcticSynthesisReal coordinates) C := by
  classical
  intro monomial
  rcases octic_signedOrbit_classification monomial with horbit | hkilled
  · obtain ⟨coordinate, transport, htransport⟩ := horbit
    have hvalue : honestOcticSynthesisReal coordinates monomial =
        coordinates coordinate *
          ((octicRepresentative coordinate).tensorSign transport : ℝ) := by
      unfold honestOcticSynthesisReal honestOcticOrbitBasisReal
      rw [Finset.sum_eq_single coordinate]
      · rw [octicOrbitBasis_of_transport coordinate monomial transport
          htransport]
        norm_cast
      · intro other _ hother
        rw [octicOrbitBasis_eq_zero_of_other_orbit other coordinate monomial
          ⟨transport, htransport⟩ hother]
        norm_num
      · simp
    rw [hvalue, abs_mul]
    rcases (octicRepresentative coordinate).tensorSign_eq_one_or_neg_one
        transport with hsign | hsign <;>
      simp [hsign, hbound coordinate]
  · have hbasis (coordinate : Fin 17) :
        honestOcticOrbitBasisReal coordinate monomial = 0 := by
      unfold honestOcticOrbitBasisReal
      rw [octic_invariant_zero_of_negative_stabilizer
        (octicOrbitBasis coordinate) (octicOrbitBasis_invariant coordinate)
        monomial hkilled]
      norm_num
    simp [honestOcticSynthesisReal, hbasis, hC]

/-- Representative analysis on real coefficients also has factor one. -/
theorem honestOcticDualReal_coefficientSup_le
    (coefficients : OcticMonomial → ℝ) {C : ℝ}
    (hbound : HasHonestOcticCoefficientSupBound coefficients C) :
    HasHonestOcticCoordinateSupBound
      (fun coordinate => honestOcticDualReal coordinate coefficients) C := by
  intro coordinate
  exact hbound (octicRepresentative coordinate)

def honestDimension16ExtractionConstant : ℝ :=
  (octicConditioningConstant : ℝ)

/-- This constant is derived from the honest `17 × 17` identity matrix, not
from the refuted padded carrier. -/
theorem honestDimension16ExtractionConstant_eq_one :
    honestDimension16ExtractionConstant = 1 := by
  norm_num [honestDimension16ExtractionConstant, octicConditioningConstant]

theorem actualWilsonOcticJetCoefficient_eq_synthesis
    (a : ℝ) :
    actualWilsonOcticJetCoefficient a =
      honestOcticSynthesisReal
        (fun coordinate => if coordinate = 0 then -2 * a ^ 12 else 0) := by
  funext monomial
  rw [actualWilsonOcticJetCoefficient_eq_basis]
  unfold honestOcticSynthesisReal honestOcticOrbitBasisReal
  rw [Finset.sum_eq_single 0]
  · simp
  · intro other _ hother
    simp [hother]
  · simp

/-! ## Two-block quantitative restoration -/

def twoBlockNormalizedSU2CartanWilsonDensity
    (a : ℝ) (F : Fin 2 → CartanCurvature) : ℝ :=
  ∑ block : Fin 2, normalizedSU2CartanWilsonDensity a (F block)

/-- The exact two-block Wilson density has the summed quantitative
restoration bound `5/2·a⁴M⁴`. -/
theorem twoBlockNormalizedSU2CartanWilsonDensity_rotation_error
    {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M)
    (R : Matrix (Fin 4) (Fin 4) ℝ) (F : Fin 2 → CartanCurvature)
    (horthogonal : R.transpose * R = 1)
    (hantisymmetric : ∀ block mu nu,
      F block mu nu = -F block nu mu)
    (hcomponent : ∀ (block : Fin 2) (plane : OrientedPlane),
      |F block plane.first plane.second| ≤ M)
    (hrotatedComponent : ∀ (block : Fin 2) (plane : OrientedPlane),
      |rotateCurvature R (F block) plane.first plane.second| ≤ M)
    (hscale : a ^ 2 * M ≤ 1) :
    |twoBlockNormalizedSU2CartanWilsonDensity a
          (fun block => rotateCurvature R (F block)) -
        twoBlockNormalizedSU2CartanWilsonDensity a F| ≤
      (5 / 2 : ℝ) * a ^ 4 * M ^ 4 := by
  have hblock (block : Fin 2) :=
    normalizedSU2CartanWilsonDensity_rotation_error ha hM R (F block)
      horthogonal (hantisymmetric block) (hcomponent block)
      (hrotatedComponent block) hscale
  simp only [twoBlockNormalizedSU2CartanWilsonDensity, Fin.sum_univ_two]
  rw [show
    (normalizedSU2CartanWilsonDensity a (rotateCurvature R (F 0)) +
        normalizedSU2CartanWilsonDensity a (rotateCurvature R (F 1))) -
      (normalizedSU2CartanWilsonDensity a (F 0) +
        normalizedSU2CartanWilsonDensity a (F 1)) =
      (normalizedSU2CartanWilsonDensity a (rotateCurvature R (F 0)) -
        normalizedSU2CartanWilsonDensity a (F 0)) +
      (normalizedSU2CartanWilsonDensity a (rotateCurvature R (F 1)) -
        normalizedSU2CartanWilsonDensity a (F 1)) by ring]
  calc
    |_ + _| ≤
        |normalizedSU2CartanWilsonDensity a (rotateCurvature R (F 0)) -
          normalizedSU2CartanWilsonDensity a (F 0)| +
        |normalizedSU2CartanWilsonDensity a (rotateCurvature R (F 1)) -
          normalizedSU2CartanWilsonDensity a (F 1)| := abs_add_le _ _
    _ ≤ (5 / 4 : ℝ) * a ^ 4 * M ^ 4 +
        (5 / 4 : ℝ) * a ^ 4 * M ^ 4 :=
      add_le_add (hblock 0) (hblock 1)
    _ = (5 / 2 : ℝ) * a ^ 4 * M ^ 4 := by ring

/-! ## Fresh two-source depth arithmetic -/

/-- Product using the newly certified honest-basis extraction constant and
the three explicitly conditional analytic bounds. -/
def honestDimension16RecursionBudget : ℝ :=
  v14WilsonRecursionConstantBudget
    unchangedFluctuationUpperBound
    unchangedCumulantUpperBoundAtTwo
    unchangedRecombinationUpperBound
    honestDimension16ExtractionConstant

theorem honestDimension16RecursionBudget_eq :
    honestDimension16RecursionBudget = (5544 : ℝ) / 5 := by
  norm_num [honestDimension16RecursionBudget,
    v14WilsonRecursionConstantBudget, unchangedFluctuationUpperBound,
    unchangedCumulantUpperBoundAtTwo, unchangedRecombinationUpperBound,
    honestDimension16ExtractionConstant, octicConditioningConstant]

/-- Conditional factor transfer with the honest-basis extraction constant.
The three analytic inequalities remain hypotheses. -/
theorem actualFactors_le_honestDimension16RecursionBudget
    {Cfluct Ccumulant Crecomb : ℝ}
    (_hfluct0 : 0 ≤ Cfluct)
    (hcumulant0 : 0 ≤ Ccumulant)
    (hrecomb0 : 0 ≤ Crecomb)
    (hfluct : Cfluct ≤ unchangedFluctuationUpperBound)
    (hcumulant : Ccumulant ≤ unchangedCumulantUpperBoundAtTwo)
    (hrecomb : Crecomb ≤ unchangedRecombinationUpperBound) :
    v14WilsonRecursionConstantBudget Cfluct Ccumulant Crecomb
        honestDimension16ExtractionConstant ≤
      honestDimension16RecursionBudget := by
  rw [honestDimension16ExtractionConstant_eq_one]
  unfold v14WilsonRecursionConstantBudget
    honestDimension16RecursionBudget
  rw [honestDimension16ExtractionConstant_eq_one]
  unfold v14WilsonRecursionConstantBudget
  norm_num only [mul_one]
  have hpair : Cfluct * Ccumulant ≤
      unchangedFluctuationUpperBound * unchangedCumulantUpperBoundAtTwo :=
    mul_le_mul hfluct hcumulant hcumulant0 (by
      norm_num [unchangedFluctuationUpperBound])
  have hupperPair0 : 0 ≤
      unchangedFluctuationUpperBound * unchangedCumulantUpperBoundAtTwo :=
    mul_nonneg
      (by norm_num [unchangedFluctuationUpperBound])
      (by norm_num [unchangedCumulantUpperBoundAtTwo])
  calc
    Cfluct * Ccumulant * Crecomb ≤
        (unchangedFluctuationUpperBound *
          unchangedCumulantUpperBoundAtTwo) * Crecomb :=
      mul_le_mul_of_nonneg_right hpair hrecomb0
    _ ≤ (unchangedFluctuationUpperBound *
          unchangedCumulantUpperBoundAtTwo) *
          unchangedRecombinationUpperBound :=
      mul_le_mul_of_nonneg_left hrecomb hupperPair0

theorem rgGain_honestDimension16_two_fifteen :
    rgGain honestDimension16RecursionBudget 2 15 =
      (693 : ℝ) / 2560 := by
  rw [honestDimension16RecursionBudget_eq]
  norm_num [rgGain, irrelevantScale]

theorem rgGain_honestDimension16_two_fourteen :
    rgGain honestDimension16RecursionBudget 2 14 =
      (693 : ℝ) / 1280 := by
  rw [honestDimension16RecursionBudget_eq]
  norm_num [rgGain, irrelevantScale]

theorem honestDimension16_twoSourceSlack_fifteen :
    HasTwoSourceBootstrapSlack honestDimension16RecursionBudget 2 15 := by
  refine ⟨?_, ?_⟩
  · rw [honestDimension16RecursionBudget_eq]
    norm_num
  · rw [rgGain_honestDimension16_two_fifteen]
    norm_num

theorem not_honestDimension16_twoSourceSlack_of_depth_le_fourteen
    {depth : ℕ} (hdepth : depth ≤ 14) :
    ¬HasTwoSourceBootstrapSlack
      honestDimension16RecursionBudget 2 depth := by
  intro h
  have hgain := h.2
  rw [honestDimension16RecursionBudget_eq] at hgain
  interval_cases depth <;> norm_num [rgGain, irrelevantScale] at hgain

/-- The two-source scalar ledger closes first at depth fifteen. -/
theorem leastDepth_honestDimension16_packet :
    HasTwoSourceBootstrapSlack honestDimension16RecursionBudget 2 15 ∧
      ∀ depth : ℕ, depth ≤ 14 →
        ¬HasTwoSourceBootstrapSlack
          honestDimension16RecursionBudget 2 depth := by
  exact ⟨honestDimension16_twoSourceSlack_fifteen,
    fun _ hdepth =>
      not_honestDimension16_twoSourceSlack_of_depth_le_fourteen hdepth⟩

/-- Combined MOVE 8B boundary/Symanzik seal.  Its restoration field is the
tree-level two-block Cartan theorem above; the scalar depth field is
conditional on the unchanged analytic factors. -/
theorem move8B_boundarySymanzik_packet
    {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M)
    (R : Matrix (Fin 4) (Fin 4) ℝ) (F : Fin 2 → CartanCurvature)
    (horthogonal : R.transpose * R = 1)
    (hantisymmetric : ∀ block mu nu,
      F block mu nu = -F block nu mu)
    (hcomponent : ∀ (block : Fin 2) (plane : OrientedPlane),
      |F block plane.first plane.second| ≤ M)
    (hrotatedComponent : ∀ (block : Fin 2) (plane : OrientedPlane),
      |rotateCurvature R (F block) plane.first plane.second| ≤ M)
    (hscale : a ^ 2 * M ≤ 1) :
    Module.finrank ℝ HonestOcticBoundaryH0 = 17 ∧
    honestDimension16ExtractionConstant = 1 ∧
    |twoBlockNormalizedSU2CartanWilsonDensity a
          (fun block => rotateCurvature R (F block)) -
        twoBlockNormalizedSU2CartanWilsonDensity a F| ≤
      (5 / 2 : ℝ) * a ^ 4 * M ^ 4 ∧
    honestDimension16RecursionBudget = (5544 : ℝ) / 5 ∧
    HasTwoSourceBootstrapSlack honestDimension16RecursionBudget 2 15 := by
  exact ⟨honestOcticBoundaryH0_finrank,
    honestDimension16ExtractionConstant_eq_one,
    twoBlockNormalizedSU2CartanWilsonDensity_rotation_error ha hM R F
      horthogonal hantisymmetric hcomponent hrotatedComponent hscale,
    honestDimension16RecursionBudget_eq,
    honestDimension16_twoSourceSlack_fifteen⟩

end HypercubicDimension16BoundarySymanzik
end YangMills
end QuantumTheory
end Mettapedia
