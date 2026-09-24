import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PeriodicGradientFluxProduct

/-!
# Actual triple Fourier products and their gradient-active image

The two scalar factors and the vector factor are reconstructed before
projection. Absolute coefficient summability proves the nested product
identities and the convergence of the triple-indexed `L²` image.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PeriodicGradientFluxTriple

open Mettapedia.Analysis UnitTorusGradientProjection ContinuousFieldBilinear
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeInfiniteFourierDerivative PancakeInfiniteRealCurl PancakePhysicalFourierDerivative
open PancakeDyadicDirectionEvolution PancakeTransverseEnergyFreezing PancakeBlockReality
open PeriodicGradientFluxSymbol PeriodicGradientFluxProduct LongitudinalVorticityTime

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureTheory.MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

def indexedProductCoeff {ι κ : Type*} (a : ι → VelocityCoefficient) (b : κ → VelocityCoefficient)
    (j : Fin 3) (p : ι × κ) : VelocityCoefficient := a p.1 j • b p.2

theorem summable_norm_indexedProductCoeff {ι κ : Type*}
    (a : ι → VelocityCoefficient) (b : κ → VelocityCoefficient)
    (ha : Summable (fun n ↦ ‖a n‖)) (hb : Summable (fun n ↦ ‖b n‖)) (j : Fin 3) :
    Summable (fun p ↦ ‖indexedProductCoeff a b j p‖) :=
  BilinearSeries.summable_norm_apply (coordinateSmul j) a b ha hb

theorem fullFourierField_indexedProduct {ι κ : Type*} (fa : ι → Wavevector) (fb : κ → Wavevector)
    (a : ι → VelocityCoefficient) (b : κ → VelocityCoefficient)
    (ha : Summable (fun n ↦ ‖a n‖)) (hb : Summable (fun n ↦ ‖b n‖)) (j : Fin 3) (x : T3) :
    fullFourierField (fun p : ι × κ ↦ fa p.1 + fb p.2) (indexedProductCoeff a b j) x =
      fullFourierField fa a x j • fullFourierField fb b x := by
  have hna : Summable (fun k ↦ ‖UnitAddTorus.mFourier (fa k) x • a k‖) := by
    simpa only [norm_smul, norm_character, one_mul] using ha
  have hnb : Summable (fun k ↦ ‖UnitAddTorus.mFourier (fb k) x • b k‖) := by
    simpa only [norm_smul, norm_character, one_mul] using hb
  have he := (BilinearSeries.hasSum_apply (coordinateSmul j)
    (fun k ↦ UnitAddTorus.mFourier (fa k) x • a k)
    (fun k ↦ UnitAddTorus.mFourier (fb k) x • b k) hna hnb).tsum_eq
  have hmode (p : ι × κ) : coordinateSmul j
      (UnitAddTorus.mFourier (fa p.1) x • a p.1) (UnitAddTorus.mFourier (fb p.2) x • b p.2) =
      UnitAddTorus.mFourier (fa p.1 + fb p.2) x • indexedProductCoeff a b j p := by
    change (UnitAddTorus.mFourier (fa p.1) x * a p.1 j) •
      (UnitAddTorus.mFourier (fb p.2) x • b p.2) = _
    simp only [indexedProductCoeff, UnitAddTorus.mFourier_add, smul_smul]
    congr 1
    ring
  simp_rw [hmode] at he
  rw [fullFourierField_apply _ _ (summable_norm_indexedProductCoeff a b ha hb j),
    fullFourierField_apply fa a ha, fullFourierField_apply fb b hb]
  exact he

abbrev TripleIndex := Wavevector × (Wavevector × Wavevector)

def tripleFrequency (p : TripleIndex) : Wavevector := p.1 + (p.2.1 + p.2.2)

def tripleCoeff (a b c : FourierVelocity) (i j : Fin 3) : TripleIndex → VelocityCoefficient :=
  indexedProductCoeff a (indexedProductCoeff b c i) j

theorem summable_norm_tripleCoeff (a b c : FourierVelocity)
    (ha : Summable (fun n ↦ ‖a n‖)) (hb : Summable (fun n ↦ ‖b n‖))
    (hc : Summable (fun n ↦ ‖c n‖)) (i j : Fin 3) :
    Summable (fun p ↦ ‖tripleCoeff a b c i j p‖) :=
  summable_norm_indexedProductCoeff a _ ha (summable_norm_indexedProductCoeff b c hb hc i) j

theorem fullFourierField_tripleCoeff (a b c : FourierVelocity)
    (ha : Summable (fun n ↦ ‖a n‖)) (hb : Summable (fun n ↦ ‖b n‖))
    (hc : Summable (fun n ↦ ‖c n‖)) (i j : Fin 3) (x : T3) :
    fullFourierField tripleFrequency (tripleCoeff a b c i j) x =
      fullFourierField id a x j • (fullFourierField id b x i • fullFourierField id c x) := by
  change fullFourierField (fun p : TripleIndex ↦ id p.1 + (p.2.1 + p.2.2))
    (indexedProductCoeff a (indexedProductCoeff b c i) j) x = _
  rw [fullFourierField_indexedProduct id (fun p : Wavevector × Wavevector ↦ p.1 + p.2)
    a _ ha (summable_norm_indexedProductCoeff b c hb hc i)]
  have hi := fullFourierField_indexedProduct id id b c hb hc i x
  change fullFourierField (fun p : Wavevector × Wavevector ↦ p.1 + p.2)
    (indexedProductCoeff b c i) x = _ at hi
  rw [hi]

def tripleField (a b c : FourierVelocity) (i j : Fin 3) : C(T3, R3) :=
  pointwise (ContinuousLinearMap.lsmul ℝ ℝ) (componentField j (realField a)) (productField b c i)

theorem tripleField_eq_tripleFourierField (a b c : FourierVelocity)
    (ha : Summable (fun n ↦ ‖a n‖)) (hb : Summable (fun n ↦ ‖b n‖))
    (hc : Summable (fun n ↦ ‖c n‖))
    (hra : ∀ n, a (-n) = coefficientConjugate (a n))
    (hrb : ∀ n, b (-n) = coefficientConjugate (b n)) (i j : Fin 3) :
    tripleField a b c i j = (complexRealPartEuclideanCLM.compLeftContinuous ℝ T3)
      (fullFourierField tripleFrequency (tripleCoeff a b c i j)) := by
  ext x l
  have hai := fullFourierField_im_zero a ha hra x j
  have hbi := fullFourierField_im_zero b hb hrb x i
  change (fullFourierField id a x j).re *
    ((fullFourierField id b x i).re * (fullFourierField id c x l).re) =
      (fullFourierField tripleFrequency (tripleCoeff a b c i j) x l).re
  rw [fullFourierField_tripleCoeff a b c ha hb hc]
  simp only [Pi.smul_apply, smul_eq_mul, Complex.mul_re, hai, hbi, zero_mul, sub_zero]

theorem gradientProjection_tripleField (a b c : FourierVelocity)
    (ha : Summable (fun n ↦ ‖a n‖)) (hb : Summable (fun n ↦ ‖b n‖))
    (hc : Summable (fun n ↦ ‖c n‖))
    (hra : ∀ n, a (-n) = coefficientConjugate (a n))
    (hrb : ∀ n, b (-n) = coefficientConjugate (b n)) (i : Fin 3) :
    gradientProjection (toTensorL2 (tripleField a b c i)) =
      ∑' p : TripleIndex, toTensorL2 (fun j ↦ realMode (tripleFrequency p)
        (projectedCoeff (tripleFrequency p) (fun l ↦ tripleCoeff a b c i l p) j)) := by
  have he : tripleField a b c i = fun j ↦ (complexRealPartEuclideanCLM.compLeftContinuous ℝ T3)
      (fullFourierField tripleFrequency (tripleCoeff a b c i j)) :=
    funext (tripleField_eq_tripleFourierField a b c ha hb hc hra hrb i)
  rw [he]
  exact gradientProjection_indexedFourier tripleFrequency (tripleCoeff a b c i)
    (summable_norm_tripleCoeff a b c ha hb hc i)

end Mettapedia.FluidDynamics.NavierStokes.PeriodicGradientFluxTriple
