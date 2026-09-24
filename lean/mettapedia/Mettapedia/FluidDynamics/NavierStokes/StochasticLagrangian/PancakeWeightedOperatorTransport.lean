import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeWeightedMatrixTransport

/-!
# Operator form of the weak weighted transport identity

The matrix entries are constructed in the canonical Euclidean basis. The
resulting pairing is the genuine inner product with the operator applied to
the field. The weight variation uses actual scalar weak derivatives of its
entries, not an independently assigned operator derivative.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeWeightedOperatorTransport

open MeasureTheory
open scoped RealInnerProductSpace
open PancakeWeightedMatrixTransport PancakeWeakIncompressibleTransport PancakeFourierMaterialPaths

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "B" => EuclideanSpace.basisFun (Fin 3) ℝ

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def operatorEntries (K : T3 → R3 →L[ℝ] R3) (i j : Fin 3) (x : T3) : ℝ := (K x (B j)) i

def vectorTransport (w : T3 → R3) (v : Fin 3 → T3 → ℝ) (x : T3) : R3 :=
  WithLp.toLp 2 (fun i ↦ coordinateTransport (fun y ↦ w y i) v x)

theorem operator_apply_coordinate (K : R3 →L[ℝ] R3) (w : R3) (i : Fin 3) :
    K w i = ∑ j : Fin 3, w j * K (B j) i := by
  have h := congrArg (fun z : R3 ↦ K z i) ((EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr w)
  simpa only [map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
    EuclideanSpace.basisFun_repr, smul_eq_mul] using h.symm

theorem operatorEntries_symmetric (K : T3 → R3 →L[ℝ] R3)
    (hK : ∀ x a b, ⟪a, K x b⟫ = ⟪K x a, b⟫) (i j : Fin 3) (x : T3) :
    operatorEntries K i j x = operatorEntries K j i x := by
  simpa only [EuclideanSpace.basisFun_inner, EuclideanSpace.inner_basisFun_real, operatorEntries]
    using hK x (B i) (B j)

theorem continuous_operatorEntries (K : T3 → R3 →L[ℝ] R3) (hK : Continuous K) (i j : Fin 3) :
    Continuous (operatorEntries K i j) :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 ↦ ℝ) i).continuous.comp
    (hK.clm_apply continuous_const)

theorem locallyLipschitz_operatorEntries (K : T3 → R3 →L[ℝ] R3)
    (hK : LocallyLipschitz (fun r : X3 ↦ K (torusPoint r))) (i j : Fin 3) :
    LocallyLipschitz (fun r : X3 ↦ operatorEntries K i j (torusPoint r)) := by
  have hobs : ContDiff ℝ 1 (fun A : R3 →L[ℝ] R3 ↦ A (B j) i) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 ↦ ℝ) i).contDiff.comp
      (contDiff_id.clm_apply contDiff_const)
  exact hobs.locallyLipschitz.comp hK

theorem matrixTransportPairing_eq_inner (K : T3 → R3 →L[ℝ] R3) (w : T3 → R3)
    (v : Fin 3 → T3 → ℝ) (hK : ∀ x a b, ⟪a, K x b⟫ = ⟪K x a, b⟫) (x : T3) :
    matrixTransportPairing (operatorEntries K) (fun i y ↦ w y i) v x =
      ⟪K x (w x), vectorTransport w v x⟫ := by
  rw [← hK x (w x) (vectorTransport w v x)]
  change (∑ i : Fin 3, ∑ j : Fin 3, operatorEntries K i j x * w x i *
    coordinateTransport (fun y ↦ w y j) v x) =
      ∑ i : Fin 3, (K x (vectorTransport w v x)) i * w x i
  apply Finset.sum_congr rfl
  intro i _
  rw [operator_apply_coordinate, Finset.sum_mul]
  simp only [vectorTransport, PiLp.toLp_apply, operatorEntries]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem integral_operatorTransport
    (K : T3 → R3 →L[ℝ] R3) (w : T3 → R3) (v : Fin 3 → T3 → ℝ)
    (hK : Continuous K) (hw : Continuous w)
    (hKL : LocallyLipschitz (fun r : X3 ↦ K (torusPoint r)))
    (hwL : LocallyLipschitz (fun r : X3 ↦ w (torusPoint r)))
    (hsym : ∀ x a b, ⟪a, K x b⟫ = ⟪K x a, b⟫)
    (hv : ∀ j, Continuous (v j))
    (hvL : ∀ j, LocallyLipschitz (fun r : X3 ↦ v j (torusPoint r)))
    (hdiv : ∀ᵐ x : T3, coordinateDivergence v x = 0) :
    Integrable (fun x ↦ ⟪K x (w x), vectorTransport w v x⟫) ∧
      Integrable (matrixWeightVariation (operatorEntries K) (fun i y ↦ w y i) v) ∧
      2 * (∫ x : T3, ⟪K x (w x), vectorTransport w v x⟫) =
        -(∫ x : T3, matrixWeightVariation (operatorEntries K) (fun i y ↦ w y i) v x) := by
  have hwc : ∀ i, Continuous (fun x : T3 ↦ w x i) := fun i ↦
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 ↦ ℝ) i).continuous.comp hw
  have hwcL : ∀ i, LocallyLipschitz (fun r : X3 ↦ w (torusPoint r) i) := fun i ↦
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 ↦ ℝ) i).lipschitz.locallyLipschitz.comp hwL
  have h := integral_matrixTransportPairing (operatorEntries K) (fun i y ↦ w y i) v
    (continuous_operatorEntries K hK) hwc (locallyLipschitz_operatorEntries K hKL) hwcL
    (operatorEntries_symmetric K hsym) hv hvL hdiv
  have he : matrixTransportPairing (operatorEntries K) (fun i y ↦ w y i) v =
      (fun x ↦ ⟪K x (w x), vectorTransport w v x⟫) :=
    funext (matrixTransportPairing_eq_inner K w v hsym)
  rw [he] at h
  exact h

end Mettapedia.FluidDynamics.NavierStokes.PancakeWeightedOperatorTransport
