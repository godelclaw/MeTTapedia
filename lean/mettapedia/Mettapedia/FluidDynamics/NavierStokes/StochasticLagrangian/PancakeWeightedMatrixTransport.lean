import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeWeightedWeakTransport

/-!
# A signed matrix-weighted transport identity

For a symmetric locally Lipschitz matrix weight, twice the transport pairing
is minus the pairing with the transported weight. All derivatives are the
actual weak periodic coordinate derivatives, including those of the weight.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeWeightedMatrixTransport

open MeasureTheory
open PancakeWeakIncompressibleTransport PancakeWeightedWeakTransport PancakeFourierMaterialPaths

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {ι : Type*} [Fintype ι]

def matrixTransportPairing (A : ι → ι → T3 → ℝ) (w : ι → T3 → ℝ)
    (v : Fin 3 → T3 → ℝ) (x : T3) : ℝ :=
  ∑ i, ∑ j, A i j x * w i x * coordinateTransport (w j) v x

def matrixWeightVariation (A : ι → ι → T3 → ℝ) (w : ι → T3 → ℝ)
    (v : Fin 3 → T3 → ℝ) (x : T3) : ℝ :=
  ∑ i, ∑ j, coordinateTransport (A i j) v x * w i x * w j x

theorem integral_matrixTransportPairing
    (A : ι → ι → T3 → ℝ) (w : ι → T3 → ℝ) (v : Fin 3 → T3 → ℝ)
    (hA : ∀ i j, Continuous (A i j)) (hw : ∀ i, Continuous (w i))
    (hAL : ∀ i j, LocallyLipschitz (fun r : X3 ↦ A i j (torusPoint r)))
    (hwL : ∀ i, LocallyLipschitz (fun r : X3 ↦ w i (torusPoint r)))
    (hsym : ∀ i j x, A i j x = A j i x)
    (hv : ∀ j, Continuous (v j))
    (hvL : ∀ j, LocallyLipschitz (fun r : X3 ↦ v j (torusPoint r)))
    (hdiv : ∀ᵐ x : T3, coordinateDivergence v x = 0) :
    Integrable (matrixTransportPairing A w v) ∧ Integrable (matrixWeightVariation A w v) ∧
      2 * (∫ x : T3, matrixTransportPairing A w v x) =
        -(∫ x : T3, matrixWeightVariation A w v x) := by
  have hP : ∀ i j, Integrable (fun x : T3 ↦ A i j x * w i x * coordinateTransport (w j) v x) := by
    intro i j
    simpa only [mul_comm] using integrable_transport_times v hv hvL hdiv
      (w j) (fun x ↦ A i j x * w i x) (hw j) ((hA i j).mul (hw i)) (hwL j)
  have hQ : ∀ i j, Integrable (fun x : T3 ↦ coordinateTransport (A i j) v x * w i x * w j x) := by
    intro i j
    simpa only [mul_assoc] using integrable_transport_times v hv hvL hdiv
      (A i j) (fun x ↦ w i x * w j x) (hA i j) ((hw i).mul (hw j)) (hAL i j)
  have hPI := integrable_finsetSum Finset.univ (fun i _ ↦ integrable_finsetSum Finset.univ (fun j _ ↦ hP i j))
  have hQI := integrable_finsetSum Finset.univ (fun i _ ↦ integrable_finsetSum Finset.univ (fun j _ ↦ hQ i j))
  refine ⟨hPI, hQI, ?_⟩
  have he : (∑ i, ∑ j,
      ((∫ x : T3, A i j x * w i x * coordinateTransport (w j) v x) +
       (∫ x : T3, A i j x * w j x * coordinateTransport (w i) v x))) =
      ∑ i, ∑ j, -(∫ x : T3, coordinateTransport (A i j) v x * w i x * w j x) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact integral_weighted_transport v hv hvL hdiv (A i j) (w i) (w j)
      (hA i j) (hw i) (hw j) (hAL i j) (hwL i) (hwL j)
  have hswap : (∑ i, ∑ j, ∫ x : T3, A i j x * w j x * coordinateTransport (w i) v x) =
      ∑ i, ∑ j, ∫ x : T3, A i j x * w i x * coordinateTransport (w j) v x := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp_rw [hsym j i]
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib] at he
  rw [hswap] at he
  unfold matrixTransportPairing matrixWeightVariation
  rw [integral_finsetSum Finset.univ (fun i _ ↦ integrable_finsetSum Finset.univ (fun j _ ↦ hP i j)),
    integral_finsetSum Finset.univ (fun i _ ↦ integrable_finsetSum Finset.univ (fun j _ ↦ hQ i j))]
  simp_rw [integral_finsetSum Finset.univ (fun j _ ↦ hP _ j),
    integral_finsetSum Finset.univ (fun j _ ↦ hQ _ j)]
  linarith

end Mettapedia.FluidDynamics.NavierStokes.PancakeWeightedMatrixTransport
