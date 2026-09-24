import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeInfiniteDirectionalTransport

/-!
# Differentiating an evolving infinite Fourier field along a real path

The material derivative is obtained term by term with a summable common
envelope. Both coefficient evolution and character motion are retained.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeInfiniteMaterialSeries

open scoped BigOperators
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicVorticityEquation
open PancakeFourierMaterialPaths PancakeIndexedFourierMoments PancakeInfiniteFourierDerivative
open PancakeCurlOutputTail PancakeInfiniteVelocityLipschitz PancakeInfiniteDirectionalTransport
open PancakeConcreteSmoothCellCutoff

local notation "X3" => Fin 3 → ℝ

theorem hasDerivAt_materialMode (u du : ℝ → FourierVelocity)
    (X v : ℝ → X3) (t : ℝ) (q : Wavevector)
    (hu : ∀ i, HasDerivAt (fun τ ↦ u τ q i) (du t q i) t)
    (hX : HasDerivAt X (v t) t) :
    HasDerivAt (fun τ ↦ UnitAddTorus.mFourier q (torusPoint (X τ)) • u τ q)
      (UnitAddTorus.mFourier q (torusPoint (X t)) • du t q +
        UnitAddTorus.mFourier q (torusPoint (X t)) • directionalCoeff (u t) (v t) q) t := by
  have h := (hasDerivAt_mFourier_torusPoint q X (v t) t
    (hasDerivAt_pi.mp hX)).smul (hasDerivAt_pi.mpr hu)
  apply h.congr_deriv
  simp only [directionalCoeff, smul_smul]
  congr 1
  rw [mul_comm (unitTorusDerivativePhase * _) _]

theorem hasDerivAt_fullFourierField_material (u du : ℝ → FourierVelocity)
    (X v : ℝ → X3) (I : Set ℝ) (hI : IsOpen I) (hc : IsPreconnected I)
    (g h : Wavevector → ℝ) (_hg : ∀ q, 0 ≤ g q)
    (hSum : Summable g) (hhSum : Summable h) (M : ℝ) (hM : 0 ≤ M)
    (hu : ∀ τ ∈ I, ∀ q, fourierMoment 1 (u τ) q ≤ g q)
    (hdu : ∀ τ ∈ I, ∀ q, ‖du τ q‖ ≤ h q)
    (hd : ∀ τ ∈ I, ∀ q i, HasDerivAt (fun r ↦ u r q i) (du τ q i) τ)
    (hX : ∀ τ ∈ I, HasDerivAt X (v τ) τ)
    (hv : ∀ τ ∈ I, ‖v τ‖ ≤ M) (t : ℝ) (ht : t ∈ I) :
    HasDerivAt (fun τ ↦ fullFourierField id (u τ) (torusPoint (X τ)))
      (fullFourierField id (du t) (torusPoint (X t)) +
        fullFourierField id (directionalCoeff (u t) (v t)) (torusPoint (X t))) t := by
  have ha (τ) (hτ : τ ∈ I) : Summable (fun q ↦ ‖u τ q‖) :=
    hSum.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun q ↦
      (norm_coefficient_le_indexedFirstMoment id _ q).trans
        (by simpa only [indexedFirstMoment_id] using hu τ hτ q))
  have hb (τ) (hτ : τ ∈ I) (q) :
      ‖directionalCoeff (u τ) (v τ) q‖ ≤ (3 * (2 * Real.pi) * M) * g q := by
    apply (norm_directionalCoeff_le _ _ q).trans
    gcongr
    · exact fourierMoment_nonneg _ _ _
    · exact hv τ hτ
    · exact hu τ hτ q
  have hds := hhSum.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (hdu t ht)
  have hms := (hSum.mul_left (3 * (2 * Real.pi) * M)).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) (hb t ht)
  have hs (a : FourierVelocity) (has : Summable (fun q ↦ ‖a q‖)) :
      Summable (fun q ↦ UnitAddTorus.mFourier q (torusPoint (X t)) • a q) :=
    has.of_norm_bounded (fun q ↦ by rw [norm_smul, norm_mFourier_apply, one_mul])
  have H := hasDerivAt_tsum_of_isPreconnected
    (hhSum.add (hSum.mul_left (3 * (2 * Real.pi) * M))) hI hc
    (fun q τ hτ ↦ hasDerivAt_materialMode u du X v τ q (hd τ hτ q) (hX τ hτ))
    (fun q τ hτ ↦ (norm_add_le _ _).trans (add_le_add
      (by simpa only [norm_smul, norm_mFourier_apply, one_mul] using hdu τ hτ q)
      (by simpa only [norm_smul, norm_mFourier_apply, one_mul] using hb τ hτ q)))
    ht (hs (u t) (ha t ht)) ht
  rw [(hs (du t) hds).tsum_add (hs (directionalCoeff (u t) (v t)) hms)] at H
  rw [fullFourierField_apply id (du t) hds,
    fullFourierField_apply id (directionalCoeff (u t) (v t)) hms]
  apply H.congr_of_eventuallyEq
  filter_upwards [hI.mem_nhds ht] with τ hτ
  exact fullFourierField_apply id (u τ) (ha τ hτ) (torusPoint (X τ))

end Mettapedia.FluidDynamics.NavierStokes.PancakeInfiniteMaterialSeries
