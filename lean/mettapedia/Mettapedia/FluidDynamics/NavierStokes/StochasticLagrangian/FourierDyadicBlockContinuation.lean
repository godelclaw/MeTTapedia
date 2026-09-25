import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierVorticitySupContinuation
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalKineticEnergy
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeArbitraryDataBlocks
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFixedOutputVelocityBound
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeExteriorReconstructionTail

/-!
# Littlewood–Paley blocks of the actual vorticity and continuation

For the actual periodic Fourier solutions this module constructs the objects
of the transported dyadic relaxation estimate:

* the hard dyadic blocks `Δ_q ω` of the actual vorticity on the shells
  `2^q ≤ |k| < 2^(q+1)` of `PancakeArbitraryDataBlocks`;
* their spatial suprema `blockSup q = ‖Δ_q ω‖_∞`;
* the high-block sum `highBlockSum Q = D_Q = ∑_{q ≥ Q} ‖Δ_q ω‖_∞`, which is
  finite and continuous in time along every local solution;
* the pointwise decomposition `|ω(x)| ≤ |S_Q ω(x)| + D_Q`, where `S_Q ω` is
  the part on `|k| < 2^Q`.

Because the low part is bounded by the nonincreasing kinetic energy,
`exists_tameSolutionOn_of_highBlockSum` gives tame solutions on every
interval `[0, H)`, provided the time integral of `D_Q` of every tame solution
is bounded on each finite horizon. This is the periodic form of the
conclusion that the conditional pancake route draws from its sector
estimates; those estimates remain open.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierDyadicBlockContinuation

open scoped BigOperators Topology
open MeasureTheory Set Filter
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeSobolevWeights PancakeSobolevVelocityRate PancakeHigherSobolevWeights
open PancakeHigherSobolevVelocityRate PancakeCurlOutputTail PancakeLatticeDecayEnvelope
open PancakeHigherLocalVelocity PancakeGalerkinKineticEnergy PancakeLocalInfiniteVelocity
open InfiniteFourierParseval LocalLowDiffusionBudget PancakeInfiniteFourierDerivative
open PancakeHigherDerivativeMoments PancakeDyadicDirectionEvolution PancakeInfiniteSpatialCurl
open PancakeArbitraryDataBlocks PancakePeriodicComplexStretch LocalVorticityDiffusion
open FourierTameTriad FourierContinuation FourierTameContinuation FourierEighthMomentControl
open FourierVorticitySupContinuation InfiniteConvectionEnergy InfiniteKineticCancellation
open PancakeBlockReality

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

section Modes

/-- The low modes `|k| < 2^Q`. -/
def lowModes (Q : ℕ) : Finset Wavevector :=
  (wavevectorBox (2 * dyadicRadius Q)).filter fun k ↦ modeSquareNat k < 4 ^ Q

theorem mem_lowModes (Q : ℕ) (k : Wavevector) : k ∈ lowModes Q ↔ modeSquareNat k < 4 ^ Q := by
  constructor
  · intro hk
    exact (Finset.mem_filter.mp hk).2
  · intro hk
    refine Finset.mem_filter.mpr ⟨mem_wavevectorBox_two_mul_of_modeSquareNat_lt ?_, hk⟩
    rw [dyadicRadius_sq]
    omega

/-- The shells `Q, …, Q + N - 1`. -/
def annulusModes (Q N : ℕ) : Finset Wavevector :=
  (Finset.range N).biUnion fun n ↦ dyadicShellModes (Q + n)

theorem pairwiseDisjoint_shells (Q N : ℕ) :
    (↑(Finset.range N) : Set ℕ).PairwiseDisjoint (fun n ↦ dyadicShellModes (Q + n)) :=
  fun _ _ _ _ hab ↦ disjoint_dyadicShellModes_of_ne (by omega)

theorem disjoint_low_annulus (Q N : ℕ) : Disjoint (lowModes Q) (annulusModes Q N) := by
  rw [Finset.disjoint_left]
  intro k hl ha
  obtain ⟨n, _, hk⟩ := Finset.mem_biUnion.mp ha
  have h1 := (mem_lowModes Q k).mp hl
  have h2 := ((mem_dyadicShellModes_iff_pow_four (Q + n) k).mp hk).1
  have h3 : 4 ^ Q ≤ 4 ^ (Q + n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- The low modes together with the first `N` shells above them. -/
def boxModes (Q N : ℕ) : Finset Wavevector := lowModes Q ∪ annulusModes Q N

theorem monotone_boxModes (Q : ℕ) : Monotone (boxModes Q) := fun _ _ h ↦
  Finset.union_subset_union le_rfl
    (Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.range_mono h))

theorem exists_mem_boxModes (Q : ℕ) (k : Wavevector) : ∃ N, k ∈ boxModes Q N := by
  by_cases hk : modeSquareNat k < 4 ^ Q
  · exact ⟨0, Finset.mem_union_left _ ((mem_lowModes Q k).mpr hk)⟩
  · have hpos : 1 ≤ 4 ^ Q := Nat.one_le_pow Q 4 (by norm_num)
    have h0 : modeSquareNat k ≠ 0 := by omega
    obtain ⟨q, hq⟩ := exists_mem_dyadicShellModes k h0
    have hqQ : Q ≤ q := by
      by_contra h
      have h4 := ((mem_dyadicShellModes_iff_pow_four q k).mp hq).2
      have h5 : 4 ^ (q + 1) ≤ 4 ^ Q := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    refine ⟨q - Q + 1, Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨q - Q, Finset.mem_range.mpr (by omega), ?_⟩)⟩
    rw [show Q + (q - Q) = q by omega]
    exact hq

theorem tendsto_boxModes (Q : ℕ) : Tendsto (boxModes Q) atTop atTop :=
  tendsto_atTop_finset_of_monotone (monotone_boxModes Q) (exists_mem_boxModes Q)

/-- Partial shell sums of a nonnegative summable family stay below its sum. -/
theorem sum_range_shell_le (Q N : ℕ) (h : Wavevector → ℝ) (h0 : ∀ k, 0 ≤ h k)
    (hs : Summable h) :
    ∑ n ∈ Finset.range N, ∑ k ∈ dyadicShellModes (Q + n), h k ≤ ∑' k, h k := by
  rw [← Finset.sum_biUnion (pairwiseDisjoint_shells Q N)]
  exact hs.sum_le_tsum _ (fun k _ ↦ h0 k)

theorem summable_shell_sums (Q : ℕ) (h : Wavevector → ℝ) (h0 : ∀ k, 0 ≤ h k)
    (hs : Summable h) :
    Summable (fun n ↦ ∑ k ∈ dyadicShellModes (Q + n), h k) :=
  summable_of_sum_range_le (fun _ ↦ Finset.sum_nonneg fun k _ ↦ h0 k)
    (fun N ↦ sum_range_shell_le Q N h h0 hs)

end Modes

section Blocks

/-- The complex reconstruction of the vorticity coefficients over a finite set. -/
def vorticityPart (s : Finset Wavevector) (u : FourierVelocity) (x : T3) : VelocityCoefficient :=
  ∑ k ∈ s, UnitAddTorus.mFourier k x • fourierCurl u k

/-- The hard Littlewood–Paley block `Δ_q ω` of the actual vorticity. -/
def vorticityBlock (q : ℕ) (u : FourierVelocity) (x : T3) : R3 :=
  complexRealPartEuclideanCLM (vorticityPart (dyadicShellModes q) u x)

/-- The low-frequency part `S_Q ω` on `|k| < 2^Q`. -/
def lowVorticity (Q : ℕ) (u : FourierVelocity) (x : T3) : R3 :=
  complexRealPartEuclideanCLM (vorticityPart (lowModes Q) u x)

/-- The block supremum `‖Δ_q ω‖_∞`. -/
def blockSup (q : ℕ) (u : FourierVelocity) : ℝ := ⨆ x : T3, ‖vorticityBlock q u x‖

/-- The high-block sum `D_Q = ∑_{q ≥ Q} ‖Δ_q ω‖_∞`. -/
def highBlockSum (Q : ℕ) (u : FourierVelocity) : ℝ := ∑' n : ℕ, blockSup (Q + n) u

theorem norm_realPart_vorticityPart_le (s : Finset Wavevector) (u : FourierVelocity) (x : T3) :
    ‖complexRealPartEuclideanCLM (vorticityPart s u x)‖ ≤
      ∑ k ∈ s, ‖coefficientVec (fourierCurl u k)‖ := by
  rw [complexRealPartEuclideanCLM_apply]
  refine (PancakeExteriorReconstructionTail.norm_realPart_le_coefficientVec _).trans ?_
  rw [vorticityPart, PancakeFixedOutputVelocityBound.coefficientVec_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
  have h1 : ‖UnitAddTorus.mFourier k x‖ ≤ 1 :=
    (ContinuousMap.norm_coe_le_norm _ x).trans_eq (UnitAddTorus.mFourier_norm (n := k))
  have hs : coefficientVec (UnitAddTorus.mFourier k x • fourierCurl u k) =
      UnitAddTorus.mFourier k x • coefficientVec (fourierCurl u k) := rfl
  rw [hs, norm_smul]
  calc ‖UnitAddTorus.mFourier k x‖ * ‖coefficientVec (fourierCurl u k)‖
      ≤ 1 * ‖coefficientVec (fourierCurl u k)‖ := by gcongr
    _ = _ := one_mul _

theorem norm_coefficientVec_fourierCurl_le (u : FourierVelocity) (k : Wavevector) :
    ‖coefficientVec (fourierCurl u k)‖ ≤ 2 * Real.pi * fourierMoment 1 u k := by
  have h := fourierMoment_curl_le 0 u k
  simpa only [fourierMoment, pow_zero, one_mul, zero_add] using h

theorem summable_curlMass (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    Summable (fun k ↦ ‖coefficientVec (fourierCurl u k)‖) :=
  (hu.mul_left (2 * Real.pi)).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (norm_coefficientVec_fourierCurl_le u)

theorem continuous_vorticityBlock (q : ℕ) (u : FourierVelocity) :
    Continuous (vorticityBlock q u) :=
  complexRealPartEuclideanCLM.continuous.comp
    (continuous_finsetSum _ fun k _ ↦ (UnitAddTorus.mFourier k).continuous.smul continuous_const)

theorem blockSup_nonneg (q : ℕ) (u : FourierVelocity) : 0 ≤ blockSup q u :=
  Real.iSup_nonneg fun _ ↦ norm_nonneg _

theorem norm_vorticityBlock_le_blockSup (q : ℕ) (u : FourierVelocity) (x : T3) :
    ‖vorticityBlock q u x‖ ≤ blockSup q u :=
  le_ciSup (isCompact_range (continuous_vorticityBlock q u).norm).bddAbove x

theorem blockSup_le (q : ℕ) (u : FourierVelocity) :
    blockSup q u ≤ ∑ k ∈ dyadicShellModes q, ‖coefficientVec (fourierCurl u k)‖ :=
  ciSup_le fun x ↦ norm_realPart_vorticityPart_le _ u x

theorem summable_blockSup (Q : ℕ) (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    Summable (fun n ↦ blockSup (Q + n) u) :=
  (summable_shell_sums Q _ (fun _ ↦ norm_nonneg _) (summable_curlMass u hu)).of_nonneg_of_le
    (fun _ ↦ blockSup_nonneg _ u) (fun _ ↦ blockSup_le _ u)

theorem highBlockSum_nonneg (Q : ℕ) (u : FourierVelocity) : 0 ≤ highBlockSum Q u :=
  tsum_nonneg fun _ ↦ blockSup_nonneg _ u

/-- **Littlewood–Paley decomposition of the actual vorticity:** at every point
the vorticity is bounded by its low part plus the high-block sum. -/
theorem norm_fullVorticity_le_low_add_high (Q : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (x : T3) :
    ‖fullVorticity u x‖ ≤ ‖lowVorticity Q u x‖ + highBlockSum Q u := by
  let f : Wavevector → VelocityCoefficient := fun k ↦ UnitAddTorus.mFourier k x • fourierCurl u k
  have hfs : Summable f := by
    refine (FullVorticityFourierCoefficients.summable_norm_fourierCurl u hu).of_norm_bounded
      fun k ↦ ?_
    have h1 : ‖UnitAddTorus.mFourier k x‖ ≤ 1 :=
      (ContinuousMap.norm_coe_le_norm _ x).trans_eq (UnitAddTorus.mFourier_norm (n := k))
    calc ‖f k‖ = ‖UnitAddTorus.mFourier k x‖ * ‖fourierCurl u k‖ := norm_smul _ _
      _ ≤ 1 * ‖fourierCurl u k‖ := by gcongr
      _ = _ := one_mul _
  have hsum : HasSum f (fullFourierField id (fourierCurl u) x) := by
    rw [fullFourierField_apply id _ (FullVorticityFourierCoefficients.summable_norm_fourierCurl u hu)]
    exact hfs.hasSum
  have ht : Tendsto (fun s : Finset Wavevector ↦ ∑ k ∈ s, f k) atTop
      (𝓝 (fullFourierField id (fourierCurl u) x)) := by
    simpa only [HasSum, SummationFilter.unconditional] using hsum
  have hre := ((complexRealPartEuclideanCLM.continuous.tendsto _).comp
    (ht.comp (tendsto_boxModes Q))).norm
  have hω : fullVorticity u x =
      complexRealPartEuclideanCLM (fullFourierField id (fourierCurl u) x) := by
    unfold fullVorticity
    rw [spatialCurl_velocity u hu]
  rw [hω]
  refine le_of_tendsto hre (Eventually.of_forall fun N ↦ ?_)
  have hsplit : (∑ k ∈ boxModes Q N, f k) =
      vorticityPart (lowModes Q) u x +
        ∑ n ∈ Finset.range N, vorticityPart (dyadicShellModes (Q + n)) u x := by
    rw [boxModes, Finset.sum_union (disjoint_low_annulus Q N), annulusModes,
      Finset.sum_biUnion (pairwiseDisjoint_shells Q N)]
    rfl
  simp only [Function.comp_apply]
  rw [hsplit, map_add, map_sum]
  calc ‖complexRealPartEuclideanCLM (vorticityPart (lowModes Q) u x) +
        ∑ n ∈ Finset.range N,
          complexRealPartEuclideanCLM (vorticityPart (dyadicShellModes (Q + n)) u x)‖
      ≤ ‖lowVorticity Q u x‖ + ∑ n ∈ Finset.range N, ‖vorticityBlock (Q + n) u x‖ :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ ‖lowVorticity Q u x‖ + ∑ n ∈ Finset.range N, blockSup (Q + n) u :=
        add_le_add le_rfl (Finset.sum_le_sum fun _ _ ↦ norm_vorticityBlock_le_blockSup _ u x)
    _ ≤ ‖lowVorticity Q u x‖ + highBlockSum Q u :=
        add_le_add le_rfl ((summable_blockSup Q u hu).sum_le_tsum _
          (fun _ _ ↦ blockSup_nonneg _ u))

/-- The constant of the low-frequency bound. -/
def lowConst (Q : ℕ) : ℝ := ∑ k ∈ lowModes Q, 2 * Real.pi * (1 + ‖frequencyVec k‖)

theorem lowConst_nonneg (Q : ℕ) : 0 ≤ lowConst Q :=
  Finset.sum_nonneg fun k _ ↦ by positivity

/-- The low part is bounded by any common bound on the modal energies. -/
theorem norm_lowVorticity_le (Q : ℕ) (u : FourierVelocity) {E : ℝ}
    (hE : ∀ k, coefficientEnergy (u k) ≤ E) (x : T3) :
    ‖lowVorticity Q u x‖ ≤ lowConst Q * Real.sqrt E := by
  refine (norm_realPart_vorticityPart_le _ u x).trans ?_
  rw [lowConst, Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ ↦ ?_
  have hk : ‖coefficientVec (u k)‖ ≤ Real.sqrt E := by
    rw [← Real.sqrt_sq (norm_nonneg (coefficientVec (u k))), norm_coefficientVec_sq]
    exact Real.sqrt_le_sqrt (hE k)
  calc ‖coefficientVec (fourierCurl u k)‖ ≤ 2 * Real.pi * fourierMoment 1 u k :=
        norm_coefficientVec_fourierCurl_le u k
    _ = 2 * Real.pi * (1 + ‖frequencyVec k‖) * ‖coefficientVec (u k)‖ := by
        simp only [fourierMoment, pow_one]
        ring
    _ ≤ 2 * Real.pi * (1 + ‖frequencyVec k‖) * Real.sqrt E := by gcongr

theorem coefficientEnergy_le_kineticEnergy (u : FourierVelocity)
    (hu : Summable (fun q ↦ ‖u q‖)) (k : Wavevector) :
    coefficientEnergy (u k) ≤ kineticEnergy u := by
  rw [kineticEnergy_eq_tsum_coefficientEnergy]
  exact (hasSum_coefficientEnergy u hu).summable.le_tsum k fun j _ ↦ by
    rw [← norm_coefficientVec_sq]
    positivity

end Blocks

section Time

variable {nu T B : ℝ} {u₀ : FourierVelocity}

theorem continuous_fourierCurl_along (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (k : Wavevector) :
    Continuous (fun t : Icc (0 : ℝ) T ↦ fourierCurl (s.coefficients t) k) := by
  refine continuous_pi fun i ↦ ?_
  have hc (j : Fin 3) : Continuous (fun t : Icc (0 : ℝ) T ↦ s.coefficients t k j) :=
    (s.continuous k j).comp continuous_subtype_val
  fin_cases i <;> simp only [fourierCurl, coefficientCross, Pi.smul_apply, smul_eq_mul] <;>
    fun_prop

theorem continuousOn_blockSup (s : LocalInfiniteVelocitySolution nu u₀ T B) (q : ℕ) :
    ContinuousOn (fun t ↦ blockSup q (s.coefficients t)) (Icc 0 T) := by
  have hc : Continuous (fun z : Icc (0 : ℝ) T × T3 ↦ ‖vorticityBlock q (s.coefficients z.1) z.2‖) := by
    refine (complexRealPartEuclideanCLM.continuous.comp (continuous_finsetSum _ fun k _ ↦ ?_)).norm
    exact ((UnitAddTorus.mFourier k).continuous.comp continuous_snd).smul
      ((continuous_fourierCurl_along s k).comp continuous_fst)
  have h := IsCompact.continuous_sSup
    (f := fun (t : Icc (0 : ℝ) T) (x : T3) ↦ ‖vorticityBlock q (s.coefficients t) x‖)
    (K := univ) isCompact_univ hc
  refine continuousOn_iff_continuous_domRestrict.mpr ?_
  have h' : Continuous fun t : Icc (0 : ℝ) T ↦
      ⨆ x : T3, ‖vorticityBlock q (s.coefficients t) x‖ := by
    simpa only [image_univ, sSup_range] using h
  exact h'

/-- The high-block sum is continuous in time along a local solution with a
common first-moment envelope. -/
theorem continuousOn_highBlockSum (s : LocalInfiniteVelocitySolution nu u₀ T B) (Q : ℕ)
    (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k) (hSum : Summable g)
    (hu : ∀ t ∈ Icc (0 : ℝ) T, ∀ k, fourierMoment 1 (s.coefficients t) k ≤ g k) :
    ContinuousOn (fun t ↦ highBlockSum Q (s.coefficients t)) (Icc 0 T) := by
  refine continuousOn_iff_continuous_domRestrict.mpr ?_
  have hM := summable_shell_sums Q (fun k ↦ 2 * Real.pi * g k)
    (fun k ↦ mul_nonneg (by positivity) (hg k)) (hSum.mul_left _)
  refine continuous_tsum (f := fun n (t : Icc (0 : ℝ) T) ↦ blockSup (Q + n) (s.coefficients t))
    (fun n ↦ continuousOn_iff_continuous_domRestrict.mp (continuousOn_blockSup s (Q + n))) hM
    (fun n t ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (blockSup_nonneg _ _)]
  refine (blockSup_le _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
  exact (norm_coefficientVec_fourierCurl_le _ k).trans
    (mul_le_mul_of_nonneg_left (hu t t.2 k) (by positivity))

end Time

section Continuation

/-- A tame solution of order at least seven restricts, around any earlier
time, to a closed-interval local solution with a common third-moment
envelope. -/
theorem exists_local_envelope (m : ℕ) (hm : 7 ≤ m) {nu : ℝ} {u₀ : FourierVelocity} {T : ℝ}
    (c : TameSolutionOn nu m u₀ T) (τ : ℝ) (hτ : τ ∈ Ico (0 : ℝ) T) :
    ∃ S, τ < S ∧ S < T ∧ ∃ B, ∃ s : LocalInfiniteVelocitySolution nu u₀ S B,
      s.coefficients = c.coefficients ∧ ∃ g : Wavevector → ℝ, (∀ k, 0 ≤ g k) ∧ Summable g ∧
        ∀ t ∈ Icc (0 : ℝ) S, ∀ k, fourierMoment 3 (s.coefficients t) k ≤ g k := by
  set S := (τ + T) / 2 with hSdef
  have hτS : τ < S := by linarith [hτ.2]
  have hST : S < T := by linarith [hτ.2]
  obtain ⟨B, hB⟩ := c.sobolev_local S hST
  obtain ⟨E, hE⟩ := c.order_local S hST
  refine ⟨S, hτS, hST, B, restrictLocal c.toSolutionOn hST hB, rfl,
    fun k ↦ Real.sqrt E * latticeDecayWeight k,
    fun k ↦ mul_nonneg (Real.sqrt_nonneg E) (latticeDecayWeight_pos k).le,
    summable_latticeDecayWeight.mul_left _, fun t ht k ↦ ?_⟩
  exact orderMoment_le_latticeEnvelope 3 _ E
    (fun F ↦ (velocityEnergy_le_of_order_le (by omega) _ F).trans (hE t ht F)) k

/-- **Global existence under a high-block bound.** For order `m ≥ 7` and any
dyadic threshold `Q`, if on every finite horizon the time integral of the
high-block sum `D_Q` of every tame solution from `u₀` is bounded by a common
constant, tame solutions exist on every interval `[0, H)`. -/
theorem exists_tameSolutionOn_of_highBlockSum (m : ℕ) (hm : 7 ≤ m) {nu : ℝ} (hnu : 0 < nu)
    (u₀ : FourierVelocity) (hr : ∀ q, u₀ (-q) = coefficientConjugate (u₀ q))
    (hd : ∀ q, modeDot q (u₀ q) = 0) (hz : u₀ 0 = 0) {E₀ : ℝ} (hE₀0 : 0 ≤ E₀)
    (hE₀ : ∀ F, velocityEnergy m F u₀ ≤ E₀) (Q : ℕ)
    (hhigh : ∀ H, 0 < H → ∃ A, ∀ T, T ≤ H → ∀ c : TameSolutionOn nu m u₀ T,
      ∀ τ ∈ Ico (0 : ℝ) T, ∫ t in (0 : ℝ)..τ, highBlockSum Q (c.coefficients t) ≤ A) :
    ∀ H, 0 < H → Nonempty (TameSolutionOn nu m u₀ H) := by
  refine exists_tameSolutionOn_of_vorticitySup m hm hnu u₀ hr hd hz hE₀0 hE₀ ?_
  intro H hH
  obtain ⟨A, hA⟩ := hhigh H hH
  set K := lowConst Q * Real.sqrt (kineticEnergy u₀) with hK
  have hK0 : 0 ≤ K := mul_nonneg (lowConst_nonneg Q) (Real.sqrt_nonneg _)
  refine ⟨H * K + A, fun T hT c τ hτ ↦ ?_⟩
  obtain ⟨S, hτS, hST, B, s, hs, g, hg, hSum, hu3⟩ := exists_local_envelope m hm c τ hτ
  have hu2 : ∀ t ∈ Icc (0 : ℝ) S, ∀ k, fourierMoment 2 (s.coefficients t) k ≤ g k :=
    fun t ht k ↦ (fourierMoment_mono _ (by omega : 2 ≤ 3) k).trans (hu3 t ht k)
  have hu1 : ∀ t ∈ Icc (0 : ℝ) S, ∀ k, fourierMoment 1 (s.coefficients t) k ≤ g k :=
    fun t ht k ↦ (fourierMoment_mono _ (by omega : 1 ≤ 3) k).trans (hu3 t ht k)
  have hsub : Icc (0 : ℝ) τ ⊆ Icc 0 S := Icc_subset_Icc le_rfl hτS.le
  have hpt : ∀ t ∈ Icc (0 : ℝ) τ,
      vorticitySup (s.coefficients t) ≤ K + highBlockSum Q (s.coefficients t) := by
    intro t ht
    have htS := hsub ht
    have hm1 : Summable (fourierMoment 1 (s.coefficients t)) :=
      hSum.of_nonneg_of_le (fourierMoment_nonneg 1 _) (hu1 t htS)
    have hnorm : Summable (fun q ↦ ‖s.coefficients t q‖) :=
      hm1.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun q ↦
        (PancakeIndexedFourierMoments.norm_coefficient_sup_le_euclidean _).trans
          (le_mul_of_one_le_left (norm_nonneg _) (by
            simp only [pow_one]
            linarith [norm_nonneg (frequencyVec q)]))
    have hkin := LocalKineticEnergy.energy_le_initial s hnu.le g hg hSum hu2 t htS
    have hE : ∀ k, coefficientEnergy (s.coefficients t k) ≤ kineticEnergy u₀ := fun k ↦
      (coefficientEnergy_le_kineticEnergy _ hnorm k).trans hkin
    refine ciSup_le fun x ↦ ?_
    calc ‖fullVorticity (s.coefficients t) x‖
        ≤ ‖lowVorticity Q (s.coefficients t) x‖ + highBlockSum Q (s.coefficients t) :=
          norm_fullVorticity_le_low_add_high Q _ hm1 x
      _ ≤ K + highBlockSum Q (s.coefficients t) := by
          gcongr
          exact norm_lowVorticity_le Q _ hE x
  have hVc := (continuousOn_vorticitySup s g hSum hu2).mono hsub
  have hDc := (continuousOn_highBlockSum s Q g hg hSum hu1).mono hsub
  have hmono := intervalIntegral.integral_mono_on hτ.1
    (hVc.intervalIntegrable_of_Icc (μ := volume) hτ.1)
    ((continuousOn_const.add hDc).intervalIntegrable_of_Icc (μ := volume) hτ.1) hpt
  simp only [Pi.add_apply] at hmono
  rw [intervalIntegral.integral_add intervalIntegrable_const
      (hDc.intervalIntegrable_of_Icc (μ := volume) hτ.1),
    intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hmono
  have hA' := hA T hT c τ hτ
  rw [← hs] at hA'
  rw [← hs]
  have hτH : τ ≤ H := hτ.2.le.trans hT
  nlinarith

end Continuation

end Mettapedia.FluidDynamics.NavierStokes.FourierDyadicBlockContinuation
