import Mettapedia.QuantumTheory.YangMills.TransferGapClustering
import Mettapedia.QuantumTheory.YangMills.Z2StrongCouplingGap
import Mettapedia.QuantumTheory.YangMills.ContinuumOSReconstruction

/-!
# Z₂ single-link transfer: gap implies clustering, gate inputs discharged

Instantiation of the abstract `NormalizedTransferGapSystem` on the one-link
`Z₂` heat-kernel model whose spectral gap `-log (e⁻¹) = 1` is proven in
`Z2StrongCouplingGap`:

* the kernel is renormalized by the constant factor `1/2` so that the constant
  vacuum has unit OS norm (an overall positive kernel scaling changes no
  spectral or clustering statement);
* the one-step gap contraction on the vacuum-orthogonal complement holds with
  `q = e⁻¹` (in fact with equality: the complement is the sign eigenvector
  line);
* consequently the truncated two-point function decays at exactly the transfer
  gap rate `1 = z2StrongCouplingGap`
  (`z2_truncatedTwoPoint_decay_at_gap_rate`);
* packaging the decay as a spatial correlation kernel discharges both the
  `massGap` and `clustering` inputs of the Kirk continuum gate
  `continuumMassGap_of_latticeMassGap_reflectionPositive_clustering` for this
  finite model (`z2_continuumMassGap_of_reconstructionMachine`).

Honest scope: this is the finite single-link model.  The still-open input of
the continuum gate is the Kirk OS reconstruction machine (the constructive-QFT
step); nothing here constructs continuum Yang-Mills.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

/-! ## The vacuum-normalized Z₂ kernel -/

/-- The `Z₂` heat kernel rescaled by `1/2` so that the constant observable
(the vacuum) has unit OS norm. -/
def z2NormalizedKernel (x y : Z2OneLinkConfig) : ℝ :=
  z2StrongCouplingKernel x y / 2

theorem osBilinearForm_z2NormalizedKernel_eq
    (f g : FiniteObservable Z2OneLinkConfig) :
    osBilinearForm z2NormalizedKernel f g
      = osBilinearForm z2StrongCouplingKernel f g / 2 := by
  unfold osBilinearForm z2NormalizedKernel
  simp only [Fin.sum_univ_two]
  ring

theorem z2NormalizedKernel_reflectionPositive :
    OSReflectionPositive z2NormalizedKernel := by
  intro f
  rw [osBilinearForm_z2NormalizedKernel_eq]
  have h := z2StrongCouplingKernel_reflectionPositive f
  linarith

theorem z2NormalizedKernel_symmetric :
    OSSymmetric z2NormalizedKernel := by
  intro f g
  rw [osBilinearForm_z2NormalizedKernel_eq,
    osBilinearForm_z2NormalizedKernel_eq,
    z2StrongCouplingKernel_symmetric f g]

theorem z2NormalizedKernel_transferSelfAdjoint :
    OSTransferSelfAdjoint z2NormalizedKernel z2StrongCouplingTransfer := by
  intro f g
  rw [osBilinearForm_z2NormalizedKernel_eq,
    osBilinearForm_z2NormalizedKernel_eq,
    z2StrongCouplingTransfer_selfAdjoint f g]

theorem z2NormalizedKernel_vacuum_norm :
    osBilinearForm z2NormalizedKernel
      z2ConstantObservable z2ConstantObservable = 1 := by
  rw [osBilinearForm_z2NormalizedKernel_eq]
  unfold osBilinearForm z2StrongCouplingKernel z2ConstantObservable
    z2Character
  simp only [Fin.sum_univ_two]
  norm_num
  ring

/-! ## Linearity and vacuum invariance of the Z₂ transfer -/

theorem z2Transfer_add (f g : FiniteObservable Z2OneLinkConfig) :
    z2StrongCouplingTransfer (f + g)
      = z2StrongCouplingTransfer f + z2StrongCouplingTransfer g := by
  funext x
  unfold z2StrongCouplingTransfer
  simp only [Pi.add_apply, Fin.sum_univ_two]
  ring

theorem z2Transfer_smul (a : ℝ) (f : FiniteObservable Z2OneLinkConfig) :
    z2StrongCouplingTransfer (a • f) = a • z2StrongCouplingTransfer f := by
  funext x
  unfold z2StrongCouplingTransfer
  simp only [Pi.smul_apply, smul_eq_mul, Fin.sum_univ_two]
  ring

theorem z2Transfer_constant_fixed :
    z2StrongCouplingTransfer z2ConstantObservable = z2ConstantObservable := by
  rw [z2StrongCouplingTransfer_constant_eigen]
  funext x
  simp [z2StrongCouplingLambdaOne]

/-! ## The gap contraction on the vacuum-orthogonal complement -/

/-- Orthogonality to the vacuum forces the observable onto the sign
eigenvector line `f 1 = -(f 0)`. -/
theorem z2_vacuum_orthogonal_iff
    (f : FiniteObservable Z2OneLinkConfig)
    (horth : osBilinearForm z2NormalizedKernel z2ConstantObservable f = 0) :
    f 1 = -(f 0) := by
  unfold osBilinearForm z2NormalizedKernel z2StrongCouplingKernel
    z2ConstantObservable z2Character at horth
  simp only [Fin.sum_univ_two] at horth
  norm_num at horth
  ring_nf at horth
  linarith

/-- One-step gap contraction with `q = e⁻¹` (in fact equality) on the
vacuum-orthogonal complement of the `Z₂` model. -/
theorem z2_gapContraction
    (f : FiniteObservable Z2OneLinkConfig)
    (horth : osBilinearForm z2NormalizedKernel z2ConstantObservable f = 0) :
    osBilinearForm z2NormalizedKernel
        (z2StrongCouplingTransfer f) (z2StrongCouplingTransfer f)
      ≤ z2StrongCouplingRatio ^ 2 *
        osBilinearForm z2NormalizedKernel f f := by
  have hf1 : f 1 = -(f 0) := z2_vacuum_orthogonal_iff f horth
  rw [osBilinearForm_z2NormalizedKernel_eq,
    osBilinearForm_z2NormalizedKernel_eq,
    z2StrongCouplingKernel_self_pairing,
    z2StrongCouplingKernel_self_pairing]
  unfold z2StrongCouplingTransfer z2StrongCouplingKernel z2Character
  simp only [Fin.sum_univ_two]
  norm_num
  rw [hf1]
  ring_nf
  exact le_rfl

/-! ## The packaged transfer-gap system -/

/-- The `Z₂` single-link model packaged as a normalized transfer-gap system
with one-step contraction `q = e⁻¹`. -/
def z2TransferGapSystem : NormalizedTransferGapSystem Z2OneLinkConfig where
  K := z2NormalizedKernel
  T := z2StrongCouplingTransfer
  vac := z2ConstantObservable
  q := z2StrongCouplingRatio
  reflectionPositive := z2NormalizedKernel_reflectionPositive
  symmetric := z2NormalizedKernel_symmetric
  selfAdjoint := z2NormalizedKernel_transferSelfAdjoint
  Tadd := z2Transfer_add
  Tsmul := z2Transfer_smul
  vacInvariant := z2Transfer_constant_fixed
  vacNormalized := z2NormalizedKernel_vacuum_norm
  qNonneg := z2StrongCouplingRatio_pos.le
  gapContraction := z2_gapContraction

/-- The abstract transfer mass gap of the packaged system is exactly the
spectral gap `1` proven for the `Z₂` model. -/
theorem z2TransferGapSystem_massGap_eq :
    transferMassGap z2TransferGapSystem = z2StrongCouplingGap := by
  show -Real.log z2StrongCouplingRatio = z2StrongCouplingGap
  simp [z2StrongCouplingGap, z2StrongCouplingLambdaTwo,
    z2StrongCouplingLambdaOne]

/-- **Clustering at the proven gap rate.**  The truncated two-point function
of the `Z₂` single-link model decays exponentially at exactly the rate
`z2StrongCouplingGap = 1`. -/
theorem z2_truncatedTwoPoint_decay_at_gap_rate
    (f g : FiniteObservable Z2OneLinkConfig) (n : ℕ) :
    |truncatedTwoPoint z2TransferGapSystem f g n|
      ≤ clusteringPrefactor z2TransferGapSystem f g
        * Real.exp (-z2StrongCouplingGap * n) := by
  have h := abs_truncatedTwoPoint_le_exp z2TransferGapSystem
    z2StrongCouplingRatio_pos f g n
  rwa [z2TransferGapSystem_massGap_eq] at h

/-! ## Spatial packaging and the Kirk-gate inputs -/

/-- Spatial correlation kernel induced by the `Z₂` truncated two-point
function, with the time separation given by the ceiling of the spatial
distance. -/
def z2SpatialCorrelation (f g : FiniteObservable Z2OneLinkConfig) :
    SpatialCorrelation :=
  fun x y => truncatedTwoPoint z2TransferGapSystem f g ⌈dist x y⌉₊

/-- Uniform exponential bound for the induced spatial kernel at the gap
rate `1`. -/
theorem z2SpatialCorrelation_uniform_bound
    (f g : FiniteObservable Z2OneLinkConfig) (x y : Space) :
    |z2SpatialCorrelation f g x y|
      ≤ clusteringPrefactor z2TransferGapSystem f g
        * Real.exp (-1 * dist x y) := by
  have h := abs_truncatedTwoPoint_le z2TransferGapSystem f g ⌈dist x y⌉₊
  refine h.trans (mul_le_mul_of_nonneg_left ?_
    (clusteringPrefactor_nonneg z2TransferGapSystem f g))
  have hq : z2TransferGapSystem.q ^ ⌈dist x y⌉₊
      = Real.exp (-(⌈dist x y⌉₊ : ℝ)) := by
    show z2StrongCouplingRatio ^ ⌈dist x y⌉₊ = _
    rw [z2StrongCouplingRatio, ← Real.exp_nat_mul]
    norm_num
  rw [hq]
  refine Real.exp_le_exp.mpr ?_
  have hceil : dist x y ≤ (⌈dist x y⌉₊ : ℝ) := Nat.le_ceil _
  linarith

/-- The induced spatial kernel clusters exponentially at every rate strictly
below the proven gap `1`. -/
theorem z2SpatialCorrelation_clustering
    (f g : FiniteObservable Z2OneLinkConfig) {C : ℝ} (hC : C < 1) :
    HasExponentialClusteringAtRate (z2SpatialCorrelation f g) C :=
  hasExponentialClusteringAtRate_of_uniform_exp_bound hC
    (z2SpatialCorrelation_uniform_bound f g)

/-- The `massGap` input of the Kirk continuum gate, discharged by the proven
`Z₂` gap. -/
def z2LatticeMassGapInput : LatticeMassGapInput where
  gap := z2StrongCouplingGap
  positive := z2StrongCouplingGap_positive

/-- The `clustering` input of the Kirk continuum gate, discharged at rate
`1/2 < 1` by the transfer-gap clustering theorem. -/
def z2LatticeClusteringInput (f g : FiniteObservable Z2OneLinkConfig) :
    LatticeExponentialClusteringInput (z2SpatialCorrelation f g) where
  rate := 1 / 2
  ratePositive := by norm_num
  clusteringAtRate := z2SpatialCorrelation_clustering f g (by norm_num)

/-- The OS reflection-positivity input, discharged by the proven reflection
positivity of the normalized and unnormalized `Z₂` kernels. -/
def z2OSReflectionPositivityInput : OSReflectionPositivityInput where
  reflectionPositiveFunctional := OSReflectionPositive z2NormalizedKernel
  reflectionPositiveCone := OSReflectionPositive z2StrongCouplingKernel
  reflectionPositive :=
    ⟨z2NormalizedKernel_reflectionPositive,
      z2StrongCouplingKernel_reflectionPositive⟩

/-- **Kirk-gate discharge for the finite `Z₂` model.**  Every input of the
continuum gate except the OS reconstruction machine itself — the lattice mass
gap, reflection positivity, and exponential clustering — is discharged by
proven statements about the `Z₂` single-link model.  The machine (the
constructive-QFT step) remains the open input; nothing here constructs
continuum Yang-Mills. -/
theorem z2_continuumMassGap_of_reconstructionMachine
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ : ℝ}
    (f g : FiniteObservable Z2OneLinkConfig)
    (machine : KirkOSReconstructionMachine A Δ (z2SpatialCorrelation f g)) :
    HasSpectralMassGap A Δ :=
  continuumMassGap_of_latticeMassGap_reflectionPositive_clustering
    machine z2LatticeMassGapInput z2OSReflectionPositivityInput
    (z2LatticeClusteringInput f g)

end YangMills
end QuantumTheory
end Mettapedia
