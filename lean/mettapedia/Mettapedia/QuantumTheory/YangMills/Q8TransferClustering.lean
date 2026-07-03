import Mettapedia.QuantumTheory.YangMills.TransferGapClustering
import Mettapedia.QuantumTheory.YangMills.Q8StrongCouplingGap
import Mettapedia.QuantumTheory.YangMills.ContinuumOSReconstruction

/-!
# `Q₈` non-abelian transfer: gap implies clustering, gate inputs discharged

Instantiation of the abstract `NormalizedTransferGapSystem` on the one-link
`Q₈ ⊂ SU(2)` heat-kernel model of `Q8StrongCouplingGap`:

* the kernel is renormalized by the constant factor `1/8` so the constant
  vacuum has unit OS norm;
* the one-step gap contraction on the vacuum-orthogonal complement holds
  with `q = e⁻¹`, the spin-sector eigenvalue: on the orthocomplement the
  transfer contracts by `e⁻²` on the three sign-character lines and by
  `e⁻¹` on the four-dimensional spin isotypic component, and `e⁻² ≤ e⁻¹`
  (proof via the spectral self-pairing identity, no eigenbasis expansion
  of the observable is needed);
* consequently the truncated two-point function decays at exactly the
  transfer gap rate `1 = q8StrongCouplingGap`
  (`q8_truncatedTwoPoint_decay_at_gap_rate`);
* packaging the decay as a spatial correlation kernel discharges the
  `massGap`, `reflectionPositive`, and `clustering` inputs of the Kirk
  continuum gate for this finite non-abelian model
  (`q8_continuumMassGap_of_reconstructionMachine`).

Honest scope: this is the finite single-link model for a finite non-abelian
subgroup of `SU(2)`.  The still-open input of the continuum gate is the Kirk
OS reconstruction machine (the constructive-QFT step); nothing here
constructs continuum Yang-Mills.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

/-! ## The vacuum-normalized `Q₈` kernel -/

/-- The `Q₈` heat kernel rescaled by `1/8` so that the constant observable
(the vacuum) has unit OS norm. -/
def q8NormalizedKernel (x y : Q8OneLinkConfig) : ℝ :=
  q8StrongCouplingKernel x y / 8

theorem osBilinearForm_q8NormalizedKernel_eq
    (f g : FiniteObservable Q8OneLinkConfig) :
    osBilinearForm q8NormalizedKernel f g
      = osBilinearForm q8StrongCouplingKernel f g / 8 :=
  osBilinearForm_kernel_div q8StrongCouplingKernel 8 f g

theorem q8NormalizedKernel_reflectionPositive :
    OSReflectionPositive q8NormalizedKernel := by
  intro f
  rw [osBilinearForm_q8NormalizedKernel_eq]
  have h := q8StrongCouplingKernel_reflectionPositive f
  linarith

theorem q8NormalizedKernel_symmetric :
    OSSymmetric q8NormalizedKernel := by
  intro f g
  rw [osBilinearForm_q8NormalizedKernel_eq,
    osBilinearForm_q8NormalizedKernel_eq,
    q8StrongCouplingKernel_symmetric f g]

theorem q8NormalizedKernel_transferSelfAdjoint :
    OSTransferSelfAdjoint q8NormalizedKernel q8StrongCouplingTransfer := by
  intro f g
  rw [osBilinearForm_q8NormalizedKernel_eq,
    osBilinearForm_q8NormalizedKernel_eq,
    q8StrongCouplingTransfer_selfAdjoint f g]

/-! ## Linearity and vacuum data of the `Q₈` transfer -/

theorem q8Transfer_add (f g : FiniteObservable Q8OneLinkConfig) :
    q8StrongCouplingTransfer (f + g)
      = q8StrongCouplingTransfer f + q8StrongCouplingTransfer g := by
  funext x
  unfold q8StrongCouplingTransfer
  simp only [Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

theorem q8Transfer_smul (a : ℝ) (f : FiniteObservable Q8OneLinkConfig) :
    q8StrongCouplingTransfer (a • f) = a • q8StrongCouplingTransfer f := by
  funext x
  unfold q8StrongCouplingTransfer
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- Pairing against the vacuum extracts the trivial-character coefficient. -/
theorem q8Kernel_vacuum_pairing (f : FiniteObservable Q8OneLinkConfig) :
    osBilinearForm q8StrongCouplingKernel q8ConstantObservable f
      = q8S0 f := by
  unfold osBilinearForm q8ConstantObservable q8S0 q8StrongCouplingKernel
  simp only [Fin.sum_univ_eight]
  simp +decide [q8SignI, q8SignJ, q8SignK, q8SpinR, q8SpinI, q8SpinJ, q8SpinK]
  ring

theorem q8NormalizedKernel_vacuum_norm :
    osBilinearForm q8NormalizedKernel
      q8ConstantObservable q8ConstantObservable = 1 := by
  rw [osBilinearForm_q8NormalizedKernel_eq, q8Kernel_vacuum_pairing]
  unfold q8S0 q8ConstantObservable
  norm_num

/-! ## The gap contraction on the vacuum-orthogonal complement -/

/-- One-step gap contraction with `q = e⁻¹` on the vacuum-orthogonal
complement: the sign sector contracts by `e⁻² ≤ e⁻¹`, the spin sector by
exactly `e⁻¹`. -/
theorem q8_gapContraction
    (f : FiniteObservable Q8OneLinkConfig)
    (horth : osBilinearForm q8NormalizedKernel q8ConstantObservable f = 0) :
    osBilinearForm q8NormalizedKernel
        (q8StrongCouplingTransfer f) (q8StrongCouplingTransfer f)
      ≤ q8SpinRatio ^ 2 *
        osBilinearForm q8NormalizedKernel f f := by
  have hS0 : q8S0 f = 0 := by
    rw [osBilinearForm_q8NormalizedKernel_eq, q8Kernel_vacuum_pairing]
      at horth
    linarith
  rw [osBilinearForm_q8NormalizedKernel_eq,
    osBilinearForm_q8NormalizedKernel_eq,
    q8StrongCouplingKernel_self_pairing,
    q8StrongCouplingKernel_self_pairing,
    q8S0_transfer, q8Si_transfer, q8Sj_transfer, q8Sk_transfer,
    q8DR_transfer, q8DI_transfer, q8DJ_transfer, q8DK_transfer, hS0]
  have hs := q8SignRatio_pos
  have hr := q8SpinRatio_pos
  have hsr := q8SignRatio_le_spinRatio
  have hsq : q8SignRatio ^ 2 ≤ q8SpinRatio ^ 2 := by nlinarith
  have hS : 0 ≤ q8Si f ^ 2 + q8Sj f ^ 2 + q8Sk f ^ 2 := by positivity
  have hD : 0 ≤ q8DR f ^ 2 + q8DI f ^ 2 + q8DJ f ^ 2 + q8DK f ^ 2 := by
    positivity
  have hkey : 0 ≤ (q8SpinRatio ^ 2 - q8SignRatio ^ 2) * q8SignRatio *
      (q8Si f ^ 2 + q8Sj f ^ 2 + q8Sk f ^ 2) :=
    mul_nonneg (mul_nonneg (sub_nonneg.2 hsq) hs.le) hS
  nlinarith [hkey, hD, hr]

/-! ## The packaged transfer-gap system -/

/-- The `Q₈` single-link model packaged as a normalized transfer-gap system
with one-step contraction `q = e⁻¹` carried by the spin sector. -/
def q8TransferGapSystem : NormalizedTransferGapSystem Q8OneLinkConfig where
  K := q8NormalizedKernel
  T := q8StrongCouplingTransfer
  vac := q8ConstantObservable
  q := q8SpinRatio
  reflectionPositive := q8NormalizedKernel_reflectionPositive
  symmetric := q8NormalizedKernel_symmetric
  selfAdjoint := q8NormalizedKernel_transferSelfAdjoint
  Tadd := q8Transfer_add
  Tsmul := q8Transfer_smul
  vacInvariant := q8StrongCouplingTransfer_constant_eigen
  vacNormalized := q8NormalizedKernel_vacuum_norm
  qNonneg := q8SpinRatio_pos.le
  gapContraction := q8_gapContraction

/-- The abstract transfer mass gap of the packaged system is exactly the
spectral gap `1` proven for the `Q₈` model. -/
theorem q8TransferGapSystem_massGap_eq :
    transferMassGap q8TransferGapSystem = q8StrongCouplingGap := by
  show -Real.log q8SpinRatio = q8StrongCouplingGap
  simp [q8StrongCouplingGap, q8StrongCouplingLambdaTwo,
    q8StrongCouplingLambdaOne]

/-- **Clustering at the proven gap rate.**  The truncated two-point function
of the non-abelian `Q₈` single-link model decays exponentially at exactly the
rate `q8StrongCouplingGap = 1`. -/
theorem q8_truncatedTwoPoint_decay_at_gap_rate
    (f g : FiniteObservable Q8OneLinkConfig) (n : ℕ) :
    |truncatedTwoPoint q8TransferGapSystem f g n|
      ≤ clusteringPrefactor q8TransferGapSystem f g
        * Real.exp (-q8StrongCouplingGap * n) := by
  have h := abs_truncatedTwoPoint_le_exp q8TransferGapSystem
    q8SpinRatio_pos f g n
  rwa [q8TransferGapSystem_massGap_eq] at h

/-! ## Spatial packaging and the Kirk-gate inputs -/

/-- Spatial correlation kernel induced by the `Q₈` truncated two-point
function, with the time separation given by the ceiling of the spatial
distance. -/
def q8SpatialCorrelation (f g : FiniteObservable Q8OneLinkConfig) :
    SpatialCorrelation :=
  fun x y => truncatedTwoPoint q8TransferGapSystem f g ⌈dist x y⌉₊

/-- Uniform exponential bound for the induced spatial kernel at the gap
rate `1`. -/
theorem q8SpatialCorrelation_uniform_bound
    (f g : FiniteObservable Q8OneLinkConfig) (x y : Space) :
    |q8SpatialCorrelation f g x y|
      ≤ clusteringPrefactor q8TransferGapSystem f g
        * Real.exp (-1 * dist x y) := by
  have h := abs_truncatedTwoPoint_le q8TransferGapSystem f g ⌈dist x y⌉₊
  refine h.trans (mul_le_mul_of_nonneg_left ?_
    (clusteringPrefactor_nonneg q8TransferGapSystem f g))
  have hq : q8TransferGapSystem.q ^ ⌈dist x y⌉₊
      = Real.exp (-(⌈dist x y⌉₊ : ℝ)) := by
    show q8SpinRatio ^ ⌈dist x y⌉₊ = _
    rw [q8SpinRatio, ← Real.exp_nat_mul]
    norm_num
  rw [hq]
  refine Real.exp_le_exp.mpr ?_
  have hceil : dist x y ≤ (⌈dist x y⌉₊ : ℝ) := Nat.le_ceil _
  linarith

/-- The induced spatial kernel clusters exponentially at every rate strictly
below the proven gap `1`. -/
theorem q8SpatialCorrelation_clustering
    (f g : FiniteObservable Q8OneLinkConfig) {C : ℝ} (hC : C < 1) :
    HasExponentialClusteringAtRate (q8SpatialCorrelation f g) C :=
  hasExponentialClusteringAtRate_of_uniform_exp_bound hC
    (q8SpatialCorrelation_uniform_bound f g)

/-- The `massGap` input of the Kirk continuum gate, discharged by the proven
`Q₈` gap. -/
def q8LatticeMassGapInput : LatticeMassGapInput where
  gap := q8StrongCouplingGap
  positive := q8StrongCouplingGap_positive

/-- The `clustering` input of the Kirk continuum gate, discharged at rate
`1/2 < 1` by the transfer-gap clustering theorem. -/
def q8LatticeClusteringInput (f g : FiniteObservable Q8OneLinkConfig) :
    LatticeExponentialClusteringInput (q8SpatialCorrelation f g) where
  rate := 1 / 2
  ratePositive := by norm_num
  clusteringAtRate := q8SpatialCorrelation_clustering f g (by norm_num)

/-- The OS reflection-positivity input, discharged by the proven reflection
positivity of the normalized and unnormalized `Q₈` kernels. -/
def q8OSReflectionPositivityInput : OSReflectionPositivityInput where
  reflectionPositiveFunctional := OSReflectionPositive q8NormalizedKernel
  reflectionPositiveCone := OSReflectionPositive q8StrongCouplingKernel
  reflectionPositive :=
    ⟨q8NormalizedKernel_reflectionPositive,
      q8StrongCouplingKernel_reflectionPositive⟩

/-- **Kirk-gate discharge for the finite non-abelian `Q₈` model.**  Every
input of the continuum gate except the OS reconstruction machine itself —
the lattice mass gap, reflection positivity, and exponential clustering — is
discharged by proven statements about the `Q₈` single-link model.  The
machine (the constructive-QFT step) remains the open input; nothing here
constructs continuum Yang-Mills. -/
theorem q8_continuumMassGap_of_reconstructionMachine
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ : ℝ}
    (f g : FiniteObservable Q8OneLinkConfig)
    (machine : KirkOSReconstructionMachine A Δ (q8SpatialCorrelation f g)) :
    HasSpectralMassGap A Δ :=
  continuumMassGap_of_latticeMassGap_reflectionPositive_clustering
    machine q8LatticeMassGapInput q8OSReflectionPositivityInput
    (q8LatticeClusteringInput f g)

end YangMills
end QuantumTheory
end Mettapedia
