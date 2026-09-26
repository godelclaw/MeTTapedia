import Mettapedia.QuantumTheory.YangMills.StrongCouplingTransferGap
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.MeasureTheory.Group.LIntegral

/-!
# Compact Wilson transfer operators

`WilsonCompact.uniform_transfer_gap` extends the lattice transfer gap to
second-countable compact topological groups with their Borel measurable space.
The reference law is a probability measure invariant under inversion, and the
potential is a continuous real class function, invariant under inversion and
valued in `[0, 2]`. The left-invariant probability specialization covers normalized
Haar measure.

At the threshold `StrongCouplingTransferGap.Rectangular.beta0 d`, there is a
positive decay rate chosen before the spatial side `L + 3`. The real `L²`
transfer operator has a strictly positive, normalized continuous ground state,
a simple positive leading eigenvalue, and an absolute bound by `exp (-κ)` times
that eigenvalue for every other point of its real spectrum. Here `d` counts
spatial directions; time is the additional direction.

Compactness factors through continuous functions and Arzelà–Ascoli. Strict
kernel positivity gives a ground state and uniform convergence of normalized
kernel powers at each fixed volume. Exact finite-product integration identifies
the periodic Wilson expectations with cyclic kernel integrals. Passing to the
long-cylinder limit in the clustering theorem then bounds each eigenvalue;
the compact Fredholm alternative covers the remaining spectrum.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped InnerProductSpace

namespace Mettapedia.QuantumTheory.YangMills.CompactTransferGap

namespace CompactSpectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A nonzero compact symmetric operator has an eigenvalue of maximal absolute value. -/
theorem exists_norm_eigenvector (T : H →L[ℝ] H) (hc : IsCompactOperator T)
    (hs : T.IsSymmetric) (hT : T ≠ 0) :
    ∃ (r : ℝ) (v : H), v ≠ 0 ∧ T v = r • v ∧ |r| = ‖T‖ := by
  have : Nontrivial H := not_subsingleton_iff_nontrivial.mp (by
    intro h
    exact hT (Subsingleton.elim _ _))
  have hn : ‖T‖ ≠ 0 := norm_ne_zero_iff.mpr hT
  have hor : ‖T‖ ∈ spectrum ℝ T ∨ -‖T‖ ∈ spectrum ℝ T := by
    simp only [spectrum, Set.mem_compl_iff]
    by_contra! h
    obtain ⟨ε, hε, hb⟩ := T.abs_rayleighQuotient_le_of_norm_mem_resolventSet
      (by simpa using h.1) (by simpa using h.2)
    have he := T.norm_eq_iSup_rayleighQuotient hs
    have hl : (⨆ x, |T.rayleighQuotient x|) ≤ ‖T‖ - ε := ciSup_le hb
    linarith
  rcases hor with hp | hp
  · obtain ⟨v, hv, hv0⟩ := ((hc.hasEigenvalue_iff_mem_spectrum hn).mpr hp).exists_hasEigenvector
    exact ⟨‖T‖, v, hv0, Module.End.mem_eigenspace_iff.mp hv, abs_of_nonneg (norm_nonneg _)⟩
  · obtain ⟨v, hv, hv0⟩ :=
      ((hc.hasEigenvalue_iff_mem_spectrum (neg_ne_zero.mpr hn)).mpr hp).exists_hasEigenvector
    exact ⟨-‖T‖, v, hv0, Module.End.mem_eigenspace_iff.mp hv, by simp⟩

omit [CompleteSpace H] in
/-- Equality in the operator-norm quadratic bound produces a top eigenvector. -/
theorem eigenvector_of_inner_eq (T : H →L[ℝ] H) (v : H)
    (h : ⟪v, T v⟫_ℝ = ‖T‖ * ‖v‖ ^ 2) : T v = ‖T‖ • v := by
  have hb := T.le_opNorm v
  have he := norm_sub_sq_real (T v) (‖T‖ • v)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg T),
    inner_smul_right, real_inner_comm v (T v), h] at he
  have hz : ‖T v - ‖T‖ • v‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖T v - ‖T‖ • v‖, norm_nonneg (T v), norm_nonneg v, norm_nonneg T]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

end CompactSpectral

namespace ContinuousFeature

variable {X H : Type*} [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Pairing with a continuous Hilbert-space-valued feature map. -/
def pairing (s : C(X, H)) : H →L[ℝ] (X →ᵇ ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun f => BoundedContinuousFunction.mkOfCompact
        ⟨fun x => ⟪s x, f⟫_ℝ, s.continuous.inner continuous_const⟩
      map_add' := fun f g => by ext x; simp [inner_add_right]
      map_smul' := fun a f => by ext x; simp [inner_smul_right] }
    ‖s‖ (fun f => (BoundedContinuousFunction.norm_le (by positivity)).mpr fun x =>
      (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (s.norm_coe_le_norm x) (norm_nonneg f)))

@[simp] theorem pairing_apply (s : C(X, H)) (f : H) (x : X) :
    pairing s f x = ⟪s x, f⟫_ℝ := rfl

/-- Compactness needs continuity of the feature map, but no spectral machinery. -/
theorem compact_pairing (s : C(X, H)) : IsCompactOperator (pairing s) := by
  apply (isCompactOperator_iff_isCompact_closure_image_closedBall (pairing s).toLinearMap
    (by norm_num : (0 : ℝ) < 1)).mpr
  apply BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0 : ℝ) ‖s‖)
    (isCompact_closedBall _ _)
  · intro f x hf
    obtain ⟨v, hv, rfl⟩ := hf
    have hv' : ‖v‖ ≤ 1 := by simpa using hv
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact (norm_inner_le_norm _ _).trans
      ((mul_le_mul_of_nonneg_left hv' (norm_nonneg _)).trans (by simpa using s.norm_coe_le_norm x))
  · intro x
    refine Metric.equicontinuousAt_of_continuity_modulus (fun y => ‖s x - s y‖)
      (by
        have hc : Continuous (fun y => ‖s x - s y‖) := (continuous_const.sub s.continuous).norm
        simpa using hc.tendsto x) _ ?_
    filter_upwards [] with y
    intro f
    obtain ⟨v, hv, he⟩ := f.property
    have hv' : ‖v‖ ≤ 1 := by simpa using hv
    change dist (f.val x) (f.val y) ≤ ‖s x - s y‖
    rw [← he]
    change dist (⟪s x, v⟫_ℝ) (⟪s y, v⟫_ℝ) ≤ ‖s x - s y‖
    rw [dist_eq_norm, ← inner_sub_left]
    exact (norm_inner_le_norm _ _).trans (by
      simpa using mul_le_mul_of_nonneg_left hv' (norm_nonneg (s x - s y)))

end ContinuousFeature

namespace IntegralKernel

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X] (μ : Measure X) [IsProbabilityMeasure μ]

abbrev Hilbert := Lp ℝ 2 μ

/-- A kernel section as an `L²` vector. -/
def sectionMap (K : C(X × X, ℝ)) : C(X, Hilbert μ) :=
  ⟨fun x => ContinuousMap.toLp 2 μ ℝ (K.curry x),
    (ContinuousMap.toLp 2 μ ℝ).continuous.comp K.curry.continuous⟩

/-- The continuous representative of the integral transform. -/
def toContinuous (K : C(X × X, ℝ)) : Hilbert μ →L[ℝ] (X →ᵇ ℝ) :=
  ContinuousFeature.pairing (sectionMap μ K)

/-- The integral operator on `L²(μ)`. -/
def operator (K : C(X × X, ℝ)) : Hilbert μ →L[ℝ] Hilbert μ :=
  (BoundedContinuousFunction.toLp 2 μ ℝ).comp (toContinuous μ K)

omit [SecondCountableTopology X] in
theorem toContinuous_apply (K : C(X × X, ℝ)) (f : Hilbert μ) (x : X) :
    toContinuous μ K f x = ∫ y, K (x, y) * f y ∂μ := by
  change ⟪ContinuousMap.toLp 2 μ ℝ (K.curry x), f⟫_ℝ = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ (K.curry x)] with y hy
  change f y * (ContinuousMap.toLp 2 μ ℝ (K.curry x)) y = _
  rw [hy]
  exact mul_comm _ _

omit [SecondCountableTopology X] in
theorem operator_apply_ae (K : C(X × X, ℝ)) (f : Hilbert μ) :
    operator μ K f =ᵐ[μ] fun x => ∫ y, K (x, y) * f y ∂μ := by
  exact (BoundedContinuousFunction.coeFn_toLp 2 μ ℝ (toContinuous μ K f)).trans
    (ae_of_all μ (toContinuous_apply μ K f))

omit [SecondCountableTopology X] in
theorem compact_operator (K : C(X × X, ℝ)) : IsCompactOperator (operator μ K) :=
  (ContinuousFeature.compact_pairing (sectionMap μ K)).clm_comp
    (BoundedContinuousFunction.toLp 2 μ ℝ)

omit [TopologicalSpace X] [CompactSpace X] [BorelSpace X] [SecondCountableTopology X] in
theorem integrable_vector (f : Hilbert μ) : Integrable f μ :=
  memLp_one_iff_integrable.mp ((Lp.memLp f).mono_exponent (by norm_num))

theorem integrable_matrix_element (K : C(X × X, ℝ)) (f g : Hilbert μ) :
    Integrable (fun p : X × X => K p * (f p.1 * g p.2)) (μ.prod μ) :=
  ((integrable_vector μ f).mul_prod (integrable_vector μ g)).bdd_mul
    K.continuous.aestronglyMeasurable (ae_of_all _ K.norm_coe_le_norm)

omit [SecondCountableTopology X] in
theorem inner_operator (K : C(X × X, ℝ)) (f g : Hilbert μ) :
    ⟪f, operator μ K g⟫_ℝ = ∫ x, ∫ y, K (x, y) * (f x * g y) ∂μ ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [operator_apply_ae μ K g] with x hx
  rw [hx]
  change (∫ y, K (x, y) * g y ∂μ) * f x = _
  rw [← integral_mul_const]
  congr 1
  funext y
  ring

theorem symmetric_operator (K : C(X × X, ℝ)) (hs : ∀ x y, K (x, y) = K (y, x)) :
    (operator μ K).IsSymmetric := by
  intro f g
  change ⟪operator μ K f, g⟫_ℝ = ⟪f, operator μ K g⟫_ℝ
  rw [real_inner_comm g (operator μ K f), inner_operator, inner_operator]
  rw [integral_integral_swap (integrable_matrix_element μ K g f)]
  congr 1
  funext x
  congr 1
  funext y
  rw [hs y x]
  ring

theorem inner_operator_prod (K : C(X × X, ℝ)) (f g : Hilbert μ) :
    ⟪f, operator μ K g⟫_ℝ = ∫ p : X × X, K p * (f p.1 * g p.2) ∂μ.prod μ :=
  (inner_operator μ K f g).trans (integral_prod _ (integrable_matrix_element μ K f g)).symm

/-- Absolute value, as an `L²` vector. -/
def modulus (f : Hilbert μ) : Hilbert μ := (Lp.memLp f).norm.toLp (fun x => ‖f x‖)

omit [TopologicalSpace X] [CompactSpace X] [BorelSpace X] [SecondCountableTopology X]
  [IsProbabilityMeasure μ] in
theorem modulus_ae (f : Hilbert μ) : modulus μ f =ᵐ[μ] fun x => |f x| := by
  simpa only [modulus, Real.norm_eq_abs] using (Lp.memLp f).norm.coeFn_toLp

omit [TopologicalSpace X] [CompactSpace X] [BorelSpace X] [SecondCountableTopology X]
  [IsProbabilityMeasure μ] in
theorem norm_modulus (f : Hilbert μ) : ‖modulus μ f‖ = ‖f‖ := by
  rw [modulus, Lp.norm_toLp, eLpNorm_norm, Lp.norm_def]

theorem abs_inner_le_modulus (K : C(X × X, ℝ)) (hK : ∀ x y, 0 ≤ K (x, y))
    (f : Hilbert μ) : |⟪f, operator μ K f⟫_ℝ| ≤
      ⟪modulus μ f, operator μ K (modulus μ f)⟫_ℝ := by
  rw [inner_operator_prod, inner_operator_prod, ← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (modulus_ae μ f),
    Measure.quasiMeasurePreserving_snd.ae (modulus_ae μ f)] with p hx hy
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hK p.1 p.2), norm_mul,
    Real.norm_eq_abs, Real.norm_eq_abs, hx, hy]

/-- A nonnegative symmetric kernel has a nonnegative top eigenvector. -/
theorem exists_nonneg_top (K : C(X × X, ℝ)) (hs : ∀ x y, K (x, y) = K (y, x))
    (hK : ∀ x y, 0 ≤ K (x, y)) (hne : operator μ K ≠ 0) :
    ∃ u : Hilbert μ, u ≠ 0 ∧ (∀ᵐ x ∂μ, 0 ≤ u x) ∧
      operator μ K u = ‖operator μ K‖ • u := by
  obtain ⟨r, v, hv, he, hr⟩ := CompactSpectral.exists_norm_eigenvector
    (operator μ K) (compact_operator μ K) (symmetric_operator μ K hs) hne
  have hu : modulus μ v ≠ 0 := by
    intro hz
    have hz' := norm_modulus μ v
    rw [hz, norm_zero] at hz'
    exact hv (norm_eq_zero.mp hz'.symm)
  refine ⟨modulus μ v, hu, (modulus_ae μ v).mono (fun x hx => by rw [hx]; positivity), ?_⟩
  apply CompactSpectral.eigenvector_of_inner_eq
  apply le_antisymm
  · calc
      _ ≤ ‖modulus μ v‖ * ‖operator μ K (modulus μ v)‖ := real_inner_le_norm _ _
      _ ≤ ‖modulus μ v‖ * (‖operator μ K‖ * ‖modulus μ v‖) :=
        mul_le_mul_of_nonneg_left ((operator μ K).le_opNorm _) (norm_nonneg _)
      _ = _ := by ring
  · have hb := abs_inner_le_modulus μ K hK v
    rw [he, inner_smul_right, real_inner_self_eq_norm_sq, abs_mul, abs_pow, abs_norm, hr] at hb
    simpa only [norm_modulus] using hb

omit [TopologicalSpace X] [CompactSpace X] [BorelSpace X] [SecondCountableTopology X] in
theorem integral_pos_of_nonneg_vector (f : Hilbert μ) (hf : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hne : f ≠ 0) : 0 < ∫ x, f x ∂μ := by
  refine lt_of_le_of_ne (integral_nonneg_of_ae hf) ?_
  intro hz
  have he := (integral_eq_zero_iff_of_nonneg_ae hf (integrable_vector μ f)).mp hz.symm
  apply hne
  exact Lp.ext (he.trans (Lp.coeFn_zero _ _ _).symm)

/-- Every eigenvector with nonzero eigenvalue has a continuous representative. -/
def eigenRepresentative (K : C(X × X, ℝ)) (r : ℝ) (f : Hilbert μ) : C(X, ℝ) :=
  r⁻¹ • (toContinuous μ K f).toContinuousMap

omit [SecondCountableTopology X] in
theorem eigenRepresentative_ae (K : C(X × X, ℝ)) {r : ℝ} (hr : r ≠ 0)
    (f : Hilbert μ) (he : operator μ K f = r • f) :
    eigenRepresentative μ K r f =ᵐ[μ] f := by
  have hp := BoundedContinuousFunction.coeFn_toLp 2 μ ℝ (toContinuous μ K f)
  change operator μ K f =ᵐ[μ] toContinuous μ K f at hp
  rw [he] at hp
  filter_upwards [hp, Lp.coeFn_smul r f] with x hx hx'
  change r⁻¹ * toContinuous μ K f x = f x
  rw [← hx, hx']
  simp [hr]

omit [SecondCountableTopology X] in
theorem eigenRepresentative_equation (K : C(X × X, ℝ)) {r : ℝ} (hr : r ≠ 0)
    (f : Hilbert μ) (he : operator μ K f = r • f) (x : X) :
    (∫ y, K (x, y) * eigenRepresentative μ K r f y ∂μ) =
      r * eigenRepresentative μ K r f x := by
  have hh := (eigenRepresentative_ae μ K hr f he).mono
    (fun y hy => congrArg (fun a => K (x, y) * a) hy)
  rw [integral_congr_ae hh, ← toContinuous_apply]
  change toContinuous μ K f x = r * (r⁻¹ * toContinuous μ K f x)
  simp [hr]

omit [SecondCountableTopology X] in
theorem toLp_eigenRepresentative (K : C(X × X, ℝ)) {r : ℝ} (hr : r ≠ 0)
    (f : Hilbert μ) (he : operator μ K f = r • f) :
    ContinuousMap.toLp 2 μ ℝ (eigenRepresentative μ K r f) = f :=
  Lp.ext ((ContinuousMap.coeFn_toLp μ _).trans (eigenRepresentative_ae μ K hr f he))

theorem operator_ne_zero (K : C(X × X, ℝ)) {a : ℝ} (ha : 0 < a)
    (hK : ∀ x y, a ≤ K (x, y)) : operator μ K ≠ 0 := by
  let f : Hilbert μ := ContinuousMap.toLp 2 μ ℝ (1 : C(X, ℝ))
  have hf : f =ᵐ[μ] fun _ => (1 : ℝ) := ContinuousMap.coeFn_toLp μ _
  have hb : a ≤ ⟪f, operator μ K f⟫_ℝ := by
    rw [inner_operator_prod]
    calc
      a = ∫ p : X × X, a ∂μ.prod μ := by simp
      _ ≤ _ := integral_mono_ae (integrable_const _) (integrable_matrix_element μ K f f) (by
        filter_upwards [Measure.quasiMeasurePreserving_fst.ae hf,
          Measure.quasiMeasurePreserving_snd.ae hf] with p hp hq
        simpa only [hp, hq, mul_one] using hK p.1 p.2)
  intro hz
  rw [hz] at hb
  exact (not_le_of_gt ha) (by simpa using hb)

omit [SecondCountableTopology X] in
theorem representative_pos (K : C(X × X, ℝ)) {r a : ℝ} (hr : 0 < r) (ha : 0 < a)
    (hK : ∀ x y, a ≤ K (x, y)) (f : Hilbert μ) (hf : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hf0 : f ≠ 0) (x : X) : 0 < eigenRepresentative μ K r f x := by
  have hi := integral_pos_of_nonneg_vector μ f hf hf0
  have hb : a * (∫ y, f y ∂μ) ≤ ∫ y, K (x, y) * f y ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono_ae ((integrable_vector μ f).const_mul a)
      ((integrable_vector μ f).bdd_mul (K.curry x).continuous.aestronglyMeasurable
        (ae_of_all _ (fun y => K.norm_coe_le_norm (x, y))))
    exact hf.mono (fun y hy => mul_le_mul_of_nonneg_right (hK x y) hy)
  change 0 < r⁻¹ * toContinuous μ K f x
  rw [toContinuous_apply]
  exact mul_pos (inv_pos.mpr hr) ((mul_pos ha hi).trans_le hb)

/-- A positive normalized continuous ground state for a uniformly positive symmetric kernel. -/
theorem exists_ground_state (K : C(X × X, ℝ)) (hs : ∀ x y, K (x, y) = K (y, x))
    {a : ℝ} (ha : 0 < a) (hK : ∀ x y, a ≤ K (x, y)) :
    0 < ‖operator μ K‖ ∧ ∃ u : C(X, ℝ),
      (∀ x, 0 < u x) ∧ ‖ContinuousMap.toLp 2 μ ℝ u‖ = 1 ∧
      ∀ x, (∫ y, K (x, y) * u y ∂μ) = ‖operator μ K‖ * u x := by
  have hne := operator_ne_zero μ K ha hK
  have hr := norm_pos_iff.mpr hne
  obtain ⟨v, hv0, hv, he⟩ := exists_nonneg_top μ K hs (fun x y => ha.le.trans (hK x y)) hne
  have hvn := norm_pos_iff.mpr hv0
  let w : Hilbert μ := ‖v‖⁻¹ • v
  have hw : ‖w‖ = 1 := by simp [w, norm_smul, hvn.ne']
  have hw0 : w ≠ 0 := by intro hz; simp [hz] at hw
  have hwpos : ∀ᵐ x ∂μ, 0 ≤ w x := by
    filter_upwards [Lp.coeFn_smul ‖v‖⁻¹ v, hv] with x hx hpos
    rw [hx]
    exact mul_nonneg (inv_nonneg.mpr hvn.le) hpos
  have hwe : operator μ K w = ‖operator μ K‖ • w := by
    simp [w, he, smul_smul, mul_comm]
  refine ⟨hr, eigenRepresentative μ K ‖operator μ K‖ w,
    representative_pos μ K hr ha hK w hwpos hw0, ?_,
    eigenRepresentative_equation μ K hr.ne' w hwe⟩
  rw [toLp_eigenRepresentative μ K hr.ne' w hwe, hw]

omit [SecondCountableTopology X] in
theorem integral_square_toLp (f : C(X, ℝ)) :
    (∫ x, f x ^ 2 ∂μ) = ‖ContinuousMap.toLp 2 μ ℝ f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ f] with x hx
  change f x ^ 2 = (ContinuousMap.toLp 2 μ ℝ f) x * (ContinuousMap.toLp 2 μ ℝ f) x
  rw [hx, pow_two]

omit [SecondCountableTopology X] in
theorem integrable_continuous (f : C(X, ℝ)) : Integrable f μ :=
  (ContinuousMap.memLp (p := 1) μ ℝ f).integrable (by norm_num)

/-- The integral transform on continuous functions. -/
def continuousOperator (K : C(X × X, ℝ)) : C(X, ℝ) →L[ℝ] C(X, ℝ) :=
  ((ContinuousMap.linearIsometryBoundedOfCompact X ℝ ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
    ((toContinuous μ K).comp (ContinuousMap.toLp 2 μ ℝ))

omit [SecondCountableTopology X] in
theorem continuousOperator_apply (K : C(X × X, ℝ)) (f : C(X, ℝ)) (x : X) :
    continuousOperator μ K f x = ∫ y, K (x, y) * f y ∂μ := by
  change toContinuous μ K (ContinuousMap.toLp 2 μ ℝ f) x = _
  rw [toContinuous_apply]
  exact integral_congr_ae ((ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ f).mono
    (fun y hy => congrArg (fun z => K (x, y) * z) hy))

omit [SecondCountableTopology X] in
theorem operator_toLp (K : C(X × X, ℝ)) (f : C(X, ℝ)) :
    operator μ K (ContinuousMap.toLp 2 μ ℝ f) =
      ContinuousMap.toLp 2 μ ℝ (continuousOperator μ K f) := rfl

theorem integral_weighted_operator (K : C(X × X, ℝ)) (hs : ∀ x y, K (x, y) = K (y, x))
    (u f : C(X, ℝ)) {r : ℝ}
    (hu : ∀ x, (∫ y, K (x, y) * u y ∂μ) = r * u x) :
    (∫ x, u x * continuousOperator μ K f x ∂μ) = r * ∫ x, u x * f x ∂μ := by
  have hh : Integrable (fun p : X × X => K p * (u p.1 * f p.2)) (μ.prod μ) :=
    ((integrable_continuous μ u).mul_prod (integrable_continuous μ f)).bdd_mul
      K.continuous.aestronglyMeasurable (ae_of_all _ K.norm_coe_le_norm)
  simp only [continuousOperator_apply, ← integral_const_mul]
  calc
    (∫ x, ∫ y, u x * (K (x, y) * f y) ∂μ ∂μ) =
      ∫ x, ∫ y, K (x, y) * (u x * f y) ∂μ ∂μ := by congr 1; funext x; congr 1; funext y; ring
    _ = ∫ y, ∫ x, K (x, y) * (u x * f y) ∂μ ∂μ := integral_integral_swap hh
    _ = ∫ y, r * (u y * f y) ∂μ := by
      congr 1
      funext y
      simp_rw [hs _ y, ← mul_assoc]
      rw [integral_mul_const, hu]

omit [SecondCountableTopology X] in
theorem integrable_continuous_fun {f : X → ℝ} (hf : Continuous f) : Integrable f μ :=
  integrable_continuous μ ⟨f, hf⟩

/-- Subtracting a positive multiple of the ground-state kernel leaves a
nonnegative kernel with smaller weighted row sums. -/
def remainderKernel (K : C(X × X, ℝ)) (u : C(X, ℝ)) (r δ : ℝ) : C(X × X, ℝ) :=
  ⟨fun p => K p - δ * r * u p.1 * u p.2, by fun_prop⟩

omit [SecondCountableTopology X] in
theorem remainder_apply (K : C(X × X, ℝ)) (u f : C(X, ℝ)) (r δ : ℝ) (x : X) :
    continuousOperator μ (remainderKernel K u r δ) f x =
      continuousOperator μ K f x - δ * r * u x * ∫ y, u y * f y ∂μ := by
  simp only [continuousOperator_apply, remainderKernel, ContinuousMap.coe_mk, sub_mul]
  rw [integral_sub (integrable_continuous_fun μ (by fun_prop))
    (integrable_continuous_fun μ (by fun_prop))]
  simp_rw [mul_assoc (δ * r * u x)]
  rw [integral_const_mul]

omit [SecondCountableTopology X] in
theorem weighted_row_bound (J : C(X × X, ℝ)) (u f : C(X, ℝ)) {r C : ℝ}
    (hJ : ∀ x y, 0 ≤ J (x, y))
    (hu : ∀ x, continuousOperator μ J u x = r * u x)
    (hf : ∀ x, |f x| ≤ C * u x) (x : X) :
    |continuousOperator μ J f x| ≤ r * C * u x := by
  rw [continuousOperator_apply, ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ y, ‖J (x, y) * f y‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, J (x, y) * (C * u y) ∂μ := by
      apply integral_mono (integrable_continuous_fun μ (by fun_prop))
        (integrable_continuous_fun μ (by fun_prop))
      intro y
      change ‖J (x, y) * f y‖ ≤ J (x, y) * (C * u y)
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hJ x y), Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hf y) (hJ x y)
    _ = C * continuousOperator μ J u x := by
      rw [continuousOperator_apply, ← integral_const_mul]
      congr 1
      funext y
      ring
    _ = _ := by rw [hu]; ring

omit [SecondCountableTopology X] in
/-- A ground-state minorization contracts every orthogonal continuous function
in the weighted supremum norm. -/
theorem weighted_contraction (K : C(X × X, ℝ)) (u f : C(X, ℝ)) {r δ C : ℝ}
    (hun : ‖ContinuousMap.toLp 2 μ ℝ u‖ = 1)
    (hu : ∀ x, continuousOperator μ K u x = r * u x)
    (hminor : ∀ x y, δ * r * u x * u y ≤ K (x, y))
    (horth : (∫ x, u x * f x ∂μ) = 0)
    (hf : ∀ x, |f x| ≤ C * u x) (x : X) :
    |continuousOperator μ K f x| ≤ (r * (1 - δ)) * C * u x := by
  have hmass : (∫ y, u y * u y ∂μ) = 1 := by
    simpa only [← pow_two, hun, one_pow] using integral_square_toLp μ u
  have hJ : ∀ x y, 0 ≤ remainderKernel K u r δ (x, y) :=
    fun x y => sub_nonneg.mpr (hminor x y)
  have hJu : ∀ x, continuousOperator μ (remainderKernel K u r δ) u x =
      (r * (1 - δ)) * u x := by
    intro x
    rw [remainder_apply, hu, hmass]
    ring
  have h := weighted_row_bound μ (remainderKernel K u r δ) u f hJ hJu hf x
  simpa only [remainder_apply, horth, mul_zero, sub_zero] using h

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
theorem exists_minorization (K : C(X × X, ℝ)) (u : C(X, ℝ)) {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hK : ∀ x y, a ≤ K (x, y)) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ x y, δ * r * u x * u y ≤ K (x, y) := by
  let M : ℝ := max ‖u‖ 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let δ : ℝ := min (1 / 2) (a / (2 * r * M ^ 2))
  have hd : 0 < δ := lt_min (by norm_num) (div_pos ha (by positivity))
  have hdhalf : δ ≤ 1 / 2 := min_le_left _ _
  have hb : δ * (2 * r * M ^ 2) ≤ a :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  refine ⟨δ, hd, lt_of_le_of_lt hdhalf (by norm_num), fun x y => ?_⟩
  have hux : |u x| ≤ M := (u.norm_coe_le_norm x).trans (le_max_left _ _)
  have huy : |u y| ≤ M := (u.norm_coe_le_norm y).trans (le_max_left _ _)
  have hp : u x * u y ≤ M ^ 2 := by
    calc
      _ ≤ |u x * u y| := le_abs_self _
      _ = |u x| * |u y| := abs_mul _ _
      _ ≤ M * M := mul_le_mul hux huy (abs_nonneg _) hM.le
      _ = _ := by ring
  calc
    δ * r * u x * u y = (δ * r) * (u x * u y) := by ring
    _ ≤ (δ * r) * M ^ 2 := mul_le_mul_of_nonneg_left hp (mul_pos hd hr).le
    _ ≤ a := by nlinarith
    _ ≤ K (x, y) := hK x y

/-- A continuous function divided by the strictly positive ground state. -/
def relative (u f : C(X, ℝ)) (hu : ∀ x, 0 < u x) : C(X, ℝ) :=
  ⟨fun x => f x / u x, f.continuous.div u.continuous (fun x => (hu x).ne')⟩

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
theorem bound_relative (u f : C(X, ℝ)) (hu : ∀ x, 0 < u x) (x : X) :
    |f x| ≤ ‖relative u f hu‖ * u x := by
  have h := (relative u f hu).norm_coe_le_norm x
  change |f x / u x| ≤ _ at h
  rw [abs_div, abs_of_pos (hu x)] at h
  exact (div_le_iff₀ (hu x)).mp h

omit [SecondCountableTopology X] in
theorem eigenvalue_bound_of_minorization (K : C(X × X, ℝ)) (u f : C(X, ℝ))
    {r δ e : ℝ} (hr : 0 < r) (hd : δ < 1) (hupos : ∀ x, 0 < u x)
    (hun : ‖ContinuousMap.toLp 2 μ ℝ u‖ = 1)
    (hu : ∀ x, continuousOperator μ K u x = r * u x)
    (hminor : ∀ x y, δ * r * u x * u y ≤ K (x, y))
    (horth : (∫ x, u x * f x ∂μ) = 0) (hf : f ≠ 0)
    (he : ∀ x, continuousOperator μ K f x = e * f x) : |e| ≤ r * (1 - δ) := by
  have hf' : relative u f hupos ≠ 0 := by
    intro hz
    apply hf
    ext x
    have hx := congrArg (fun g : C(X, ℝ) => g x) hz
    change f x / u x = 0 at hx
    exact (div_eq_zero_iff).mp hx |>.resolve_right (hupos x).ne'
  have hnorm : 0 < ‖relative u f hupos‖ := norm_pos_iff.mpr hf'
  have hb : ‖e • relative u f hupos‖ ≤ (r * (1 - δ)) * ‖relative u f hupos‖ := by
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro x
    have h := weighted_contraction μ K u f hun hu hminor horth (bound_relative u f hupos) x
    rw [he] at h
    change |e * (f x / u x)| ≤ _
    rw [← mul_div_assoc, abs_div, abs_of_pos (hupos x)]
    exact (div_le_iff₀ (hupos x)).mpr h
  rw [norm_smul, Real.norm_eq_abs] at hb
  exact (mul_le_mul_iff_left₀ hnorm).mp hb

theorem eigenfunction_orthogonal (K : C(X × X, ℝ))
    (hs : ∀ x y, K (x, y) = K (y, x)) (u f : C(X, ℝ)) {r e : ℝ}
    (hu : ∀ x, continuousOperator μ K u x = r * u x)
    (he : ∀ x, continuousOperator μ K f x = e * f x) (hne : e ≠ r) :
    (∫ x, u x * f x ∂μ) = 0 := by
  have h := integral_weighted_operator μ K hs u f (by simpa only [continuousOperator_apply] using hu)
  simp_rw [he, mul_left_comm (u _) e, integral_const_mul] at h
  exact (mul_eq_mul_right_iff.mp h).resolve_left hne

omit [SecondCountableTopology X] in
/-- Strict positivity makes the leading eigenfunction unique up to a scalar. -/
theorem leading_eigenfunction_unique (K : C(X × X, ℝ)) (u f : C(X, ℝ))
    {r δ : ℝ} (hr : 0 < r) (hd0 : 0 < δ) (hd1 : δ < 1)
    (hupos : ∀ x, 0 < u x) (hun : ‖ContinuousMap.toLp 2 μ ℝ u‖ = 1)
    (hu : ∀ x, continuousOperator μ K u x = r * u x)
    (hminor : ∀ x y, δ * r * u x * u y ≤ K (x, y))
    (hf : ∀ x, continuousOperator μ K f x = r * f x) :
    f = (∫ x, u x * f x ∂μ) • u := by
  let c := ∫ x, u x * f x ∂μ
  let g : C(X, ℝ) := f - c • u
  have hmass : (∫ x, u x * u x ∂μ) = 1 := by
    simpa only [← pow_two, hun, one_pow] using integral_square_toLp μ u
  have hgorth : (∫ x, u x * g x ∂μ) = 0 := by
    change (∫ x, u x * (f x - c * u x) ∂μ) = 0
    simp_rw [mul_sub, mul_left_comm (u _) c]
    rw [integral_sub (integrable_continuous_fun μ (by fun_prop))
      (integrable_continuous_fun μ (by fun_prop)), integral_const_mul, hmass]
    simp only [mul_one, c, sub_self]
  have hge : ∀ x, continuousOperator μ K g x = r * g x := by
    intro x
    change continuousOperator μ K (f - c • u) x = _
    rw [map_sub, map_smul]
    change continuousOperator μ K f x - c * continuousOperator μ K u x = r * (f x - c * u x)
    rw [hf, hu]
    ring
  have hgz : g = 0 := by
    by_contra hn
    have hb := eigenvalue_bound_of_minorization μ K u g hr hd1 hupos hun hu hminor hgorth hn hge
    rw [abs_of_pos hr] at hb
    nlinarith [mul_pos hr hd0]
  exact sub_eq_zero.mp hgz

omit [SecondCountableTopology X] in
theorem eigenRepresentative_continuous_eigenfunction (K : C(X × X, ℝ)) {r : ℝ}
    (hr : r ≠ 0) (f : Hilbert μ) (he : operator μ K f = r • f) (x : X) :
    continuousOperator μ K (eigenRepresentative μ K r f) x =
      r * eigenRepresentative μ K r f x := by
  rw [continuousOperator_apply]
  exact eigenRepresentative_equation μ K hr f he x

/-- Every nonzero eigenvalue has a continuous eigenfunction representative. -/
theorem eigenvalue_alternative (K : C(X × X, ℝ))
    (hs : ∀ x y, K (x, y) = K (y, x)) (u : C(X, ℝ))
    {r δ : ℝ} (hr : 0 < r) (hd0 : 0 < δ) (hd1 : δ < 1)
    (hupos : ∀ x, 0 < u x) (hun : ‖ContinuousMap.toLp 2 μ ℝ u‖ = 1)
    (hu : ∀ x, continuousOperator μ K u x = r * u x)
    (hminor : ∀ x y, δ * r * u x * u y ≤ K (x, y))
    {e : ℝ} {v : Hilbert μ} (hv : v ≠ 0) (he : operator μ K v = e • v) :
    (e = r ∧ ∃ c : ℝ, v = c • ContinuousMap.toLp 2 μ ℝ u) ∨ |e| ≤ r * (1 - δ) := by
  by_cases he0 : e = 0
  · right
    rw [he0, abs_zero]
    positivity
  let f := eigenRepresentative μ K e v
  have hfe := eigenRepresentative_continuous_eigenfunction μ K he0 v he
  have hf : f ≠ 0 := by
    intro hz
    have h := toLp_eigenRepresentative μ K he0 v he
    change ContinuousMap.toLp 2 μ ℝ f = v at h
    rw [hz, map_zero] at h
    exact hv h.symm
  by_cases her : e = r
  · left
    refine ⟨her, ∫ x, u x * f x ∂μ, ?_⟩
    have huniq := leading_eigenfunction_unique μ K u f hr hd0 hd1 hupos hun hu hminor
      (fun x => (hfe x).trans (by change e * f x = r * f x; rw [her]))
    have hlp := congrArg (ContinuousMap.toLp 2 μ ℝ) huniq
    rw [map_smul] at hlp
    exact (toLp_eigenRepresentative μ K he0 v he).symm.trans hlp
  · exact Or.inr (eigenvalue_bound_of_minorization μ K u f hr hd1 hupos hun hu hminor
      (eigenfunction_orthogonal μ K hs u f hu hfe her) hf hfe)

/-- Positivity of a continuous symmetric kernel gives a simple positive leading
eigenvalue and a strict absolute spectral gap. The gap here can depend on the kernel. -/
theorem positive_kernel_spectral_gap (K : C(X × X, ℝ))
    (hs : ∀ x y, K (x, y) = K (y, x)) {a : ℝ}
    (ha : 0 < a) (hK : ∀ x y, a ≤ K (x, y)) :
    ∃ (r δ : ℝ) (u : C(X, ℝ)), 0 < r ∧ 0 < δ ∧ δ < 1 ∧
      (∀ x, 0 < u x) ∧ ‖ContinuousMap.toLp 2 μ ℝ u‖ = 1 ∧
      operator μ K (ContinuousMap.toLp 2 μ ℝ u) = r • ContinuousMap.toLp 2 μ ℝ u ∧
      (∀ e ∈ spectrum ℝ (operator μ K), e = r ∨ |e| ≤ r * (1 - δ)) ∧
      (∀ v : Hilbert μ, operator μ K v = r • v →
        ∃ c : ℝ, v = c • ContinuousMap.toLp 2 μ ℝ u) := by
  obtain ⟨hr, u, hup, hun, hu⟩ := exists_ground_state μ K hs ha hK
  let r := ‖operator μ K‖
  obtain ⟨δ, hd0, hd1, hminor⟩ := exists_minorization K u ha hr hK
  have hu' : ∀ x, continuousOperator μ K u x = r * u x := by
    simpa only [continuousOperator_apply] using hu
  have hul : operator μ K (ContinuousMap.toLp 2 μ ℝ u) = r • ContinuousMap.toLp 2 μ ℝ u := by
    rw [operator_toLp, ← map_smul]
    congr 1
    ext x
    exact hu' x
  refine ⟨r, δ, u, hr, hd0, hd1, hup, hun, hul, ?_, ?_⟩
  · intro e he
    by_cases hz : e = 0
    · right; rw [hz, abs_zero]; positivity
    obtain ⟨v, hv, hv0⟩ :=
      (((compact_operator μ K).hasEigenvalue_iff_mem_spectrum hz).mpr he).exists_hasEigenvector
    exact (eigenvalue_alternative μ K hs u hr hd0 hd1 hup hun hu' hminor hv0
      (Module.End.mem_eigenspace_iff.mp hv)).imp (fun h => h.1) id
  · intro v hv
    by_cases hv0 : v = 0
    · exact ⟨0, by simp [hv0]⟩
    rcases eigenvalue_alternative μ K hs u hr hd0 hd1 hup hun hu' hminor hv0 hv with h | h
    · exact h.2
    · rw [abs_of_pos hr] at h
      nlinarith [mul_pos hr hd0]

/-- Composition of two continuous integral kernels. -/
def convolution (K J : C(X × X, ℝ)) : C(X × X, ℝ) :=
  ⟨fun p => ∫ y, K (p.1, y) * J (y, p.2) ∂μ, by
    apply continuous_of_dominated (bound := fun _ => ‖K‖ * ‖J‖)
    · intro p; exact (show Continuous (fun y => K (p.1, y) * J (y, p.2)) by fun_prop).aestronglyMeasurable
    · intro p
      exact ae_of_all _ (fun y => by
        rw [norm_mul]
        exact mul_le_mul (K.norm_coe_le_norm _) (J.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _))
    · exact integrable_const _
    · exact ae_of_all _ (fun y => by fun_prop)⟩

/-- `kernelPower K n` has `n + 1` edges; no distributional identity kernel is needed. -/
def kernelPower (K : C(X × X, ℝ)) : ℕ → C(X × X, ℝ)
  | 0 => K
  | n + 1 => convolution μ K (kernelPower K n)

theorem kernelPower_succ (K : C(X × X, ℝ)) (n : ℕ) (x y : X) :
    kernelPower μ K (n + 1) (x, y) =
      ∫ z, K (x, z) * kernelPower μ K n (z, y) ∂μ := rfl

/-- Column of a continuous kernel. -/
def column (K : C(X × X, ℝ)) (y : X) : C(X, ℝ) :=
  ⟨fun x => K (x, y), K.continuous.comp (continuous_id.prodMk continuous_const)⟩

theorem kernelPower_column (K : C(X × X, ℝ)) (n : ℕ) (y : X) :
    column (kernelPower μ K n) y = (continuousOperator μ K ^ n) (column K y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ']
    change column (kernelPower μ K (n + 1)) y =
      continuousOperator μ K ((continuousOperator μ K ^ n) (column K y))
    rw [← ih]
    ext x
    exact (continuousOperator_apply μ K (column (kernelPower μ K n) y) x).symm

theorem power_weighted_mean (K : C(X × X, ℝ))
    (hs : ∀ x y, K (x, y) = K (y, x)) (u f : C(X, ℝ))
    (hu : ∀ x, continuousOperator μ K u x = u x) (n : ℕ) :
    (∫ x, u x * ((continuousOperator μ K ^ n) f) x ∂μ) = ∫ x, u x * f x ∂μ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ']
    change (∫ x, u x * continuousOperator μ K ((continuousOperator μ K ^ n) f) x ∂μ) = _
    rw [integral_weighted_operator μ K hs u _ (r := 1)
      (by simpa only [continuousOperator_apply, one_mul] using hu), one_mul, ih]

/-- Exponential convergence on the complement of a normalized positive ground state. -/
theorem power_weighted_contraction (K : C(X × X, ℝ))
    (hs : ∀ x y, K (x, y) = K (y, x)) (u f : C(X, ℝ)) {δ C : ℝ}
    (hun : ‖ContinuousMap.toLp 2 μ ℝ u‖ = 1)
    (hu : ∀ x, continuousOperator μ K u x = u x)
    (hminor : ∀ x y, δ * u x * u y ≤ K (x, y))
    (horth : (∫ x, u x * f x ∂μ) = 0) (hf : ∀ x, |f x| ≤ C * u x)
    (n : ℕ) (x : X) :
    |((continuousOperator μ K ^ n) f) x| ≤ (1 - δ) ^ n * C * u x := by
  induction n generalizing x with
  | zero => simpa using hf x
  | succ n ih =>
    rw [pow_succ']
    change |continuousOperator μ K ((continuousOperator μ K ^ n) f) x| ≤ _
    have h := weighted_contraction μ K u ((continuousOperator μ K ^ n) f)
      (r := 1) (C := (1 - δ) ^ n * C) hun (by simpa using hu)
      (by simpa using hminor) (by rw [power_weighted_mean μ K hs u f hu, horth]) ih
    simpa only [one_mul, pow_succ', mul_assoc] using h x

omit [SecondCountableTopology X] in
theorem power_ground (K : C(X × X, ℝ)) (u : C(X, ℝ))
    (hu : ∀ x, continuousOperator μ K u x = u x) (n : ℕ) :
    (continuousOperator μ K ^ n) u = u := by
  have hu' : continuousOperator μ K u = u := ContinuousMap.ext hu
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ']
    change continuousOperator μ K ((continuousOperator μ K ^ n) u) = u
    rw [ih, hu']

theorem kernelPower_error_bound (K : C(X × X, ℝ))
    (hs : ∀ x y, K (x, y) = K (y, x)) (u : C(X, ℝ)) {δ C : ℝ}
    (hun : ‖ContinuousMap.toLp 2 μ ℝ u‖ = 1)
    (hu : ∀ x, continuousOperator μ K u x = u x)
    (hminor : ∀ x y, δ * u x * u y ≤ K (x, y))
    (hb : ∀ x y, |K (x, y) - u x * u y| ≤ C * u x) (n : ℕ) (x y : X) :
    |kernelPower μ K n (x, y) - u x * u y| ≤ (1 - δ) ^ n * C * u x := by
  let f : C(X, ℝ) := column K y - u y • u
  have hmass : (∫ x, u x * u x ∂μ) = 1 := by
    simpa only [← pow_two, hun, one_pow] using integral_square_toLp μ u
  have horth : (∫ x, u x * f x ∂μ) = 0 := by
    change (∫ x, u x * (K (x, y) - u y * u x) ∂μ) = 0
    simp_rw [mul_sub, mul_left_comm (u _) (u y)]
    rw [integral_sub (integrable_continuous_fun μ (by fun_prop))
      (integrable_continuous_fun μ (by fun_prop)), integral_const_mul, hmass, mul_one]
    have h := hu y
    rw [continuousOperator_apply] at h
    simp_rw [hs _ y, mul_comm (u _) (K (_, _))]
    exact sub_eq_zero.mpr h
  have he : ((continuousOperator μ K ^ n) f) x = kernelPower μ K n (x, y) - u x * u y := by
    change ((continuousOperator μ K ^ n) (column K y - u y • u)) x = _
    rw [map_sub, map_smul, power_ground μ K u hu, ← kernelPower_column]
    change kernelPower μ K n (x, y) - u y * u x = _
    ring
  rw [← he]
  apply power_weighted_contraction μ K hs u f hun hu hminor horth
  intro z
  change |K (z, y) - u y * u z| ≤ C * u z
  simpa only [mul_comm (u y) (u z)] using hb z y

/-- Kernel of the orthogonal projection onto a normalized ground state. -/
def rankOne (u : C(X, ℝ)) : C(X × X, ℝ) :=
  ⟨fun p => u p.1 * u p.2, by fun_prop⟩

/-- Normalized kernel powers converge uniformly to the ground-state projection. -/
theorem kernelPower_tendsto (K : C(X × X, ℝ))
    (hs : ∀ x y, K (x, y) = K (y, x)) (u : C(X, ℝ)) {δ : ℝ}
    (hd0 : 0 < δ) (hd1 : δ < 1) (hup : ∀ x, 0 < u x)
    (hun : ‖ContinuousMap.toLp 2 μ ℝ u‖ = 1)
    (hu : ∀ x, continuousOperator μ K u x = u x)
    (hminor : ∀ x y, δ * u x * u y ≤ K (x, y)) :
    Tendsto (kernelPower μ K) atTop (𝓝 (rankOne u)) := by
  let R : C(X × X, ℝ) := ⟨fun p => (K p - u p.1 * u p.2) / u p.1,
    by exact (K.continuous.sub (by fun_prop)).div (by fun_prop) (fun p => (hup p.1).ne')⟩
  have hR (x y : X) : |K (x, y) - u x * u y| ≤ ‖R‖ * u x := by
    have h := R.norm_coe_le_norm (x, y)
    change |(K (x, y) - u x * u y) / u x| ≤ _ at h
    rw [abs_div, abs_of_pos (hup x)] at h
    exact (div_le_iff₀ (hup x)).mp h
  have hb (n : ℕ) : ‖kernelPower μ K n - rankOne u‖ ≤ (1 - δ) ^ n * ‖R‖ * ‖u‖ := by
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro p
    change |kernelPower μ K n p - u p.1 * u p.2| ≤ _
    exact (kernelPower_error_bound μ K hs u hun hu hminor hR n p.1 p.2).trans
      (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (u.norm_coe_le_norm _)) (by positivity))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) hb
  simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith : 0 ≤ 1 - δ)
    (by linarith : 1 - δ < 1)).mul_const ‖R‖).mul_const ‖u‖

omit [SecondCountableTopology X] in
/-- Integration as a bounded linear functional on continuous functions. -/
def integralMap : C(X, ℝ) →L[ℝ] ℝ :=
  MeasureTheory.L1.integralCLM.comp (ContinuousMap.toLp 1 μ ℝ)

omit [SecondCountableTopology X] in
theorem integralMap_apply (f : C(X, ℝ)) : integralMap μ f = ∫ x, f x ∂μ := by
  change MeasureTheory.L1.integralCLM (ContinuousMap.toLp 1 μ ℝ f) = _
  rw [← MeasureTheory.L1.integral_eq, MeasureTheory.L1.integral_eq_integral]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) μ f)

/-- Two arcs joined at their endpoints, with an observable on the endpoints. -/
def cycleIntegral (K : C(X × X, ℝ)) (k n : ℕ) (F : C(X × X, ℝ)) : ℝ :=
  ∫ p, F p * kernelPower μ K k p * kernelPower μ K n (p.2, p.1) ∂μ.prod μ

theorem cycleIntegral_tendsto (K : C(X × X, ℝ)) (u : C(X, ℝ))
    (hlim : Tendsto (kernelPower μ K) atTop (𝓝 (rankOne u))) (k : ℕ) (F : C(X × X, ℝ)) :
    Tendsto (fun n => cycleIntegral μ K k n F) atTop
      (𝓝 (∫ p, F p * kernelPower μ K k p * (u p.2 * u p.1) ∂μ.prod μ)) := by
  let swap : C(X × X, X × X) := ⟨Prod.swap, continuous_swap⟩
  have hc : Continuous (fun J : C(X × X, ℝ) => integralMap (μ.prod μ)
      ((F * kernelPower μ K k) * (J.comp swap))) := by fun_prop
  have h := hc.continuousAt.tendsto.comp hlim
  simpa only [integralMap_apply, ContinuousMap.coe_mul, ContinuousMap.coe_comp,
    ContinuousMap.coe_mk, Pi.mul_apply, Function.comp_def, Prod.swap, rankOne, cycleIntegral, swap] using h

theorem convolution_apply (K J : C(X × X, ℝ)) (f : C(X, ℝ)) (x : X) :
    continuousOperator μ (convolution μ K J) f x =
      continuousOperator μ K (continuousOperator μ J f) x := by
  simp only [continuousOperator_apply, convolution, ContinuousMap.coe_mk]
  simp_rw [← integral_mul_const, ← integral_const_mul]
  have hh : Integrable (fun p : X × X => K (x, p.2) * (J (p.2, p.1) * f p.1)) (μ.prod μ) :=
    integrable_continuous_fun (μ.prod μ) (by fun_prop)
  calc
    _ = ∫ y, ∫ z, K (x, z) * (J (z, y) * f y) ∂μ ∂μ := by
      congr 1; funext y; congr 1; funext z; ring
    _ = _ := integral_integral_swap hh

theorem kernelPower_operator (K : C(X × X, ℝ)) (n : ℕ) (f : C(X, ℝ)) :
    continuousOperator μ (kernelPower μ K n) f = (continuousOperator μ K ^ (n + 1)) f := by
  induction n with
  | zero => simp [kernelPower]
  | succ n ih =>
    ext x
    change continuousOperator μ (convolution μ K (kernelPower μ K n)) f x = _
    rw [convolution_apply, ih, pow_succ' _ (n + 1)]
    rfl

/-- Multiplication of separate endpoint observables. -/
def endpointProduct (F G : C(X, ℝ)) : C(X × X, ℝ) :=
  ⟨fun p => F p.1 * G p.2, by fun_prop⟩

theorem ground_endpoint_integral (K : C(X × X, ℝ)) (u F G : C(X, ℝ)) (k : ℕ) :
    (∫ p, endpointProduct F G p * kernelPower μ K k p * (u p.2 * u p.1) ∂μ.prod μ) =
      ∫ x, (F x * u x) * ((continuousOperator μ K ^ (k + 1)) (G * u)) x ∂μ := by
  rw [integral_prod _ (integrable_continuous_fun (μ.prod μ) (by fun_prop))]
  simp_rw [← kernelPower_operator, continuousOperator_apply, ← integral_const_mul]
  congr 1
  funext x
  congr 1
  funext y
  change (F x * G y) * kernelPower μ K k (x, y) * (u y * u x) =
    (F x * u x) * (kernelPower μ K k (x, y) * (G y * u y))
  ring

theorem cycle_partition_tendsto (K : C(X × X, ℝ)) (u : C(X, ℝ))
    (hun : ‖ContinuousMap.toLp 2 μ ℝ u‖ = 1)
    (hu : ∀ x, continuousOperator μ K u x = u x)
    (hlim : Tendsto (kernelPower μ K) atTop (𝓝 (rankOne u))) (k : ℕ) :
    Tendsto (fun n => cycleIntegral μ K k n 1) atTop (𝓝 1) := by
  have h := cycleIntegral_tendsto μ K u hlim k (endpointProduct 1 1)
  have h1 : endpointProduct (1 : C(X, ℝ)) 1 = 1 := by ext p; simp [endpointProduct]
  rw [ground_endpoint_integral, h1] at h
  simpa only [one_mul, ContinuousMap.one_apply, power_ground μ K u hu,
    ← pow_two, integral_square_toLp, hun, one_pow] using h

/-- Normalized periodic expectation of endpoint observables. -/
def cycleExpectation (K : C(X × X, ℝ)) (k n : ℕ) (F : C(X × X, ℝ)) : ℝ :=
  cycleIntegral μ K k n F / cycleIntegral μ K k n 1

theorem cycleExpectation_tendsto (K : C(X × X, ℝ)) (u : C(X, ℝ))
    (hun : ‖ContinuousMap.toLp 2 μ ℝ u‖ = 1)
    (hu : ∀ x, continuousOperator μ K u x = u x)
    (hlim : Tendsto (kernelPower μ K) atTop (𝓝 (rankOne u))) (k : ℕ) (F G : C(X, ℝ)) :
    Tendsto (fun n => cycleExpectation μ K k n (endpointProduct F G)) atTop
      (𝓝 (∫ x, (F x * u x) * ((continuousOperator μ K ^ (k + 1)) (G * u)) x ∂μ)) := by
  have h := (cycleIntegral_tendsto μ K u hlim k (endpointProduct F G)).div
    (cycle_partition_tendsto μ K u hun hu hlim k) (by norm_num : (1 : ℝ) ≠ 0)
  simpa only [cycleExpectation, div_one, ground_endpoint_integral, Pi.div_def] using h

omit [SecondCountableTopology X] in
theorem power_eigenfunction (K : C(X × X, ℝ)) (f : C(X, ℝ)) {e : ℝ}
    (hf : ∀ x, continuousOperator μ K f x = e * f x) (n : ℕ) :
    (continuousOperator μ K ^ n) f = e ^ n • f := by
  have hf' : continuousOperator μ K f = e • f := ContinuousMap.ext hf
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change continuousOperator μ K ((continuousOperator μ K ^ n) f) = _
    rw [ih, map_smul, hf', smul_smul, pow_succ]

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
theorem relative_mul_ground (u f : C(X, ℝ)) (hu : ∀ x, 0 < u x) :
    relative u f hu * u = f := by
  ext x
  exact div_mul_cancel₀ _ (hu x).ne'

/-- The infinite-cylinder covariance of the relative eigenfunction detects its eigenvalue. -/
theorem cycle_covariance_eigenfunction_tendsto (K : C(X × X, ℝ))
    (hs : ∀ x y, K (x, y) = K (y, x)) (u f : C(X, ℝ)) {e : ℝ}
    (hup : ∀ x, 0 < u x) (hun : ‖ContinuousMap.toLp 2 μ ℝ u‖ = 1)
    (hu : ∀ x, continuousOperator μ K u x = u x)
    (hlim : Tendsto (kernelPower μ K) atTop (𝓝 (rankOne u)))
    (hf : ∀ x, continuousOperator μ K f x = e * f x) (he : e ≠ 1) (k : ℕ) :
    Tendsto (fun n =>
      cycleExpectation μ K k n (endpointProduct (relative u f hup) (relative u f hup)) -
      cycleExpectation μ K k n (endpointProduct (relative u f hup) 1) *
      cycleExpectation μ K k n (endpointProduct 1 (relative u f hup))) atTop
      (𝓝 (e ^ (k + 1) * ‖ContinuousMap.toLp 2 μ ℝ f‖ ^ 2)) := by
  let F := relative u f hup
  have hFu := relative_mul_ground u f hup
  have ho : (∫ x, u x * f x ∂μ) = 0 :=
    eigenfunction_orthogonal μ K hs u f (by simpa using hu) hf he
  have hp := cycleExpectation_tendsto μ K u hun hu hlim k F F
  have hl := cycleExpectation_tendsto μ K u hun hu hlim k F 1
  have hr := cycleExpectation_tendsto μ K u hun hu hlim k 1 F
  have hp' : Tendsto (fun n => cycleExpectation μ K k n (endpointProduct F F)) atTop
      (𝓝 (e ^ (k + 1) * ‖ContinuousMap.toLp 2 μ ℝ f‖ ^ 2)) := by
    simpa only [F, hFu, ← ContinuousMap.mul_apply, power_eigenfunction μ K f hf,
      ContinuousMap.smul_apply, smul_eq_mul, mul_left_comm (f _) (e ^ (k + 1)),
      ← pow_two, integral_const_mul, integral_square_toLp] using hp
  have hl' : Tendsto (fun n => cycleExpectation μ K k n (endpointProduct F 1)) atTop (𝓝 0) := by
    have ho' : (∫ x, (u * f) x ∂μ) = 0 := ho
    simpa only [one_mul, F, power_ground μ K u hu, ← ContinuousMap.mul_apply, hFu,
      mul_comm f u, ho'] using hl
  have hr' : Tendsto (fun n => cycleExpectation μ K k n (endpointProduct 1 F)) atTop (𝓝 0) := by
    simpa only [F, hFu, ContinuousMap.one_apply, one_mul, power_eigenfunction μ K f hf,
      ContinuousMap.smul_apply, smul_eq_mul, mul_left_comm (u _) (e ^ (k + 1)),
      integral_const_mul, ho, mul_zero] using hr
  simpa only [mul_zero, sub_zero] using hp'.sub (hl'.mul hr')

/-- Connected correlation of one observable at the two endpoints of a cycle. -/
def cycleCovariance (K : C(X × X, ℝ)) (k n : ℕ) (F : C(X, ℝ)) : ℝ :=
  cycleExpectation μ K k n (endpointProduct F F) -
    cycleExpectation μ K k n (endpointProduct F 1) *
    cycleExpectation μ K k n (endpointProduct 1 F)

/-- Periodic-volume clustering bounds the eigenvalue ratio without traces or
an eigenvalue enumeration. The covariance prefactor may depend on the observable. -/
theorem eigenvalue_le_of_cycle_clustering (K : C(X × X, ℝ))
    (hs : ∀ x y, K (x, y) = K (y, x)) (u f : C(X, ℝ)) {e κ C : ℝ}
    (hup : ∀ x, 0 < u x) (hun : ‖ContinuousMap.toLp 2 μ ℝ u‖ = 1)
    (hu : ∀ x, continuousOperator μ K u x = u x)
    (hlim : Tendsto (kernelPower μ K) atTop (𝓝 (rankOne u)))
    (hf : ∀ x, continuousOperator μ K f x = e * f x) (he : e ≠ 1)
    (hf0 : ContinuousMap.toLp 2 μ ℝ f ≠ 0)
    (hcluster : ∀ k : ℕ, ∀ᶠ n in atTop,
      |cycleCovariance μ K k n (relative u f hup)| ≤ C * Real.exp (-κ * (k + 1))) :
    |e| ≤ Real.exp (-κ) := by
  have hmass : 0 < ‖ContinuousMap.toLp 2 μ ℝ f‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hf0)
  apply StrongCouplingTransferGap.Spectral.le_of_power_bound (Real.exp_pos _)
    (C := C / ‖ContinuousMap.toLp 2 μ ℝ f‖ ^ 2)
  intro q hq
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  have ht := cycle_covariance_eigenfunction_tendsto μ K hs u f hup hun hu hlim hf he k
  have hb := le_of_tendsto ht.abs (hcluster k)
  simp only [abs_mul, abs_pow, abs_norm] at hb
  have hexp : Real.exp (-κ * (k + 1)) = Real.exp (-κ) ^ (k + 1) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hexp] at hb
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hmass).mpr hb

omit [SecondCountableTopology X] in
theorem continuousOperator_smul (K : C(X × X, ℝ)) (a : ℝ) (f : C(X, ℝ)) :
    continuousOperator μ (a • K) f = a • continuousOperator μ K f := by
  ext x
  simp only [continuousOperator_apply, ContinuousMap.smul_apply, smul_eq_mul]
  simp_rw [mul_assoc, integral_const_mul]

theorem kernelPower_smul (K : C(X × X, ℝ)) (a : ℝ) (n : ℕ) :
    kernelPower μ (a • K) n = a ^ (n + 1) • kernelPower μ K n := by
  induction n with
  | zero => simp [kernelPower]
  | succ n ih =>
    ext p
    rcases p with ⟨x, y⟩
    rw [kernelPower_succ, ih]
    change (∫ z, (a * K (x, z)) * (a ^ (n + 1) * kernelPower μ K n (z, y)) ∂μ) =
      a ^ (n + 1 + 1) * kernelPower μ K (n + 1) (x, y)
    simp_rw [show ∀ z, (a * K (x, z)) * (a ^ (n + 1) * kernelPower μ K n (z, y)) =
      (a * a ^ (n + 1)) * (K (x, z) * kernelPower μ K n (z, y)) by intro z; ring]
    rw [integral_const_mul, ← pow_succ']
    rfl

theorem cycleIntegral_smul (K : C(X × X, ℝ)) (a : ℝ) (k n : ℕ) (F : C(X × X, ℝ)) :
    cycleIntegral μ (a • K) k n F = (a ^ (k + 1) * a ^ (n + 1)) * cycleIntegral μ K k n F := by
  unfold cycleIntegral
  simp only [kernelPower_smul, ContinuousMap.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext p
  ring

theorem cycleExpectation_smul (K : C(X × X, ℝ)) {a : ℝ} (ha : a ≠ 0)
    (k n : ℕ) (F : C(X × X, ℝ)) :
    cycleExpectation μ (a • K) k n F = cycleExpectation μ K k n F := by
  simp only [cycleExpectation, cycleIntegral_smul]
  exact mul_div_mul_left _ _ (mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ ha))

theorem cycleCovariance_smul (K : C(X × X, ℝ)) {a : ℝ} (ha : a ≠ 0)
    (k n : ℕ) (F : C(X, ℝ)) : cycleCovariance μ (a • K) k n F = cycleCovariance μ K k n F := by
  simp only [cycleCovariance, cycleExpectation_smul μ K ha]

/-- An exponential bound for periodic covariances gives an absolute gap in the
entire real spectrum, and the leading eigenvalue is simple. -/
theorem spectral_gap_of_cycle_clustering (K : C(X × X, ℝ))
    (hs : ∀ x y, K (x, y) = K (y, x)) {a κ : ℝ}
    (ha : 0 < a) (hK : ∀ x y, a ≤ K (x, y))
    (hcluster : ∀ F : C(X, ℝ), ∃ C : ℝ, ∀ k : ℕ, ∀ᶠ n in atTop,
      |cycleCovariance μ K k n F| ≤ C * Real.exp (-κ * (k + 1))) :
    ∃ (r : ℝ) (u : C(X, ℝ)), 0 < r ∧ (∀ x, 0 < u x) ∧
      ‖ContinuousMap.toLp 2 μ ℝ u‖ = 1 ∧
      operator μ K (ContinuousMap.toLp 2 μ ℝ u) = r • ContinuousMap.toLp 2 μ ℝ u ∧
      (∀ v : Hilbert μ, operator μ K v = r • v →
        ∃ c : ℝ, v = c • ContinuousMap.toLp 2 μ ℝ u) ∧
      (∀ e ∈ spectrum ℝ (operator μ K), e = r ∨ |e| ≤ Real.exp (-κ) * r) := by
  obtain ⟨hr, u, hup, hun, hu⟩ := exists_ground_state μ K hs ha hK
  let r := ‖operator μ K‖
  obtain ⟨δ, hd0, hd1, hminor⟩ := exists_minorization K u ha hr hK
  have hu' : ∀ x, continuousOperator μ K u x = r * u x := by
    simpa only [continuousOperator_apply] using hu
  let J : C(X × X, ℝ) := r⁻¹ • K
  have hJs : ∀ x y, J (x, y) = J (y, x) := by
    intro x y
    change r⁻¹ * K (x, y) = r⁻¹ * K (y, x)
    rw [hs]
  have hJu : ∀ x, continuousOperator μ J u x = u x := by
    intro x
    rw [continuousOperator_smul]
    change r⁻¹ * continuousOperator μ K u x = u x
    rw [hu', ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
  have hJminor : ∀ x y, δ * u x * u y ≤ J (x, y) := by
    intro x y
    change δ * u x * u y ≤ r⁻¹ * K (x, y)
    rw [← div_eq_inv_mul, le_div_iff₀ hr]
    calc
      δ * u x * u y * r = δ * r * u x * u y := by ring
      _ ≤ K (x, y) := hminor x y
  have hlim := kernelPower_tendsto μ J hJs u hd0 hd1 hup hun hJu hJminor
  have hul : operator μ K (ContinuousMap.toLp 2 μ ℝ u) = r • ContinuousMap.toLp 2 μ ℝ u := by
    rw [operator_toLp, ← map_smul]
    congr 1
    ext x
    exact hu' x
  refine ⟨r, u, hr, hup, hun, hul, ?_, ?_⟩
  · intro v hv
    by_cases hv0 : v = 0
    · exact ⟨0, by simp [hv0]⟩
    rcases eigenvalue_alternative μ K hs u hr hd0 hd1 hup hun hu' hminor hv0 hv with h | h
    · exact h.2
    · rw [abs_of_pos hr] at h
      nlinarith [mul_pos hr hd0]
  · intro e he
    by_cases her : e = r
    · exact Or.inl her
    right
    by_cases he0 : e = 0
    · rw [he0, abs_zero]; positivity
    obtain ⟨v, hv, hv0⟩ :=
      (((compact_operator μ K).hasEigenvalue_iff_mem_spectrum he0).mpr he).exists_hasEigenvector
    have hve := Module.End.mem_eigenspace_iff.mp hv
    let f := eigenRepresentative μ K e v
    have hfe := eigenRepresentative_continuous_eigenfunction μ K he0 v hve
    have hf0 : ContinuousMap.toLp 2 μ ℝ f ≠ 0 := by
      rw [toLp_eigenRepresentative μ K he0 v hve]
      exact hv0
    have hJe : ∀ x, continuousOperator μ J f x = (e / r) * f x := by
      intro x
      rw [continuousOperator_smul]
      change r⁻¹ * continuousOperator μ K f x = _
      rw [hfe]
      ring
    have hne : e / r ≠ 1 := by
      intro h
      exact her ((div_eq_one_iff_eq hr.ne').mp h)
    obtain ⟨C, hC⟩ := hcluster (relative u f hup)
    have hb := eigenvalue_le_of_cycle_clustering μ J hJs u f hup hun hJu hlim hJe hne hf0
      (C := C) (κ := κ) (fun k => by
        filter_upwards [hC k] with n hn
        change |cycleCovariance μ (r⁻¹ • K) k n (relative u f hup)| ≤ _
        rw [cycleCovariance_smul μ K (inv_ne_zero hr.ne')]
        exact hn)
    rw [abs_div, abs_of_pos hr] at hb
    exact (div_le_iff₀ hr).mp hb

end IntegralKernel

namespace ProductMeasure

variable {A B X : Type*} [TopologicalSpace A] [TopologicalSpace B]
  [CompactSpace A] [CompactSpace B] [MeasurableSpace B] [BorelSpace B]

/-- Integrating one compact variable preserves continuity. -/
def partialIntegral [FirstCountableTopology A] (ν : Measure B) [IsProbabilityMeasure ν]
    (F : C(A × B, ℝ)) : C(A, ℝ) :=
  ⟨fun a => ∫ b, F (a, b) ∂ν, by
    apply continuous_of_dominated (bound := fun _ => ‖F‖)
    · intro a; exact (F.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · intro a; exact ae_of_all _ (fun b => F.norm_coe_le_norm (a, b))
    · exact integrable_const _
    · exact ae_of_all _ (fun b => F.continuous.comp (continuous_id.prodMk continuous_const))⟩

@[fun_prop] theorem continuous_integral [FirstCountableTopology A] (ν : Measure B)
    [IsProbabilityMeasure ν] {F : A → B → ℝ} (hF : Continuous (Function.uncurry F)) :
    Continuous (fun a => ∫ b, F a b ∂ν) :=
  (partialIntegral ν ⟨Function.uncurry F, hF⟩).continuous

omit [TopologicalSpace A] [TopologicalSpace B] [CompactSpace A] [CompactSpace B]
    [MeasurableSpace B] [BorelSpace B] in
/-- Flattening a finite product of finite products preserves the product law. -/
theorem measurePreserving_uncurry [Fintype A] [Fintype B] [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] :
    MeasurePreserving (MeasurableEquiv.curry A B X).symm
      (Measure.pi fun _ : A => Measure.pi fun _ : B => ν)
      (Measure.pi fun _ : A × B => ν) := by
  refine ⟨(MeasurableEquiv.curry A B X).symm.measurable, (Measure.pi_eq fun s _ => ?_).symm⟩
  rw [MeasurableEquiv.map_apply]
  have he : (MeasurableEquiv.curry A B X).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun a => Set.univ.pi (fun b => s (a, b))) := by
    ext f
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const,
      MeasurableEquiv.coe_curry_symm, Function.uncurry_apply_pair, Prod.forall]
  rw [he, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  exact (Fintype.prod_prod_type fun p : A × B => ν (s p)).symm

section FiniteProduct

variable [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] (μ : Measure X) [IsProbabilityMeasure μ]

theorem integral_cons {n : ℕ} (F : (Fin (n + 1) → X) → ℝ) (hF : Continuous F) :
    (∫ v, F v ∂Measure.pi (fun _ => μ)) =
      ∫ x, ∫ u : Fin n → X, F (Fin.cons x u) ∂Measure.pi (fun _ => μ) ∂μ := by
  rw [← ((measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm).integral_comp' F]
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Equiv.coe_fn_mk, Fin.insertNth_zero, cast_eq]
  change (∫ p : X × (Fin n → X), F (Fin.cons p.1 p.2) ∂μ.prod (Measure.pi fun _ => μ)) = _
  exact integral_prod _ (IntegralKernel.integrable_continuous_fun _
    (show Continuous (fun p : X × (Fin n → X) => F (Fin.cons p.1 p.2)) from hF.comp (by fun_prop)))

open StrongCouplingTransferGap.CyclicMatrix

def appendEquiv (a b : ℕ) : ((Fin a → X) × (Fin b → X)) ≃ᵐ (Fin (a + b) → X) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin a ⊕ Fin b => X)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (a + b) => X) finSumFinEquiv)

omit [TopologicalSpace X] [CompactSpace X] [BorelSpace X] [SecondCountableTopology X] in
theorem appendEquiv_left (a b : ℕ) (uv : (Fin a → X) × (Fin b → X)) (i : Fin a) :
    appendEquiv a b uv (i.castAdd b) = uv.1 i := by
  exact MeasurableEquiv.piCongrLeft_apply_apply finSumFinEquiv
    (β := fun _ : Fin (a + b) => X)
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin a ⊕ Fin b => X)).symm uv) (Sum.inl i)

omit [TopologicalSpace X] [CompactSpace X] [BorelSpace X] [SecondCountableTopology X] in
theorem appendEquiv_right (a b : ℕ) (uv : (Fin a → X) × (Fin b → X)) (i : Fin b) :
    appendEquiv a b uv (i.natAdd a) = uv.2 i := by
  exact MeasurableEquiv.piCongrLeft_apply_apply finSumFinEquiv
    (β := fun _ : Fin (a + b) => X)
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin a ⊕ Fin b => X)).symm uv) (Sum.inr i)

omit [TopologicalSpace X] [CompactSpace X] [BorelSpace X] [SecondCountableTopology X] in
theorem appendEquiv_eq (a b : ℕ) (uv : (Fin a → X) × (Fin b → X)) :
    appendEquiv a b uv = Fin.append uv.1 uv.2 := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [Fin.append_left] using appendEquiv_left a b uv j
  · simpa only [Fin.append_right] using appendEquiv_right a b uv j

omit [CompactSpace X] [BorelSpace X] in
theorem measurePreserving_append (a b : ℕ) :
    MeasurePreserving (appendEquiv (X := X) a b)
      ((Measure.pi fun _ : Fin a => μ).prod (Measure.pi fun _ : Fin b => μ))
      (Measure.pi fun _ : Fin (a + b) => μ) :=
  (measurePreserving_piCongrLeft (fun _ : Fin (a + b) => μ) finSumFinEquiv).comp
    (measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin a ⊕ Fin b => μ))

theorem integral_append (a b : ℕ) (F : (Fin (a + b) → X) → ℝ) (hF : Continuous F) :
    (∫ v, F v ∂Measure.pi (fun _ => μ)) =
      ∫ u : Fin a → X, ∫ v : Fin b → X, F (Fin.append u v)
        ∂Measure.pi (fun _ => μ) ∂Measure.pi (fun _ => μ) := by
  rw [← (measurePreserving_append μ a b).integral_comp' F]
  simp only [appendEquiv_eq]
  exact integral_prod _ (IntegralKernel.integrable_continuous_fun _
    (hF.comp (show Continuous (fun p : (Fin a → X) × (Fin b → X) => Fin.append p.1 p.2) by fun_prop)))

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
theorem continuous_segment (K : C(X × X, ℝ)) {n : ℕ} :
    Continuous (fun p : (Fin n → X) × X => segment (Matrix.of fun x y => K (x, y)) p.1 p.2) := by
  unfold StrongCouplingTransferGap.CyclicMatrix.segment
  simp only [Matrix.of_apply]
  fun_prop

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
@[fun_prop] theorem continuous_segment_comp {Y : Type*} [TopologicalSpace Y]
    (K : C(X × X, ℝ)) {n : ℕ} {u : Y → Fin n → X} {y : Y → X}
    (hu : Continuous u) (hy : Continuous y) :
    Continuous (fun z => segment (Matrix.of fun x y => K (x, y)) (u z) (y z)) :=
  (continuous_segment K).comp (hu.prodMk hy)

/-- Integrating the internal variables of a chain gives its kernel power. -/
theorem integral_segment (K : C(X × X, ℝ)) (n : ℕ) (x y : X) :
    (∫ u : Fin n → X, segment (Matrix.of fun x y => K (x, y)) (Fin.cons x u) y
      ∂Measure.pi (fun _ => μ)) = IntegralKernel.kernelPower μ K n (x, y) := by
  induction n generalizing x with
  | zero =>
    have hb (u : Fin 0 → X) :
        segment (Matrix.of fun x y => K (x, y)) (Fin.cons x u) y = K (x, y) := by
      unfold StrongCouplingTransferGap.CyclicMatrix.segment
      rw [Fin.prod_univ_one]
      rfl
    simp only [hb, integral_const, MeasureTheory.probReal_univ, one_smul, IntegralKernel.kernelPower]
  | succ n ih =>
    rw [integral_cons μ _ (show Continuous (fun u : Fin (n + 1) → X =>
      StrongCouplingTransferGap.CyclicMatrix.segment (Matrix.of fun x y => K (x, y)) (Fin.cons x u) y) from
      (continuous_segment K (n := (n + 1) + 1)).comp
        (show Continuous (fun u : Fin (n + 1) → X => (Fin.cons x u, y)) by fun_prop))]
    simp only [segment_cons, ← Fin.cons_snoc_eq_snoc_cons, Fin.cons_zero, Matrix.of_apply]
    simp_rw [integral_const_mul]
    have hi (z : X) : (∫ u : Fin n → X,
        K (z, Fin.snoc (α := fun _ => X) u y 0) * segment (Matrix.of fun x y => K (x, y)) u y
        ∂Measure.pi (fun _ => μ)) = IntegralKernel.kernelPower μ K n (z, y) := by
      simpa only [segment_cons, Matrix.of_apply] using ih z
    simp_rw [hi]
    rfl

/-- Two independently integrated chains give the two-arc cycle integral. -/
theorem integral_two_segments (K : C(X × X, ℝ)) (k n : ℕ) (F : C(X × X, ℝ)) :
    (∫ u : Fin (k + 1) → X, ∫ v : Fin (n + 1) → X,
      F (u 0, v 0) * segment (Matrix.of fun x y => K (x, y)) u (v 0) *
        segment (Matrix.of fun x y => K (x, y)) v (u 0)
      ∂Measure.pi (fun _ => μ) ∂Measure.pi (fun _ => μ)) =
      IntegralKernel.cycleIntegral μ K k n F := by
  rw [integral_cons μ _ (by fun_prop), IntegralKernel.cycleIntegral,
    integral_prod _ (IntegralKernel.integrable_continuous_fun _ (by fun_prop))]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [Fin.cons_zero]
  have hh (u : Fin k → X) :
      (∫ v : Fin (n + 1) → X, F (x, v 0) *
        segment (Matrix.of fun x y => K (x, y)) (Fin.cons x u) (v 0) *
        segment (Matrix.of fun x y => K (x, y)) v x ∂Measure.pi (fun _ => μ)) =
      ∫ y, ∫ v : Fin n → X, F (x, y) *
        segment (Matrix.of fun x y => K (x, y)) (Fin.cons x u) y *
        segment (Matrix.of fun x y => K (x, y)) (Fin.cons y v) x
        ∂Measure.pi (fun _ => μ) ∂μ :=
    integral_cons μ _ (by fun_prop)
  simp_rw [hh]
  rw [integral_integral_swap (IntegralKernel.integrable_continuous_fun _ (by fun_prop))]
  apply integral_congr_ae
  filter_upwards [] with y
  simp_rw [integral_const_mul, integral_segment, integral_mul_const]
  rw [integral_const_mul, integral_segment]

/-- Rejoining two consecutive chains into a periodic time coordinate. -/
def cycleJoinEquiv (k n : ℕ) : ((Fin (k + 1) → X) × (Fin (n + 1) → X)) ≃ᵐ
    (ZMod ((k + 1) + (n + 1)) → X) :=
  (appendEquiv (k + 1) (n + 1)).trans
    (MeasurableEquiv.piCongrLeft (fun _ => X) (residueEquiv ((k + 1) + (n + 1))))

omit [TopologicalSpace X] [CompactSpace X] [BorelSpace X] [SecondCountableTopology X] in
theorem cycleJoin_left (k n : ℕ) (uv : (Fin (k + 1) → X) × (Fin (n + 1) → X))
    (i : Fin (k + 1)) : cycleJoinEquiv k n uv (i.val : ZMod _) = uv.1 i := by
  have h := MeasurableEquiv.piCongrLeft_apply_apply (residueEquiv ((k + 1) + (n + 1)))
    (β := fun _ => X) (appendEquiv (k + 1) (n + 1) uv) (i.castAdd (n + 1))
  exact h.trans (appendEquiv_left _ _ uv i)

omit [TopologicalSpace X] [CompactSpace X] [BorelSpace X] [SecondCountableTopology X] in
theorem cycleJoin_right (k n : ℕ) (uv : (Fin (k + 1) → X) × (Fin (n + 1) → X))
    (i : Fin (n + 1)) : cycleJoinEquiv k n uv ((k + 1 + i.val : ℕ) : ZMod _) = uv.2 i := by
  have h := MeasurableEquiv.piCongrLeft_apply_apply (residueEquiv ((k + 1) + (n + 1)))
    (β := fun _ => X) (appendEquiv (k + 1) (n + 1) uv) (i.natAdd (k + 1))
  exact h.trans (appendEquiv_right _ _ uv i)

omit [CompactSpace X] [BorelSpace X] in
theorem measurePreserving_cycleJoin (k n : ℕ) :
    MeasurePreserving (cycleJoinEquiv (X := X) k n)
      ((Measure.pi fun _ : Fin (k + 1) => μ).prod (Measure.pi fun _ : Fin (n + 1) => μ))
      (Measure.pi fun _ : ZMod ((k + 1) + (n + 1)) => μ) :=
  (measurePreserving_piCongrLeft (fun _ => μ) (residueEquiv ((k + 1) + (n + 1)))).comp
    (measurePreserving_append μ (k + 1) (n + 1))

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
theorem cycle_split (K : C(X × X, ℝ)) (k n : ℕ)
    (U : ZMod ((k + 1) + (n + 1)) → X) :
    (∏ t, K (U t, U (t + 1))) =
      segment (Matrix.of fun x y => K (x, y)) (fun i : Fin (k + 1) => U (i.val : ZMod _)) (U (k + 1)) *
      segment (Matrix.of fun x y => K (x, y))
        (fun i : Fin (n + 1) => U ((k + 1 + i.val : ℕ) : ZMod _)) (U 0) := by
  rw [← Equiv.prod_comp (residueEquiv ((k + 1) + (n + 1))), Fin.prod_univ_add]
  have h₁ := segment_sample (Matrix.of fun x y => K (x, y)) (n := k + 1) U 0
  have h₂ := segment_sample (Matrix.of fun x y => K (x, y)) (n := n + 1) U (k + 1)
  simp only [Nat.zero_add] at h₁
  simp only [ZMod.natCast_self] at h₂
  simp only [Nat.cast_add, Nat.cast_one, Matrix.of_apply] at h₁ h₂
  simp only [residueEquiv, Equiv.coe_fn_mk, Fin.val_castAdd, Fin.val_natAdd,
    Nat.cast_add, Nat.cast_one]
  rw [h₁, h₂]

omit [CompactSpace X] [BorelSpace X] [SecondCountableTopology X] in
theorem cycleJoin_weight (K : C(X × X, ℝ)) (k n : ℕ)
    (uv : (Fin (k + 1) → X) × (Fin (n + 1) → X)) :
    (∏ t, K (cycleJoinEquiv k n uv t, cycleJoinEquiv k n uv (t + 1))) =
      segment (Matrix.of fun x y => K (x, y)) uv.1 (uv.2 0) *
      segment (Matrix.of fun x y => K (x, y)) uv.2 (uv.1 0) := by
  have h0 : cycleJoinEquiv k n uv 0 = uv.1 0 := cycleJoin_left k n uv 0
  have hk : cycleJoinEquiv k n uv (k + 1) = uv.2 0 := by
    simpa only [Fin.val_zero, add_zero, Nat.cast_add, Nat.cast_one] using cycleJoin_right k n uv 0
  rw [cycle_split, hk, h0]
  congr 1
  · congr 1
    funext i
    exact cycleJoin_left k n uv i
  · congr 1
    funext i
    exact cycleJoin_right k n uv i

/-- Exact finite-volume identification of the cyclic product integral with two kernel powers. -/
theorem integral_cycle (K : C(X × X, ℝ)) (k n : ℕ) (F : C(X × X, ℝ)) :
    (∫ U : ZMod ((k + 1) + (n + 1)) → X,
      F (U 0, U (k + 1)) * ∏ t, K (U t, U (t + 1)) ∂Measure.pi (fun _ => μ)) =
      IntegralKernel.cycleIntegral μ K k n F := by
  rw [← (measurePreserving_cycleJoin μ k n).integral_comp'
    (fun U => F (U 0, U (k + 1)) * ∏ t, K (U t, U (t + 1)))]
  have he (uv : (Fin (k + 1) → X) × (Fin (n + 1) → X)) :
      F (cycleJoinEquiv k n uv 0, cycleJoinEquiv k n uv (k + 1)) *
        (∏ t, K (cycleJoinEquiv k n uv t, cycleJoinEquiv k n uv (t + 1))) =
      F (uv.1 0, uv.2 0) * segment (Matrix.of fun x y => K (x, y)) uv.1 (uv.2 0) *
        segment (Matrix.of fun x y => K (x, y)) uv.2 (uv.1 0) := by
    have h0 : cycleJoinEquiv k n uv 0 = uv.1 0 := cycleJoin_left k n uv 0
    have hk : cycleJoinEquiv k n uv (k + 1) = uv.2 0 := by
      simpa only [Fin.val_zero, add_zero, Nat.cast_add, Nat.cast_one] using cycleJoin_right k n uv 0
    rw [h0, hk, cycleJoin_weight]
    ring
  simp_rw [he]
  rw [integral_prod _ (IntegralKernel.integrable_continuous_fun _ (by fun_prop))]
  exact integral_two_segments μ K k n F

theorem integral_cycle_length (K : C(X × X, ℝ)) {N : ℕ} [NeZero N] (k n : ℕ)
    (hN : N = (k + 1) + (n + 1)) (F : C(X × X, ℝ)) :
    (∫ U : ZMod N → X, F (U 0, U (k + 1)) * ∏ t, K (U t, U (t + 1))
      ∂Measure.pi (fun _ => μ)) = IntegralKernel.cycleIntegral μ K k n F := by
  subst N
  exact integral_cycle μ K k n F

end FiniteProduct

end ProductMeasure

namespace WilsonCompact

open StrongCouplingTransferGap.WilsonFinite
open StrongCouplingTwist (holonomy)

variable {E : Type*} [Group E] [TopologicalSpace E] [IsTopologicalGroup E]
  [CompactSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (ν₀ : Measure E) [IsProbabilityMeasure ν₀] {d L : ℕ}

/-- Product reference measure on the spatial links of one slice. -/
def sliceMeasure (d L : ℕ) : Measure (State E d L) :=
  Measure.pi (fun _ => ν₀)

instance sliceMeasure_probability (d L : ℕ) : IsProbabilityMeasure (sliceMeasure ν₀ d L) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : StrongCouplingCrossing.Link d L => ν₀)))

/-- Jointly continuous one-step Boltzmann factor before temporal links are integrated out. -/
def edgeMap (ψ : E → ℝ) (hψ : Continuous ψ) (β : ℝ) :
    C((State E d L × State E d L) × Temporal E d L, ℝ) :=
  ⟨fun p => edgeWeight ψ β p.1.1 p.1.2 p.2, by
    unfold edgeWeight spatialAction temporalAction holonomy
    fun_prop⟩

/-- Wilson transfer kernel with the temporal links integrated against the reference law. -/
def kernel (ψ : E → ℝ) (hψ : Continuous ψ) (β : ℝ) : C(State E d L × State E d L, ℝ) :=
  ProductMeasure.partialIntegral (Measure.pi fun _ => ν₀) (edgeMap ψ hψ β)

theorem kernel_symmetric (ψ : E → ℝ) (hψ : Continuous ψ) (β : ℝ)
    (hclass : ∀ g h, ψ (g * h * g⁻¹) = ψ h) (hinv : ∀ g, ψ g⁻¹ = ψ g)
    (hν : ν₀.map Inv.inv = ν₀) (U V : State E d L) :
    kernel ν₀ ψ hψ β (U, V) = kernel ν₀ ψ hψ β (V, U) := by
  have hv : MeasurePreserving (fun (h : Temporal E d L) x => (h x)⁻¹)
      (Measure.pi fun _ => ν₀) (Measure.pi fun _ => ν₀) :=
    measurePreserving_pi (fun _ => ν₀) (fun _ => ν₀) (fun _ => ⟨measurable_inv, hν⟩)
  have hi := hv.integral_comp (MeasurableEquiv.inv (Temporal E d L)).measurableEmbedding
    (fun h => edgeWeight ψ β V U h)
  change (∫ h, edgeWeight ψ β U V h ∂Measure.pi fun _ => ν₀) =
    (∫ h, edgeWeight ψ β V U h ∂Measure.pi fun _ => ν₀)
  simpa only [Function.comp_def, edgeWeight_inv ψ β hclass hinv] using hi

/-- Compactness of the configuration space makes strict positivity uniform at
each fixed spatial volume and coupling. -/
theorem kernel_uniformly_positive (ψ : E → ℝ) (hψ : Continuous ψ) (β : ℝ) :
    ∃ a : ℝ, 0 < a ∧ ∀ U V : State E d L, a ≤ kernel ν₀ ψ hψ β (U, V) := by
  obtain ⟨p, _, hp⟩ := isCompact_univ.exists_isMinOn
    (Set.univ_nonempty : (Set.univ : Set ((State E d L × State E d L) × Temporal E d L)).Nonempty)
    (edgeMap (d := d) (L := L) ψ hψ β).continuous.continuousOn
  refine ⟨edgeMap ψ hψ β p, Real.exp_pos _, fun U V => ?_⟩
  change edgeMap ψ hψ β p ≤ ∫ h, edgeWeight ψ β U V h ∂Measure.pi (fun _ => ν₀)
  calc
    _ = ∫ _ : Temporal E d L, edgeMap ψ hψ β p ∂Measure.pi (fun _ => ν₀) := by simp
    _ ≤ _ := integral_mono (integrable_const _)
      (IntegralKernel.integrable_continuous_fun _
        ((edgeMap ψ hψ β).continuous.comp (continuous_const.prodMk continuous_id)))
      (fun h => hp (Set.mem_univ ((U, V), h)))

/-- The real Hilbert-space Wilson transfer operator. -/
def transfer (ψ : E → ℝ) (hψ : Continuous ψ) (β : ℝ) :
    IntegralKernel.Hilbert (sliceMeasure ν₀ d L) →L[ℝ]
      IntegralKernel.Hilbert (sliceMeasure ν₀ d L) :=
  IntegralKernel.operator (sliceMeasure ν₀ d L) (kernel ν₀ ψ hψ β)

theorem compact_transfer (ψ : E → ℝ) (hψ : Continuous ψ) (β : ℝ) :
    IsCompactOperator (transfer (d := d) (L := L) ν₀ ψ hψ β) :=
  IntegralKernel.compact_operator _ _

theorem symmetric_transfer (ψ : E → ℝ) (hψ : Continuous ψ) (β : ℝ)
    (hclass : ∀ g h, ψ (g * h * g⁻¹) = ψ h) (hinv : ∀ g, ψ g⁻¹ = ψ g)
    (hν : ν₀.map Inv.inv = ν₀) :
    (transfer (d := d) (L := L) ν₀ ψ hψ β).IsSymmetric :=
  IntegralKernel.symmetric_operator _ _ (kernel_symmetric ν₀ ψ hψ β hclass hinv hν)

theorem selfAdjoint_transfer (ψ : E → ℝ) (hψ : Continuous ψ) (β : ℝ)
    (hclass : ∀ g h, ψ (g * h * g⁻¹) = ψ h) (hinv : ∀ g, ψ g⁻¹ = ψ g)
    (hν : ν₀.map Inv.inv = ν₀) :
    IsSelfAdjoint (transfer (d := d) (L := L) ν₀ ψ hψ β) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    (symmetric_transfer ν₀ ψ hψ β hclass hinv hν)

def linkCoordinates (d T L : ℕ) :
    (ZMod (T + 3) × StrongCouplingCrossing.Link d L) ⊕
      (ZMod (T + 3) × StrongCouplingCrossing.Site d L) ≃
        StrongCouplingTransferGap.Rectangular.Link d T L where
  toFun := fun l => match l with
    | .inl (t, x, i) => ((t, x), i.succ)
    | .inr (t, x) => ((t, x), 0)
  invFun := fun l => Fin.cases (.inr l.1) (fun i => .inl (l.1.1, l.1.2, i)) l.2
  left_inv := by rintro (⟨t, x, i⟩ | ⟨t, x⟩) <;> rfl
  right_inv := by rintro ⟨⟨t, x⟩, i⟩; cases i using Fin.cases <;> rfl

/-- Spatial and temporal time slices give a measurable parametrization of all links. -/
def assembleEquiv (d T L : ℕ) :
    ((ZMod (T + 3) → State E d L) × (ZMod (T + 3) → Temporal E d L)) ≃ᵐ
      (StrongCouplingTransferGap.Rectangular.Link d T L → E) :=
  (((MeasurableEquiv.curry (ZMod (T + 3)) (StrongCouplingCrossing.Link d L) E).symm.prodCongr
      (MeasurableEquiv.curry (ZMod (T + 3)) (StrongCouplingCrossing.Site d L) E).symm).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ => E)).symm).trans
      (MeasurableEquiv.piCongrLeft (fun _ => E) (linkCoordinates d T L))

omit [Group E] [TopologicalSpace E] [IsTopologicalGroup E] [CompactSpace E]
    [BorelSpace E] [SecondCountableTopology E] in
theorem assembleEquiv_apply {T : ℕ}
    (Uh : (ZMod (T + 3) → State E d L) × (ZMod (T + 3) → Temporal E d L)) :
    assembleEquiv d T L Uh = assemble Uh.1 Uh.2 := by
  ext l
  rcases l with ⟨⟨t, x⟩, i⟩
  cases i using Fin.cases with
  | zero =>
    exact MeasurableEquiv.piCongrLeft_apply_apply (linkCoordinates d T L) (β := fun _ => E)
      ((MeasurableEquiv.sumPiEquivProdPi (fun _ => E)).symm
        (Function.uncurry Uh.1, Function.uncurry Uh.2)) (.inr (t, x))
  | succ i =>
    exact MeasurableEquiv.piCongrLeft_apply_apply (linkCoordinates d T L) (β := fun _ => E)
      ((MeasurableEquiv.sumPiEquivProdPi (fun _ => E)).symm
        (Function.uncurry Uh.1, Function.uncurry Uh.2)) (.inl (t, x, i))

omit [Group E] [IsTopologicalGroup E] [CompactSpace E] [BorelSpace E] in
theorem measurePreserving_assemble (d T L : ℕ) :
    MeasurePreserving (assembleEquiv (E := E) d T L)
      ((Measure.pi fun _ : ZMod (T + 3) => sliceMeasure ν₀ d L).prod
        (Measure.pi fun _ : ZMod (T + 3) => Measure.pi fun _ : StrongCouplingCrossing.Site d L => ν₀))
      (Measure.pi fun _ : StrongCouplingTransferGap.Rectangular.Link d T L => ν₀) :=
  (measurePreserving_piCongrLeft (fun _ => ν₀) (linkCoordinates d T L)).comp
    ((measurePreserving_sumPiEquivProdPi_symm (fun _ => ν₀)).comp
      ((ProductMeasure.measurePreserving_uncurry ν₀).prod (ProductMeasure.measurePreserving_uncurry ν₀)))

omit [Group E] [IsTopologicalGroup E] [CompactSpace E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] in
theorem continuous_assemble {T : ℕ} :
    Continuous (fun Uh : (ZMod (T + 3) → State E d L) × (ZMod (T + 3) → Temporal E d L) =>
      assemble Uh.1 Uh.2) := by
  apply continuous_pi
  rintro ⟨⟨t, x⟩, i⟩
  cases i using Fin.cases with
  | zero =>
    change Continuous (fun Uh : (ZMod (T + 3) → State E d L) × (ZMod (T + 3) → Temporal E d L) => Uh.2 t x)
    fun_prop
  | succ i =>
    change Continuous (fun Uh : (ZMod (T + 3) → State E d L) × (ZMod (T + 3) → Temporal E d L) => Uh.1 t (x, i))
    fun_prop

theorem integral_temporal_weights {T : ℕ} (ψ : E → ℝ) (hψ : Continuous ψ) (β : ℝ)
    (U : ZMod (T + 3) → State E d L) :
    (∫ h : ZMod (T + 3) → Temporal E d L, ∏ t, edgeWeight ψ β (U t) (U (t + 1)) (h t)
      ∂Measure.pi (fun _ => Measure.pi (fun _ => ν₀))) =
        ∏ t, kernel ν₀ ψ hψ β (U t, U (t + 1)) :=
  integral_fintype_prod_eq_prod _

/-- Exact integration of temporal links converts the Wilson law into a cyclic
product of transfer kernels. -/
theorem integral_wilson_eq_cycle {T : ℕ} (ψ : E → ℝ) (hψ : Continuous ψ) (β : ℝ)
    (F : C(ZMod (T + 3) → State E d L, ℝ)) :
    (∫ ω : StrongCouplingTransferGap.Rectangular.Link d T L → E,
      (F (fun t => StrongCouplingTransferGap.Rectangular.sliceConfiguration t ω) : ℂ) *
        StrongCouplingTransferGap.Rectangular.wilsonDensity (d := d) (v := (T, L)) (ψ ∘ holonomy) β ω
      ∂Measure.pi (fun _ => ν₀)) =
      ((∫ U : ZMod (T + 3) → State E d L,
        F U * ∏ t, kernel ν₀ ψ hψ β (U t, U (t + 1))
        ∂Measure.pi (fun _ => sliceMeasure ν₀ d L) : ℝ) : ℂ) := by
  let : BorelSpace (State E d L) := inferInstance
  let : BorelSpace (Temporal E d L) := inferInstance
  let : BorelSpace (ZMod (T + 3) → State E d L) := inferInstance
  let : BorelSpace (ZMod (T + 3) → Temporal E d L) := inferInstance
  rw [← (measurePreserving_assemble ν₀ d T L).integral_comp']
  simp only [assembleEquiv_apply]
  change (∫ Uh : (ZMod (T + 3) → State E d L) × (ZMod (T + 3) → Temporal E d L),
    (F Uh.1 : ℂ) * StrongCouplingTransferGap.Rectangular.wilsonDensity (d := d) (v := (T, L)) (ψ ∘ holonomy) β
      (assemble Uh.1 Uh.2)
    ∂(Measure.pi (fun _ => sliceMeasure ν₀ d L)).prod
      (Measure.pi (fun _ => Measure.pi (fun _ => ν₀)))) = _
  simp_rw [density_assemble, ← Complex.ofReal_mul]
  rw [integral_complex_ofReal]
  apply congrArg Complex.ofReal
  have hc : Continuous (fun Uh : (ZMod (T + 3) → State E d L) × (ZMod (T + 3) → Temporal E d L) =>
      F Uh.1 * ∏ t, edgeWeight ψ β (Uh.1 t) (Uh.1 (t + 1)) (Uh.2 t)) := by
    change Continuous (fun Uh : (ZMod (T + 3) → State E d L) × (ZMod (T + 3) → Temporal E d L) =>
      F Uh.1 * ∏ t, edgeMap (d := d) (L := L) ψ hψ β ((Uh.1 t, Uh.1 (t + 1)), Uh.2 t))
    fun_prop
  rw [integral_prod _ (IntegralKernel.integrable_continuous_fun _ hc)]
  simp_rw [integral_const_mul, integral_temporal_weights ν₀ ψ hψ β]

theorem wilsonExpectation_eq_cycle {T : ℕ} (ψ : E → ℝ) (hψ : Continuous ψ) (β : ℝ)
    (F : C(ZMod (T + 3) → State E d L, ℝ)) :
    StrongCouplingTransferGap.Rectangular.wilsonExpectation (v := (T, L)) ν₀ (ψ ∘ holonomy) β
      (fun ω => (F (fun t => StrongCouplingTransferGap.Rectangular.sliceConfiguration t ω) : ℂ)) =
      (((∫ U, F U * ∏ t, kernel ν₀ ψ hψ β (U t, U (t + 1))
          ∂Measure.pi (fun _ => sliceMeasure ν₀ d L)) /
        (∫ U : ZMod (T + 3) → State E d L, ∏ t, kernel ν₀ ψ hψ β (U t, U (t + 1))
          ∂Measure.pi (fun _ => sliceMeasure ν₀ d L)) : ℝ) : ℂ) := by
  unfold StrongCouplingTransferGap.Rectangular.wilsonExpectation
  rw [integral_wilson_eq_cycle ν₀ ψ hψ β F]
  have hz := integral_wilson_eq_cycle (d := d) (L := L) (T := T) ν₀ ψ hψ β 1
  simp only [ContinuousMap.one_apply, Complex.ofReal_one, one_mul] at hz
  rw [hz, Complex.ofReal_div]

theorem wilsonExpectation_eq_two_arcs {T : ℕ} (ψ : E → ℝ) (hψ : Continuous ψ) (β : ℝ)
    (k n : ℕ) (hT : T + 3 = (k + 1) + (n + 1)) (F : C(State E d L × State E d L, ℝ)) :
    StrongCouplingTransferGap.Rectangular.wilsonExpectation (v := (T, L)) ν₀ (ψ ∘ holonomy) β
      (fun ω => (F (StrongCouplingTransferGap.Rectangular.sliceConfiguration 0 ω,
        StrongCouplingTransferGap.Rectangular.sliceConfiguration (k + 1) ω) : ℂ)) =
      (IntegralKernel.cycleExpectation (sliceMeasure ν₀ d L) (kernel ν₀ ψ hψ β) k n F : ℂ) := by
  let G : C(ZMod (T + 3) → State E d L, ℝ) := ⟨fun U => F (U 0, U (k + 1)), by fun_prop⟩
  change StrongCouplingTransferGap.Rectangular.wilsonExpectation (v := (T, L)) ν₀ (ψ ∘ holonomy) β
    (fun ω => (G (fun t => StrongCouplingTransferGap.Rectangular.sliceConfiguration t ω) : ℂ)) = _
  rw [wilsonExpectation_eq_cycle ν₀ ψ hψ β G]
  change (((∫ U : ZMod (T + 3) → State E d L,
    F (U 0, U (k + 1)) * ∏ t, kernel ν₀ ψ hψ β (U t, U (t + 1))
    ∂Measure.pi (fun _ => sliceMeasure ν₀ d L)) /
    (∫ U : ZMod (T + 3) → State E d L, ∏ t, kernel ν₀ ψ hψ β (U t, U (t + 1))
      ∂Measure.pi (fun _ => sliceMeasure ν₀ d L)) : ℝ) : ℂ) = _
  rw [ProductMeasure.integral_cycle_length _ _ k n hT F]
  have hz := ProductMeasure.integral_cycle_length (sliceMeasure ν₀ d L) (kernel ν₀ ψ hψ β) k n hT 1
  simp only [ContinuousMap.one_apply, one_mul] at hz
  rw [hz]
  rfl

/-- SC7 clustering expressed directly in terms of the compact transfer kernel.
The rate is independent of the spatial extent; the prefactor need not be. -/
theorem cycle_clustering (d : ℕ) (ψ : E → ℝ) (hψ : Continuous ψ)
    (hψ0 : ∀ g, 0 ≤ ψ g) (hψ2 : ∀ g, ψ g ≤ 2)
    {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ StrongCouplingTransferGap.Rectangular.beta0 d) :
    ∃ κ > 0, ∀ (L : ℕ) (F : C(State E d L, ℝ)), ∃ C : ℝ, ∀ k : ℕ, ∀ᶠ n in atTop,
      |IntegralKernel.cycleCovariance (sliceMeasure ν₀ d L) (kernel ν₀ ψ hψ β) k n F| ≤
        C * Real.exp (-κ * (k + 1)) := by
  have hφ : Measurable (ψ ∘ holonomy) := by
    apply Continuous.measurable
    unfold holonomy
    fun_prop
  obtain ⟨κ, hκ, hc⟩ := StrongCouplingTransferGap.Rectangular.slice_clustering d ν₀ (1 : E)
    hφ (fun v => hψ0 _) (fun v => hψ2 _) hβ hβ0
  refine ⟨κ, hκ, fun L F => ⟨3 * ‖F‖ * ‖F‖ * Real.exp (6 * ((L + 3) ^ d * (d + 1) : ℕ)), ?_⟩⟩
  intro k
  filter_upwards [eventually_ge_atTop (k + 1)] with n hn
  let T := k + n - 1
  have hT : T + 3 = (k + 1) + (n + 1) := by dsimp [T]; omega
  have hsep : 2 * (k + 1) ≤ T + 3 := by omega
  have hFm : Measurable (fun U => (F U : ℂ)) := Complex.continuous_ofReal.comp F.continuous |>.measurable
  have hFb : ∀ U, ‖(F U : ℂ)‖ ≤ ‖F‖ := fun U => by simpa using F.norm_coe_le_norm U
  have hb := hc T L (k + 1) hsep (fun U => (F U : ℂ)) (fun U => (F U : ℂ)) ‖F‖ ‖F‖
    hFm hFm hFb hFb
  simp only [Nat.cast_add, Nat.cast_one] at hb
  have hp := wilsonExpectation_eq_two_arcs ν₀ ψ hψ β k n hT (IntegralKernel.endpointProduct F F)
  have hl := wilsonExpectation_eq_two_arcs ν₀ ψ hψ β k n hT (IntegralKernel.endpointProduct F 1)
  have hr := wilsonExpectation_eq_two_arcs ν₀ ψ hψ β k n hT (IntegralKernel.endpointProduct 1 F)
  simp only [IntegralKernel.endpointProduct, ContinuousMap.coe_mk, ContinuousMap.one_apply,
    mul_one, one_mul, Complex.ofReal_mul] at hp hl hr
  rw [hp, hl, hr, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real] at hb
  simpa only [IntegralKernel.cycleCovariance, IntegralKernel.endpointProduct, ContinuousMap.one_apply,
    mul_one, one_mul, Real.norm_eq_abs, Nat.cast_add, Nat.cast_one] using hb

/-- A simple positive leading eigenvalue and an absolute spectral gap at strong
coupling, uniformly in the spatial volume. The spatial torus has dimension `d`
and side `L + 3`; Euclidean time is the additional lattice direction. -/
theorem uniform_transfer_gap (d : ℕ) (ψ : E → ℝ) (hψ : Continuous ψ)
    (hclass : ∀ g h, ψ (g * h * g⁻¹) = ψ h) (hinv : ∀ g, ψ g⁻¹ = ψ g)
    (hν : ν₀.map Inv.inv = ν₀) (hψ0 : ∀ g, 0 ≤ ψ g) (hψ2 : ∀ g, ψ g ≤ 2)
    {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ StrongCouplingTransferGap.Rectangular.beta0 d) :
    ∃ κ > 0, ∀ L : ℕ, ∃ (r : ℝ) (u : C(State E d L, ℝ)),
      0 < r ∧ (∀ U, 0 < u U) ∧ ‖ContinuousMap.toLp 2 (sliceMeasure ν₀ d L) ℝ u‖ = 1 ∧
      transfer ν₀ ψ hψ β (ContinuousMap.toLp 2 (sliceMeasure ν₀ d L) ℝ u) =
        r • ContinuousMap.toLp 2 (sliceMeasure ν₀ d L) ℝ u ∧
      (∀ v : IntegralKernel.Hilbert (sliceMeasure ν₀ d L), transfer ν₀ ψ hψ β v = r • v →
        ∃ c : ℝ, v = c • ContinuousMap.toLp 2 (sliceMeasure ν₀ d L) ℝ u) ∧
      (∀ e ∈ spectrum ℝ (transfer (d := d) (L := L) ν₀ ψ hψ β),
        e = r ∨ |e| ≤ Real.exp (-κ) * r) := by
  obtain ⟨κ, hκ, hc⟩ := cycle_clustering ν₀ d ψ hψ hψ0 hψ2 hβ hβ0
  refine ⟨κ, hκ, fun L => ?_⟩
  obtain ⟨a, ha, hK⟩ := kernel_uniformly_positive (d := d) (L := L) ν₀ ψ hψ β
  exact IntegralKernel.spectral_gap_of_cycle_clustering (sliceMeasure ν₀ d L) (kernel ν₀ ψ hψ β)
    (kernel_symmetric ν₀ ψ hψ β hclass hinv hν) ha hK (hc L)

omit [CompactSpace E] in
/-- A left-invariant probability law is inversion invariant. In particular,
normalized Haar probability satisfies the reference-measure hypothesis. -/
theorem map_inv_eq_of_leftInvariant [Measure.IsMulLeftInvariant ν₀] :
    ν₀.map Inv.inv = ν₀ := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf measurable_inv]
  have hy (y : E) : (∫⁻ x, f (x⁻¹ * y) ∂ν₀) = ∫⁻ x, f x⁻¹ ∂ν₀ := by
    have h := lintegral_mul_left_eq_self (μ := ν₀) (fun x => f (x⁻¹ * y)) y
    simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one] using h.symm
  have hx (x : E) : (∫⁻ y, f (x⁻¹ * y) ∂ν₀) = ∫⁻ y, f y ∂ν₀ :=
    lintegral_mul_left_eq_self f x⁻¹
  have hswap := lintegral_lintegral_swap (μ := ν₀) (ν := ν₀)
    (f := fun x y => f (x⁻¹ * y)) (hf.comp (measurable_fst.inv.mul measurable_snd)).aemeasurable
  simp only [hx, hy, lintegral_const, measure_univ, mul_one] at hswap
  exact hswap.symm

/-- The volume-uniform compact-group gap for normalized Haar reference measure,
stated using only its probability and left-invariance properties. -/
theorem uniform_transfer_gap_of_leftInvariant [Measure.IsMulLeftInvariant ν₀]
    (d : ℕ) (ψ : E → ℝ) (hψ : Continuous ψ)
    (hclass : ∀ g h, ψ (g * h * g⁻¹) = ψ h) (hinv : ∀ g, ψ g⁻¹ = ψ g)
    (hψ0 : ∀ g, 0 ≤ ψ g) (hψ2 : ∀ g, ψ g ≤ 2)
    {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ StrongCouplingTransferGap.Rectangular.beta0 d) :
    ∃ κ > 0, ∀ L : ℕ, ∃ (r : ℝ) (u : C(State E d L, ℝ)),
      0 < r ∧ (∀ U, 0 < u U) ∧ ‖ContinuousMap.toLp 2 (sliceMeasure ν₀ d L) ℝ u‖ = 1 ∧
      transfer ν₀ ψ hψ β (ContinuousMap.toLp 2 (sliceMeasure ν₀ d L) ℝ u) =
        r • ContinuousMap.toLp 2 (sliceMeasure ν₀ d L) ℝ u ∧
      (∀ v : IntegralKernel.Hilbert (sliceMeasure ν₀ d L), transfer ν₀ ψ hψ β v = r • v →
        ∃ c : ℝ, v = c • ContinuousMap.toLp 2 (sliceMeasure ν₀ d L) ℝ u) ∧
      (∀ e ∈ spectrum ℝ (transfer (d := d) (L := L) ν₀ ψ hψ β),
        e = r ∨ |e| ≤ Real.exp (-κ) * r) :=
  uniform_transfer_gap ν₀ d ψ hψ hclass hinv (map_inv_eq_of_leftInvariant ν₀) hψ0 hψ2 hβ hβ0

end WilsonCompact

#print axioms IntegralKernel.compact_operator
#print axioms IntegralKernel.positive_kernel_spectral_gap
#print axioms IntegralKernel.spectral_gap_of_cycle_clustering
#print axioms ProductMeasure.integral_cycle
#print axioms WilsonCompact.compact_transfer
#print axioms WilsonCompact.selfAdjoint_transfer
#print axioms WilsonCompact.wilsonExpectation_eq_two_arcs
#print axioms WilsonCompact.uniform_transfer_gap
#print axioms WilsonCompact.uniform_transfer_gap_of_leftInvariant

end Mettapedia.QuantumTheory.YangMills.CompactTransferGap
