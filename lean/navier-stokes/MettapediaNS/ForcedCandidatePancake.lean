import MettapediaNS.ForcedPathEnergy
import NavierStokes.R3.ProblemStatement
import Euler.CompactSmoothTimeField
import Euler.MeanCutoffDifferenceBound
import NavierStokes.ComparatorBridge

/-!
# Forced singularities violate uniform middle-eigenvalue budgets

OpenAI's Theorem 1.1 constructs smooth solutions of the forced Navier–Stokes equations on
`ℝ³` that break down at time one. This module shows that no family of nonnegative continuous
majorants of their middle strain eigenvalue has uniformly bounded time integrals on the
compact slabs exhausting `[1/2, 1)`.

On every slab `[a, b] ⊂ (0, 1)` the candidate is a forced path of smooth `L²` fields: its
slices are smooth with a common compact support, so their jets are continuous in time in the
uniform norm (OpenAI's `SmoothTimeField`), hence in `L²`. A majorant of the middle
eigenvalue then bounds the gradient energy, the gradient energy bounds the order-two energy,
and these energies bound the velocity through the whole-space `H²` embedding. That contradicts the
unbounded speed at time one.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ForcedCandidatePancake

open Set Filter MeasureTheory InnerProductSpace EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerMeanSolenoidal
open scoped ContDiff Topology Laplacian

/-! ## Compactly supported smooth fields -/

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A smooth compactly supported field is a smooth `L²` field. -/
def compactField (g : Space → V) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    SmoothL2Field V where
  field := g
  smooth := hg
  integrable n := (hg.continuous_iteratedFDeriv (by simp)).memLp_of_hasCompactSupport
    (hc.iteratedFDeriv n)

@[simp] theorem compactField_field (g : Space → V) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) : (compactField g hg hc).field = g := rfl

/-- **Uniformly continuous jets with a common compact support are continuous in `L²`.** -/
theorem continuous_jetLp_of_timeField {s : Type} [TopologicalSpace s] [CompactSpace s]
    (A : SmoothTimeField s Space V) (K : Set Space) (hK : IsCompact K)
    (hsupp : ∀ t, tsupport (A.field t : Space → V) ⊆ K)
    (F : s → SmoothL2Field V) (hF : ∀ t, (F t).field = A.field t) (n : ℕ) :
    Continuous (fun t ↦ (F t).jetLp n) := by
  have hvol : volume K ≠ ⊤ := hK.measure_lt_top.ne
  set c : ℝ := (volume K).toReal ^ (1 / (2 : ENNReal).toReal) with hcdef
  have hc : 0 ≤ c := by positivity
  have hdist (t t' : s) :
      dist ((F t).jetLp n) ((F t').jetLp n) ≤ dist (A.jet n t) (A.jet n t') * c := by
    rw [dist_eq_norm, jetLp, jetLp, ← MemLp.toLp_sub, Lp.norm_toLp,
      toReal_eLpNorm (((F t).integrable n).sub ((F t').integrable n)).1]
    refine EulerMeanBoundary.lpNorm_le_bound_volume _
      (((F t).integrable n).sub ((F t').integrable n)).1 K hvol _ dist_nonneg ?_ ?_ 2
    · intro x
      rw [Pi.sub_apply, hF, hF, ← A.jet_eq, ← A.jet_eq, ← dist_eq_norm]
      exact BoundedContinuousFunction.dist_coe_le_dist x
    · intro x hx
      have h1 : x ∉ tsupport (iteratedFDeriv ℝ n (F t).field) := fun h ↦
        hx (((tsupport_iteratedFDeriv_subset n).trans (by rw [hF]; exact hsupp t)) h)
      have h2 : x ∉ tsupport (iteratedFDeriv ℝ n (F t').field) := fun h ↦
        hx (((tsupport_iteratedFDeriv_subset n).trans (by rw [hF]; exact hsupp t')) h)
      rw [Pi.sub_apply, image_eq_zero_of_notMem_tsupport h1,
        image_eq_zero_of_notMem_tsupport h2, sub_zero]
  refine continuous_iff_continuousAt.mpr fun t ↦ Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  have hJ : ∀ᶠ t' in 𝓝 t, dist (A.jet n t') (A.jet n t) < ε / (c + 1) :=
    Metric.tendsto_nhds.mp ((A.jet n).continuous.tendsto t) _ (by positivity)
  filter_upwards [hJ] with t' ht'
  calc dist ((F t').jetLp n) ((F t).jetLp n) ≤ dist (A.jet n t') (A.jet n t) * c := hdist t' t
    _ ≤ ε / (c + 1) * c := mul_le_mul_of_nonneg_right ht'.le hc
    _ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith

theorem continuous_jetLp_of_compact_family (s : Set ℝ) [CompactSpace s]
    (u : ℝ × Space → V) (hu : ContDiffOn ℝ ∞ u (s ×ˢ univ))
    (K : Set Space) (hK : IsCompact K)
    (hsupp : ∀ t ∈ s, tsupport (fun x ↦ u (t, x)) ⊆ K)
    (F : s → SmoothL2Field V) (hF : ∀ t, (F t).field = fun x ↦ u (t, x)) (n : ℕ) :
    Continuous (fun t ↦ (F t).jetLp n) := by
  let A := SmoothTimeField.ofContDiffOnCompactSupport s u hu K hK hsupp
  exact continuous_jetLp_of_timeField A K hK (fun t ↦ hsupp t t.property) F hF n

open NavierStokesR3.ProblemStatement hiding Space

/-- The ordinary spatial slice of a candidate is smooth at every interior time. -/
theorem slice_smooth (g : ℝ × Space → V) (hg : ContDiffOn ℝ ∞ g preSingularDomain)
    (t : Ioo (0 : ℝ) 1) : ContDiff ℝ ∞ (fun x ↦ g (t, x)) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  exact (NavierStokes.ProblemStatement.smooth_at_interior hg t.property x).comp x
    (contDiffAt_const.prodMk contDiffAt_id)

/-- A spatially compact candidate slice, carrying its actual derivatives in `L²`. -/
def sliceField (g : ℝ × Space → V) (hg : ContDiffOn ℝ ∞ g preSingularDomain)
    (K : Set Space) (hK : IsCompact K)
    (hsupp : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x ↦ g (t, x)) ⊆ K)
    (t : Ioo (0 : ℝ) 1) : SmoothL2Field V :=
  compactField _ (slice_smooth g hg t)
    (hK.of_isClosed_subset (isClosed_tsupport _) (hsupp t ⟨t.property.1.le, t.property.2⟩))

@[simp] theorem sliceField_field (g : ℝ × Space → V)
    (hg : ContDiffOn ℝ ∞ g preSingularDomain) (K : Set Space) (hK : IsCompact K)
    (hsupp : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x ↦ g (t, x)) ⊆ K)
    (t : Ioo (0 : ℝ) 1) (x : Space) :
    (sliceField g hg K hK hsupp t).field x = g (t, x) := rfl

/-- Shifted interior slabs retain continuity of every actual spatial `L²` jet. -/
theorem sliceField_continuous (g : ℝ × Space → V)
    (hg : ContDiffOn ℝ ∞ g preSingularDomain) (K : Set Space) (hK : IsCompact K)
    (hsupp : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x ↦ g (t, x)) ⊆ K)
    (a T : ℝ) (ha : 0 < a) (hTa : a + T < 1) (n : ℕ) :
    Continuous (fun t : Icc (0 : ℝ) T ↦
      (sliceField g hg K hK hsupp
        ⟨a + t, by constructor <;> linarith [t.property.1, t.property.2]⟩).jetLp n) := by
  apply continuous_jetLp_of_compact_family (Icc 0 T) (fun z ↦ g (a + z.1, z.2))
    ?_ K hK ?_ _ (fun _ ↦ rfl) n
  · exact hg.comp ((contDiffOn_const.add contDiffOn_fst).prodMk contDiffOn_snd)
      (fun z hz ↦ ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, mem_univ _⟩)
  · intro t ht
    exact hsupp (a + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩

omit [NormedSpace ℝ V] in
/-- A compact spacetime support supplies a common compact spatial support for all slices. -/
theorem slice_support_subset (g : ℝ × Space → V) (hg : HasCompactSupport g) (t : ℝ) :
    tsupport (fun x ↦ g (t, x)) ⊆ Prod.snd '' tsupport g := by
  apply closure_minimal ?_ (hg.image continuous_snd).isClosed
  intro x hx
  exact ⟨(t, x), subset_closure hx, rfl⟩

/-- A slice of a globally smooth compactly supported forcing. -/
def forceSlice (f : ℝ × Space → Space) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (t : ℝ) : SmoothL2Field Space :=
  compactField _ (hf.comp (contDiff_const.prodMk contDiff_id))
    ((hc.image continuous_snd).of_isClosed_subset (isClosed_tsupport _)
      (slice_support_subset f hc t))

@[simp] theorem forceSlice_field (f : ℝ × Space → Space) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (t : ℝ) (x : Space) :
    (forceSlice f hf hc t).field x = f (t, x) := rfl

theorem forceSlice_continuous (f : ℝ × Space → Space) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (a T : ℝ) (n : ℕ) :
    Continuous (fun t : Icc (0 : ℝ) T ↦ (forceSlice f hf hc (a + t)).jetLp n) := by
  apply continuous_jetLp_of_compact_family (Icc 0 T) (fun z ↦ f (a + z.1, z.2))
    (hf.comp ((contDiff_const.add contDiff_fst).prodMk contDiff_snd)).contDiffOn
    (Prod.snd '' tsupport f) (hc.image continuous_snd) ?_ _ (fun _ ↦ rfl) n
  exact fun t _ ↦ slice_support_subset f hc (a + t)

/-- The actual pressure gradient as a smooth `L²` field. -/
def gradientField (A : SmoothL2Field ℝ) : SmoothL2Field Space :=
  mapField (toDual ℝ Space).symm.toContinuousLinearMap A.derivative

@[simp] theorem gradientField_field (A : SmoothL2Field ℝ) (x : Space) :
    (gradientField A).field x = gradient A.field x := rfl

theorem gradientField_continuous {s : Type} [TopologicalSpace s]
    (A : s → SmoothL2Field ℝ) (hA : ∀ n, Continuous (fun t ↦ (A t).jetLp n)) (n : ℕ) :
    Continuous (fun t ↦ (gradientField (A t)).jetLp n) :=
  continuous_jetLp_mapField _ _ (continuous_jetLp_derivative A hA) n

theorem gradientField_mem (A : SmoothL2Field ℝ) :
    (gradientField A).toLp ∈ gradientSpace :=
  EulerOrdinarySobolev.gradient_mem _ A.field A.smooth (fun _ ↦ rfl)

open WholeSpaceViscousEnergy WholeSpaceViscousFlow EulerVolterraConvolution

theorem navierStokesRhs_continuous {s : Type} [TopologicalSpace s] [CompactSpace s]
    (ν : ℝ) (A P : s → SmoothL2Field Space)
    (hA : ∀ n, Continuous (fun t ↦ (A t).jetLp n))
    (hP : ∀ n, Continuous (fun t ↦ (P t).jetLp n)) (n : ℕ) :
    Continuous (fun t ↦ (navierStokesRhs ν (A t) (P t)).jetLp n) := by
  apply continuous_jetLp_addField
  · exact continuous_jetLp_mapField _ _
      (continuous_jetLp_addField _ _ (advectionField_continuous A hA) hP)
  · exact continuous_jetLp_mapField _ _ (continuous_jetLp_laplacianField A hA)

section Candidate

variable {ν : ℝ} {u : VelocityField} {p : PressureField} {f : VelocityField}
  {K : Set Space} (h : CandidateProperties ν u p f K)

/-- The candidate's velocity slice, on the open lifespan. -/
def velocitySlice (t : Ioo (0 : ℝ) 1) : SmoothL2Field Space :=
  sliceField u h.velocity_smooth K h.support_compact h.velocity_support t

/-- The candidate's scalar pressure slice, on the open lifespan. -/
def pressureSlice (t : Ioo (0 : ℝ) 1) : SmoothL2Field ℝ :=
  sliceField p h.pressure_smooth K h.support_compact h.pressure_support t

@[simp] theorem velocitySlice_field (t : Ioo (0 : ℝ) 1) (x : Space) :
    (velocitySlice h t).field x = u (t, x) := rfl

@[simp] theorem pressureSlice_field (t : Ioo (0 : ℝ) 1) (x : Space) :
    (pressureSlice h t).field x = p (t, x) := rfl

theorem velocitySlice_solenoidal (t : Ioo (0 : ℝ) 1) :
    (velocitySlice h t).toLp ∈ solenoidalSpace := by
  apply smooth_mem_solenoidal _ (velocitySlice h t).smooth (velocitySlice h t).memLp
  intro x
  have hd := h.divergence_free t ⟨t.property.1.le, t.property.2⟩ x
  rw [NavierStokes.ComparatorBridge.divergence_eq] at hd
  exact hd

/-- The translated parameter of a compact slab starting at time `1/2`. -/
def slabTime (T : ℝ) (hT1 : T < 1 / 2) (t : Icc (0 : ℝ) T) : Ioo (0 : ℝ) 1 :=
  ⟨1 / 2 + t, by constructor <;> linarith [t.property.1, t.property.2]⟩

/-- The PDE identifies the ordinary time derivative with the forced field derivative. -/
theorem velocity_time_hasDerivAt (t : Ioo (0 : ℝ) 1) (x : Space) :
    HasDerivAt (fun r ↦ u (r, x))
      ((addField (navierStokesRhs ν (velocitySlice h t)
        (gradientField (pressureSlice h t)))
        (forceSlice f h.force_smooth h.force_support.1 t)).field x) t := by
  have hd : DifferentiableAt ℝ (fun r ↦ u (r, x)) t :=
    ((NavierStokes.ProblemStatement.smooth_at_interior h.velocity_smooth t.property x).comp
      (t : ℝ) (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  apply hd.hasDerivAt.congr_deriv
  rw [addField_field, navierStokesRhs_field]
  change deriv (fun r ↦ u (r, x)) t =
    -fderiv ℝ (fun y ↦ u (t, y)) x (u (t, x)) -
      gradient (fun y ↦ p (t, y)) x + ν • Δ (fun y ↦ u (t, y)) x + f (t, x)
  have he := h.navier_stokes t t.property x
  rw [navierStokesResidual,
    NavierStokes.ComparatorBridge.laplacian_eq u t x
      ((velocitySlice h t).smooth.of_le (by simp)),
    NavierStokes.ComparatorBridge.gradient_eq] at he
  change deriv (fun r ↦ u (r, x)) t + fderiv ℝ (fun y ↦ u (t, y)) x (u (t, x)) -
    ν • Δ (fun y ↦ u (t, y)) x + gradient (fun y ↦ p (t, y)) x = f (t, x) at he
  have he' := congrArg (fun z : Space ↦ z - fderiv ℝ (fun y ↦ u (t, y)) x (u (t, x)) -
    gradient (fun y ↦ p (t, y)) x + ν • Δ (fun y ↦ u (t, y)) x) he
  convert he' using 1 <;> abel

open ForcedPathEnergy

/-- The candidate on a compact slab, using its actual velocity, pressure and forcing. -/
def forcedPath (T : ℝ) (hT : 0 ≤ T) (hT1 : T < 1 / 2) : ForcedPath ν T hT where
  velocity t := velocitySlice h (slabTime T hT1 t)
  pressureForce t := gradientField (pressureSlice h (slabTime T hT1 t))
  force t := forceSlice f h.force_smooth h.force_support.1 (1 / 2 + t)
  derivative t := addField (navierStokesRhs ν (velocitySlice h (slabTime T hT1 t))
    (gradientField (pressureSlice h (slabTime T hT1 t))))
    (forceSlice f h.force_smooth h.force_support.1 (1 / 2 + t))
  velocity_continuous := sliceField_continuous u h.velocity_smooth K h.support_compact
    h.velocity_support (1 / 2) T (by norm_num) (by linarith)
  force_continuous := forceSlice_continuous f h.force_smooth h.force_support.1 (1 / 2) T
  derivative_continuous := continuous_jetLp_addField _ _
    (navierStokesRhs_continuous ν _ _
      (sliceField_continuous u h.velocity_smooth K h.support_compact h.velocity_support
        (1 / 2) T (by norm_num) (by linarith))
      (gradientField_continuous _ (sliceField_continuous p h.pressure_smooth K
        h.support_compact h.pressure_support (1 / 2) T (by norm_num) (by linarith))))
    (forceSlice_continuous f h.force_smooth h.force_support.1 (1 / 2) T)
  solenoidal t := velocitySlice_solenoidal h (slabTime T hT1 t)
  gradient t := gradientField_mem (pressureSlice h (slabTime T hT1 t))
  time_law t ht x := by
    have hd := (velocity_time_hasDerivAt h (slabTime T hT1 ⟨t, ht.1.le, ht.2.le⟩) x).scomp t
      ((hasDerivAt_id t).const_add (1 / 2 : ℝ))
    simp only [one_smul, Function.comp_def] at hd
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
    simp only [projIcc_of_mem hT (show r ∈ Icc 0 T from ⟨hr.1.le, hr.2.le⟩)]
    rfl
  equation _ := rfl

@[simp] theorem forcedPath_velocity (T : ℝ) (hT : 0 ≤ T) (hT1 : T < 1 / 2)
    (t : Icc (0 : ℝ) T) :
    (forcedPath h T hT hT1).velocity t = velocitySlice h (slabTime T hT1 t) := rfl

@[simp] theorem forcedPath_force (T : ℝ) (hT : 0 ≤ T) (hT1 : T < 1 / 2)
    (t : Icc (0 : ℝ) T) :
    (forcedPath h T hT hT1).force t =
      forceSlice f h.force_smooth h.force_support.1 (1 / 2 + t) := rfl

open WholeSpaceOrderEnergy WholeSpaceBetchov EulerContinuousTimeIntegral MiddleEigenvalueAlgebra
  EulerSmoothSobolev
open PancakeSpectralProjectorRegularity.SymmetricStrain

/-- The forcing energy is continuous even across the candidate's breakdown time. -/
def forceEnergyPath (n : ℕ) : C(Icc (0 : ℝ) 1, ℝ) :=
  ⟨fun t ↦ Real.sqrt (orderEnergy n (forceSlice f h.force_smooth h.force_support.1 t)),
    Real.continuous_sqrt.comp (orderEnergy_continuous_of _ (fun m ↦ by
      simpa only [zero_add] using
        forceSlice_continuous f h.force_smooth h.force_support.1 0 1 m) n)⟩

/-- Every shorter slab has the same force bound. -/
theorem forcedPath_forcePath_le (T : ℝ) (hT : 0 ≤ T) (hT1 : T < 1 / 2)
    (n : ℕ) (t : Icc (0 : ℝ) T) :
    (forcedPath h T hT hT1).forcePath n t ≤ ‖forceEnergyPath h n‖ := by
  have ht : 1 / 2 + (t : ℝ) ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [t.property.1, t.property.2]
  exact (le_abs_self _).trans ((forceEnergyPath h n).norm_coe_le_norm ⟨1 / 2 + t, ht⟩)

/-- The zeroth word energy is twice the candidate's actual kinetic energy. -/
theorem orderEnergy_zero_eq (t : Ioo (0 : ℝ) 1) :
    orderEnergy 0 (velocitySlice h t) = 2 * kineticEnergy u t := by
  have hi := WholeSpaceOfficial.integral_norm_sq (velocitySlice h t)
  simp only [velocitySlice_field] at hi
  simp [orderEnergy, kineticEnergy, hi]

/-- Initial fields agree for all the translated slabs. -/
theorem forcedPath_initial (T : ℝ) (hT : 0 ≤ T) (hT1 : T < 1 / 2) :
    (forcedPath h T hT hT1).velocity ⟨0, le_rfl, hT⟩ =
      velocitySlice h ⟨1 / 2, by norm_num⟩ := by
  apply field_ext
  funext x
  change u (1 / 2 + 0, x) = u (1 / 2, x)
  rw [add_zero]

/-- The majorant may depend on the slab; its integral bound is independent of the endpoint. -/
def UniformMiddleMajorants : Prop :=
    ∃ G : ℝ, ∀ (T : ℝ) (hT : 0 ≤ T) (hT1 : T < 1 / 2),
      ∃ B : C(Icc (0 : ℝ) T, ℝ), (∀ t, 0 ≤ B t) ∧
        (∀ t x, secondEigenvalue (toStrain
          (symm (gradMatrix ((forcedPath h T hT hT1).velocity t) x)) (symm_symm _)) ≤ B t) ∧
        realIntegral T hT B T ≤ G

/-- A uniform middle-eigenvalue budget would contradict the candidate's speed blow-up. -/
theorem no_uniform_middle_majorants (hν : 0 < ν) : ¬ UniformMiddleMajorants h := by
  rintro ⟨G, hG⟩
  let F := ‖forceEnergyPath h 1‖ + ‖forceEnergyPath h 2‖
  have hF0 : 0 ≤ F := add_nonneg (norm_nonneg _) (norm_nonneg _)
  let A := velocitySlice h ⟨1 / 2, by norm_num⟩
  let Z := (1 + orderEnergy 1 A) * Real.exp (2 * G + F)
  let W := (1 + orderEnergy 2 A) * Real.exp (rungTwoConstant ν Z + F)
  obtain ⟨E, hE0, hE⟩ := h.energy_bounded
  have hbounds (T : ℝ) (hT : 0 ≤ T) (hT1 : T < 1 / 2) :
      ∀ t, orderEnergy 1 ((forcedPath h T hT hT1).velocity t) ≤ Z ∧
        orderEnergy 2 ((forcedPath h T hT hT1).velocity t) ≤ W := by
    let U := forcedPath h T hT hT1
    obtain ⟨B, hB0, hB, hBG⟩ := hG T hT hT1
    have hf1 (t) : U.forcePath 1 t ≤ F :=
      (forcedPath_forcePath_le h T hT hT1 1 t).trans (le_add_of_nonneg_right (norm_nonneg _))
    have hf2 (t) : U.forcePath 2 t ≤ F :=
      (forcedPath_forcePath_le h T hT hT1 2 t).trans (le_add_of_nonneg_left (norm_nonneg _))
    have hz (t) : orderEnergy 1 (U.velocity t) ≤ Z := by
      have hz := U.orderEnergy_one_uniform hν.le (by linarith) B hB0 hB hBG hF0 hf1 t
      simpa only [U, forcedPath_initial] using hz
    intro t
    refine ⟨hz t, ?_⟩
    have hw := U.orderEnergy_two_uniform hν (by linarith) hz hF0 hf2 t
    simpa only [U, forcedPath_initial] using hw
  let M := (13 * smoothEmbeddingConstant) * Real.sqrt (2 * E + Z + W)
  have hM0 : 0 ≤ M := mul_nonneg
    (mul_nonneg (by norm_num) smoothEmbeddingConstant_nonneg) (Real.sqrt_nonneg _)
  obtain ⟨t, x, ht, hnear, hspeed⟩ := h.speed_unbounded (M + 1) (by linarith) (1 / 2)
    (by norm_num)
  let T := t - 1 / 2
  have hT : 0 ≤ T := by dsimp [T]; linarith
  have hT1 : T < 1 / 2 := by dsimp [T]; linarith [ht.2]
  let s : Icc (0 : ℝ) T := ⟨T, hT, le_rfl⟩
  let U := forcedPath h T hT hT1
  have hu : U.velocity s = velocitySlice h ⟨t, ht⟩ := by
    apply field_ext
    funext y
    change u (1 / 2 + (t - 1 / 2), y) = u (t, y)
    congr 1
    ext <;> simp
  have h0 : orderEnergy 0 (U.velocity s) ≤ 2 * E := by
    rw [hu, orderEnergy_zero_eq]
    exact mul_le_mul_of_nonneg_left (hE t ⟨ht.1.le, ht.2⟩).2 (by norm_num)
  obtain ⟨h1, h2⟩ := hbounds T hT hT1 s
  have hw : wordEnergy 2 (U.velocity s) ≤ 2 * E + Z + W := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, wordEnergy_succ, wordEnergy_succ, wordEnergy_zero]
    linarith
  have hp := wordBound_pointwise (wordBound_sqrt_energy 2 (U.velocity s)) x
  have hm : ‖(U.velocity s).field x‖ ≤ M := hp.trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hw)
      (mul_nonneg (by norm_num) smoothEmbeddingConstant_nonneg))
  rw [hu, velocitySlice_field] at hm
  linarith

end Candidate

end Mettapedia.FluidDynamics.NavierStokes.ForcedCandidatePancake
