import Euler.IntervalPathConcatenation
import Euler.OrdinaryHelmholtzField
import Euler.OrdinaryStrongTime
import Euler.OrdinaryVariableGronwall
import Euler.OrdinaryEulerGradientControl
import Euler.SmoothCoefficientTimeRestriction
import MettapediaNS.WholeSpaceViscousFlow

/-!
# Continuation of smooth Navier–Stokes evolutions on `ℝ³`

The smooth Navier–Stokes evolutions of `MettapediaNS.WholeSpaceViscousFlow` restrict to
shorter intervals and concatenate: the Leray projection removes the pressure, the
Laplacian of a solenoidal field is solenoidal, so the `L²` time derivative of every
evolution is the function `-P((u·∇)u) + ν Δu` of its velocity alone, and two evolutions
that meet at the seam glue to one evolution. Restarting from the endpoint with the local
existence theorem extends every evolution.

The gradient supremum is a continuous path along each evolution, and its time integral
controls the `H³` energy: the upstream transport estimate applies unchanged and viscosity
only adds dissipation. The local existence time depends only on the `H³` energy of the
datum, so a bounded gradient integral would give a uniform restart time and an extension
past any finite maximal time. Hence at a finite maximal time the gradient integral, and
the gradient itself near the endpoint, are unbounded. No rescaling is used, so the
viscosity is never changed.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.WholeSpaceViscousFlow

open Set Filter MeasureTheory InnerProductSpace
open EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
  EulerMeanSolenoidal EulerMeanClassical EulerMeanSobolevBoundedField EulerVolterraConvolution
  EulerContinuousTimeIntegral EulerIntervalConcatenation EulerTimeIntervalRestriction
  WholeSpaceViscousEnergy Finset Laplacian
open scoped Topology

/-! ## The pressure-free right-hand side -/

/-- The Laplacian of a solenoidal field is solenoidal. -/
theorem laplacianField_mem_solenoidal (A : SmoothL2Field Space)
    (hA : A.toLp ∈ solenoidalSpace) : (laplacianField A).toLp ∈ solenoidalSpace := by
  rw [toLp_laplacianField]
  exact Submodule.sum_mem _ fun i _ ↦ word_solenoidal A hA (doubleWord i)

/-- The Navier–Stokes right-hand side with the pressure eliminated,
`-P((u·∇)u) + ν Δu`, with `P` the Leray projection. -/
def nsProjectedRhs (ν : ℝ) (A : SmoothL2Field Space) : SmoothL2Field Space :=
  addField (projectedRhs A) (EulerOrdinarySobolev.scaleField ν (laplacianField A))

theorem nsProjectedRhs_field (ν : ℝ) (A : SmoothL2Field Space) (x : Space) :
    (nsProjectedRhs ν A).field x =
      -fderiv ℝ A.field x (A.field x) - (pressureField A).field x + ν • Δ A.field x := by
  simp only [nsProjectedRhs, addField_field, projectedRhs_field,
    EulerOrdinarySobolev.scaleField_field, laplacianField_field]

theorem nsProjectedRhs_toLp (ν : ℝ) (A : SmoothL2Field Space) :
    (nsProjectedRhs ν A).toLp = (projectedRhs A).toLp + ν • (laplacianField A).toLp := by
  simp only [nsProjectedRhs, toLp_addField, EulerOrdinarySobolev.scaleField_toLp]

theorem nsProjectedRhs_continuous {K : Type*} [TopologicalSpace K] [CompactSpace K] (ν : ℝ)
    (A : K → SmoothL2Field Space) (hA : ∀ n, Continuous (fun t ↦ (A t).jetLp n)) (n : ℕ) :
    Continuous (fun t ↦ (nsProjectedRhs ν (A t)).jetLp n) :=
  continuous_jetLp_addField _ _ (projectedRhs_continuous A hA)
    (fun k ↦ continuous_jetLp_mapField _ _ (continuous_jetLp_laplacianField A hA) k) n

namespace NSEvolution

variable {ν T : ℝ} {hT : 0 ≤ T}

/-! ## Restriction -/

/-- Restriction of a smooth Navier–Stokes evolution to an initial interval. -/
def restrictTime (U : NSEvolution ν T hT) (S : ℝ) (hS : 0 ≤ S) (hST : S ≤ T) :
    NSEvolution ν S hS where
  velocity t := U.velocity (initialInclusion T S hST t)
  pressureForce t := U.pressureForce (initialInclusion T S hST t)
  velocity_continuous n := (U.velocity_continuous n).comp (initialInclusion T S hST).continuous
  pressure_continuous n := (U.pressure_continuous n).comp (initialInclusion T S hST).continuous
  solenoidal t := U.solenoidal (initialInclusion T S hST t)
  gradient t := U.gradient (initialInclusion T S hST t)
  time_law t ht x := by
    have htT : t ∈ Ioo (0 : ℝ) T := ⟨ht.1, ht.2.trans_le hST⟩
    have hd := U.time_law t htT x
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
    rw [projIcc_of_mem hS ⟨hr.1.le, hr.2.le⟩,
      projIcc_of_mem hT ⟨hr.1.le, hr.2.le.trans hST⟩]
    rfl

theorem restrictTime_velocity (U : NSEvolution ν T hT) (S : ℝ) (hS : 0 ≤ S) (hST : S ≤ T)
    (t : Icc (0 : ℝ) S) :
    (U.restrictTime S hS hST).velocity t = U.velocity ⟨t, t.property.1, t.property.2.trans hST⟩ :=
  rfl

/-! ## The pressure-free time derivative -/

theorem derivative_eq_navierStokesRhs (U : NSEvolution ν T hT) (t : Icc (0 : ℝ) T) :
    U.derivative t = navierStokesRhs ν (U.velocity t) (U.pressureForce t) := by
  apply field_ext
  funext x
  rw [derivative_field, navierStokesRhs_field]

theorem velocity_hasDerivWithinAt (U : NSEvolution ν T hT) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun r ↦ (U.velocity (projIcc 0 T hT r)).toLp) (U.derivative t).toLp
      (Icc (0 : ℝ) T) t := by
  have h := ordinaryWord_hasDerivWithinAt T hT U.velocity U.derivative U.velocity_continuous
    U.derivative_continuous
    (fun r hr x ↦ by simpa only [derivative_field] using U.time_law r hr x)
    (Fin.elim0 : Fin 0 → Fin 3) t
  simpa only [wordField_zero] using h

theorem derivative_mem_solenoidal (U : NSEvolution ν T hT) (hpos : 0 < T)
    (t : Icc (0 : ℝ) T) : (U.derivative t).toLp ∈ solenoidalSpace := by
  have hu := U.velocity_hasDerivWithinAt t
  have hp := solenoidalProjection.hasFDerivAt.comp_hasDerivWithinAt (t : ℝ) hu
  have he : (fun r ↦ solenoidalProjection ((U.velocity (projIcc 0 T hT r)).toLp)) =
      fun r ↦ (U.velocity (projIcc 0 T hT r)).toLp := by
    funext r
    exact solenoidalSpace.starProjection_eq_self_iff.mpr (U.solenoidal (projIcc 0 T hT r))
  simp only [Function.comp_def] at hp
  rw [he] at hp
  have hd := (hp.derivWithin (uniqueDiffOn_Icc hpos t t.property)).symm.trans
    (hu.derivWithin (uniqueDiffOn_Icc hpos t t.property))
  exact solenoidalSpace.starProjection_eq_self_iff.mp hd

theorem derivative_toLp_expand (U : NSEvolution ν T hT) (t : Icc (0 : ℝ) T) :
    (U.derivative t).toLp = -((advectionField (U.velocity t) (U.velocity t)).toLp +
      (U.pressureForce t).toLp) + ν • (laplacianField (U.velocity t)).toLp := by
  rw [U.derivative_eq_navierStokesRhs, navierStokesRhs, toLp_addField, eulerRhs, toLp_fieldNeg,
    toLp_addField, EulerOrdinarySobolev.scaleField_toLp]

/-- **The pressure is eliminated.** On a nondegenerate interval, the `L²` time derivative
of a smooth Navier–Stokes evolution is `-P((u·∇)u) + ν Δu`, a function of the velocity. -/
theorem derivative_toLp_projected (U : NSEvolution ν T hT) (hpos : 0 < T)
    (t : Icc (0 : ℝ) T) :
    (U.derivative t).toLp = (nsProjectedRhs ν (U.velocity t)).toLp := by
  have hd : solenoidalProjection (U.derivative t).toLp = (U.derivative t).toLp :=
    solenoidalSpace.starProjection_eq_self_iff.mpr (U.derivative_mem_solenoidal hpos t)
  have hL : solenoidalProjection (laplacianField (U.velocity t)).toLp =
      (laplacianField (U.velocity t)).toLp :=
    solenoidalSpace.starProjection_eq_self_iff.mpr
      (laplacianField_mem_solenoidal _ (U.solenoidal t))
  rw [U.derivative_toLp_expand t, map_add, map_neg, map_add, map_smul,
    (solenoidalProjection_eq_zero_iff _).mpr (U.gradient t), add_zero, hL] at hd
  rw [nsProjectedRhs_toLp, projectedRhs_toLp, U.derivative_toLp_expand t, ← hd]

/-- **The pressure is determined by the velocity.** -/
theorem pressureForce_eq (U : NSEvolution ν T hT) (hpos : 0 < T) (t : Icc (0 : ℝ) T) :
    U.pressureForce t = pressureField (U.velocity t) := by
  apply smoothField_eq_of_toLp_eq
  have h := U.derivative_toLp_projected hpos t
  rw [U.derivative_toLp_expand t, nsProjectedRhs_toLp, projectedRhs_toLp] at h
  have h' : (advectionField (U.velocity t) (U.velocity t)).toLp + (U.pressureForce t).toLp =
      solenoidalProjection (advectionField (U.velocity t) (U.velocity t)).toLp :=
    neg_inj.mp (add_right_cancel h)
  rw [pressureField_toLp, ← h']
  abel

/-! ## Concatenation -/

variable {S : ℝ} {hS : 0 ≤ S}

/-- The velocity of `U` followed by that of `V`. -/
def joinedVelocity (U : NSEvolution ν T hT) (V : NSEvolution ν S hS)
    (t : Icc (0 : ℝ) (T + S)) : SmoothL2Field Space :=
  join T S hT hS U.velocity V.velocity t

theorem joinedVelocity_continuous (U : NSEvolution ν T hT) (V : NSEvolution ν S hS)
    (hmatch : U.velocity ⟨T, hT, le_rfl⟩ = V.velocity ⟨0, le_rfl, hS⟩) (n : ℕ) :
    Continuous (fun t ↦ (U.joinedVelocity V t).jetLp n) := by
  have hc := join_continuous (hT := hT) (hS := hS)
    (fun t ↦ (U.velocity t).jetLp n) (fun t ↦ (V.velocity t).jetLp n)
    (U.velocity_continuous n) (V.velocity_continuous n)
    (congrArg (fun A : SmoothL2Field Space ↦ A.jetLp n) hmatch)
  have he : (fun t : Icc (0 : ℝ) (T + S) ↦ (U.joinedVelocity V t).jetLp n) =
      fun t : Icc (0 : ℝ) (T + S) ↦
        join T S hT hS (fun s ↦ (U.velocity s).jetLp n) (fun s ↦ (V.velocity s).jetLp n) t := by
    funext t
    exact map_join U.velocity V.velocity (fun A : SmoothL2Field Space ↦ A.jetLp n) t
  rw [he]
  exact hc.comp continuous_subtype_val

theorem velocity_hasDerivWithinAt_projected (U : NSEvolution ν T hT) (hpos : 0 < T)
    (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun r ↦ (U.velocity (projIcc 0 T hT r)).toLp)
      (nsProjectedRhs ν (U.velocity t)).toLp (Icc (0 : ℝ) T) t := by
  rw [← U.derivative_toLp_projected hpos t]
  exact U.velocity_hasDerivWithinAt t

theorem joinedVelocity_derivative (U : NSEvolution ν T hT) (V : NSEvolution ν S hS)
    (hTpos : 0 < T) (hSpos : 0 < S)
    (hmatch : U.velocity ⟨T, hT, le_rfl⟩ = V.velocity ⟨0, le_rfl, hS⟩)
    (t : ℝ) (ht : t ∈ Ioo 0 (T + S)) :
    HasDerivAt (fun r ↦ (U.joinedVelocity V (projIcc 0 (T + S) (add_nonneg hT hS) r)).toLp)
      (nsProjectedRhs ν (U.joinedVelocity V ⟨t, ht.1.le, ht.2.le⟩)).toLp t := by
  have hd := join_hasDerivAt (fun s ↦ (U.velocity s).toLp) (fun s ↦ (V.velocity s).toLp)
    (fun s ↦ (nsProjectedRhs ν (U.velocity s)).toLp)
    (fun s ↦ (nsProjectedRhs ν (V.velocity s)).toLp)
    hTpos hSpos (congrArg (fun A : SmoothL2Field Space ↦ A.toLp) hmatch)
    (U.velocity_hasDerivWithinAt_projected hTpos)
    (V.velocity_hasDerivWithinAt_projected hSpos)
    (congrArg (fun A : SmoothL2Field Space ↦ (nsProjectedRhs ν A).toLp) hmatch) t ht
  have hb : join T S hT hS (fun s ↦ (nsProjectedRhs ν (U.velocity s)).toLp)
      (fun s ↦ (nsProjectedRhs ν (V.velocity s)).toLp) t =
      (nsProjectedRhs ν (U.joinedVelocity V ⟨t, ht.1.le, ht.2.le⟩)).toLp :=
    (map_join U.velocity V.velocity
      (fun A : SmoothL2Field Space ↦ (nsProjectedRhs ν A).toLp) t).symm
  rw [hb] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds ht.1 ht.2] with r hr
  rw [projIcc_of_mem (add_nonneg hT hS) hr]
  exact map_join U.velocity V.velocity (fun A : SmoothL2Field Space ↦ A.toLp) r

theorem joinedVelocity_solenoidal (U : NSEvolution ν T hT) (V : NSEvolution ν S hS)
    (t : Icc (0 : ℝ) (T + S)) : (U.joinedVelocity V t).toLp ∈ solenoidalSpace := by
  unfold joinedVelocity EulerIntervalConcatenation.join
  split
  · exact U.solenoidal _
  · exact V.solenoidal _

/-- **Concatenation.** Two smooth Navier–Stokes evolutions that meet at the seam glue to
one smooth Navier–Stokes evolution; its pressure is the canonical one. -/
def concatenate (U : NSEvolution ν T hT) (V : NSEvolution ν S hS) (hTpos : 0 < T)
    (hSpos : 0 < S) (hmatch : U.velocity ⟨T, hT, le_rfl⟩ = V.velocity ⟨0, le_rfl, hS⟩) :
    NSEvolution ν (T + S) (add_nonneg hT hS) where
  velocity := U.joinedVelocity V
  pressureForce t := pressureField (U.joinedVelocity V t)
  velocity_continuous := U.joinedVelocity_continuous V hmatch
  pressure_continuous := pressureField_continuous (U.joinedVelocity V)
    (U.joinedVelocity_continuous V hmatch)
  solenoidal := U.joinedVelocity_solenoidal V
  gradient t := pressureField_mem_gradient (U.joinedVelocity V t)
  time_law t ht x := by
    have hd := pointwise_derivative_of_l2 (T + S) (add_nonneg hT hS)
      (U.joinedVelocity V) (fun s ↦ nsProjectedRhs ν (U.joinedVelocity V s))
      (U.joinedVelocity_continuous V hmatch)
      (nsProjectedRhs_continuous ν (U.joinedVelocity V) (U.joinedVelocity_continuous V hmatch))
      (U.joinedVelocity_derivative V hTpos hSpos hmatch) ⟨t, ht.1.le, ht.2.le⟩ x
    simpa only [nsProjectedRhs_field] using hd.hasDerivAt (Icc_mem_nhds ht.1 ht.2)

theorem concatenate_initial (U : NSEvolution ν T hT) (V : NSEvolution ν S hS) (hTpos : 0 < T)
    (hSpos : 0 < S) (hmatch : U.velocity ⟨T, hT, le_rfl⟩ = V.velocity ⟨0, le_rfl, hS⟩) :
    (U.concatenate V hTpos hSpos hmatch).velocity ⟨0, le_rfl, add_nonneg hT hS⟩ =
      U.velocity ⟨0, le_rfl, hT⟩ := by
  change join T S hT hS U.velocity V.velocity 0 = U.velocity ⟨0, le_rfl, hT⟩
  rw [join_left U.velocity V.velocity hT,
    projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩)]

theorem concatenate_left (U : NSEvolution ν T hT) (V : NSEvolution ν S hS) (hTpos : 0 < T)
    (hSpos : 0 < S) (hmatch : U.velocity ⟨T, hT, le_rfl⟩ = V.velocity ⟨0, le_rfl, hS⟩)
    (t : Icc (0 : ℝ) T) :
    (U.concatenate V hTpos hSpos hmatch).velocity
        ⟨t, t.property.1, t.property.2.trans (le_add_of_nonneg_right hS)⟩ = U.velocity t := by
  change join T S hT hS U.velocity V.velocity t = U.velocity t
  rw [join_left U.velocity V.velocity t.property.2, projIcc_of_mem hT t.property]

theorem concatenate_right (U : NSEvolution ν T hT) (V : NSEvolution ν S hS) (hTpos : 0 < T)
    (hSpos : 0 < S) (hmatch : U.velocity ⟨T, hT, le_rfl⟩ = V.velocity ⟨0, le_rfl, hS⟩)
    (t : Icc (0 : ℝ) S) :
    (U.concatenate V hTpos hSpos hmatch).velocity
        ⟨T + t, add_nonneg hT t.property.1, add_le_add_right t.property.2 T⟩ = V.velocity t := by
  change join T S hT hS U.velocity V.velocity (T + t) = V.velocity t
  rw [join_right U.velocity V.velocity hmatch (le_add_of_nonneg_right t.property.1),
    add_sub_cancel_left, projIcc_of_mem hS t.property]

/-- **Extension.** Every smooth Navier–Stokes evolution on a nondegenerate interval extends
by the local existence time of its final velocity. -/
theorem exists_extension (hν : 0 ≤ ν) (U : NSEvolution ν T hT) (hTpos : 0 < T) :
    ∃ V : NSEvolution ν (T + regularizedTime (U.velocity ⟨T, hT, le_rfl⟩))
        (add_nonneg hT (regularizedTime_pos _).le),
      V.velocity ⟨0, le_rfl, add_nonneg hT (regularizedTime_pos _).le⟩ =
          U.velocity ⟨0, le_rfl, hT⟩ ∧
        ∀ t : Icc (0 : ℝ) T, V.velocity ⟨t, t.property.1,
          t.property.2.trans (le_add_of_nonneg_right (regularizedTime_pos _).le)⟩ =
            U.velocity t := by
  let A := U.velocity ⟨T, hT, le_rfl⟩
  let W := localNSEvolution hν A (U.solenoidal ⟨T, hT, le_rfl⟩)
  have hmatch : U.velocity ⟨T, hT, le_rfl⟩ = W.velocity ⟨0, le_rfl, (regularizedTime_pos A).le⟩ :=
    (localNSEvolution_initial hν A (U.solenoidal ⟨T, hT, le_rfl⟩)).symm
  exact ⟨U.concatenate W hTpos (regularizedTime_pos A) hmatch,
    U.concatenate_initial W hTpos (regularizedTime_pos A) hmatch,
    U.concatenate_left W hTpos (regularizedTime_pos A) hmatch⟩

/-! ## Gradient control of the `H³` energy -/

/-- The supremum of the velocity gradient, a continuous path. -/
def gradientNormPath (U : NSEvolution ν T hT) : C(Icc (0 : ℝ) T, ℝ) :=
  ⟨fun t ↦ ‖finiteField (U.velocity t).derivative‖,
    (continuous_finiteField (fun t ↦ (U.velocity t).derivative)
      (continuous_jetLp_derivative U.velocity U.velocity_continuous)).norm⟩

theorem gradientNormPath_nonneg (U : NSEvolution ν T hT) (t : Icc (0 : ℝ) T) :
    0 ≤ U.gradientNormPath t := by
  change 0 ≤ ‖finiteField (U.velocity t).derivative‖
  exact norm_nonneg _

theorem gradientNormPath_le_iff (U : NSEvolution ν T hT) (t : Icc (0 : ℝ) T) (K : ℝ) :
    U.gradientNormPath t ≤ K ↔ ∀ x, ‖fderiv ℝ (U.velocity t).field x‖ ≤ K := by
  change ‖finiteField (U.velocity t).derivative‖ ≤ K ↔ _
  rw [BoundedContinuousFunction.norm_le_of_nonempty]
  simp only [finiteField_apply]
  rfl

theorem pointwise_gradient_le (U : NSEvolution ν T hT) (t : Icc (0 : ℝ) T) (x : Space) :
    ‖fderiv ℝ (U.velocity t).field x‖ ≤ U.gradientNormPath t :=
  (U.gradientNormPath_le_iff t _).mp le_rfl x

/-- The time integral of the gradient supremum. -/
def gradientIntegral (U : NSEvolution ν T hT) (t : Icc (0 : ℝ) T) : ℝ :=
  realIntegral T hT U.gradientNormPath t

theorem gradientIntegral_nonneg (U : NSEvolution ν T hT) (t : Icc (0 : ℝ) T) :
    0 ≤ U.gradientIntegral t :=
  intervalIntegral.integral_nonneg_of_forall t.property.1
    (fun r ↦ U.gradientNormPath_nonneg (projIcc 0 T hT r))

theorem gradientIntegral_le_const (U : NSEvolution ν T hT) (K : ℝ)
    (hK : ∀ t x, ‖fderiv ℝ (U.velocity t).field x‖ ≤ K) (t : Icc (0 : ℝ) T) :
    U.gradientIntegral t ≤ K * (t : ℝ) := by
  have hc := extendPath_continuous T hT U.gradientNormPath
  calc
    _ ≤ ∫ _r in (0 : ℝ)..(t : ℝ), K :=
      intervalIntegral.integral_mono_on t.property.1 (hc.intervalIntegrable 0 t)
        (continuous_const.intervalIntegrable 0 t) (fun r _ ↦
          (U.gradientNormPath_le_iff (projIcc 0 T hT r) K).mpr (hK _))
    _ = _ := by simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]; ring

theorem gradientIntegral_mono (U : NSEvolution ν T hT) (s t : Icc (0 : ℝ) T)
    (hst : (s : ℝ) ≤ t) : U.gradientIntegral s ≤ U.gradientIntegral t :=
  intervalIntegral.integral_mono_interval le_rfl s.property.1 hst
    (Eventually.of_forall (fun r ↦ U.gradientNormPath_nonneg (projIcc 0 T hT r)))
    ((extendPath_continuous T hT U.gradientNormPath).intervalIntegrable 0 t)

/-- The integer-order energy along the evolution, a continuous path. -/
def energyPath (U : NSEvolution ν T hT) (m : ℕ) : C(Icc (0 : ℝ) T, ℝ) :=
  ⟨fun t ↦ wordEnergy m (U.velocity t), wordEnergy_continuous U.velocity U.velocity_continuous m⟩

theorem energy_hasDerivWithinAt (U : NSEvolution ν T hT) (m : ℕ) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (U.energyPath m))
      (integerEnergyProduction m (U.velocity t) (U.derivative t)) (Icc (0 : ℝ) T) t := by
  apply wordEnergy_hasDerivWithinAt T hT U.velocity U.derivative
    U.velocity_continuous U.derivative_continuous
  intro r hr x
  simpa only [derivative_field] using U.time_law r hr x

/-- The upstream `H³` transport estimate along the evolution; viscosity only helps. -/
theorem energyProduction_gradient (hν : 0 ≤ ν) (U : NSEvolution ν T hT) (K : ℝ)
    (t : Icc (0 : ℝ) T) (hK : ∀ x, ‖fderiv ℝ (U.velocity t).field x‖ ≤ K) :
    integerEnergyProduction 3 (U.velocity t) (U.derivative t) ≤
      gradientEnergyConstant * K * wordEnergy 3 (U.velocity t) := by
  rw [U.derivative_eq_navierStokesRhs]
  exact h3_energyProduction_le_of_nonneg hν _ _ K hK
    (solenoidal_representative_divergence _ (U.solenoidal t) _ (U.velocity t).smooth
      (U.velocity t).toLp_ae)
    (U.solenoidal t) (U.gradient t)

/-- **The gradient integral controls the `H³` energy.** -/
theorem h3_energy_gradientIntegral (hν : 0 ≤ ν) (U : NSEvolution ν T hT) (t : Icc (0 : ℝ) T) :
    wordEnergy 3 (U.velocity t) ≤ wordEnergy 3 (U.velocity ⟨0, le_rfl, hT⟩) *
      Real.exp (gradientEnergyConstant * U.gradientIntegral t) := by
  have hd (r : ℝ) (hr : r ∈ Ico 0 T) :
      HasDerivWithinAt (extendPath T hT (U.energyPath 3))
        (integerEnergyProduction 3 (U.velocity (projIcc 0 T hT r))
          (U.derivative (projIcc 0 T hT r))) (Icc 0 T) r := by
    have h := U.energy_hasDerivWithinAt 3 ⟨r, hr.1, hr.2.le⟩
    simpa only [projIcc_of_mem hT (show r ∈ Icc 0 T from ⟨hr.1, hr.2.le⟩)] using h
  have hb (r : ℝ) (_hr : r ∈ Ico 0 T) :
      integerEnergyProduction 3 (U.velocity (projIcc 0 T hT r))
          (U.derivative (projIcc 0 T hT r)) ≤
        gradientEnergyConstant * extendPath T hT U.gradientNormPath r *
          extendPath T hT (U.energyPath 3) r :=
    U.energyProduction_gradient hν _ _ (U.pointwise_gradient_le _)
  have h := variable_linear_stability T hT (extendPath T hT (U.energyPath 3))
    (fun r ↦ integerEnergyProduction 3 (U.velocity (projIcc 0 T hT r))
      (U.derivative (projIcc 0 T hT r)))
    gradientEnergyConstant U.gradientNormPath
    ((U.energyPath 3).continuous.comp continuous_projIcc).continuousOn hd hb t
  simpa only [extendPath, projIcc_of_mem hT t.property,
    projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩),
    energyPath, ContinuousMap.coe_mk, gradientIntegral] using h

end NSEvolution

/-! ## Maximal lifespans -/

/-- `A` starts a smooth Navier–Stokes evolution on `[0, T]`. -/
def HasNSEvolution (ν : ℝ) (A : SmoothL2Field Space) (T : ℝ) : Prop :=
  ∃ hT : 0 < T, ∃ U : NSEvolution ν T hT.le, U.velocity ⟨0, le_rfl, hT.le⟩ = A

theorem HasNSEvolution.restrict {ν : ℝ} {A : SmoothL2Field Space} {T : ℝ}
    (h : HasNSEvolution ν A T) (S : ℝ) (hS : 0 < S) (hST : S ≤ T) : HasNSEvolution ν A S := by
  obtain ⟨hT, U, hU⟩ := h
  exact ⟨hS, U.restrictTime S hS.le hST, hU⟩

theorem HasNSEvolution.lt_of_failure {ν : ℝ} {A : SmoothL2Field Space} {T B : ℝ}
    (h : HasNSEvolution ν A T) (hB : 0 < B) (hfail : ¬ HasNSEvolution ν A B) : T < B := by
  by_contra hn
  exact hfail (h.restrict B hB (le_of_not_gt hn))

theorem HasNSEvolution.extend {ν : ℝ} (hν : 0 ≤ ν) {A : SmoothL2Field Space} {T : ℝ}
    (h : HasNSEvolution ν A T) : ∃ S, T < S ∧ HasNSEvolution ν A S := by
  obtain ⟨hT, U, hU⟩ := h
  obtain ⟨V, hV, -⟩ := U.exists_extension hν hT
  exact ⟨_, lt_add_of_pos_right T (regularizedTime_pos _),
    add_pos hT (regularizedTime_pos _), V, hV.trans hU⟩

theorem hasNSEvolution_local {ν : ℝ} (hν : 0 ≤ ν) (A : SmoothL2Field Space)
    (hA : A.toLp ∈ solenoidalSpace) : ∃ T, HasNSEvolution ν A T := by
  obtain ⟨T, hT, U, hU⟩ := exists_local_nsEvolution hν A hA
  exact ⟨T, hT, U, hU⟩

/-- **A finite maximal lifespan**: smooth evolutions on every shorter interval and none
on any longer one. -/
structure NSLifespan (ν : ℝ) (A : SmoothL2Field Space) where
  duration : ℝ
  duration_pos : 0 < duration
  shorter : ∀ S, 0 < S → S < duration → HasNSEvolution ν A S
  maximal : ∀ S, duration < S → ¬ HasNSEvolution ν A S

theorem exists_nsLifespan {ν : ℝ} (A : SmoothL2Field Space) (B : ℝ) (hB : 0 < B)
    (hlocal : ∃ T, HasNSEvolution ν A T) (hfail : ¬ HasNSEvolution ν A B) :
    ∃ L : NSLifespan ν A, L.duration ≤ B := by
  let times : Set ℝ := {T | HasNSEvolution ν A T}
  have hne : times.Nonempty := hlocal
  have hbound : ∀ T ∈ times, T ≤ B := fun T hT ↦ (hT.lt_of_failure hB hfail).le
  have hbdd : BddAbove times := ⟨B, hbound⟩
  have hpos : 0 < sSup times := by
    obtain ⟨T, hT⟩ := hlocal
    exact hT.choose.trans_le (le_csSup hbdd hT)
  refine ⟨{
    duration := sSup times
    duration_pos := hpos
    shorter := ?_
    maximal := ?_ }, csSup_le hne hbound⟩
  · intro S hS hST
    obtain ⟨T, hT, hST'⟩ := exists_lt_of_lt_csSup hne hST
    exact hT.restrict S hS hST'.le
  · intro S hST hS
    exact (not_le_of_gt hST) (le_csSup hbdd hS)

/-- **Global existence or a finite maximal lifespan.** -/
theorem global_or_lifespan {ν : ℝ} (hν : 0 ≤ ν) (A : SmoothL2Field Space)
    (hA : A.toLp ∈ solenoidalSpace) :
    (∀ T, 0 < T → HasNSEvolution ν A T) ∨ Nonempty (NSLifespan ν A) := by
  by_cases h : ∀ T, 0 < T → HasNSEvolution ν A T
  · exact Or.inl h
  · push Not at h
    obtain ⟨B, hB, hfail⟩ := h
    obtain ⟨L, -⟩ := exists_nsLifespan A B hB (hasNSEvolution_local hν A hA) hfail
    exact Or.inr ⟨L⟩

namespace NSLifespan

variable {ν : ℝ} {A : SmoothL2Field Space} (L : NSLifespan ν A)

/-- The smooth evolution on a shorter interval. -/
def evolution (S : ℝ) (hS : 0 < S) (hSL : S < L.duration) : NSEvolution ν S hS.le :=
  (L.shorter S hS hSL).choose_spec.choose

theorem evolution_initial (S : ℝ) (hS : 0 < S) (hSL : S < L.duration) :
    (L.evolution S hS hSL).velocity ⟨0, le_rfl, hS.le⟩ = A :=
  (L.shorter S hS hSL).choose_spec.choose_spec

/-- The evolutions on shorter intervals agree, by uniqueness. -/
theorem evolution_agrees (hν : 0 ≤ ν) (S T : ℝ) (hS : 0 < S) (hT : 0 < T)
    (hSL : S < L.duration) (hTL : T < L.duration) (hST : S ≤ T) (t : Icc (0 : ℝ) S) :
    (L.evolution T hT hTL).velocity ⟨t, t.property.1, t.property.2.trans hST⟩ =
      (L.evolution S hS hSL).velocity t := by
  have hinit : ((L.evolution S hS hSL).velocity ⟨0, le_rfl, hS.le⟩).toLp =
      (((L.evolution T hT hTL).restrictTime S hS.le hST).velocity ⟨0, le_rfl, hS.le⟩).toLp := by
    rw [L.evolution_initial S hS hSL, NSEvolution.restrictTime_velocity]
    exact congrArg SmoothL2Field.toLp (L.evolution_initial T hT hTL).symm
  exact (((L.evolution T hT hTL).restrictTime S hS.le hST).velocity_eq_of_initial hν
    (L.evolution S hS hSL) hinit t).symm

theorem evolution_agrees_at (hν : 0 ≤ ν) (S T : ℝ) (hS : 0 < S) (hT : 0 < T)
    (hSL : S < L.duration) (hTL : T < L.duration) (t : ℝ) (ht0 : 0 ≤ t) (htS : t ≤ S)
    (htT : t ≤ T) :
    (L.evolution S hS hSL).velocity ⟨t, ht0, htS⟩ =
      (L.evolution T hT hTL).velocity ⟨t, ht0, htT⟩ := by
  rcases le_total S T with hST | hTS
  · exact (L.evolution_agrees hν S T hS hT hSL hTL hST ⟨t, ht0, htS⟩).symm
  · exact L.evolution_agrees hν T S hT hS hTL hSL hTS ⟨t, ht0, htT⟩

/-- **Continuation.** The gradient integrals of the shorter evolutions are not bounded:
otherwise the `H³` energy would be bounded, every restart time would exceed a fixed
`δ > 0`, and restarting at `L - δ/2` would give an evolution past `L`. -/
theorem not_gradientIntegral_bounded (hν : 0 ≤ ν) (G : ℝ)
    (hG : ∀ S (hS : 0 < S) (hSL : S < L.duration) t,
      (L.evolution S hS hSL).gradientIntegral t ≤ G) : False := by
  have hc := tameEnergyConstant_nonneg 3
  have hE0 : 0 ≤ wordEnergy 3 A * Real.exp (gradientEnergyConstant * G) :=
    mul_nonneg (wordEnergy_nonneg 3 A) (Real.exp_pos _).le
  obtain ⟨E, hE0, hEdef⟩ : ∃ E, 0 ≤ E ∧ E = wordEnergy 3 A * Real.exp (gradientEnergyConstant * G) :=
    ⟨_, hE0, rfl⟩
  have hδpos : 0 < 2 * (1 + tameEnergyConstant 3) * (1 + E) :=
    mul_pos (mul_pos two_pos (by linarith)) (by linarith)
  obtain ⟨δ, hδ, hδdef⟩ : ∃ δ, 0 < δ ∧ δ = (2 * (1 + tameEnergyConstant 3) * (1 + E))⁻¹ :=
    ⟨_, inv_pos.mpr hδpos, rfl⟩
  obtain ⟨S, hSmax⟩ : ∃ S, S = max (L.duration - δ / 2) (L.duration / 2) := ⟨_, rfl⟩
  have hS : 0 < S := by
    rw [hSmax]
    exact lt_of_lt_of_le (half_pos L.duration_pos) (le_max_right _ _)
  have hSL : S < L.duration := by
    rw [hSmax]
    exact max_lt (by linarith) (half_lt_self L.duration_pos)
  have hSδ : L.duration - δ / 2 ≤ S := by
    rw [hSmax]
    exact le_max_left _ _
  have hEU : wordEnergy 3 ((L.evolution S hS hSL).velocity ⟨S, hS.le, le_rfl⟩) ≤ E := by
    have h := (L.evolution S hS hSL).h3_energy_gradientIntegral hν ⟨S, hS.le, le_rfl⟩
    rw [L.evolution_initial S hS hSL] at h
    rw [hEdef]
    exact h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (hG S hS hSL _) gradientEnergyConstant_nonneg))
      (wordEnergy_nonneg 3 A))
  have hδR : δ ≤ regularizedTime ((L.evolution S hS hSL).velocity ⟨S, hS.le, le_rfl⟩) := by
    rw [hδdef, regularizedTime]
    have hw := wordEnergy_nonneg 3 ((L.evolution S hS hSL).velocity ⟨S, hS.le, le_rfl⟩)
    apply inv_anti₀ (mul_pos (mul_pos two_pos (by linarith)) (by linarith))
    have h2 : 0 ≤ 2 * (1 + tameEnergyConstant 3) := by linarith
    exact mul_le_mul_of_nonneg_left (by linarith) h2
  obtain ⟨V, hV, -⟩ := (L.evolution S hS hSL).exists_extension hν hS
  apply L.maximal (S + regularizedTime ((L.evolution S hS hSL).velocity ⟨S, hS.le, le_rfl⟩))
  · linarith
  · exact ⟨add_pos hS (regularizedTime_pos _), V, hV.trans (L.evolution_initial S hS hSL)⟩

/-- **The gradient integral blows up at a finite maximal time.** -/
theorem gradientIntegral_unbounded (hν : 0 ≤ ν) (G : ℝ) :
    ∃ (S : ℝ) (hS : 0 < S) (hSL : S < L.duration) (t : Icc (0 : ℝ) S),
      G < (L.evolution S hS hSL).gradientIntegral t := by
  by_contra hn
  push Not at hn
  exact L.not_gradientIntegral_bounded hν G hn

/-- **The gradient is unbounded at a finite maximal time.** -/
theorem gradient_unbounded (hν : 0 ≤ ν) (K : ℝ) :
    ∃ (S : ℝ) (hS : 0 < S) (hSL : S < L.duration) (t : Icc (0 : ℝ) S) (x : Space),
      K < ‖fderiv ℝ ((L.evolution S hS hSL).velocity t).field x‖ := by
  by_contra hn
  push Not at hn
  apply L.not_gradientIntegral_bounded hν ((max K 0) * L.duration)
  intro S hS hSL t
  apply ((L.evolution S hS hSL).gradientIntegral_le_const (max K 0)
    (fun r x ↦ (hn S hS hSL r x).trans (le_max_left K 0)) t).trans
  exact mul_le_mul_of_nonneg_left (t.property.2.trans hSL.le) (le_max_right K 0)

/-- The gradient is unbounded on every final segment of the lifespan. -/
theorem gradient_unbounded_near_endpoint (hν : 0 ≤ ν) (τ K : ℝ) (hτ : τ < L.duration) :
    ∃ (S : ℝ) (hS : 0 < S) (hSL : S < L.duration) (t : Icc (0 : ℝ) S) (x : Space),
      τ < t ∧ K < ‖fderiv ℝ ((L.evolution S hS hSL).velocity t).field x‖ := by
  by_contra hn
  push Not at hn
  obtain ⟨R, hRdef⟩ : ∃ R, R = (max τ 0 + L.duration) / 2 := ⟨_, rfl⟩
  have hm : max τ 0 < L.duration := max_lt hτ L.duration_pos
  have hR : 0 < R := by rw [hRdef]; linarith [le_max_right τ 0, L.duration_pos]
  have hRL : R < L.duration := by rw [hRdef]; linarith
  have hτR : τ < R := by rw [hRdef]; linarith [le_max_left τ 0]
  obtain ⟨C, hCdef⟩ : ∃ C, C = ‖(L.evolution R hR hRL).gradientNormPath‖ := ⟨_, rfl⟩
  obtain ⟨S, hS, hSL, t, x, hx⟩ := L.gradient_unbounded hν (max C K)
  apply (not_lt_of_ge (show ‖fderiv ℝ ((L.evolution S hS hSL).velocity t).field x‖ ≤
    max C K from ?_)) hx
  by_cases ht : (t : ℝ) ≤ R
  · have he := L.evolution_agrees_at hν S R hS hR hSL hRL t t.property.1 t.property.2 ht
    rw [he]
    apply ((L.evolution R hR hRL).pointwise_gradient_le ⟨t, t.property.1, ht⟩ x).trans
    apply le_trans _ (le_max_left C K)
    rw [hCdef]
    exact le_trans (le_abs_self _) ((L.evolution R hR hRL).gradientNormPath.norm_coe_le_norm _)
  · exact (hn S hS hSL t x (hτR.trans (lt_of_not_ge ht))).trans (le_max_right C K)

end NSLifespan

end Mettapedia.FluidDynamics.NavierStokes.WholeSpaceViscousFlow
