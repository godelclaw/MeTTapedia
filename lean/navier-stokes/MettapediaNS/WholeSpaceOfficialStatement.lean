import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mettapedia.FluidDynamics.NavierStokes.OfficialWholeSpaceProblem
import MettapediaNS.WholeSpacePressurePotential
import MettapediaNS.WholeSpaceNSBlowup

/-!
# From smooth evolutions on `ℝ³` to the official statement (A)

Initial data of the official whole-space problem are smooth `L²` fields: every derivative is
bounded by a multiple of `(1 + |x|)⁻⁴`, which is square integrable in three dimensions, and
the divergence condition makes the field solenoidal. If such data have smooth Navier–Stokes
evolutions on every interval `[0, n + 1]`, uniqueness makes them agree, and they glue to one
velocity on `ℝ³ × [0, ∞)`. The space-time smoothness of the evolutions and of their scalar
pressure potentials makes the glued velocity and pressure `C^∞` on `ℝ³ × [0, ∞)`, the time
derivative within `[0, ∞)` is the pressure-free right-hand side up to time zero, and the
energy inequality bounds the kinetic energy by that of the data.

Hence global existence of the smooth evolutions for all such data gives the official
statement (A) with zero force, and so do finite-horizon bounds on the vorticity integrals,
by the Beale–Kato–Majda criterion of `MettapediaNS.WholeSpaceNSBlowup`. Neither
hypothesis is proved here.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.WholeSpaceOfficial

open Set Filter MeasureTheory InnerProductSpace Module
open EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
  EulerMeanSolenoidal EulerMeanClassical EulerCanonicalGraphPotential WholeSpaceViscousFlow
  WholeSpaceTimeSmooth OfficialPeriodicProblem OfficialWholeSpaceProblem
open scoped Topology ContDiff Laplacian RealInnerProductSpace

/-! ## Rapidly decaying data are smooth `L²` fields -/

theorem memLp_of_decay {E : Type*} [NormedAddCommGroup E] {f : Space → E} (hf : Continuous f)
    (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C / (1 + ‖x‖) ^ (4 : ℝ)) : MemLp f 2 volume := by
  have hint : Integrable (fun x : Space ↦ (1 + ‖x‖) ^ (-(8 : ℝ))) volume :=
    integrable_one_add_norm (by rw [finrank_euclideanSpace, Fintype.card_fin]; norm_num)
  have hgc : Continuous (fun x : Space ↦ C * (1 + ‖x‖) ^ (-(4 : ℝ))) :=
    continuous_const.mul ((continuous_const.add continuous_norm).rpow_const
      fun x ↦ Or.inl (by have hx : (0 : ℝ) < 1 + ‖x‖ := by positivity
                         exact hx.ne'))
  have hg : MemLp (fun x : Space ↦ C * (1 + ‖x‖) ^ (-(4 : ℝ))) 2 volume := by
    rw [memLp_two_iff_integrable_sq hgc.aestronglyMeasurable]
    refine (hint.const_mul (C ^ 2)).congr (Eventually.of_forall fun x ↦ ?_)
    have hpos : 0 < 1 + ‖x‖ := by positivity
    have h1 : ((1 + ‖x‖) ^ (-(4 : ℝ))) ^ 2 = (1 + ‖x‖) ^ (-(8 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
      norm_num
    change C ^ 2 * (1 + ‖x‖) ^ (-(8 : ℝ)) = (C * (1 + ‖x‖) ^ (-(4 : ℝ))) ^ 2
    rw [mul_pow, h1]
  refine hg.of_le hf.aestronglyMeasurable (Eventually.of_forall fun x ↦ ?_)
  have hpos : 0 < 1 + ‖x‖ := by positivity
  have hC0 : 0 ≤ C := by
    have h0 := (norm_nonneg (f x)).trans (hC x)
    have hd : 0 < (1 + ‖x‖) ^ (4 : ℝ) := Real.rpow_pos_of_pos hpos 4
    exact (div_nonneg_iff.mp h0).elim (fun h ↦ h.1) fun h ↦ absurd h.2 (not_le.mpr hd)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC0 (Real.rpow_nonneg hpos.le _)),
    Real.rpow_neg hpos.le, ← div_eq_mul_inv]
  exact hC x

/-- The initial velocity of the official problem as a smooth `L²` field. -/
def dataField (u₀ : Space → Space) (h : InitialVelocityConditionDecay u₀) :
    SmoothL2Field Space where
  field := u₀
  smooth := h.smooth
  integrable n := by
    obtain ⟨C, hC⟩ := h.decay n 4
    exact memLp_of_decay (h.smooth.continuous_iteratedFDeriv (by simp)) C hC

theorem dataField_solenoidal (u₀ : Space → Space) (h : InitialVelocityConditionDecay u₀) :
    (dataField u₀ h).toLp ∈ solenoidalSpace :=
  smooth_mem_solenoidal u₀ h.smooth (dataField u₀ h).memLp h.div_free

theorem integral_norm_sq (B : SmoothL2Field Space) :
    ∫ x, ‖B.field x‖ ^ 2 = ‖B.toLp‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [B.toLp_ae] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

/-! ## Gluing the evolutions -/

section Global

variable {ν : ℝ} {A : SmoothL2Field Space} (hglob : ∀ T, 0 < T → HasNSEvolution ν A T)

theorem horizon_pos (n : ℕ) : (0 : ℝ) < n + 1 := by positivity

/-- The chosen evolution on `[0, n + 1]`. -/
def evol (n : ℕ) : NSEvolution ν (n + 1) (horizon_pos n).le :=
  (hglob (n + 1) (horizon_pos n)).choose_spec.choose

theorem evol_initial (n : ℕ) :
    (evol hglob n).velocity ⟨0, le_rfl, (horizon_pos n).le⟩ = A :=
  (hglob (n + 1) (horizon_pos n)).choose_spec.choose_spec

theorem evol_agree (hν : 0 ≤ ν) {n m : ℕ} (hnm : n ≤ m) (t : ℝ) (ht0 : 0 ≤ t)
    (htn : t ≤ n + 1) :
    (evol hglob m).velocity ⟨t, ht0, htn.trans (by
      have := (Nat.cast_le (α := ℝ)).mpr hnm; linarith)⟩ = (evol hglob n).velocity ⟨t, ht0, htn⟩ := by
  have hle : (n : ℝ) + 1 ≤ m + 1 := by have := (Nat.cast_le (α := ℝ)).mpr hnm; linarith
  have hinit : ((evol hglob n).velocity ⟨0, le_rfl, (horizon_pos n).le⟩).toLp =
      (((evol hglob m).restrictTime (n + 1) (horizon_pos n).le hle).velocity
        ⟨0, le_rfl, (horizon_pos n).le⟩).toLp := by
    rw [evol_initial, NSEvolution.restrictTime_velocity]
    exact congrArg SmoothL2Field.toLp (evol_initial hglob m).symm
  exact (((evol hglob m).restrictTime (n + 1) (horizon_pos n).le hle).velocity_eq_of_initial hν
    (evol hglob n) hinit ⟨t, ht0, htn⟩).symm

theorem velocity_evol_eq (hν : 0 ≤ ν) (n m : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (htn : t ≤ n + 1)
    (htm : t ≤ m + 1) :
    (evol hglob n).velocity ⟨t, ht0, htn⟩ = (evol hglob m).velocity ⟨t, ht0, htm⟩ := by
  rcases le_total n m with h | h
  · exact (evol_agree hglob hν h t ht0 htn).symm
  · exact evol_agree hglob hν h t ht0 htm

theorem joint_evol_eq (hν : 0 ≤ ν) (n m : ℕ) (x : Space) (t : ℝ) (ht0 : 0 ≤ t)
    (htn : t ≤ n + 1) (htm : t ≤ m + 1) :
    joint (horizon_pos n).le (evol hglob n).velocity (x, t) =
      joint (horizon_pos m).le (evol hglob m).velocity (x, t) := by
  simp only [joint, projIcc_of_mem _ ⟨ht0, htn⟩, projIcc_of_mem _ ⟨ht0, htm⟩,
    velocity_evol_eq hglob hν n m t ht0 htn htm]

theorem potential_evol_eq (hν : 0 ≤ ν) (n m : ℕ) (x : Space) (t : ℝ) (ht0 : 0 ≤ t)
    (htn : t ≤ n + 1) (htm : t ≤ m + 1) :
    potential (horizon_pos n).le (evol hglob n).pressureForce (x, t) =
      potential (horizon_pos m).le (evol hglob m).pressureForce (x, t) := by
  simp only [potential, projIcc_of_mem _ ⟨ht0, htn⟩, projIcc_of_mem _ ⟨ht0, htm⟩,
    (evol hglob n).pressureForce_eq (horizon_pos n), (evol hglob m).pressureForce_eq (horizon_pos m),
    velocity_evol_eq hglob hν n m t ht0 htn htm]

/-- The glued velocity. -/
def globalVelocity (x : Space) (t : ℝ) : Space :=
  joint (horizon_pos ⌊t⌋₊).le (evol hglob ⌊t⌋₊).velocity (x, t)

/-- The glued scalar pressure. -/
def globalPressure (x : Space) (t : ℝ) : ℝ :=
  potential (horizon_pos ⌊t⌋₊).le (evol hglob ⌊t⌋₊).pressureForce (x, t)

theorem globalVelocity_eq (hν : 0 ≤ ν) (M : ℕ) (x : Space) (t : ℝ) (ht0 : 0 ≤ t)
    (htM : t ≤ M + 1) :
    globalVelocity hglob x t = joint (horizon_pos M).le (evol hglob M).velocity (x, t) :=
  joint_evol_eq hglob hν _ M x t ht0 (Nat.lt_floor_add_one t).le htM

theorem globalPressure_eq (hν : 0 ≤ ν) (M : ℕ) (x : Space) (t : ℝ) (ht0 : 0 ≤ t)
    (htM : t ≤ M + 1) :
    globalPressure hglob x t = potential (horizon_pos M).le (evol hglob M).pressureForce (x, t) :=
  potential_evol_eq hglob hν _ M x t ht0 (Nat.lt_floor_add_one t).le htM

theorem Icc_mem_nhdsWithin (M : ℕ) (t : ℝ) (ht : t < M + 1) :
    Icc (0 : ℝ) (M + 1) ∈ 𝓝[Ici 0] t :=
  mem_nhdsWithin.mpr ⟨Iio ((M : ℝ) + 1), isOpen_Iio, ht, fun _ hτ ↦ ⟨hτ.2, hτ.1.le⟩⟩

theorem prod_mem_nhdsWithin (M : ℕ) (p : Space × ℝ) (ht : p.2 < M + 1) :
    univ ×ˢ Icc (0 : ℝ) (M + 1) ∈ 𝓝[univ ×ˢ Ici 0] p :=
  mem_nhdsWithin.mpr ⟨univ ×ˢ Iio ((M : ℝ) + 1), isOpen_univ.prod isOpen_Iio, ⟨trivial, ht⟩,
    fun _ hq ↦ ⟨trivial, hq.2.2, hq.1.2.le⟩⟩

theorem globalVelocity_smooth (hν : 0 ≤ ν) :
    ContDiffOn ℝ ∞ (Function.uncurry (globalVelocity hglob)) (univ ×ˢ Ici 0) := by
  rintro ⟨x₀, t₀⟩ ⟨-, ht₀⟩
  have ht₀' : (0 : ℝ) ≤ t₀ := ht₀
  have htM : t₀ < ⌊t₀⌋₊ + 1 := Nat.lt_floor_add_one t₀
  have hnhds := prod_mem_nhdsWithin ⌊t₀⌋₊ (x₀, t₀) htM
  have hsmooth := (evol hglob ⌊t₀⌋₊).velocity_contDiffOn (horizon_pos _) (x₀, t₀)
    ⟨trivial, ht₀', htM.le⟩
  have heq : Function.uncurry (globalVelocity hglob) =ᶠ[𝓝[univ ×ˢ Ici 0] (x₀, t₀)]
      joint (horizon_pos ⌊t₀⌋₊).le (evol hglob ⌊t₀⌋₊).velocity := by
    filter_upwards [hnhds, self_mem_nhdsWithin] with q hq hq'
    exact globalVelocity_eq hglob hν _ q.1 q.2 hq'.2 hq.2.2
  exact (hsmooth.mono_of_mem_nhdsWithin hnhds).congr_of_eventuallyEq heq
    (heq.eq_of_nhdsWithin ⟨trivial, ht₀'⟩)

theorem globalPressure_smooth (hν : 0 ≤ ν) :
    ContDiffOn ℝ ∞ (Function.uncurry (globalPressure hglob)) (univ ×ˢ Ici 0) := by
  rintro ⟨x₀, t₀⟩ ⟨-, ht₀⟩
  have ht₀' : (0 : ℝ) ≤ t₀ := ht₀
  have htM : t₀ < ⌊t₀⌋₊ + 1 := Nat.lt_floor_add_one t₀
  have hnhds := prod_mem_nhdsWithin ⌊t₀⌋₊ (x₀, t₀) htM
  have hsmooth := (evol hglob ⌊t₀⌋₊).scalarPressure_contDiffOn (horizon_pos _) (x₀, t₀)
    ⟨trivial, ht₀', htM.le⟩
  have heq : Function.uncurry (globalPressure hglob) =ᶠ[𝓝[univ ×ˢ Ici 0] (x₀, t₀)]
      potential (horizon_pos ⌊t₀⌋₊).le (evol hglob ⌊t₀⌋₊).pressureForce := by
    filter_upwards [hnhds, self_mem_nhdsWithin] with q hq hq'
    exact globalPressure_eq hglob hν _ q.1 q.2 hq'.2 hq.2.2
  exact (hsmooth.mono_of_mem_nhdsWithin hnhds).congr_of_eventuallyEq heq
    (heq.eq_of_nhdsWithin ⟨trivial, ht₀'⟩)

theorem globalVelocity_slice (t : ℝ) (ht : 0 ≤ t) :
    (globalVelocity hglob · t) =
      ((evol hglob ⌊t⌋₊).velocity ⟨t, ht, (Nat.lt_floor_add_one t).le⟩).field := by
  funext y
  simp only [globalVelocity, joint, projIcc_of_mem _ ⟨ht, (Nat.lt_floor_add_one t).le⟩]

theorem globalPressure_slice (t : ℝ) (ht : 0 ≤ t) :
    (globalPressure hglob · t) =
      radialPotential ((evol hglob ⌊t⌋₊).pressureForce ⟨t, ht, (Nat.lt_floor_add_one t).le⟩).field := by
  funext y
  simp only [globalPressure, potential, projIcc_of_mem _ ⟨ht, (Nat.lt_floor_add_one t).le⟩]

/-- **The glued fields solve the official equation**, with the one-sided time derivative at
time zero. -/
theorem global_navier_stokes (hν : 0 ≤ ν) (x : Space) (t : ℝ) (ht : t ≥ 0) :
    derivWithin (globalVelocity hglob x ·) (Ici 0) t +
        fderiv ℝ (globalVelocity hglob · t) x (globalVelocity hglob x t) =
      ν • Δ (globalVelocity hglob · t) x - gradient (globalPressure hglob · t) x +
        (fun _ _ ↦ (0 : Space)) x t := by
  have htM : t < ⌊t⌋₊ + 1 := Nat.lt_floor_add_one t
  have hmem : t ∈ Icc (0 : ℝ) (⌊t⌋₊ + 1) := ⟨ht, htM.le⟩
  have hd := ((evol hglob ⌊t⌋₊).timeDeriv (horizon_pos _)).within ⟨t, hmem⟩ x
  have hnhds := Icc_mem_nhdsWithin ⌊t⌋₊ t htM
  have hd' : HasDerivWithinAt (globalVelocity hglob x ·)
      ((nsProjectedRhs ν ((evol hglob ⌊t⌋₊).velocity ⟨t, hmem⟩)).field x) (Ici 0) t := by
    apply (hd.mono_of_mem_nhdsWithin hnhds).congr_of_eventuallyEq
    · filter_upwards [hnhds, self_mem_nhdsWithin] with τ hτ hτ0
      exact globalVelocity_eq hglob hν ⌊t⌋₊ x τ hτ0 hτ.2
    · exact globalVelocity_eq hglob hν ⌊t⌋₊ x t ht htM.le
  have hpoint : globalVelocity hglob x t =
      ((evol hglob ⌊t⌋₊).velocity ⟨t, hmem⟩).field x :=
    congrFun (globalVelocity_slice hglob t ht) x
  rw [hd'.derivWithin (uniqueDiffOn_Ici 0 t ht), hpoint, globalVelocity_slice hglob t ht,
    globalPressure_slice hglob t ht,
    (potential_spec (evol hglob ⌊t⌋₊).gradient ⟨t, hmem⟩).2 x,
    (evol hglob ⌊t⌋₊).pressureForce_eq (horizon_pos _), nsProjectedRhs_field]
  abel_nf

theorem global_div_free (x : Space) (t : ℝ) (ht : t ≥ 0) :
    OfficialPeriodicProblem.divergence (globalVelocity hglob · t) x = 0 := by
  rw [globalVelocity_slice hglob t ht]
  exact solenoidal_representative_divergence _ ((evol hglob ⌊t⌋₊).solenoidal _) _
    ((evol hglob ⌊t⌋₊).velocity _).smooth ((evol hglob ⌊t⌋₊).velocity _).toLp_ae x

theorem global_initial (hν : 0 ≤ ν) (x : Space) : globalVelocity hglob x 0 = A.field x := by
  rw [globalVelocity_eq hglob hν 0 x 0 le_rfl (horizon_pos 0).le]
  simp only [joint]
  rw [projIcc_of_mem _ ⟨le_rfl, (horizon_pos 0).le⟩, evol_initial]

theorem global_energy (hν : 0 ≤ ν) (t : ℝ) (ht : t ≥ 0) :
    ∫ x, ‖globalVelocity hglob x t‖ ^ 2 ≤ ‖A.toLp‖ ^ 2 := by
  have hs := congrFun (globalVelocity_slice hglob t ht)
  simp only [hs, integral_norm_sq]
  have h := (evol hglob ⌊t⌋₊).l2_norm_le hν ⟨t, ht, (Nat.lt_floor_add_one t).le⟩
  rw [evol_initial] at h
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

end Global

/-! ## The official statement -/

/-- **Global existence of the smooth evolutions gives the official statement (A).** -/
theorem wholeSpaceStatementA_of_global
    (hglobal : ∀ ν : ℝ, 0 < ν → ∀ A : SmoothL2Field Space, A.toLp ∈ solenoidalSpace →
      ∀ T, 0 < T → HasNSEvolution ν A T) : WholeSpaceStatementA := by
  intro ν hν u₀ hu₀
  have hglob := hglobal ν hν (dataField u₀ hu₀) (dataField_solenoidal u₀ hu₀)
  refine ⟨globalVelocity hglob, globalPressure hglob, ?_⟩
  exact {
    navier_stokes := fun x t ht ↦ global_navier_stokes hglob hν.le x t ht
    div_free := fun x t ht ↦ global_div_free hglob x t ht
    initial_condition := fun x ↦ global_initial hglob hν.le x
    velocity_smooth := globalVelocity_smooth hglob hν.le
    pressure_smooth := globalPressure_smooth hglob hν.le
    integrable := fun t ht ↦ by
      have hs := congrFun (globalVelocity_slice hglob t ht)
      simp only [hs]
      exact ((evol hglob ⌊t⌋₊).velocity _).memLp.norm
    globally_bounded_energy := ⟨‖(dataField u₀ hu₀).toLp‖ ^ 2 + 1, fun t ht ↦
      (global_energy hglob hν.le t ht).trans_lt (lt_add_one _)⟩ }

/-- **Finite-horizon vorticity bounds give the official statement (A).** If, for every
viscosity and every smooth solenoidal datum with all derivatives in `L²`, the vorticity
integrals of all smooth evolutions from the datum are bounded on each finite horizon, then
the official whole-space statement holds. -/
theorem wholeSpaceStatementA_of_vorticityIntegral_bound
    (hbound : ∀ ν : ℝ, 0 < ν → ∀ A : SmoothL2Field Space, A.toLp ∈ solenoidalSpace →
      ∀ H, ∃ G, ∀ S (hS : 0 < S), S ≤ H → ∀ U : NSEvolution ν S hS.le,
        U.velocity ⟨0, le_rfl, hS.le⟩ = A → ∀ t, U.vorticityIntegral t ≤ G) :
    WholeSpaceStatementA :=
  wholeSpaceStatementA_of_global fun ν hν A hA ↦
    hasNSEvolution_of_vorticityIntegral_bound hν.le A hA (hbound ν hν A hA)

end Mettapedia.FluidDynamics.NavierStokes.WholeSpaceOfficial
