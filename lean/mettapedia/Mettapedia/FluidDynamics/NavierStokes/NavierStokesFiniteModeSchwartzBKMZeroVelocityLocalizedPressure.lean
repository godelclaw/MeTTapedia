import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeSchwartzBKMAffinePressureObstructions

/-!
# Navier-Stokes Finite-Mode Schwartz BKM: ZeroVelocityLocalizedPressure

Localized-Schwartz pressure classification for zero-velocity BKM data.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- A Schwartz pressure profile on the concrete Navier--Stokes space cannot
have a nonzero globally constant spatial gradient.  Boundedness of the
Schwartz function contradicts the affine growth forced by a nonzero constant
gradient. -/
theorem schwartzMap_gradient_constant_eq_zero
    (q : 𝓢(NSSpace, ℝ))
    (hconst : ∀ x : NSSpace,
      gradient (fun z : NSSpace => q z) x =
        gradient (fun z : NSSpace => q z) (0 : NSSpace)) :
    ∀ x : NSSpace, gradient (fun z : NSSpace => q z) x = 0 := by
  let f : NSSpace → ℝ := fun z => q z
  let g : NSSpace := gradient f (0 : NSSpace)
  have hdiff : Differentiable ℝ f := by
    simpa [f] using q.smooth'.differentiable (by simp)
  have hgzero : g = 0 := by
    by_contra hg
    let φ : NSSpace →L[ℝ] ℝ := fderiv ℝ f (0 : NSSpace)
    have hfd : ∀ z : NSSpace, fderiv ℝ f z = φ := by
      intro z
      apply ContinuousLinearMap.ext
      intro v
      have hz : DifferentiableAt ℝ f z := hdiff z
      have h0 : DifferentiableAt ℝ f (0 : NSSpace) := hdiff 0
      have hgradz : gradient f z = gradient f (0 : NSSpace) := by
        simpa [f] using hconst z
      calc
        (fderiv ℝ f z) v = ⟪gradient f z, v⟫ := by
          rw [← inner_gradient_left hz]
        _ = ⟪g, v⟫ := by
          simpa [g] using congrArg (fun w : NSSpace => ⟪w, v⟫) hgradz
        _ = (fderiv ℝ f (0 : NSSpace)) v := by
          rw [inner_gradient_left h0]
        _ = φ v := rfl
    let M : ℝ := (SchwartzMap.seminorm ℝ 0 0) q
    have hMnonneg : 0 ≤ M :=
      apply_nonneg (SchwartzMap.seminorm ℝ 0 0) q
    have hnormgpos : 0 < ‖g‖ := norm_pos_iff.mpr hg
    have hdenpos : 0 < ‖g‖ ^ 2 := sq_pos_of_ne_zero (ne_of_gt hnormgpos)
    have hdenne : ‖g‖ ^ 2 ≠ 0 := ne_of_gt hdenpos
    let r : ℝ := (2 * M + 1) / ‖g‖ ^ 2
    have hrmul : r * ‖g‖ ^ 2 = 2 * M + 1 := by
      simpa [r] using (div_mul_cancel₀ (2 * M + 1) hdenne)
    have hbound : ‖q (r • g) - q (0 : NSSpace)‖ ≤ 2 * M := by
      calc
        ‖q (r • g) - q (0 : NSSpace)‖ ≤
            ‖q (r • g)‖ + ‖q (0 : NSSpace)‖ :=
          norm_sub_le _ _
        _ ≤ M + M := by
          exact add_le_add (SchwartzMap.norm_le_seminorm ℝ q (r • g))
            (SchwartzMap.norm_le_seminorm ℝ q (0 : NSSpace))
        _ = 2 * M := by ring
    have haffnorm : ‖q (r • g) - q (0 : NSSpace) - φ ((r • g) - 0)‖ ≤ 0 := by
      simpa [f, zero_mul] using
        ((convex_univ : Convex ℝ (Set.univ : Set NSSpace)).norm_image_sub_le_of_norm_fderiv_le'
          (f := f)
          (C := 0)
          (s := Set.univ)
          (x := (0 : NSSpace))
          (y := r • g)
          (φ := φ)
          (fun z _hz => hdiff z)
          (fun z _hz => by rw [hfd z, sub_self, norm_zero])
          trivial
          trivial)
    have haffzero : q (r • g) - q (0 : NSSpace) - φ ((r • g) - 0) = 0 := by
      exact norm_eq_zero.mp (le_antisymm haffnorm (norm_nonneg _))
    have hdiff_eq : q (r • g) - q (0 : NSSpace) = φ ((r • g) - 0) := by
      linarith
    have hφg : φ g = ‖g‖ ^ 2 := by
      have h0 : DifferentiableAt ℝ f (0 : NSSpace) := hdiff 0
      calc
        φ g = ⟪gradient f (0 : NSSpace), g⟫ := by
          rw [inner_gradient_left h0]
        _ = ⟪g, g⟫ := rfl
        _ = ‖g‖ ^ 2 := real_inner_self_eq_norm_sq g
    have hphi : φ ((r • g) - 0) = r * ‖g‖ ^ 2 := by
      calc
        φ ((r • g) - 0) = φ (r • g) := by simp
        _ = r * φ g := by simp
        _ = r * ‖g‖ ^ 2 := by rw [hφg]
    have hdiff_val : q (r • g) - q (0 : NSSpace) = 2 * M + 1 := by
      rw [hdiff_eq, hphi, hrmul]
    have hnorm_eq : ‖q (r • g) - q (0 : NSSpace)‖ = 2 * M + 1 := by
      rw [hdiff_val, Real.norm_of_nonneg]
      linarith
    have : 2 * M + 1 ≤ 2 * M := by
      rwa [hnorm_eq] at hbound
    linarith
  intro x
  simpa [f, g, hgzero] using hconst x

/-- Exact zero-flow BKM-data classification for the full
affine-plus-localized pressure class.  The localized pressure term leaves no
extra gauge freedom: zero-flow BKM data exists exactly when the initial
velocity is zero and the affine coefficient cancels the time-scaled Schwartz
pressure gradient at every point of the certified slab. -/
theorem BKMData_zeroVelocity_affineAddScalarSchwartzPressure_iff_initialVelocity_zero_and_pressureGradientBalanceOn
    {ν T : ℝ} {u0 : NSInitialVelocity}
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      u0 = 0 ∧
        ∀ t x, 0 ≤ t → t ≤ T →
          c t + ρ t •
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) t x = 0 := by
  have hp : smoothSpaceTimePressure (affineAddScalarSchwartzPressure c π ρ q) :=
    smoothSpaceTimePressure_affineAddScalarSchwartzPressure hc hπ hρ q
  constructor
  · intro hData
    rcases
        (BKMData_zeroVelocity_iff_initialVelocity_zero_and_spatialPressureGradient_zero
          (ν := ν)
          (T := T)
          (u0 := u0)
          (p := affineAddScalarSchwartzPressure c π ρ q)
          hp).1 hData with
      ⟨hu0, hgrad⟩
    refine ⟨hu0, ?_⟩
    intro t x ht0 htT
    simpa [spatialPressureGradient_affineAddScalarSchwartzPressure
      c π ρ q t x] using hgrad t x ht0 htT
  · rintro ⟨hu0, hbalance⟩
    exact
      (BKMData_zeroVelocity_iff_initialVelocity_zero_and_spatialPressureGradient_zero
        (ν := ν)
        (T := T)
        (u0 := u0)
        (p := affineAddScalarSchwartzPressure c π ρ q)
        hp).2
        ⟨hu0, by
          intro t x ht0 htT
          simpa [spatialPressureGradient_affineAddScalarSchwartzPressure
            c π ρ q t x] using hbalance t x ht0 htT⟩

/-- Constructive zero-flow BKM data for the full affine-plus-localized pressure
class when the pressure-gradient balance holds on the certified slab. -/
theorem BKMData_zeroVelocity_affineAddScalarSchwartzPressure_of_pressureGradientBalanceOn
    {ν T : ℝ}
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ)
    (hbalance :
      ∀ t x, 0 ≤ t → t ≤ T →
        c t + ρ t •
          spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) t x = 0) :
    ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
      W.velocity = (0 : NSVelocityField) ∧
        W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
        ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
          vorticityEnvelopeOn W.velocity T Ω ∧
            integrableVorticityEnvelopeOn Ω T Bint := by
  exact
    (BKMData_zeroVelocity_affineAddScalarSchwartzPressure_iff_initialVelocity_zero_and_pressureGradientBalanceOn
      (ν := ν)
      (T := T)
      (u0 := (0 : NSInitialVelocity))
      c π ρ q hc hπ hρ).2
      ⟨rfl, hbalance⟩

/-- Combined no-go for the full affine-plus-localized pressure class.  Zero
velocity BKM data is impossible if the initial velocity is nonzero or if the
affine-plus-localized pressure-gradient balance fails at one certified slab
point. -/
theorem not_exists_BKMData_zeroVelocity_affineAddScalarSchwartzPressure_of_initialVelocity_ne_zero_or_exists_pressureGradientBalanceFailureOn
    {ν T : ℝ} {u0 : NSInitialVelocity}
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ)
    (hfail :
      u0 ≠ 0 ∨
        ∃ t, ∃ x, 0 ≤ t ∧ t ≤ T ∧
          c t + ρ t •
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) t x ≠ 0) :
    ¬
      (∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) := by
  intro hData
  rcases
      (BKMData_zeroVelocity_affineAddScalarSchwartzPressure_iff_initialVelocity_zero_and_pressureGradientBalanceOn
        (ν := ν) (T := T) (u0 := u0) c π ρ q hc hπ hρ).1 hData with
    ⟨hu0zero, hbalance⟩
  cases hfail with
  | inl hu0 =>
      exact hu0 hu0zero
  | inr hbad =>
      rcases hbad with ⟨t, x, ht0, htT, hneq⟩
      exact hneq (hbalance t x ht0 htT)

/-- A localized Schwartz pressure profile with two different spatial gradients
at a time where its amplitude is nonzero cannot be hidden by choosing an
affine pressure coefficient.  This blocks the main cancellation repair for
zero-flow BKM data in the full affine-plus-localized pressure subclass. -/
theorem not_exists_BKMData_zeroVelocity_affineAddScalarSchwartzPressure_of_initialVelocity_ne_zero_or_exists_nonconstant_schwartzPressureGradientOn
    {ν T : ℝ} {u0 : NSInitialVelocity}
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ)
    (hfail :
      u0 ≠ 0 ∨
        ∃ t, ∃ x, ∃ y, 0 ≤ t ∧ t ≤ T ∧ ρ t ≠ 0 ∧
          spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x ≠
            spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y) :
    ¬
      (∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) := by
  intro hData
  rcases
      (BKMData_zeroVelocity_affineAddScalarSchwartzPressure_iff_initialVelocity_zero_and_pressureGradientBalanceOn
        (ν := ν) (T := T) (u0 := u0) c π ρ q hc hπ hρ).1 hData with
    ⟨hu0zero, hbalance⟩
  cases hfail with
  | inl hu0 =>
      exact hu0 hu0zero
  | inr hnonconstant =>
      rcases hnonconstant with ⟨t, x, y, ht0, htT, hρne, hgradne⟩
      let gx :=
        spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x
      let gy :=
        spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y
      have hx : c t + ρ t • gx = 0 := hbalance t x ht0 htT
      have hy : c t + ρ t • gy = 0 := hbalance t y ht0 htT
      have hsmul : ρ t • (gx - gy) = 0 := by
        calc
          ρ t • (gx - gy) = (c t + ρ t • gx) - (c t + ρ t • gy) := by
            simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
          _ = 0 := by
            rw [hx, hy]
            simp
      rcases smul_eq_zero.mp hsmul with hρzero | hdiff
      · exact hρne hρzero
      · exact hgradne (sub_eq_zero.mp hdiff)

/-- Any full affine-plus-localized zero-flow BKM data with nonzero localized
amplitude at a certified slab time forces the fixed Schwartz pressure profile
to have spatially constant gradient at that time.  This is the exact repair
burden left by the affine cancellation freedom. -/
theorem BKMData_zeroVelocity_affineAddScalarSchwartzPressure_implies_schwartzPressureGradient_constantOn_of_nonzeroAmplitude
    {ν T : ℝ} {u0 : NSInitialVelocity}
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ)
    (hData :
      ∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) :
    ∀ t, 0 ≤ t → t ≤ T → ρ t ≠ 0 →
      ∀ x y,
        spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x =
          spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y := by
  intro t ht0 htT hρne x y
  rcases
      (BKMData_zeroVelocity_affineAddScalarSchwartzPressure_iff_initialVelocity_zero_and_pressureGradientBalanceOn
        (ν := ν) (T := T) (u0 := u0) c π ρ q hc hπ hρ).1 hData with
    ⟨_hu0zero, hbalance⟩
  let gx :=
    spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x
  let gy :=
    spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y
  have hx : c t + ρ t • gx = 0 := hbalance t x ht0 htT
  have hy : c t + ρ t • gy = 0 := hbalance t y ht0 htT
  have hsmul : ρ t • (gx - gy) = 0 := by
    calc
      ρ t • (gx - gy) = (c t + ρ t • gx) - (c t + ρ t • gy) := by
        simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      _ = 0 := by
        rw [hx, hy]
        simp
  rcases smul_eq_zero.mp hsmul with hρzero | hdiff
  · exact False.elim (hρne hρzero)
  · exact sub_eq_zero.mp hdiff

/-- The constant-gradient consequence is even sharper for Schwartz profiles:
at any nonzero-amplitude certified slab time, a full affine-plus-localized
zero-flow BKM datum forces the localized pressure profile's spatial gradient
to vanish everywhere. -/
theorem BKMData_zeroVelocity_affineAddScalarSchwartzPressure_implies_schwartzPressureGradient_zero_of_nonzeroAmplitude
    {ν T : ℝ} {u0 : NSInitialVelocity}
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ)
    (hData :
      ∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) :
    ∀ t, 0 ≤ t → t ≤ T → ρ t ≠ 0 →
      ∀ x,
        spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x = 0 := by
  intro t ht0 htT hρne
  have hconst :=
    BKMData_zeroVelocity_affineAddScalarSchwartzPressure_implies_schwartzPressureGradient_constantOn_of_nonzeroAmplitude
      c π ρ q hc hπ hρ hData t ht0 htT hρne
  have hconstGradient :
      ∀ x : NSSpace,
        gradient (fun z : NSSpace => q z) x =
          gradient (fun z : NSSpace => q z) (0 : NSSpace) := by
    intro x
    simpa [spatialPressureGradient] using hconst x (0 : NSSpace)
  have hzero := schwartzMap_gradient_constant_eq_zero q hconstGradient
  intro x
  simpa [spatialPressureGradient] using hzero x

/-- Therefore a nonzero-amplitude zero-flow BKM datum in the full
affine-plus-localized pressure class also forces the affine pressure
coefficient to vanish at that certified slab time. -/
theorem BKMData_zeroVelocity_affineAddScalarSchwartzPressure_implies_affineCoeff_zero_of_nonzeroAmplitude
    {ν T : ℝ} {u0 : NSInitialVelocity}
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ)
    (hData :
      ∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) :
    ∀ t, 0 ≤ t → t ≤ T → ρ t ≠ 0 → c t = 0 := by
  intro t ht0 htT hρne
  rcases
      (BKMData_zeroVelocity_affineAddScalarSchwartzPressure_iff_initialVelocity_zero_and_pressureGradientBalanceOn
        (ν := ν) (T := T) (u0 := u0) c π ρ q hc hπ hρ).1 hData with
    ⟨_hu0zero, hbalance⟩
  have hgradzero :=
    BKMData_zeroVelocity_affineAddScalarSchwartzPressure_implies_schwartzPressureGradient_zero_of_nonzeroAmplitude
      c π ρ q hc hπ hρ hData t ht0 htT hρne (0 : NSSpace)
  have hbal : c t + ρ t • (0 : NSSpace) = 0 := by
    simpa [hgradzero] using hbalance t (0 : NSSpace) ht0 htT
  simpa using hbal

/-- Exact zero-flow BKM-data classification after the Schwartz constant-gradient
collapse.  The full affine-plus-localized pressure repair can support zero
velocity only when the initial velocity is zero, the affine spatial coefficient
vanishes throughout the certified slab, and any certified nonzero localized
amplitude forces the whole fixed Schwartz pressure gradient to vanish. -/
theorem BKMData_zeroVelocity_affineAddScalarSchwartzPressure_iff_initialVelocity_zero_and_affineCoeff_zeroOn_and_schwartzPressureGradient_zero_if_nonzeroAmplitudeOn
    {ν T : ℝ} {u0 : NSInitialVelocity}
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      u0 = 0 ∧
        (∀ t, 0 ≤ t → t ≤ T → c t = 0) ∧
        ((∃ t, 0 ≤ t ∧ t ≤ T ∧ ρ t ≠ 0) →
          ∀ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x = 0) := by
  constructor
  · intro hData
    rcases
        (BKMData_zeroVelocity_affineAddScalarSchwartzPressure_iff_initialVelocity_zero_and_pressureGradientBalanceOn
          (ν := ν) (T := T) (u0 := u0) c π ρ q hc hπ hρ).1 hData with
      ⟨hu0zero, hbalance⟩
    refine ⟨hu0zero, ?_, ?_⟩
    · intro t ht0 htT
      by_cases hρzero : ρ t = 0
      · have hbal0 : c t + ρ t •
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) t
              (0 : NSSpace) = 0 :=
          hbalance t (0 : NSSpace) ht0 htT
        simpa [hρzero] using hbal0
      · exact
          BKMData_zeroVelocity_affineAddScalarSchwartzPressure_implies_affineCoeff_zero_of_nonzeroAmplitude
            c π ρ q hc hπ hρ hData t ht0 htT hρzero
    · rintro ⟨t, ht0, htT, hρne⟩ s x
      have hzeroAt :=
        BKMData_zeroVelocity_affineAddScalarSchwartzPressure_implies_schwartzPressureGradient_zero_of_nonzeroAmplitude
          c π ρ q hc hπ hρ hData t ht0 htT hρne x
      simpa [spatialPressureGradient] using hzeroAt
  · rintro ⟨hu0zero, hcZero, hgradZeroOfNonzeroAmplitude⟩
    exact
      (BKMData_zeroVelocity_affineAddScalarSchwartzPressure_iff_initialVelocity_zero_and_pressureGradientBalanceOn
        (ν := ν) (T := T) (u0 := u0) c π ρ q hc hπ hρ).2
        ⟨hu0zero, by
          intro t x ht0 htT
          by_cases hρzero : ρ t = 0
          · simp [hcZero t ht0 htT, hρzero]
          · have hgradZero :=
              hgradZeroOfNonzeroAmplitude ⟨t, ht0, htT, hρzero⟩ t x
            simp [hcZero t ht0 htT, hgradZero]⟩
end NavierStokes
end FluidDynamics
end Mettapedia
