import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeGalerkinVorticityBridge
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Noncommuting localization and moving-projection energy

Localized directional energy uses `C* P C`, not `C² P`. The former is
positive for an orthogonal projector even when spatial projection and
frequency localization do not commute.

The strong energy identity below keeps an explicit common domain for
transport and diffusion. These operators need not be bounded on the
ambient real Hilbert space, nor preserve its divergence-free subspace.
No estimate of the resulting commutators or moving-frame rates is assumed
as a conclusion.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeLocalizedQuadraticEnergy

open scoped RealInnerProductSpace BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def localizedEnergy (A : H →L[ℝ] H) (w : H) : ℝ := ⟪w, A w⟫

def sandwich (C P : H →L[ℝ] H) : H →L[ℝ] H := C.adjoint ∘L P ∘L C

theorem sandwich_selfAdjoint (C P : H →L[ℝ] H) (hP : IsSelfAdjoint P) :
    IsSelfAdjoint (sandwich C P) := hP.adjoint_conj C

theorem localizedEnergy_sandwich (C P : H →L[ℝ] H) (w : H) :
    localizedEnergy (sandwich C P) w = ⟪C w, P (C w)⟫ := by
  exact C.adjoint_inner_right w (P (C w))

theorem localizedEnergy_sandwich_eq_norm_sq (C P : H →L[ℝ] H) (w : H)
    (hP : IsSelfAdjoint P) (hP2 : P ∘L P = P) :
    localizedEnergy (sandwich C P) w = ‖P (C w)‖ ^ 2 := by
  rw [localizedEnergy_sandwich]
  have he : P (P (C w)) = P (C w) := congrArg (fun A : H →L[ℝ] H ↦ A (C w)) hP2
  have hp := hP.isSymmetric (C w) (P (C w))
  change ⟪P (C w), P (C w)⟫ = ⟪C w, P (P (C w))⟫ at hp
  rw [he, real_inner_self_eq_norm_sq] at hp
  exact hp.symm

theorem localizedEnergy_sandwich_nonneg (C P : H →L[ℝ] H) (w : H)
    (hP : IsSelfAdjoint P) (hP2 : P ∘L P = P) :
    0 ≤ localizedEnergy (sandwich C P) w := by
  rw [localizedEnergy_sandwich_eq_norm_sq C P w hP hP2]
  positivity

theorem sandwich_complement (C P : H →L[ℝ] H) :
    sandwich C P + sandwich C (1 - P) = C.adjoint ∘L C := by
  ext w
  simp [sandwich]

theorem localizedEnergy_complement (C P : H →L[ℝ] H) (w : H) :
    localizedEnergy (sandwich C P) w + localizedEnergy (sandwich C (1 - P)) w = ‖C w‖ ^ 2 := by
  rw [localizedEnergy_sandwich, localizedEnergy_sandwich]
  simp [inner_sub_right]

theorem hasDerivAt_localizedEnergy (A : ℝ → H →L[ℝ] H) (Adot : H →L[ℝ] H)
    (w : ℝ → H) (wdot : H) (t : ℝ)
    (hA : HasDerivAt A Adot t) (hw : HasDerivAt w wdot t) (hs : IsSelfAdjoint (A t)) :
    HasDerivAt (fun tau ↦ localizedEnergy (A tau) (w tau))
      (⟪w t, Adot (w t)⟫ + 2 * ⟪A t (w t), wdot⟫) t := by
  have h := hw.inner ℝ (hA.clm_apply hw)
  have ha := hs.isSymmetric (w t) wdot
  change ⟪A t (w t), wdot⟫ = ⟪w t, A t wdot⟫ at ha
  have he : ⟪w t, Adot (w t) + A t wdot⟫ + ⟪wdot, A t (w t)⟫ =
      ⟪w t, Adot (w t)⟫ + 2 * ⟪A t (w t), wdot⟫ := by
    rw [inner_add_right, ← ha, real_inner_comm (A t (w t)) wdot]
    ring
  rw [he] at h
  exact h

/-- Transport and diffusion may be unbounded: their integration-by-parts
identities are required only on the displayed common core. -/
theorem localizedEnergy_evolution_rate
    (A Adot : H →L[ℝ] H) (w stretch : H) (B D : H → H) (nu : ℝ)
    (core : Set H) (hw : w ∈ core) (hAw : A w ∈ core)
    (hA : IsSelfAdjoint A)
    (hB : ∀ x ∈ core, ∀ y ∈ core, ⟪B x, y⟫ = -⟪x, B y⟫)
    (hD : ∀ x ∈ core, ∀ y ∈ core, ⟪D x, y⟫ = ⟪x, D y⟫) :
    ⟪w, Adot w⟫ + 2 * ⟪A w, -B w + stretch + nu • D w⟫ =
      ⟪w, Adot w⟫ + ⟪w, B (A w) - A (B w)⟫ + 2 * ⟪A w, stretch⟫ +
        nu * ⟪w, A (D w) + D (A w)⟫ := by
  have haB := hA.isSymmetric w (B w)
  have haD := hA.isSymmetric w (D w)
  have hb := hB w hw (A w) hAw
  have hd := hD w hw (A w) hAw
  change ⟪A w, B w⟫ = ⟪w, A (B w)⟫ at haB
  change ⟪A w, D w⟫ = ⟪w, A (D w)⟫ at haD
  rw [real_inner_comm (A w) (B w)] at hb
  rw [real_inner_comm (A w) (D w)] at hd
  simp only [inner_add_right, inner_sub_right, inner_neg_right, inner_smul_right]
  rw [← haB, ← haD, ← hd]
  have hb' : ⟪w, B (A w)⟫ = -⟪A w, B w⟫ := by linarith
  rw [hb']
  ring

theorem hasDerivAt_localizedEnergy_evolution
    (A : ℝ → H →L[ℝ] H) (Adot : H →L[ℝ] H) (w : ℝ → H)
    (B D : H → H) (stretch : H) (nu t : ℝ)
    (core : Set H) (hwcore : w t ∈ core) (hAwcore : A t (w t) ∈ core)
    (hA : HasDerivAt A Adot t) (hs : IsSelfAdjoint (A t))
    (hw : HasDerivAt w (-B (w t) + stretch + nu • D (w t)) t)
    (hB : ∀ x ∈ core, ∀ y ∈ core, ⟪B x, y⟫ = -⟪x, B y⟫)
    (hD : ∀ x ∈ core, ∀ y ∈ core, ⟪D x, y⟫ = ⟪x, D y⟫) :
    HasDerivAt (fun tau ↦ localizedEnergy (A tau) (w tau))
      (⟪w t, Adot (w t)⟫ + ⟪w t, B (A t (w t)) - A t (B (w t))⟫ +
        2 * ⟪A t (w t), stretch⟫ +
        nu * ⟪w t, A t (D (w t)) + D (A t (w t))⟫) t := by
  have h := hasDerivAt_localizedEnergy A Adot w _ t hA hw hs
  rw [localizedEnergy_evolution_rate (A t) Adot (w t) stretch B D nu core hwcore hAwcore hs hB hD] at h
  exact h

/-- Separate motion of the frequency localizer and directional projector. -/
def sandwichMotionRate (C Cdot P Pdot : H →L[ℝ] H) (w : H) : ℝ :=
  2 * ⟪P (C w), Cdot w⟫ + ⟪C w, Pdot (C w)⟫

theorem hasDerivAt_sandwichEnergy
    (C P : ℝ → H →L[ℝ] H) (Cdot Pdot : H →L[ℝ] H)
    (w : ℝ → H) (wdot : H) (t : ℝ)
    (hC : HasDerivAt C Cdot t) (hP : HasDerivAt P Pdot t)
    (hw : HasDerivAt w wdot t) (hs : IsSelfAdjoint (P t)) :
    HasDerivAt (fun tau ↦ localizedEnergy (sandwich (C tau) (P tau)) (w tau))
      (sandwichMotionRate (C t) Cdot (P t) Pdot (w t) +
        2 * ⟪sandwich (C t) (P t) (w t), wdot⟫) t := by
  have h := hasDerivAt_localizedEnergy P Pdot (fun tau ↦ C tau (w tau))
    (Cdot (w t) + C t wdot) t hP (hC.clm_apply hw) hs
  convert h using 1
  · funext tau
    exact localizedEnergy_sandwich (C tau) (P tau) (w tau)
  · dsimp only [sandwichMotionRate]
    rw [inner_add_right, ← (C t).adjoint_inner_left wdot (P t (C t (w t)))]
    change _ + 2 * ⟪(C t).adjoint (P t (C t (w t))), wdot⟫ = _
    ring

theorem hasDerivAt_sandwichEnergy_evolution
    (C P : ℝ → H →L[ℝ] H) (Cdot Pdot : H →L[ℝ] H) (w : ℝ → H)
    (B D : H → H) (stretch : H) (nu t : ℝ)
    (core : Set H) (hwcore : w t ∈ core)
    (hAwcore : sandwich (C t) (P t) (w t) ∈ core)
    (hC : HasDerivAt C Cdot t) (hP : HasDerivAt P Pdot t) (hs : IsSelfAdjoint (P t))
    (hw : HasDerivAt w (-B (w t) + stretch + nu • D (w t)) t)
    (hB : ∀ x ∈ core, ∀ y ∈ core, ⟪B x, y⟫ = -⟪x, B y⟫)
    (hD : ∀ x ∈ core, ∀ y ∈ core, ⟪D x, y⟫ = ⟪x, D y⟫) :
    HasDerivAt (fun tau ↦ localizedEnergy (sandwich (C tau) (P tau)) (w tau))
      (sandwichMotionRate (C t) Cdot (P t) Pdot (w t) +
        ⟪w t, B (sandwich (C t) (P t) (w t)) - sandwich (C t) (P t) (B (w t))⟫ +
        2 * ⟪sandwich (C t) (P t) (w t), stretch⟫ +
        nu * ⟪w t, sandwich (C t) (P t) (D (w t)) + D (sandwich (C t) (P t) (w t))⟫) t := by
  have he := localizedEnergy_evolution_rate (sandwich (C t) (P t)) 0 (w t) stretch B D nu
    core hwcore hAwcore (sandwich_selfAdjoint _ _ hs) hB hD
  simp only [zero_apply, inner_zero_right, zero_add] at he
  have h := hasDerivAt_sandwichEnergy C P Cdot Pdot w _ t hC hP hw hs
  rw [he] at h
  convert h using 1
  ring

omit [CompleteSpace H] in
/-- Complementary directional sectors cancel projector motion exactly.
The common localizer's motion survives until its own partition is summed. -/
theorem sandwichMotionRate_complement (C Cdot P Pdot : H →L[ℝ] H) (w : H) :
    sandwichMotionRate C Cdot P Pdot w + sandwichMotionRate C Cdot (1 - P) (-Pdot) w =
      2 * ⟪C w, Cdot w⟫ := by
  simp only [sandwichMotionRate, sub_apply, one_apply_eq_self,
    neg_apply, inner_sub_left, inner_neg_right]
  ring

/-- Motion relative to advection: `Cdot + [B,C]` and `Pdot + [B,P]`
are kept distinct. Their estimates have different geometric content. -/
def materialMotionRate (C Cdot P Pdot : H →L[ℝ] H) (B : H → H) (w : H) : ℝ :=
  2 * ⟪P (C w), Cdot w + B (C w) - C (B w)⟫ +
    ⟪C w, Pdot (C w) + B (P (C w)) - P (B (C w))⟫

theorem sandwichMotionRate_add_transport
    (C Cdot P Pdot : H →L[ℝ] H) (B : H → H) (w : H)
    (core : Set H) (hw : w ∈ core) (hAw : sandwich C P w ∈ core)
    (hCw : C w ∈ core) (hPCw : P (C w) ∈ core)
    (hP : IsSelfAdjoint P)
    (hB : ∀ x ∈ core, ∀ y ∈ core, ⟪B x, y⟫ = -⟪x, B y⟫) :
    sandwichMotionRate C Cdot P Pdot w +
      ⟪w, B (sandwich C P w) - sandwich C P (B w)⟫ =
        materialMotionRate C Cdot P Pdot B w := by
  have ha := (sandwich_selfAdjoint C P hP).isSymmetric w (B w)
  change ⟪sandwich C P w, B w⟫ = ⟪w, sandwich C P (B w)⟫ at ha
  have hb := hB w hw (sandwich C P w) hAw
  rw [real_inner_comm (sandwich C P w) (B w)] at hb
  have hbc := hB (C w) hCw (P (C w)) hPCw
  rw [real_inner_comm (P (C w)) (B (C w))] at hbc
  have hp := hP.isSymmetric (C w) (B (C w))
  change ⟪P (C w), B (C w)⟫ = ⟪C w, P (B (C w))⟫ at hp
  have hadj : ⟪sandwich C P w, B w⟫ = ⟪P (C w), C (B w)⟫ :=
    C.adjoint_inner_left (B w) (P (C w))
  simp only [sandwichMotionRate, materialMotionRate, inner_add_right, inner_sub_right]
  rw [← ha, ← hp, ← hadj]
  linarith

theorem hasDerivAt_sandwichEnergy_material
    (C P : ℝ → H →L[ℝ] H) (Cdot Pdot : H →L[ℝ] H) (w : ℝ → H)
    (B D : H → H) (stretch : H) (nu t : ℝ)
    (core : Set H) (hwcore : w t ∈ core)
    (hAwcore : sandwich (C t) (P t) (w t) ∈ core)
    (hCwcore : C t (w t) ∈ core) (hPCwcore : P t (C t (w t)) ∈ core)
    (hC : HasDerivAt C Cdot t) (hP : HasDerivAt P Pdot t) (hs : IsSelfAdjoint (P t))
    (hw : HasDerivAt w (-B (w t) + stretch + nu • D (w t)) t)
    (hB : ∀ x ∈ core, ∀ y ∈ core, ⟪B x, y⟫ = -⟪x, B y⟫)
    (hD : ∀ x ∈ core, ∀ y ∈ core, ⟪D x, y⟫ = ⟪x, D y⟫) :
    HasDerivAt (fun tau ↦ localizedEnergy (sandwich (C tau) (P tau)) (w tau))
      (materialMotionRate (C t) Cdot (P t) Pdot B (w t) +
        2 * ⟪sandwich (C t) (P t) (w t), stretch⟫ +
        nu * ⟪w t, sandwich (C t) (P t) (D (w t)) + D (sandwich (C t) (P t) (w t))⟫) t := by
  have h := hasDerivAt_sandwichEnergy_evolution C P Cdot Pdot w B D stretch nu t
    core hwcore hAwcore hC hP hs hw hB hD
  rw [sandwichMotionRate_add_transport (C t) Cdot (P t) Pdot B (w t) core
    hwcore hAwcore hCwcore hPCwcore hs hB] at h
  exact h

/-- A complete finite operator partition cancels signed transport transfer
on the common core, without assuming its individual commutators vanish. -/
theorem partition_transport_commutator_zero {ι : Type*} (cells : Finset ι)
    (A : ι → H →L[ℝ] H) (B : H → H) (w : H) (core : Set H)
    (hw : w ∈ core) (hAw : ∀ a ∈ cells, A a w ∈ core)
    (hA : ∀ a ∈ cells, IsSelfAdjoint (A a))
    (hB : ∀ x ∈ core, ∀ y ∈ core, ⟪B x, y⟫ = -⟪x, B y⟫)
    (hp : ∑ a ∈ cells, A a = 1) :
    ∑ a ∈ cells, ⟪w, B (A a w) - A a (B w)⟫ = 0 := by
  have hpair (a : ι) (ha : a ∈ cells) :
      ⟪w, B (A a w) - A a (B w)⟫ = -2 * ⟪A a w, B w⟫ := by
    have hb := hB w hw (A a w) (hAw a ha)
    have hs := (hA a ha).isSymmetric w (B w)
    change ⟪A a w, B w⟫ = ⟪w, A a (B w)⟫ at hs
    rw [real_inner_comm (A a w) (B w)] at hb
    rw [inner_sub_right, ← hs]
    linarith
  simp_rw [Finset.sum_congr rfl hpair, ← Finset.mul_sum, ← sum_inner]
  have he : (∑ a ∈ cells, A a w) = w := by
    simpa only [sum_apply, one_apply_eq_self] using
      congrArg (fun F : H →L[ℝ] H ↦ F w) hp
  rw [he]
  have hz := hB w hw w hw
  rw [real_inner_comm w (B w)] at hz
  linarith

omit [CompleteSpace H] in
theorem partition_motion_rate_zero {ι : Type*} (cells : Finset ι)
    (A : ℝ → ι → H →L[ℝ] H) (Adot : ι → H →L[ℝ] H) (t : ℝ) (w : H)
    (hd : ∀ a ∈ cells, HasDerivAt (fun tau ↦ A tau a) (Adot a) t)
    (hp : ∀ tau, ∑ a ∈ cells, A tau a = 1) :
    ∑ a ∈ cells, ⟪w, Adot a w⟫ = 0 := by
  have h := HasDerivAt.fun_sum hd
  have he : (fun tau ↦ ∑ a ∈ cells, A tau a) = (fun _ : ℝ ↦ (1 : H →L[ℝ] H)) := funext hp
  rw [he] at h
  have hz := h.unique (hasDerivAt_const t (1 : H →L[ℝ] H))
  rw [← inner_sum]
  have hzero : (∑ a ∈ cells, Adot a w) = 0 := by
    simpa only [sum_apply, zero_apply] using
      congrArg (fun F : H →L[ℝ] H ↦ F w) hz
  rw [hzero, inner_zero_right]

end Mettapedia.FluidDynamics.NavierStokes.PancakeLocalizedQuadraticEnergy
