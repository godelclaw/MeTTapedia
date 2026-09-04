import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeRealCoherentPairEstimate

/-!
# Rotation covariance of the coherent pancake estimate

The fixed-axis coherent calculation is useful for a spatially varying strain
frame only after proving that no cancellation is tied to those coordinates.
This module packages an oriented Euclidean frame change by its algebraic
invariants and proves that Biot--Savart stretching, coherent polarization, and
the normalized stretching coefficient commute with that frame change.

The final theorem transports the continuous-frequency aperture estimate to
every frozen oriented orthonormal frame.  Handling variation of the frame in
space is a separate commutator problem; it is not hidden in this covariance
statement.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeFrameCovariance

open PancakeRealCoherentPairEstimate

/-- Algebraic data retained by an orientation-preserving Euclidean frame
change.  These are precisely the identities used by the three-dimensional
Biot--Savart strain symbol. -/
structure OrientedFrameEquiv where
  toFun : RealVec3 → RealVec3
  bijective : Function.Bijective toFun
  map_add : ∀ u v, toFun (add u v) = add (toFun u) (toFun v)
  map_smul : ∀ (c : ℝ) u, toFun (smul c u) = smul c (toFun u)
  map_dot : ∀ u v, dot (toFun u) (toFun v) = dot u v
  map_cross : ∀ u v, toFun (cross u v) = cross (toFun u) (toFun v)

def ey : RealVec3 := (0, 1, 0)

def ez : RealVec3 := (0, 0, 1)

/-- Coherent polarization relative to an arbitrary in-plane reference
direction. -/
def coherentWAlong (reference k : RealVec3) : RealVec3 :=
  add (smul (normSq k) reference) (smul (-(dot k reference)) k)

def coherentCoeffAlong (reference k w : RealVec3) : ℝ :=
  dot (coherentWAlong reference k) w /
    normSq (coherentWAlong reference k)

def coherentProjectAlong (reference k w : RealVec3) : RealVec3 :=
  smul (coherentCoeffAlong reference k w) (coherentWAlong reference k)

@[simp]
theorem coherentWAlong_ex (k : RealVec3) :
    coherentWAlong ex k = coherentW k := rfl

theorem OrientedFrameEquiv.map_normSq (F : OrientedFrameEquiv)
    (u : RealVec3) :
    normSq (F.toFun u) = normSq u := by
  exact F.map_dot u u

theorem OrientedFrameEquiv.map_coherentW (F : OrientedFrameEquiv)
    (k : RealVec3) :
    F.toFun (coherentW k) = coherentWAlong (F.toFun ex) (F.toFun k) := by
  unfold coherentW coherentWAlong
  rw [F.map_add, F.map_smul, F.map_smul, F.map_normSq, F.map_dot]

theorem OrientedFrameEquiv.map_coherentProject (F : OrientedFrameEquiv)
    (k w : RealVec3) :
    F.toFun (coherentProject k w) =
      coherentProjectAlong (F.toFun ex) (F.toFun k) (F.toFun w) := by
  unfold coherentProject coherentCoeff coherentProjectAlong coherentCoeffAlong
  rw [F.map_smul, ← F.map_coherentW, F.map_dot, F.map_normSq]

theorem OrientedFrameEquiv.map_biotSavartAmp (F : OrientedFrameEquiv)
    (k w : RealVec3) :
    F.toFun (biotSavartAmp k w) =
      biotSavartAmp (F.toFun k) (F.toFun w) := by
  unfold biotSavartAmp
  rw [F.map_smul, F.map_cross, F.map_normSq]

theorem OrientedFrameEquiv.map_stretchAmp (F : OrientedFrameEquiv)
    (k w₁ w₂ : RealVec3) :
    F.toFun (stretchAmp k w₁ w₂) =
      stretchAmp (F.toFun k) (F.toFun w₁) (F.toFun w₂) := by
  simp only [stretchAmp]
  rw [F.map_smul, F.map_add, F.map_smul, F.map_smul]
  rw [show dot (biotSavartAmp k w₁) w₂ =
      dot (F.toFun (biotSavartAmp k w₁)) (F.toFun w₂) from
        (F.map_dot (biotSavartAmp k w₁) w₂).symm]
  rw [show dot k w₂ = dot (F.toFun k) (F.toFun w₂) from
    (F.map_dot k w₂).symm]
  rw [F.map_biotSavartAmp]

theorem OrientedFrameEquiv.sigmaSq_map (F : OrientedFrameEquiv)
    (k w₁ w₂ : RealVec3) :
    sigmaSq (F.toFun k) (F.toFun w₁) (F.toFun w₂) =
      sigmaSq k w₁ w₂ := by
  unfold sigmaSq
  rw [← F.map_stretchAmp, F.map_normSq, F.map_normSq, F.map_normSq]

theorem dot_ex (k : RealVec3) : dot ex k = k.1 := by
  simp [dot, ex]

theorem dot_ey (k : RealVec3) : dot ey k = k.2.1 := by
  simp [dot, ey]

/-- **Frozen-frame coherent pair estimate.**  For every oriented orthonormal
frame, cone confinement in its two transverse coordinates gives the same
aperture gain as in the fixed coordinate frame. -/
theorem sigmaSq_coherentFrame_le
    (F : OrientedFrameEquiv) (k₁ k₂ : RealVec3) (d₁ d₂ : ℝ)
    (hk₁ : normSq (F.toFun k₁) ≠ 0)
    (hk₂ : normSq (F.toFun k₂) ≠ 0)
    (hcone₁ : dot (F.toFun ex) (F.toFun k₁) ^ 2 +
        dot (F.toFun ey) (F.toFun k₁) ^ 2 ≤
          d₁ * normSq (F.toFun k₁))
    (hcone₂ : dot (F.toFun ex) (F.toFun k₂) ^ 2 +
        dot (F.toFun ey) (F.toFun k₂) ^ 2 ≤
          d₂ * normSq (F.toFun k₂))
    (hd₁ : d₁ ≤ 1 / 4) (hd₂ : d₂ ≤ 1 / 4) :
    sigmaSq (F.toFun k₁)
        (coherentWAlong (F.toFun ex) (F.toFun k₁))
        (coherentWAlong (F.toFun ex) (F.toFun k₂)) ≤
      6 * (d₁ + d₂) := by
  have hk₁' : normSq k₁ ≠ 0 := by
    rwa [F.map_normSq] at hk₁
  have hk₂' : normSq k₂ ≠ 0 := by
    rwa [F.map_normSq] at hk₂
  have hcone₁' : k₁.1 ^ 2 + k₁.2.1 ^ 2 ≤ d₁ * normSq k₁ := by
    rw [F.map_dot, F.map_dot, F.map_normSq, dot_ex, dot_ey] at hcone₁
    exact hcone₁
  have hcone₂' : k₂.1 ^ 2 + k₂.2.1 ^ 2 ≤ d₂ * normSq k₂ := by
    rw [F.map_dot, F.map_dot, F.map_normSq, dot_ex, dot_ey] at hcone₂
    exact hcone₂
  rw [← F.map_coherentW, ← F.map_coherentW, F.sigmaSq_map]
  exact sigmaSq_coherent_le k₁ k₂ d₁ d₂ hk₁' hk₂'
    hcone₁' hcone₂' hd₁ hd₂

/-- **Frozen-frame arbitrary-amplitude estimate.**  Projecting arbitrary
amplitudes onto the coherent lines of a frozen oriented frame retains the
same aperture gain against the original amplitude energies. -/
theorem normSq_stretchAmp_coherentProjectFrame_le_input
    (F : OrientedFrameEquiv) (k₁ k₂ w₁ w₂ : RealVec3) (d₁ d₂ : ℝ)
    (hk₁ : normSq (F.toFun k₁) ≠ 0)
    (hk₂ : normSq (F.toFun k₂) ≠ 0)
    (hcone₁ : dot (F.toFun ex) (F.toFun k₁) ^ 2 +
        dot (F.toFun ey) (F.toFun k₁) ^ 2 ≤
          d₁ * normSq (F.toFun k₁))
    (hcone₂ : dot (F.toFun ex) (F.toFun k₂) ^ 2 +
        dot (F.toFun ey) (F.toFun k₂) ^ 2 ≤
          d₂ * normSq (F.toFun k₂))
    (hd₁ : d₁ ≤ 1 / 4) (hd₂ : d₂ ≤ 1 / 4) :
    normSq (stretchAmp (F.toFun k₁)
        (coherentProjectAlong (F.toFun ex) (F.toFun k₁) (F.toFun w₁))
        (coherentProjectAlong (F.toFun ex) (F.toFun k₂) (F.toFun w₂))) ≤
      6 * (d₁ + d₂) * normSq (F.toFun w₁) * normSq (F.toFun w₂) := by
  have hk₁' : normSq k₁ ≠ 0 := by
    rwa [F.map_normSq] at hk₁
  have hk₂' : normSq k₂ ≠ 0 := by
    rwa [F.map_normSq] at hk₂
  have hcone₁' : k₁.1 ^ 2 + k₁.2.1 ^ 2 ≤ d₁ * normSq k₁ := by
    rw [F.map_dot, F.map_dot, F.map_normSq, dot_ex, dot_ey] at hcone₁
    exact hcone₁
  have hcone₂' : k₂.1 ^ 2 + k₂.2.1 ^ 2 ≤ d₂ * normSq k₂ := by
    rw [F.map_dot, F.map_dot, F.map_normSq, dot_ex, dot_ey] at hcone₂
    exact hcone₂
  have hbase := normSq_stretchAmp_coherentProject_le_input
    k₁ k₂ w₁ w₂ d₁ d₂ hk₁' hk₂'
      hcone₁' hcone₂' hd₁ hd₂
  calc
    normSq (stretchAmp (F.toFun k₁)
        (coherentProjectAlong (F.toFun ex) (F.toFun k₁) (F.toFun w₁))
        (coherentProjectAlong (F.toFun ex) (F.toFun k₂) (F.toFun w₂))) =
        normSq (F.toFun (stretchAmp k₁ (coherentProject k₁ w₁)
          (coherentProject k₂ w₂))) := by
      rw [F.map_stretchAmp, F.map_coherentProject, F.map_coherentProject]
    _ = normSq (stretchAmp k₁ (coherentProject k₁ w₁)
          (coherentProject k₂ w₂)) := F.map_normSq _
    _ ≤ 6 * (d₁ + d₂) * normSq w₁ * normSq w₂ := hbase
    _ = 6 * (d₁ + d₂) * normSq (F.toFun w₁) *
        normSq (F.toFun w₂) := by rw [F.map_normSq, F.map_normSq]

/-- Identity frame canary. -/
def identityFrame : OrientedFrameEquiv where
  toFun := id
  bijective := Function.bijective_id
  map_add := by intros; rfl
  map_smul := by intros; rfl
  map_dot := by intros; rfl
  map_cross := by intros; rfl

end PancakeFrameCovariance
end NavierStokes
end FluidDynamics
end Mettapedia
