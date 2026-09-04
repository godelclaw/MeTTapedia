import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeCoherentPairEstimate
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.DyadicPancakeClosure

/-
# The misalignment-refined pin

This module commits the outcome of the 2026-09-04 adjudication campaign
on the open pin `ScaleLocalPancakeStrainBudget`: a strictly sharper
named pin, together with the machine-checked kinematics that justify
the sharpening and the exact statement of what remains unproven.

**Proven side (kinematics, sealed).**
* `PancakeConeDirectionDichotomy`: wavevector-cone confinement alone
  gives no pairwise depletion (worst pair saturates `sigma^2 = 1/4` at
  every aperture), while the direction-aligned polarization of the same
  pair depletes with a full inverse-square frequency power.
* `PancakeCoherentPairEstimate.sigmaSq_coherent_le`: two
  direction-coherent cone modes with squared tilts `d1, d2 ≤ 1/4`
  stretch each other with `sigma^2 ≤ 6 (d1 + d2)`.
* `sum_sigmaSq_coherent_le` (this module): the same bound aggregates
  over any finite family of coherent source modes, giving the
  Schur-type block estimate `Σ sigma^2 ≤ card * 6 (d1 + d2)`.

**The refined pin.**  `CoherentMisalignmentSplitData` splits the
pancake-sector stretching functional into a direction-coherent share —
carrying the interface `coherent_le`, the abstract form of the proven
aperture-gain kinematics — and a misalignment share.
`MisalignmentStrainBudget` demands the time-integrable envelope ONLY
for the misalignment share.  The sealed implication
`scaleLocalPancakeStrainBudget_of_misalignmentBudget` shows the refined
pin plus the coherent interface reproduces the original pin with gain
`coherentGain + ε`.  The refinement is strict: the original pin
demanded the envelope for the full pancake sum; the burden now rests
only on the misalignment share, whose controlling quantity is the
vorticity-direction variation — the Constantin–Fefferman coherence
integrand, which unlike the full strain has known dynamical handles.

**Unproven boundary (exact).**
1. The field-level transfer: realizing `split_le` and `coherent_le`
   for actual Navier–Stokes Littlewood–Paley data from the mode-level
   kinematics proved here (a coherent/misaligned decomposition of real
   vorticity fields with quantitative constants).
2. `MisalignmentStrainBudget` itself: the dynamical, time-integrated
   control of the misalignment share.  The checked fences apply: it
   cannot be proved by operator-norm, frozen-strain, or static
   arguments.

This is a route reduction, not a proof of any part of Navier–Stokes
regularity.
-/

set_option autoImplicit false

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace MisalignmentRefinedPin

open PancakeConeDirectionDichotomy
open PancakeCoherentPairEstimate

/-! ## The aggregated kinematic estimate (proved) -/

/-- **Blockwise Schur aggregation of the coherent pair estimate.**  For
any finite family of direction-coherent source modes inside the cone of
squared aperture `d1`, acting on one coherent receiver inside the cone
of squared aperture `d2`, the summed squared stretching coefficients
obey the count-times-gain bound. -/
theorem sum_sigmaSq_coherent_le {ι : Type*} (s : Finset ι)
    (k : ι → Vec3) (k2 : Vec3) (d1 d2 : ℚ)
    (hk : ∀ i ∈ s, normSq (k i) ≠ 0) (hk2 : normSq k2 ≠ 0)
    (hcone : ∀ i ∈ s, (k i).1 ^ 2 + (k i).2.1 ^ 2 ≤ d1 * normSq (k i))
    (hcone2 : k2.1 ^ 2 + k2.2.1 ^ 2 ≤ d2 * normSq k2)
    (hd1 : d1 ≤ 1 / 4) (hd2 : d2 ≤ 1 / 4) :
    ∑ i ∈ s, sigmaSq (k i) (coherentW (k i)) (coherentW k2) ≤
      s.card * (6 * (d1 + d2)) := by
  calc ∑ i ∈ s, sigmaSq (k i) (coherentW (k i)) (coherentW k2)
      ≤ ∑ _i ∈ s, 6 * (d1 + d2) := by
        apply Finset.sum_le_sum
        intro i hi
        exact sigmaSq_coherent_le (k i) k2 d1 d2 (hk i hi) hk2
          (hcone i hi) hcone2 hd1 hd2
    _ = s.card * (6 * (d1 + d2)) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-! ## The refined pin -/

/-- A coherent/misalignment split of the pancake-sector stretching
functional.  `coherent_le` is the abstract interface of the proven
aperture-gain kinematics (`sigmaSq_coherent_le`,
`sum_sigmaSq_coherent_le`); realizing it for actual Littlewood–Paley
Navier–Stokes data is the first item of the unproven boundary recorded
in the module docstring. -/
structure CoherentMisalignmentSplitData
    (D : DyadicVorticityStretchingData) where
  /-- The direction-coherent share of the pancake stretching sum. -/
  coherentStretchSum : ℝ → ℝ
  coherentStretchSum_nonneg : ∀ t, 0 ≤ coherentStretchSum t
  /-- The misalignment share of the pancake stretching sum. -/
  misalignStretchSum : ℝ → ℝ
  misalignStretchSum_nonneg : ∀ t, 0 ≤ misalignStretchSum t
  misalignStretchSum_integrable :
    IntervalIntegrable misalignStretchSum MeasureTheory.volume 0 D.T
  /-- The split dominates the pancake functional. -/
  split_le : ∀ t ∈ Set.Icc (0 : ℝ) D.T,
    D.pancakeStretchSum t ≤ coherentStretchSum t + misalignStretchSum t
  /-- The aperture gain of the coherent share. -/
  coherentGain : ℝ
  coherentGain_nonneg : 0 ≤ coherentGain
  /-- The coherent share obeys the proven aperture-gain bound against
  the high-frequency block sum. -/
  coherent_le : ∀ t ∈ Set.Icc (0 : ℝ) D.T,
    coherentStretchSum t ≤ coherentGain * D.highBlockSum t

/-- **The strictly sharper pin.**  A time-integrable envelope is
demanded only for the misalignment share of the pancake stretching
functional. -/
def MisalignmentStrainBudget (D : DyadicVorticityStretchingData)
    (split : CoherentMisalignmentSplitData D) (B ε : ℝ) : Prop :=
  ∃ budget : ℝ → ℝ,
    IntervalIntegrable budget MeasureTheory.volume 0 D.T ∧
    (∫ t in (0 : ℝ)..D.T, budget t) ≤ B ∧
    ∀ t ∈ Set.Icc (0 : ℝ) D.T,
      split.misalignStretchSum t ≤ budget t + ε * D.highBlockSum t

/-- **The reduction.**  The misalignment budget, through the coherent
interface, reproduces the original scale-local pancake strain budget
with gain `coherentGain + ε`.  The original pin's burden on the full
pancake sum is thereby strictly reduced to its misalignment share. -/
theorem scaleLocalPancakeStrainBudget_of_misalignmentBudget
    (D : DyadicVorticityStretchingData)
    (split : CoherentMisalignmentSplitData D) {B ε : ℝ}
    (hb : MisalignmentStrainBudget D split B ε) :
    ScaleLocalPancakeStrainBudget D B (split.coherentGain + ε) := by
  obtain ⟨budget, hint, hB, hpt⟩ := hb
  refine ⟨budget, hint, hB, ?_⟩
  intro t ht
  have h1 := split.split_le t ht
  have h2 := split.coherent_le t ht
  have h3 := hpt t ht
  have := D.highBlockSum_nonneg t
  nlinarith [h1, h2, h3]

/-- Rest canary: the refined hypotheses are simultaneously satisfiable
(the all-zero split of any data with vanishing pancake functional). -/
theorem rest_misalignmentBudget
    (D : DyadicVorticityStretchingData)
    (hzero : ∀ t, D.pancakeStretchSum t = 0) :
    ∃ split : CoherentMisalignmentSplitData D,
      MisalignmentStrainBudget D split 0 0 := by
  refine ⟨⟨fun _ => 0, fun _ => le_refl 0, fun _ => 0, fun _ => le_refl 0,
    intervalIntegrable_const, ?_, 0, le_refl 0, ?_⟩, ?_⟩
  · intro t _
    rw [hzero t]
    norm_num
  · intro t _
    simp
  · refine ⟨fun _ => 0, intervalIntegrable_const, by simp, ?_⟩
    intro t _
    simp

end MisalignmentRefinedPin
end NavierStokes
end FluidDynamics
end Mettapedia
