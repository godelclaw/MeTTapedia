import Mettapedia.Computability.PNP.PostSwitchResidualWitnessSupport
import Mettapedia.Computability.PNP.ResidualSideInformationResolutionCostInvariantPerfect

/-!
# Active post-switch residual advantage and fork obstruction
-/

namespace Mettapedia.Computability.PNP

section

variable {Z : Type*}

/-- The active two-point exact post-switch witness is correct on every
positive-weight point, so the abstract invariant-base exact-success theorem
already forces the whole supported mass to be orbit-resolving mass. -/
theorem resolvedMass_activeOrbit_eq_weightedTotalMass
    [Fintype Z] (z0 : Z) :
    resolvedMass tiInputMap
      (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b)
      (activeOrbitWeight z0) =
    weightedTotalMass (activeOrbitWeight z0) := by
  exact
    resolvedMass_eq_weightedTotalMass_of_supportwise_correct_invariant_base
      tiInputMap
      invariantVisibleData
      (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b)
      activeOrbitTarget
      (activeOrbitWeight z0)
      activeOrbitClassifier
      invariantVisibleData_tiInputMap
      (activeOrbitTarget_flip_of_positiveWeight z0)
      (activeOrbitWeight_tiInputMap z0)
      (activeOrbitCorrect_of_positiveWeight z0)

/-- On the exact active two-point post-switch witness, every supported point is
resolved by the retained side bit, so the resolved mass is the whole support
mass. -/
theorem resolvedMass_activeOrbit_eq_two
    [Fintype Z] (z0 : Z) :
    resolvedMass tiInputMap
      (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b)
      (activeOrbitWeight z0) = 2 := by
  rw [resolvedMass_activeOrbit_eq_weightedTotalMass (Z := Z) z0,
    weightedTotalMass_activeOrbitWeight (Z := Z) z0]

theorem doubledAdvantage_activeOrbit_eq_two
    [Fintype Z] (z0 : Z) :
    doubledAdvantage
        activeOrbitFeatures
        activeOrbitTarget
        (activeOrbitWeight z0)
        activeOrbitClassifier
      = 2 := by
  rw [doubledAdvantage_eq_weightedTotalMass_of_supportwise_correct
    activeOrbitFeatures
    activeOrbitTarget
    (activeOrbitWeight z0)
    activeOrbitClassifier
    (activeOrbitCorrect_of_positiveWeight z0)]
  exact weightedTotalMass_activeOrbitWeight (Z := Z) z0

theorem doubledAdvantage_activeOrbit_eq_resolvedMass
    [Fintype Z] (z0 : Z) :
    doubledAdvantage
        activeOrbitFeatures
        activeOrbitTarget
        (activeOrbitWeight z0)
        activeOrbitClassifier =
      resolvedMass tiInputMap
        (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b)
        (activeOrbitWeight z0) := by
  exact
    doubledAdvantage_eq_resolvedMass_of_supportwise_correct_invariant_base
      tiInputMap
      invariantVisibleData
      (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b)
      activeOrbitTarget
      (activeOrbitWeight z0)
      activeOrbitClassifier
      invariantVisibleData_tiInputMap
      (activeOrbitTarget_flip_of_positiveWeight z0)
      (activeOrbitWeight_tiInputMap z0)
      (activeOrbitCorrect_of_positiveWeight z0)

theorem pos_doubledAdvantage_activeOrbit
    [Fintype Z] (z0 : Z) :
    0 <
      doubledAdvantage
        activeOrbitFeatures
        activeOrbitTarget
        (activeOrbitWeight z0)
        activeOrbitClassifier := by
  rw [doubledAdvantage_activeOrbit_eq_two (Z := Z) z0]
  decide

theorem total_lt_two_mul_weightedCorrectMass_activeOrbit
    [Fintype Z] (z0 : Z) :
    weightedTotalMass (activeOrbitWeight z0) <
      2 * weightedCorrectMass
        activeOrbitFeatures
        activeOrbitTarget
        (activeOrbitWeight z0)
        activeOrbitClassifier := by
  have hcorrect :=
    weightedCorrectMass_activeOrbit_eq_weightedTotalMass (Z := Z) z0
  have htotal := weightedTotalMass_activeOrbitWeight (Z := Z) z0
  omega

theorem pos_nonzeroColumnMass_activeOrbit
    [Fintype Z] (z0 : Z) :
    0 <
      sliceMass
        (fun u : ExactVisiblePostSwitchSurface Z 1 => nonzeroColumn u.a)
        (activeOrbitWeight z0) := by
  classical
  let u0 :
      {u : ExactVisiblePostSwitchSurface Z 1 // nonzeroColumn u.a} :=
    ⟨activeOrbitInputFalse z0, ⟨0, by simp [activeOrbitInputFalse, oneBitVec_apply]⟩⟩
  have hterm : 0 < activeOrbitWeight z0 u0.1 := by
    simp [u0, activeOrbitWeight]
  unfold sliceMass
  have hle :
      activeOrbitWeight z0 u0.1 ≤
        ∑ u :
          {u : ExactVisiblePostSwitchSurface Z 1 // nonzeroColumn u.a},
            activeOrbitWeight z0 u.1 := by
    simpa [u0] using
      (Finset.single_le_sum
        (fun u _ => Nat.zero_le (activeOrbitWeight z0 u.1))
        (Finset.mem_univ u0))
  exact lt_of_lt_of_le hterm hle

theorem not_exactInputInvariantWeightedSupport_activeOrbit
    (z0 : Z) :
    ¬ exactInputInvariantWeightedSupport (activeOrbitWeight z0) := by
  intro hsupport
  have hpos : 0 < activeOrbitWeight z0 (activeOrbitInputFalse z0) := by
    simp [activeOrbitWeight]
  have hfix := hsupport (activeOrbitInputFalse z0) hpos
  have hneq : tiInputMap (activeOrbitInputFalse z0) ≠ activeOrbitInputFalse z0 := by
    simpa using (activeOrbitInputFalse_ne_inputTrue z0).symm
  exact hneq hfix

theorem exactPostSwitch_activeOrbit_forces_fork_obstruction
    [Fintype Z] (z0 : Z) :
    weightedTotalMass (activeOrbitWeight z0) <
        2 * weightedCorrectMass
          activeOrbitFeatures
          activeOrbitTarget
          (activeOrbitWeight z0)
          activeOrbitClassifier ∧
      0 <
        sliceMass
          (fun u : ExactVisiblePostSwitchSurface Z 1 => nonzeroColumn u.a)
          (activeOrbitWeight z0) ∧
      ¬ exactInputInvariantWeightedSupport (activeOrbitWeight z0) := by
  refine ⟨total_lt_two_mul_weightedCorrectMass_activeOrbit (Z := Z) z0,
    pos_nonzeroColumnMass_activeOrbit (Z := Z) z0,
    not_exactInputInvariantWeightedSupport_activeOrbit (Z := Z) z0⟩

end

end Mettapedia.Computability.PNP
