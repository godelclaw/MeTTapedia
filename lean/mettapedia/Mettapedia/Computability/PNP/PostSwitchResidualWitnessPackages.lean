import Mettapedia.Computability.PNP.PostSwitchResidualWitnessAdvantage
import Mettapedia.Computability.PNP.ResidualSideInformationResolutionCostBalancingCollapse

/-!
# Active post-switch residual package witnesses
-/

namespace Mettapedia.Computability.PNP

section

variable {Z : Type*}

theorem exists_positive_prediction_separation_activeOrbit
    (z0 : Z) :
    ∃ u : ExactVisiblePostSwitchSurface Z 1,
      0 < activeOrbitWeight z0 u ∧
      activeOrbitClassifier (activeOrbitFeatures (tiInputMap u)) ≠
        activeOrbitClassifier (activeOrbitFeatures u) := by
  classical
  refine ⟨activeOrbitInputFalse z0, by simp [activeOrbitWeight], ?_⟩
  simp [activeOrbitFeatures, activeOrbitClassifier]

theorem exists_positive_same_base_ne_side_activeOrbit
    (z0 : Z) :
    ∃ u : ExactVisiblePostSwitchSurface Z 1,
      0 < activeOrbitWeight z0 u ∧
      invariantVisibleData (tiInputMap u) = invariantVisibleData u ∧
      (tiInputMap u).b ≠ u.b := by
  classical
  refine ⟨activeOrbitInputFalse z0, by simp [activeOrbitWeight], ?_, ?_⟩
  · rfl
  · intro h
    have h0 := congrArg (fun b : BitVec 1 => b 0) h
    simp at h0

/-- The active two-point exact post-switch witness has positive ordinary
orbit-resolving mass for the retained side bit itself. -/
theorem pos_resolvedMass_activeOrbit
    [Fintype Z]
    (z0 : Z) :
    0 < resolvedMass tiInputMap (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b)
      (activeOrbitWeight z0) := by
  rw [resolvedMass_activeOrbit_eq_two (Z := Z) z0]
  decide

/-- On the exact visible post-switch surface, positive resolving mass for the
retained side bit already forces the pure residual obstruction package. -/
theorem exactPostSwitch_pos_resolvedMass_forces_pure_residual_obstruction_package
    [Fintype Z]
    (w : ExactVisiblePostSwitchSurface Z 1 → ℕ)
    (hmass :
      0 < resolvedMass tiInputMap (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b) w) :
    ¬ SideInfoDeterminedBy invariantVisibleData
        (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b) ∧
      PositiveWeightSideInfoCollisionOverBase invariantVisibleData
        (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b) w ∧
      (∃ u : ExactVisiblePostSwitchSurface Z 1,
        0 < w u ∧
          invariantVisibleData (tiInputMap u) = invariantVisibleData u ∧
          (tiInputMap u).b ≠ u.b) ∧
      (∃ u : ExactVisiblePostSwitchSurface Z 1,
        0 < w u ∧
          ¬ SourceOnlyPredicateCapturesSideEq
            invariantVisibleData
            (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b) (u.b)) := by
  simpa [invariantVisibleData] using
    pos_resolvedMass_obstruction_package_invariant_base
      tiInputMap
      invariantVisibleData
      (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b)
      w
      invariantVisibleData_tiInputMap
      hmass

/-- The concrete active two-point exact post-switch witness already realizes
the pure residual obstruction package, before any classifier-level
prediction-separation fact is invoked. -/
theorem exactPostSwitch_activeOrbit_realizes_pure_residual_obstruction_package
    [Fintype Z] (z0 : Z) :
    0 < resolvedMass tiInputMap (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b)
        (activeOrbitWeight z0) ∧
      ¬ SideInfoDeterminedBy invariantVisibleData
          (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b) ∧
      PositiveWeightSideInfoCollisionOverBase
        invariantVisibleData
        (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b)
        (activeOrbitWeight z0) ∧
      (∃ u : ExactVisiblePostSwitchSurface Z 1,
        0 < activeOrbitWeight z0 u ∧
          invariantVisibleData (tiInputMap u) = invariantVisibleData u ∧
          (tiInputMap u).b ≠ u.b) ∧
      (∃ u : ExactVisiblePostSwitchSurface Z 1,
        0 < activeOrbitWeight z0 u ∧
          ¬ SourceOnlyPredicateCapturesSideEq
            invariantVisibleData
            (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b) (u.b)) := by
  have hmass := pos_resolvedMass_activeOrbit (Z := Z) z0
  refine ⟨hmass, ?_⟩
  exact
    exactPostSwitch_pos_resolvedMass_forces_pure_residual_obstruction_package
      (Z := Z) (activeOrbitWeight z0) hmass

theorem exactPostSwitch_activeOrbit_realizes_residual_prediction_witness
    [Fintype Z] (z0 : Z) :
    (∀ u : ExactVisiblePostSwitchSurface Z 1,
      invariantVisibleData (tiInputMap u) = invariantVisibleData u) ∧
    (∀ u : ExactVisiblePostSwitchSurface Z 1,
      activeOrbitWeight z0 (tiInputMap u) = activeOrbitWeight z0 u) ∧
    (∀ u : ExactVisiblePostSwitchSurface Z 1, 0 < activeOrbitWeight z0 u →
      activeOrbitTarget (tiInputMap u) = !(activeOrbitTarget u)) ∧
    0 <
      doubledAdvantage
        activeOrbitFeatures
        activeOrbitTarget
        (activeOrbitWeight z0)
        activeOrbitClassifier ∧
    ∃ u : ExactVisiblePostSwitchSurface Z 1,
      0 < activeOrbitWeight z0 u ∧
      activeOrbitClassifier (activeOrbitFeatures (tiInputMap u)) ≠
        activeOrbitClassifier (activeOrbitFeatures u) := by
  refine ⟨invariantVisibleData_tiInputMap, activeOrbitWeight_tiInputMap z0,
    activeOrbitTarget_flip_of_positiveWeight z0,
    pos_doubledAdvantage_activeOrbit (Z := Z) z0,
    exists_positive_prediction_separation_activeOrbit (Z := Z) z0⟩

/-- On the concrete active two-point exact post-switch witness, the retained
classifier output cannot already be source-only over the invariant base,
because some positive-weight involution pair is separated by the final
prediction. -/
theorem activeOrbitClassifier_not_supportwiseSourceOnly
    [Fintype Z] (z0 : Z) :
    ¬ SupportwiseSourceOnlyPairClassifier
        invariantVisibleData
        (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b)
        (activeOrbitWeight z0)
        activeOrbitClassifier := by
  intro hsource
  rcases exists_positive_prediction_separation_activeOrbit (Z := Z) z0 with
    ⟨u, hu, hsep⟩
  have heq :=
    prediction_eq_under_involution_of_supportwiseSourceOnlyPairClassifier_invariant_base
      tiInputMap
      invariantVisibleData
      (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b)
      (activeOrbitWeight z0)
      activeOrbitClassifier
      invariantVisibleData_tiInputMap
      (activeOrbitWeight_tiInputMap z0)
      hsource
      u
      hu
  exact hsep heq

/-- The manuscript's concrete active exact post-switch orbit already realizes
the full supported proof-relevant residual obstruction package with the actual
successful classifier, and that same visible surface cannot support any
supportwise visible-pair balancing involution. -/
theorem exactPostSwitch_activeOrbit_realizes_supported_obstruction_package_and_no_visiblePairBalancing
    [Fintype Z] (z0 : Z) :
    0 <
      doubledAdvantage
        activeOrbitFeatures
        activeOrbitTarget
        (activeOrbitWeight z0)
        activeOrbitClassifier ∧
      0 < resolvedMass tiInputMap
        (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b)
        (activeOrbitWeight z0) ∧
      ¬ SideInfoDeterminedBy invariantVisibleData
          (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b) ∧
      ¬ SupportwiseSourceOnlyPairClassifier
          invariantVisibleData
          (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b)
          (activeOrbitWeight z0)
          activeOrbitClassifier ∧
      (∃ u : ExactVisiblePostSwitchSurface Z 1,
        0 < activeOrbitWeight z0 u ∧
          invariantVisibleData (tiInputMap u) = invariantVisibleData u ∧
          (tiInputMap u).b ≠ u.b) ∧
      (∃ u : ExactVisiblePostSwitchSurface Z 1,
        0 < activeOrbitWeight z0 u ∧
          ¬ SourceOnlyPredicateCapturesSideEq
            invariantVisibleData
            (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b) (u.b)) ∧
      (∃ u : ExactVisiblePostSwitchSurface Z 1,
        0 < activeOrbitWeight z0 u ∧
          activeOrbitClassifier (activeOrbitFeatures (tiInputMap u)) ≠
            activeOrbitClassifier (activeOrbitFeatures u)) ∧
      ¬ SupportwiseVisiblePairBalancing
          invariantVisibleData
          (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b)
          activeOrbitTarget
          (activeOrbitWeight z0) := by
  have hpackage :=
    exactPostSwitch_activeOrbit_realizes_pure_residual_obstruction_package
      (Z := Z) z0
  rcases hpackage with
    ⟨hmass, hnot, _hcollision, hwitness, hpred⟩
  have hadv := pos_doubledAdvantage_activeOrbit (Z := Z) z0
  refine ⟨hadv, hmass, hnot, ?_, hwitness, hpred, ?_, ?_⟩
  · exact activeOrbitClassifier_not_supportwiseSourceOnly (Z := Z) z0
  · exact exists_positive_prediction_separation_activeOrbit (Z := Z) z0
  · exact
      not_supportwiseVisiblePairBalancing_of_pos_doubledAdvantage_pair
        invariantVisibleData
        (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b)
        activeOrbitTarget
        (activeOrbitWeight z0)
        activeOrbitClassifier
        hadv


end

end Mettapedia.Computability.PNP
