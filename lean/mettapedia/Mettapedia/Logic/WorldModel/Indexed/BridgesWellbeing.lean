import Mettapedia.Logic.WorldModel.Indexed.Survival
import Mettapedia.CogArch.Agent.WellbeingObserverTransformationBoundary

/-!
# Shared appraisals are the view law

An appraisal visible at an observer is a consumer factoring through the
observer's view (`appraisalVisibleAt_iff`).  A source appraisal admits a
shared appraisal with some target appraisal exactly when it factors through
the source view (`exists_sharedAppraisal_iff`).  The preservation of shared
appraisals by observer-preserving maps and the collision no-go are derived
from the general view law (`preserves_shared_appraisal_of_law`,
`no_shared_appraisal_of_collision_of_law`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.WorldModel.Indexed.BridgesWellbeing

open Mettapedia.Cybernetics
open Mettapedia.GSLT.Dynamics
open Mettapedia.GSLT.Dynamics.ObserverRelativeTransformationCrown
open Mettapedia.CogArch.Agent.WellbeingObserverTransformationBoundary

universe uSource uTarget uView uAppraisal

variable {Source : Type uSource} {Target : Type uTarget} {View : Type uView}
  {Appraisal : Type uAppraisal}

/-- Visibility is factoring through the view. -/
theorem appraisalVisibleAt_iff [Nonempty Appraisal] (appraisal : Source → Appraisal)
    (observer : Observer Source View) :
    AppraisalVisibleAt appraisal observer ↔ appraisal.FactorsThrough observer.observe :=
  (factorsThrough_iff_exists_recover observer.observe appraisal).symm

/-- A source appraisal is shared with some target appraisal exactly when it
factors through the source view. -/
theorem exists_sharedAppraisal_iff [Nonempty Appraisal]
    (sourceObserver : Observer Source View) (targetObserver : Observer Target View)
    (sourceAppraisal : Source → Appraisal) :
    (∃ targetAppraisal : Target → Appraisal,
        Nonempty (SharedAppraisal sourceObserver targetObserver sourceAppraisal targetAppraisal)) ↔
      sourceAppraisal.FactorsThrough sourceObserver.observe := by
  constructor
  · rintro ⟨_, ⟨shared⟩⟩
    exact (factorsThrough_iff_exists_recover _ _).2 ⟨shared.readout, shared.source_agrees⟩
  · intro factors
    obtain ⟨readout, agrees⟩ := (factorsThrough_iff_exists_recover _ _).1 factors
    exact ⟨readout ∘ targetObserver.observe, ⟨⟨readout, agrees, fun _ => rfl⟩⟩⟩

/-- The local preservation theorem, derived from the view law. -/
theorem preserves_shared_appraisal_of_law
    {sourceObserver : Observer Source View} {targetObserver : Observer Target View}
    {sourceAppraisal : Source → Appraisal} {targetAppraisal : Target → Appraisal}
    (representation : ObserverPreservingMap Source Target View sourceObserver targetObserver)
    (shared : SharedAppraisal sourceObserver targetObserver sourceAppraisal targetAppraisal)
    (source : Source) :
    targetAppraisal (representation.transform source) = sourceAppraisal source := by
  have kept := congrFun (kept_of_view_preserving
    (h := representation.transform) (funext representation.preserves) shared.readout) source
  simp only [Function.comp_apply] at kept
  rw [← shared.target_agrees, kept, shared.source_agrees]

/-- The local collision no-go, derived from the failure of factoring. -/
theorem no_shared_appraisal_of_collision_of_law
    {sourceObserver : Observer Source View} {targetObserver : Observer Target View}
    {sourceAppraisal : Source → Appraisal} {targetAppraisal : Target → Appraisal}
    {first second : Source}
    (sameView : sourceObserver.observe first = sourceObserver.observe second)
    (different : sourceAppraisal first ≠ sourceAppraisal second) :
    ¬ Nonempty (SharedAppraisal sourceObserver targetObserver sourceAppraisal targetAppraisal) := by
  rintro ⟨shared⟩
  have : sourceAppraisal.FactorsThrough sourceObserver.observe := by
    intro a b same
    rw [← shared.source_agrees a, ← shared.source_agrees b, same]
  exact different (this sameView)

end Mettapedia.Logic.WorldModel.Indexed.BridgesWellbeing
