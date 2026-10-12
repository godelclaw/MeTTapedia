import Mettapedia.GSLT.LanguageDef.BootstrapCell.CheckingWeakness

/-!
# Exact replay correctness and independent semantic qualification

An implementation checks exactly the erased derivations of a replay
signature. Correctness determines its Boolean behavior extensionally.
Meaning is supplied separately by a predicate closed under the local rules.
The soundness and rejection laws apply to every such interpretation.

Formerly `Mettapedia.GSLT.LanguageDef.BootstrapCell.CoreNIK`, part of the native inference kernel (NIK) development of 2026-08-11 to 2026-10-08; renamed to its subject name on 2026-10-08.
Renamed declarations: `CoreNIK` → `ReplayCorrect`, `coreNIK_replay` → `replay_correct`, `coreNIK_checkRaw` → `checkRaw_correct`, `not_coreNIK_tooStrong` → `tooStrong_not_replay_correct`; `ReflexiveCell` and `CheckingClaim` moved to `BootstrapCell.ReflexiveLayer`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BootstrapCell

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

universe u

/-! ## Exact certificate replay -/

/-- **`ReplayCorrect`**: an implementation refines the abstract replay of a
signature. -/
structure ReplayCorrect (σ : ReplaySignature.{u}) (implementation : σ.Goal → RawProof → Bool) :
    Prop where
  sound : ∀ goal certificate, implementation goal certificate = true →
    ∃ derivation : σ.Deriv goal, derivation.erase = certificate
  complete : ∀ goal (derivation : σ.Deriv goal), implementation goal derivation.erase = true

namespace ReplayCorrect

variable {σ : ReplaySignature.{u}} {implementation : σ.Goal → RawProof → Bool}

/-- An accepted certificate determines its goal. -/
theorem goal_unique (core : ReplayCorrect σ implementation) {first second : σ.Goal}
    {certificate : RawProof} (firstAccepted : implementation first certificate = true)
    (secondAccepted : implementation second certificate = true) : first = second := by
  obtain ⟨firstDerivation, firstErased⟩ := core.sound first certificate firstAccepted
  obtain ⟨secondDerivation, secondErased⟩ := core.sound second certificate secondAccepted
  have firstReplay := firstDerivation.replay_erase
  have secondReplay := secondDerivation.replay_erase
  rw [firstErased] at firstReplay
  rw [secondErased] at secondReplay
  exact ReplaySignature.replay_goal_unique firstReplay secondReplay

/-- **`ReplayCorrect` determines the implementation**: it holds exactly for the
replay function itself, up to extensional equality. -/
theorem iff_eq_replay : ReplayCorrect σ implementation ↔ implementation = σ.replay := by
  constructor
  · intro core
    funext goal certificate
    apply Bool.eq_iff_iff.mpr
    rw [ReplaySignature.replay_iff]
    constructor
    · exact core.sound goal certificate
    · rintro ⟨derivation, rfl⟩
      exact core.complete goal derivation
  · rintro rfl
    exact ⟨fun goal certificate accepted =>
        (ReplaySignature.replay_iff goal certificate).mp accepted,
      fun _ derivation => derivation.replay_erase⟩

end ReplayCorrect

/-- Replay satisfies `ReplayCorrect`. -/
theorem replay_correct (σ : ReplaySignature.{u}) : ReplayCorrect σ σ.replay :=
  ReplayCorrect.iff_eq_replay.mpr rfl

/-- The generic inference checker satisfies `ReplayCorrect` for every validated
calculus. -/
theorem checkRaw_correct (definition : ValidatedCalculusLanguageDef) :
    ReplayCorrect (calculusReplaySignature definition) (checkRaw definition) :=
  ReplayCorrect.iff_eq_replay.mpr (funext fun goal => funext fun certificate =>
    checkRaw_eq_replay definition goal certificate)

/-- **Negative control.**  The too-strong kernel is not a `ReplayCorrect`
implementation. -/
theorem tooStrong_not_replay_correct :
    ¬ ReplayCorrect (CheckingWeakness.modusPonens ()) (CheckingWeakness.tooStrong ()) := by
  intro core
  have faithful : CheckingWeakness.Faithful CheckingWeakness.modusPonens
      CheckingWeakness.tooStrong := by
    rintro ⟨⟨⟩, goal, certificate⟩
    refine ⟨core.sound goal certificate, ?_⟩
    rintro ⟨derivation, erased⟩
    have erased' : derivation.erase = certificate := erased
    show CheckingWeakness.tooStrong () goal certificate = true
    rw [← erased']
    exact core.complete goal derivation
  exact CheckingWeakness.tooStrong_not_weakest
    ((CheckingWeakness.isWeakestAdmissible_iff_faithful _).mpr faithful)

/-! ## Semantic qualification: the separate interface -/

/-- A meaning closed under every local rule application, supplied separately
from `ReplayCorrect`. -/
structure SemanticQualification (σ : ReplaySignature.{u}) where
  Meaning : σ.Goal → Prop
  closed : ∀ label premises conclusion, σ.step label = some (premises, conclusion) →
    (∀ premise ∈ premises, Meaning premise) → Meaning conclusion

/-- Acceptance, derivability, truth: an accepted goal holds in every supplied
qualification. -/
theorem ReplayCorrect.accepted_meaning {σ : ReplaySignature.{u}}
    {implementation : σ.Goal → RawProof → Bool} (core : ReplayCorrect σ implementation)
    (qualification : SemanticQualification σ) {goal : σ.Goal} {certificate : RawProof}
    (accepted : implementation goal certificate = true) : qualification.Meaning goal := by
  obtain ⟨derivation, _⟩ := core.sound goal certificate accepted
  exact ReplaySignature.Deriv.sound qualification.Meaning qualification.closed derivation

/-- A goal outside the supplied meaning is rejected for every certificate. -/
theorem ReplayCorrect.rejects_outside_meaning {σ : ReplaySignature.{u}}
    {implementation : σ.Goal → RawProof → Bool} (core : ReplayCorrect σ implementation)
    (qualification : SemanticQualification σ) {goal : σ.Goal}
    (outside : ¬ qualification.Meaning goal) (certificate : RawProof) :
    implementation goal certificate = false := by
  cases accepted : implementation goal certificate with
  | false => rfl
  | true => exact absurd (core.accepted_meaning qualification accepted) outside

end Mettapedia.GSLT.LanguageDef.BootstrapCell
