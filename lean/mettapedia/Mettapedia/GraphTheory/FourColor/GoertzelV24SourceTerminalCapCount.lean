import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularFrontierCapComposedProfileCount
import Mettapedia.GraphTheory.FourColor.GoertzelV24SourceTerminalCapGauge

/-!
# The corrected Seed count on the compressed source carrier

The corrected cap-composed Seed count is stated on the all-colour uniform
profile.  The manuscript, however, chooses an ordered majority/singleton
triple and globally relabels it to the standard three colours.  This module
proves that the two presentations agree: all-colour acceptance is equivalent
to acceptance of some normalized two-role source view.

It also defines the actual finite accepting subset of the bounded compressed
cumulative source carrier and proves that lossless compression preserves
membership.  No executable enumeration or minimized-closure certificate is
claimed here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SourceTerminalCapCount

open GoertzelV24AnnularFrontierMenu
open GoertzelV24AnnularFrontierCapComposedProfileSemantics
open GoertzelV24AnnularFrontierCapComposedProfileCount
open GoertzelV24SourceCorridorProfile
open GoertzelV24SourceTerminalAwareProfileCompression
open GoertzelV24SourceTerminalCapView
open GoertzelV24SourceTerminalCapGauge

/-- Project the all-colour uniform profile to the two source roles relative to
one ordered Tait triple. -/
def terminalCapViewOfUniformProfileAt
    (profile : AnnularFrontierMenuUniformProfile)
    (alpha beta gamma : Color) : SourceTerminalCapView where
  word := profile.word
  strand pair first second :=
    let colors := sourceTrackedColorPairColors alpha beta gamma pair
    profile.connectionTable colors.1 colors.2 first second

theorem capComposedMenuBForPairOfProfile_iff_sourceViewAt
    (profile : AnnularFrontierMenuUniformProfile)
    (alpha beta gamma : Color) (pair : SourceTrackedColorPair) :
    CapComposedMenuBForPairOfProfile profile
        (sourceTrackedColorPairColors alpha beta gamma pair).1
        (sourceTrackedColorPairColors alpha beta gamma pair).2 ↔
      capComposedMenuBForPairAt
        (terminalCapViewOfUniformProfileAt profile alpha beta gamma)
        alpha beta gamma pair := by
  cases pair <;>
    rfl

/-- The corrected all-colour profile predicate is exactly acceptance of some
canonically normalized two-role source view. -/
theorem capComposedMenuBStateOfProfile_iff_exists_normalized_sourceView
    (profile : AnnularFrontierMenuUniformProfile) :
    CapComposedMenuBStateOfProfile profile ↔
      ∃ (alpha beta gamma : Color)
          (htriple : AnnularFrontierMajorityTriple
            profile.word alpha beta gamma),
        (normalizedCapView
          (terminalCapViewOfUniformProfileAt profile alpha beta gamma)
          htriple.1).standardGaugeCapComposedMenuBState := by
  constructor
  · rintro ⟨alpha, beta, gamma, htriple, hfirst | hsecond⟩
    · refine ⟨alpha, beta, gamma, htriple, ?_⟩
      apply (standardGaugeCapComposedMenuBState_normalized_iff
        (terminalCapViewOfUniformProfileAt profile alpha beta gamma)
        htriple).2
      refine ⟨htriple, Or.inl ?_⟩
      exact (capComposedMenuBForPairOfProfile_iff_sourceViewAt
        profile alpha beta gamma .alphaBeta).1 hfirst
    · refine ⟨alpha, beta, gamma, htriple, ?_⟩
      apply (standardGaugeCapComposedMenuBState_normalized_iff
        (terminalCapViewOfUniformProfileAt profile alpha beta gamma)
        htriple).2
      refine ⟨htriple, Or.inr ?_⟩
      exact (capComposedMenuBForPairOfProfile_iff_sourceViewAt
        profile alpha beta gamma .alphaGamma).1 hsecond
  · rintro ⟨alpha, beta, gamma, htriple, haccepted⟩
    have hsource :=
      (standardGaugeCapComposedMenuBState_normalized_iff
        (terminalCapViewOfUniformProfileAt profile alpha beta gamma)
        htriple).1 haccepted
    rcases hsource with ⟨_, hfirst | hsecond⟩
    · exact ⟨alpha, beta, gamma, htriple,
        Or.inl ((capComposedMenuBForPairOfProfile_iff_sourceViewAt
          profile alpha beta gamma .alphaBeta).2 hfirst)⟩
    · exact ⟨alpha, beta, gamma, htriple,
        Or.inr ((capComposedMenuBForPairOfProfile_iff_sourceViewAt
          profile alpha beta gamma .alphaGamma).2 hsecond)⟩

/-- The corrected Seed count is positive exactly when a positive realized
uniform profile supplies an accepted normalized source view. -/
theorem capComposedSeedCount_pos_iff_exists_normalized_sourceView
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {outerCount : Nat}
    (data : GoertzelV24ClosedWebBoundaryData.AnnularBoundaryData G outerCount)
    (hdata : data.WellFormed) (word : CAP5BoundaryWord) :
    0 < capComposedSeedCount data hdata word ↔
      ∃ profile : AnnularFrontierMenuUniformProfile,
        profile.word = word ∧
          0 < annularFrontierMenuUniformProfileCount data hdata profile ∧
            ∃ (alpha beta gamma : Color)
                (htriple : AnnularFrontierMajorityTriple
                  profile.word alpha beta gamma),
              (normalizedCapView
                (terminalCapViewOfUniformProfileAt profile alpha beta gamma)
                htriple.1).standardGaugeCapComposedMenuBState := by
  rw [capComposedSeedCount_pos_iff_exists_profile]
  constructor
  · rintro ⟨profile, hword, hpositive, haccepted⟩
    exact ⟨profile, hword, hpositive,
      (capComposedMenuBStateOfProfile_iff_exists_normalized_sourceView
        profile).1 haccepted⟩
  · rintro ⟨profile, hword, hpositive, haccepted⟩
    exact ⟨profile, hword, hpositive,
      (capComposedMenuBStateOfProfile_iff_exists_normalized_sourceView
        profile).2 haccepted⟩

/-- The concrete accepting subset of the bounded compressed cumulative source
carrier. -/
noncomputable def acceptedSourceCompressedProfileSet
    (crossingEdgeCount faceFragmentBound : Nat) :
    Finset (BoundedSourceTerminalAwareCompressedProfile
      crossingEdgeCount 5 faceFragmentBound) := by
  classical
  exact Finset.univ.filter fun code =>
    (terminalCapViewOfBoundedCompressed code).standardGaugeCapComposedMenuBState

theorem mem_acceptedSourceCompressedProfileSet_iff
    {crossingEdgeCount faceFragmentBound : Nat}
    (code : BoundedSourceTerminalAwareCompressedProfile
      crossingEdgeCount 5 faceFragmentBound) :
    code ∈ acceptedSourceCompressedProfileSet crossingEdgeCount faceFragmentBound ↔
      (terminalCapViewOfBoundedCompressed code).standardGaugeCapComposedMenuBState := by
  classical
  simp [acceptedSourceCompressedProfileSet]

theorem compressBounded_mem_acceptedSourceCompressedProfileSet_iff
    {crossingEdgeCount faceFragmentBound : Nat}
    (profile : BoundedSourceCorridorCutProfile crossingEdgeCount 5
      faceFragmentBound)
    (semantic : BoundedIsSourceTerminalGraphSemantic profile) :
    compressBounded profile semantic ∈
        acceptedSourceCompressedProfileSet crossingEdgeCount faceFragmentBound ↔
      (terminalCapViewOfBoundedSourceProfile profile).standardGaugeCapComposedMenuBState := by
  rw [mem_acceptedSourceCompressedProfileSet_iff,
    standardGaugeCapComposedMenuBState_compressBounded_iff]

theorem sourceCompressedCodeOfCell3_mem_accepted_iff
    (profile : GoertzelV24GraphDerivedTerminalProfile.Cell3TerminalAwareProfile)
    (semantic : GoertzelV24TerminalAwareProfileCompression.BoundedIsTerminalGraphSemantic
      profile) :
    sourceCompressedCodeOfCell3 profile semantic ∈
        acceptedSourceCompressedProfileSet 2 8 ↔
      (terminalCapViewOfBoundedSourceProfile
        (GoertzelV24SourceCorridorProfile.toBoundedSourceProfile
          profile)).standardGaugeCapComposedMenuBState := by
  rw [mem_acceptedSourceCompressedProfileSet_iff,
    standardGaugeCapComposedMenuBState_sourceCompressedCodeOfCell3_iff]

end GoertzelV24SourceTerminalCapCount

end Mettapedia.GraphTheory.FourColor
