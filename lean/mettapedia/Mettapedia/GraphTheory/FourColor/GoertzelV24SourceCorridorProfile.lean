import Mettapedia.GraphTheory.FourColor.CAP5BoundaryWord
import Mettapedia.GraphTheory.FourColor.GoertzelV24BoundaryProfileFiniteState

/-!
# The manuscript-exact two-pair corridor profile

The length profile in the source records connectivity for
`alpha ∪ beta` and `alpha ∪ gamma`.  It does not record the third
`beta ∪ gamma` pair.  The older `CorridorCutProfile` deliberately stores all
three color pairs as a conservative internal refinement.  This file separates
those two interfaces explicitly.

The two-role source profile is the object whose reachable cardinality may enter
the source-facing pumping bound.  The three-pair profile remains useful for
local transition proofs, but must be projected through `toSourceProfile` before
its state count is interpreted as the manuscript's profile count.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SourceCorridorProfile

open GoertzelV24CorridorProfile
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24WindingClassification

/-- The two connectivity roles named in the manuscript's length profile. -/
inductive SourceTrackedColorPair where
  | alphaBeta
  | alphaGamma
  deriving DecidableEq, Fintype

/-- Interpret the two source roles relative to the ordered Tait triple chosen
by the good boundary word. -/
def sourceTrackedColorPairColors
    (alpha beta gamma : Color) : SourceTrackedColorPair → Color × Color
  | .alphaBeta => (alpha, beta)
  | .alphaGamma => (alpha, gamma)

/-- Both source pairs consist of distinct nonzero colors. -/
theorem sourceTrackedColorPairColors_wellFormed
    {alpha beta gamma : Color} (htriple : IsTaitColorTriple alpha beta gamma)
    (pair : SourceTrackedColorPair) :
    let colors := sourceTrackedColorPairColors alpha beta gamma pair
    colors.1 ≠ 0 ∧ colors.2 ≠ 0 ∧ colors.1 ≠ colors.2 := by
  rcases htriple with ⟨halpha, hbeta, hgamma, halphaBeta,
    halphaGamma, _hbetaGamma⟩
  cases pair
  · exact ⟨halpha, hbeta, halphaBeta⟩
  · exact ⟨halpha, hgamma, halphaGamma⟩

/-- Under the standard color-name gauge, select the corresponding entries of
the conservative three-pair family. -/
def SourceTrackedColorPair.toTrackedColorPair :
    SourceTrackedColorPair → TrackedColorPair
  | .alphaBeta => .ab
  | .alphaGamma => .ac

theorem card_sourceTrackedColorPair :
    Fintype.card SourceTrackedColorPair = 2 := by
  decide

/-- The literal source profile: cut colors, two connectivity families, and the
same finite face-progress receipt used by the conservative profile. -/
structure SourceCorridorCutProfile
    (crossingEdgeCount terminalCount faceFragmentCount : Nat) where
  edgeColor : Fin crossingEdgeCount → StrandColor
  strandConnected :
    SourceTrackedColorPair →
      CorridorPort crossingEdgeCount terminalCount →
      CorridorPort crossingEdgeCount terminalCount → Bool
  faceContinues :
    Fin faceFragmentCount → Fin faceFragmentCount → Bool
  fragmentContainsPort :
    Fin faceFragmentCount →
      CorridorPort crossingEdgeCount terminalCount → Bool
  faceLengthCap : Fin faceFragmentCount → Fin 6
  deriving DecidableEq

private def sourceCorridorCutProfileEquiv
    (crossingEdgeCount terminalCount faceFragmentCount : Nat) :
    SourceCorridorCutProfile crossingEdgeCount terminalCount
        faceFragmentCount ≃
      ((Fin crossingEdgeCount → StrandColor) ×
        (SourceTrackedColorPair →
          CorridorPort crossingEdgeCount terminalCount →
          CorridorPort crossingEdgeCount terminalCount → Bool) ×
        (Fin faceFragmentCount → Fin faceFragmentCount → Bool) ×
        (Fin faceFragmentCount →
          CorridorPort crossingEdgeCount terminalCount → Bool) ×
        (Fin faceFragmentCount → Fin 6)) where
  toFun profile :=
    (profile.edgeColor, profile.strandConnected,
      profile.faceContinues, profile.fragmentContainsPort,
      profile.faceLengthCap)
  invFun data :=
    ⟨data.1, data.2.1, data.2.2.1, data.2.2.2.1, data.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance sourceCorridorCutProfileFintype
    (crossingEdgeCount terminalCount faceFragmentCount : Nat) :
    Fintype (SourceCorridorCutProfile crossingEdgeCount terminalCount
      faceFragmentCount) :=
  Fintype.ofEquiv _
    (sourceCorridorCutProfileEquiv crossingEdgeCount terminalCount
      faceFragmentCount).symm

/-- Exact size of the chosen finite over-encoding of the source's two-pair
profile.  Reachability compression can make the realized carrier much smaller. -/
def sourceCorridorCutProfileCount
    (crossingEdgeCount terminalCount faceFragmentCount : Nat) : Nat :=
  3 ^ crossingEdgeCount *
    (2 ^ ((crossingEdgeCount + terminalCount) *
      (crossingEdgeCount + terminalCount))) ^ 2 *
    2 ^ (faceFragmentCount * faceFragmentCount) *
    2 ^ (faceFragmentCount *
      (crossingEdgeCount + terminalCount)) *
    6 ^ faceFragmentCount

theorem card_sourceCorridorCutProfile
    (crossingEdgeCount terminalCount faceFragmentCount : Nat) :
    Fintype.card (SourceCorridorCutProfile crossingEdgeCount terminalCount
      faceFragmentCount) =
      sourceCorridorCutProfileCount crossingEdgeCount terminalCount
        faceFragmentCount := by
  rw [Fintype.card_congr
    (sourceCorridorCutProfileEquiv crossingEdgeCount terminalCount
      faceFragmentCount)]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool, Fintype.card_sum]
  have hcolor : Fintype.card StrandColor = 3 := by decide
  rw [hcolor, card_sourceTrackedColorPair]
  unfold sourceCorridorCutProfileCount
  ring

/-- Forget the conservative `beta ∪ gamma` entry. -/
def toSourceProfile
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (profile : CorridorCutProfile crossingEdgeCount terminalCount
      faceFragmentCount) :
    SourceCorridorCutProfile crossingEdgeCount terminalCount
      faceFragmentCount where
  edgeColor := profile.edgeColor
  strandConnected pair :=
    profile.strandConnected pair.toTrackedColorPair
  faceContinues := profile.faceContinues
  fragmentContainsPort := profile.fragmentContainsPort
  faceLengthCap := profile.faceLengthCap

/-- A canonical conservative lift, assigning `false` to the extra third pair. -/
def SourceCorridorCutProfile.toConservativeProfile
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (profile : SourceCorridorCutProfile crossingEdgeCount terminalCount
      faceFragmentCount) :
    CorridorCutProfile crossingEdgeCount terminalCount faceFragmentCount where
  edgeColor := profile.edgeColor
  strandConnected pair :=
    match pair with
    | .ab => profile.strandConnected .alphaBeta
    | .ac => profile.strandConnected .alphaGamma
    | .bc => fun _ _ => false
  faceContinues := profile.faceContinues
  fragmentContainsPort := profile.fragmentContainsPort
  faceLengthCap := profile.faceLengthCap

@[simp]
theorem SourceCorridorCutProfile.toConservativeProfile_toSourceProfile
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (profile : SourceCorridorCutProfile crossingEdgeCount terminalCount
      faceFragmentCount) :
    toSourceProfile profile.toConservativeProfile = profile := by
  cases profile
  unfold toSourceProfile SourceCorridorCutProfile.toConservativeProfile
  congr
  funext pair first second
  cases pair <;> rfl

/-- The source projection loses no source profile states. -/
theorem toSourceProfile_surjective
    {crossingEdgeCount terminalCount faceFragmentCount : Nat} :
    Function.Surjective
      (@toSourceProfile crossingEdgeCount terminalCount
        faceFragmentCount) := by
  intro profile
  exact ⟨profile.toConservativeProfile, by simp⟩

/-- Source-exact profiles with a variable number of face fragments below one
fixed bound. -/
structure BoundedSourceCorridorCutProfile
    (crossingEdgeCount terminalCount faceFragmentBound : Nat) where
  faceFragmentCount : Fin (faceFragmentBound + 1)
  profile : SourceCorridorCutProfile crossingEdgeCount terminalCount
    faceFragmentCount.val
  deriving DecidableEq

private def boundedSourceCorridorCutProfileEquiv
    (crossingEdgeCount terminalCount faceFragmentBound : Nat) :
    BoundedSourceCorridorCutProfile crossingEdgeCount terminalCount
        faceFragmentBound ≃
      Σ faceFragmentCount : Fin (faceFragmentBound + 1),
        SourceCorridorCutProfile crossingEdgeCount terminalCount
          faceFragmentCount.val where
  toFun state := ⟨state.faceFragmentCount, state.profile⟩
  invFun state := ⟨state.1, state.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance boundedSourceCorridorCutProfileFintype
    (crossingEdgeCount terminalCount faceFragmentBound : Nat) :
    Fintype (BoundedSourceCorridorCutProfile crossingEdgeCount terminalCount
      faceFragmentBound) :=
  Fintype.ofEquiv _
    (boundedSourceCorridorCutProfileEquiv crossingEdgeCount terminalCount
      faceFragmentBound).symm

def boundedSourceCorridorCutProfileCount
    (crossingEdgeCount terminalCount faceFragmentBound : Nat) : Nat :=
  ∑ faceFragmentCount : Fin (faceFragmentBound + 1),
    sourceCorridorCutProfileCount crossingEdgeCount terminalCount
      faceFragmentCount.val

theorem card_boundedSourceCorridorCutProfile
    (crossingEdgeCount terminalCount faceFragmentBound : Nat) :
    Fintype.card (BoundedSourceCorridorCutProfile crossingEdgeCount
      terminalCount faceFragmentBound) =
      boundedSourceCorridorCutProfileCount crossingEdgeCount terminalCount
        faceFragmentBound := by
  rw [Fintype.card_congr
    (boundedSourceCorridorCutProfileEquiv crossingEdgeCount terminalCount
      faceFragmentBound), Fintype.card_sigma]
  simp_rw [card_sourceCorridorCutProfile]
  rfl

/-- Project the variable-fragment conservative state to the manuscript state. -/
def toBoundedSourceProfile
    {crossingEdgeCount terminalCount faceFragmentBound : Nat}
    (profile : BoundedCorridorCutProfile crossingEdgeCount terminalCount
      faceFragmentBound) :
    BoundedSourceCorridorCutProfile crossingEdgeCount terminalCount
      faceFragmentBound where
  faceFragmentCount := profile.faceFragmentCount
  profile := toSourceProfile profile.profile

/-- Canonical lift of a bounded source state to the conservative carrier. -/
def BoundedSourceCorridorCutProfile.toConservativeProfile
    {crossingEdgeCount terminalCount faceFragmentBound : Nat}
    (profile : BoundedSourceCorridorCutProfile crossingEdgeCount terminalCount
      faceFragmentBound) :
    BoundedCorridorCutProfile crossingEdgeCount terminalCount
      faceFragmentBound where
  faceFragmentCount := profile.faceFragmentCount
  profile := profile.profile.toConservativeProfile

@[simp]
theorem BoundedSourceCorridorCutProfile.toConservativeProfile_toBoundedSourceProfile
    {crossingEdgeCount terminalCount faceFragmentBound : Nat}
    (profile : BoundedSourceCorridorCutProfile crossingEdgeCount terminalCount
      faceFragmentBound) :
    toBoundedSourceProfile profile.toConservativeProfile = profile := by
  rcases profile with ⟨faceFragmentCount, profile⟩
  have hprofile :
      toSourceProfile profile.toConservativeProfile = profile := by
    simp
  unfold toBoundedSourceProfile
    BoundedSourceCorridorCutProfile.toConservativeProfile
  rw [hprofile]

theorem toBoundedSourceProfile_surjective
    {crossingEdgeCount terminalCount faceFragmentBound : Nat} :
    Function.Surjective
      (@toBoundedSourceProfile crossingEdgeCount terminalCount
        faceFragmentBound) := by
  intro profile
  exact ⟨profile.toConservativeProfile, by simp⟩

end GoertzelV24SourceCorridorProfile

end Mettapedia.GraphTheory.FourColor
