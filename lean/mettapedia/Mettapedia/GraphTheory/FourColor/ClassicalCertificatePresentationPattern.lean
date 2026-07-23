import Mathlib.Tactic
import Mettapedia.GraphTheory.FourColor.ClassicalCertificatePresentationLogic

/-!
# Local face-size patterns for unavoidability certificates

The finite presentations constrain face arities in the second neighborhood
of a distinguished face.  An upper endpoint of nine denotes infinity.  Every
sector stores the spoke, hat, and three possible fan ranges; a fan omitted by
the compact source notation is represented by the free range.  This total
representation makes splitting pointwise while retaining the source
language's legality check for which fans actually exist.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificatePresentationPattern

open ClassicalCertificatePresentationLogic

/-- A face-size interval.  `upper = 9` is the unbounded endpoint. -/
structure FaceRange where
  lower : Nat
  upper : Nat
deriving DecidableEq, Repr

namespace FaceRange

/-- The interval is one of the standard nonempty ranges beginning at five. -/
def Valid (range : FaceRange) : Prop :=
  5 ≤ range.lower ∧ range.lower ≤ range.upper ∧ range.upper ≤ 9

instance (range : FaceRange) : Decidable range.Valid := by
  unfold Valid
  infer_instance

/-- Boolean validity check for certificate data. -/
def validChecker (range : FaceRange) : Bool :=
  decide range.Valid

/-- Membership, with endpoint nine interpreted as infinity. -/
def Contains (range : FaceRange) (arity : Nat) : Prop :=
  range.lower ≤ arity ∧ (range.upper = 9 ∨ arity ≤ range.upper)

/-- The unconstrained range in a pentagonal map. -/
def free : FaceRange := ⟨5, 9⟩

/-- A singleton finite face-size range. -/
def singleton (arity : Nat) : FaceRange := ⟨arity, arity⟩

/-- Restrict an interval to one side of a threshold. -/
def split (range : FaceRange) (bound : Nat) (lowerSide : Bool) : FaceRange :=
  if lowerSide then
    ⟨range.lower, min range.upper bound⟩
  else
    ⟨max range.lower (bound + 1), range.upper⟩

@[simp] theorem split_true (range : FaceRange) (bound : Nat) :
    range.split bound true = ⟨range.lower, min range.upper bound⟩ := by
  rfl

@[simp] theorem split_false (range : FaceRange) (bound : Nat) :
    range.split bound false =
      ⟨max range.lower (bound + 1), range.upper⟩ := by
  rfl

/-- A split is nontrivial and remains inside the finite endpoint convention. -/
def GoodSplit (range : FaceRange) (bound : Nat) : Prop :=
  range.Valid ∧ range.lower ≤ bound ∧ bound < range.upper ∧ bound < 9

/-- Boolean nontrivial-split check. -/
def goodSplitChecker (range : FaceRange) (bound : Nat) : Bool :=
  range.validChecker &&
    (decide (range.lower ≤ bound) &&
      (decide (bound < range.upper) && decide (bound < 9)))

theorem validChecker_eq_true_iff (range : FaceRange) :
    range.validChecker = true ↔ range.Valid := by
  simp [validChecker]

theorem goodSplitChecker_eq_true_iff (range : FaceRange) (bound : Nat) :
    range.goodSplitChecker bound = true ↔ range.GoodSplit bound := by
  simp [goodSplitChecker, GoodSplit, validChecker_eq_true_iff]

/-- The lower and upper restrictions cover every member of the interval. -/
theorem contains_split_or
    {range : FaceRange} {bound arity : Nat}
    (hbound : bound < 9) (hcontains : range.Contains arity) :
    (range.split bound true).Contains arity ∨
      (range.split bound false).Contains arity := by
  rcases hcontains with ⟨hlower, hupper⟩
  by_cases harity : arity ≤ bound
  · left
    rw [split_true]
    change range.lower ≤ arity ∧
      (min range.upper bound = 9 ∨ arity ≤ min range.upper bound)
    constructor
    · exact hlower
    · apply Or.inr
      apply Nat.le_min.2
      constructor
      · rcases hupper with hfree | hfinite
        · omega
        · exact hfinite
      · exact harity
  · right
    rw [split_false]
    change max range.lower (bound + 1) ≤ arity ∧
      (range.upper = 9 ∨ arity ≤ range.upper)
    constructor
    · exact Nat.max_le.2 ⟨hlower, by omega⟩
    · exact hupper

/-- The selected restriction and its complement cover the original range. -/
theorem contains_split_side_or_complement
    {range : FaceRange} {bound arity : Nat} {lowerSide : Bool}
    (hbound : bound < 9) (hcontains : range.Contains arity) :
    (range.split bound lowerSide).Contains arity ∨
      (range.split bound (!lowerSide)).Contains arity := by
  cases lowerSide
  · simpa using (contains_split_or hbound hcontains).symm
  · exact contains_split_or hbound hcontains

/-- Membership in either restriction implies membership in the original. -/
theorem contains_of_contains_split
    {range : FaceRange} {bound arity : Nat} {lowerSide : Bool}
    (hvalid : range.Valid)
    (hcontains : (range.split bound lowerSide).Contains arity) :
    range.Contains arity := by
  cases lowerSide
  · rw [split_false] at hcontains
    change max range.lower (bound + 1) ≤ arity ∧
      (range.upper = 9 ∨ arity ≤ range.upper) at hcontains
    rcases hcontains with ⟨hlower, hupper⟩
    exact ⟨le_trans (Nat.le_max_left _ _) hlower, hupper⟩
  · rw [split_true] at hcontains
    change range.lower ≤ arity ∧
      (min range.upper bound = 9 ∨ arity ≤ min range.upper bound)
      at hcontains
    rcases hcontains with ⟨hlower, hupper⟩
    refine ⟨hlower, ?_⟩
    rcases hupper with hfree | hfinite
    · exact Or.inl (by
        have hmin : 9 ≤ range.upper := by
          rw [← hfree]
          exact Nat.min_le_left _ _
        exact Nat.le_antisymm hvalid.2.2 hmin)
    · exact Or.inr (le_trans hfinite (Nat.min_le_left _ _))

/-- A side condition cut from one range cuts every other range containing
the same arity on the same side. -/
theorem contains_split_of_contains_split_and_contains
    {source target : FaceRange} {bound arity : Nat} {lowerSide : Bool}
    (hbound : bound < 9)
    (hsource : (source.split bound lowerSide).Contains arity)
    (htarget : target.Contains arity) :
    (target.split bound lowerSide).Contains arity := by
  cases lowerSide
  · rw [split_false] at hsource ⊢
    change max source.lower (bound + 1) ≤ arity ∧
      (source.upper = 9 ∨ arity ≤ source.upper) at hsource
    change max target.lower (bound + 1) ≤ arity ∧
      (target.upper = 9 ∨ arity ≤ target.upper)
    rcases hsource with ⟨hsourceLower, _hsourceUpper⟩
    rcases htarget with ⟨htargetLower, htargetUpper⟩
    exact ⟨Nat.max_le.2 ⟨htargetLower,
      le_trans (Nat.le_max_right _ _) hsourceLower⟩, htargetUpper⟩
  · rw [split_true] at hsource ⊢
    change source.lower ≤ arity ∧
      (min source.upper bound = 9 ∨ arity ≤ min source.upper bound)
      at hsource
    change target.lower ≤ arity ∧
      (min target.upper bound = 9 ∨ arity ≤ min target.upper bound)
    rcases hsource with ⟨_sourceLower, hsourceUpper⟩
    rcases htarget with ⟨htargetLower, htargetUpper⟩
    refine ⟨htargetLower, Or.inr ?_⟩
    apply Nat.le_min.2
    constructor
    · rcases htargetUpper with htargetFree | htargetFinite
      · simpa [htargetFree] using (show arity ≤ 9 by
          rcases hsourceUpper with hsourceFree | hsourceFinite
          · have := Nat.min_le_right source.upper bound
            omega
          · exact le_trans hsourceFinite
              (le_trans (Nat.min_le_right _ _) (Nat.le_of_lt hbound)))
      · exact htargetFinite
    · rcases hsourceUpper with hsourceFree | hsourceFinite
      · have := Nat.min_le_right source.upper bound
        omega
      · exact le_trans hsourceFinite (Nat.min_le_right _ _)

/-- Every arity accepted by `source` is accepted by `target`. -/
def IsSubset (source target : FaceRange) : Prop :=
  ∀ arity, source.Contains arity → target.Contains arity

/-- A closed-form interval-containment check. -/
def subsetChecker (source target : FaceRange) : Bool :=
  decide (target.lower ≤ source.lower ∧
    (target.upper = 9 ∨
      (source.upper ≠ 9 ∧ source.upper ≤ target.upper)))

theorem subsetChecker_sound {source target : FaceRange}
    (hcheck : source.subsetChecker target = true) :
    source.IsSubset target := by
  have hbounds : target.lower ≤ source.lower ∧
      (target.upper = 9 ∨
        (source.upper ≠ 9 ∧ source.upper ≤ target.upper)) := by
    simpa [subsetChecker] using of_decide_eq_true hcheck
  intro arity hsource
  refine ⟨le_trans hbounds.1 hsource.1, ?_⟩
  rcases hbounds.2 with htargetFree | ⟨hsourceFinite, hupper⟩
  · exact Or.inl htargetFree
  · exact Or.inr (le_trans (hsource.2.resolve_left hsourceFinite) hupper)

end FaceRange

/-- Address of one face in a sector. -/
inductive Location where
  | spoke
  | hat
  | fan1
  | fan2
  | fan3
deriving DecidableEq, Repr

/-- The five possible face ranges in a second-neighborhood sector. -/
structure Sector where
  spoke : FaceRange
  hat : FaceRange
  fan1 : FaceRange
  fan2 : FaceRange
  fan3 : FaceRange
deriving DecidableEq, Repr

namespace Sector

/-- Compact sector with no explicit fan constraint. -/
def plain (spoke hat : FaceRange) : Sector :=
  ⟨spoke, hat, FaceRange.free, FaceRange.free, FaceRange.free⟩

/-- Sector with a fixed six-spoke and one explicit fan. -/
def six (hat fan1 : FaceRange) : Sector :=
  ⟨FaceRange.singleton 6, hat, fan1, FaceRange.free, FaceRange.free⟩

/-- Sector with a fixed seven-spoke and two explicit fans. -/
def seven (hat fan1 fan2 : FaceRange) : Sector :=
  ⟨FaceRange.singleton 7, hat, fan1, fan2, FaceRange.free⟩

/-- Sector with a fixed eight-spoke and three explicit fans. -/
def eight (hat fan1 fan2 fan3 : FaceRange) : Sector :=
  ⟨FaceRange.singleton 8, hat, fan1, fan2, fan3⟩

/-- The range stored at an addressed location. -/
def rangeAt (sector : Sector) : Location → FaceRange
  | .spoke => sector.spoke
  | .hat => sector.hat
  | .fan1 => sector.fan1
  | .fan2 => sector.fan2
  | .fan3 => sector.fan3

/-- Replace one addressed range. -/
def replaceAt (sector : Sector) (location : Location)
    (range : FaceRange) : Sector :=
  match location with
  | .spoke => { sector with spoke := range }
  | .hat => { sector with hat := range }
  | .fan1 => { sector with fan1 := range }
  | .fan2 => { sector with fan2 := range }
  | .fan3 => { sector with fan3 := range }

@[simp] theorem rangeAt_replaceAt_same
    (sector : Sector) (location : Location) (range : FaceRange) :
    (sector.replaceAt location range).rangeAt location = range := by
  cases location <;> rfl

/-- Apply one side of a range split. -/
def splitAt (sector : Sector) (location : Location)
    (bound : Nat) (lowerSide : Bool) : Sector :=
  sector.replaceAt location
    ((sector.rangeAt location).split bound lowerSide)

/-- The source language permits a fan split only after its spoke arity fixes
that fan as an actual face of the sector. -/
def FanAvailable (sector : Sector) : Location → Prop
  | .spoke | .hat => True
  | .fan1 =>
      sector.spoke = FaceRange.singleton 6 ∨
        sector.spoke = FaceRange.singleton 7 ∨
          sector.spoke = FaceRange.singleton 8
  | .fan2 =>
      sector.spoke = FaceRange.singleton 7 ∨
        sector.spoke = FaceRange.singleton 8
  | .fan3 => sector.spoke = FaceRange.singleton 8

instance (sector : Sector) (location : Location) :
    Decidable (sector.FanAvailable location) := by
  cases location <;> simp only [FanAvailable] <;> infer_instance

/-- A legal sector split. -/
def GoodSplit (sector : Sector) (location : Location) (bound : Nat) : Prop :=
  sector.FanAvailable location ∧ (sector.rangeAt location).GoodSplit bound

/-- Boolean legality check for a sector split. -/
def goodSplitChecker (sector : Sector) (location : Location)
    (bound : Nat) : Bool :=
  decide (sector.FanAvailable location) &&
    (sector.rangeAt location).goodSplitChecker bound

theorem goodSplitChecker_eq_true_iff
    (sector : Sector) (location : Location) (bound : Nat) :
    sector.goodSplitChecker location bound = true ↔
      sector.GoodSplit location bound := by
  simp [goodSplitChecker, GoodSplit, FaceRange.goodSplitChecker_eq_true_iff]

/-- Every stored interval in a sector is valid. -/
def Valid (sector : Sector) : Prop :=
  sector.spoke.Valid ∧ sector.hat.Valid ∧ sector.fan1.Valid ∧
    sector.fan2.Valid ∧ sector.fan3.Valid

/-- Boolean validity check for one sector. -/
def validChecker (sector : Sector) : Bool :=
  sector.spoke.validChecker && (sector.hat.validChecker &&
    (sector.fan1.validChecker && (sector.fan2.validChecker &&
      sector.fan3.validChecker)))

theorem validChecker_eq_true_iff (sector : Sector) :
    sector.validChecker = true ↔ sector.Valid := by
  simp [validChecker, Valid, FaceRange.validChecker_eq_true_iff]

/-- Pointwise containment of all five sector ranges. -/
def IsSubset (source target : Sector) : Prop :=
  source.spoke.IsSubset target.spoke ∧
    source.hat.IsSubset target.hat ∧
      source.fan1.IsSubset target.fan1 ∧
        source.fan2.IsSubset target.fan2 ∧
          source.fan3.IsSubset target.fan3

/-- Boolean pointwise sector containment. -/
def subsetChecker (source target : Sector) : Bool :=
  source.spoke.subsetChecker target.spoke &&
    (source.hat.subsetChecker target.hat &&
      (source.fan1.subsetChecker target.fan1 &&
        (source.fan2.subsetChecker target.fan2 &&
          source.fan3.subsetChecker target.fan3)))

theorem subsetChecker_sound {source target : Sector}
    (hcheck : source.subsetChecker target = true) :
    source.IsSubset target := by
  simp only [subsetChecker, Bool.and_eq_true] at hcheck
  exact ⟨FaceRange.subsetChecker_sound hcheck.1,
    FaceRange.subsetChecker_sound hcheck.2.1,
    FaceRange.subsetChecker_sound hcheck.2.2.1,
    FaceRange.subsetChecker_sound hcheck.2.2.2.1,
    FaceRange.subsetChecker_sound hcheck.2.2.2.2⟩

end Sector

/-- The five actual face arities observed in one sector. -/
structure SectorProfile where
  spoke : Nat
  hat : Nat
  fan1 : Nat
  fan2 : Nat
  fan3 : Nat
deriving DecidableEq, Repr

namespace SectorProfile

/-- The arity observed at one addressed location. -/
def valueAt (profile : SectorProfile) : Location → Nat
  | .spoke => profile.spoke
  | .hat => profile.hat
  | .fan1 => profile.fan1
  | .fan2 => profile.fan2
  | .fan3 => profile.fan3

/-- Every observed face belongs to a pentagonal map. -/
def Valid (profile : SectorProfile) : Prop :=
  5 ≤ profile.spoke ∧ 5 ≤ profile.hat ∧ 5 ≤ profile.fan1 ∧
    5 ≤ profile.fan2 ∧ 5 ≤ profile.fan3

/-- The observed arities satisfy all five ranges of a sector. -/
def Fits (profile : SectorProfile) (sector : Sector) : Prop :=
  sector.spoke.Contains profile.spoke ∧
    sector.hat.Contains profile.hat ∧
      sector.fan1.Contains profile.fan1 ∧
        sector.fan2.Contains profile.fan2 ∧
          sector.fan3.Contains profile.fan3

/-- A fit is preserved when every source range is contained in its target. -/
theorem Fits.mono {profile : SectorProfile} {source target : Sector}
    (hfits : profile.Fits source) (hsubset : source.IsSubset target) :
    profile.Fits target :=
  ⟨hsubset.1 _ hfits.1,
    hsubset.2.1 _ hfits.2.1,
    hsubset.2.2.1 _ hfits.2.2.1,
    hsubset.2.2.2.1 _ hfits.2.2.2.1,
    hsubset.2.2.2.2 _ hfits.2.2.2.2⟩

/-- A legal split covers every profile fitting the unsplit sector. -/
theorem fits_splitAt_or
    (profile : SectorProfile) (sector : Sector) (location : Location)
    (bound : Nat) (lowerSide : Bool)
    (hgood : sector.GoodSplit location bound)
    (hfits : profile.Fits sector) :
    profile.Fits (sector.splitAt location bound lowerSide) ∨
      profile.Fits (sector.splitAt location bound (!lowerSide)) := by
  have hbound : bound < 9 := hgood.2.2.2.2
  rcases hfits with ⟨hspoke, hhat, hfan1, hfan2, hfan3⟩
  cases location
  · rcases FaceRange.contains_split_side_or_complement hbound hspoke with
      hleft | hright
    · exact Or.inl ⟨hleft, hhat, hfan1, hfan2, hfan3⟩
    · exact Or.inr ⟨hright, hhat, hfan1, hfan2, hfan3⟩
  · rcases FaceRange.contains_split_side_or_complement hbound hhat with
      hleft | hright
    · exact Or.inl ⟨hspoke, hleft, hfan1, hfan2, hfan3⟩
    · exact Or.inr ⟨hspoke, hright, hfan1, hfan2, hfan3⟩
  · rcases FaceRange.contains_split_side_or_complement hbound hfan1 with
      hleft | hright
    · exact Or.inl ⟨hspoke, hhat, hleft, hfan2, hfan3⟩
    · exact Or.inr ⟨hspoke, hhat, hright, hfan2, hfan3⟩
  · rcases FaceRange.contains_split_side_or_complement hbound hfan2 with
      hleft | hright
    · exact Or.inl ⟨hspoke, hhat, hfan1, hleft, hfan3⟩
    · exact Or.inr ⟨hspoke, hhat, hfan1, hright, hfan3⟩
  · rcases FaceRange.contains_split_side_or_complement hbound hfan3 with
      hleft | hright
    · exact Or.inl ⟨hspoke, hhat, hfan1, hfan2, hleft⟩
    · exact Or.inr ⟨hspoke, hhat, hfan1, hfan2, hright⟩

/-- Forgetting a split restriction recovers a fit of the original sector. -/
theorem fits_of_fits_splitAt
    (profile : SectorProfile) (sector : Sector) (location : Location)
    (bound : Nat) (lowerSide : Bool)
    (hgood : sector.GoodSplit location bound)
    (hfits : profile.Fits (sector.splitAt location bound lowerSide)) :
    profile.Fits sector := by
  rcases hfits with ⟨hspoke, hhat, hfan1, hfan2, hfan3⟩
  cases location
  · exact ⟨FaceRange.contains_of_contains_split hgood.2.1 hspoke,
      hhat, hfan1, hfan2, hfan3⟩
  · exact ⟨hspoke, FaceRange.contains_of_contains_split hgood.2.1 hhat,
      hfan1, hfan2, hfan3⟩
  · exact ⟨hspoke, hhat,
      FaceRange.contains_of_contains_split hgood.2.1 hfan1,
      hfan2, hfan3⟩
  · exact ⟨hspoke, hhat, hfan1,
      FaceRange.contains_of_contains_split hgood.2.1 hfan2, hfan3⟩
  · exact ⟨hspoke, hhat, hfan1, hfan2,
      FaceRange.contains_of_contains_split hgood.2.1 hfan3⟩

/-- A side condition obtained from one sector can be imposed on another
sector already fitted by the same observed profile. -/
theorem fits_splitAt_of_fits_splitAt_and_fits
    (profile : SectorProfile) (source target : Sector)
    (location : Location) (bound : Nat) (lowerSide : Bool)
    (hbound : bound < 9)
    (hsource : profile.Fits (source.splitAt location bound lowerSide))
    (htarget : profile.Fits target) :
    profile.Fits (target.splitAt location bound lowerSide) := by
  rcases hsource with ⟨hsourceSpoke, hsourceHat, hsourceFan1,
    hsourceFan2, hsourceFan3⟩
  rcases htarget with ⟨htargetSpoke, htargetHat, htargetFan1,
    htargetFan2, htargetFan3⟩
  cases location
  · exact ⟨FaceRange.contains_split_of_contains_split_and_contains
      hbound hsourceSpoke htargetSpoke,
      htargetHat, htargetFan1, htargetFan2, htargetFan3⟩
  · exact ⟨htargetSpoke,
      FaceRange.contains_split_of_contains_split_and_contains
        hbound hsourceHat htargetHat,
      htargetFan1, htargetFan2, htargetFan3⟩
  · exact ⟨htargetSpoke, htargetHat,
      FaceRange.contains_split_of_contains_split_and_contains
        hbound hsourceFan1 htargetFan1,
      htargetFan2, htargetFan3⟩
  · exact ⟨htargetSpoke, htargetHat, htargetFan1,
      FaceRange.contains_split_of_contains_split_and_contains
        hbound hsourceFan2 htargetFan2,
      htargetFan3⟩
  · exact ⟨htargetSpoke, htargetHat, htargetFan1, htargetFan2,
      FaceRange.contains_split_of_contains_split_and_contains
        hbound hsourceFan3 htargetFan3⟩

end SectorProfile

/-- A complete cyclic list of second-neighborhood sectors. -/
abbrev Pattern := List Sector

/-- The observed arities in the same cyclic order. -/
abbrev HubProfile := List SectorProfile

namespace Pattern

/-- The completely unconstrained pattern of a given hub size. -/
def free (hubSize : Nat) : Pattern :=
  List.replicate hubSize (Sector.plain FaceRange.free FaceRange.free)

/-- Every sector of the pattern is well formed. -/
def Valid (pattern : Pattern) : Prop :=
  ∀ sector ∈ pattern, sector.Valid

/-- Boolean pattern validity. -/
def validChecker (pattern : Pattern) : Bool :=
  pattern.all Sector.validChecker

theorem validChecker_eq_true_iff (pattern : Pattern) :
    pattern.validChecker = true ↔ pattern.Valid := by
  simp [validChecker, Valid, Sector.validChecker_eq_true_iff]

/-- Pointwise containment of two equally long cyclic patterns. -/
def IsSubset : Pattern → Pattern → Prop
  | [], [] => True
  | source :: sources, target :: targets =>
      source.IsSubset target ∧ IsSubset sources targets
  | _, _ => False

/-- Boolean pointwise pattern containment. -/
def subsetChecker : Pattern → Pattern → Bool
  | [], [] => true
  | source :: sources, target :: targets =>
      source.subsetChecker target && subsetChecker sources targets
  | _, _ => false

theorem subsetChecker_sound {source target : Pattern}
    (hcheck : source.subsetChecker target = true) :
    source.IsSubset target := by
  induction source generalizing target with
  | nil =>
      cases target <;> simp [subsetChecker, IsSubset] at hcheck ⊢
  | cons source sources ih =>
      cases target with
      | nil => simp [subsetChecker] at hcheck
      | cons target targets =>
          rcases Bool.and_eq_true_iff.mp (by
            simpa [subsetChecker] using hcheck) with ⟨hhead, htail⟩
          exact ⟨Sector.subsetChecker_sound hhead, ih htail⟩

/-- A profile and pattern have the same sector count and fit pointwise. -/
def Fits (profile : HubProfile) (pattern : Pattern) : Prop :=
  List.Forall₂ SectorProfile.Fits profile pattern

/-- Pointwise pattern containment preserves profile fitting. -/
theorem Fits.mono {profile : HubProfile} {source target : Pattern}
    (hfits : Fits profile source) (hsubset : source.IsSubset target) :
    Fits profile target := by
  induction hfits generalizing target with
  | nil =>
      cases target with
      | nil => exact .nil
      | cons target targets => simp [IsSubset] at hsubset
  | cons hhead htail ih =>
      cases target with
      | nil => simp [IsSubset] at hsubset
      | cons target targets =>
          exact .cons (hhead.mono hsubset.1) (ih hsubset.2)

/-- Replace one sector, leaving an out-of-range address unchanged. -/
def modifySector (pattern : Pattern) (index : Nat)
    (update : Sector → Sector) : Pattern :=
  match index, pattern with
  | 0, sector :: rest => update sector :: rest
  | index + 1, sector :: rest => sector :: modifySector rest index update
  | _, [] => []

@[simp] theorem length_modifySector
    (pattern : Pattern) (index : Nat) (update : Sector → Sector) :
    (pattern.modifySector index update).length = pattern.length := by
  induction index generalizing pattern with
  | zero => cases pattern <;> rfl
  | succ index ih =>
      cases pattern with
      | nil => rfl
      | cons sector rest => simp [modifySector, ih]

/-- Rotate sectors to the left without reducing an oversized amount modulo
the length. -/
def rotate (amount : Nat) (pattern : Pattern) : Pattern :=
  pattern.drop amount ++ pattern.take amount

/-- Reflect one sector after supplying the hat that follows it before
reflection.  Fans reverse within the one, two, or three positions determined
by a fixed spoke size. -/
def mirrorSectorWithHat (sector : Sector) (nextHat : FaceRange) : Sector :=
  if sector.spoke = FaceRange.singleton 7 then
    ⟨sector.spoke, nextHat, sector.fan2, sector.fan1, sector.fan3⟩
  else if sector.spoke = FaceRange.singleton 8 then
    ⟨sector.spoke, nextHat, sector.fan3, sector.fan2, sector.fan1⟩
  else
    ⟨sector.spoke, nextHat, sector.fan1, sector.fan2, sector.fan3⟩

/-- Tail-recursive reflection of a cyclic pattern across its root spoke. -/
def mirrorAux (firstHat : FaceRange) : Pattern → Pattern → Pattern
  | [], reversed => reversed
  | sector :: rest, reversed =>
      let nextHat := match rest with
        | [] => firstHat
        | next :: _ => next.hat
      mirrorAux firstHat rest
        (mirrorSectorWithHat sector nextHat :: reversed)

/-- Reflection across the root spoke, including the cyclic shift of hats. -/
def mirror : Pattern → Pattern
  | [] => []
  | sector :: rest => mirrorAux sector.hat (sector :: rest) []

/-- One presentation split command.  Indices are zero based internally. -/
structure SplitCode where
  location : Location
  sector : Nat
  bound : Nat
  lowerSide : Bool
deriving DecidableEq, Repr

/-- The addressed split is nontrivial and geometrically available. -/
def goodSplitChecker (pattern : Pattern) (code : SplitCode) : Bool :=
  match pattern[code.sector]? with
  | none => false
  | some sector => sector.goodSplitChecker code.location code.bound

/-- Apply the selected half of a split to a pattern. -/
def split (pattern : Pattern) (code : SplitCode) : Pattern :=
  pattern.modifySector code.sector
    (fun sector => sector.splitAt code.location code.bound code.lowerSide)

/-- Complement the selected side of a split. -/
def SplitCode.complement (code : SplitCode) : SplitCode :=
  { code with lowerSide := !code.lowerSide }

@[simp] theorem SplitCode.complement_location (code : SplitCode) :
    code.complement.location = code.location := rfl

@[simp] theorem SplitCode.complement_sector (code : SplitCode) :
    code.complement.sector = code.sector := rfl

@[simp] theorem SplitCode.complement_bound (code : SplitCode) :
    code.complement.bound = code.bound := rfl

@[simp] theorem SplitCode.complement_lowerSide (code : SplitCode) :
    code.complement.lowerSide = !code.lowerSide := rfl

/-- A legal split covers every profile fitting the original pattern. -/
theorem fits_split_or
    (profile : HubProfile) (pattern : Pattern) (code : SplitCode)
    (hgood : pattern.goodSplitChecker code = true)
    (hfits : Fits profile pattern) :
    Fits profile (pattern.split code) ∨
      Fits profile (pattern.split code.complement) := by
  rcases code with ⟨location, index, bound, lowerSide⟩
  induction index generalizing profile pattern with
  | zero =>
      cases pattern with
      | nil => simp [goodSplitChecker] at hgood
      | cons sector rest =>
          cases profile with
          | nil => cases hfits
          | cons observed tail =>
              cases hfits with
              | cons hhead htail =>
                  have hsectorGood :
                      sector.GoodSplit location bound :=
                    (Sector.goodSplitChecker_eq_true_iff _ _ _).1 (by
                      simpa [goodSplitChecker] using hgood)
                  rcases observed.fits_splitAt_or sector location
                      bound lowerSide hsectorGood hhead with
                    hleft | hright
                  · exact Or.inl (.cons hleft htail)
                  · exact Or.inr (.cons hright htail)
  | succ index ih =>
      cases pattern with
      | nil => simp [goodSplitChecker] at hgood
      | cons sector rest =>
          cases profile with
          | nil => cases hfits
          | cons observed tail =>
              cases hfits with
              | cons hhead htail =>
                  have htailGood :
                      goodSplitChecker rest
                          ⟨location, index, bound, lowerSide⟩ =
                        true := by
                    simpa [goodSplitChecker] using hgood
                  rcases ih (profile := tail) (pattern := rest)
                      (hgood := htailGood) (hfits := htail) with
                    hleft | hright
                  · exact Or.inl (.cons hhead hleft)
                  · exact Or.inr (.cons hhead hright)

/-- Forgetting one split restriction recovers a fit of the original pattern. -/
theorem fits_of_fits_split
    (profile : HubProfile) (pattern : Pattern) (code : SplitCode)
    (hgood : pattern.goodSplitChecker code = true)
    (hfits : Fits profile (pattern.split code)) :
    Fits profile pattern := by
  rcases code with ⟨location, index, bound, lowerSide⟩
  induction index generalizing profile pattern with
  | zero =>
      cases pattern with
      | nil => simpa [split, modifySector] using hfits
      | cons sector rest =>
          cases profile with
          | nil => cases hfits
          | cons observed tail =>
              cases hfits with
              | cons hhead htail =>
                  have hsectorGood :
                      sector.GoodSplit location bound :=
                    (Sector.goodSplitChecker_eq_true_iff _ _ _).1 (by
                      simpa [goodSplitChecker] using hgood)
                  exact .cons
                    (observed.fits_of_fits_splitAt sector location
                      bound lowerSide hsectorGood hhead)
                    htail
  | succ index ih =>
      cases pattern with
      | nil => simpa [split, modifySector] using hfits
      | cons sector rest =>
          cases profile with
          | nil => cases hfits
          | cons observed tail =>
              cases hfits with
              | cons hhead htail =>
                  have htailGood :
                      goodSplitChecker rest
                          ⟨location, index, bound, lowerSide⟩ = true := by
                    simpa [goodSplitChecker] using hgood
                  exact .cons hhead
                    (ih (profile := tail) (pattern := rest)
                      (hgood := htailGood) (hfits := htail))

/-- A side condition cut from a context can be imposed on a goal pattern
fitted by the same profile. -/
theorem fits_split_of_fits_contextSplit_and_fits
    (profile : HubProfile) (context pattern : Pattern) (code : SplitCode)
    (hcontextGood : context.goodSplitChecker code = true)
    (hpatternGood : pattern.goodSplitChecker code = true)
    (hcontext : Fits profile (context.split code))
    (hpattern : Fits profile pattern) :
    Fits profile (pattern.split code) := by
  rcases code with ⟨location, index, bound, lowerSide⟩
  induction index generalizing profile context pattern with
  | zero =>
      cases context with
      | nil => simp [goodSplitChecker] at hcontextGood
      | cons contextSector contextRest =>
          cases pattern with
          | nil => simp [goodSplitChecker] at hpatternGood
          | cons patternSector patternRest =>
              cases profile with
              | nil => cases hpattern
              | cons observed tail =>
                  cases hcontext with
                  | cons hcontextHead hcontextTail =>
                      cases hpattern with
                      | cons hpatternHead hpatternTail =>
                          have hpatternSectorGood :
                              patternSector.GoodSplit location bound :=
                            (Sector.goodSplitChecker_eq_true_iff _ _ _).1 (by
                              simpa [goodSplitChecker] using hpatternGood)
                          exact .cons
                            (observed.fits_splitAt_of_fits_splitAt_and_fits
                              contextSector patternSector location
                              bound lowerSide
                              hpatternSectorGood.2.2.2.2
                              hcontextHead hpatternHead)
                            hpatternTail
  | succ index ih =>
      cases context with
      | nil => simp [goodSplitChecker] at hcontextGood
      | cons contextSector contextRest =>
          cases pattern with
          | nil => simp [goodSplitChecker] at hpatternGood
          | cons patternSector patternRest =>
              cases profile with
              | nil => cases hpattern
              | cons observed tail =>
                  cases hcontext with
                  | cons hcontextHead hcontextTail =>
                      cases hpattern with
                      | cons hpatternHead hpatternTail =>
                          exact .cons hpatternHead
                            (ih (profile := tail)
                              (context := contextRest)
                              (pattern := patternRest)
                              (hcontextGood := by
                                simpa [goodSplitChecker] using hcontextGood)
                              (hpatternGood := by
                                simpa [goodSplitChecker] using hpatternGood)
                              (hcontext := hcontextTail)
                              (hpattern := hpatternTail))

/-- Patterns used by the left context, left goal, and right goal of one
presentation split. -/
def splitResult (context pattern : Pattern) (code : SplitCode) :
    SplitResult Pattern :=
  let left := pattern.split code
  { leftContext :=
      if context.goodSplitChecker code then context.split code else left
    left := left
    right := pattern.split code.complement }

/-- Reflection followed by rotation, as named by a presentation similarity
leaf. -/
structure SimilarityCode where
  mirror : Bool
  rotation : Nat
deriving DecidableEq, Repr

/-- The transformed current goal compared with a previously closed pattern. -/
def SimilarityCode.transform (code : SimilarityCode)
    (pattern : Pattern) : Pattern :=
  rotate code.rotation (if code.mirror then pattern.mirror else pattern)

/-- Check that the transformed goal pattern is contained in the previously
closed pattern. -/
def similarityChecker (code : SimilarityCode)
    (known pattern : Pattern) : Bool :=
  (code.transform pattern).subsetChecker known

section ObservedHub

universe u

variable {Hub : Type u}

/-- Interpret patterns through the concrete second-neighborhood profile
observed at each semantic hub. -/
def observedSemantics (valid : Hub → Prop) (observe : Hub → HubProfile) :
    Semantics Hub Pattern where
  valid := valid
  fits hub pattern := Fits (observe hub) pattern

/-- Geometric realization of the two cyclic symmetries used by presentation
similarity leaves. -/
structure ObservedSymmetry (valid : Hub → Prop)
    (observe : Hub → HubProfile) where
  mirrorHub : Hub → Hub
  rotateHub : Nat → Hub → Hub
  valid_mirror : ∀ {hub}, valid hub → valid (mirrorHub hub)
  valid_rotate : ∀ amount {hub}, valid hub → valid (rotateHub amount hub)
  fits_mirror : ∀ {hub pattern}, Fits (observe hub) pattern →
    Fits (observe (mirrorHub hub)) pattern.mirror
  fits_rotate : ∀ amount {hub pattern}, Fits (observe hub) pattern →
    Fits (observe (rotateHub amount hub)) (pattern.rotate amount)

namespace ObservedSymmetry

/-- Apply the same reflection-then-rotation word to a semantic hub. -/
def transformHub {valid : Hub → Prop} {observe : Hub → HubProfile}
    (symmetry : ObservedSymmetry valid observe)
    (code : SimilarityCode) (hub : Hub) : Hub :=
  symmetry.rotateHub code.rotation
    (if code.mirror then symmetry.mirrorHub hub else hub)

theorem valid_transformHub
    {valid : Hub → Prop} {observe : Hub → HubProfile}
    (symmetry : ObservedSymmetry valid observe)
    (code : SimilarityCode) {hub : Hub} (hvalid : valid hub) :
    valid (symmetry.transformHub code hub) := by
  apply symmetry.valid_rotate code.rotation
  cases code.mirror
  · exact hvalid
  · exact symmetry.valid_mirror hvalid

theorem fits_transformHub
    {valid : Hub → Prop} {observe : Hub → HubProfile}
    (symmetry : ObservedSymmetry valid observe)
    (code : SimilarityCode) {hub : Hub} {pattern : Pattern}
    (hfits : Fits (observe hub) pattern) :
    Fits (observe (symmetry.transformHub code hub))
      (code.transform pattern) := by
  apply symmetry.fits_rotate code.rotation
  cases code.mirror
  · exact hfits
  · exact symmetry.fits_mirror hfits

/-- An accepted similarity leaf transports a hypothetical fitting hub to the
known pattern and contradicts that pattern's prior success. -/
theorem similarity_sound
    {valid : Hub → Prop} {observe : Hub → HubProfile}
    (symmetry : ObservedSymmetry valid observe)
    {code : SimilarityCode} {known pattern : Pattern}
    (hcheck : similarityChecker code known pattern = true)
    (hknown : (observedSemantics valid observe).Successful known) :
    (observedSemantics valid observe).Successful pattern := by
  intro hub hvalid hfits
  let transformed := symmetry.transformHub code hub
  have htransformedValid : valid transformed :=
    symmetry.valid_transformHub code hvalid
  have htransformedFits :
      Fits (observe transformed) (code.transform pattern) :=
    symmetry.fits_transformHub code hfits
  have hsubset : (code.transform pattern).IsSubset known :=
    subsetChecker_sound hcheck
  exact hknown transformed htransformedValid
    (htransformedFits.mono hsubset)

end ObservedSymmetry

/-- The computed left and right goals of a legal split cover its parent
pattern for every observed hub. -/
theorem splitResult_cover
    (valid : Hub → Prop) (observe : Hub → HubProfile)
    {context pattern : Pattern} {code : SplitCode}
    (hcheck : pattern.goodSplitChecker code = true) :
    ∀ hub, (observedSemantics valid observe).valid hub →
      (observedSemantics valid observe).fits hub pattern →
        (observedSemantics valid observe).fits hub
            (splitResult context pattern code).left ∨
          (observedSemantics valid observe).fits hub
            (splitResult context pattern code).right := by
  intro hub _hvalid hfits
  simpa [observedSemantics, splitResult] using
    fits_split_or (observe hub) pattern code hcheck hfits

/-- The retained left context forces the left goal.  If the original context
can itself be split, its selected-side constraint is transferred to the goal;
otherwise the retained context is definitionally the left goal. -/
theorem splitResult_left_forces
    (valid : Hub → Prop) (observe : Hub → HubProfile)
    {context pattern : Pattern} {code : SplitCode}
    (hcheck : pattern.goodSplitChecker code = true)
    (hforces : (observedSemantics valid observe).Forces context pattern) :
    (observedSemantics valid observe).Forces
      (splitResult context pattern code).leftContext
      (splitResult context pattern code).left := by
  intro hub hvalid hleftContext
  by_cases hcontextGood : context.goodSplitChecker code = true
  · have hcontextSplit : Fits (observe hub) (context.split code) := by
      simpa [observedSemantics, splitResult, hcontextGood] using hleftContext
    have hcontext : Fits (observe hub) context :=
      fits_of_fits_split (observe hub) context code hcontextGood hcontextSplit
    have hpattern : Fits (observe hub) pattern :=
      hforces hub hvalid hcontext
    have hleft := fits_split_of_fits_contextSplit_and_fits
      (observe hub) context pattern code hcontextGood hcheck
      hcontextSplit hpattern
    simpa [observedSemantics, splitResult] using hleft
  · simpa [observedSemantics, splitResult, hcontextGood] using hleftContext

/-- Assemble the generic presentation backend once concrete terminal checks
and their soundness theorem are supplied. -/
def backend
    {Leaf : Type*}
    (valid : Hub → Prop) (observe : Hub → HubProfile)
    (symmetry : ObservedSymmetry valid observe)
    (leafCheck : Leaf → Pattern → Bool)
    (leafSound : ∀ {leaf pattern}, leafCheck leaf pattern = true →
      (observedSemantics valid observe).Successful pattern) :
    Backend Hub Pattern Leaf SplitCode SimilarityCode where
  semantics := observedSemantics valid observe
  leafCheck := leafCheck
  leaf_sound := leafSound
  splitResult := splitResult
  splitCheck := fun _context pattern code => pattern.goodSplitChecker code
  split_cover := by
    intro context pattern code hcheck
    exact splitResult_cover valid observe hcheck
  split_left_forces := by
    intro context pattern code hcheck hforces
    exact splitResult_left_forces valid observe hcheck hforces
  similarityCheck := similarityChecker
  similarity_sound := by
    intro code known pattern hcheck hknown
    exact symmetry.similarity_sound hcheck hknown

end ObservedHub

end Pattern

end ClassicalCertificatePresentationPattern

end Mettapedia.GraphTheory.FourColor
