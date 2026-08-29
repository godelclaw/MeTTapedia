import Mettapedia.GraphTheory.FourColor.GoertzelV24TargetAwareReplacementQuantifiers

/-!
# Rich boundary profiles erase to their word supports at a colouring splice

The cumulative corridor state records substantially more than the boundary
colour word: in particular, tracked two-colour connectivity and partial face
data.  Those coordinates are indispensable for evolving a state through the
next Cell.  They do not alter the compatibility test at a literal colouring
splice.  Two colourings glue exactly when their boundary words agree.

This module isolates that distinction.  A set of rich profiles is observed by
an exterior only through the image of its word projection.  Consequently an
unrestricted target-aware replacement theorem for rich profiles still
collapses to inclusion of the projected word supports.  Any genuine gain must
therefore come from a theorem restricting which projected supports are
realized by physical planar exteriors, not merely from retaining more fields
in each profile.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24TargetAwareProfileErasure

universe u v w x

variable {Word : Type u} {LeftProfile : Type v} {RightProfile : Type w}
  {Candidate : Type x}

/-- The boundary words observed from a set of rich profiles. -/
def projectedSupport (word : LeftProfile → Word)
    (profiles : Set LeftProfile) : Set Word :=
  word '' profiles

/-- Literal profile compatibility: one profile on each side has the same
boundary word.  No other profile coordinate enters the colouring splice. -/
def Compatible (leftWord : LeftProfile → Word)
    (rightWord : RightProfile → Word)
    (leftProfiles : Set LeftProfile) (rightProfiles : Set RightProfile) : Prop :=
  ∃ left ∈ leftProfiles, ∃ right ∈ rightProfiles,
    leftWord left = rightWord right

/-- Rich-profile compatibility is exactly intersection of projected word
supports. -/
theorem compatible_iff_projectedSupports_meet
    (leftWord : LeftProfile → Word) (rightWord : RightProfile → Word)
    (leftProfiles : Set LeftProfile) (rightProfiles : Set RightProfile) :
    Compatible leftWord rightWord leftProfiles rightProfiles ↔
      ∃ word : Word,
        word ∈ projectedSupport leftWord leftProfiles ∧
          word ∈ projectedSupport rightWord rightProfiles := by
  constructor
  · rintro ⟨left, hleft, right, hright, hword⟩
    exact ⟨leftWord left, ⟨left, hleft, rfl⟩,
      ⟨right, hright, hword.symm⟩⟩
  · rintro ⟨word, ⟨left, hleft, hleftWord⟩,
      ⟨right, hright, hrightWord⟩⟩
    exact ⟨left, hleft, right, hright, hleftWord.trans hrightWord.symm⟩

/-- Incompatibility of rich profiles is exactly disjointness of their
projected word supports. -/
theorem not_compatible_iff_disjoint_projectedSupports
    (leftWord : LeftProfile → Word) (rightWord : RightProfile → Word)
    (leftProfiles : Set LeftProfile) (rightProfiles : Set RightProfile) :
    ¬ Compatible leftWord rightWord leftProfiles rightProfiles ↔
      Disjoint (projectedSupport leftWord leftProfiles)
        (projectedSupport rightWord rightProfiles) := by
  rw [compatible_iff_projectedSupports_meet, Set.disjoint_left]
  push Not
  rfl

/-- Two rich profile languages with the same projected support are
indistinguishable by every exterior profile language. -/
theorem compatible_iff_of_projectedSupport_eq
    (leftWord : LeftProfile → Word) (rightWord : RightProfile → Word)
    (leftProfiles : Set LeftProfile)
    (first second : Set RightProfile)
    (hprojected : projectedSupport rightWord first =
      projectedSupport rightWord second) :
    Compatible leftWord rightWord leftProfiles first ↔
      Compatible leftWord rightWord leftProfiles second := by
  rw [compatible_iff_projectedSupports_meet,
    compatible_iff_projectedSupports_meet, hprojected]

/-- **Profile-erasure form of the unrestricted target-aware collapse.**
Even when every candidate is presented as a language of rich profiles, an
exterior quantified over arbitrary word supports can be avoided precisely
when some candidate's projected word support is contained in the original
projected word support. -/
theorem unrestricted_profileTargetAware_iff_exists_projected_subset
    (originalWord : LeftProfile → Word) (replacementWord : RightProfile → Word)
    (original : Set LeftProfile)
    (replacement : Candidate → Set RightProfile) :
    (∀ exterior : Set Word,
        Disjoint exterior (projectedSupport originalWord original) →
          ∃ candidate,
            Disjoint exterior
              (projectedSupport replacementWord (replacement candidate))) ↔
      ∃ candidate,
        projectedSupport replacementWord (replacement candidate) ⊆
          projectedSupport originalWord original := by
  exact
    GoertzelV24TargetAwareReplacementQuantifiers.unrestricted_targetAware_iff_exists_subset
      (projectedSupport originalWord original)
      (fun candidate =>
        projectedSupport replacementWord (replacement candidate))

/-- The complement of the projected original support is the explicit maximal
abstract exterior adversary for rich-profile candidates. -/
theorem projected_complement_adversary_of_no_subset
    (originalWord : LeftProfile → Word) (replacementWord : RightProfile → Word)
    (original : Set LeftProfile) (replacement : Candidate → Set RightProfile)
    (hnoSubset : ∀ candidate,
      ¬ projectedSupport replacementWord (replacement candidate) ⊆
        projectedSupport originalWord original) :
    Disjoint (projectedSupport originalWord original)ᶜ
        (projectedSupport originalWord original) ∧
      ∀ candidate,
        ¬ Disjoint (projectedSupport originalWord original)ᶜ
          (projectedSupport replacementWord (replacement candidate)) := by
  exact
    GoertzelV24TargetAwareReplacementQuantifiers.complement_adversary_of_no_subset
      (projectedSupport originalWord original)
      (fun candidate =>
        projectedSupport replacementWord (replacement candidate)) hnoSubset

end GoertzelV24TargetAwareProfileErasure

end Mettapedia.GraphTheory.FourColor
