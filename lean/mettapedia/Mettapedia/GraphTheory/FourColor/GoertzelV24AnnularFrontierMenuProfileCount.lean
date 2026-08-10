import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularFrontierMenuProfileSemantics

/-!
# Profile-indexed Menu-B counts for annular frontier fibers

Addendum XXV uses the statement `seeds = 0` in its minimal-counterexample
descent.  The counting functor in the compositional source says that this is
not merely a predicate of a coloring: it is a finite vector of counts indexed
by the transfer profile.  This file gives that factorization for the actual
five-stub Menu-B condition.

For each computed uniform profile, its count is the number of literal Tait
colorings carrying that profile.  Equality of profiles already preserves Menu
B, so the positive seed-count target is equivalent to the existence of a
positive count at an accepted finite profile.  No corridor, self-loop, or
base enumeration is asserted here; those are the later L1--L3 ingredients
that must establish positivity.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularFrontierMenu

open SimpleGraph
open GoertzelV24ClosedWebBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

/-- The literal fiber of Tait colorings at one complete finite Menu-B
profile.  This is the source `Count` vector's entry at that profile, before
the corridor supplies its second boundary coordinate. -/
noncomputable def annularFrontierMenuUniformProfileFiber
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (profile : AnnularFrontierMenuUniformProfile) :
    Finset (G.EdgeColoring Color) := by
  classical
  exact Finset.univ.filter fun coloring =>
    IsTaitEdgeColoring G coloring ∧
      annularFrontierMenuUniformProfile data hdata coloring = profile

/-- Membership in a generated profile-count fiber has exactly its literal
graph meaning. -/
theorem mem_annularFrontierMenuUniformProfileFiber_iff
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (profile : AnnularFrontierMenuUniformProfile)
    (coloring : G.EdgeColoring Color) :
    coloring ∈ annularFrontierMenuUniformProfileFiber data hdata profile ↔
      IsTaitEdgeColoring G coloring ∧
        annularFrontierMenuUniformProfile data hdata coloring = profile := by
  classical
  simp [annularFrontierMenuUniformProfileFiber]

/-- The generated natural-number count at one finite Menu-B profile. -/
noncomputable def annularFrontierMenuUniformProfileCount
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (profile : AnnularFrontierMenuUniformProfile) : Nat :=
  (annularFrontierMenuUniformProfileFiber data hdata profile).card

@[simp] theorem annularFrontierMenuUniformProfileCount_apply
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (profile : AnnularFrontierMenuUniformProfile) :
    annularFrontierMenuUniformProfileCount data hdata profile =
      (annularFrontierMenuUniformProfileFiber data hdata profile).card :=
  rfl

/-- Positivity of a profile count is exactly realization by an actual Tait
coloring. -/
theorem annularFrontierMenuUniformProfileCount_pos_iff
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (profile : AnnularFrontierMenuUniformProfile) :
    0 < annularFrontierMenuUniformProfileCount data hdata profile ↔
      ∃ coloring : G.EdgeColoring Color,
        IsTaitEdgeColoring G coloring ∧
          annularFrontierMenuUniformProfile data hdata coloring = profile := by
  rw [annularFrontierMenuUniformProfileCount_apply]
  constructor
  · intro hpositive
    rcases Finset.card_pos.mp hpositive with ⟨coloring, hmember⟩
    exact ⟨coloring,
      (mem_annularFrontierMenuUniformProfileFiber_iff
        data hdata profile coloring).mp hmember⟩
  · rintro ⟨coloring, hcoloring, hprofile⟩
    apply Finset.card_pos.mpr
    exact ⟨coloring,
      (mem_annularFrontierMenuUniformProfileFiber_iff
        data hdata profile coloring).mpr ⟨hcoloring, hprofile⟩⟩

/-- The boundary-word coordinate of a computed uniform profile is literal. -/
@[simp] theorem annularFrontierMenuUniformProfile_word
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (coloring : G.EdgeColoring Color) :
    (annularFrontierMenuUniformProfile data hdata coloring).word =
      data.innerBoundaryWord coloring :=
  rfl

/-- An occupied finite profile is accepted precisely when one (and hence
every) literal coloring carrying it realizes the source's Menu-B state. -/
def AnnularFrontierMenuUniformProfileHasMenuB
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (profile : AnnularFrontierMenuUniformProfile) : Prop :=
  ∃ coloring : G.EdgeColoring Color,
    IsTaitEdgeColoring G coloring ∧
      annularFrontierMenuUniformProfile data hdata coloring = profile ∧
        AnnularFrontierMenuBState data coloring

/-- The accepted-profile predicate is independent of the chosen realizing
coloring because the uniform code contains exactly the Menu-B data. -/
theorem annularFrontierMenuUniformProfileHasMenuB_iff
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (profile : AnnularFrontierMenuUniformProfile)
    (coloring : G.EdgeColoring Color) (hcoloring : IsTaitEdgeColoring G coloring)
    (hprofile : annularFrontierMenuUniformProfile data hdata coloring = profile) :
    AnnularFrontierMenuUniformProfileHasMenuB data hdata profile ↔
      AnnularFrontierMenuBState data coloring := by
  constructor
  · rintro ⟨other, hotherColoring, hotherProfile, hmenu⟩
    exact (annularFrontierMenuBState_iff_of_uniformProfile_eq
      data hdata other coloring (hotherProfile.trans hprofile.symm)).mp hmenu
  · intro hmenu
    exact ⟨coloring, hcoloring, hprofile, hmenu⟩

/-- The literal Seed-Lemma target factors through the finite generated
profile counts: it is positive exactly when an accepted profile at the fixed
good-word interface has positive count. -/
theorem annularFrontierMenuBSeedCount_pos_iff_exists_uniformProfile
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (word : CAP5BoundaryWord) :
    0 < annularFrontierMenuBSeedCount data word ↔
      ∃ profile : AnnularFrontierMenuUniformProfile,
        profile.word = word ∧
          0 < annularFrontierMenuUniformProfileCount data hdata profile ∧
            AnnularFrontierMenuUniformProfileHasMenuB data hdata profile := by
  constructor
  · intro hpositive
    rcases (annularFrontierMenuBSeedCount_pos_iff data word).mp hpositive with
      ⟨coloring, hfiber, hmenu⟩
    rcases (mem_annularFrontierTaitFiber_iff data word coloring).mp hfiber with
      ⟨hcoloring, hword⟩
    refine ⟨annularFrontierMenuUniformProfile data hdata coloring, ?_, ?_, ?_⟩
    · simpa only [annularFrontierMenuUniformProfile_word] using hword
    · exact (annularFrontierMenuUniformProfileCount_pos_iff data hdata
        (annularFrontierMenuUniformProfile data hdata coloring)).mpr
          ⟨coloring, hcoloring, rfl⟩
    · exact ⟨coloring, hcoloring, rfl, hmenu⟩
  · rintro ⟨profile, hword, hpositive, haccepted⟩
    rcases (annularFrontierMenuUniformProfileCount_pos_iff
      data hdata profile).mp hpositive with ⟨coloring, hcoloring, hprofile⟩
    have hmenu : AnnularFrontierMenuBState data coloring :=
      (annularFrontierMenuUniformProfileHasMenuB_iff
        data hdata profile coloring hcoloring hprofile).mp haccepted
    apply (annularFrontierMenuBSeedCount_pos_iff data word).mpr
    refine ⟨coloring, ?_, hmenu⟩
    apply (mem_annularFrontierTaitFiber_iff data word coloring).mpr
    refine ⟨hcoloring, ?_⟩
    have hprofileWord :
        (annularFrontierMenuUniformProfile data hdata coloring).word = word := by
      rw [hprofile]
      exact hword
    simpa only [annularFrontierMenuUniformProfile_word] using hprofileWord

/-- Source-facing form of the count factorization: the accepting condition is
the decidable finite-profile Menu-B predicate itself, not an existential over
an unmentioned graph coloring. -/
theorem annularFrontierMenuBSeedCount_pos_iff_exists_profileMenuB
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (word : CAP5BoundaryWord) :
    0 < annularFrontierMenuBSeedCount data word ↔
      ∃ profile : AnnularFrontierMenuUniformProfile,
        profile.word = word ∧
          0 < annularFrontierMenuUniformProfileCount data hdata profile ∧
            AnnularFrontierMenuBStateOfProfile profile := by
  constructor
  · intro hpositive
    rcases (annularFrontierMenuBSeedCount_pos_iff data word).mp hpositive with
      ⟨coloring, hfiber, hmenu⟩
    rcases (mem_annularFrontierTaitFiber_iff data word coloring).mp hfiber with
      ⟨hcoloring, hword⟩
    refine ⟨annularFrontierMenuUniformProfile data hdata coloring, ?_, ?_, ?_⟩
    · simpa only [annularFrontierMenuUniformProfile_word] using hword
    · exact (annularFrontierMenuUniformProfileCount_pos_iff data hdata
        (annularFrontierMenuUniformProfile data hdata coloring)).mpr
          ⟨coloring, hcoloring, rfl⟩
    · exact (annularFrontierMenuBState_iff_of_uniformProfile
        data hdata coloring).mp hmenu
  · rintro ⟨profile, hword, hpositive, hmenu⟩
    rcases (annularFrontierMenuUniformProfileCount_pos_iff
      data hdata profile).mp hpositive with ⟨coloring, hcoloring, hprofile⟩
    have hmenuColoring : AnnularFrontierMenuBState data coloring := by
      have hprofileMenu : AnnularFrontierMenuBStateOfProfile
          (annularFrontierMenuUniformProfile data hdata coloring) := by
        rw [hprofile]
        exact hmenu
      exact (annularFrontierMenuBState_iff_of_uniformProfile
        data hdata coloring).mpr hprofileMenu
    apply (annularFrontierMenuBSeedCount_pos_iff data word).mpr
    refine ⟨coloring, ?_, hmenuColoring⟩
    apply (mem_annularFrontierTaitFiber_iff data word coloring).mpr
    refine ⟨hcoloring, ?_⟩
    have hprofileWord :
        (annularFrontierMenuUniformProfile data hdata coloring).word = word := by
      rw [hprofile]
      exact hword
    simpa only [annularFrontierMenuUniformProfile_word] using hprofileWord

end

end GoertzelV24AnnularFrontierMenu

end Mettapedia.GraphTheory.FourColor
