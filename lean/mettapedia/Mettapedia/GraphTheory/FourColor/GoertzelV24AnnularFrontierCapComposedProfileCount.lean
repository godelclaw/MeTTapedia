import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularFrontierMenuProfileCount
import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularFrontierCapComposedProfileSemantics

/-!
# The cap-correct Seed count factors through finite profiles

The legacy `annularFrontierMenuBSeedCount` filters by the open-tangle Menu
predicate and is therefore the whole good fibre on realizable profiles.  This
file defines the corrected count by filtering only after the pentagonal cap is
restored.  It then proves the exact finite-profile factorization required by a
route-native closure computation.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularFrontierCapComposedProfileCount

open SimpleGraph
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24AnnularFrontierMenu
open GoertzelV24AnnularFrontierCapComposedProfileSemantics

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

/-- The literal fixed-word fibre accepted by Menu B after restoring the cap. -/
noncomputable def capComposedSeedFiber
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (word : CAP5BoundaryWord) : Finset (G.EdgeColoring Color) := by
  classical
  exact (annularFrontierTaitFiber data word).filter
    (RestoredMenuBState data hdata)

theorem mem_capComposedSeedFiber_iff
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (word : CAP5BoundaryWord) (coloring : G.EdgeColoring Color) :
    coloring ∈ capComposedSeedFiber data hdata word ↔
      coloring ∈ annularFrontierTaitFiber data word ∧
        RestoredMenuBState data hdata coloring := by
  classical
  simp [capComposedSeedFiber]

/-- The source-correct number of seeds in one boundary-word fibre. -/
noncomputable def capComposedSeedCount
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (word : CAP5BoundaryWord) : Nat :=
  (capComposedSeedFiber data hdata word).card

@[simp] theorem capComposedSeedCount_apply
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (word : CAP5BoundaryWord) :
    capComposedSeedCount data hdata word =
      (capComposedSeedFiber data hdata word).card :=
  rfl

/-- Positivity has exactly the corrected literal graph meaning. -/
theorem capComposedSeedCount_pos_iff
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (word : CAP5BoundaryWord) :
    0 < capComposedSeedCount data hdata word ↔
      ∃ coloring : G.EdgeColoring Color,
        coloring ∈ annularFrontierTaitFiber data word ∧
          RestoredMenuBState data hdata coloring := by
  rw [capComposedSeedCount_apply]
  constructor
  · intro hpositive
    rcases Finset.card_pos.mp hpositive with ⟨coloring, hmember⟩
    exact ⟨coloring,
      (mem_capComposedSeedFiber_iff
        data hdata word coloring).mp hmember⟩
  · rintro ⟨coloring, hfiber, hmenu⟩
    apply Finset.card_pos.mpr
    exact ⟨coloring,
      (mem_capComposedSeedFiber_iff
        data hdata word coloring).mpr ⟨hfiber, hmenu⟩⟩

/-- **The corrected Seed count is an accepted-profile count.**  It is positive
exactly when some realized profile at the fixed word satisfies the
cap-composed terminal predicate. -/
theorem capComposedSeedCount_pos_iff_exists_profile
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (word : CAP5BoundaryWord) :
    0 < capComposedSeedCount data hdata word ↔
      ∃ profile : AnnularFrontierMenuUniformProfile,
        profile.word = word ∧
          0 < annularFrontierMenuUniformProfileCount data hdata profile ∧
            CapComposedMenuBStateOfProfile profile := by
  constructor
  · intro hpositive
    rcases (capComposedSeedCount_pos_iff data hdata word).mp hpositive with
      ⟨coloring, hfiber, hmenu⟩
    rcases (mem_annularFrontierTaitFiber_iff data word coloring).mp hfiber with
      ⟨hcoloring, hword⟩
    refine ⟨annularFrontierMenuUniformProfile data hdata coloring, ?_, ?_, ?_⟩
    · simpa only [annularFrontierMenuUniformProfile_word] using hword
    · exact (annularFrontierMenuUniformProfileCount_pos_iff data hdata
        (annularFrontierMenuUniformProfile data hdata coloring)).mpr
          ⟨coloring, hcoloring, rfl⟩
    · exact (restoredMenuBState_iff_capComposedOfUniformProfile
        data hdata coloring).mp hmenu
  · rintro ⟨profile, hword, hpositive, hmenu⟩
    rcases (annularFrontierMenuUniformProfileCount_pos_iff
      data hdata profile).mp hpositive with
      ⟨coloring, hcoloring, hprofile⟩
    have hmenuColoring : RestoredMenuBState data hdata coloring := by
      apply (restoredMenuBState_iff_capComposedOfUniformProfile
        data hdata coloring).mpr
      rw [hprofile]
      exact hmenu
    apply (capComposedSeedCount_pos_iff data hdata word).mpr
    refine ⟨coloring, ?_, hmenuColoring⟩
    apply (mem_annularFrontierTaitFiber_iff data word coloring).mpr
    refine ⟨hcoloring, ?_⟩
    have hprofileWord :
        (annularFrontierMenuUniformProfile data hdata coloring).word = word := by
      rw [hprofile]
      exact hword
    simpa only [annularFrontierMenuUniformProfile_word] using hprofileWord

/-- **Zero corrected Seed count is rejection by the finite accepted
language.**  Every cap-composed profile at the fixed word has literal count
zero, and conversely. -/
theorem capComposedSeedCount_eq_zero_iff_forall_profile_count_eq_zero
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (word : CAP5BoundaryWord) :
    capComposedSeedCount data hdata word = 0 ↔
      ∀ profile : AnnularFrontierMenuUniformProfile,
        profile.word = word →
          CapComposedMenuBStateOfProfile profile →
            annularFrontierMenuUniformProfileCount data hdata profile = 0 := by
  constructor
  · intro hseed profile hword hmenu
    by_contra hcount
    have hcountPositive :
        0 < annularFrontierMenuUniformProfileCount data hdata profile :=
      Nat.pos_of_ne_zero hcount
    have hseedPositive : 0 < capComposedSeedCount data hdata word :=
      (capComposedSeedCount_pos_iff_exists_profile
        data hdata word).2 ⟨profile, hword, hcountPositive, hmenu⟩
    omega
  · intro hprofiles
    by_contra hseed
    have hseedPositive : 0 < capComposedSeedCount data hdata word :=
      Nat.pos_of_ne_zero hseed
    rcases (capComposedSeedCount_pos_iff_exists_profile
      data hdata word).1 hseedPositive with
      ⟨profile, hword, hcountPositive, hmenu⟩
    have hcountZero := hprofiles profile hword hmenu
    omega

end

end GoertzelV24AnnularFrontierCapComposedProfileCount

end Mettapedia.GraphTheory.FourColor
