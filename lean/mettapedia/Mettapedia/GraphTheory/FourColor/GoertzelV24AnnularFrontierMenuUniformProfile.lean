import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularFrontierMenuFiniteCode

/-!
# A fixed finite profile carrier for annular Menu-B states

The source transfer state must have one fixed finite carrier before a
pigeonhole repeat can compare two cross-sections.  A dependent carrier of
active cap ports is convenient for local graph arguments, but it changes when
the cap word changes.  Here the carrier is made uniform: retain the complete
five-edge boundary word and record, for every color pair and every pair of cap
positions, whether the corresponding active ports lie in the same selected
component.

This is the boundary-color plus connectivity part of the source `Count`
profile.  Capped face progress is intentionally not duplicated here: Menu B
does not inspect it, while a later corridor construction still has to supply
that coordinate for the full transfer engine.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularFrontierMenu

open SimpleGraph
open GoertzelV24ClosedWebBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

/-- A uniform Boolean table for the component-pairing coordinate.  Inactive
cap positions are recorded as `false`; the accompanying cap word tells which
positions are active for each color pair. -/
abbrev AnnularFrontierMenuConnectionTable :=
  Color → Color → Fin 5 → Fin 5 → Bool

/-- The computed table entry is true exactly for two active cap positions in
the same selected-pair support component. -/
noncomputable def annularFrontierMenuConnectionTable
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (coloring : G.EdgeColoring Color) : AnnularFrontierMenuConnectionTable := by
  classical
  intro first second left right
  by_cases hleft : left ∈ cap5ActiveSupport first second
      (data.innerBoundaryWord coloring)
  · by_cases hright : right ∈ cap5ActiveSupport first second
        (data.innerBoundaryWord coloring)
    · exact decide
        (annularFrontierActivePairPortComponent data hdata coloring first second
          ⟨left, hleft⟩ =
          annularFrontierActivePairPortComponent data hdata coloring first second
            ⟨right, hright⟩)
    · exact false
  · exact false

/-- The Boolean entry has its literal graph meaning. -/
theorem annularFrontierMenuConnectionTable_eq_true_iff
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (coloring : G.EdgeColoring Color) (first second : Color)
    (left right : Fin 5) :
    annularFrontierMenuConnectionTable data hdata coloring first second left right = true ↔
      ∃ hleft : left ∈ cap5ActiveSupport first second
          (data.innerBoundaryWord coloring),
        ∃ hright : right ∈ cap5ActiveSupport first second
          (data.innerBoundaryWord coloring),
          annularFrontierActivePairPortComponent data hdata coloring first second
            ⟨left, hleft⟩ =
            annularFrontierActivePairPortComponent data hdata coloring first second
              ⟨right, hright⟩ := by
  classical
  unfold annularFrontierMenuConnectionTable
  by_cases hleft : left ∈ cap5ActiveSupport first second
      (data.innerBoundaryWord coloring)
  · by_cases hright : right ∈ cap5ActiveSupport first second
        (data.innerBoundaryWord coloring)
    · simp [hleft, hright]
    · simp [hleft, hright]
  · simp [hleft]

/-- Addendum VII in a fixed, nondependent table: Menu B for one selected
pair means two active cap ports receive a false same-component entry. -/
theorem annularFrontierMenuBForPair_iff_exists_active_connectionTable_false
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (coloring : G.EdgeColoring Color) (first second : Color) :
    AnnularFrontierMenuBForPair data coloring first second ↔
      ∃ left right : Fin 5,
        left ∈ cap5ActiveSupport first second (data.innerBoundaryWord coloring) ∧
          right ∈ cap5ActiveSupport first second (data.innerBoundaryWord coloring) ∧
          annularFrontierMenuConnectionTable data hdata coloring
            first second left right = false := by
  constructor
  · intro hmenu
    rcases (annularFrontierMenuBForPair_iff_exists_not_mem_connectionProfile
      data hdata coloring first second).mp hmenu with
      ⟨left, right, hseparated⟩
    refine ⟨left.1, right.1, left.2, right.2, ?_⟩
    by_cases hconnected :
        annularFrontierActivePairPortComponent data hdata coloring first second left =
          annularFrontierActivePairPortComponent data hdata coloring first second right
    · exfalso
      apply hseparated
      exact (mem_annularFrontierPairConnectionProfile_iff
        data hdata coloring first second (left, right)).mpr hconnected
    · simp [annularFrontierMenuConnectionTable, left.2, right.2, hconnected]
  · rintro ⟨left, right, hleft, hright, hfalse⟩
    apply (annularFrontierMenuBForPair_iff_exists_not_mem_connectionProfile
      data hdata coloring first second).mpr
    let leftPort : AnnularFrontierActivePairPort data coloring first second :=
      ⟨left, hleft⟩
    let rightPort : AnnularFrontierActivePairPort data coloring first second :=
      ⟨right, hright⟩
    refine ⟨leftPort, rightPort, ?_⟩
    intro hconnected
    have hcomponent :
        annularFrontierActivePairPortComponent data hdata coloring first second leftPort =
          annularFrontierActivePairPortComponent data hdata coloring first second rightPort :=
      (mem_annularFrontierPairConnectionProfile_iff
        data hdata coloring first second (leftPort, rightPort)).mp hconnected
    have htrue :
        annularFrontierMenuConnectionTable data hdata coloring
          first second left right = true :=
      (annularFrontierMenuConnectionTable_eq_true_iff
        data hdata coloring first second left right).mpr
        ⟨hleft, hright, by simpa [leftPort, rightPort] using hcomponent⟩
    rw [htrue] at hfalse
    cases hfalse

/-- The finite fixed carrier that controls Menu-B membership: the actual
five-edge boundary word and its complete selected-pair connectivity table. -/
structure AnnularFrontierMenuUniformProfile where
  word : CAP5BoundaryWord
  connectionTable : AnnularFrontierMenuConnectionTable

/-- An explicit enumeration of the profile carrier.  Keeping this instance
local to the source profile makes the finite-state premise of the later
pigeonhole argument a theorem of the actual data representation. -/
noncomputable instance : Fintype AnnularFrontierMenuUniformProfile :=
  Fintype.ofInjective
    (fun profile : AnnularFrontierMenuUniformProfile =>
      (profile.word, profile.connectionTable))
    (by
      intro left right heq
      cases left
      cases right
      cases heq
      rfl)

/-- Compute the uniform Menu-B profile from an actual coloring. -/
noncomputable def annularFrontierMenuUniformProfile
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (coloring : G.EdgeColoring Color) : AnnularFrontierMenuUniformProfile where
  word := data.innerBoundaryWord coloring
  connectionTable := annularFrontierMenuConnectionTable data hdata coloring

/-- The uniform Menu-B profile carrier is finite by construction. -/
theorem annularFrontierMenuUniformProfile_finite :
    Finite AnnularFrontierMenuUniformProfile := by
  classical
  infer_instance

/-- Equal uniform tables preserve Menu B for any selected color pair once
their boundary-word coordinate agrees. -/
theorem annularFrontierMenuBForPair_iff_of_word_eq_of_connectionTable_eq
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (leftColoring rightColoring : G.EdgeColoring Color)
    (hword : data.innerBoundaryWord leftColoring =
      data.innerBoundaryWord rightColoring)
    (htable : annularFrontierMenuConnectionTable data hdata leftColoring =
      annularFrontierMenuConnectionTable data hdata rightColoring)
    (first second : Color) :
    AnnularFrontierMenuBForPair data leftColoring first second ↔
      AnnularFrontierMenuBForPair data rightColoring first second := by
  rw [annularFrontierMenuBForPair_iff_exists_active_connectionTable_false
      data hdata leftColoring first second,
    annularFrontierMenuBForPair_iff_exists_active_connectionTable_false
      data hdata rightColoring first second]
  constructor
  · rintro ⟨left, right, hleft, hright, hfalse⟩
    refine ⟨left, right, ?_, ?_, ?_⟩
    · simpa only [hword] using hleft
    · simpa only [hword] using hright
    · exact (congrFun (congrFun (congrFun (congrFun htable first) second) left)
        right).symm.trans hfalse
  · rintro ⟨left, right, hleft, hright, hfalse⟩
    refine ⟨left, right, ?_, ?_, ?_⟩
    · simpa only [hword] using hleft
    · simpa only [hword] using hright
    · exact (congrFun (congrFun (congrFun (congrFun htable first) second) left)
        right).trans hfalse

/-- Equality of the fixed finite profile preserves the complete source
Menu-B state.  The boundary word carries the majority/singleton data and the
uniform table carries exactly the component-separation test. -/
theorem annularFrontierMenuBState_iff_of_uniformProfile_eq
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (leftColoring rightColoring : G.EdgeColoring Color)
    (hprofile : annularFrontierMenuUniformProfile data hdata leftColoring =
      annularFrontierMenuUniformProfile data hdata rightColoring) :
    AnnularFrontierMenuBState data leftColoring ↔
      AnnularFrontierMenuBState data rightColoring := by
  have hword : data.innerBoundaryWord leftColoring =
      data.innerBoundaryWord rightColoring :=
    congrArg AnnularFrontierMenuUniformProfile.word hprofile
  have htable : annularFrontierMenuConnectionTable data hdata leftColoring =
      annularFrontierMenuConnectionTable data hdata rightColoring :=
    congrArg AnnularFrontierMenuUniformProfile.connectionTable hprofile
  constructor
  · rintro ⟨majority, singletonFirst, singletonSecond, htriple, hmenu⟩
    have htripleRight : AnnularFrontierMajorityTriple
        (data.innerBoundaryWord rightColoring)
        majority singletonFirst singletonSecond := by
      rw [← hword]
      exact htriple
    refine ⟨majority, singletonFirst, singletonSecond, htripleRight, ?_⟩
    rcases hmenu with hfirst | hsecond
    · exact Or.inl
        ((annularFrontierMenuBForPair_iff_of_word_eq_of_connectionTable_eq
          data hdata leftColoring rightColoring hword htable
          majority singletonFirst).mp hfirst)
    · exact Or.inr
        ((annularFrontierMenuBForPair_iff_of_word_eq_of_connectionTable_eq
          data hdata leftColoring rightColoring hword htable
          majority singletonSecond).mp hsecond)
  · rintro ⟨majority, singletonFirst, singletonSecond, htriple, hmenu⟩
    have htripleLeft : AnnularFrontierMajorityTriple
        (data.innerBoundaryWord leftColoring)
        majority singletonFirst singletonSecond := by
      rw [hword]
      exact htriple
    refine ⟨majority, singletonFirst, singletonSecond, htripleLeft, ?_⟩
    rcases hmenu with hfirst | hsecond
    · exact Or.inl
        ((annularFrontierMenuBForPair_iff_of_word_eq_of_connectionTable_eq
          data hdata leftColoring rightColoring hword htable
          majority singletonFirst).mpr hfirst)
    · exact Or.inr
        ((annularFrontierMenuBForPair_iff_of_word_eq_of_connectionTable_eq
          data hdata leftColoring rightColoring hword htable
          majority singletonSecond).mpr hsecond)

end

end GoertzelV24AnnularFrontierMenu

end Mettapedia.GraphTheory.FourColor
