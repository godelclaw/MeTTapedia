import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularFrontierMenuUniformProfile

/-!
# Menu-B semantics read directly from a finite profile

The `Count` profile in the source is useful only if its acceptance condition
can be read from the profile itself. For the Seed Lemma that condition is
Menu B: a majority/singleton color pair has two cap ports in distinct selected
components. The uniform profile records exactly the boundary word and the
selected-pair component table needed to state that test without referring back
to a graph coloring.

This file proves that profile-level test equivalent to the literal graph
definition on every actual Tait coloring. It therefore does not replace the
connectivity calculation with an interface axiom.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularFrontierMenu

open SimpleGraph
open GoertzelV24ClosedWebBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

/-- The profile-only form of Menu B for one selected color pair. The word
identifies active cap ports, while the Boolean table says whether their two
canonical selected components agree. -/
def AnnularFrontierMenuBForPairOfProfile
    (profile : AnnularFrontierMenuUniformProfile)
    (first second : Color) : Prop :=
  ∃ left right : Fin 5,
    left ∈ cap5ActiveSupport first second profile.word ∧
      right ∈ cap5ActiveSupport first second profile.word ∧
        profile.connectionTable first second left right = false

/-- The source's complete “some majority pair has Menu B” predicate, read
solely from the finite profile carrier. -/
def AnnularFrontierMenuBStateOfProfile
    (profile : AnnularFrontierMenuUniformProfile) : Prop :=
  ∃ majority singletonFirst singletonSecond : Color,
    AnnularFrontierMajorityTriple profile.word
      majority singletonFirst singletonSecond ∧
      (AnnularFrontierMenuBForPairOfProfile profile majority singletonFirst ∨
        AnnularFrontierMenuBForPairOfProfile profile majority singletonSecond)

/-- Addendum VII has the same content when read from the computed uniform
profile as when read from the selected support graph. -/
theorem annularFrontierMenuBForPair_iff_of_uniformProfile
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (coloring : G.EdgeColoring Color) (first second : Color) :
    AnnularFrontierMenuBForPair data coloring first second ↔
      AnnularFrontierMenuBForPairOfProfile
        (annularFrontierMenuUniformProfile data hdata coloring) first second := by
  change AnnularFrontierMenuBForPair data coloring first second ↔
    ∃ left right : Fin 5,
      left ∈ cap5ActiveSupport first second (data.innerBoundaryWord coloring) ∧
        right ∈ cap5ActiveSupport first second (data.innerBoundaryWord coloring) ∧
          annularFrontierMenuConnectionTable data hdata coloring
            first second left right = false
  exact annularFrontierMenuBForPair_iff_exists_active_connectionTable_false
    data hdata coloring first second

/-- The source Menu-B state is exactly a finite profile predicate at every
literal graph coloring. -/
theorem annularFrontierMenuBState_iff_of_uniformProfile
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (coloring : G.EdgeColoring Color) :
    AnnularFrontierMenuBState data coloring ↔
      AnnularFrontierMenuBStateOfProfile
        (annularFrontierMenuUniformProfile data hdata coloring) := by
  change
    (∃ majority singletonFirst singletonSecond : Color,
      AnnularFrontierMajorityTriple (data.innerBoundaryWord coloring)
        majority singletonFirst singletonSecond ∧
        (AnnularFrontierMenuBForPair data coloring majority singletonFirst ∨
          AnnularFrontierMenuBForPair data coloring majority singletonSecond)) ↔
    (∃ majority singletonFirst singletonSecond : Color,
      AnnularFrontierMajorityTriple (data.innerBoundaryWord coloring)
        majority singletonFirst singletonSecond ∧
        ((∃ left right : Fin 5,
          left ∈ cap5ActiveSupport majority singletonFirst
            (data.innerBoundaryWord coloring) ∧
            right ∈ cap5ActiveSupport majority singletonFirst
              (data.innerBoundaryWord coloring) ∧
              annularFrontierMenuConnectionTable data hdata coloring
                majority singletonFirst left right = false) ∨
          ∃ left right : Fin 5,
            left ∈ cap5ActiveSupport majority singletonSecond
              (data.innerBoundaryWord coloring) ∧
              right ∈ cap5ActiveSupport majority singletonSecond
                (data.innerBoundaryWord coloring) ∧
                annularFrontierMenuConnectionTable data hdata coloring
                  majority singletonSecond left right = false))
  constructor
  · rintro ⟨majority, singletonFirst, singletonSecond, htriple,
      hfirst | hsecond⟩
    · exact ⟨majority, singletonFirst, singletonSecond, htriple,
        Or.inl ((annularFrontierMenuBForPair_iff_of_uniformProfile
          data hdata coloring majority singletonFirst).mp hfirst)⟩
    · exact ⟨majority, singletonFirst, singletonSecond, htriple,
        Or.inr ((annularFrontierMenuBForPair_iff_of_uniformProfile
          data hdata coloring majority singletonSecond).mp hsecond)⟩
  · rintro ⟨majority, singletonFirst, singletonSecond, htriple,
      hfirst | hsecond⟩
    · exact ⟨majority, singletonFirst, singletonSecond, htriple,
        Or.inl ((annularFrontierMenuBForPair_iff_of_uniformProfile
          data hdata coloring majority singletonFirst).mpr hfirst)⟩
    · exact ⟨majority, singletonFirst, singletonSecond, htriple,
        Or.inr ((annularFrontierMenuBForPair_iff_of_uniformProfile
          data hdata coloring majority singletonSecond).mpr hsecond)⟩

/-- Profile equality preserves the source Menu-B state because the predicate
is now visibly a function of the profile. -/
theorem annularFrontierMenuBState_iff_of_uniformProfile_eq'
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (leftColoring rightColoring : G.EdgeColoring Color)
    (hprofile : annularFrontierMenuUniformProfile data hdata leftColoring =
      annularFrontierMenuUniformProfile data hdata rightColoring) :
    AnnularFrontierMenuBState data leftColoring ↔
      AnnularFrontierMenuBState data rightColoring := by
  rw [annularFrontierMenuBState_iff_of_uniformProfile data hdata leftColoring,
    annularFrontierMenuBState_iff_of_uniformProfile data hdata rightColoring,
    hprofile]

end

end GoertzelV24AnnularFrontierMenu

end Mettapedia.GraphTheory.FourColor
