import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebTotalClosure
import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularFrontierCapComposedProfileSemantics

/-!
# A totally closed five-port web satisfies the cap-composed Menu-B test

The refutation of the universal Good-Word Closed-web Obstruction does not
revive an adversarial terminal.  At five outer stubs, Cubic Closure makes
every bichromatic component inner-touching, and the exact endpoint census
then says that no component contains two distinct inner stubs.  Consequently
the open strand relation on the five cap positions is diagonal.  Restoring the
pentagonal cap leaves its two active blocks distinct, which is exactly the
cap-composed Menu-B predicate.

This module proves that argument on the literal graph/profile carriers.  It
uses neither the refuted GWCO statement nor an abstract replacement relation.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebCapComposedMenu

open SimpleGraph
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebRadialComponents
open GoertzelV24ClosedWebInnerTouching
open GoertzelV24ClosedWebComponentCensus
open GoertzelV24ClosedWebTotalClosure
open GoertzelV24AnnularFrontierMenu
open GoertzelV24AnnularFrontierMenuCapMatching
open GoertzelV24AnnularFrontierMenuCapComposed
open GoertzelV24AnnularFrontierMenuCapRestoration
open GoertzelV24AnnularFrontierCapComposedProfileSemantics

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- At the five-port boundary, the profile strand relation of an
inner-touching Tait colouring can only relate a position to itself. -/
theorem eq_of_profileStrand_of_innerTouching_at_five
    (data : AnnularBoundaryData G 5) (hdata : data.WellFormed)
    (coloring : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G coloring)
    (hinnerTouching : EveryColorPairComponentInnerTouching data coloring)
    {first second : Color} (hpair : ValidColorPair first second)
    {left right : Fin 5}
    (hstrand : ProfileStrand
      (annularFrontierMenuUniformProfile data hdata coloring)
        first second left right) :
    left = right := by
  have htable :
      annularFrontierMenuConnectionTable data hdata coloring
        first second left right = true := by
    simpa [ProfileStrand, annularFrontierMenuUniformProfile] using hstrand
  rcases (annularFrontierMenuConnectionTable_eq_true_iff
      data hdata coloring first second left right).mp htable with
    ⟨hleft, hright, hcomponents⟩
  let leftPort : AnnularFrontierActivePairPort data coloring first second :=
    ⟨left, hleft⟩
  let rightPort : AnnularFrontierActivePairPort data coloring first second :=
    ⟨right, hright⟩
  let component :=
    annularFrontierActivePairPortComponent
      data hdata coloring first second leftPort
  have hleftContains :
      ComponentContainsInnerStub data coloring first second component left := by
    exact annularFrontierActivePairPortComponent_contains
      data hdata coloring first second leftPort
  have hrightContains :
      ComponentContainsInnerStub data coloring first second component right := by
    have hrightCanonical :=
      annularFrontierActivePairPortComponent_contains
        data hdata coloring first second rightPort
    change ComponentContainsInnerStub data coloring first second component right
    rw [show component =
        annularFrontierActivePairPortComponent
          data hdata coloring first second rightPort by
      exact hcomponents]
    exact hrightCanonical
  exact
    (noColorPairComponentHasTwoDistinctInnerStubs_at_five
      data hdata coloring htait hinnerTouching)
      first second hpair component left right hleftContains hrightContains

/-- The graph-derived open strand relation has no transverse chord once every
bichromatic component is inner-touching. -/
theorem no_transverseChord_of_innerTouching_at_five
    (data : AnnularBoundaryData G 5) (hdata : data.WellFormed)
    (coloring : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G coloring)
    (hinnerTouching : EveryColorPairComponentInnerTouching data coloring)
    {first second : Color} (hpair : ValidColorPair first second)
    (inactive : Fin 5) :
    ¬ TransverseChord
      (ProfileStrand
        (annularFrontierMenuUniformProfile data hdata coloring) first second)
      inactive := by
  rintro ⟨left, right, -, -, hstrand, hcross⟩
  have heq : left = right :=
    eq_of_profileStrand_of_innerTouching_at_five
      data hdata coloring htait hinnerTouching hpair hstrand
  subst right
  exact hcross Iff.rfl

/-- For either majority pair, total radiality of the open web implies Menu B
after the literal pentagonal cap is restored. -/
theorem restoredMenuBForPair_of_innerTouching_at_five
    (data : AnnularBoundaryData G 5) (hdata : data.WellFormed)
    (coloring : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G coloring)
    (hinnerTouching : EveryColorPairComponentInnerTouching data coloring)
    {first second : Color} (hpair : ValidColorPair first second)
    {inactive : Fin 5}
    (hinactive : InactivePosition
      (data.innerBoundaryWord coloring) first second inactive) :
    RestoredMenuBForPair data hdata coloring first second := by
  refine ⟨inactive, hinactive, ?_⟩
  apply (restoredMenuB_iff_no_transverseChord
    (fun _ _ hstrand => profileStrand_active_of_uniformProfile
      data hdata coloring first second hinactive hstrand)).mpr
  exact no_transverseChord_of_innerTouching_at_five
    data hdata coloring htait hinnerTouching hpair inactive

/-- **Surviving closed-web lemma.**  In a connected annular tangle with five
inner and five outer stubs, a totally closed Tait colouring at a good inner
word is Menu B for both majority/singleton pairs after cap restoration. -/
theorem both_restoredMenuBForPair_of_totallyClosed_at_five
    (data : AnnularBoundaryData G 5) (hdata : data.WellFormed)
    (hconnected : G.Connected)
    (coloring : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G coloring)
    (hclosed : TotallyClosedWeb data coloring)
    (hgood : CAP5BoundaryWordHasColoredBlock311
      (data.innerBoundaryWord coloring)) :
    ∃ majority singletonFirst singletonSecond : Color,
      AnnularFrontierMajorityTriple (data.innerBoundaryWord coloring)
        majority singletonFirst singletonSecond ∧
      RestoredMenuBForPair data hdata coloring majority singletonFirst ∧
      RestoredMenuBForPair data hdata coloring majority singletonSecond := by
  rcases exists_annularFrontierMajorityTriple_of_goodWord hgood with
    ⟨majority, singletonFirst, singletonSecond, htriple⟩
  let hinnerTouching : EveryColorPairComponentInnerTouching data coloring :=
    everyColorPairComponentInnerTouching_of_totallyClosed
      data hdata hconnected coloring htait hclosed
  rcases AnnularFrontierMajorityTriple.exists_inactive_first htriple with
    ⟨firstInactive, hfirstInactive⟩
  rcases AnnularFrontierMajorityTriple.exists_inactive_second htriple with
    ⟨secondInactive, hsecondInactive⟩
  have hfirstPair : ValidColorPair majority singletonFirst :=
    ⟨htriple.1.1, htriple.1.2.1, htriple.1.2.2.2.1⟩
  have hsecondPair : ValidColorPair majority singletonSecond :=
    ⟨htriple.1.1, htriple.1.2.2.1, htriple.1.2.2.2.2.1⟩
  refine ⟨majority, singletonFirst, singletonSecond, htriple, ?_, ?_⟩
  · exact restoredMenuBForPair_of_innerTouching_at_five
      data hdata coloring htait hinnerTouching hfirstPair hfirstInactive
  · exact restoredMenuBForPair_of_innerTouching_at_five
      data hdata coloring htait hinnerTouching hsecondPair hsecondInactive

/-- The previous theorem implies the corrected Seed terminal predicate, which
only asks for one of the two majority pairs. -/
theorem restoredMenuBState_of_totallyClosed_at_five
    (data : AnnularBoundaryData G 5) (hdata : data.WellFormed)
    (hconnected : G.Connected)
    (coloring : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G coloring)
    (hclosed : TotallyClosedWeb data coloring)
    (hgood : CAP5BoundaryWordHasColoredBlock311
      (data.innerBoundaryWord coloring)) :
    RestoredMenuBState data hdata coloring := by
  rcases both_restoredMenuBForPair_of_totallyClosed_at_five
      data hdata hconnected coloring htait hclosed hgood with
    ⟨majority, singletonFirst, singletonSecond, htriple, hfirst, -⟩
  exact ⟨majority, singletonFirst, singletonSecond, htriple, Or.inl hfirst⟩

end

end GoertzelV24ClosedWebCapComposedMenu

end Mettapedia.GraphTheory.FourColor
