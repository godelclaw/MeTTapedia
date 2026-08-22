import Mettapedia.GraphTheory.FourColor.GoertzelV24GraphDerivedCorridorOpenProfile

/-!
# Regional corridor profiles depend only on regional colors

The cut profile observes colors only on its stored finite edge region.  If two
color functions agree there, and every named port belongs to that region, then
their complete five-coordinate regional profiles agree.  In particular, this
transports not only boundary colors but the three tracked connectivity
relations; the facial coordinates are independent of the coloring by
definition.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24GraphDerivedCorridorCutProfile

open GoertzelV24CorridorProfile
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24HexCorridorFiniteColorTransition
open GoertzelV24WindingClassification
open SimpleGraphDartRotation

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- A complete regional profile is unchanged when the coloring is unchanged
on the region it observes. -/
theorem GraphCorridorCutData.regionalProfile_eq_of_eq_on_region
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (data : GraphCorridorCutData RS crossingEdgeCount terminalCount
      faceFragmentCount)
    (hports : data.PortsInRegion)
    (left right : E → Color)
    (hleft : ∀ crossing, left (data.crossingEdge crossing) ≠ 0)
    (hright : ∀ crossing, right (data.crossingEdge crossing) ≠ 0)
    (heq : ∀ edge ∈ data.regionEdges, left edge = right edge) :
    data.regionalProfile left hleft = data.regionalProfile right hright := by
  unfold GraphCorridorCutData.regionalProfile
  congr 1
  · funext crossing
    apply StrandColor.toColor_injective
    simp only [strandColorOfNonzero_toColor]
    exact heq _ (hports (.inl crossing))
  · funext pair port₁ port₂
    have hport₁ := hports port₁
    have hport₂ := hports port₂
    have hgraph : regionalTrackedEdgeGraph RS data.regionEdges left
        (trackedColorPairColors pair).1 (trackedColorPairColors pair).2 =
      regionalTrackedEdgeGraph RS data.regionEdges right
        (trackedColorPairColors pair).1 (trackedColorPairColors pair).2 := by
      ext first second
      simp only [regionalTrackedEdgeGraph, RotationSystem.trackedEdgeGraph]
      constructor
      · rintro ⟨⟨hadj, hfirstTracked, hsecondTracked⟩, hfirst, hsecond⟩
        exact ⟨⟨hadj, heq first hfirst ▸ hfirstTracked,
          heq second hsecond ▸ hsecondTracked⟩, hfirst, hsecond⟩
      · rintro ⟨⟨hadj, hfirstTracked, hsecondTracked⟩, hfirst, hsecond⟩
        exact ⟨⟨hadj, (heq first hfirst).symm ▸ hfirstTracked,
          (heq second hsecond).symm ▸ hsecondTracked⟩, hfirst, hsecond⟩
    apply Bool.eq_iff_iff.mpr
    rw [regionalTrackedConnectivity_eq_true_iff,
      regionalTrackedConnectivity_eq_true_iff]
    rw [hgraph, heq _ hport₁, heq _ hport₂]

end

end GoertzelV24GraphDerivedCorridorCutProfile

end Mettapedia.GraphTheory.FourColor
