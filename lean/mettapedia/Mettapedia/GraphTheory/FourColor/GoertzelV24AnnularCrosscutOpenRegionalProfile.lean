import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutSlitRotation
import Mettapedia.GraphTheory.FourColor.GoertzelV24GraphDerivedCorridorOpenProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationVertexCutProfile

/-!
# Full profiles from literal cut-open regional colorings

An open transversal replaces each crossed edge by two degree-one stubs.  A
Tait coloring of that literal slit can therefore be read on either vertex-side
region: for every regional ambient edge, choose its incident dart on that
side and read the color of the corresponding slit edge.

Together with `GraphCorridorCutData.regionalProfile`, this supplies all five
coordinates of the finite corridor profile from a genuine open Tait coloring.
The construction remains parameterized by the selected side, so it is usable
for the concrete component separated by the paired source crosscuts.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscutOpenRegionalProfile

open GoertzelV24AnnularCrosscutSlitRotation
open GoertzelV24CorridorProfile
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24RotationSpliceConstructor
open GoertzelV24RotationVertexCutProfile

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- A regional ambient edge has a dart based at a vertex of the chosen side.
This is the orientation from which its color is read in a cut-open map. -/
theorem exists_vertexSideDart
    (RS : RotationSystem V E) (inside : Finset V) {edge : E}
    (hedge : edge ∈ vertexSetRegionEdges RS inside) :
    ∃ dart : RS.D,
      RS.edgeOf dart = edge ∧ RS.vertOf dart ∈ inside := by
  rw [mem_vertexSetRegionEdges_iff RS] at hedge
  rcases hedge with ⟨vertex, hvertexEndpoint, hvertexInside⟩
  rcases (RS.mem_endpoints_iff).1 hvertexEndpoint with
    ⟨dart, hdartEdge, hdartVertex⟩
  refine ⟨dart, (RS.mem_dartsOn).1 hdartEdge, ?_⟩
  rw [hdartVertex]
  exact hvertexInside

/-- A fixed representative dart at the selected endpoint of a regional edge.
For a cut edge this picks the corresponding boundary side; for an uncut edge
the two old darts still represent the same slit edge. -/
noncomputable def vertexSideDart
    (RS : RotationSystem V E) (inside : Finset V) (edge : E)
    (hedge : edge ∈ vertexSetRegionEdges RS inside) : RS.D :=
  Classical.choose (exists_vertexSideDart RS inside hedge)

@[simp]
theorem vertexSideDart_edgeOf
    (RS : RotationSystem V E) (inside : Finset V) (edge : E)
    (hedge : edge ∈ vertexSetRegionEdges RS inside) :
    RS.edgeOf (vertexSideDart RS inside edge hedge) = edge :=
  (Classical.choose_spec (exists_vertexSideDart RS inside hedge)).1

@[simp]
theorem vertexSideDart_mem_inside
    (RS : RotationSystem V E) (inside : Finset V) (edge : E)
    (hedge : edge ∈ vertexSetRegionEdges RS inside) :
    RS.vertOf (vertexSideDart RS inside edge hedge) ∈ inside :=
  (Classical.choose_spec (exists_vertexSideDart RS inside hedge)).2

/-- Read a color on the chosen component side from a coloring of the literal
slit rotation system.  Values outside the selected region are deliberately
zero: every profile coordinate below is guarded by `regionEdges`, so no
extraneous closed-graph coloring is smuggled into the open semantics. -/
noncomputable def slitColorOnVertexSide
    (RS : RotationSystem V E) (cut : Finset E) (inside : Finset V)
    (coloring : (slitRotationSystem RS cut).EdgeColoring Color) : E → Color :=
  fun edge =>
    if hedge : edge ∈ vertexSetRegionEdges RS inside then
      coloring ((slitRotationSystem RS cut).edgeOf
        (Sum.inl (vertexSideDart RS inside edge hedge)))
    else 0

/-- Every regional color read from an open Tait coloring is nonzero.  Boundary
stubs are genuine edges of the slit map, so this does not require the old
closed graph to be colored. -/
theorem slitColorOnVertexSide_ne_zero
    (RS : RotationSystem V E) (cut : Finset E) (inside : Finset V)
    (coloring : (slitRotationSystem RS cut).EdgeColoring Color)
    (hcoloring : (slitRotationSystem RS cut).IsTaitEdgeColoring coloring)
    {edge : E} (hedge : edge ∈ vertexSetRegionEdges RS inside) :
    slitColorOnVertexSide RS cut inside coloring edge ≠ 0 := by
  rw [slitColorOnVertexSide]
  simp only [dif_pos hedge]
  exact hcoloring _

/-- The full finite profile of one open, cut-open regional piece.  The port
and region hypotheses are structural facts of the actual source crosscut;
they ensure that the nonzero colors required by the boundary alphabet are
read from literal slit edges. -/
noncomputable def slitRegionalProfile
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (data : GraphCorridorCutData RS crossingEdgeCount terminalCount
      faceFragmentCount)
    (cut : Finset E) (inside : Finset V)
    (hregion : data.regionEdges ⊆ vertexSetRegionEdges RS inside)
    (hports : data.PortsInRegion)
    (coloring : (slitRotationSystem RS cut).EdgeColoring Color)
    (hcoloring : (slitRotationSystem RS cut).IsTaitEdgeColoring coloring) :
    CorridorCutProfile crossingEdgeCount terminalCount faceFragmentCount :=
  data.regionalProfile (slitColorOnVertexSide RS cut inside coloring)
    (fun crossing => slitColorOnVertexSide_ne_zero RS cut inside coloring
      hcoloring (hregion (hports (.inl crossing))))

/-- The boundary-color coordinate of a slit-derived profile is exactly the
color read from the selected side of the literal open map. -/
@[simp]
theorem slitRegionalProfile_edgeColor_toColor
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (data : GraphCorridorCutData RS crossingEdgeCount terminalCount
      faceFragmentCount)
    (cut : Finset E) (inside : Finset V)
    (hregion : data.regionEdges ⊆ vertexSetRegionEdges RS inside)
    (hports : data.PortsInRegion)
    (coloring : (slitRotationSystem RS cut).EdgeColoring Color)
    (hcoloring : (slitRotationSystem RS cut).IsTaitEdgeColoring coloring)
    (crossing : Fin crossingEdgeCount) :
    ((slitRegionalProfile data cut inside hregion hports coloring hcoloring).edgeColor
      crossing).toColor =
      slitColorOnVertexSide RS cut inside coloring (data.crossingEdge crossing) :=
  data.regionalProfile_edgeColor_toColor
    (slitColorOnVertexSide RS cut inside coloring)
    (fun index => slitColorOnVertexSide_ne_zero RS cut inside coloring
      hcoloring (hregion (hports (.inl index)))) crossing

/-- The connectivity coordinate of a slit-derived profile is computed solely
from the selected component's regional edges and their slit colors. -/
theorem slitRegionalProfile_strandConnected_eq_true_iff
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (data : GraphCorridorCutData RS crossingEdgeCount terminalCount
      faceFragmentCount)
    (cut : Finset E) (inside : Finset V)
    (hregion : data.regionEdges ⊆ vertexSetRegionEdges RS inside)
    (hports : data.PortsInRegion)
    (coloring : (slitRotationSystem RS cut).EdgeColoring Color)
    (hcoloring : (slitRotationSystem RS cut).IsTaitEdgeColoring coloring)
    (pair : TrackedColorPair)
    (left right : CorridorPort crossingEdgeCount terminalCount) :
    (slitRegionalProfile data cut inside hregion hports coloring hcoloring).strandConnected
        pair left right = true ↔
      data.portEdge left ∈ data.regionEdges ∧
      data.portEdge right ∈ data.regionEdges ∧
      IsTrackedColor (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2
          (slitColorOnVertexSide RS cut inside coloring (data.portEdge left)) ∧
      IsTrackedColor (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2
          (slitColorOnVertexSide RS cut inside coloring (data.portEdge right)) ∧
      (regionalTrackedEdgeGraph RS data.regionEdges
        (slitColorOnVertexSide RS cut inside coloring)
        (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2).Reachable
          (data.portEdge left) (data.portEdge right) :=
  data.regionalProfile_strandConnected_eq_true_iff
    (slitColorOnVertexSide RS cut inside coloring)
    (fun index => slitColorOnVertexSide_ne_zero RS cut inside coloring
      hcoloring (hregion (hports (.inl index)))) pair left right

end

end GoertzelV24AnnularCrosscutOpenRegionalProfile

end Mettapedia.GraphTheory.FourColor
