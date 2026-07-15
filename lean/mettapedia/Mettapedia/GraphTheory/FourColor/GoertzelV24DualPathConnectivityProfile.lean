import Mettapedia.GraphTheory.FourColor.GoertzelV24DualPathTransversal
import Mettapedia.GraphTheory.FourColor.GoertzelV24GraphDerivedCorridorCutProfile

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24DualPathConnectivityProfile

open GoertzelV24CorridorProfile
open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24WindingClassification
open SimpleGraph
open SimpleGraphDartRotation

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Raw corridor-cut data whose ordered crossing ports are computed from a
facial-dual walk. The regional edge set is explicit; terminals and face
fragments are deliberately absent from this connectivity-only profile. -/
def dualPathCutData (RS : RotationSystem V E) (region : Finset E)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    (walk : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Walk start finish) :
    GraphCorridorCutData RS walk.length 0 0 where
  regionEdges := region
  crossingEdge := dualWalkCrossingEdge (orbitFaceBoundary RS)
    (Finset.univ : Finset (OrbitFace RS)) hunique walk
  terminalEdge := Fin.elim0
  fragmentFace := Fin.elim0
  fragmentEdges := Fin.elim0

@[simp]
theorem dualPathCutData_crossingEdge
    (RS : RotationSystem V E) (region : Finset E)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    (walk : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Walk start finish)
    (step : Fin walk.length) :
    (dualPathCutData RS region hunique walk).crossingEdge step =
      dualWalkCrossingEdge (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) hunique walk step :=
  rfl

/-- If the chosen region contains the computed crossing set, every cut port
is genuinely present in that region. -/
theorem dualPathCutData_portsInRegion
    (RS : RotationSystem V E) (region : Finset E)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    (walk : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Walk start finish)
    (hcrossing : dualWalkCrossingEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) hunique walk ⊆ region) :
    (dualPathCutData RS region hunique walk).PortsInRegion := by
  intro port
  rcases port with step | terminal
  · apply hcrossing
    exact (mem_dualWalkCrossingEdges_iff
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) hunique walk _).2 ⟨step, rfl⟩
  · exact Fin.elim0 terminal

/-- A simple facial-dual path gives injective ordered cut ports. This is
derived from face incidence and path simplicity, not stored in the cut data. -/
theorem dualPathCutData_portsInjective_of_isPath
    (RS : RotationSystem V E) (region : Finset E)
    (hall : ∀ edge,
      totalIncidenceCount (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) edge ≤ 2)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    (walk : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Walk start finish)
    (hpath : walk.IsPath) :
    (dualPathCutData RS region hunique walk).PortsInjective := by
  intro left right hedges
  rcases left with left | left <;> rcases right with right | right
  · have hedgeEq :
        dualWalkCrossingEdge (orbitFaceBoundary RS)
            (Finset.univ : Finset (OrbitFace RS)) hunique walk left =
          dualWalkCrossingEdge (orbitFaceBoundary RS)
            (Finset.univ : Finset (OrbitFace RS)) hunique walk right := hedges
    have hstepEq : left = right :=
      dualWalkCrossingEdge_injective_of_isPath
        (orbitFaceBoundary RS) (Finset.univ : Finset (OrbitFace RS))
        hall hunique walk hpath hedgeEq
    exact congrArg Sum.inl hstepEq
  · exact Fin.elim0 right
  · exact Fin.elim0 left
  · exact Fin.elim0 left

/-- The finite connectivity profile on the ordered dual-path crossings,
computed from an actual regional tracked-edge graph and Tait coloring. -/
def dualPathCutProfile (RS : RotationSystem V E) (region : Finset E)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    (walk : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Walk start finish)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C) :
    CorridorCutProfile walk.length 0 0 :=
  (dualPathCutData RS region hunique walk).profile C hC

@[simp]
theorem dualPathCutProfile_edgeColor_toColor
    (RS : RotationSystem V E) (region : Finset E)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    (walk : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Walk start finish)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (step : Fin walk.length) :
    ((dualPathCutProfile RS region hunique walk C hC).edgeColor step).toColor =
      C (dualWalkCrossingEdge (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) hunique walk step) := by
  exact GraphCorridorCutData.profile_edgeColor_toColor
    (dualPathCutData RS region hunique walk) C hC step

/-- The dual-path matrix entry is exactly regional two-color reachability
between the corresponding computed primal crossing edges. -/
theorem dualPathCutProfile_strandConnected_eq_true_iff
    (RS : RotationSystem V E) (region : Finset E)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    (walk : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Walk start finish)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (pair : TrackedColorPair) (left right : Fin walk.length) :
    (dualPathCutProfile RS region hunique walk C hC).strandConnected pair
        (.inl left) (.inl right) = true ↔
      let colors := trackedColorPairColors pair
      let leftEdge := dualWalkCrossingEdge (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) hunique walk left
      let rightEdge := dualWalkCrossingEdge (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) hunique walk right
      leftEdge ∈ region ∧ rightEdge ∈ region ∧
      IsTrackedColor colors.1 colors.2 (C leftEdge) ∧
      IsTrackedColor colors.1 colors.2 (C rightEdge) ∧
      (regionalTrackedEdgeGraph RS region C colors.1 colors.2).Reachable
        leftEdge rightEdge := by
  exact GraphCorridorCutData.profile_strandConnected_eq_true_iff
    (dualPathCutData RS region hunique walk) C hC pair (.inl left) (.inl right)

/-- On a region containing all crossings, the diagonal of the dual-path
matrix is exactly the active support of the selected color pair. -/
theorem dualPathCutProfile_strandConnected_self_eq_true_iff
    (RS : RotationSystem V E) (region : Finset E)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    (walk : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Walk start finish)
    (hcrossing : dualWalkCrossingEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) hunique walk ⊆ region)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (pair : TrackedColorPair) (step : Fin walk.length) :
    (dualPathCutProfile RS region hunique walk C hC).strandConnected pair
        (.inl step) (.inl step) = true ↔
      IsTrackedColor (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2
        (C (dualWalkCrossingEdge (orbitFaceBoundary RS)
          (Finset.univ : Finset (OrbitFace RS)) hunique walk step)) := by
  exact GraphCorridorCutData.profile_strandConnected_self_eq_true_iff
    (dualPathCutData RS region hunique walk)
    (dualPathCutData_portsInRegion RS region hunique walk hcrossing)
    C hC pair (.inl step)

/-- The computed dual-path connectivity matrix is symmetric. -/
theorem dualPathCutProfile_strandConnected_comm
    (RS : RotationSystem V E) (region : Finset E)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    (walk : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Walk start finish)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (pair : TrackedColorPair) (left right : Fin walk.length) :
    (dualPathCutProfile RS region hunique walk C hC).strandConnected pair
        (.inl left) (.inl right) =
      (dualPathCutProfile RS region hunique walk C hC).strandConnected pair
        (.inl right) (.inl left) := by
  exact regionalTrackedConnectivity_comm RS region C pair _ _

/-- The computed dual-path connectivity matrix is transitive on its active
support, hence records whole regional components rather than an assumed
two-endpoint pairing. -/
theorem dualPathCutProfile_strandConnected_trans
    (RS : RotationSystem V E) (region : Finset E)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    (walk : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Walk start finish)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (pair : TrackedColorPair) (left middle right : Fin walk.length)
    (hleftMiddle :
      (dualPathCutProfile RS region hunique walk C hC).strandConnected pair
        (.inl left) (.inl middle) = true)
    (hmiddleRight :
      (dualPathCutProfile RS region hunique walk C hC).strandConnected pair
        (.inl middle) (.inl right) = true) :
    (dualPathCutProfile RS region hunique walk C hC).strandConnected pair
        (.inl left) (.inl right) = true := by
  exact regionalTrackedConnectivity_trans RS region C pair _ _ _
    hleftMiddle hmiddleRight

/-- Equal-colored crossings of a simple dual path have disjoint endpoint
sets. Thus each color class visible on the transversal is a genuine primal
matching, derived from proper edge coloring and port injectivity. -/
theorem dualWalkCrossingEdges_endpoints_disjoint_of_sameColor
    (RS : RotationSystem V E)
    (hall : ∀ edge,
      totalIncidenceCount (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) edge ≤ 2)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    (walk : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Walk start finish)
    (hpath : walk.IsPath) (C : RS.EdgeColoring Color)
    {left right : Fin walk.length} (hne : left ≠ right)
    (hcolor :
      C (dualWalkCrossingEdge (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) hunique walk left) =
      C (dualWalkCrossingEdge (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) hunique walk right)) :
    Disjoint
      (RS.endpoints (dualWalkCrossingEdge (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) hunique walk left))
      (RS.endpoints (dualWalkCrossingEdge (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) hunique walk right)) := by
  rw [Finset.disjoint_left]
  intro vertex hleft hright
  let leftEdge := dualWalkCrossingEdge (orbitFaceBoundary RS)
    (Finset.univ : Finset (OrbitFace RS)) hunique walk left
  let rightEdge := dualWalkCrossingEdge (orbitFaceBoundary RS)
    (Finset.univ : Finset (OrbitFace RS)) hunique walk right
  have hedgeNe : leftEdge ≠ rightEdge :=
    (dualWalkCrossingEdge_injective_of_isPath
      (orbitFaceBoundary RS) (Finset.univ : Finset (OrbitFace RS))
      hall hunique walk hpath).ne hne
  have hadj : RS.edgeAdjacencyGraph.Adj leftEdge rightEdge :=
    (RS.edgeAdjacencyGraph_adj_iff).2
      ⟨hedgeNe, vertex, hleft, hright⟩
  exact C.valid hadj hcolor

end

end GoertzelV24DualPathConnectivityProfile

end Mettapedia.GraphTheory.FourColor
