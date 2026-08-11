import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationBoundaryFaceCutProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24TerminalProfileRegionalCoverage
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Boundary coverage of vertex-side face fragments

For a face incident to a finite vertex cut, every connected fragment of the
face retained on either vertex side contains an actual crossing edge.  Thus
the raw connected fragments used by the relational face-update law are honest
coordinates of the boundary-local profile whenever their face meets the cut.

The proof is combinatorial.  The linear path through the cyclic face
positions is connected.  If a fragment does not already contain a selected
cut occurrence, a first edge leaving the fragment is adjacent on the face to
an edge outside the regional edge set.  Its retained predecessor must then be
a crossing edge: otherwise both predecessor endpoints lie on the retained
side, forcing the successor edge to meet that side as well.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24VertexSideBoundaryFragmentCoverage

open GoertzelV24HexFaceRungType
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationAllFaceCutProfile
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationFaceFragments
open GoertzelV24RotationVertexCutProfile
open GoertzelV24TerminalProfileRegionalCoverage
open SimpleGraph
open SimpleGraphDartRotation

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- The ordinary linear path on the bounded powers of a face permutation is
a subgraph of the actual cyclic face-position graph.  The wraparound edge is
not needed for connectedness. -/
theorem pathGraph_le_faceCyclePositionGraph
    (RS : RotationSystem V E) (root : RS.D) :
    pathGraph (RS.faceOrbit root).card ≤ faceCyclePositionGraph RS root := by
  intro left right hadj
  rw [pathGraph_adj] at hadj
  rcases hadj with hforward | hbackward
  · refine ⟨?_, Or.inl ?_⟩
    · intro heq
      have hval := congrArg Fin.val heq
      omega
    · simp only [faceCycleDart]
      rw [← hforward]
      simp only [pow_succ', Equiv.Perm.coe_mul, Function.comp_apply]
  · refine ⟨?_, Or.inr ?_⟩
    · intro heq
      have hval := congrArg Fin.val heq
      omega
    · simp only [faceCycleDart]
      rw [← hbackward]
      simp only [pow_succ', Equiv.Perm.coe_mul, Function.comp_apply]

/-- The graph of cyclic positions on one actual face is preconnected. -/
theorem faceCyclePositionGraph_preconnected
    (RS : RotationSystem V E) (root : RS.D) :
    (faceCyclePositionGraph RS root).Preconnected :=
  (pathGraph_preconnected (RS.faceOrbit root).card).mono
    (pathGraph_le_faceCyclePositionGraph RS root)

/-- Every fragment of a cut-incident face on a vertex-induced regional side
contains a genuine crossing edge. -/
theorem faceRegionalFragment_touches_vertexSetCrossingEdges
    (RS : RotationSystem V E)
    (hcubic : RS.IsCubic) (hrotation : VertexRotationCyclic RS)
    (htwoSided : OrbitFacesTwoSided RS) (inside : Finset V)
    (face : CutIncidentFace RS (vertexSetCrossingEdges RS inside))
    (fragment : FaceRegionalFragment RS (orbitFaceRoot RS face.1)
      (vertexSetRegionEdges RS inside)) :
    FaceFragmentTouchesCut RS (vertexSetCrossingEdges RS inside)
      (vertexSetRegionEdges RS inside) face fragment := by
  let root := orbitFaceRoot RS face.1
  rcases (mem_cutIncidentFaces_iff RS
    (vertexSetCrossingEdges RS inside) face.1).1 face.2 with
    ⟨cutEdge, hcutEdge, hcutFace⟩
  have hcutFaceRoot :
      cutEdge ∈ orbitFaceBoundary RS (dartOrbitFace RS root) := by
    simpa [root] using hcutFace
  rcases existsUnique_faceCycleEdge_eq RS htwoSided root cutEdge
      hcutFaceRoot with ⟨targetPosition, htargetEdge, _htargetUnique⟩
  have htargetRegionEdge :
      faceCycleEdge RS root targetPosition ∈ vertexSetRegionEdges RS inside := by
    rw [htargetEdge]
    exact vertexSetCrossingEdges_subset_regionEdges RS inside hcutEdge
  let target : FaceRegionalPosition RS root
      (vertexSetRegionEdges RS inside) :=
    ⟨targetPosition,
      (mem_faceRegionalPositions_iff RS root
        (vertexSetRegionEdges RS inside) targetPosition).2 htargetRegionEdge⟩
  by_cases htargetFragment : target ∈ fragment.supp
  · refine ⟨cutEdge, ?_, hcutEdge⟩
    apply (mem_faceRegionalFragmentEdges_iff RS root
      (vertexSetRegionEdges RS inside) fragment cutEdge).2
    refine ⟨targetPosition, ?_, htargetEdge⟩
    apply (mem_faceRegionalFragmentPositions_iff RS root
      (vertexSetRegionEdges RS inside) fragment targetPosition).2
    exact ⟨target, htargetFragment, rfl⟩
  · rcases ConnectedComponent.nonempty_supp fragment with
      ⟨start, hstartFragment⟩
    have hstartPosition : start.1 ∈
        faceRegionalFragmentPositions RS root
          (vertexSetRegionEdges RS inside) fragment :=
      (mem_faceRegionalFragmentPositions_iff RS root
        (vertexSetRegionEdges RS inside) fragment start.1).2
        ⟨start, hstartFragment, rfl⟩
    have htargetPosition : targetPosition ∉
        faceRegionalFragmentPositions RS root
          (vertexSetRegionEdges RS inside) fragment := by
      intro htargetPosition
      rcases (mem_faceRegionalFragmentPositions_iff RS root
        (vertexSetRegionEdges RS inside) fragment targetPosition).1
          htargetPosition with ⟨otherTarget, hotherTarget, hotherValue⟩
      have hotherEq : otherTarget = target := Subtype.ext hotherValue
      exact htargetFragment (hotherEq ▸ hotherTarget)
    rcases faceCyclePositionGraph_preconnected RS root start.1 targetPosition
      with ⟨walk⟩
    rcases walk.exists_boundary_dart
      (↑(faceRegionalFragmentPositions RS root
        (vertexSetRegionEdges RS inside) fragment) :
          Set (Fin (RS.faceOrbit root).card))
      hstartPosition htargetPosition with
      ⟨boundaryDart, _hboundaryDartWalk, hleftPosition,
        hrightPosition⟩
    rcases (mem_faceRegionalFragmentPositions_iff RS root
      (vertexSetRegionEdges RS inside) fragment boundaryDart.fst).1
        hleftPosition with ⟨leftRegional, hleftFragment, hleftValue⟩
    have hrightNotRegion :
        faceCycleEdge RS root boundaryDart.snd ∉
          vertexSetRegionEdges RS inside := by
      intro hrightRegion
      let rightRegional : FaceRegionalPosition RS root
          (vertexSetRegionEdges RS inside) :=
        ⟨boundaryDart.snd,
          (mem_faceRegionalPositions_iff RS root
            (vertexSetRegionEdges RS inside) boundaryDart.snd).2
              hrightRegion⟩
      have hadjRegional :
          (faceRegionalPositionGraph RS root
            (vertexSetRegionEdges RS inside)).Adj leftRegional
              rightRegional := by
        change (faceCyclePositionGraph RS root).Adj leftRegional.1
          rightRegional.1
        simpa [hleftValue, rightRegional] using boundaryDart.2
      have hleftComponent :
          (faceRegionalPositionGraph RS root
              (vertexSetRegionEdges RS inside)).connectedComponentMk
              leftRegional = fragment :=
        (ConnectedComponent.mem_supp_iff fragment leftRegional).1
          hleftFragment
      have hrightComponent :
          (faceRegionalPositionGraph RS root
              (vertexSetRegionEdges RS inside)).connectedComponentMk
              rightRegional = fragment :=
        (ConnectedComponent.sound hadjRegional.symm.reachable).trans
          hleftComponent
      have hrightFragment : rightRegional ∈ fragment.supp :=
        (ConnectedComponent.mem_supp_iff fragment rightRegional).2
          hrightComponent
      exact hrightPosition
        ((mem_faceRegionalFragmentPositions_iff RS root
          (vertexSetRegionEdges RS inside) fragment boundaryDart.snd).2
          ⟨rightRegional, hrightFragment, rfl⟩)
    have hleftRegion :
        faceCycleEdge RS root boundaryDart.fst ∈
          vertexSetRegionEdges RS inside := by
      have := leftRegional.2
      rw [mem_faceRegionalPositions_iff] at this
      simpa [hleftValue] using this
    have hleftCrossing :
        faceCycleEdge RS root boundaryDart.fst ∈
          vertexSetCrossingEdges RS inside := by
      by_contra hnotCrossing
      have hleftEndpoints := endpoints_subset_of_mem_region_not_mem_crossing
        RS inside hleftRegion hnotCrossing
      have hedgeAdj := edgeAdjacencyGraph_adj_of_faceCyclePositionGraph_adj
        RS hcubic hrotation root boundaryDart.2
      rcases hedgeAdj.2 with
        ⟨sharedVertex, hsharedLeft, hsharedRight⟩
      exact hrightNotRegion
        ((mem_vertexSetRegionEdges_iff RS inside
          (faceCycleEdge RS root boundaryDart.snd)).2
          ⟨sharedVertex, hsharedRight, hleftEndpoints hsharedLeft⟩)
    refine ⟨faceCycleEdge RS root boundaryDart.fst, ?_, hleftCrossing⟩
    exact (mem_faceRegionalFragmentEdges_iff RS root
      (vertexSetRegionEdges RS inside) fragment
      (faceCycleEdge RS root boundaryDart.fst)).2
      ⟨boundaryDart.fst, hleftPosition, rfl⟩

/-- On a cubic cyclic two-sided rotation system, retaining only fragments
that touch the vertex cut loses no fragment of a cut-incident face.  This is
the typed bridge from the raw factor fragments used by relational composition
to the boundary-indexed fragments stored by the finite profile. -/
noncomputable def cutIncidentFaceRegionalFragmentEquivBoundary
    (RS : RotationSystem V E)
    (hcubic : RS.IsCubic) (hrotation : VertexRotationCyclic RS)
    (htwoSided : OrbitFacesTwoSided RS) (inside : Finset V) :
    (Σ face : CutIncidentFace RS (vertexSetCrossingEdges RS inside),
      FaceRegionalFragment RS (orbitFaceRoot RS face.1)
        (vertexSetRegionEdges RS inside)) ≃
      BoundaryRegionalFragment RS (vertexSetCrossingEdges RS inside)
        (vertexSetRegionEdges RS inside) where
  toFun item :=
    ⟨item.1, ⟨item.2,
      faceRegionalFragment_touches_vertexSetCrossingEdges RS hcubic
        hrotation htwoSided inside item.1 item.2⟩⟩
  invFun item := ⟨item.1, item.2.1⟩
  left_inv item := by
    rcases item with ⟨face, fragment⟩
    rfl
  right_inv item := by
    rcases item with ⟨face, fragment, htouches⟩
    rfl

/-- Every raw fragment of a cut-incident face therefore has a canonical
coordinate in the finite boundary-fragment enumeration. -/
theorem exists_boundaryRegionalFragmentAt_eq_cutIncidentFaceFragment
    (RS : RotationSystem V E)
    (hcubic : RS.IsCubic) (hrotation : VertexRotationCyclic RS)
    (htwoSided : OrbitFacesTwoSided RS) (inside : Finset V)
    (face : CutIncidentFace RS (vertexSetCrossingEdges RS inside))
    (fragment : FaceRegionalFragment RS (orbitFaceRoot RS face.1)
      (vertexSetRegionEdges RS inside)) :
    ∃ index : Fin (Fintype.card (BoundaryRegionalFragment RS
        (vertexSetCrossingEdges RS inside)
        (vertexSetRegionEdges RS inside))),
      boundaryRegionalFragmentAt RS (vertexSetCrossingEdges RS inside)
          (vertexSetRegionEdges RS inside) index =
        cutIncidentFaceRegionalFragmentEquivBoundary RS hcubic hrotation
          htwoSided inside ⟨face, fragment⟩ :=
  exists_boundaryRegionalFragmentAt_eq RS
    (vertexSetCrossingEdges RS inside) (vertexSetRegionEdges RS inside)
    (cutIncidentFaceRegionalFragmentEquivBoundary RS hcubic hrotation
      htwoSided inside ⟨face, fragment⟩)

end

end GoertzelV24VertexSideBoundaryFragmentCoverage

end Mettapedia.GraphTheory.FourColor
