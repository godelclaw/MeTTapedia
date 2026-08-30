import Mathlib.Combinatorics.SimpleGraph.Ends.Defs
import Mettapedia.GraphTheory.FourColor.GoertzelV24CycleSupportMinimality
import Mettapedia.GraphTheory.FourColor.GoertzelV24SharedFacesTwoEdgeSeparator
import Mettapedia.GraphTheory.FourColor.GoertzelV24VertexSidePrimalKempeFaceSeparator

/-!
# A simple primal cycle is a bond of the facial dual

The face-set potential of a simple primal cycle has connected selected and
unselected sides in the facial dual.  The proof is the circuit--bond argument:
the boundary of one proper dual component would be a nonempty binary cycle
strictly supported inside the original simple cycle.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24PrimalCycleFacialBond

open SimpleGraph
open SimpleGraphDartRotation
open GoertzelV24CycleSupportMinimality
open GoertzelV24FaceBoundaryLinearAlgebra
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexagonPairingTargetAwareBoundary
open GoertzelV24KauffmanFacePotential
open GoertzelV24OpenTangleComposition
open GoertzelV24OrbitFaceCycleSpaceEquality
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24PortTangleCommonKempeWeb
open GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24PortTangleKempeEndpoints
open GoertzelV24PrimalCycleSpace
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24SharedFacesTwoEdgeSeparator
open GoertzelV24SimpleGraphFaceDualConnectedness
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24VertexSidePrimalKempeFaceSeparator
open GoertzelV24VertexSidePrimalKempeTrail

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The full facial dual, with the vacuous `Finset.univ` subtype removed from
its vertex type. -/
def orbitFaceDualGraph (data : Data G) :
    SimpleGraph (OrbitFace data.toRotationSystem) where
  Adj left right :=
    (interiorDualGraph (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Adj
        ⟨left, Finset.mem_univ _⟩ ⟨right, Finset.mem_univ _⟩
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => h.ne rfl⟩

/-- Forgetting the `Finset.univ` membership proof is a graph homomorphism
from the ambient-face presentation to `orbitFaceDualGraph`. -/
def ambientFaceValHom (data : Data G) :
    interiorDualGraph (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset (OrbitFace data.toRotationSystem)) →g
      orbitFaceDualGraph data where
  toFun := Subtype.val
  map_rel' := by
    intro left right hadj
    exact hadj

/-- Connectedness of the existing full-dual carrier transfers to the direct
quotient-face carrier. -/
theorem orbitFaceDualGraph_connected
    (data : Data G)
    (hclass : BridgelessSphericalCubicMapData data.toRotationSystem) :
    (orbitFaceDualGraph data).Connected := by
  let hfull := orbitFaceInteriorDual_connected data.toRotationSystem
    hclass.spherical.cubic hclass.primalConnected
    hclass.vertexRotationCyclic
  letI : Nonempty (OrbitFace data.toRotationSystem) :=
    ⟨dartOrbitFace data.toRotationSystem data.toRotationSystem.outer⟩
  constructor
  intro left right
  have hreach := hfull.preconnected
    (⟨left, Finset.mem_univ _⟩ : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)))
    (⟨right, Finset.mem_univ _⟩ : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)))
  change (orbitFaceDualGraph data).Reachable left right
  exact hreach.map (ambientFaceValHom data)

/-- Faces in one connected component of the selected induced dual, viewed
again as a finite set of quotient faces. -/
def componentFaceSet (data : Data G)
    (faces : Finset (OrbitFace data.toRotationSystem))
    (component : ((orbitFaceDualGraph data).induce
      {face | face ∈ faces}).ConnectedComponent) :
    Finset (OrbitFace data.toRotationSystem) := by
  classical
  exact Finset.univ.filter fun face =>
    ∃ hface : face ∈ faces,
      (⟨face, hface⟩ : {face | face ∈ faces}) ∈ component.supp

theorem mem_componentFaceSet_iff
    (data : Data G) (faces : Finset (OrbitFace data.toRotationSystem))
    (component : ((orbitFaceDualGraph data).induce
      {face | face ∈ faces}).ConnectedComponent)
    {face : OrbitFace data.toRotationSystem} :
    face ∈ componentFaceSet data faces component ↔
      ∃ hface : face ∈ faces,
        (⟨face, hface⟩ : {face | face ∈ faces}) ∈ component.supp := by
  simp [componentFaceSet]

theorem componentFaceSet_subset
    (data : Data G) (faces : Finset (OrbitFace data.toRotationSystem))
    (component : ((orbitFaceDualGraph data).induce
      {face | face ∈ faces}).ConnectedComponent) :
    componentFaceSet data faces component ⊆ faces := by
  intro face hface
  exact (mem_componentFaceSet_iff data faces component).1 hface |>.choose

theorem componentFaceSet_nonempty
    (data : Data G) (faces : Finset (OrbitFace data.toRotationSystem))
    (component : ((orbitFaceDualGraph data).induce
      {face | face ∈ faces}).ConnectedComponent) :
    (componentFaceSet data faces component).Nonempty := by
  rcases component.exists_rep with ⟨face, rfl⟩
  refine ⟨face.1, (mem_componentFaceSet_iff data faces _).2 ?_⟩
  exact ⟨face.2, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩

/-- A selected dual neighbour of a face in one selected component remains
in that component. -/
theorem mem_componentFaceSet_of_adj
    (data : Data G) (faces : Finset (OrbitFace data.toRotationSystem))
    (component : ((orbitFaceDualGraph data).induce
      {face | face ∈ faces}).ConnectedComponent)
    {left right : OrbitFace data.toRotationSystem}
    (hleft : left ∈ componentFaceSet data faces component)
    (hright : right ∈ faces)
    (hadj : (orbitFaceDualGraph data).Adj left right) :
    right ∈ componentFaceSet data faces component := by
  rcases (mem_componentFaceSet_iff data faces component).1 hleft with
    ⟨hleftFaces, hleftComponent⟩
  refine (mem_componentFaceSet_iff data faces component).2
    ⟨hright, ?_⟩
  have hinduced : ((orbitFaceDualGraph data).induce
      {face | face ∈ faces}).Adj
      ⟨left, hleftFaces⟩ ⟨right, hright⟩ := hadj
  exact (component.mem_supp_congr_adj hinduced).mp hleftComponent

/-- On an edge shared by two distinct quotient faces, a face-set boundary is
the sum of the two face indicators. -/
theorem faceSetBoundary_apply_eq_of_shared_face_pair
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (faces : Finset (OrbitFace data.toRotationSystem))
    {left right : OrbitFace data.toRotationSystem} (hfaces : left ≠ right)
    (edge : G.edgeSet)
    (hleft : edge ∈ orbitFaceBoundary data.toRotationSystem left)
    (hright : edge ∈ orbitFaceBoundary data.toRotationSystem right) :
    orbitFaceBoundaryLinearMap data.toRotationSystem
        (faceSetIndicator data faces) edge =
      faceSetIndicator data faces left + faceSetIndicator data faces right := by
  rw [orbitFaceBoundaryLinearMap_apply]
  calc
    (∑ face : OrbitFace data.toRotationSystem,
        if edge ∈ orbitFaceBoundary data.toRotationSystem face then
          faceSetIndicator data faces face else 0) =
        ∑ face ∈ (Finset.univ.filter fun face :
          OrbitFace data.toRotationSystem =>
            edge ∈ orbitFaceBoundary data.toRotationSystem face),
          faceSetIndicator data faces face := by
      rw [Finset.sum_filter]
    _ = ∑ face ∈ ({left, right} :
          Finset (OrbitFace data.toRotationSystem)),
          faceSetIndicator data faces face := by
      rw [orbitFace_incidentFaces_eq_pair_of_mem
        data.toRotationSystem htwoSided hfaces edge hleft hright]
    _ = faceSetIndicator data faces left +
          faceSetIndicator data faces right := by
      simp [hfaces]

/-- A facial-dual adjacency supplies a primal edge shared by the two faces,
and on that edge a face-set boundary is the sum of the two indicators. -/
theorem exists_shared_edge_faceSetBoundary_apply
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (faces : Finset (OrbitFace data.toRotationSystem))
    {left right : OrbitFace data.toRotationSystem}
    (hadj : (orbitFaceDualGraph data).Adj left right) :
    ∃ edge : G.edgeSet,
      edge ∈ orbitFaceBoundary data.toRotationSystem left ∧
      edge ∈ orbitFaceBoundary data.toRotationSystem right ∧
      orbitFaceBoundaryLinearMap data.toRotationSystem
          (faceSetIndicator data faces) edge =
        faceSetIndicator data faces left + faceSetIndicator data faces right := by
  rcases (interiorDualGraph_adj_iff
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).1 hadj with
    ⟨hfaces, edge, _hinterior, hleft, hright⟩
  exact ⟨edge, hleft, hright,
    faceSetBoundary_apply_eq_of_shared_face_pair
      data htwoSided faces hfaces edge hleft hright⟩

private theorem f2_eq_one_of_ne_zero {value : F2} (hvalue : value ≠ 0) :
    value = 1 := by
  fin_cases value
  · exact (hvalue rfl).elim
  · rfl

/-- The binary boundary of one selected dual component is supported inside
the original simple primal cycle. -/
theorem componentBoundary_support_subset_cycle
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    {vertex : V} (walk : G.Walk vertex vertex)
    (faces : Finset (OrbitFace data.toRotationSystem))
    (hseparator : ∀ dart : data.toRotationSystem.D,
      (data.toRotationSystem.edgeOf dart).1 ∈ walk.edges ↔
        ((dartOrbitFace data.toRotationSystem dart ∈ faces ∧
            dartOrbitFace data.toRotationSystem
              (data.toRotationSystem.alpha dart) ∉ faces) ∨
          (dartOrbitFace data.toRotationSystem dart ∉ faces ∧
            dartOrbitFace data.toRotationSystem
              (data.toRotationSystem.alpha dart) ∈ faces)))
    (component : ((orbitFaceDualGraph data).induce
      {face | face ∈ faces}).ConnectedComponent)
    (edge : G.edgeSet)
    (hedge : orbitFaceBoundaryLinearMap data.toRotationSystem
      (faceSetIndicator data (componentFaceSet data faces component)) edge ≠ 0) :
    edge.1 ∈ walk.edges := by
  rcases data.toRotationSystem.dartsOn_nonempty edge with ⟨dart, hdart⟩
  have hdartEdge : data.toRotationSystem.edgeOf dart = edge :=
    (data.toRotationSystem.mem_dartsOn).1 hdart
  have hone : orbitFaceBoundaryLinearMap data.toRotationSystem
      (faceSetIndicator data (componentFaceSet data faces component))
        (data.toRotationSystem.edgeOf dart) = 1 := by
    rw [hdartEdge]
    exact f2_eq_one_of_ne_zero hedge
  have hsplit := (faceSetBoundary_apply_eq_one_iff_separates
    data htwoSided (componentFaceSet data faces component) dart).1 hone
  rw [← hdartEdge]
  apply (hseparator dart).2
  rcases hsplit with hsplit | hsplit
  · left
    refine ⟨componentFaceSet_subset data faces component hsplit.1, ?_⟩
    intro hrightFaces
    have hrightBoundary : data.toRotationSystem.edgeOf dart ∈
        orbitFaceBoundary data.toRotationSystem
          (dartOrbitFace data.toRotationSystem
            (data.toRotationSystem.alpha dart)) := by
      rw [← data.toRotationSystem.edge_alpha dart]
      exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace
        data.toRotationSystem (data.toRotationSystem.alpha dart)
    have hadj : (orbitFaceDualGraph data).Adj
        (dartOrbitFace data.toRotationSystem dart)
        (dartOrbitFace data.toRotationSystem
          (data.toRotationSystem.alpha dart)) := by
      exact interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
        (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset (OrbitFace data.toRotationSystem))
        (orbitFace_incidence_le_two data.toRotationSystem)
        (htwoSided dart)
        (edgeOf_mem_orbitFaceBoundary_dartOrbitFace
          data.toRotationSystem dart)
        hrightBoundary
    exact hsplit.2 (mem_componentFaceSet_of_adj data faces component
      hsplit.1 hrightFaces hadj)
  · right
    refine ⟨?_, componentFaceSet_subset data faces component hsplit.2⟩
    intro hleftFaces
    have hrightBoundary : data.toRotationSystem.edgeOf dart ∈
        orbitFaceBoundary data.toRotationSystem
          (dartOrbitFace data.toRotationSystem
            (data.toRotationSystem.alpha dart)) := by
      rw [← data.toRotationSystem.edge_alpha dart]
      exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace
        data.toRotationSystem (data.toRotationSystem.alpha dart)
    have hadj : (orbitFaceDualGraph data).Adj
        (dartOrbitFace data.toRotationSystem
          (data.toRotationSystem.alpha dart))
        (dartOrbitFace data.toRotationSystem dart) := by
      exact interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
        (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset (OrbitFace data.toRotationSystem))
        (orbitFace_incidence_le_two data.toRotationSystem)
        (htwoSided dart).symm
        hrightBoundary
        (edgeOf_mem_orbitFaceBoundary_dartOrbitFace
          data.toRotationSystem dart)
    exact hsplit.1 (mem_componentFaceSet_of_adj data faces component
      hsplit.2 hleftFaces hadj)

/-- In a connected facial dual, every proper selected component has an edge
to an unselected face. -/
theorem exists_adj_from_component_to_unselected
    (data : Data G)
    (hclass : BridgelessSphericalCubicMapData data.toRotationSystem)
    (faces : Finset (OrbitFace data.toRotationSystem))
    (component : ((orbitFaceDualGraph data).induce
      {face | face ∈ faces}).ConnectedComponent)
    {outside : OrbitFace data.toRotationSystem}
    (houtside : outside ∉ componentFaceSet data faces component) :
    ∃ inside beyond : OrbitFace data.toRotationSystem,
      inside ∈ componentFaceSet data faces component ∧
      beyond ∉ faces ∧
      (orbitFaceDualGraph data).Adj inside beyond := by
  let dual := orbitFaceDualGraph data
  let selectedComponent := componentFaceSet data faces component
  let outsideComponent : dual.ComponentCompl
      (↑selectedComponent : Set (OrbitFace data.toRotationSystem)) :=
    dual.componentComplMk houtside
  have hselectedNonempty :
      (↑selectedComponent : Set (OrbitFace data.toRotationSystem)).Nonempty := by
    rcases componentFaceSet_nonempty data faces component with ⟨face, hface⟩
    exact ⟨face, hface⟩
  rcases SimpleGraph.ComponentCompl.exists_adj_boundary_pair
      (orbitFaceDualGraph_connected data hclass).preconnected
      hselectedNonempty outsideComponent with
    ⟨pair, hpairOutside, hpairInside, hadj⟩
  have hpairNotSelected : pair.1 ∉ selectedComponent :=
    outsideComponent.notMem_of_mem hpairOutside
  have hpairNotFaces : pair.1 ∉ faces := by
    intro hpairFaces
    exact hpairNotSelected (mem_componentFaceSet_of_adj data faces component
      hpairInside hpairFaces hadj.symm)
  exact ⟨pair.2, pair.1, hpairInside, hpairNotFaces, hadj.symm⟩

/-- If a simple primal cycle is the exact boundary of a face set, the
selected faces induce a connected subgraph of the facial dual. -/
theorem selected_faces_induce_connected_of_isCycle
    (data : Data G)
    (hclass : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    {vertex : V} (walk : G.Walk vertex vertex) (hcycle : walk.IsCycle)
    (faces : Finset (OrbitFace data.toRotationSystem))
    (hseparator : ∀ dart : data.toRotationSystem.D,
      (data.toRotationSystem.edgeOf dart).1 ∈ walk.edges ↔
        ((dartOrbitFace data.toRotationSystem dart ∈ faces ∧
            dartOrbitFace data.toRotationSystem
              (data.toRotationSystem.alpha dart) ∉ faces) ∨
          (dartOrbitFace data.toRotationSystem dart ∉ faces ∧
            dartOrbitFace data.toRotationSystem
              (data.toRotationSystem.alpha dart) ∈ faces))) :
    ((orbitFaceDualGraph data).induce {face | face ∈ faces}).Connected := by
  let first := walk.firstDart hcycle.not_nil
  have hfirstEdge : (data.toRotationSystem.edgeOf first).1 ∈ walk.edges := by
    change first.edge ∈ walk.edges
    dsimp only [first]
    rw [walk.edge_firstDart hcycle.not_nil]
    exact walk.mk_start_snd_mem_edges hcycle.not_nil
  have hfirstSplit := (hseparator first).1 hfirstEdge
  obtain ⟨selectedRoot, hselectedRoot⟩ :
      ∃ face : OrbitFace data.toRotationSystem, face ∈ faces := by
    rcases hfirstSplit with hsplit | hsplit
    · exact ⟨_, hsplit.1⟩
    · exact ⟨_, hsplit.2⟩
  rw [SimpleGraph.connected_iff]
  constructor
  swap
  · exact ⟨⟨selectedRoot, hselectedRoot⟩⟩
  intro left right
  by_contra hnotReachable
  let selectedDual := (orbitFaceDualGraph data).induce
    {face | face ∈ faces}
  let leftComponent : selectedDual.ConnectedComponent :=
    selectedDual.connectedComponentMk left
  let rightComponent : selectedDual.ConnectedComponent :=
    selectedDual.connectedComponentMk right
  have hcomponentsNe : leftComponent ≠ rightComponent := by
    intro heq
    exact hnotReachable (SimpleGraph.ConnectedComponent.exact heq)
  have hleftMem : left.1 ∈
      componentFaceSet data faces leftComponent := by
    refine (mem_componentFaceSet_iff data faces leftComponent).2
      ⟨left.2, ?_⟩
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hrightMem : right.1 ∈
      componentFaceSet data faces rightComponent := by
    refine (mem_componentFaceSet_iff data faces rightComponent).2
      ⟨right.2, ?_⟩
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hrightNotLeft : right.1 ∉
      componentFaceSet data faces leftComponent := by
    intro hrightLeft
    rcases (mem_componentFaceSet_iff data faces leftComponent).1
      hrightLeft with ⟨hrightFaces, hrightComponent⟩
    have heq : rightComponent = leftComponent := by
      change selectedDual.connectedComponentMk right = leftComponent
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff
        leftComponent right).1 hrightComponent
    exact hcomponentsNe heq.symm
  have hleftNotRight : left.1 ∉
      componentFaceSet data faces rightComponent := by
    intro hleftRight
    rcases (mem_componentFaceSet_iff data faces rightComponent).1
      hleftRight with ⟨hleftFaces, hleftComponent⟩
    have heq : leftComponent = rightComponent := by
      change selectedDual.connectedComponentMk left = rightComponent
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff
        rightComponent left).1 hleftComponent
    exact hcomponentsNe heq
  rcases exists_adj_from_component_to_unselected data hclass faces
      leftComponent hrightNotLeft with
    ⟨leftInside, leftBeyond, hleftInside, hleftBeyond, hleftAdj⟩
  rcases exists_adj_from_component_to_unselected data hclass faces
      rightComponent hleftNotRight with
    ⟨rightInside, rightBeyond, hrightInside, hrightBeyond, hrightAdj⟩
  rcases exists_shared_edge_faceSetBoundary_apply data htwoSided
      (componentFaceSet data faces leftComponent) hleftAdj with
    ⟨leftEdge, hleftEdgeInside, hleftEdgeBeyond, hleftEdgeValue⟩
  have hleftBeyondNotComponent : leftBeyond ∉
      componentFaceSet data faces leftComponent := by
    intro hmem
    exact hleftBeyond
      (componentFaceSet_subset data faces leftComponent hmem)
  have hleftBoundaryNonzero :
      orbitFaceBoundaryLinearMap data.toRotationSystem
        (faceSetIndicator data
          (componentFaceSet data faces leftComponent)) leftEdge ≠ 0 := by
    rw [hleftEdgeValue]
    simp [faceSetIndicator, hleftInside, hleftBeyondNotComponent]
  rcases exists_shared_edge_faceSetBoundary_apply data htwoSided
      (componentFaceSet data faces rightComponent) hrightAdj with
    ⟨rightEdge, hrightEdgeInside, hrightEdgeBeyond, hrightEdgeValue⟩
  have hrightBeyondNotComponent : rightBeyond ∉
      componentFaceSet data faces rightComponent := by
    intro hmem
    exact hrightBeyond
      (componentFaceSet_subset data faces rightComponent hmem)
  have hrightBoundaryNonzero :
      orbitFaceBoundaryLinearMap data.toRotationSystem
        (faceSetIndicator data
          (componentFaceSet data faces rightComponent)) rightEdge ≠ 0 := by
    rw [hrightEdgeValue]
    simp [faceSetIndicator, hrightInside, hrightBeyondNotComponent]
  have hrightEdgeWalk : rightEdge.1 ∈ walk.edges :=
    componentBoundary_support_subset_cycle data htwoSided walk faces
      hseparator rightComponent rightEdge hrightBoundaryNonzero
  have hrightInsideNotLeft : rightInside ∉
      componentFaceSet data faces leftComponent := by
    intro hmem
    rcases (mem_componentFaceSet_iff data faces leftComponent).1 hmem with
      ⟨hrightFaces, hcomponent⟩
    rcases (mem_componentFaceSet_iff data faces rightComponent).1
      hrightInside with ⟨_, hcomponentRight⟩
    have heq : leftComponent = rightComponent := by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hcomponent
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hcomponentRight
      exact hcomponent.symm.trans hcomponentRight
    exact hcomponentsNe heq
  have hrightBeyondNotLeft : rightBeyond ∉
      componentFaceSet data faces leftComponent := by
    intro hmem
    exact hrightBeyond
      (componentFaceSet_subset data faces leftComponent hmem)
  have hleftBoundaryRightEdgeZero :
      orbitFaceBoundaryLinearMap data.toRotationSystem
        (faceSetIndicator data
          (componentFaceSet data faces leftComponent)) rightEdge = 0 := by
    rw [faceSetBoundary_apply_eq_of_shared_face_pair data htwoSided
      (componentFaceSet data faces leftComponent) hrightAdj.ne rightEdge
      hrightEdgeInside hrightEdgeBeyond]
    simp [faceSetIndicator, hrightInsideNotLeft, hrightBeyondNotLeft]
  have hleftBoundaryCycle :
      orbitFaceBoundaryLinearMap data.toRotationSystem
          (faceSetIndicator data
            (componentFaceSet data faces leftComponent)) ∈ f2CycleSpace G :=
    range_orbitFaceBoundaryLinearMap_le_f2CycleSpace data htwoSided
      ⟨_, rfl⟩
  have hcubic : ∀ graphVertex : V,
      (incidentEdgeFinset G graphVertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      data hclass.spherical.cubic
  have hminimalSupport := f2CycleSpace_support_eq_cycle_of_subset
    walk hcycle
    (orbitFaceBoundaryLinearMap data.toRotationSystem
      (faceSetIndicator data
        (componentFaceSet data faces leftComponent)))
    hleftBoundaryCycle hcubic
    (componentBoundary_support_subset_cycle data htwoSided walk faces
      hseparator leftComponent)
    leftEdge hleftBoundaryNonzero
  have hleftBoundaryRightEdgeNonzero :=
    (hminimalSupport rightEdge).2 hrightEdgeWalk
  exact hleftBoundaryRightEdgeNonzero hleftBoundaryRightEdgeZero

/-- A simple primal cycle has connected face sides: it is a bond of the
facial dual.  The complement is obtained by applying the same argument to
the complementary face potential. -/
theorem face_sides_connected_of_isCycle
    (data : Data G)
    (hclass : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    {vertex : V} (walk : G.Walk vertex vertex) (hcycle : walk.IsCycle)
    (faces : Finset (OrbitFace data.toRotationSystem))
    (hseparator : ∀ dart : data.toRotationSystem.D,
      (data.toRotationSystem.edgeOf dart).1 ∈ walk.edges ↔
        ((dartOrbitFace data.toRotationSystem dart ∈ faces ∧
            dartOrbitFace data.toRotationSystem
              (data.toRotationSystem.alpha dart) ∉ faces) ∨
          (dartOrbitFace data.toRotationSystem dart ∉ faces ∧
            dartOrbitFace data.toRotationSystem
              (data.toRotationSystem.alpha dart) ∈ faces))) :
    ((orbitFaceDualGraph data).induce {face | face ∈ faces}).Connected ∧
      ((orbitFaceDualGraph data).induce {face | face ∉ faces}).Connected := by
  constructor
  · exact selected_faces_induce_connected_of_isCycle
      data hclass htwoSided walk hcycle faces hseparator
  · let complementFaces : Finset (OrbitFace data.toRotationSystem) :=
      Finset.univ \ faces
    have hcomplementSeparator : ∀ dart : data.toRotationSystem.D,
        (data.toRotationSystem.edgeOf dart).1 ∈ walk.edges ↔
          ((dartOrbitFace data.toRotationSystem dart ∈ complementFaces ∧
              dartOrbitFace data.toRotationSystem
                (data.toRotationSystem.alpha dart) ∉ complementFaces) ∨
            (dartOrbitFace data.toRotationSystem dart ∉ complementFaces ∧
              dartOrbitFace data.toRotationSystem
                (data.toRotationSystem.alpha dart) ∈ complementFaces)) := by
      intro dart
      rw [hseparator dart]
      simp only [complementFaces, Finset.mem_sdiff, Finset.mem_univ,
        true_and]
      tauto
    have hcomplementFaces :
        (↑complementFaces : Set (OrbitFace data.toRotationSystem)) =
          {face | face ∉ faces} := by
      ext face
      simp [complementFaces]
    rw [← hcomplementFaces]
    exact selected_faces_induce_connected_of_isCycle
      data hclass htwoSided walk hcycle complementFaces
        hcomplementSeparator

/-- A simple primal cycle admits an exact facial separator whose two shores
are both connected. -/
theorem exists_faceSet_bond_of_isCycle
    (data : Data G)
    (hclass : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    {vertex : V} (walk : G.Walk vertex vertex) (hcycle : walk.IsCycle) :
    ∃ faces : Finset (OrbitFace data.toRotationSystem),
      (∀ dart : data.toRotationSystem.D,
        (data.toRotationSystem.edgeOf dart).1 ∈ walk.edges ↔
          ((dartOrbitFace data.toRotationSystem dart ∈ faces ∧
              dartOrbitFace data.toRotationSystem
                (data.toRotationSystem.alpha dart) ∉ faces) ∨
            (dartOrbitFace data.toRotationSystem dart ∉ faces ∧
              dartOrbitFace data.toRotationSystem
                (data.toRotationSystem.alpha dart) ∈ faces))) ∧
      ((orbitFaceDualGraph data).induce {face | face ∈ faces}).Connected ∧
      ((orbitFaceDualGraph data).induce {face | face ∉ faces}).Connected := by
  rcases exists_faceSet_separates_iff_mem_walk_of_isCycle
      data hclass htwoSided walk hcycle with ⟨faces, hseparator⟩
  exact ⟨faces, hseparator,
    face_sides_connected_of_isCycle
      data hclass htwoSided walk hcycle faces hseparator⟩

/-- A boundary-free physical Kempe component produces an ambient simple
cycle together with its exact connected facial shores. -/
theorem exists_ambientPrimalKempeCycle_faceSetBond_of_boundaryFree
    (graphData : Data G)
    (hclass : BridgelessSphericalCubicMapData
      graphData.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (keep : V → Prop)
    (outer : RetainedDart graphData.toRotationSystem keep)
    (coloring : Coloring (vertexSidePortTangle graphData keep outer))
    (hproper : IsProper coloring) (pair : TaitColorPair)
    (root : ActiveDart
      (vertexSidePortTangle graphData keep outer) coloring pair)
    (hboundaryFree : componentPortDarts
      (vertexSidePortTangle graphData keep outer) coloring pair root = ∅) :
    ∃ walk : G.Walk
        ((vertexSidePortTangle graphData keep outer).vert root.1).1
        ((vertexSidePortTangle graphData keep outer).vert root.1).1,
      walk.IsCycle ∧
        ∃ faces : Finset (OrbitFace graphData.toRotationSystem),
          (∀ dart : graphData.toRotationSystem.D,
            (graphData.toRotationSystem.edgeOf dart).1 ∈ walk.edges ↔
              ((dartOrbitFace graphData.toRotationSystem dart ∈ faces ∧
                  dartOrbitFace graphData.toRotationSystem
                    (graphData.toRotationSystem.alpha dart) ∉ faces) ∨
                (dartOrbitFace graphData.toRotationSystem dart ∉ faces ∧
                  dartOrbitFace graphData.toRotationSystem
                    (graphData.toRotationSystem.alpha dart) ∈ faces))) ∧
          ((orbitFaceDualGraph graphData).induce
            {face | face ∈ faces}).Connected ∧
          ((orbitFaceDualGraph graphData).induce
            {face | face ∉ faces}).Connected := by
  rcases exists_ambientPrimalKempeCycle_of_boundaryFree
      graphData keep outer hclass.spherical.cubic coloring hproper pair root
      hboundaryFree with ⟨walk, hcycle⟩
  rcases exists_faceSet_bond_of_isCycle
      graphData hclass htwoSided walk hcycle with
    ⟨faces, hseparator, hconnected, hcomplementConnected⟩
  exact ⟨walk, hcycle, faces, hseparator, hconnected,
    hcomplementConnected⟩

end

end GoertzelV24PrimalCycleFacialBond

end Mettapedia.GraphTheory.FourColor
