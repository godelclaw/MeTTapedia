import Mettapedia.GraphTheory.FourColor.GoertzelV24FourEdgeCutAlternatingTrail
import Mettapedia.GraphTheory.FourColor.GoertzelV24FourEdgeCutStateOverlap
import Mettapedia.GraphTheory.FourColor.GoertzelV24KempePortPrimalTrail

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FourEdgeCutKempeEscape

open GoertzelV24FourDefectBoundary
open GoertzelV24CyclicExactCutConnectedSides
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourEdgeCutAlternatingTrail
open GoertzelV24FourEdgeCutBoundaryData
open GoertzelV24FourEdgeCutClosureColor
open GoertzelV24FourEdgeCutNoncrossingInterfaces
open GoertzelV24FourEdgeCutRetainedBridge
open GoertzelV24FourEdgeCutStateOverlap
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationVertexCutProfile
open GoertzelV24ThreeEdgeCutMinimality
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

/-- Switching a proper nonempty part of a constant four-port word cannot
leave the word all-equal. -/
theorem boundaryKempeSwap_constant_not_allEqual :
    ∀ (a b : Color) (support : Finset (Fin 4)),
      ValidColorPair a b →
        0 ∈ support → support ≠ Finset.univ →
          ¬ SquareBoundaryWord.AllEqual
            (boundaryKempeSwap a b support (fun _ ↦ a)) := by
  intro a b support hab hzero hproper hall
  have hone : 1 ∈ support := by
    by_contra hone
    have heq := hall.1
    simp [boundaryKempeSwap, hzero, hone] at heq
    exact hab.2.2 heq.symm
  have htwo : 2 ∈ support := by
    by_contra htwo
    have heq := hall.2.1
    simp [boundaryKempeSwap, hone, htwo] at heq
    exact hab.2.2 heq.symm
  have hthree : 3 ∈ support := by
    by_contra hthree
    have heq := hall.2.2
    simp [boundaryKempeSwap, htwo, hthree] at heq
    exact hab.2.2 heq.symm
  apply hproper
  ext port
  fin_cases port <;> simp [hzero, hone, htwo, hthree]

/-- If the component through port zero turns a constant word into the
opposite-pair class, its boundary support is exactly the opposite pair
`{0,2}`. -/
theorem support_eq_zero_two_of_constant_opposite_swap :
    ∀ (a b : Color) (support : Finset (Fin 4)),
      ValidColorPair a b → 0 ∈ support →
        SquareBoundaryWord.OppositePairs
          (boundaryKempeSwap a b support (fun _ ↦ a)) →
          support = {0, 2} := by
  intro a b support hab hzero hopposite
  have htwo : 2 ∈ support := by
    by_contra htwo
    have heq := hopposite.1
    simp [boundaryKempeSwap, hzero, htwo] at heq
    exact hab.2.2 heq.symm
  have hone : 1 ∉ support := by
    intro hone
    apply hopposite.2.2
    simp [boundaryKempeSwap, hzero, hone]
  have hthree : 3 ∉ support := by
    intro hthree
    have heq := hopposite.2.1
    simp [boundaryKempeSwap, hone, hthree, hab.2.2] at heq
  ext port
  fin_cases port <;> simp [hzero, hone, htwo, hthree]

/-- A second component through port one, disjoint at ports zero and two,
must terminate at port three once its switched word obeys four-pole parity. -/
theorem support_eq_one_three_of_classified_constant_swap :
    ∀ (a b : Color) (support : Finset (Fin 4)),
      ValidColorPair a b → 1 ∈ support →
        0 ∉ support → 2 ∉ support →
        (SquareBoundaryWord.AllEqual
            (boundaryKempeSwap a b support (fun _ ↦ a)) ∨
          SquareBoundaryWord.AdjacentPairs
            (boundaryKempeSwap a b support (fun _ ↦ a)) ∨
          SquareBoundaryWord.OppositePairs
            (boundaryKempeSwap a b support (fun _ ↦ a))) →
          support = {1, 3} := by
  intro a b support hab hone hzero htwo hclassified
  have hthree : 3 ∈ support := by
    by_contra hthree
    rcases hclassified with hall | hadjacent | hopposite
    · simp [SquareBoundaryWord.AllEqual, boundaryKempeSwap,
        hzero, hone, htwo, hthree, hab.2.2] at hall
    · rcases hadjacent with hadjacent | hadjacent
      · simp [SquareBoundaryWord.Adjacent01_23, boundaryKempeSwap,
          hzero, hone, htwo, hthree, hab.2.2] at hadjacent
      · simp [SquareBoundaryWord.Adjacent12_30, boundaryKempeSwap,
          hzero, hone, htwo, hthree] at hadjacent
    · simp [SquareBoundaryWord.OppositePairs, boundaryKempeSwap,
        hzero, hone, htwo, hthree] at hopposite
      exact hopposite.2 hopposite.1.symm
  ext port
  fin_cases port <;> simp [hzero, hone, htwo, hthree]

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance kempeEscapeGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- If the left endpoints of two simple routes lie in distinct selected
Kempe components, their entire line-graph supports are disjoint. -/
theorem evenKempePortPaths_ambient_support_disjoint_of_not_connected
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b : Color}
    {firstLeft firstRight secondLeft secondRight : Fin 4}
    (firstRoute : data.EvenKempePortPath C a b firstLeft firstRight)
    (secondRoute : data.EvenKempePortPath C a b secondLeft secondRight)
    (hnotConnected :
      ¬ data.KempePortsConnected C a b firstLeft secondLeft) :
    firstRoute.ambientPath.support.Disjoint
      secondRoute.ambientPath.support := by
  rw [List.disjoint_left]
  intro edge hfirst hsecond
  rcases (firstRoute.mem_ambientPath_support_iff edge).1 hfirst with
    ⟨hselectedFirst, hpathFirst⟩
  rcases (secondRoute.mem_ambientPath_support_iff edge).1 hsecond with
    ⟨hselectedSecond, hpathSecond⟩
  let shared : C.bicoloredSet a b := ⟨edge, hselectedFirst⟩
  have hsharedFirst : shared ∈ firstRoute.path.support := by
    simpa only [shared] using hpathFirst
  have hsharedSecond : shared ∈ secondRoute.path.support := by
    simpa only [shared] using hpathSecond
  have hreachFirst :
      (C.bicoloredSubgraph a b).Reachable firstRoute.leftEdge shared :=
    (firstRoute.path.takeUntil shared hsharedFirst).reachable
  have hreachSecond :
      (C.bicoloredSubgraph a b).Reachable secondRoute.leftEdge shared :=
    (secondRoute.path.takeUntil shared hsharedSecond).reachable
  apply hnotConnected
  exact ⟨firstRoute.leftEdge, secondRoute.leftEdge,
    firstRoute.leftIncident, secondRoute.leftIncident,
    hreachFirst.trans hreachSecond.symm⟩

/-- Every nonzero Tait color can be chosen as the first member of a valid
two-color Kempe pair. -/
theorem exists_validColorPair_with_first_of_ne_zero
    {a : Color} (ha : a ≠ 0) :
    ∃ b : Color, ValidColorPair a b := by
  rcases exists_validColorPair_containing_of_ne_zero ha ha with
    ⟨first, second, hpair, haSelected, _⟩
  rcases haSelected with rfl | rfl
  · exact ⟨second, hpair⟩
  · exact ⟨first, hpair.2.1, hpair.1, hpair.2.2.symm⟩

/-- An all-equal Tait state on a planar four-pole has an adjacent-pair
Kempe successor whenever edge-disjoint opposite port trails are forbidden.
This is the graph-theoretic core of the all-equal escape. -/
theorem exists_adjacent_kempe_successor_of_no_disjoint_opposite_trails
    (data : DegreeTwoBoundaryData G 4)
    (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    {a : Color}
    (hconstant : ∀ port : Fin 4, data.colorWord C port = a)
    (hnoOppositeTrails :
      ∀ (firstTrail : G.Walk (data.defectVertex 0)
          (data.defectVertex 2))
        (secondTrail : G.Walk (data.defectVertex 1)
          (data.defectVertex 3)),
        firstTrail.IsTrail → secondTrail.IsTrail →
          firstTrail.edges.Disjoint secondTrail.edges → False) :
    ∃ C' : G.EdgeColoring Color,
      IsTaitEdgeColoring G C' ∧
        SquareBoundaryWord.AdjacentPairs (data.colorWord C') := by
  have ha : a ≠ 0 := by
    rw [← hconstant 0]
    exact data.colorWord_ne_zero hdata C 0
  rcases exists_validColorPair_with_first_of_ne_zero ha with ⟨b, hab⟩
  have hselected : ∀ port : Fin 4,
      data.colorWord C port = a ∨ data.colorWord C port = b :=
    fun port ↦ Or.inl (hconstant port)
  have hwordConstant : data.colorWord C = fun _ ↦ a :=
    funext hconstant

  rcases data.existsUnique_incident_bicolored_edge_of_colorWord_selected
      hdata C hab 0 (hselected 0) with
    ⟨edge0, hedge0, _hunique0⟩
  let selected0 : C.bicoloredSet a b := ⟨edge0, hedge0.2⟩
  let K0 := (C.bicoloredSubgraph a b).connectedComponentMk selected0
  have hK0zero : data.KempeComponentMeetsPort C a b K0 0 := by
    exact ⟨edge0, hedge0.1,
      C.mem_kempeComponentSet_self selected0.property⟩
  have hzeroSupport0 : 0 ∈ data.kempePortSupport C a b K0 :=
    (data.mem_kempePortSupport_iff C a b K0 0).2 hK0zero
  have hsupport0Proper :
      data.kempePortSupport C a b K0 ≠ Finset.univ := by
    intro hsupport
    apply data.not_exists_allPort_kempeComponent hdata C hab hselected
    exact ⟨K0, hsupport⟩

  let C0 := C.swapOnKempeComponent a b K0
  have hC0 : IsTaitEdgeColoring G C0 :=
    GoertzelV24FramedTrail.isTaitEdgeColoring_swapOnKempeComponent
      hC hab K0
  have hword0 : data.colorWord C0 =
      boundaryKempeSwap a b (data.kempePortSupport C a b K0)
        (data.colorWord C) := by
    exact data.colorWord_swapOnKempeComponent_eq_boundaryKempeSwap
      C hab K0
  have hnotAll0 : ¬ SquareBoundaryWord.AllEqual (data.colorWord C0) := by
    rw [hword0, hwordConstant]
    exact boundaryKempeSwap_constant_not_allEqual a b
      (data.kempePortSupport C a b K0) hab hzeroSupport0 hsupport0Proper
  have hclass0 := data.four_colorWord_classification hdata C0 hC0
  rcases hclass0.resolve_left hnotAll0 with hadjacent0 | hopposite0
  · exact ⟨C0, hC0, hadjacent0⟩

  have hsupport0 : data.kempePortSupport C a b K0 = {0, 2} := by
    apply support_eq_zero_two_of_constant_opposite_swap
      a b (data.kempePortSupport C a b K0) hab hzeroSupport0
    rw [← hwordConstant, ← hword0]
    exact hopposite0
  have hK0two : data.KempeComponentMeetsPort C a b K0 2 := by
    apply (data.mem_kempePortSupport_iff C a b K0 2).1
    rw [hsupport0]
    simp
  have hK0notOne : ¬ data.KempeComponentMeetsPort C a b K0 1 := by
    intro hmeet
    have hmem := (data.mem_kempePortSupport_iff C a b K0 1).2 hmeet
    rw [hsupport0] at hmem
    simp at hmem

  rcases data.existsUnique_incident_bicolored_edge_of_colorWord_selected
      hdata C hab 1 (hselected 1) with
    ⟨edge1, hedge1, _hunique1⟩
  let selected1 : C.bicoloredSet a b := ⟨edge1, hedge1.2⟩
  let K1 := (C.bicoloredSubgraph a b).connectedComponentMk selected1
  have hK1one : data.KempeComponentMeetsPort C a b K1 1 := by
    exact ⟨edge1, hedge1.1,
      C.mem_kempeComponentSet_self selected1.property⟩
  have hK1neK0 : K1 ≠ K0 := by
    intro heq
    apply hK0notOne
    simpa [heq] using hK1one
  have hK1notZero : ¬ data.KempeComponentMeetsPort C a b K1 0 := by
    intro hmeet
    apply hK1neK0
    exact data.kempeComponent_eq_of_meetsPort_of_colorWord_selected
      hdata C hab 0 (hselected 0) hmeet hK0zero
  have hK1notTwo : ¬ data.KempeComponentMeetsPort C a b K1 2 := by
    intro hmeet
    apply hK1neK0
    exact data.kempeComponent_eq_of_meetsPort_of_colorWord_selected
      hdata C hab 2 (hselected 2) hmeet hK0two
  have honeSupport1 : 1 ∈ data.kempePortSupport C a b K1 :=
    (data.mem_kempePortSupport_iff C a b K1 1).2 hK1one
  have hzeroNotSupport1 : 0 ∉ data.kempePortSupport C a b K1 := by
    simpa only [data.mem_kempePortSupport_iff] using hK1notZero
  have htwoNotSupport1 : 2 ∉ data.kempePortSupport C a b K1 := by
    simpa only [data.mem_kempePortSupport_iff] using hK1notTwo

  let C1 := C.swapOnKempeComponent a b K1
  have hC1 : IsTaitEdgeColoring G C1 :=
    GoertzelV24FramedTrail.isTaitEdgeColoring_swapOnKempeComponent
      hC hab K1
  have hword1 : data.colorWord C1 =
      boundaryKempeSwap a b (data.kempePortSupport C a b K1)
        (data.colorWord C) := by
    exact data.colorWord_swapOnKempeComponent_eq_boundaryKempeSwap
      C hab K1
  have hclass1 := data.four_colorWord_classification hdata C1 hC1
  have hsupport1 : data.kempePortSupport C a b K1 = {1, 3} := by
    apply support_eq_one_three_of_classified_constant_swap
      a b (data.kempePortSupport C a b K1) hab honeSupport1
      hzeroNotSupport1 htwoNotSupport1
    rw [← hwordConstant, ← hword1]
    exact hclass1
  have hK1three : data.KempeComponentMeetsPort C a b K1 3 := by
    apply (data.mem_kempePortSupport_iff C a b K1 3).1
    rw [hsupport1]
    simp

  have hconnected02 : data.KempePortsConnected C a b 0 2 :=
    (data.kempePortsConnected_iff_exists_component_meets_both
      C a b 0 2).2 ⟨K0, hK0zero, hK0two⟩
  have hconnected13 : data.KempePortsConnected C a b 1 3 :=
    (data.kempePortsConnected_iff_exists_component_meets_both
      C a b 1 3).2 ⟨K1, hK1one, hK1three⟩
  rcases data.exists_even_simpleKempePortPath_of_constant_colorWord
      hdata C hC hab hconstant 0 2 hconnected02 with
    ⟨leftEdge02, rightEdge02, hleftIncident02, hrightIncident02,
      hleftColor02, hrightColor02, path02, hpath02, heven02⟩
  let route02 : data.EvenKempePortPath C a b 0 2 :=
    ⟨leftEdge02, rightEdge02, hleftIncident02, hrightIncident02,
      hleftColor02, hrightColor02, path02, hpath02, heven02⟩
  rcases data.exists_even_simpleKempePortPath_of_constant_colorWord
      hdata C hC hab hconstant 1 3 hconnected13 with
    ⟨leftEdge13, rightEdge13, hleftIncident13, hrightIncident13,
      hleftColor13, hrightColor13, path13, hpath13, heven13⟩
  let route13 : data.EvenKempePortPath C a b 1 3 :=
    ⟨leftEdge13, rightEdge13, hleftIncident13, hrightIncident13,
      hleftColor13, hrightColor13, path13, hpath13, heven13⟩
  have hnotConnected01 : ¬ data.KempePortsConnected C a b 0 1 := by
    intro hconnected
    rcases (data.kempePortsConnected_iff_exists_component_meets_both
      C a b 0 1).1 hconnected with ⟨K, hKzero, hKone⟩
    have heq : K = K0 :=
      data.kempeComponent_eq_of_meetsPort_of_colorWord_selected
        hdata C hab 0 (hselected 0) hKzero hK0zero
    apply hK0notOne
    simpa [heq] using hKone
  have hrouteDisjoint : route02.ambientPath.support.Disjoint
      route13.ambientPath.support :=
    evenKempePortPaths_ambient_support_disjoint_of_not_connected
      route02 route13 hnotConnected01

  rcases route02.exists_primalTrail hdata hab
      (Or.inl (hconstant 0)) (Or.inl (hconstant 2)) (by decide) with
    ⟨trail02, htrail02, hedges02⟩
  rcases route13.exists_primalTrail hdata hab
      (Or.inl (hconstant 1)) (Or.inl (hconstant 3)) (by decide) with
    ⟨trail13, htrail13, hedges13⟩
  have htrailDisjoint : trail02.edges.Disjoint trail13.edges := by
    rw [hedges02, hedges13]
    exact hrouteDisjoint.map Subtype.val_injective
  exact (hnoOppositeTrails trail02 trail13 htrail02 htrail13
    htrailDisjoint).elim

/-- The all-equal escape holds for the concrete state family of an exact
cyclic four-cut in a connected spherical cubic rotation system. -/
theorem commonRetainedStateSet_allEqualKempeEscape_of_topology
    (graphData : Data G)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (hsphere : OrbitSphericalCubicMapData graphData.toRotationSystem)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 4)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut)) :
    BoundaryClassSupported
        (commonRetainedStateSet graphData cut cyclicData) .allEqual →
      BoundaryClassSupported
          (commonRetainedStateSet graphData cut cyclicData) .adjacent01_23 ∨
        BoundaryClassSupported
          (commonRetainedStateSet graphData cut cyclicData)
            .adjacent12_30 := by
  rintro ⟨word, ⟨C, hC, hword⟩, hall⟩
  subst word
  let data := commonRetainedBoundaryData graphData cut cyclicData
  let hcubicGraph : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3 := fun vertex ↦ by
    rw [GoertzelV24DeletedEdgeTrail.incidentEdgeFinset_card_eq_degree]
    exact (graphData.toRotationSystem_isCubic_iff.mp hcubic) vertex
  have hdata : data.WellFormed :=
    commonRetainedBoundaryData_wellFormed
      graphData hcubicGraph hcyclic cut hcard cyclicData
  let a := data.colorWord C 0
  have hconstant : ∀ port : Fin 4, data.colorWord C port = a := by
    intro port
    fin_cases port
    · rfl
    · exact hall.1.symm
    · exact (hall.1.trans hall.2.1).symm
    · exact (hall.1.trans (hall.2.1.trans hall.2.2)).symm
  have hnoOppositeTrails :
      ∀ (firstTrail : (retainedCutGraph G cut).Walk
          (data.defectVertex 0) (data.defectVertex 2))
        (secondTrail : (retainedCutGraph G cut).Walk
          (data.defectVertex 1) (data.defectVertex 3)),
        firstTrail.IsTrail → secondTrail.IsTrail →
          firstTrail.edges.Disjoint secondTrail.edges → False := by
    intro firstTrail secondTrail hfirstTrail hsecondTrail hdisjoint
    have hsecondNil : ¬ secondTrail.Nil := by
      intro hnil
      have hendpoints : data.defectVertex 1 = data.defectVertex 3 :=
        SimpleGraph.Walk.eq_of_length_eq_zero
          (SimpleGraph.Walk.length_eq_zero_iff.mpr hnil)
      exact (by decide : (1 : Fin 4) ≠ 3) (hdata.1 hendpoints)
    exact no_edge_disjoint_opposite_retained_trails_of_exact_cut
      graphData htwoSided hdual hconnected hsphere hcubic hrotation
      hcyclic cut hcard cyclicData firstTrail secondTrail
      hfirstTrail hsecondTrail hsecondNil hdisjoint
  rcases exists_adjacent_kempe_successor_of_no_disjoint_opposite_trails
      data hdata C hC hconstant hnoOppositeTrails with
    ⟨C', hC', hadjacent⟩
  rcases hadjacent with hadjacent01 | hadjacent12
  · exact Or.inl ⟨data.colorWord C', ⟨C', hC', rfl⟩, hadjacent01⟩
  · exact Or.inr ⟨data.colorWord C', ⟨C', hC', rfl⟩, hadjacent12⟩

/-- In a graph-backed vertex-minimal counterexample the ambient structural
fields discharge every topological premise of the concrete all-equal
escape. -/
theorem commonRetainedStateSet_allEqualKempeEscape
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut)) :
    BoundaryClassSupported
        (commonRetainedStateSet graphData cut cyclicData) .allEqual →
      BoundaryClassSupported
          (commonRetainedStateSet graphData cut cyclicData) .adjacent01_23 ∨
        BoundaryClassSupported
          (commonRetainedStateSet graphData cut cyclicData)
            .adjacent12_30 := by
  have hconnected : G.Connected := by
    rw [← GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq
      G graphData]
    exact minimal.primalConnected
  have hdual : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))).Connected :=
    orbitFaceInteriorDual_connected graphData.toRotationSystem
      minimal.spherical.cubic minimal.primalConnected
      minimal.vertexRotationCyclic
  have hcyclic :=
    cyclicEdgeConnectivityAtLeast_four_of_vertexMinimalTaitCounterexample
      graphData minimal
  exact commonRetainedStateSet_allEqualKempeEscape_of_topology
    graphData minimal.facesTwoSided hdual hconnected minimal.spherical
    minimal.spherical.cubic minimal.vertexRotationCyclic hcyclic
    cut hcard cyclicData

/-- The concrete complement-side color states of an exact cyclic four-cut
form the noncrossing four-pole profile required by the overlap theorem.
In particular, its all-equal escape is now a theorem rather than profile
input. -/
noncomputable def commonRetainedStateProfile
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut)) :
    NoncrossingFourPoleStateProfile := by
  let hcubicGraph : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3 := fun vertex ↦ by
    rw [GoertzelV24DeletedEdgeTrail.incidentEdgeFinset_card_eq_degree]
    exact (graphData.toRotationSystem_isCubic_iff.mp
      minimal.spherical.cubic) vertex
  let hcyclic :=
    cyclicEdgeConnectivityAtLeast_four_of_vertexMinimalTaitCounterexample
      graphData minimal
  exact
    { states := commonRetainedStateSet graphData cut cyclicData
      nonzero := fun word hword ↦
        commonRetainedStateSet_nonzero graphData hcubicGraph hcyclic
          cut hcard cyclicData word hword
      join01_23 := commonRetainedStateSet_has_compatible
        graphData minimal cut hcard cyclicData .join01_23
      join12_30 := commonRetainedStateSet_has_compatible
        graphData minimal cut hcard cyclicData .join12_30
      allEqualKempeEscape :=
        commonRetainedStateSet_allEqualKempeEscape
          graphData minimal cut hcard cyclicData }

@[simp]
theorem commonRetainedStateProfile_states
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut)) :
    (commonRetainedStateProfile graphData minimal cut hcard cyclicData).states =
      commonRetainedStateSet graphData cut cyclicData := by
  rfl

end

end GoertzelV24FourEdgeCutKempeEscape

end Mettapedia.GraphTheory.FourColor
