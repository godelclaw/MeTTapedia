import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationSystemPrimalFaceTransport

namespace Mettapedia.GraphTheory.FourColor

/-!
# Geometry transport to the computed primal graph

Canonical graph backing of an endpoint-simple rotation system changes the
edge, dart, and quotient-face carriers, but not its cellular geometry.  This
module transports facial boundary support and the selected-face dual graph
through those canonical equivalences.

The result is representation transport only.  It does not prove that a
particular splice has simple facial boundaries or connected internal dual;
those remain literal geometric obligations on the splice rotation system.
-/

namespace GoertzelV24RotationSystemPrimalGeometryTransport

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24RotationSystemPrimalEdgePresentation
open GoertzelV24RotationSystemPrimalFaceTransport
open GoertzelV24RotationSystemPrimalGraphBacking

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

local instance rotationPrimalGraphAdjDecidable (RS : RotationSystem V E) :
    DecidableRel (rotationPrimalGraph RS).Adj :=
  Classical.decRel _

local instance rotationPrimalGraphEdgeDecidableEq (RS : RotationSystem V E) :
    DecidableEq (rotationPrimalGraph RS).edgeSet :=
  Subtype.instDecidableEq

/-- The canonical graph-backing dart equivalence restricts to an equivalence
on every complete facial orbit. -/
def graphFaceDartEquiv
    (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints)
    (face : OrbitFace RS) :
    {dart : RS.D // dart ∈ orbitFaceDarts RS face} ≃
      {dart : (graphData RS hinjective).toRotationSystem.D //
        dart ∈ orbitFaceDarts (graphData RS hinjective).toRotationSystem
          (graphFaceEquiv RS hinjective face)} where
  toFun dart := ⟨primalDartEquiv RS hinjective dart.1, by
    rw [mem_orbitFaceDarts_iff, ← graphFaceEquiv_dartOrbitFace]
    exact congrArg (graphFaceEquiv RS hinjective)
      ((mem_orbitFaceDarts_iff RS face dart.1).1 dart.2)⟩
  invFun dart := ⟨(primalDartEquiv RS hinjective).symm dart.1, by
    rw [mem_orbitFaceDarts_iff]
    apply (graphFaceEquiv RS hinjective).injective
    rw [graphFaceEquiv_dartOrbitFace]
    have hface := (mem_orbitFaceDarts_iff
      (graphData RS hinjective).toRotationSystem
      (graphFaceEquiv RS hinjective face) dart.1).1 dart.2
    simpa using hface⟩
  left_inv dart := by
    apply Subtype.ext
    exact (primalDartEquiv RS hinjective).symm_apply_apply dart.1
  right_inv dart := by
    apply Subtype.ext
    exact (primalDartEquiv RS hinjective).apply_symm_apply dart.1

/-- Graph backing preserves the number of darts in every quotient face. -/
theorem graphFaceEquiv_orbitFaceDarts_card
    (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints)
    (face : OrbitFace RS) :
    (orbitFaceDarts (graphData RS hinjective).toRotationSystem
      (graphFaceEquiv RS hinjective face)).card =
      (orbitFaceDarts RS face).card := by
  have hcard := Fintype.card_congr (graphFaceDartEquiv RS hinjective face)
  rw [Fintype.card_coe, Fintype.card_coe] at hcard
  exact hcard.symm

/-- Representative-level form of facial-orbit cardinality preservation. -/
theorem graphData_faceOrbit_card_eq
    (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints)
    (dart : RS.D) :
    ((graphData RS hinjective).toRotationSystem.faceOrbit
      (primalDartEquiv RS hinjective dart)).card =
      (RS.faceOrbit dart).card := by
  rw [← orbitFaceDarts_dartOrbitFace_eq_faceOrbit,
    ← orbitFaceDarts_dartOrbitFace_eq_faceOrbit,
    ← graphFaceEquiv_dartOrbitFace]
  exact graphFaceEquiv_orbitFaceDarts_card RS hinjective
    (dartOrbitFace RS dart)

/-- The dart and edge graph-backing equivalences use the same underlying
unordered endpoint pair. -/
theorem graphData_edgeOf_primalDartEquiv_eq_edgeEquiv
    (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints)
    (dart : RS.D) :
    (graphData RS hinjective).toRotationSystem.edgeOf
        (primalDartEquiv RS hinjective dart) =
      edgeEquiv RS hinjective (RS.edgeOf dart) := by
  apply Subtype.ext
  rw [SimpleGraphDartRotation.Data.toRotationSystem_edgeOf]
  change s(RS.vertOf dart, RS.vertOf (RS.alpha dart)) =
    s(RS.vertOf (chosenDart RS (RS.edgeOf dart)),
      RS.vertOf (RS.alpha (chosenDart RS (RS.edgeOf dart))))
  rcases RS.edge_fiber_two_cases
      (chosenDart_edgeOf RS (RS.edgeOf dart)) rfl with hsame | hreverse
  · exact congrArg (fun source : RS.D =>
      s(RS.vertOf source, RS.vertOf (RS.alpha source))) hsame
  · have hchosen : chosenDart RS (RS.edgeOf dart) = RS.alpha dart := by
      have halpha := congrArg RS.alpha hreverse
      simpa [RS.alpha_involutive] using halpha.symm
    rw [hchosen, RS.alpha_involutive]
    exact Sym2.eq_swap

/-- Graph backing sends the literal boundary support of one quotient face
exactly to the graph-backed boundary support. -/
theorem graphFaceEquiv_orbitFaceBoundary_eq_map
    (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints)
    (face : OrbitFace RS) :
    orbitFaceBoundary (graphData RS hinjective).toRotationSystem
        (graphFaceEquiv RS hinjective face) =
      (orbitFaceBoundary RS face).map (edgeEquiv RS hinjective).toEmbedding := by
  ext graphEdge
  constructor
  · intro hgraphEdge
    rcases (mem_orbitFaceBoundary_iff
      (graphData RS hinjective).toRotationSystem
      (graphFaceEquiv RS hinjective face) graphEdge).1 hgraphEdge with
      ⟨graphDart, hgraphDartFace, hgraphDartEdge⟩
    let sourceDart := (primalDartEquiv RS hinjective).symm graphDart
    have hsourceDartFace : sourceDart ∈ orbitFaceDarts RS face := by
      rw [mem_orbitFaceDarts_iff]
      apply (graphFaceEquiv RS hinjective).injective
      rw [graphFaceEquiv_dartOrbitFace]
      simpa [sourceDart] using hgraphDartFace
    have hsourceEdge : RS.edgeOf sourceDart ∈ orbitFaceBoundary RS face :=
      (mem_orbitFaceBoundary_iff RS face (RS.edgeOf sourceDart)).2
        ⟨sourceDart, hsourceDartFace, rfl⟩
    apply Finset.mem_map.2
    refine ⟨RS.edgeOf sourceDart, hsourceEdge, ?_⟩
    have htransport :=
      graphData_edgeOf_primalDartEquiv_eq_edgeEquiv RS hinjective sourceDart
    rw [Equiv.apply_symm_apply] at htransport
    exact htransport.symm.trans hgraphDartEdge
  · intro hgraphEdge
    rcases Finset.mem_map.1 hgraphEdge with ⟨sourceEdge, hsourceEdge, hedge⟩
    rcases (mem_orbitFaceBoundary_iff RS face sourceEdge).1 hsourceEdge with
      ⟨sourceDart, hsourceDartFace, hsourceDartEdge⟩
    apply (mem_orbitFaceBoundary_iff
      (graphData RS hinjective).toRotationSystem
      (graphFaceEquiv RS hinjective face) graphEdge).2
    refine ⟨primalDartEquiv RS hinjective sourceDart, ?_, ?_⟩
    · rw [mem_orbitFaceDarts_iff, ← graphFaceEquiv_dartOrbitFace]
      exact congrArg (graphFaceEquiv RS hinjective)
        ((mem_orbitFaceDarts_iff RS face sourceDart).1 hsourceDartFace)
    · rw [graphData_edgeOf_primalDartEquiv_eq_edgeEquiv,
        hsourceDartEdge]
      exact hedge

/-- Graph backing preserves the support-cardinality of every facial
boundary. -/
theorem graphFaceEquiv_orbitFaceBoundary_card
    (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints)
    (face : OrbitFace RS) :
    (orbitFaceBoundary (graphData RS hinjective).toRotationSystem
      (graphFaceEquiv RS hinjective face)).card =
      (orbitFaceBoundary RS face).card := by
  rw [graphFaceEquiv_orbitFaceBoundary_eq_map]
  exact Finset.card_map _

/-- A selected literal face set, transported to the graph-backed quotient
face carrier. -/
def graphFaceFinset
    (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints)
    (faces : Finset (OrbitFace RS)) :
    Finset (OrbitFace (graphData RS hinjective).toRotationSystem) :=
  faces.map (graphFaceEquiv RS hinjective).toEmbedding

/-- Canonical face transport sends the full literal face set to the full
graph-backed face set. -/
@[simp] theorem graphFaceFinset_univ
    (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints) :
    graphFaceFinset RS hinjective Finset.univ = Finset.univ := by
  unfold graphFaceFinset
  exact Finset.map_univ_equiv (graphFaceEquiv RS hinjective)

/-- Canonical face transport commutes with adjoining one selected face. -/
@[simp] theorem graphFaceFinset_insert
    (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints)
    (face : OrbitFace RS) (faces : Finset (OrbitFace RS)) :
    graphFaceFinset RS hinjective (insert face faces) =
      insert (graphFaceEquiv RS hinjective face)
        (graphFaceFinset RS hinjective faces) := by
  unfold graphFaceFinset
  exact Finset.map_insert _ _ _

/-- Canonical face transport commutes with a singleton selection. -/
@[simp] theorem graphFaceFinset_singleton
    (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints)
    (face : OrbitFace RS) :
    graphFaceFinset RS hinjective {face} =
      {graphFaceEquiv RS hinjective face} := by
  unfold graphFaceFinset
  exact Finset.map_singleton _ _

/-- Canonical face transport commutes with finite-set difference. -/
theorem graphFaceFinset_sdiff
    (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints)
    (left right : Finset (OrbitFace RS)) :
    graphFaceFinset RS hinjective (left \ right) =
      graphFaceFinset RS hinjective left \
        graphFaceFinset RS hinjective right := by
  unfold graphFaceFinset
  exact Finset.map_sdiff left right

/-- The canonical face equivalence restricts to any selected face set. -/
def graphAmbientFaceEquiv
    (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints)
    (faces : Finset (OrbitFace RS)) :
    AmbientFace faces ≃ AmbientFace (graphFaceFinset RS hinjective faces) :=
  (graphFaceEquiv RS hinjective).subtypeEquiv (fun face => by
    simp [graphFaceFinset])

private theorem selected_orbitFace_totalIncidenceCount_le_two
    (RS : RotationSystem V E)
    (faces : Finset (OrbitFace RS)) :
    ∀ edge, totalIncidenceCount (orbitFaceBoundary RS) faces edge ≤ 2 := by
  intro edge
  calc
    totalIncidenceCount (orbitFaceBoundary RS) faces edge ≤
        totalIncidenceCount (orbitFaceBoundary RS) Finset.univ edge := by
      unfold totalIncidenceCount
      apply Finset.card_le_card
      intro face hface
      exact Finset.mem_filter.2
        ⟨Finset.mem_univ _, (Finset.mem_filter.1 hface).2⟩
    _ ≤ 2 := orbitFace_totalIncidenceCount_le_two RS edge

/-- Graph backing identifies the facial dual on every selected set of
quotient faces. -/
def graphInteriorDualIso
    (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints)
    (faces : Finset (OrbitFace RS)) :
    interiorDualGraph (orbitFaceBoundary RS) faces ≃g
      interiorDualGraph
        (orbitFaceBoundary (graphData RS hinjective).toRotationSystem)
        (graphFaceFinset RS hinjective faces) where
  toEquiv := graphAmbientFaceEquiv RS hinjective faces
  map_rel_iff' := by
    intro left right
    let graphRS := (graphData RS hinjective).toRotationSystem
    let faceEquiv := graphFaceEquiv RS hinjective
    let edgeEquiv' := edgeEquiv RS hinjective
    constructor
    · intro htarget
      rcases (interiorDualGraph_adj_iff
        (orbitFaceBoundary graphRS)
        (graphFaceFinset RS hinjective faces)).1 htarget with
        ⟨hne, graphEdge, _hinterior, hleft, hright⟩
      let edge := edgeEquiv'.symm graphEdge
      apply interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
        (orbitFaceBoundary RS) faces
        (selected_orbitFace_totalIncidenceCount_le_two RS faces)
      · intro heq
        apply hne
        change faceEquiv left.1 = faceEquiv right.1
        exact congrArg faceEquiv heq
      · have hleft' : graphEdge ∈ orbitFaceBoundary graphRS
            (faceEquiv left.1) := hleft
        rw [graphFaceEquiv_orbitFaceBoundary_eq_map] at hleft'
        simpa [edge, edgeEquiv'] using hleft'
      · have hright' : graphEdge ∈ orbitFaceBoundary graphRS
            (faceEquiv right.1) := hright
        rw [graphFaceEquiv_orbitFaceBoundary_eq_map] at hright'
        simpa [edge, edgeEquiv'] using hright'
    · intro hsource
      rcases (interiorDualGraph_adj_iff
        (orbitFaceBoundary RS) faces).1 hsource with
        ⟨hne, edge, _hinterior, hleft, hright⟩
      apply interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
        (orbitFaceBoundary graphRS)
        (graphFaceFinset RS hinjective faces)
        (selected_orbitFace_totalIncidenceCount_le_two graphRS
          (graphFaceFinset RS hinjective faces))
      · intro heq
        apply hne
        change faceEquiv left.1 = faceEquiv right.1 at heq
        exact faceEquiv.injective heq
      · change edgeEquiv' edge ∈ orbitFaceBoundary graphRS
          (faceEquiv left.1)
        rw [graphFaceEquiv_orbitFaceBoundary_eq_map]
        exact Finset.mem_map.2 ⟨edge, hleft, rfl⟩
      · change edgeEquiv' edge ∈ orbitFaceBoundary graphRS
          (faceEquiv right.1)
        rw [graphFaceEquiv_orbitFaceBoundary_eq_map]
        exact Finset.mem_map.2 ⟨edge, hright, rfl⟩

/-- Internal-dual connectedness is invariant under canonical graph backing. -/
theorem graphInteriorDual_connected_iff
    (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints)
    (faces : Finset (OrbitFace RS)) :
    (interiorDualGraph
      (orbitFaceBoundary (graphData RS hinjective).toRotationSystem)
      (graphFaceFinset RS hinjective faces)).Connected ↔
      (interiorDualGraph (orbitFaceBoundary RS) faces).Connected :=
  (graphInteriorDualIso RS hinjective faces).connected_iff.symm

end

end GoertzelV24RotationSystemPrimalGeometryTransport

end Mettapedia.GraphTheory.FourColor
