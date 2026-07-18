import Mettapedia.GraphTheory.FourColor.GoertzelV24ThreeEdgeCutCapUntouchedFaces
import Mettapedia.GraphTheory.FourColor.GoertzelV24PlanarBondSpliceEuler
import Mettapedia.GraphTheory.FourColor.GoertzelV24CyclicThreeCutConnectedSides

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24RetainedSpliceEdgeCount
open GoertzelV24RetainedSpliceAmbientFaceCount
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24CyclicThreeCutConnectedSides
open GoertzelV24FaceDualConnectedness
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24PlanarBondBoundaryOrder
open GoertzelV24PlanarBondSpliceEuler

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Map each intact retained dart to its ambient retained internal edge. -/
def internalDartToRetainedInternalEdge
    (RS : RotationSystem V E) (keep : V → Prop)
    (dart : InternalDart RS keep) : RetainedInternalEdge RS keep :=
  ⟨RS.edgeOf dart.1.1, ⟨dart, rfl⟩⟩

/-- One fiber of the intact-dart-to-edge map is the old two-dart edge
fiber. -/
def internalDartFiberEquivDartsOn
    (RS : RotationSystem V E) (keep : V → Prop)
    (edge : RetainedInternalEdge RS keep) :
    {dart : InternalDart RS keep //
      internalDartToRetainedInternalEdge RS keep dart = edge} ≃
      ↑(RS.dartsOn edge.1) := by
  let toDartsOn :
      {dart : InternalDart RS keep //
        internalDartToRetainedInternalEdge RS keep dart = edge} →
        ↑(RS.dartsOn edge.1) :=
    fun dart => ⟨dart.1.1.1, by
      apply RS.mem_dartsOn.mpr
      exact congrArg Subtype.val dart.2⟩
  apply Equiv.ofBijective toDartsOn
  constructor
  · intro left right heq
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    simpa only [toDartsOn] using congrArg Subtype.val heq
  · intro dart
    rcases edge.2 with ⟨root, hroot⟩
    rcases RS.edge_fiber_two_cases hroot
        (RS.mem_dartsOn.mp dart.2) with hsame | hopposite
    · let source : {dart : InternalDart RS keep //
          internalDartToRetainedInternalEdge RS keep dart = edge} :=
        ⟨root, by
          apply Subtype.ext
          exact hroot⟩
      refine ⟨source, ?_⟩
      apply Subtype.ext
      exact hsame.symm
    · let opposite := internalAlpha RS keep root
      let source : {dart : InternalDart RS keep //
          internalDartToRetainedInternalEdge RS keep dart = edge} :=
        ⟨opposite, by
          apply Subtype.ext
          change RS.edgeOf opposite.1.1 = edge.1
          rw [internalAlpha_val, RS.edge_alpha, hroot]⟩
      refine ⟨source, ?_⟩
      apply Subtype.ext
      change opposite.1.1 = dart.1
      rw [internalAlpha_val]
      exact hopposite.symm

theorem card_internalDartFiber_eq_two
    (RS : RotationSystem V E) (keep : V → Prop)
    (edge : RetainedInternalEdge RS keep) :
    Fintype.card {dart : InternalDart RS keep //
      internalDartToRetainedInternalEdge RS keep dart = edge} = 2 := by
  calc
    Fintype.card {dart : InternalDart RS keep //
        internalDartToRetainedInternalEdge RS keep dart = edge} =
        Fintype.card ↑(RS.dartsOn edge.1) :=
      Fintype.card_congr (internalDartFiberEquivDartsOn RS keep edge)
    _ = (RS.dartsOn edge.1).card := Fintype.card_coe _
    _ = 2 := RS.dartsOn_card_two edge.1

/-- Every retained internal edge contributes exactly its two old darts. -/
theorem card_internalDart_eq_twice_retainedInternalEdge
    (RS : RotationSystem V E) (keep : V → Prop) :
    Fintype.card (InternalDart RS keep) =
      2 * Fintype.card (RetainedInternalEdge RS keep) := by
  calc
    Fintype.card (InternalDart RS keep) =
        Fintype.card (Σ edge : RetainedInternalEdge RS keep,
          {dart : InternalDart RS keep //
            internalDartToRetainedInternalEdge RS keep dart = edge}) :=
      Fintype.card_congr
        (Equiv.sigmaFiberEquiv
          (internalDartToRetainedInternalEdge RS keep)).symm
    _ = ∑ edge : RetainedInternalEdge RS keep,
          Fintype.card {dart : InternalDart RS keep //
            internalDartToRetainedInternalEdge RS keep dart = edge} :=
      Fintype.card_sigma
    _ = 2 * Fintype.card (RetainedInternalEdge RS keep) := by
      simp_rw [card_internalDartFiber_eq_two]
      simp [mul_comm]

namespace RotationSystem

namespace ThreeEdgeCutSideData

variable {RS : RotationSystem V E} (data : ThreeEdgeCutSideData RS)

/-- The canonically deleted vertex set complementary to the retained cap
side. -/
def deletedComplement : Finset V :=
  Finset.univ \ data.side

theorem keep_eq_deletedRegionKeep_deletedComplement :
    data.keep =
      GoertzelV24DeletedRegionRotationSplice.deletedRegionKeep
        data.deletedComplement := by
  funext vertex
  apply propext
  simp [keep, deletedComplement,
    GoertzelV24DeletedRegionRotationSplice.deletedRegionKeep]

theorem planarOrdered_keep_eq_deletedRegionKeep_deletedComplement
    (htwoSided : GoertzelV24OrbitFaceTwoSided.OrbitFacesTwoSided RS) :
    (data.planarOrdered htwoSided).keep =
      GoertzelV24DeletedRegionRotationSplice.deletedRegionKeep
        data.deletedComplement := by
  rw [show (data.planarOrdered htwoSided).keep = data.keep by rfl]
  exact data.keep_eq_deletedRegionKeep_deletedComplement

/-- The cap carrier contains two darts per retained internal edge and six
darts on its three new spokes. -/
theorem card_capDart_eq_twice_internalEdge_add_six :
    Fintype.card data.CapDart =
      2 * Fintype.card (RetainedInternalEdge RS data.keep) + 6 := by
  have hinternal := card_internalDart_eq_twice_retainedInternalEdge
    RS data.keep
  have hboundary : Fintype.card (BoundaryDart RS data.keep) = 3 := by
    simpa using Fintype.card_congr data.crossingBoundaryDartEquiv.symm
  change Fintype.card
      (InternalDart RS data.keep ⊕ (BoundaryDart RS data.keep ⊕ Fin 3)) = _
  rw [Fintype.card_sum, Fintype.card_sum]
  simp only [Fintype.card_fin]
  omega

/-- Hence the honest cap has the retained internal edges plus its three
spokes. -/
theorem card_capRotationSystem_edges :
    Fintype.card data.capRewiredDartSystem.Edge =
      Fintype.card (RetainedInternalEdge RS data.keep) + 3 := by
  have hdarts := data.capRotationSystem.card_darts_eq_twice_card_edges
  have hcapDarts := data.card_capDart_eq_twice_internalEdge_add_six
  change Fintype.card data.CapDart =
    2 * Fintype.card data.capRewiredDartSystem.Edge at hdarts
  omega

/-- The cap vertex carrier is the retained side plus one new vertex. -/
theorem card_capVertex :
    Fintype.card data.CapVertex =
      Fintype.card (RetainedVertex data.keep) + 1 := by
  change Fintype.card (RetainedVertex data.keep ⊕ Unit) = _
  simp

/-- The exact connected-side cycle-rank equation is the sole Euler input
needed after the planar cap order has been chosen. -/
theorem planarOrdered_cap_sphericalCubicMapData_of_faceRank
    (hCubic : RS.IsCubic)
    (htwoSided : GoertzelV24OrbitFaceTwoSided.OrbitFacesTwoSided RS)
    (hfaceRank :
      Fintype.card (AmbientRetainedFaceOrbit RS
          (data.planarOrdered htwoSided).keep) +
        Fintype.card
          (RetainedVertex (data.planarOrdered htwoSided).keep) =
      Fintype.card (RetainedInternalEdge RS
          (data.planarOrdered htwoSided).keep) + 1) :
    GoertzelV24CurvatureScope.SphericalCubicMapData
      (data.planarOrdered htwoSided).capRotationSystem where
  cubic := (data.planarOrdered htwoSided).capRotationSystem_isCubic hCubic
  euler := by
    have hvertices := (data.planarOrdered htwoSided).card_capVertex
    have hedges :=
      (data.planarOrdered htwoSided).card_capRotationSystem_edges
    have hfaces :=
      data.card_planarOrdered_cap_faceCycleLengths_eq_three_add_ambient
        htwoSided
    have hverticesInt :
        (Fintype.card (data.planarOrdered htwoSided).CapVertex : Int) =
          Fintype.card
            (RetainedVertex (data.planarOrdered htwoSided).keep) + 1 := by
      exact_mod_cast hvertices
    have hedgesInt :
        (Fintype.card
            (data.planarOrdered htwoSided).capRewiredDartSystem.Edge : Int) =
          Fintype.card (RetainedInternalEdge RS
            (data.planarOrdered htwoSided).keep) + 3 := by
      exact_mod_cast hedges
    have hfacesInt :
        ((GoertzelV24CurvatureScope.faceCycleLengths
            (data.planarOrdered htwoSided).capRotationSystem).card : Int) =
          3 + Fintype.card (AmbientRetainedFaceOrbit RS
            (data.planarOrdered htwoSided).keep) := by
      exact_mod_cast hfaces
    have hfaceRankInt :
        (Fintype.card (AmbientRetainedFaceOrbit RS
            (data.planarOrdered htwoSided).keep) : Int) +
          Fintype.card
            (RetainedVertex (data.planarOrdered htwoSided).keep) =
        Fintype.card (RetainedInternalEdge RS
            (data.planarOrdered htwoSided).keep) + 1 := by
      exact_mod_cast hfaceRank
    omega

variable {G : SimpleGraph V} [DecidableRel G.Adj]

local instance graphEdgeSetFintype : Fintype G.edgeSet :=
  SimpleGraph.fintypeEdgeSet G

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- For a graph-backed spherical bond, connectedness of both induced sides
discharges the cap's local face-rank equation. -/
theorem planarOrdered_faceRank_of_planarBond
    (rotation : SimpleGraphDartRotation.Data G)
    (deleted : Finset V)
    (sideData : ThreeEdgeCutSideData rotation.toRotationSystem)
    (hsphere : OrbitSphericalCubicMapData rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided rotation.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic rotation.toRotationSystem)
    (hretainedConnected :
      (G.induce {vertex |
        GoertzelV24DeletedRegionRotationSplice.deletedRegionKeep
          deleted vertex}).Connected)
    (hdeletedConnected :
      (G.induce {vertex |
        ¬ GoertzelV24DeletedRegionRotationSplice.deletedRegionKeep
          deleted vertex}).Connected)
    (hkeep : (sideData.planarOrdered htwoSided).keep =
      GoertzelV24DeletedRegionRotationSplice.deletedRegionKeep deleted) :
    Fintype.card (AmbientRetainedFaceOrbit rotation.toRotationSystem
        (sideData.planarOrdered htwoSided).keep) +
      Fintype.card
        (RetainedVertex (sideData.planarOrdered htwoSided).keep) =
    Fintype.card (RetainedInternalEdge rotation.toRotationSystem
        (sideData.planarOrdered htwoSided).keep) + 1 := by
  have hranks := planarBond_exact_sideRanks_and_transitionCount
    rotation deleted hsphere htwoSided hconnected hrotation
      hretainedConnected hdeletedConnected
  have hrank := hranks.1
  rw [← hkeep] at hrank
  have hambient := card_ambientRetainedFaceOrbit_eq_allOnSide
    rotation.toRotationSystem (sideData.planarOrdered htwoSided).keep
  have hvertices :
      sideVertexCount (sideData.planarOrdered htwoSided).keep =
        Fintype.card
          (RetainedVertex (sideData.planarOrdered htwoSided).keep) := by
    exact sideVertexCount_eq_card_sideVertex _
  have hedges := card_retainedInternalEdge_eq_allOnSide rotation
    (sideData.planarOrdered htwoSided).keep
  omega

/-- Therefore each planar-ordered side cap of a connected graph-backed
spherical bond is itself an honest spherical cubic rotation system. -/
theorem planarOrdered_cap_sphericalCubicMapData_of_planarBond
    (rotation : SimpleGraphDartRotation.Data G)
    (deleted : Finset V)
    (sideData : ThreeEdgeCutSideData rotation.toRotationSystem)
    (hsphere : OrbitSphericalCubicMapData rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided rotation.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic rotation.toRotationSystem)
    (hretainedConnected :
      (G.induce {vertex |
        GoertzelV24DeletedRegionRotationSplice.deletedRegionKeep
          deleted vertex}).Connected)
    (hdeletedConnected :
      (G.induce {vertex |
        ¬ GoertzelV24DeletedRegionRotationSplice.deletedRegionKeep
          deleted vertex}).Connected)
    (hkeep : (sideData.planarOrdered htwoSided).keep =
      GoertzelV24DeletedRegionRotationSplice.deletedRegionKeep deleted) :
    GoertzelV24CurvatureScope.SphericalCubicMapData
      (sideData.planarOrdered htwoSided).capRotationSystem := by
  apply sideData.planarOrdered_cap_sphericalCubicMapData_of_faceRank
    hsphere.cubic htwoSided
  exact planarOrdered_faceRank_of_planarBond rotation deleted sideData
    hsphere htwoSided hconnected hrotation hretainedConnected
      hdeletedConnected hkeep

/-- Quotient-face form of the same spherical cap theorem. -/
def planarOrdered_cap_orbitSphericalCubicMapData_of_planarBond
    (rotation : SimpleGraphDartRotation.Data G)
    (deleted : Finset V)
    (sideData : ThreeEdgeCutSideData rotation.toRotationSystem)
    (hsphere : OrbitSphericalCubicMapData rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided rotation.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic rotation.toRotationSystem)
    (hretainedConnected :
      (G.induce {vertex |
        GoertzelV24DeletedRegionRotationSplice.deletedRegionKeep
          deleted vertex}).Connected)
    (hdeletedConnected :
      (G.induce {vertex |
        ¬ GoertzelV24DeletedRegionRotationSplice.deletedRegionKeep
          deleted vertex}).Connected)
    (hkeep : (sideData.planarOrdered htwoSided).keep =
      GoertzelV24DeletedRegionRotationSplice.deletedRegionKeep deleted) :
    OrbitSphericalCubicMapData
      (sideData.planarOrdered htwoSided).capRotationSystem :=
  OrbitSphericalCubicMapData.ofSphericalCubicMapData _
    (planarOrdered_cap_sphericalCubicMapData_of_planarBond
      rotation deleted sideData hsphere htwoSided hconnected hrotation
      hretainedConnected hdeletedConnected hkeep)

/-- Canonical-complement form: no predicate-identification premise remains. -/
def planarOrdered_cap_orbitSphericalCubicMapData
    (rotation : SimpleGraphDartRotation.Data G)
    (sideData : ThreeEdgeCutSideData rotation.toRotationSystem)
    (hsphere : OrbitSphericalCubicMapData rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided rotation.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic rotation.toRotationSystem)
    (hretainedConnected :
      (G.induce {vertex | sideData.keep vertex}).Connected)
    (hdeletedConnected :
      (G.induce {vertex | ¬ sideData.keep vertex}).Connected) :
    OrbitSphericalCubicMapData
      (sideData.planarOrdered htwoSided).capRotationSystem := by
  let deleted := sideData.deletedComplement
  have hkeep :=
    sideData.planarOrdered_keep_eq_deletedRegionKeep_deletedComplement
      htwoSided
  have hretained :
      (G.induce {vertex |
        GoertzelV24DeletedRegionRotationSplice.deletedRegionKeep
          deleted vertex}).Connected := by
    rw [← hkeep]
    simpa only [planarOrdered, reindex_keep] using hretainedConnected
  have hdeleted :
      (G.induce {vertex |
        ¬ GoertzelV24DeletedRegionRotationSplice.deletedRegionKeep
          deleted vertex}).Connected := by
    rw [← hkeep]
    simpa only [planarOrdered, reindex_keep] using hdeletedConnected
  exact planarOrdered_cap_orbitSphericalCubicMapData_of_planarBond
    rotation deleted sideData hsphere htwoSided hconnected hrotation
      hretained hdeleted hkeep

/-- An exact cyclic three-edge cut in a cyclically three-edge-connected
ambient graph automatically supplies both connected-side premises. -/
def planarOrdered_cap_orbitSphericalCubicMapData_of_exactCyclicThreeCut
    (rotation : SimpleGraphDartRotation.Data G)
    (sideData : ThreeEdgeCutSideData rotation.toRotationSystem)
    (cut : SmallCyclicEdgeCut G)
    (hside : sideData.keep = cut.side)
    (hcard : cut.edgeCut.card = 3)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 3)
    (hsphere : OrbitSphericalCubicMapData rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided rotation.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic rotation.toRotationSystem) :
    OrbitSphericalCubicMapData
      (sideData.planarOrdered htwoSided).capRotationSystem := by
  have hsides := induce_both_sides_connected_of_card_eq_three
    hconnected hcyclic cut hcard
  have hretained :
      (G.induce {vertex | sideData.keep vertex}).Connected := by
    rw [hside]
    rw [show ({vertex | cut.side vertex} : Set V) = cut.side by rfl]
    exact hsides.1
  have hdeleted :
      (G.induce {vertex | ¬ sideData.keep vertex}).Connected := by
    rw [hside]
    rw [show ({vertex | ¬ cut.side vertex} : Set V) =
      (fun vertex => ¬ cut.side vertex) by rfl]
    exact hsides.2
  exact sideData.planarOrdered_cap_orbitSphericalCubicMapData rotation
    hsphere htwoSided hconnected hrotation hretained hdeleted

end ThreeEdgeCutSideData

end RotationSystem

end

end Mettapedia.GraphTheory.FourColor
