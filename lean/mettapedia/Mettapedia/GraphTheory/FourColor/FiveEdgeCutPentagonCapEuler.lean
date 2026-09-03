import Mettapedia.GraphTheory.FourColor.FiveEdgeCutPentagonCapUntouchedFaces
import Mettapedia.GraphTheory.FourColor.GoertzelV24ThreeEdgeCutCapEuler
import Mettapedia.GraphTheory.FourColor.GoertzelV24PlanarBondSpliceEuler

/-!
# Euler data of the pentagon-capped shore

The pentagon cap adds five vertices, ten edges, and six faces to the
retained shore, so its Euler characteristic is inherited: with the exact
planar bond's side-rank equation, the capped shore is a spherical cubic
map.
-/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24CurvatureScope
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FaceDualConnectedness
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24PlanarBondBoundaryOrder
open GoertzelV24PlanarBondSpliceEuler
open GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24RetainedSpliceAmbientFaceCount
open GoertzelV24RetainedSpliceEdgeCount
open GoertzelV24RetainedSpliceFaceCount
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RotationCutDartDecomposition

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

namespace FiveEdgeCutPentagonCapData

variable {RS : RotationSystem V E} (data : FiveEdgeCutPentagonCapData RS)

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

/-- The cap carrier contains two darts per retained internal edge, the ten
pentagon cycle darts, the five boundary darts, and the five spokes. -/
theorem card_capDart_eq_twice_internalEdge_add_twenty :
    Fintype.card data.CapDart =
      2 * Fintype.card (RetainedInternalEdge RS data.keep) + 20 := by
  have hinternal := card_internalDart_eq_twice_retainedInternalEdge
    RS data.keep
  change Fintype.card
      ((InternalDart RS data.keep ⊕ (Fin 5 × Bool)) ⊕ (Fin 5 ⊕ Fin 5)) = _
  rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_sum,
    Fintype.card_prod]
  simp only [Fintype.card_fin, Fintype.card_bool]
  omega

/-- Hence the pentagon-capped shore has the retained internal edges, the
five cycle edges, and the five spokes. -/
theorem card_capRotationSystem_edges :
    Fintype.card data.capRewiredDartSystem.Edge =
      Fintype.card (RetainedInternalEdge RS data.keep) + 10 := by
  have hdarts := data.capRotationSystem.card_darts_eq_twice_card_edges
  have hcapDarts := data.card_capDart_eq_twice_internalEdge_add_twenty
  change Fintype.card data.CapDart =
    2 * Fintype.card data.capRewiredDartSystem.Edge at hdarts
  omega

/-- The cap vertex carrier is the retained side plus five new vertices. -/
theorem card_capVertex :
    Fintype.card data.CapVertex =
      Fintype.card (RetainedVertex data.keep) + 5 := by
  change Fintype.card (RetainedVertex data.keep ⊕ Fin 5) = _
  simp

/-- The exact connected-side cycle-rank equation is the sole Euler input
needed once the crossing enumeration follows the facial boundary order. -/
theorem cap_sphericalCubicMapData_of_faceRank
    (hCubic : RS.IsCubic)
    (hsucc : retainedRegionBoundarySuccessor RS data.keep =
      data.crossingBoundaryDartEquiv.permCongr (finRotate 5)⁻¹)
    (hfaceRank :
      Fintype.card (AmbientRetainedFaceOrbit RS data.keep) +
        Fintype.card (RetainedVertex data.keep) =
      Fintype.card (RetainedInternalEdge RS data.keep) + 1) :
    SphericalCubicMapData data.capRotationSystem where
  cubic := data.capRotationSystem_isCubic hCubic
  euler := by
    have hvertices := data.card_capVertex
    have hedges := data.card_capRotationSystem_edges
    have hfaces := data.card_cap_faceCycleLengths_eq_six_add_ambient hsucc
    have hverticesInt :
        (Fintype.card data.CapVertex : Int) =
          Fintype.card (RetainedVertex data.keep) + 5 := by
      exact_mod_cast hvertices
    have hedgesInt :
        (Fintype.card data.capRewiredDartSystem.Edge : Int) =
          Fintype.card (RetainedInternalEdge RS data.keep) + 10 := by
      exact_mod_cast hedges
    have hfacesInt :
        ((faceCycleLengths data.capRotationSystem).card : Int) =
          6 + Fintype.card (AmbientRetainedFaceOrbit RS data.keep) := by
      exact_mod_cast hfaces
    have hfaceRankInt :
        (Fintype.card (AmbientRetainedFaceOrbit RS data.keep) : Int) +
          Fintype.card (RetainedVertex data.keep) =
        Fintype.card (RetainedInternalEdge RS data.keep) + 1 := by
      exact_mod_cast hfaceRank
    omega

variable {G : SimpleGraph V} [DecidableRel G.Adj]

local instance graphEdgeSetFintype : Fintype G.edgeSet :=
  SimpleGraph.fintypeEdgeSet G

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- For a graph-backed spherical bond, connectedness of both induced sides
discharges the cap's local face-rank equation. -/
theorem faceRank_of_planarBond
    (rotation : SimpleGraphDartRotation.Data G)
    (deleted : Finset V)
    (capData : FiveEdgeCutPentagonCapData rotation.toRotationSystem)
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
    (hkeep : capData.keep =
      GoertzelV24DeletedRegionRotationSplice.deletedRegionKeep deleted) :
    Fintype.card (AmbientRetainedFaceOrbit rotation.toRotationSystem
        capData.keep) +
      Fintype.card (RetainedVertex capData.keep) =
    Fintype.card (RetainedInternalEdge rotation.toRotationSystem
        capData.keep) + 1 := by
  have hranks := planarBond_exact_sideRanks_and_transitionCount
    rotation deleted hsphere htwoSided hconnected hrotation
      hretainedConnected hdeletedConnected
  have hrank := hranks.1
  rw [← hkeep] at hrank
  have hambient := card_ambientRetainedFaceOrbit_eq_allOnSide
    rotation.toRotationSystem capData.keep
  have hvertices :
      sideVertexCount capData.keep =
        Fintype.card (RetainedVertex capData.keep) := by
    exact sideVertexCount_eq_card_sideVertex _
  have hedges := card_retainedInternalEdge_eq_allOnSide rotation
    capData.keep
  omega

/-- Each pentagon-capped side of a connected graph-backed spherical bond
is an honest spherical cubic rotation system. -/
theorem cap_sphericalCubicMapData_of_planarBond
    (rotation : SimpleGraphDartRotation.Data G)
    (deleted : Finset V)
    (capData : FiveEdgeCutPentagonCapData rotation.toRotationSystem)
    (hsphere : OrbitSphericalCubicMapData rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided rotation.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic rotation.toRotationSystem)
    (hsucc : retainedRegionBoundarySuccessor rotation.toRotationSystem
        capData.keep =
      capData.crossingBoundaryDartEquiv.permCongr (finRotate 5)⁻¹)
    (hretainedConnected :
      (G.induce {vertex |
        GoertzelV24DeletedRegionRotationSplice.deletedRegionKeep
          deleted vertex}).Connected)
    (hdeletedConnected :
      (G.induce {vertex |
        ¬ GoertzelV24DeletedRegionRotationSplice.deletedRegionKeep
          deleted vertex}).Connected)
    (hkeep : capData.keep =
      GoertzelV24DeletedRegionRotationSplice.deletedRegionKeep deleted) :
    SphericalCubicMapData capData.capRotationSystem := by
  apply capData.cap_sphericalCubicMapData_of_faceRank
    hsphere.cubic hsucc
  exact faceRank_of_planarBond rotation deleted capData
    hsphere htwoSided hconnected hrotation hretainedConnected
      hdeletedConnected hkeep

/-- Quotient-face form of the spherical pentagon-cap theorem. -/
def cap_orbitSphericalCubicMapData_of_planarBond
    (rotation : SimpleGraphDartRotation.Data G)
    (deleted : Finset V)
    (capData : FiveEdgeCutPentagonCapData rotation.toRotationSystem)
    (hsphere : OrbitSphericalCubicMapData rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided rotation.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic rotation.toRotationSystem)
    (hsucc : retainedRegionBoundarySuccessor rotation.toRotationSystem
        capData.keep =
      capData.crossingBoundaryDartEquiv.permCongr (finRotate 5)⁻¹)
    (hretainedConnected :
      (G.induce {vertex |
        GoertzelV24DeletedRegionRotationSplice.deletedRegionKeep
          deleted vertex}).Connected)
    (hdeletedConnected :
      (G.induce {vertex |
        ¬ GoertzelV24DeletedRegionRotationSplice.deletedRegionKeep
          deleted vertex}).Connected)
    (hkeep : capData.keep =
      GoertzelV24DeletedRegionRotationSplice.deletedRegionKeep deleted) :
    OrbitSphericalCubicMapData capData.capRotationSystem :=
  OrbitSphericalCubicMapData.ofSphericalCubicMapData _
    (cap_sphericalCubicMapData_of_planarBond rotation deleted capData
      hsphere htwoSided hconnected hrotation hsucc hretainedConnected
      hdeletedConnected hkeep)

end FiveEdgeCutPentagonCapData

end

end Mettapedia.GraphTheory.FourColor
