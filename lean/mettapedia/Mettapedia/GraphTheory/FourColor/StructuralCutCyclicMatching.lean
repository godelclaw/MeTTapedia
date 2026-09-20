import Mettapedia.GraphTheory.FourColor.GoertzelV24MajorityShorePhysicalReplacement
import Mettapedia.GraphTheory.FourColor.GoertzelV24CyclicBondBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24ConnectedShoreLiteralNode

/-!
# Matching the cyclic borders of two physical planar bonds

For the structural part of a shore replacement, equality of the *entire*
normalized seam state is stronger than necessary. Two full boundary cycles of
the same size admit an orientation-reversing matching. The colour-language
condition remains separate; this file makes no assertion about it.
-/

namespace Mettapedia.GraphTheory.FourColor.StructuralCutCyclicMatching

open Equiv Equiv.Perm
open GoertzelV24SeamExchange
open GoertzelV24CyclicBondBoundary.CyclicBondBoundaryData
open GoertzelV24CanonicalHubCyclicity
open GoertzelV24CanonicalHubClosure
open GoertzelV24CompositeSeamMultigraph
open GoertzelV24CompositeSphericity
open GoertzelV24ComplementaryShoreBoundaryOrder
open GoertzelV24ConnectedEdgeShoreMajority
open GoertzelV24ConnectedEdgeShoreStructuralData
open GoertzelV24ConnectedShoreLiteralNode
open GoertzelV24ConnectedMapEulerBound
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FaceDualConnectedness
open GoertzelV24OpenTangleComposition
open GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24MajorityShoreNormalizedState
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationMultigraphAdapter
open GoertzelV24SimpleGraphFaceDualConnectedness
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24VertexSideOpenTangle
open SimpleGraphDartRotation

universe u

variable {L R : Type u} [Fintype L] [DecidableEq L]
  [Fintype R] [DecidableEq R]

/-- A full cycle has no fixed points, stated as support equality. -/
private theorem support_eq_univ_of_forall_mem
    (ρ : Equiv.Perm L) (hfull : ∀ x : L, x ∈ ρ.support) :
    ρ.support = Finset.univ := by
  ext x
  simp [hfull x]

/-- Any two full cycles on equally sized finite carriers can be sewn in
opposite orientation. This is a genuine existence theorem: no seam state or
colour support is supplied as an input. -/
theorem exists_orientationReversing_of_full_cycles
    (ρL : Equiv.Perm L) (ρR : Equiv.Perm R)
    (hcard : Fintype.card L = Fintype.card R)
    (hcycleL : ρL.IsCycle) (hcycleR : ρR.IsCycle)
    (hfullL : ∀ x : L, x ∈ ρL.support)
    (hfullR : ∀ x : R, x ∈ ρR.support) :
    ∃ matching : L ≃ R, OrientationReversing matching ρL ρR := by
  let e : L ≃ R := Fintype.equivOfCardEq hcard
  let σ : Equiv.Perm R := e.permCongr ρL⁻¹
  have hσcycle : σ.IsCycle := isCycle_permCongr e ρL⁻¹ hcycleL.inv
  have hσfull : ∀ y : R, y ∈ σ.support := by
    intro y
    rw [Equiv.Perm.mem_support]
    change e (ρL⁻¹ (e.symm y)) ≠ y
    intro heq
    have hfixed : ρL⁻¹ (e.symm y) = e.symm y := e.injective (by
      simpa only [e.apply_symm_apply] using heq)
    have horig : ρL (e.symm y) = e.symm y := by
      simpa using (congrArg ρL hfixed).symm
    exact (Equiv.Perm.mem_support.mp (hfullL (e.symm y))) horig
  have hsupport : σ.support.card = ρR.support.card := by
    rw [support_eq_univ_of_forall_mem σ hσfull,
      support_eq_univ_of_forall_mem ρR hfullR]
  obtain ⟨π, hπ⟩ := (isConj_iff.mp (hσcycle.isConj hcycleR hsupport))
  refine ⟨e.trans π, ?_⟩
  intro x
  have hcomm : ρR (π (e x)) = π (σ (e x)) := by
    rw [← hπ]
    simp [Equiv.Perm.mul_apply]
  simpa [σ, Equiv.permCongr_apply] using hcomm

/-- One orbit and a nontrivial cycle mean that every point is moved. -/
theorem full_support_of_one_orbit_cycle
    (ρ : Equiv.Perm L) (hcount : GoertzelV24PermutationOrbitSurgery.orbitCount ρ = 1)
    (hcycle : ρ.IsCycle) :
    ∀ x : L, x ∈ ρ.support := by
  obtain ⟨root, hroot, _⟩ := hcycle
  intro x
  have hsame := sameCycle_all_of_orbitCount_eq_one ρ hcount root x
  exact hsame.mem_support_iff.mp (Equiv.Perm.mem_support.mpr hroot)

section Physical

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]

local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

omit [G.LocallyFinite] in
/-- Two literal connected planar bonds with the same number of ports admit
an orientation-reversing seam. The resulting physical composition is again a
connected, bridgeless, spherical cubic map. No colouring-state equality is
assumed or inferred. -/
theorem exists_structural_splice_of_two_planar_bonds
    (rotation : Data G)
    (ambient : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (deletedL deletedR : Finset V)
    (outerL : RetainedDart rotation.toRotationSystem (deletedRegionKeep deletedL))
    (outerR : RetainedDart rotation.toRotationSystem (deletedRegionKeep deletedR))
    (hretainedL :
      (G.induce {v | deletedRegionKeep deletedL v}).Connected)
    (hdeletedL :
      (G.induce {v | ¬ deletedRegionKeep deletedL v}).Connected)
    (hretainedR :
      (G.induce {v | deletedRegionKeep deletedR v}).Connected)
    (hdeletedR :
      (G.induce {v | ¬ deletedRegionKeep deletedR v}).Connected)
    (firstL secondL : BoundaryDart rotation.toRotationSystem
      (deletedRegionKeep deletedL)) (hneL : firstL ≠ secondL)
    (firstR secondR : BoundaryDart rotation.toRotationSystem
      (deletedRegionKeep deletedR)) (hneR : firstR ≠ secondR)
    (hcard :
      Fintype.card (BoundaryDart rotation.toRotationSystem
        (deletedRegionKeep deletedL)) =
      Fintype.card (BoundaryDart rotation.toRotationSystem
        (deletedRegionKeep deletedR))) :
    ∃ matching : BoundaryDart rotation.toRotationSystem
        (deletedRegionKeep deletedL) ≃
        BoundaryDart rotation.toRotationSystem
          (deletedRegionKeep deletedR),
      OrientationReversing matching
        (canonicalHubRotation rotation.toRotationSystem
          (deletedRegionKeep deletedL))
        (canonicalHubRotation rotation.toRotationSystem
          (deletedRegionKeep deletedR)) ∧
      BridgelessSphericalCubicMapData
        ((ofVertexSide rotation.toRotationSystem
          (deletedRegionKeep deletedL) outerL).composeRotationSystem
          (ofVertexSide rotation.toRotationSystem
            (deletedRegionKeep deletedR) outerR) matching) := by
  let RS := rotation.toRotationSystem
  let keepL := deletedRegionKeep deletedL
  let keepR := deletedRegionKeep deletedR
  let TL := ofVertexSide RS keepL outerL
  let TR := ofVertexSide RS keepR outerR
  let ρL := canonicalHubRotation RS keepL
  let ρR := canonicalHubRotation RS keepR
  have hgraphConnected : G.Connected := by
    simpa only [rotationPrimalGraph_toRotationSystem_eq] using ambient.primalConnected
  have hdiscL : CanonicalHubDiscData TL ρL :=
    canonicalHubDiscData_of_planarBond rotation deletedL outerL
      ambient.spherical htwo hgraphConnected ambient.vertexRotationCyclic
      hretainedL hdeletedL firstL secondL hneL
  have hdiscR : CanonicalHubDiscData TR ρR :=
    canonicalHubDiscData_of_planarBond rotation deletedR outerR
      ambient.spherical htwo hgraphConnected ambient.vertexRotationCyclic
      hretainedR hdeletedR firstR secondR hneR
  have hsideL : (sideMultigraph TL).Connected := by
    apply sideMultigraph_connected_of_induce_connected
    simpa [RS, keepL, rotationPrimalGraph_toRotationSystem_eq] using hretainedL
  have hsideR : (sideMultigraph TR).Connected := by
    apply sideMultigraph_connected_of_induce_connected
    simpa [RS, keepR, rotationPrimalGraph_toRotationSystem_eq] using hretainedR
  have hcountL : GoertzelV24PermutationOrbitSurgery.orbitCount ρL = 1 :=
    orbitCount_hubRotation_eq_one_of_closedSideSpherical TL ρL hsideL
      (openRotationCyclic_ofVertexSide RS keepL outerL
        ambient.vertexRotationCyclic)
      (openIsCubic_ofVertexSide RS keepL outerL ambient.spherical.cubic)
      firstL hdiscL.closedSpherical
  have hcountR : GoertzelV24PermutationOrbitSurgery.orbitCount ρR = 1 :=
    orbitCount_hubRotation_eq_one_of_closedSideSpherical TR ρR hsideR
      (openRotationCyclic_ofVertexSide RS keepR outerR
        ambient.vertexRotationCyclic)
      (openIsCubic_ofVertexSide RS keepR outerR ambient.spherical.cubic)
      firstR hdiscR.closedSpherical
  obtain ⟨matching, hrev⟩ := exists_orientationReversing_of_full_cycles
    ρL ρR hcard hdiscL.hubCycle hdiscR.hubCycle
      (full_support_of_one_orbit_cycle ρL hcountL hdiscL.hubCycle)
      (full_support_of_one_orbit_cycle ρR hcountR hdiscR.hubCycle)
  refine ⟨matching, hrev, ?_⟩
  exact bridgelessSphericalCubicMapData_ofVertexSides
    RS keepL keepR outerL outerR matching ρL ρR
    (by simpa [RS, keepL, rotationPrimalGraph_toRotationSystem_eq] using hretainedL)
    (by simpa [RS, keepR, rotationPrimalGraph_toRotationSystem_eq] using hretainedR)
    ((bridgeless_iff_edgeBridgeFree (RS := RS)).2 ambient.edgeBridgeFree)
    firstL secondL hneL ambient.spherical.cubic ambient.vertexRotationCyclic
    hdiscL.facesDistinct hdiscR.facesDistinct hrev
    hdiscL.closedSpherical hdiscR.closedSpherical


omit [G.LocallyFinite] in
/-- The live replacement geometry accepts *any* orientation-reversing
matching between the old majority exterior and new majority interior. The
planar connected-bond hypotheses are sufficient to prove the sewn map remains
in the bridgeless spherical cubic class; colour compatibility is deliberately
not smuggled into this geometric theorem. -/
theorem structural_majority_replacement_of_orientationReversing
    (rotation : Data G)
    (ambient : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (oldShore newShore : Finset G.edgeSet)
    (outsideOuter : RetainedDart rotation.toRotationSystem
      (majorityDeletedKeep G oldShore))
    (newInnerOuter : RetainedDart rotation.toRotationSystem
      (majorityRetainedKeep G newShore))
    (hOldInside :
      (G.induce {v | majorityRetainedKeep G oldShore v}).Connected)
    (hOldOutside :
      (G.induce {v | majorityDeletedKeep G oldShore v}).Connected)
    (hNewInside :
      (G.induce {v | majorityRetainedKeep G newShore v}).Connected)
    (hNewOutside :
      (G.induce {v | majorityDeletedKeep G newShore v}).Connected)
    (matching : BoundaryDart rotation.toRotationSystem
      (majorityDeletedKeep G oldShore) ≃
      BoundaryDart rotation.toRotationSystem
        (majorityRetainedKeep G newShore))
    (hrev : OrientationReversing matching
      (canonicalHubRotation rotation.toRotationSystem
        (majorityDeletedKeep G oldShore))
      (canonicalHubRotation rotation.toRotationSystem
        (majorityRetainedKeep G newShore)))
    (first second : BoundaryDart rotation.toRotationSystem
      (majorityDeletedKeep G oldShore)) (hne : first ≠ second) :
    BridgelessSphericalCubicMapData
      ((GoertzelV24MajorityShorePhysicalReplacement.outsideTangle
        rotation oldShore outsideOuter).composeRotationSystem
        (GoertzelV24MajorityShoreNormalizedState.innerTangle
          rotation newShore newInnerOuter) matching) := by
  let RS := rotation.toRotationSystem
  have hgraphConnected : G.Connected := by
    simpa only [rotationPrimalGraph_toRotationSystem_eq] using ambient.primalConnected
  have hOldOutsideRS :
      ((rotationPrimalGraph RS).induce
        {v | majorityDeletedKeep G oldShore v}).Connected := by
    simpa [RS, rotationPrimalGraph_toRotationSystem_eq] using hOldOutside
  have hNewInsideRS :
      ((rotationPrimalGraph RS).induce
        {v | majorityRetainedKeep G newShore v}).Connected := by
    simpa [RS, rotationPrimalGraph_toRotationSystem_eq] using hNewInside
  exact bridgelessSphericalCubicMapData_ofVertexSides
    RS (majorityDeletedKeep G oldShore)
      (majorityRetainedKeep G newShore)
    outsideOuter newInnerOuter matching
    (canonicalHubRotation RS (majorityDeletedKeep G oldShore))
    (canonicalHubRotation RS (majorityRetainedKeep G newShore))
    hOldOutsideRS hNewInsideRS
    ((bridgeless_iff_edgeBridgeFree (RS := RS)).2 ambient.edgeBridgeFree)
    first second hne ambient.spherical.cubic ambient.vertexRotationCyclic
    (hubFacesDistinct_canonical RS
      (majorityDeletedKeep G oldShore) outsideOuter)
    (hubFacesDistinct_canonical RS
      (majorityRetainedKeep G newShore) newInnerOuter)
    hrev
    (closedSideSpherical_canonical_deletedSide_of_planarBond
      rotation (majorityDeletedVertices G oldShore) outsideOuter
      ambient.spherical htwo hgraphConnected ambient.vertexRotationCyclic
      hOldInside hOldOutside)
    (closedSideSpherical_canonical_of_planarBond
      rotation (majorityDeletedVertices G newShore) newInnerOuter
      ambient.spherical htwo hgraphConnected ambient.vertexRotationCyclic
      hNewInside hNewOutside)

omit [G.LocallyFinite] in
/-- Equal-width physical majority bonds provide at least one geometrically
valid replacement matching. This removes normalized hub-rotation equality as
an input to *structural* descent, while leaving the actual-exterior colour
test open and explicit. -/
theorem exists_structural_majority_replacement
    (rotation : Data G)
    (ambient : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (oldShore newShore : Finset G.edgeSet)
    (outsideOuter : RetainedDart rotation.toRotationSystem
      (majorityDeletedKeep G oldShore))
    (newInnerOuter : RetainedDart rotation.toRotationSystem
      (majorityRetainedKeep G newShore))
    (hOldInside :
      (G.induce {v | majorityRetainedKeep G oldShore v}).Connected)
    (hOldOutside :
      (G.induce {v | majorityDeletedKeep G oldShore v}).Connected)
    (hNewInside :
      (G.induce {v | majorityRetainedKeep G newShore v}).Connected)
    (hNewOutside :
      (G.induce {v | majorityDeletedKeep G newShore v}).Connected)
    (hwidth : boundaryWidth rotation oldShore =
      boundaryWidth rotation newShore) :
    ∃ matching : BoundaryDart rotation.toRotationSystem
        (majorityDeletedKeep G oldShore) ≃
        BoundaryDart rotation.toRotationSystem
          (majorityRetainedKeep G newShore),
      OrientationReversing matching
        (canonicalHubRotation rotation.toRotationSystem
          (majorityDeletedKeep G oldShore))
        (canonicalHubRotation rotation.toRotationSystem
          (majorityRetainedKeep G newShore)) ∧
      BridgelessSphericalCubicMapData
        ((GoertzelV24MajorityShorePhysicalReplacement.outsideTangle
          rotation oldShore outsideOuter).composeRotationSystem
          (innerTangle rotation newShore newInnerOuter) matching) := by
  let RS := rotation.toRotationSystem
  let keepL := majorityDeletedKeep G oldShore
  let keepR := majorityRetainedKeep G newShore
  let TL := GoertzelV24MajorityShorePhysicalReplacement.outsideTangle
    rotation oldShore outsideOuter
  let TR := innerTangle rotation newShore newInnerOuter
  let ρL := canonicalHubRotation RS keepL
  let ρR := canonicalHubRotation RS keepR
  have hgraphConnected : G.Connected := by
    simpa only [rotationPrimalGraph_toRotationSystem_eq] using ambient.primalConnected
  have hsideL : (sideMultigraph TL).Connected := by
    apply sideMultigraph_connected_of_induce_connected
    simpa [RS, keepL, rotationPrimalGraph_toRotationSystem_eq] using hOldOutside
  have hsideR : (sideMultigraph TR).Connected := by
    apply sideMultigraph_connected_of_induce_connected
    simpa [RS, keepR, rotationPrimalGraph_toRotationSystem_eq] using hNewInside
  have hclosedL : ClosedSideSpherical TL ρL :=
    closedSideSpherical_canonical_deletedSide_of_planarBond
      rotation (majorityDeletedVertices G oldShore) outsideOuter
      ambient.spherical htwo hgraphConnected ambient.vertexRotationCyclic
      hOldInside hOldOutside
  have hclosedR : ClosedSideSpherical TR ρR :=
    closedSideSpherical_canonical_of_planarBond
      rotation (majorityDeletedVertices G newShore) newInnerOuter
      ambient.spherical htwo hgraphConnected ambient.vertexRotationCyclic
      hNewInside hNewOutside
  have hcard : Fintype.card (BoundaryDart RS keepL) =
      Fintype.card (BoundaryDart RS keepR) := by
    have hc := Fintype.card_congr
      (complementBoundaryAlphaEquiv RS
        (majorityDeletedVertices G oldShore))
    change boundaryWidth rotation oldShore =
      Fintype.card (BoundaryDart RS keepL) at hc
    exact hc.symm.trans hwidth
  have hcardL : 2 ≤ Fintype.card (BoundaryDart RS keepL) := by
    obtain ⟨⟨inside, hins⟩, _⟩ :=
      (SimpleGraph.connected_iff_exists_forall_reachable _).mp hOldOutside
    obtain ⟨⟨outside, houts⟩, _⟩ :=
      (SimpleGraph.connected_iff_exists_forall_reachable _).mp hOldInside
    exact two_le_card_boundaryDart_of_connected_edgeBridgeFree RS
      ambient.primalConnected ambient.edgeBridgeFree keepL
      ⟨inside, hins⟩ ⟨outside, by simpa [keepL, majorityDeletedKeep_iff,
        majorityRetainedKeep_iff] using houts⟩
  have hcardR : 2 ≤ Fintype.card (BoundaryDart RS keepR) := by
    rw [← hcard]
    exact hcardL
  obtain ⟨firstL, secondL, hneL⟩ :=
    Fintype.exists_pair_of_one_lt_card (by omega :
      1 < Fintype.card (BoundaryDart RS keepL))
  obtain ⟨firstR, secondR, hneR⟩ :=
    Fintype.exists_pair_of_one_lt_card (by omega :
      1 < Fintype.card (BoundaryDart RS keepR))
  have hcountL := orbitCount_hubRotation_eq_one_of_closedSideSpherical
    TL ρL hsideL
    (openRotationCyclic_ofVertexSide RS keepL outsideOuter
      ambient.vertexRotationCyclic)
    (openIsCubic_ofVertexSide RS keepL outsideOuter ambient.spherical.cubic)
    firstL hclosedL
  have hcountR := orbitCount_hubRotation_eq_one_of_closedSideSpherical
    TR ρR hsideR
    (openRotationCyclic_ofVertexSide RS keepR newInnerOuter
      ambient.vertexRotationCyclic)
    (openIsCubic_ofVertexSide RS keepR newInnerOuter ambient.spherical.cubic)
    firstR hclosedR
  have hcycleL := hubRotation_isCycle_of_closedSideSpherical
    TL ρL hsideL
    (openRotationCyclic_ofVertexSide RS keepL outsideOuter
      ambient.vertexRotationCyclic)
    (openIsCubic_ofVertexSide RS keepL outsideOuter ambient.spherical.cubic)
    firstL secondL hneL hclosedL
  have hcycleR := hubRotation_isCycle_of_closedSideSpherical
    TR ρR hsideR
    (openRotationCyclic_ofVertexSide RS keepR newInnerOuter
      ambient.vertexRotationCyclic)
    (openIsCubic_ofVertexSide RS keepR newInnerOuter ambient.spherical.cubic)
    firstR secondR hneR hclosedR
  obtain ⟨matching, hrev⟩ := exists_orientationReversing_of_full_cycles
    ρL ρR hcard hcycleL hcycleR
    (full_support_of_one_orbit_cycle ρL hcountL hcycleL)
    (full_support_of_one_orbit_cycle ρR hcountR hcycleR)
  refine ⟨matching, hrev, ?_⟩
  exact structural_majority_replacement_of_orientationReversing
    rotation ambient htwo oldShore newShore outsideOuter newInnerOuter
    hOldInside hOldOutside hNewInside hNewOutside
    matching hrev firstL secondL hneL

end Physical

end Mettapedia.GraphTheory.FourColor.StructuralCutCyclicMatching
