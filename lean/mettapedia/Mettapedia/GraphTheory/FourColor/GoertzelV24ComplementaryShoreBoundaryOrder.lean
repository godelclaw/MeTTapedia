import Mettapedia.GraphTheory.FourColor.GoertzelV24CanonicalHubCyclicity

/-!
# Complementary literal shores have opposite boundary orders

The planar-bond boundary theorem computes the deleted-side first-return order
on the retained shore's boundary carrier.  The physical seam theorem instead
uses one boundary carrier for each literal shore.  This file supplies the
missing adapter: ambient `alpha` identifies the two boundary carriers, and
under that identification their actual first-return orders are opposite.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ComplementaryShoreBoundaryOrder

open Equiv Equiv.Perm
open GoertzelV24CanonicalHubClosure
open GoertzelV24ComplementaryRegionBoundaryOrder
open GoertzelV24CompositeSphericity
open GoertzelV24CompositeStructuralData
open GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FaceDualConnectedness
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24OpenTangleComposition
open GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24PlanarBondBoundaryOrder
open GoertzelV24PlanarBondSpliceEuler
open GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RotationMultigraphAdapter
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24SeamExchange
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24VertexSideOpenTangle
open SimpleGraphDartRotation

noncomputable section

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- The literal vertex predicate on the deleted shore. -/
abbrev deletedSideKeep (deleted : Finset V) (vertex : V) : Prop :=
  ¬ deletedRegionKeep deleted vertex

/-- Darts retained by the literal deleted shore are the deleted-based darts,
without changing their ambient representative. -/
def deletedSideDartEquiv
    (RS : RotationSystem V E) (deleted : Finset V) :
    RetainedDart RS (deletedSideKeep deleted) ≃
      DeletedBasedDart RS deleted where
  toFun dart := ⟨dart.1, by
    simpa [deletedSideKeep, deletedRegionKeep] using dart.2⟩
  invFun dart := ⟨dart.1, by
    simpa [deletedSideKeep, deletedRegionKeep] using dart.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem deletedSideDartEquiv_val
    (RS : RotationSystem V E) (deleted : Finset V)
    (dart : RetainedDart RS (deletedSideKeep deleted)) :
    (deletedSideDartEquiv RS deleted dart).1 = dart.1 :=
  rfl

@[simp]
theorem deletedSideDartEquiv_symm_val
    (RS : RotationSystem V E) (deleted : Finset V)
    (dart : DeletedBasedDart RS deleted) :
    ((deletedSideDartEquiv RS deleted).symm dart).1 = dart.1 :=
  rfl

/-- The exposed-dart predicates agree under the identity-on-ambient-darts
equivalence. -/
theorem deletedSideDartEquiv_hit_iff
    (RS : RotationSystem V E) (deleted : Finset V)
    (dart : RetainedDart RS (deletedSideKeep deleted)) :
    (¬ deletedSideKeep deleted
        (RS.vertOf (RS.alpha dart.1))) ↔
      IsDeletedBoundaryHalfDart RS deleted
        (deletedSideDartEquiv RS deleted dart) := by
  simp [deletedSideKeep, deletedRegionKeep,
    IsDeletedBoundaryHalfDart]

/-- The capped face permutation on the literal deleted shore is the existing
deleted-region face permutation after the identity-on-darts transport. -/
theorem deletedFacePerm_eq_permCongr_deletedSide
    (RS : RotationSystem V E) (deleted : Finset V) :
    deletedFacePerm RS deleted =
      (deletedSideDartEquiv RS deleted).permCongr
        (retainedCappedFacePerm RS (deletedSideKeep deleted)) := by
  let dartEquiv := deletedSideDartEquiv RS deleted
  have hrho : deletedRho RS deleted =
      dartEquiv.permCongr
        (retainedRho RS (deletedSideKeep deleted)) := by
    apply Equiv.ext
    intro dart
    apply Subtype.ext
    rfl
  have halpha : deletedAlpha RS deleted =
      dartEquiv.permCongr
        (retainedCappedAlpha RS (deletedSideKeep deleted)) := by
    apply Equiv.ext
    intro dart
    rw [Equiv.permCongr_apply]
    apply Subtype.ext
    by_cases hmem : RS.vertOf (RS.alpha dart.1) ∈ deleted
    · have hkeep : deletedSideKeep deleted
          (RS.vertOf (RS.alpha (dartEquiv.symm dart).1)) := by
        dsimp [dartEquiv]
        simpa [deletedSideKeep, deletedRegionKeep] using hmem
      rw [deletedAlpha_apply_internal RS deleted dart hmem]
      calc
        RS.alpha dart.1 =
            RS.alpha (dartEquiv.symm dart).1 := by
          rw [deletedSideDartEquiv_symm_val]
        _ = (retainedCappedAlpha RS (deletedSideKeep deleted)
              (dartEquiv.symm dart)).1 :=
          (retainedCappedAlpha_apply_internal RS _ _ hkeep).symm
        _ = (dartEquiv (retainedCappedAlpha RS
              (deletedSideKeep deleted) (dartEquiv.symm dart))).1 := by
          rfl
    · have hkeepNot : ¬ deletedSideKeep deleted
          (RS.vertOf (RS.alpha (dartEquiv.symm dart).1)) := by
        dsimp [dartEquiv]
        simpa [deletedSideKeep, deletedRegionKeep] using hmem
      rw [deletedAlpha_apply_boundary RS deleted dart hmem,
        retainedCappedAlpha_apply_boundary RS _ _ hkeepNot]
      rfl
  rw [deletedFacePerm, retainedCappedFacePerm, hrho, halpha]
  exact (Equiv.permCongr_mul dartEquiv _ _).symm

/-- Reversing a crossing dart by ambient `alpha` identifies the boundary
carriers of the two complementary literal shores. -/
def complementBoundaryAlphaEquiv
    (RS : RotationSystem V E) (deleted : Finset V) :
    BoundaryDart RS (deletedRegionKeep deleted) ≃
      BoundaryDart RS (deletedSideKeep deleted) :=
  let dartEquiv := deletedSideDartEquiv RS deleted
  let markedEquiv := dartEquiv.subtypeEquiv
    (deletedSideDartEquiv_hit_iff RS deleted)
  (markedEquiv.trans
    (deletedBoundaryHalfDartEquivBoundaryDart RS deleted)).symm

@[simp]
theorem complementBoundaryAlphaEquiv_val
    (RS : RotationSystem V E) (deleted : Finset V)
    (dart : BoundaryDart RS (deletedRegionKeep deleted)) :
    (complementBoundaryAlphaEquiv RS deleted dart).1.1 =
      RS.alpha dart.1.1 := by
  rfl

/-- The existing deleted-region successor is precisely the literal deleted
shore's successor transported back through boundary `alpha`. -/
theorem deletedRegionBoundarySuccessor_eq_permCongr_deletedSide
    (RS : RotationSystem V E) (deleted : Finset V) :
    deletedRegionBoundarySuccessor RS deleted =
      (complementBoundaryAlphaEquiv RS deleted).symm.permCongr
        (retainedRegionBoundarySuccessor RS
          (deletedSideKeep deleted)) := by
  let dartEquiv := deletedSideDartEquiv RS deleted
  let hitRetained := fun dart : RetainedDart RS
      (deletedSideKeep deleted) ↦
    ¬ deletedSideKeep deleted (RS.vertOf (RS.alpha dart.1))
  let hitDeleted := IsDeletedBoundaryHalfDart RS deleted
  let markedEquiv := dartEquiv.subtypeEquiv
    (deletedSideDartEquiv_hit_iff RS deleted)
  let deletedBoundaryEquiv :=
    deletedBoundaryHalfDartEquivBoundaryDart RS deleted
  have hface := deletedFacePerm_eq_permCongr_deletedSide RS deleted
  have hnext := nextHitPerm_permCongr dartEquiv
    (retainedCappedFacePerm RS (deletedSideKeep deleted))
    hitRetained hitDeleted
    (deletedSideDartEquiv_hit_iff RS deleted)
  change deletedBoundaryEquiv.permCongr
      (nextHitPerm (deletedFacePerm RS deleted) hitDeleted) =
    (markedEquiv.trans deletedBoundaryEquiv).permCongr
      (nextHitPerm (retainedCappedFacePerm RS
        (deletedSideKeep deleted)) hitRetained)
  rw [hface, hnext]
  apply Equiv.ext
  intro boundary
  simp only [Equiv.permCongr_apply]
  simp [markedEquiv]

section GraphBacked

variable {G : SimpleGraph V} [DecidableRel G.Adj]

local instance graphEdgeSetFintype : Fintype G.edgeSet :=
  SimpleGraph.fintypeEdgeSet G

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- For a connected spherical planar bond, ambient `alpha` is an
orientation-reversing matching of the two actual literal-shore first-return
orders.  Thus opposite boundary order is a consequence of the planar-bond
hypotheses, not an additional splice premise. -/
theorem boundarySuccessors_opposite_of_planarBond
    (rotation : SimpleGraphDartRotation.Data G)
    (deleted : Finset V)
    (hsphere : OrbitSphericalCubicMapData rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided rotation.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic rotation.toRotationSystem)
    (hretainedConnected :
      (G.induce {vertex | deletedRegionKeep deleted vertex}).Connected)
    (hdeletedConnected :
      (G.induce {vertex | deletedSideKeep deleted vertex}).Connected)
    (dart : BoundaryDart rotation.toRotationSystem
      (deletedRegionKeep deleted)) :
    retainedRegionBoundarySuccessor rotation.toRotationSystem
        (deletedSideKeep deleted)
        (complementBoundaryAlphaEquiv rotation.toRotationSystem deleted
          (retainedRegionBoundarySuccessor rotation.toRotationSystem
            (deletedRegionKeep deleted) dart)) =
      complementBoundaryAlphaEquiv rotation.toRotationSystem deleted dart := by
  let RS := rotation.toRotationSystem
  let matching := complementBoundaryAlphaEquiv RS deleted
  let retainedSuccessor :=
    retainedRegionBoundarySuccessor RS (deletedRegionKeep deleted)
  let deletedSuccessor := deletedRegionBoundarySuccessor RS deleted
  let literalDeletedSuccessor :=
    retainedRegionBoundarySuccessor RS (deletedSideKeep deleted)
  have hinverse : retainedSuccessor = deletedSuccessor⁻¹ := by
    exact retained_boundarySuccessor_eq_deleted_inverse_of_planar_bond
      rotation deleted hsphere htwoSided hconnected hrotation
        hretainedConnected hdeletedConnected
  have htransport : deletedSuccessor =
      matching.symm.permCongr literalDeletedSuccessor := by
    exact deletedRegionBoundarySuccessor_eq_permCongr_deletedSide RS deleted
  have hstep (point : BoundaryDart RS (deletedRegionKeep deleted)) :
      literalDeletedSuccessor (matching point) =
        matching (deletedSuccessor point) := by
    have hpoint := congrArg (fun permutation => permutation point) htransport
    calc
      literalDeletedSuccessor (matching point) =
          matching (matching.symm
            (literalDeletedSuccessor (matching point))) := by simp
      _ = matching (deletedSuccessor point) :=
        congrArg matching hpoint.symm
  change literalDeletedSuccessor (matching (retainedSuccessor dart)) =
    matching dart
  rw [hstep, hinverse]
  simp

/-- Equivalently, the canonical inverse-return hub rotations on the two
literal shores satisfy the orientation equation consumed by seam
sphericity. -/
theorem orientationReversing_canonicalHubRotation_of_planarBond
    (rotation : SimpleGraphDartRotation.Data G)
    (deleted : Finset V)
    (hsphere : OrbitSphericalCubicMapData rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided rotation.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic rotation.toRotationSystem)
    (hretainedConnected :
      (G.induce {vertex | deletedRegionKeep deleted vertex}).Connected)
    (hdeletedConnected :
      (G.induce {vertex | deletedSideKeep deleted vertex}).Connected) :
    OrientationReversing
      (complementBoundaryAlphaEquiv rotation.toRotationSystem deleted)
      (canonicalHubRotation rotation.toRotationSystem
        (deletedRegionKeep deleted))
      (canonicalHubRotation rotation.toRotationSystem
        (deletedSideKeep deleted)) := by
  apply orientationReversing_canonicalHubRotation_of_opposite
  exact boundarySuccessors_opposite_of_planarBond rotation deleted
    hsphere htwoSided hconnected hrotation hretainedConnected
      hdeletedConnected

/-- The planar-bond side-rank theorem closes the literal deleted shore as
well as the retained shore. -/
theorem closedSideSpherical_canonical_deletedSide_of_planarBond
    (rotation : SimpleGraphDartRotation.Data G)
    (deleted : Finset V)
    (outer : RetainedDart rotation.toRotationSystem
      (deletedSideKeep deleted))
    (hsphere : OrbitSphericalCubicMapData rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided rotation.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic rotation.toRotationSystem)
    (hretainedConnected :
      (G.induce {vertex | deletedRegionKeep deleted vertex}).Connected)
    (hdeletedConnected :
      (G.induce {vertex | deletedSideKeep deleted vertex}).Connected) :
    ClosedSideSpherical
      (ofVertexSide rotation.toRotationSystem
        (deletedSideKeep deleted) outer)
      (canonicalHubRotation rotation.toRotationSystem
        (deletedSideKeep deleted)) := by
  have hranks := planarBond_exact_sideRanks_and_transitionCount
    rotation deleted hsphere htwoSided hconnected hrotation
      hretainedConnected hdeletedConnected
  have hrank :
      (orbitFacesAllOnSide rotation.toRotationSystem
          (deletedSideKeep deleted)).card +
        sideVertexCount (deletedSideKeep deleted) =
      (graphEdgesAllOnSide G (deletedSideKeep deleted)).card + 1 := by
    simpa only [deletedSideKeep] using hranks.2.1
  have hambient := card_ambientRetainedFaceOrbit_eq_allOnSide
    rotation.toRotationSystem (deletedSideKeep deleted)
  have hvertices :
      sideVertexCount (deletedSideKeep deleted) =
        Fintype.card (RetainedVertex (deletedSideKeep deleted)) :=
    sideVertexCount_eq_card_sideVertex _
  have hedges := card_retainedInternalEdge_eq_allOnSide rotation
    (deletedSideKeep deleted)
  apply closedSideSpherical_canonical_of_faceRank
  omega

/-- Complete structural D3 package for a connected planar bond.  The seam is
the literal ambient edge flip; both cap Euler equalities and the opposite
orientation are consequences, not caller-supplied fields. -/
def bridgelessSphericalCubicMapData_of_planarBond_canonical
    (rotation : SimpleGraphDartRotation.Data G)
    (deleted : Finset V)
    (outerRetained : RetainedDart rotation.toRotationSystem
      (deletedRegionKeep deleted))
    (outerDeleted : RetainedDart rotation.toRotationSystem
      (deletedSideKeep deleted))
    (hsphere : OrbitSphericalCubicMapData rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided rotation.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic rotation.toRotationSystem)
    (hretainedConnected :
      (G.induce {vertex | deletedRegionKeep deleted vertex}).Connected)
    (hdeletedConnected :
      (G.induce {vertex | deletedSideKeep deleted vertex}).Connected)
    (hbridgeless :
      (toMultigraph rotation.toRotationSystem).Bridgeless)
    (first second : BoundaryDart rotation.toRotationSystem
      (deletedRegionKeep deleted))
    (hne : first ≠ second) :
    BridgelessSphericalCubicMapData
      ((ofVertexSide rotation.toRotationSystem
          (deletedRegionKeep deleted) outerRetained).composeRotationSystem
        (ofVertexSide rotation.toRotationSystem
          (deletedSideKeep deleted) outerDeleted)
        (complementBoundaryAlphaEquiv
          rotation.toRotationSystem deleted)) := by
  let RS := rotation.toRotationSystem
  have hretainedConnected' :
      ((rotationPrimalGraph RS).induce
        {vertex | deletedRegionKeep deleted vertex}).Connected := by
    simpa [RS,
      GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq]
      using hretainedConnected
  have hdeletedConnected' :
      ((rotationPrimalGraph RS).induce
        {vertex | deletedSideKeep deleted vertex}).Connected := by
    simpa [RS,
      GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq]
      using hdeletedConnected
  exact bridgelessSphericalCubicMapData_ofVertexSides
    RS (deletedRegionKeep deleted) (deletedSideKeep deleted)
    outerRetained outerDeleted
    (complementBoundaryAlphaEquiv RS deleted)
    (canonicalHubRotation RS (deletedRegionKeep deleted))
    (canonicalHubRotation RS (deletedSideKeep deleted))
    hretainedConnected' hdeletedConnected' hbridgeless
    first second hne hsphere.cubic hrotation
    (hubFacesDistinct_canonical RS
      (deletedRegionKeep deleted) outerRetained)
    (hubFacesDistinct_canonical RS
      (deletedSideKeep deleted) outerDeleted)
    (orientationReversing_canonicalHubRotation_of_planarBond
      rotation deleted hsphere htwoSided hconnected hrotation
        hretainedConnected hdeletedConnected)
    (closedSideSpherical_canonical_of_planarBond rotation deleted
      outerRetained hsphere htwoSided hconnected hrotation
        hretainedConnected hdeletedConnected)
    (closedSideSpherical_canonical_deletedSide_of_planarBond
      rotation deleted outerDeleted hsphere htwoSided hconnected hrotation
        hretainedConnected hdeletedConnected)

end GraphBacked

end

end GoertzelV24ComplementaryShoreBoundaryOrder

end Mettapedia.GraphTheory.FourColor
