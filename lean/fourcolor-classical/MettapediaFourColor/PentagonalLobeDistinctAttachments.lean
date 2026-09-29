import MettapediaFourColor.PentagonalLobeEmbeddedReduction
import Mettapedia.GraphTheory.FourColor.MatchingBoundaryConnectivity
import Mettapedia.GraphTheory.FourColor.GoertzelV24ThreeEdgeCutMinimality

/-!
# A local attachment condition supplies the connected lobe exterior

Six distinct exterior attachment vertices make the actual exterior connected
in a cubic source with cyclic edge-connectivity at least four. Minimality
already supplies that cut bound. The recognized pentagonal patch therefore
reduces without an independently assumed connected exterior.

The exact local patch recognition and distinctness of its six exterior
attachments remain geometric hypotheses. Their supply from alternating lobes
is not asserted here.
-/

namespace Mettapedia.GraphTheory.FourColor.MatchingBoundaryConnectivity

open GoertzelV24CubicSmallBoundaryCycle GoertzelV24RotationCutDartDecomposition

noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The graph-cut dart and rotation-system port retain the same actual dart. -/
def crossingBoundaryEquiv (rotation : SimpleGraphDartRotation.Data G) (keep : V → Prop) :
    CrossingSideDart G keep ≃ BoundaryDart rotation.toRotationSystem keep where
  toFun d := ⟨⟨d.1, d.2.1⟩, d.2.2⟩
  invFun b := ⟨b.1.1, b.1.2, b.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end
end Mettapedia.GraphTheory.FourColor.MatchingBoundaryConnectivity

namespace FourColor.PentagonalLobePatch.Tangle.Embedded

open Mettapedia.GraphTheory.FourColor
open GoertzelV24OpenTangleComposition GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24RotationCutDartDecomposition GoertzelV24DeletedRegionRotationSplice
open GoertzelV24ComplementaryShoreBoundaryOrder
open GoertzelV24TwoEdgeCutMinimality GoertzelV24OrbitFaceTwoSided
open GoertzelV24ThreeEdgeCutMinimality GoertzelV24CubicSmallBoundaryCycle
open MatchingBoundaryConnectivity

noncomputable section
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance attachmentEdgeSetDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

variable (rotation : SimpleGraphDartRotation.Data G) (deleted : Finset V)
  (rootIn : RetainedDart rotation.toRotationSystem (deletedSideKeep deleted))
  (recognition : OpenTangleIsomorphism.Iso piece
    (ofVertexSide rotation.toRotationSystem (deletedSideKeep deleted) rootIn))

/-- The six actual vertices on the exterior ends of the cut edges. -/
def attachment (i : Fin 6) : V := (ports rotation deleted rootIn recognition i).1.1.fst

theorem exterior_connected_of_distinct_attachments
    (hcubic : rotation.toRotationSystem.IsCubic)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 4)
    (hinj : Function.Injective (attachment rotation deleted rootIn recognition)) :
    (G.induce {v | deletedRegionKeep deleted v}).Connected := by
  let order := ports rotation deleted rootIn recognition
  let e := crossingBoundaryEquiv rotation (deletedRegionKeep deleted)
  apply connected_of_boundary_card_lt_eight (deletedRegionKeep deleted)
    (fun v => (degree_instance_independent v _ _).trans
      ((rotation.toRotationSystem_isCubic_iff.mp hcubic) v)) hcyclic
  · exact ⟨(order 0).1.1.fst, (order 0).1.2⟩
  · intro a b he
    apply e.injective
    apply order.symm.injective
    apply hinj
    change (order (order.symm (e a))).1.1.fst = (order (order.symm (e b))).1.1.fst
    simp only [Equiv.apply_symm_apply]
    exact he
  · have hc := Fintype.card_congr (e.trans order.symm)
    simp only [Fintype.card_fin] at hc
    omega

theorem strict_reduction_of_distinct_attachments
    (rootOut : RetainedDart rotation.toRotationSystem (deletedRegionKeep deleted))
    (h : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 4)
    (hinj : Function.Injective (attachment rotation deleted rootIn recognition)) :
    Fintype.card ({v : V // deletedRegionKeep deleted v} ⊕ Fin 4) + 12 = Fintype.card V ∧
      Fintype.card ({v : V // deletedRegionKeep deleted v} ⊕ Fin 4) < Fintype.card V ∧
      BridgelessSphericalCubicMapData (smaller rotation deleted rootOut rootIn recognition) ∧
      (RotationSystemTaitColorable (smaller rotation deleted rootOut rootIn recognition) →
        RotationSystemTaitColorable rotation.toRotationSystem) :=
  strict_reduction rotation deleted rootOut rootIn recognition h htwo
    (exterior_connected_of_distinct_attachments rotation deleted rootIn recognition
      h.spherical.cubic hcyclic hinj)

/-- Minimality supplies the cyclic cut bound, the smaller colouring and all
ambient geometric conditions. Only the local recognized occurrence and its
six distinct exterior endpoints remain. -/
theorem not_in_minimal_counterexample_of_distinct_attachments
    (rootOut : RetainedDart rotation.toRotationSystem (deletedRegionKeep deleted))
    (hinj : Function.Injective (attachment rotation deleted rootIn recognition))
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation) : False :=
  not_in_minimal_counterexample rotation deleted rootOut rootIn recognition
    (exterior_connected_of_distinct_attachments rotation deleted rootIn recognition
      minimal.spherical.cubic
      (cyclicEdgeConnectivityAtLeast_four_of_vertexMinimalTaitCounterexample rotation minimal) hinj)
    minimal

end
end FourColor.PentagonalLobePatch.Tangle.Embedded
