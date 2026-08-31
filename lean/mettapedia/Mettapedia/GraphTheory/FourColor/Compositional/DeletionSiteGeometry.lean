import Mettapedia.GraphTheory.FourColor.Compositional.DeletionColorMatching
import Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnNoncrossing
import Mettapedia.GraphTheory.FourColor.Compositional.ResidualSiteProvenance

/-!
# Residual geometry from an arbitrary deletion colouring

The mesh-global residual receipts remember one preselected deletion colouring
at every physical step.  Consecutive path repair, however, produces different
deletion colourings chosen for compatibility on their common carriers.  This
module factors the common semantic interface out of that choice mechanism.

A `DeletionAlternatingSiteReceipt` starts with any Tait colouring of an
adjacent-pair deletion and the absent colour class completed across the deleted
edge.  A `DeletionTwoSectorReturnReceipt` carries that exact state through the
alternating-cycle, facial-bond, formation, physical-return, shore, and
two-sector constructions.  No mesh, global choice function, or cross-site
compatibility hypothesis occurs in either structure.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.DeletionSiteGeometry

open AlternatingSiteGeometry
open DeletionColorMatching
open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24AdjacentPairMatchingExtraction
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrderedMeshResidualSiteFacialBond
open GoertzelV24PrimalCycleFacialBond
open GoertzelV24ResidualFormationSwitch
open GoertzelV24ResidualReturnPairing
open GoertzelV24ResidualReturnShore
open GoertzelV24RotationMultigraphAdapter
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TaitMatchingDecomposition
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open ResidualReturnNoncrossing
open ResidualSiteProvenance
open SimpleGraph
open SimpleGraphDartRotation

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- One canonical incident-edge triple system for a graph-backed least
counterexample.  Using one definition here keeps all path-selected receipts
on the same dependent carrier. -/
def cubicIncidentEdgeTriples
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation) :
    HasCubicIncidentEdgeTriples G :=
  hasCubicIncidentEdgeTriples_of_incidentEdgeFinset_card_eq_three
    (incidentEdgeFinset_card_eq_three rotation minimal)

/-- An arbitrary deletion-colouring state carried into the proper alternating
component that it determines against a fixed residual-defect minimizer. -/
structure DeletionAlternatingSiteReceipt
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (minimizer : ResidualDefectMinimizer G)
    (data : AdjacentPairData G)
    (state : DeletionMatchingState data) where
  site : ProperAlternatingComponentWitness G minimizer.pairing
    data.firstVertex data.secondVertex
  site_tau_eq : site.tau =
    state.pairing (incidentEdgeFinset_card_eq_three rotation minimal)

namespace DeletionAlternatingSiteReceipt

/-- A noncentral completed deletion matching determines a proper alternating
component, without requiring that its colouring be a globally selected one. -/
theorem ofState
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (minimizer : ResidualDefectMinimizer G)
    (data : AdjacentPairData G)
    (state : DeletionMatchingState data)
    (hne : minimizer.pairing.partner data.firstVertex ≠ data.secondVertex) :
    Nonempty (DeletionAlternatingSiteReceipt
      rotation minimal minimizer data state) := by
  let hcubic := incidentEdgeFinset_card_eq_three rotation minimal
  let other := state.pairing hcubic
  have hother : other.SupportedBy G := state.pairing_supported hcubic
  have hprescribed : other.partner data.firstVertex = data.secondVertex :=
    state.pairing_partner_first hcubic
  have hnot : ¬ TaitColorable G :=
    graphBackedVertexMinimalTaitCounterexample_not_graphTaitColorable
      rotation minimal
  obtain ⟨site, hsite⟩ := properAlternatingComponentWitness_of_partner_ne
    (cubicIncidentEdgeTriples rotation minimal) hnot
    minimizer.pairing minimizer.supported other hother
    (fun carrier hMinimizerClosed hOtherClosed =>
      minimizer.exchange_minimal other carrier
        hMinimizerClosed hOtherClosed hother)
    data.firstVertex data.secondVertex hprescribed hne
  exact ⟨{
    site := site
    site_tau_eq := by simpa only [other] using hsite }⟩

end DeletionAlternatingSiteReceipt

/-- Complete two-sector residual geometry retaining the exact arbitrary
deletion-colouring state from which the second matching was built. -/
structure DeletionTwoSectorReturnReceipt
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (minimizer : ResidualDefectMinimizer G)
    (data : AdjacentPairData G)
    (state : DeletionMatchingState data) where
  alternating : DeletionAlternatingSiteReceipt
    rotation minimal minimizer data state
  base : TwoSectorReturnReceipt rotation
    (cubicIncidentEdgeTriples rotation minimal) minimizer.pairing
    data.firstVertex data.secondVertex
  base_site_eq : base.base.bond.site = alternating.site

namespace DeletionTwoSectorReturnReceipt

/-- Carry an arbitrary deletion-colouring alternating site through the exact
facial and physical return geometry, without changing its matching. -/
theorem ofAlternating
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (minimizer : ResidualDefectMinimizer G)
    (data : AdjacentPairData G)
    (state : DeletionMatchingState data)
    (receipt : DeletionAlternatingSiteReceipt
      rotation minimal minimizer data state) :
    Nonempty (DeletionTwoSectorReturnReceipt
      rotation minimal minimizer data state) := by
  rcases exists_faceSet_bond_of_isCycle rotation
      minimal.toBridgelessSphericalCubicMapData minimal.facesTwoSided
      receipt.site.cycle receipt.site.cycle_isCycle with
    ⟨faces, hseparator, hselected, hcomplement⟩
  let bond : ProperAlternatingSiteFacialBondWitness rotation
      minimizer.pairing data.firstVertex data.secondVertex :=
    { site := receipt.site
      faces := faces
      cycle_separates_faces := hseparator
      selected_faces_connected := hselected
      complement_faces_connected := hcomplement }
  let hG := cubicIncidentEdgeTriples rotation minimal
  let returnPairing : Pairing (BoundaryVertex bond.site.carrier) :=
    siteReturnPairing hG minimizer.pairing minimizer.supported bond.site
  let returnShore : FacialFormationReturnShoreReceipt rotation hG
      minimizer.pairing data.firstVertex data.secondVertex :=
    { sigma_supported := minimizer.supported
      bond := bond
      formation := fun vertex =>
        facialFormationSwitchReceipt rotation minimal minimizer.pairing
          minimizer.supported bond vertex.2
      returnPairing := returnPairing
      return_reachable := fun vertex =>
        siteReturnPairing_reachable hG minimizer.pairing
          minimizer.supported bond.site vertex
      return_is_canonical := rfl
      return_same_face_shore := fun vertex =>
        siteReturnPairing_thirdDarts_same_face_shore rotation
          minimal.spherical.cubic minimal.vertexRotationCyclic hG
          minimizer.pairing minimizer.supported bond vertex }
  let base := TwoSectorReturnReceipt.ofReturnShoreReceipt
    rotation minimal hG minimizer.pairing returnShore
  exact ⟨{
    alternating := receipt
    base := base
    base_site_eq := rfl }⟩

/-- Consumer constructor from an arbitrary noncentral deletion-colouring state
directly to its complete two-sector geometry. -/
theorem ofState
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (minimizer : ResidualDefectMinimizer G)
    (data : AdjacentPairData G)
    (state : DeletionMatchingState data)
    (hne : minimizer.pairing.partner data.firstVertex ≠ data.secondVertex) :
    Nonempty (DeletionTwoSectorReturnReceipt
      rotation minimal minimizer data state) := by
  let alternating := Classical.choice
    (DeletionAlternatingSiteReceipt.ofState
      rotation minimal minimizer data state hne)
  exact DeletionTwoSectorReturnReceipt.ofAlternating
    rotation minimal minimizer data state alternating

end DeletionTwoSectorReturnReceipt

end

end Mettapedia.GraphTheory.FourColor.Compositional.DeletionSiteGeometry
