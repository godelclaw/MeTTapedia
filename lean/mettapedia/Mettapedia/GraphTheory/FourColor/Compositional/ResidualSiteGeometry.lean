import Mettapedia.GraphTheory.FourColor.Compositional.ResidualSiteProvenance

/-!
# Provenance-preserving residual site geometry

The local residual geometry was historically assembled after existentially
choosing an alternating site.  This module factors that assembly through a
supplied `ProvenancedAlternatingSiteReceipt`.  Consequently the facial bond,
formation switch, physical return pairing, and two-sector conclusion all
refer to the absent colour class of the exact globally selected deletion
colouring.

The construction is pointwise in a mesh step.  It does not assert that the
selected deletion colourings at two distinct steps are compatible.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.ResidualSiteGeometry

open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24OrderedMeshGlobalSites
open GoertzelV24OrderedMeshResidualSiteFacialBond
open GoertzelV24PrimalCycleFacialBond
open GoertzelV24ResidualDefectDescent
open GoertzelV24ResidualFormationSwitch
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnPairing
open GoertzelV24ResidualReturnShore
open GoertzelV24RotationMultigraphAdapter
open GoertzelV24TaitMatchingPair
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnNoncrossing
open Mettapedia.GraphTheory.FourColor.Compositional.ResidualSiteProvenance
open SimpleGraph
open SimpleGraphDartRotation

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {a b : Nat}

/-- A facial bond whose alternating site is identified with the exact site
carried by a colouring-provenance receipt. -/
structure ProvenancedFacialBondReceipt
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b)
    (sigma : Pairing V)
    (step : GlobalMeshStep rotation ordered) where
  provenance : ProvenancedAlternatingSiteReceipt
    rotation minimal ordered sigma step
  bond : ProperAlternatingSiteFacialBondWitness rotation sigma
    (globalFirstVertex rotation ordered step)
    (globalSecondVertex rotation ordered step)
  bond_site_eq : bond.site = provenance.site

/-- Turn a supplied provenanced alternating site into its two connected
facial shores.  This is the generic Jordan-facing constructor used by the
global mesh theorem below. -/
theorem ProvenancedFacialBondReceipt.ofAlternating
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b)
    (sigma : Pairing V)
    (step : GlobalMeshStep rotation ordered)
    (receipt : ProvenancedAlternatingSiteReceipt
      rotation minimal ordered sigma step) :
    Nonempty (ProvenancedFacialBondReceipt
      rotation minimal ordered sigma step) := by
  rcases exists_faceSet_bond_of_isCycle rotation
      minimal.toBridgelessSphericalCubicMapData minimal.facesTwoSided
      receipt.site.cycle receipt.site.cycle_isCycle with
    ⟨faces, hseparator, hselected, hcomplement⟩
  let bond : ProperAlternatingSiteFacialBondWitness rotation sigma
      (globalFirstVertex rotation ordered step)
      (globalSecondVertex rotation ordered step) :=
    { site := receipt.site
      faces := faces
      cycle_separates_faces := hseparator
      selected_faces_connected := hselected
      complement_faces_connected := hcomplement }
  exact ⟨{
    provenance := receipt
    bond := bond
    bond_site_eq := rfl }⟩

/-- The complete formation/return/shore geometry together with the exact
colouring provenance of its alternating site. -/
structure ProvenancedReturnShoreReceipt
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V)
    (step : GlobalMeshStep rotation ordered) where
  facialBond : ProvenancedFacialBondReceipt
    rotation minimal ordered sigma step
  base : FacialFormationReturnShoreReceipt rotation hG sigma
    (globalFirstVertex rotation ordered step)
    (globalSecondVertex rotation ordered step)
  base_site_eq : base.bond.site = facialBond.provenance.site

/-- Build the physical formation, canonical return pairing, and face-shore
transport from a supplied provenanced facial bond. -/
theorem ProvenancedReturnShoreReceipt.ofFacialBond
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V)
    (hSigma : sigma.SupportedBy G)
    (step : GlobalMeshStep rotation ordered)
    (receipt : ProvenancedFacialBondReceipt
      rotation minimal ordered sigma step) :
    Nonempty (ProvenancedReturnShoreReceipt
      rotation minimal ordered hG sigma step) := by
  let returnPairing : Pairing (BoundaryVertex receipt.bond.site.carrier) :=
    siteReturnPairing hG sigma hSigma receipt.bond.site
  let base : FacialFormationReturnShoreReceipt rotation hG sigma
      (globalFirstVertex rotation ordered step)
      (globalSecondVertex rotation ordered step) :=
    { sigma_supported := hSigma
      bond := receipt.bond
      formation := fun vertex =>
        facialFormationSwitchReceipt rotation minimal sigma hSigma
          receipt.bond vertex.2
      returnPairing := returnPairing
      return_reachable := fun vertex =>
        siteReturnPairing_reachable hG sigma hSigma receipt.bond.site vertex
      return_is_canonical := rfl
      return_same_face_shore := fun vertex =>
        siteReturnPairing_thirdDarts_same_face_shore rotation
          minimal.spherical.cubic minimal.vertexRotationCyclic hG sigma hSigma
          receipt.bond vertex }
  exact ⟨{
    facialBond := receipt
    base := base
    base_site_eq := receipt.bond_site_eq }⟩

/-- A two-sector noncrossing receipt that still carries the exact selected
deletion colouring from which its second matching arose. -/
structure ProvenancedTwoSectorReturnReceipt
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V)
    (step : GlobalMeshStep rotation ordered) where
  returnShore : ProvenancedReturnShoreReceipt
    rotation minimal ordered hG sigma step
  base : TwoSectorReturnReceipt rotation hG sigma
    (globalFirstVertex rotation ordered step)
    (globalSecondVertex rotation ordered step)
  base_site_eq : base.base.bond.site = returnShore.facialBond.provenance.site

/-- Add the already-proved two-sector noncrossing theorem without changing
the site, bond, or return pairing. -/
def ProvenancedTwoSectorReturnReceipt.ofReturnShore
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V)
    (step : GlobalMeshStep rotation ordered)
    (receipt : ProvenancedReturnShoreReceipt
      rotation minimal ordered hG sigma step) :
    ProvenancedTwoSectorReturnReceipt
      rotation minimal ordered hG sigma step :=
  { returnShore := receipt
    base := TwoSectorReturnReceipt.ofReturnShoreReceipt
      rotation minimal hG sigma receipt.base
    base_site_eq := receipt.base_site_eq }

/-- The second matching visible to the final geometric consumer is exactly
the absent-colour completion recorded at the selected deletion colouring. -/
theorem ProvenancedTwoSectorReturnReceipt.site_tau_eq_pairing
    {rotation : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample rotation}
    {ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b}
    {hG : HasCubicIncidentEdgeTriples G}
    {sigma : Pairing V}
    {step : GlobalMeshStep rotation ordered}
    (receipt : ProvenancedTwoSectorReturnReceipt
      rotation minimal ordered hG sigma step) :
    receipt.base.base.bond.site.tau =
      receipt.returnShore.facialBond.provenance.provenance.pairing := by
  rw [receipt.base_site_eq]
  exact receipt.returnShore.facialBond.provenance.site_tau_eq

/-- The colouring recorded by the final receipt is the pre-existing global
choice for this mesh step, rather than a new local witness. -/
theorem ProvenancedTwoSectorReturnReceipt.site_eq_selected
    {rotation : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample rotation}
    {ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b}
    {hG : HasCubicIncidentEdgeTriples G}
    {sigma : Pairing V}
    {step : GlobalMeshStep rotation ordered}
    (receipt : ProvenancedTwoSectorReturnReceipt
      rotation minimal ordered hG sigma step) :
    receipt.returnShore.facialBond.provenance.provenance.site =
      selectedGlobalKempeSite rotation minimal ordered step :=
  receipt.returnShore.facialBond.provenance.provenance.site_eq_selected

/-- Consumer-facing form of
`ProvenancedTwoSectorReturnReceipt.site_tau_eq_pairing`. -/
theorem provenancedTwoSectorReturn_site_tau_eq_pairing
    {rotation : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample rotation}
    {ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b}
    {hG : HasCubicIncidentEdgeTriples G}
    {sigma : Pairing V}
    {step : GlobalMeshStep rotation ordered}
    (receipt : ProvenancedTwoSectorReturnReceipt
      rotation minimal ordered hG sigma step) :
    receipt.base.base.bond.site.tau =
      receipt.returnShore.facialBond.provenance.provenance.pairing :=
  receipt.site_tau_eq_pairing

/-- Consumer-facing form of
`ProvenancedTwoSectorReturnReceipt.site_eq_selected`. -/
theorem provenancedTwoSectorReturn_site_eq_selected
    {rotation : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample rotation}
    {ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b}
    {hG : HasCubicIncidentEdgeTriples G}
    {sigma : Pairing V}
    {step : GlobalMeshStep rotation ordered}
    (receipt : ProvenancedTwoSectorReturnReceipt
      rotation minimal ordered hG sigma step) :
    receipt.returnShore.facialBond.provenance.provenance.site =
      selectedGlobalKempeSite rotation minimal ordered step :=
  receipt.site_eq_selected

/-- One common residual-defect minimizer supplies, at every noncentral mesh
step, the entire two-sector geometry with the exact selected deletion
colouring and absent colour retained.  The theorem is pointwise in `step` and
does not assert compatibility between distinct receipts. -/
theorem exists_provenancedTwoSectorReturnReceipt_at_every_globalMeshStep
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b) :
    ∃ hG : HasCubicIncidentEdgeTriples G,
      ∃ sigma : Pairing V,
        sigma.SupportedBy G ∧
        2 ≤ residualDefect G sigma ∧
        ∀ step : GlobalMeshStep rotation ordered,
          sigma.partner (globalFirstVertex rotation ordered step) =
              globalSecondVertex rotation ordered step ∨
            Nonempty (ProvenancedTwoSectorReturnReceipt
              rotation minimal ordered hG sigma step) := by
  have hCubic : G.IsRegularOfDegree 3 :=
    rotation.toRotationSystem_isCubic_iff.mp minimal.spherical.cubic
  let hG : HasCubicIncidentEdgeTriples G :=
    hasCubicIncidentEdgeTriples_of_incidentEdgeFinset_card_eq_three
      fun vertex => by
        rw [incidentEdgeFinset_card_eq_degree, hCubic vertex]
  obtain ⟨sigma, hSigma, hodd, hsites⟩ :=
    exists_exchangeRigid_with_provenanced_alternatingSite_at_every_globalMeshStep
      rotation minimal ordered
  refine ⟨hG, sigma, hSigma, hodd, ?_⟩
  intro step
  rcases hsites step with hcentral | halternating
  · exact Or.inl hcentral
  · rcases halternating with ⟨alternating⟩
    let facialBond := Classical.choice
      (ProvenancedFacialBondReceipt.ofAlternating
        rotation minimal ordered sigma step alternating)
    let returnShore := Classical.choice
      (ProvenancedReturnShoreReceipt.ofFacialBond
        rotation minimal ordered hG sigma hSigma step facialBond)
    exact Or.inr ⟨ProvenancedTwoSectorReturnReceipt.ofReturnShore
      rotation minimal ordered hG sigma step returnShore⟩

end

end Mettapedia.GraphTheory.FourColor.Compositional.ResidualSiteGeometry
