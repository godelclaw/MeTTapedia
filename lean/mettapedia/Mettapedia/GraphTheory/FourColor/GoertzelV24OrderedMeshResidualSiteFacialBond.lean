import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedMeshResidualSiteMatching
import Mettapedia.GraphTheory.FourColor.GoertzelV24PrimalCycleFacialBond

/-!
# Facial bonds carried by residual ordered-mesh sites

The residual-defect minimizer supplies, at every mesh edge it does not use,
a simple ambient alternating cycle through that edge.  Spherical map theory
then turns that primal cycle into an exact bond of the facial dual: its edges
are precisely the primal edges separating two connected face shores.

This is the correct Jordan-facing output of the matching construction.  It
does not label alternating cycle vertices as two sides, and it does not claim
compatibility between the face shores selected at different mesh sites.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OrderedMeshResidualSiteFacialBond

open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24OrderedMeshGlobalSites
open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24PrimalCycleFacialBond
open GoertzelV24ResidualDefectDescent
open GoertzelV24ResidualOddness
open GoertzelV24RotationMultigraphAdapter
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {a b : Nat}

/-- A residual alternating site together with the exact two connected face
shores bounded by its simple ambient cycle. -/
structure ProperAlternatingSiteFacialBondWitness
    (rotation : Data G) (sigma : Pairing V) (first second : V) where
  site : ProperAlternatingSiteWitness G sigma first second
  faces : Finset (OrbitFace rotation.toRotationSystem)
  cycle_separates_faces :
    ∀ dart : rotation.toRotationSystem.D,
      (rotation.toRotationSystem.edgeOf dart).1 ∈ site.cycle.edges ↔
        ((dartOrbitFace rotation.toRotationSystem dart ∈ faces ∧
            dartOrbitFace rotation.toRotationSystem
              (rotation.toRotationSystem.alpha dart) ∉ faces) ∨
          (dartOrbitFace rotation.toRotationSystem dart ∉ faces ∧
            dartOrbitFace rotation.toRotationSystem
              (rotation.toRotationSystem.alpha dart) ∈ faces))
  selected_faces_connected :
    ((orbitFaceDualGraph rotation).induce
      {face | face ∈ faces}).Connected
  complement_faces_connected :
    ((orbitFaceDualGraph rotation).induce
      {face | face ∉ faces}).Connected

/-- One global minimum-residual-defect matching controls every ordered-mesh
edge.  At an edge it does not use, the rigid alternating component is also an
exact facial-dual bond with two connected shores.

No compatibility between bonds at distinct sites is asserted. -/
theorem exists_exchangeRigid_with_facialBond_at_every_globalMeshStep
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b) :
    ∃ sigma : Pairing V,
      sigma.SupportedBy G ∧
      2 ≤ residualDefect G sigma ∧
      ∀ step : GlobalMeshStep rotation ordered,
        sigma.partner (globalFirstVertex rotation ordered step) =
            globalSecondVertex rotation ordered step ∨
          Nonempty
            (ProperAlternatingSiteFacialBondWitness rotation sigma
              (globalFirstVertex rotation ordered step)
              (globalSecondVertex rotation ordered step)) := by
  obtain ⟨sigma, hSigma, hodd, hsites⟩ :=
    exists_exchangeRigid_with_proper_alternatingComponent_at_every_globalMeshStep
      rotation minimal ordered
  refine ⟨sigma, hSigma, hodd, ?_⟩
  intro step
  rcases hsites step with hcentral | hsite
  · exact Or.inl hcentral
  · rcases hsite with ⟨site⟩
    rcases exists_faceSet_bond_of_isCycle rotation
        minimal.toBridgelessSphericalCubicMapData minimal.facesTwoSided
        site.cycle site.cycle_isCycle with
      ⟨faces, hseparator, hselected, hcomplement⟩
    exact Or.inr ⟨{
      site := site
      faces := faces
      cycle_separates_faces := hseparator
      selected_faces_connected := hselected
      complement_faces_connected := hcomplement }⟩

end

end GoertzelV24OrderedMeshResidualSiteFacialBond

end Mettapedia.GraphTheory.FourColor
