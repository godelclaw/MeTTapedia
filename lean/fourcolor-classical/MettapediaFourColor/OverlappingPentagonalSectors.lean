import MettapediaFourColor.PentagonalDiamondFaceReduction
import Mettapedia.GraphTheory.FourColor.PentagonalNeighbourSupply

/-!
# A pentagonal overlap exposes the shared diamond

Two local views start on opposite sides of one actual edge. Their readings
of the third face at an endpoint have consecutive roots. If that face is
pentagonal, two backward steps from one root and two forward steps from
the other identify the same dart. Thus information about the outer corner
of either view transfers to the other, without an extra matching assumption.

Three neighbouring pentagon readings, distributed between these views,
then supply the existing diamond recognition and strict reduction. The two
faces incident with the original edge have unrestricted sizes, as does the
rest of the map. Ambient normal form is used only by the existing reduction.

The overlap in Figure 11 of arXiv:2603.24880v1 motivates this local law. This
module does not classify zero-charge cartwheels or prove that the required
readings occur in every such pair. No figure or external program is an axiom.
-/

namespace FourColor.OverlappingPentagonalSectors

open Mettapedia.GraphTheory.FourColor
open PentagonalNeighbourSupply GoertzelV24OrbitFaceCyclicOrder
open Equiv Equiv.Perm

section Rotation

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (RS : RotationSystem V E)

/-- Cross the next edge on the first incident face. -/
def leftRoot (d : RS.D) : RS.D := RS.alpha (RS.phi d)

/-- Read the same corner from the second incident face. -/
def rightRoot (d : RS.D) : RS.D := RS.rho (RS.rho (RS.alpha d))

def leftNear (d : RS.D) : RS.D := RS.alpha (RS.phi.symm (leftRoot RS d))
def leftOuter (d : RS.D) : RS.D :=
  RS.alpha (RS.phi.symm (RS.phi.symm (leftRoot RS d)))
def rightNear (d : RS.D) : RS.D := RS.alpha (RS.phi (rightRoot RS d))
def rightOuter (d : RS.D) : RS.D := RS.alpha (RS.phi (RS.phi (rightRoot RS d)))

/-- Agreement is derived from the actual edge and rotation operations. -/
theorem roots_consecutive (d : RS.D) :
    rightRoot RS d = RS.phi (leftRoot RS d) := by
  simp only [rightRoot, leftRoot, RotationSystem.phi, Perm.mul_apply,
    RS.alpha_involutive]

private theorem period (d : RS.D) (hp : size RS (leftRoot RS d) = 5) :
    RS.phi (RS.phi (RS.phi (RS.phi (RS.phi (leftRoot RS d))))) = leftRoot RS d := by
  have h := (phi_isCycleOn_faceOrbit RS (leftRoot RS d)).pow_card_apply
    (RS.mem_faceOrbit_self (leftRoot RS d))
  change (RS.phi ^ size RS (leftRoot RS d)) (leftRoot RS d) = leftRoot RS d at h
  simpa only [hp, pow_succ', pow_zero, Perm.mul_apply, Perm.one_apply] using h

private theorem backwards_one (d : RS.D) (hp : size RS (leftRoot RS d) = 5) :
    RS.phi.symm (leftRoot RS d) =
      RS.phi (RS.phi (RS.phi (RS.phi (leftRoot RS d)))) := by
  apply RS.phi.injective
  rw [RS.phi.apply_symm_apply, period RS d hp]

private theorem backwards_two (d : RS.D) (hp : size RS (leftRoot RS d) = 5) :
    RS.phi.symm (RS.phi.symm (leftRoot RS d)) =
      RS.phi (RS.phi (RS.phi (leftRoot RS d))) := by
  apply RS.phi.injective
  rw [RS.phi.apply_symm_apply, backwards_one RS d hp]

/-- The outer corners are literally the same dart, hence have the same
face, edge, and all observations on that dart. Pairwise possibilities are
not substituted for this common witness. -/
theorem outer_dart_eq (d : RS.D) (hp : size RS (leftRoot RS d) = 5) :
    leftOuter RS d = rightOuter RS d := by
  simp only [leftOuter, rightOuter, roots_consecutive, backwards_two RS d hp]

theorem observe_outer_eq {O : Type*} (observe : RS.D → O) (d : RS.D)
    (hp : size RS (leftRoot RS d) = 5) :
    observe (leftOuter RS d) = observe (rightOuter RS d) :=
  congrArg observe (outer_dart_eq RS d hp)

/-- Two outer-corner readings are redundant after the geometric overlap
has been established. Either view may supply the required degree. -/
theorem outer_size_iff (d : RS.D) (hp : size RS (leftRoot RS d) = 5) (n : ℕ) :
    size RS (leftOuter RS d) = n ↔ size RS (rightOuter RS d) = n := by
  rw [outer_dart_eq RS d hp]

/-- The positions fail to agree on a six-cycle. This is a control on the
cyclic argument, not an ambient planar-map counterexample. -/
theorem six_cycle_positions_differ : (0 - 2 : Fin 6) ≠ 1 + 2 := by decide +kernel

end Rotation

noncomputable section Graph

open SimpleGraphDartRotation PhysicalForkCodeFaces
open GoertzelV24TwoEdgeCutMinimality GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided GoertzelV24WeightedOrbitFaceCorridor
open GoertzelV24ComplementaryShoreBoundaryOrder GoertzelV24DeletedRegionRotationSplice

set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

variable (rotation : Data G) (seam : G.Dart)

/-- Readings of actual neighbouring faces. Neither a diamond occurrence
nor a colouring is assumed. The outer corner may be read from either side. -/
structure Readings : Prop where
  central : size rotation.toRotationSystem (leftRoot rotation.toRotationSystem seam) = 5
  left : size rotation.toRotationSystem (leftNear rotation.toRotationSystem seam) = 5
  right : size rotation.toRotationSystem (rightNear rotation.toRotationSystem seam) = 5
  outer : size rotation.toRotationSystem (leftOuter rotation.toRotationSystem seam) = 5 ∨
    size rotation.toRotationSystem (rightOuter rotation.toRotationSystem seam) = 5

/-- Rebasing the shared face places the three forced pentagons at the
positions consumed by the existing geometric diamond theorem. -/
theorem face_pattern (h : Readings rotation seam) :
    PentagonalDiamond.FaceLengths rotation (rightRoot rotation.toRotationSystem seam) := by
  let RS := rotation.toRotationSystem
  have hout : size RS (rightOuter RS seam) = 5 :=
    h.outer.elim ((outer_size_iff RS seam h.central 5).mp) id
  refine ⟨?_, ?_⟩
  · change size RS (rightRoot RS seam) = 5
    rw [roots_consecutive, size_phi]
    exact h.central
  · intro i hi hj
    fin_cases i
    · norm_num at hi
    · exact h.right
    · exact hout
    · change size RS (RS.alpha ((RS.phi ^ 3) (rightRoot RS seam))) = 5
      have he : (RS.phi ^ 3) (rightRoot RS seam) = RS.phi.symm (leftRoot RS seam) := by
        simpa only [roots_consecutive, pow_succ', pow_zero, Perm.mul_apply,
          Perm.one_apply] using (backwards_one RS seam h.central).symm
      rw [he]
      exact h.left
    · norm_num at hj

variable (readings : Readings rotation seam)
  (ambient : BridgelessSphericalCubicMapData rotation.toRotationSystem)
  (minimum : OrbitFaceMinimumFive rotation.toRotationSystem)
  (connectivity : CyclicallyFiveEdgeConnected G)

abbrev root := rightRoot rotation.toRotationSystem seam
abbrev deleted := PentagonalDiamondPatch.Tangle.Recognition.deleted rotation (root rotation seam)

/-- Exact source occurrence, built from the overlap readings and ambient
normal form, for use by the existing boundary reconstruction theorem. -/
def recognized := PentagonalDiamondPatch.Tangle.FaceReduction.recognized
  rotation (root rotation seam) (face_pattern rotation seam readings) ambient minimum connectivity

/-- The overlap exposes a strict reduction of the whole source: twelve
vertices are removed and four introduced. All exterior vertices are counted. -/
theorem strict_reduction (twoSided : OrbitFacesTwoSided rotation.toRotationSystem) :
    let rin := PentagonalDiamondPatch.Tangle.Recognition.rootIn rotation (root rotation seam)
      (PentagonalDiamondPatch.Tangle.FaceReduction.cubic rotation ambient)
      (face_pattern rotation seam readings)
    let R := recognized rotation seam readings ambient minimum connectivity
    let rout := (SixPortTreeReplacement.Embedded.ports PentagonalDiamondPatch.Tangle.scheme
      rotation (deleted rotation seam) rin R 0).1
    let candidate := SixPortTreeReplacement.Embedded.smaller PentagonalDiamondPatch.Tangle.scheme
      rotation (deleted rotation seam) rout rin R
    Fintype.card ({v : V // deletedRegionKeep (deleted rotation seam) v} ⊕ Fin 4) + 8 =
        Fintype.card V ∧
      Fintype.card ({v : V // deletedRegionKeep (deleted rotation seam) v} ⊕ Fin 4) <
        Fintype.card V ∧
      BridgelessSphericalCubicMapData candidate ∧
      (RotationSystemTaitColorable candidate →
        RotationSystemTaitColorable rotation.toRotationSystem) :=
  PentagonalDiamondPatch.Tangle.FaceReduction.strict_reduction_of_face_pattern
    rotation (root rotation seam) (face_pattern rotation seam readings)
    ambient minimum connectivity twoSided

omit ambient minimum connectivity in
include readings in
/-- A minimal counterexample cannot realize these joint local readings.
Its normal-form and smaller-colouring obligations are derived by the
existing reduction rather than added as boundary-support hypotheses. -/
theorem not_in_minimal
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation) : False :=
  PentagonalDiamondPatch.Tangle.FaceReduction.not_in_minimal_counterexample_of_face_pattern
    rotation (root rotation seam) (face_pattern rotation seam readings) minimal

end Graph
end FourColor.OverlappingPentagonalSectors
