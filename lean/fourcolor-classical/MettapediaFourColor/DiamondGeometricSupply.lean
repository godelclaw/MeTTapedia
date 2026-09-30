import Mettapedia.GraphTheory.FourColor.PentagonalNeighbourSupply
import MettapediaFourColor.PentagonalDiamondFaceReduction
import MettapediaFourColor.MixedDiamondFaceReduction
import MettapediaFourColor.JointDiamondFaceClearance

/-!
# One density law supplies the three coupled diamond reductions

The edge's two incident faces have lengths five or six; its two flanks are
pentagons. Reversing and rebasing the actual dart identifies the appropriate
existing face-pattern theorem. Under the normal-form hypotheses each supplied
pattern has its already certified strict reduction and colouring reconstruction.

This gives geometric coverage below 56 vertices in the all-five/six class,
and excludes three pentagonal incidences at any face of a vertex-minimal
counterexample in that class. Wider or less dense maps remain outside this
supply theorem. The completed Four Colour theorem is not used.
-/

namespace FourColor.DiamondGeometricSupply

open Mettapedia.GraphTheory.FourColor
open SimpleGraphDartRotation PhysicalForkCodeFaces
open GoertzelV24FaceOrbitIncidence GoertzelV24OrbitFaceCyclicOrder
open GoertzelV24OrbitFaceCurvatureBulk GoertzelV24TwoEdgeCutMinimality
open PentagonalNeighbourSupply

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance supplyEdgeFintype : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance supplyEdgeDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

variable (rotation : Data G)

/-- A disjunction of the existing geometric recognition hypotheses, with
the actual root dart retained for reconstruction. -/
def HasDiamond : Prop :=
  (∃ root, PentagonalDiamond.FaceLengths rotation root) ∨
  (∃ root, MixedDiamond.FaceLengths rotation root) ∨
  (∃ root, JointDiamond.FaceLengths rotation root)

private theorem period (d : G.Dart) (n : ℕ)
    (hn : size rotation.toRotationSystem d = n) :
    (rotation.toRotationSystem.phi ^ n) d = d := by
  have hp := (phi_isCycleOn_faceOrbit rotation.toRotationSystem d).pow_card_apply
    (rotation.toRotationSystem.mem_faceOrbit_self d)
  change (rotation.toRotationSystem.phi ^ size rotation.toRotationSystem d) d = d at hp
  simpa only [hn] using hp

private theorem mixed (hC : Cubic3 rotation.toRotationSystem) (d : G.Dart)
    (h5 : size rotation.toRotationSystem d = 5)
    (h6 : size rotation.toRotationSystem d.symm = 6)
    (hf : Flanked rotation.toRotationSystem d) :
    MixedDiamond.FaceLengths rotation d := by
  refine ⟨h5, h6, ?_⟩
  intro i hi
  rcases hi with rfl | rfl
  · exact (next_flank rotation.toRotationSystem d).trans hf.2
  · exact (last_flank rotation.toRotationSystem hC d 4 (period rotation d 5 h5)).trans hf.1

theorem classify_flanked (hC : Cubic3 rotation.toRotationSystem)
    (hs : ShortFaces rotation.toRotationSystem) (d : G.Dart)
    (hf : Flanked rotation.toRotationSystem d) : HasDiamond rotation := by
  rcases hs d with h5 | h6
  · rcases hs d.symm with ha5 | ha6
    · refine Or.inl ⟨(rotation.toRotationSystem.phi ^ 3) d, ?_⟩
      refine ⟨(size_pow rotation.toRotationSystem d 3).trans h5, ?_⟩
      intro i hlo hhi
      have hp := period rotation d 5 h5
      fin_cases i
      · norm_num at hlo
      · exact (last_flank rotation.toRotationSystem hC d 4 hp).trans hf.1
      · change size rotation.toRotationSystem
          (rotation.toRotationSystem.alpha ((rotation.toRotationSystem.phi ^ 5) d)) = 5
        simpa only [hp, rotation.toRotationSystem_alpha] using ha5
      · change size rotation.toRotationSystem
          (rotation.toRotationSystem.alpha ((rotation.toRotationSystem.phi ^ 6) d)) = 5
        have he : (rotation.toRotationSystem.phi ^ 6) d = rotation.toRotationSystem.phi d := by
          rw [show 6 = 1 + 5 from rfl, pow_add, Equiv.Perm.mul_apply, hp, pow_one]
        rw [he]
        exact (next_flank rotation.toRotationSystem d).trans hf.2
      · norm_num at hhi
    · exact Or.inr (Or.inl ⟨d, mixed rotation hC d h5 ha6 hf⟩)
  · rcases hs d.symm with ha5 | ha6
    · exact Or.inr (Or.inl ⟨d.symm, mixed rotation hC d.symm ha5 h6
        ((flanked_flip rotation.toRotationSystem d).mpr hf)⟩)
    · refine Or.inr (Or.inr ⟨d, h6, ha6, ?_⟩)
      intro i hi
      rcases hi with rfl | rfl
      · exact (next_flank rotation.toRotationSystem d).trans hf.2
      · exact (last_flank rotation.toRotationSystem hC d 5 (period rotation d 6 h6)).trans hf.1

/-- A density condition at any face supplies one of the three recognized
strict reductions. There is no specified closing seam or starting colouring. -/
theorem of_three_neighbours (hC : Cubic3 rotation.toRotationSystem)
    (hs : ShortFaces rotation.toRotationSystem) (face : OrbitFace rotation.toRotationSystem)
    (hthree : 2 < (neighbours rotation.toRotationSystem face).card) : HasDiamond rotation := by
  obtain ⟨d, hd⟩ := exists_flanked_of_three rotation.toRotationSystem hC hs face hthree
  exact classify_flanked rotation hC hs d hd

theorem of_card_lt_fiftysix (hC : Cubic3 rotation.toRotationSystem)
    (hs : ShortFaces rotation.toRotationSystem)
    (sphere : OrbitSphericalCubicMapData rotation.toRotationSystem)
    (hlt : Fintype.card V < 56) : HasDiamond rotation := by
  obtain ⟨d, hd⟩ := exists_flanked_of_card_lt_fiftysix rotation.toRotationSystem hC hs sphere hlt
  exact classify_flanked rotation hC hs d hd

/-- Every branch uses its physical replacement and smaller-map colouring.
The original catalogue certificates and complete theorem are unnecessary. -/
theorem not_in_minimal (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hd : HasDiamond rotation) : False := by
  rcases hd with ⟨d, hd⟩ | ⟨d, hd⟩ | ⟨d, hd⟩
  · exact PentagonalDiamondPatch.Tangle.FaceReduction.not_in_minimal_counterexample_of_face_pattern
      rotation d hd minimal
  · exact MixedDiamondPatch.Tangle.FaceReduction.not_in_minimal_counterexample_of_face_pattern
      rotation d hd minimal
  · exact JointDiamondPatch.Tangle.FaceClearance.not_in_minimal_counterexample_of_face_pattern
      rotation d hd minimal

theorem neighbours_le_two_of_minimal
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hs : ShortFaces rotation.toRotationSystem) (face : OrbitFace rotation.toRotationSystem) :
    (neighbours rotation.toRotationSystem face).card ≤ 2 := by
  by_contra h
  let ambient := minimal.toBridgelessSphericalCubicMapData
  exact not_in_minimal rotation minimal (of_three_neighbours rotation
    (cubic3_of _ ambient.spherical.cubic ambient.vertexRotationCyclic) hs face (by omega))

theorem fiftysix_le_vertices_of_minimal
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hs : ShortFaces rotation.toRotationSystem) : 56 ≤ Fintype.card V := by
  by_contra h
  let ambient := minimal.toBridgelessSphericalCubicMapData
  exact not_in_minimal rotation minimal (of_card_lt_fiftysix rotation
    (cubic3_of _ ambient.spherical.cubic ambient.vertexRotationCyclic)
    hs ambient.spherical (by omega))

/-- Consumer in the existing fullerene class, stated by boundary edges.
The dart-length correspondence is derived from the actual two-sided map. -/
theorem fiftysix_le_vertices_of_fullerene_minimal
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hf : OrbitFaceFullerene rotation.toRotationSystem) : 56 ≤ Fintype.card V :=
  fiftysix_le_vertices_of_minimal rotation minimal
    (shortFaces_of_fullerene rotation.toRotationSystem minimal.facesTwoSided hf)

end
end FourColor.DiamondGeometricSupply
