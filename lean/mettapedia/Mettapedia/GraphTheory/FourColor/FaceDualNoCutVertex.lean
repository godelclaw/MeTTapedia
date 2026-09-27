import Mettapedia.GraphTheory.FourColor.FaceRegionPatch
import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicFaceBoundaryCycleRigidity

/-!
# Deleting a face leaves the actual facial dual connected

In a graph-backed bridgeless spherical cubic map every facial boundary is
a simple primal cycle. The facial-bond theorem therefore makes the other
faces connected in the dual. This supplies the vertex-deletion hypothesis
for connected bipartition growth without assuming a dual connectivity class.
-/

namespace Mettapedia.GraphTheory.FourColor.FaceDualNoCutVertex

open GoertzelV24FaceOrbitIncidence GoertzelV24OrbitFaceTwoSided
open GoertzelV24PrimalCycleFacialBond GoertzelV24TwoEdgeCutMinimality
open GoertzelV24BridgelessFaceTwoSided SimpleGraphDartRotation

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The facial dual has no cut vertex, on its original quotient-face carrier. -/
theorem delete_face_connected (data : Data G)
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    (f : OrbitFace data.toRotationSystem) :
    ((orbitFaceDualGraph data).induce ({f} : Set _)ᶜ).Connected := by
  have htwo := BridgelessSphericalCubicMapData.orbitFacesTwoSided
    data.toRotationSystem ambient
  obtain ⟨d, hd⟩ := exists_dartOrbitFace_eq data.toRotationSystem f
  obtain ⟨cycle, hc, _, he⟩ := exists_rootedFaceCycle data ambient.spherical.cubic htwo d
  have hseparator (e : data.toRotationSystem.D) :
      (data.toRotationSystem.edgeOf e).val ∈ cycle.edges ↔
        ((dartOrbitFace data.toRotationSystem e ∈ ({f} : Finset _) ∧
            dartOrbitFace data.toRotationSystem (data.toRotationSystem.alpha e) ∉ ({f} : Finset _)) ∨
          (dartOrbitFace data.toRotationSystem e ∉ ({f} : Finset _) ∧
            dartOrbitFace data.toRotationSystem (data.toRotationSystem.alpha e) ∈ ({f} : Finset _))) := by
    rw [he, hd]
    have hh := FaceRegionDegree.edge_mem_iff data.toRotationSystem {f} e
    simp only [FaceRegionDegree.edges, Finset.singleton_biUnion, Finset.mem_singleton] at hh ⊢
    rw [hh]
    have hn := htwo e
    have hnot : ¬ (dartOrbitFace data.toRotationSystem e = f ∧
        dartOrbitFace data.toRotationSystem (data.toRotationSystem.alpha e) = f) :=
      fun h => hn (h.1.trans h.2.symm)
    tauto
  have hh := (face_sides_connected_of_isCycle data ambient htwo cycle hc {f} hseparator).2
  have hset : ({g | g ∉ ({f} : Finset _)} : Set _) = ({f} : Set _)ᶜ := by
    ext g
    simp
  rw [hset] at hh
  exact hh

end
end Mettapedia.GraphTheory.FourColor.FaceDualNoCutVertex
