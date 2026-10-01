import Mettapedia.GraphTheory.FourColor.OpenTangleInternalReplacement
import Mettapedia.GraphTheory.FourColor.OpenTanglePortReplacement
import Mettapedia.GraphTheory.OrbitCountSplitting
import Mathlib.GroupTheory.Perm.Fin

/-!
# One ordered boundary vertex

The hub has no internal edges. Its ports occur in one prescribed cyclic
order, and its open-face return is that same order. Its Euler mass is four
at every width at least two, so it can replace a disk with the same return
and mass for geometric arguments. The hub need not be cubic.
-/

namespace Mettapedia.GraphTheory.FourColor.OpenTangleBoundaryHub

open GoertzelV24OpenTangleComposition GoertzelV24CompositeSeamCubic
open GoertzelV24CompositeSeamMultigraph GoertzelV24BoundaryEssentialGluing
open OpenTangleMarkedFace OpenTanglePortReplacement OpenTangleReplacementEuler
open GoertzelV24OrderedCutFaceReturnProfile PermutationFirstReturnRestriction
open GoertzelV24PermutationOrbitSurgery

noncomputable section
attribute [local instance] Classical.propDecidable

variable (n : ℕ) [NeZero n]

def hub : OpenTangleData Unit Empty (Fin n) where
  interiorVert := Empty.elim
  boundaryVert := fun _ => ()
  interiorAlpha := Equiv.refl Empty
  interiorAlpha_involutive := by intro d; exact nomatch d
  interiorAlpha_fixfree := by intro d; exact nomatch d
  rho := Equiv.sumCongr (Equiv.refl Empty) (finRotate n)
  vert_rho := by intro d; exact Subsingleton.elim _ _
  interior_no_self_loops := by intro d; exact nomatch d
  outer := .inr 0

@[simp] theorem rho_port (i : Fin n) : (hub n).rho (.inr i) = .inr (finRotate n i) := rfl

@[simp] theorem phi_eq_rho : openPhi (hub n) = (hub n).rho := by
  ext d
  rcases d with e | i
  · exact nomatch e
  · rfl

theorem boundary_return : returnCode (hub n) = finRotate n := by
  apply Equiv.ext
  intro i
  change SerialTangleFaceCode.boundaryCoordinate Empty (Fin n)
    (nextHitPerm (openPhi (hub n)) SerialTangleFaceTransfer.Boundary
      ⟨.inr i, trivial⟩) = _
  have hr : ReturnArc (openPhi (hub n)) SerialTangleFaceTransfer.Boundary
      (.inr i) (.inr (finRotate n i)) 1 := by
    refine ⟨by decide, ?_, ?_⟩
    · simp
    · intro k hk hlt
      omega
  exact congrArg (SerialTangleFaceCode.boundaryCoordinate Empty (Fin n))
    (nextHit_eq_of_returnArc (openPhi (hub n)) SerialTangleFaceTransfer.Boundary
      ⟨.inr i, trivial⟩ ⟨.inr (finRotate n i), trivial⟩ hr)

theorem rotation_cyclic (hn : 2 ≤ n) : OpenRotationCyclic (hub n) := by
  rintro (e | i) (f | j) _
  · exact nomatch e
  · exact nomatch e
  · exact nomatch f
  · apply sameCycle_sumCongr_inr
    apply (isCycle_finRotate_of_le hn).sameCycle
    · exact Equiv.Perm.mem_support.mp (by rw [support_finRotate_of_le hn]; exact Finset.mem_univ _)
    · exact Equiv.Perm.mem_support.mp (by rw [support_finRotate_of_le hn]; exact Finset.mem_univ _)

theorem face_count (hn : 2 ≤ n) : (openPhi (hub n)).partition.parts.card = 1 := by
  rw [← GoertzelV24FaceOrbitPartitionBridge.card_permOrbit_eq_card_partition_parts]
  change orbitCount (openPhi (hub n)) = 1
  have h := OrbitCountSplitting.orbitCount_eq_card_of_completeInvariant
    (σ := openPhi (hub n))
    (fun _ : Empty ⊕ Fin n => ())
    (fun d e => by
      constructor
      · intro _; rfl
      · intro _
        rw [phi_eq_rho]
        exact rotation_cyclic n hn d e (Subsingleton.elim _ _))
    (fun _ => ⟨.inr 0, rfl⟩)
  simpa using h

theorem euler_mass (hn : 2 ≤ n) : eulerMass (hub n) = 4 := by
  unfold eulerMass
  rw [face_count n hn]
  norm_num

theorem connected_bridgeless :
    (sideMultigraph (hub n)).Connected ∧ (sideMultigraph (hub n)).Bridgeless := by
  constructor
  · intro u v
    have : u = v := Subsingleton.elim _ _
    subst v
    exact .refl
  · intro e
    exact Empty.elim e.2.choose

end
end Mettapedia.GraphTheory.FourColor.OpenTangleBoundaryHub
