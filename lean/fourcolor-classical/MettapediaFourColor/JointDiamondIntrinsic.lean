import MettapediaFourColor.JointDiamondTangle
import Mettapedia.GraphTheory.FourColor.OpenTanglePortReplacement
import Mettapedia.GraphTheory.FourColor.OpenTangleReplacementEuler
import Mettapedia.GraphTheory.FourColor.OpenTangleVertexReflection

/-!
# Intrinsic geometry of the eight-port joint diamond

The actual finite piece is connected, has one ordered boundary-return cycle,
and has Euler mass four. These are incidence and face geometry checks; its
colour repair continues to use the integrated shared diamond proof.
-/

namespace FourColor.JointDiamondPatch.Tangle

open Mettapedia.GraphTheory.FourColor
open GoertzelV24OpenTangleComposition GoertzelV24CompositeSeamMultigraph
open GoertzelV24BoundaryEssentialGluing Multigraph
open OpenTangleMarkedFace OpenTanglePortReplacement OpenTangleReplacementEuler
open GoertzelV24CompositeSeamCubic OpenTangleVertexReflection
open GoertzelV24TwoEdgeCutMinimality PermutationFirstReturnRestriction
open ConfigurationTable

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def vertexOrder : Fin 14 ≃ Fin 14 where
  toFun := lookup "ABHEGMCNFKDLJI"
  invFun := lookup "ABGKDIECNMJLFH"
  left_inv := by decide
  right_inv := by decide

theorem piece_connected : (sideMultigraph piece).Connected := by
  have down : ∀ v : Fin 14, v ≠ 0 → ∃ i : Fin 34,
      piece.interiorVert i = vertexOrder v ∧
        vertexOrder.symm (piece.interiorVert (piece.interiorAlpha i)) < v := by decide
  have root (v : Fin 14) : (sideMultigraph piece).Reach (vertexOrder v) (vertexOrder 0) := by
    induction v using Fin.strong_induction_on with
    | h v ih =>
      by_cases hv : v = 0
      · subst v; exact .refl
      · obtain ⟨i, hi, hj⟩ := down v hv
        have hs : (sideMultigraph piece).Step (vertexOrder v)
            (piece.interiorVert (piece.interiorAlpha i)) := by
          refine ⟨sideEdgeOf piece i, not_false, ?_⟩
          simpa only [hi] using sideMultigraph_ends piece i
        have hr := ih _ hj
        rw [Equiv.apply_symm_apply] at hr
        exact (Relation.ReflTransGen.single hs).trans hr
  intro u v
  change Relation.ReflTransGen (sideMultigraph piece).Step u v
  simpa only [Equiv.apply_symm_apply] using
    (root (vertexOrder.symm u)).trans (reach_symm (root (vertexOrder.symm v)))

private instance boundaryDecidable {I B : Type*} (d : I ⊕ B) :
    Decidable (SerialTangleFaceTransfer.Boundary d) := by
  cases d <;> unfold SerialTangleFaceTransfer.Boundary <;> infer_instance

private theorem code_of_arcs {V I : Type*} [Fintype I] [DecidableEq I]
    (T : OpenTangleData V I (Fin 8)) (time : Fin 8 → Fin 5)
    (h : ∀ i, 0 < (time i).val ∧
      (openPhi T ^ (time i).val) (.inr i) = .inr (i + 1) ∧
      ∀ j : Fin 5, 0 < j.val → j.val < (time i).val →
        ¬ SerialTangleFaceTransfer.Boundary ((openPhi T ^ j.val) (.inr i))) :
    returnCode T = finRotate 8 := by
  apply Equiv.ext
  intro i
  rw [finRotate_apply]
  change SerialTangleFaceCode.boundaryCoordinate I (Fin 8)
    (GoertzelV24OrderedCutFaceReturnProfile.nextHitPerm (openPhi T)
      SerialTangleFaceTransfer.Boundary ⟨.inr i, trivial⟩) = i + 1
  have hr : ReturnArc (openPhi T) SerialTangleFaceTransfer.Boundary
      (.inr i) (.inr (i + 1)) (time i).val := by
    refine ⟨(h i).1, (h i).2.1, ?_⟩
    intro n hn hlt
    exact (h i).2.2 ⟨n, lt_trans hlt (time i).isLt⟩ hn hlt
  exact congrArg (SerialTangleFaceCode.boundaryCoordinate I (Fin 8))
    (nextHit_eq_of_returnArc (openPhi T) SerialTangleFaceTransfer.Boundary
      ⟨.inr i, trivial⟩ ⟨.inr (i + 1), trivial⟩ hr)

/-- The eight first-return arcs have lengths 2,3,2,3,2,3,2,3. -/
theorem piece_returnCode : returnCode piece = finRotate 8 := by
  apply code_of_arcs piece (lookup "CDCDCDCD")
  decide

theorem piece_face_count : (openPhi piece).partition.parts.card = 5 := by decide

theorem piece_eulerMass : eulerMass piece = 4 := by
  unfold eulerMass
  rw [piece_face_count]
  norm_num


end FourColor.JointDiamondPatch.Tangle
