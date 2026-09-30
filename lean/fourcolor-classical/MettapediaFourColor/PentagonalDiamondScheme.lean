import MettapediaFourColor.PentagonalDiamondTangle
import MettapediaFourColor.SixPortTreeReplacement

/-!
# The diamond instantiates the shared six-port replacement law

The finite checks here certify incidence, boundary first returns and Euler
mass. Colour repair is inherited from the integrated diamond profile proof.
The replacement removes twelve vertices and introduces the same four-vertex
tree, for a net decrease of eight.
-/

namespace FourColor.PentagonalDiamondPatch.Tangle

open Mettapedia.GraphTheory.FourColor
open GoertzelV24OpenTangleComposition GoertzelV24CompositeSeamMultigraph
open GoertzelV24BoundaryEssentialGluing Multigraph
open OpenTangleMarkedFace OpenTanglePortReplacement OpenTangleReplacementEuler
open GoertzelV24CompositeSeamCubic OpenTangleVertexReflection
open GoertzelV24TwoEdgeCutMinimality PermutationFirstReturnRestriction
open ConfigurationTable
open PentagonalLobePatch.Tangle (portCycle)

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def vertexOrder : Fin 12 ≃ Fin 12 where
  toFun := lookup "ABLCHKDIJEGF"
  invFun := lookup "ABDGJLKEHIFC"
  left_inv := by decide
  right_inv := by decide

theorem piece_connected : (sideMultigraph piece).Connected := by
  have down : ∀ v : Fin 12, v ≠ 0 → ∃ i : Fin 30,
      piece.interiorVert i = vertexOrder v ∧
        vertexOrder.symm (piece.interiorVert (piece.interiorAlpha i)) < v := by decide
  have root (v : Fin 12) : (sideMultigraph piece).Reach (vertexOrder v) (vertexOrder 0) := by
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
    (T : OpenTangleData V I (Fin 6)) (time : Fin 6 → Fin 5)
    (h : ∀ i, 0 < (time i).val ∧
      (openPhi T ^ (time i).val) (.inr i) = .inr (i + 1) ∧
      ∀ j : Fin 5, 0 < j.val → j.val < (time i).val →
        ¬ SerialTangleFaceTransfer.Boundary ((openPhi T ^ j.val) (.inr i))) :
    returnCode T = portCycle := by
  apply Equiv.ext
  intro i
  change SerialTangleFaceCode.boundaryCoordinate I (Fin 6)
    (GoertzelV24OrderedCutFaceReturnProfile.nextHitPerm (openPhi T)
      SerialTangleFaceTransfer.Boundary ⟨.inr i, trivial⟩) = i + 1
  have hr : ReturnArc (openPhi T) SerialTangleFaceTransfer.Boundary
      (.inr i) (.inr (i + 1)) (time i).val := by
    refine ⟨(h i).1, (h i).2.1, ?_⟩
    intro n hn hlt
    exact (h i).2.2 ⟨n, lt_trans hlt (time i).isLt⟩ hn hlt
  exact congrArg (SerialTangleFaceCode.boundaryCoordinate I (Fin 6))
    (nextHit_eq_of_returnArc (openPhi T) SerialTangleFaceTransfer.Boundary
      ⟨.inr i, trivial⟩ ⟨.inr (i + 1), trivial⟩ hr)

/-- The six first-return arcs have lengths 2,3,3,2,3,3. -/
theorem piece_returnCode : returnCode piece = portCycle := by
  apply code_of_arcs piece (lookup "CDDCDD")
  decide

theorem piece_face_count : (openPhi piece).partition.parts.card = 5 := by decide

theorem piece_eulerMass : eulerMass piece = 4 := by
  unfold eulerMass
  rw [piece_face_count]
  norm_num

/-- Actual interior witnesses interpret the previously proved repair. -/
theorem open_repair : KempeBoundarySplit.Repairs
    (PentagonalLobePatch.Tangle.OpenTrace piece (Equiv.refl _)) 6 := by
  intro et hlen hzero hsum Q hQ hold
  obtain ⟨k, hk⟩ := compatible_colouring hQ et hlen hzero hsum hold
  exact ⟨trace (boundary.map k), ⟨colouring k, colouring_valid k, boundary_colouring k⟩, hk⟩

def scheme : SixPortTreeReplacement.Scheme 12 30 where
  piece := piece
  size := by decide
  connected := piece_connected
  return_eq := piece_returnCode
  euler_eq := piece_eulerMass
  repair := open_repair

end FourColor.PentagonalDiamondPatch.Tangle
