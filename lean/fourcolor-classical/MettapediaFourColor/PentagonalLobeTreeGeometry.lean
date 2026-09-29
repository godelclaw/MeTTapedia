import MettapediaFourColor.PentagonalLobeTangle
import Mettapedia.GraphTheory.FourColor.OpenTanglePortReplacement
import Mettapedia.GraphTheory.FourColor.OpenTangleConnectedReplacement
import Mettapedia.GraphTheory.FourColor.OpenTangleVertexReflection
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutMinimality

/-!
# Replacing the pentagonal lobe by a six-port tree

The literal sixteen-vertex patch and a four-vertex path-shaped cubic tree
have the same ordered face return and open Euler mass. Sewing either to
the same exterior therefore has the same Euler characteristic. If that
exterior is connected, the replacement preserves the connected bridgeless
spherical cubic class and removes twelve vertices from the whole map.

This file proves geometry and size. Colouring reconstruction uses the
joint exterior relation and its physical Kempe closure separately.
-/

namespace FourColor.PentagonalLobePatch.Tangle

open Mettapedia.GraphTheory.FourColor
open GoertzelV24OpenTangleComposition GoertzelV24CompositeSeamMultigraph
open GoertzelV24BoundaryEssentialGluing Multigraph
open OpenTangleMarkedFace OpenTanglePortReplacement OpenTangleReplacementEuler
open GoertzelV24CompositeSeamCubic OpenTangleVertexReflection
open GoertzelV24TwoEdgeCutMinimality PermutationFirstReturnRestriction
open ConfigurationTable

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Tree

abbrev Dart := Fin 6 ⊕ Fin 6

def index : Dart ≃ Fin 12 where
  toFun
    | .inl i => ⟨i.val, by omega⟩
    | .inr i => ⟨6 + i.val, by omega⟩
  invFun i := if h : i.val < 6 then .inl ⟨i.val, h⟩
    else .inr ⟨i.val - 6, by omega⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def vertex (d : Dart) : Fin 4 := lookup "ABBCCDAABCDD" (index d)

def rotate (s : String) (d : Dart) : Dart := index.symm (lookup s (index d))

def rho : Equiv.Perm Dart where
  toFun := rotate "GIBJDKHACELF"
  invFun := rotate "HCIEJLAGBDFK"
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alpha : Equiv.Perm (Fin 6) where
  toFun := lookup "BADCFE"
  invFun := lookup "BADCFE"
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Three internal edges form the path `0--1--2--3`. Every vertex has
at least one boundary port, and each end has two. -/
def piece : OpenTangleData (Fin 4) (Fin 6) (Fin 6) where
  interiorVert i := vertex (.inl i)
  boundaryVert i := vertex (.inr i)
  interiorAlpha := alpha
  interiorAlpha_involutive := by decide +kernel
  interiorAlpha_fixfree := by decide +kernel
  rho := rho
  vert_rho := by decide +kernel
  interior_no_self_loops := by decide +kernel
  outer := .inr 0

theorem cubic : OpenIsCubic piece := by
  unfold OpenIsCubic
  decide +kernel

theorem cyclic : OpenRotationCyclic piece := by
  unfold OpenRotationCyclic
  decide +kernel

theorem ports_surjective : Function.Surjective piece.boundaryVert := by decide +kernel

/-- Actual multigraph connectivity, independent of how edge representatives
were chosen from the dart involution. -/
theorem connected : (sideMultigraph piece).Connected := by
  have step (i : Fin 3) : (sideMultigraph piece).Step i.castSucc i.succ := by
    have hex : ∀ i : Fin 3, ∃ d : Fin 6,
        piece.interiorVert d = i.castSucc ∧
          piece.interiorVert (piece.interiorAlpha d) = i.succ := by decide +kernel
    obtain ⟨d, hd, he⟩ := hex i
    refine ⟨sideEdgeOf piece d, not_false, ?_⟩
    simpa only [hd, he] using sideMultigraph_ends piece d
  have root (i : Fin 4) : (sideMultigraph piece).Reach 0 i := by
    induction i using Fin.induction with
    | zero => exact .refl
    | succ i ih => exact ih.tail (step i)
  intro u v
  exact (reach_symm (root u)).trans (root v)

end Tree

/-- Common cyclic order, including its orientation. -/
def portCycle : Equiv.Perm (Fin 6) where
  toFun i := i + 1
  invFun i := i - 1
  left_inv := by intro i; simp
  right_inv := by intro i; simp

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

/-- The original patch's six first-return arcs have lengths `3,3,3,3,3,2`. -/
theorem piece_returnCode : returnCode piece = portCycle := by
  apply code_of_arcs piece (lookup "DDDDDC")
  decide +kernel

/-- The tree has the same first-return order, with lengths `1,2,2,2,1,4`. -/
theorem tree_returnCode : returnCode Tree.piece = portCycle := by
  apply code_of_arcs Tree.piece (lookup "BCCCBE")
  decide +kernel

/-- Six inner faces and the single boundary face of the original patch. -/
theorem piece_face_count : (openPhi piece).partition.parts.card = 7 := by decide +kernel

/-- The tree has one open face. -/
theorem tree_face_count : (openPhi Tree.piece).partition.parts.card = 1 := by decide +kernel

theorem piece_eulerMass : eulerMass piece = 4 := by
  unfold eulerMass
  rw [piece_face_count]
  norm_num

theorem tree_eulerMass : eulerMass Tree.piece = 4 := by
  unfold eulerMass
  rw [tree_face_count]
  norm_num

section Context

variable {V I B : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
  [Fintype B] [DecidableEq B]
  (outside : OpenTangleData V I B) (seam : B ≃ Fin 6)

/-- Exact Euler preservation for every fixed exterior and seam matching. -/
theorem tree_replacement_euler :
    OpenTangleRewireFaces.compositeEuler outside piece seam =
      OpenTangleRewireFaces.compositeEuler outside Tree.piece seam := by
  apply (euler_eq_iff_mass piece Tree.piece
    (piece_returnCode.trans tree_returnCode.symm) outside seam).mpr
  exact piece_eulerMass.trans tree_eulerMass.symm

/-- Exactly six faces disappear, in every exterior. -/
theorem tree_replacement_face_count :
    Fintype.card (GoertzelV24FaceOrbitIncidence.OrbitFace
      (outside.composeRotationSystem piece seam)) =
    Fintype.card (GoertzelV24FaceOrbitIncidence.OrbitFace
      (outside.composeRotationSystem Tree.piece seam)) + 6 := by
  have h := face_count_replacement piece Tree.piece
    (piece_returnCode.trans tree_returnCode.symm) outside seam
  rw [piece_face_count, tree_face_count] at h
  simp only [compositeRS_eq] at h
  have h' : Fintype.card (GoertzelV24FaceOrbitIncidence.OrbitFace
      (outside.composeRotationSystem piece seam)) + 1 =
      Fintype.card (GoertzelV24FaceOrbitIncidence.OrbitFace
        (outside.composeRotationSystem Tree.piece seam)) + 7 := by
    convert h using 2 <;> exact Fintype.card_congr (Equiv.refl _)
  omega

/-- The boundary elimination preserves cofaciality of all exterior darts. -/
theorem tree_replacement_exterior_faces (a b : I ⊕ B) :
    (outside.composeRotationSystem piece seam).phi.SameCycle
        (composeDartEquiv (.inl a)) (composeDartEquiv (.inl b)) ↔
      (outside.composeRotationSystem Tree.piece seam).phi.SameCycle
        (composeDartEquiv (.inl a)) (composeDartEquiv (.inl b)) :=
  exterior_sameCycle_iff piece Tree.piece
    (piece_returnCode.trans tree_returnCode.symm) outside seam a b

/-- The actual replacement stays in the minimality class. Connectivity of
the exterior is required; its boundary-essentiality follows from the source. -/
theorem tree_replacement_class
    (hout : (sideMultigraph outside).Connected)
    (h : BridgelessSphericalCubicMapData (outside.composeRotationSystem piece seam)) :
    BridgelessSphericalCubicMapData (outside.composeRotationSystem Tree.piece seam) := by
  have hs := OpenTangleConnectedReplacement.replacement_structural outside piece Tree.piece
    seam seam hout Tree.connected
    (OpenTangleConnectedReplacement.essential_of_surjective (sideMultigraph Tree.piece)
      (Tree.piece.boundaryVert ∘ seam) (Tree.ports_surjective.comp seam.surjective))
    ⟨h.primalConnected, h.edgeBridgeFree⟩
    (p := seam.symm 0) (q := seam.symm 1)
    (by intro he; have := seam.symm.injective he; exact (by decide : (0 : Fin 6) ≠ 1) this)
  exact {
    spherical := {
      cubic := isCubic_composeRotationSystem outside Tree.piece seam
        (exterior_isCubic outside piece seam h.spherical.cubic) Tree.cubic
      euler := by
        change OpenTangleRewireFaces.compositeEuler outside Tree.piece seam = 2
        rw [← tree_replacement_euler outside seam]
        exact h.spherical.euler }
    primalConnected := hs.1
    vertexRotationCyclic := vertexRotationCyclic_composeRotationSystem outside Tree.piece seam
      (exterior_rotationCyclic outside piece seam h.vertexRotationCyclic) Tree.cyclic
    edgeBridgeFree := hs.2 }

omit [DecidableEq V] in
/-- The whole map loses twelve vertices, including all four introduced
vertices in the replacement count. -/
theorem tree_vertex_decrease :
    Fintype.card (V ⊕ Fin 4) + 12 = Fintype.card (V ⊕ Fin 16) := by
  simp [Fintype.card_sum, Nat.add_assoc]

end Context
end FourColor.PentagonalLobePatch.Tangle
