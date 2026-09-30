import MettapediaFourColor.ConfigurationTable
import Mettapedia.GraphTheory.FourColor.OpenTangleReplacementClass
import Mettapedia.GraphTheory.FourColor.PermutationFirstReturnRestriction
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# A five-vertex cubic path with seven ordered ports

Every vertex has a boundary port, and each endpoint has two. The literal
rotation has a single open face and the cyclic boundary order 0,1,...,6.
These geometric facts let the path replace larger pieces with the same
boundary return and Euler mass. No colouring certificate is used here.
-/

namespace FourColor.SevenPortTree

open Mettapedia.GraphTheory.FourColor ConfigurationTable
open GoertzelV24OpenTangleComposition GoertzelV24CompositeSeamMultigraph
open GoertzelV24BoundaryEssentialGluing.Multigraph GoertzelV24CompositeSeamCubic
open OpenTangleMarkedFace OpenTanglePortReplacement OpenTangleReplacementEuler
open PermutationFirstReturnRestriction

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

abbrev Dart := Fin 8 ⊕ Fin 7

def index : Dart ≃ Fin 15 where
  toFun
    | .inl i => ⟨i.val, by omega⟩
    | .inr i => ⟨8 + i.val, by omega⟩
  invFun i := if h : i.val < 8 then .inl ⟨i.val, h⟩
    else .inr ⟨i.val - 8, by omega⟩
  left_inv := by decide
  right_inv := by decide

def vertexCodes : String := "ABBCCDDEAABCDEE"
def rotationCodes : String := "IKBLDMFNJACEGOH"
def inverseCodes : String := "JCKELGMOAIBDFHN"
def alphaCodes : String := "BADCFEHG"

def vertex (d : Dart) : Fin 5 := lookup vertexCodes (index d)
def rotate (s : String) (d : Dart) : Dart := index.symm (lookup s (index d))

def rho : Equiv.Perm Dart where
  toFun := rotate rotationCodes
  invFun := rotate inverseCodes
  left_inv := by decide
  right_inv := by decide

def alpha : Equiv.Perm (Fin 8) where
  toFun := lookup alphaCodes
  invFun := lookup alphaCodes
  left_inv := by decide
  right_inv := by decide

/-- Four internal edges form the path 0--1--2--3--4. -/
def piece : OpenTangleData (Fin 5) (Fin 8) (Fin 7) where
  interiorVert i := vertex (.inl i)
  boundaryVert i := vertex (.inr i)
  interiorAlpha := alpha
  interiorAlpha_involutive := by decide
  interiorAlpha_fixfree := by decide
  rho := rho
  vert_rho := by decide
  interior_no_self_loops := by decide
  outer := .inr 0

theorem cubic : OpenIsCubic piece := by unfold OpenIsCubic; decide

theorem cyclic : OpenRotationCyclic piece := by unfold OpenRotationCyclic; decide

theorem ports_surjective : Function.Surjective piece.boundaryVert := by decide

theorem connected : (sideMultigraph piece).Connected := by
  have step (i : Fin 4) : (sideMultigraph piece).Step i.castSucc i.succ := by
    have hex : ∀ i : Fin 4, ∃ d : Fin 8,
        piece.interiorVert d = i.castSucc ∧
          piece.interiorVert (piece.interiorAlpha d) = i.succ := by decide
    obtain ⟨d, hd, he⟩ := hex i
    refine ⟨sideEdgeOf piece d, not_false, ?_⟩
    simpa only [hd, he] using sideMultigraph_ends piece d
  have root (i : Fin 5) : (sideMultigraph piece).Reach 0 i := by
    induction i using Fin.induction with
    | zero => exact .refl
    | succ i ih => exact ih.tail (step i)
  intro u v
  exact (reach_symm (root u)).trans (root v)

private instance boundaryDecidable {I B : Type*} (d : I ⊕ B) :
    Decidable (SerialTangleFaceTransfer.Boundary d) := by
  cases d <;> unfold SerialTangleFaceTransfer.Boundary <;> infer_instance

/-- First-return lengths 1,2,2,2,2,1,5 preserve the full boundary order. -/
theorem piece_returnCode : returnCode piece = finRotate 7 := by
  let time : Fin 7 → Fin 6 := lookup "BCCCCBF"
  have h : ∀ i : Fin 7, 0 < (time i).val ∧
      (openPhi piece ^ (time i).val) (.inr i) = .inr (i + 1) ∧
      ∀ j : Fin 6, 0 < j.val → j.val < (time i).val →
        ¬ SerialTangleFaceTransfer.Boundary ((openPhi piece ^ j.val) (.inr i)) := by decide
  apply Equiv.ext
  intro i
  rw [finRotate_apply]
  change SerialTangleFaceCode.boundaryCoordinate (Fin 8) (Fin 7)
    (GoertzelV24OrderedCutFaceReturnProfile.nextHitPerm (openPhi piece)
      SerialTangleFaceTransfer.Boundary ⟨.inr i, trivial⟩) = i + 1
  have hr : ReturnArc (openPhi piece) SerialTangleFaceTransfer.Boundary
      (.inr i) (.inr (i + 1)) (time i).val := by
    refine ⟨(h i).1, (h i).2.1, ?_⟩
    intro n hn hlt
    exact (h i).2.2 ⟨n, lt_trans hlt (time i).isLt⟩ hn hlt
  exact congrArg (SerialTangleFaceCode.boundaryCoordinate (Fin 8) (Fin 7))
    (nextHit_eq_of_returnArc (openPhi piece) SerialTangleFaceTransfer.Boundary
      ⟨.inr i, trivial⟩ ⟨.inr (i + 1), trivial⟩ hr)

theorem piece_face_count : (openPhi piece).partition.parts.card = 1 := by decide

theorem piece_eulerMass : eulerMass piece = 4 := by
  unfold eulerMass
  rw [piece_face_count]
  norm_num

end FourColor.SevenPortTree
