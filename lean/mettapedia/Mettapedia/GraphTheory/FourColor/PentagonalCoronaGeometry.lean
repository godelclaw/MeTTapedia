import Mettapedia.GraphTheory.FourColor.FacialCoronaTraversal
import Mettapedia.GraphTheory.FourColor.ElevenLobeSpokeOrder
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceCyclicOrder

/-!
# Constructing an eleven-lobe from six actual faces

A central pentagon has four pentagonal neighbours and one hexagonal
neighbour. Actual face traversal constructs the eleven outer vertices,
their edges, the alternating turns and the five inner attachments.
Distinctness of the sixteen traced vertices and absence of outer chords
are retained as explicit geometric conditions.
-/

namespace Mettapedia.GraphTheory.FourColor.PentagonalCoronaGeometry

open SimpleGraph SimpleGraphDartRotation PhysicalForkCodeFaces
open CubicCycleIncidence ElevenLobeSpokeOrder Equiv Equiv.Perm
open GoertzelV24OrbitFaceCyclicOrder

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance coronaEdgeFintype : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance coronaEdgeDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

variable (rotation : Data G) (root : G.Dart)

def center (i : Fin 5) : G.Dart := (rotation.toRotationSystem.phi ^ i.val) root

abbrev incoming (i : Fin 5) : G.Dart :=
  FacialCoronaTraversal.incoming rotation.toRotationSystem (center rotation root) i

abbrev first (i : Fin 5) : G.Dart :=
  FacialCoronaTraversal.first rotation.toRotationSystem (center rotation root) i

/-- Each base dart is obtained by crossing an edge already traced from the
central face. The extra vertex in the hexagon occupies the closing gap. -/
def outerBase : Fin 11 → G.Dart
  | 0 => (first rotation root 0).symm
  | 1 => incoming rotation root 0
  | 2 => (first rotation root 4).symm
  | 3 => incoming rotation root 4
  | 4 => (first rotation root 3).symm
  | 5 => incoming rotation root 3
  | 6 => (first rotation root 2).symm
  | 7 => incoming rotation root 2
  | 8 => (first rotation root 1).symm
  | 9 => incoming rotation root 1
  | 10 => (rotation.toRotationSystem.phi (first rotation root 0)).symm

def outerVertex (i : Fin 11) : V := (outerBase rotation root i).fst

def tracedVertex : Fin 11 ⊕ Fin 5 → V
  | .inl i => outerVertex rotation root i
  | .inr i => (center rotation root i).fst

/-- Slots retain the joint boundary information: spoke, previous, next. -/
def outerStar (i : Fin 11) (s : Fin 3) : G.Dart :=
  if reverseAt i then
    match s with
    | 0 => rotation.vertexRotation (rotation.vertexRotation (outerBase rotation root i))
    | 1 => rotation.vertexRotation (outerBase rotation root i)
    | 2 => outerBase rotation root i
  else
    match s with
    | 0 => outerBase rotation root i
    | 1 => rotation.vertexRotation (outerBase rotation root i)
    | 2 => rotation.vertexRotation (rotation.vertexRotation (outerBase rotation root i))

theorem outerStar_fst (i : Fin 11) (s : Fin 3) :
    (outerStar rotation root i s).fst = outerVertex rotation root i := by
  cases h : reverseAt i <;> fin_cases s <;>
    simp [outerStar, h, outerVertex, rotation.vertexRotation_fst]

theorem outerStar_rotation (hC : Cubic3 rotation.toRotationSystem)
    (d : CycleBoundaryOrientation.Dart 11) :
    rotation.vertexRotation (outerStar rotation root d.1 d.2) =
      outerStar rotation root (CycleBoundaryOrientation.turn 11 reverseAt d).1
        (CycleBoundaryOrientation.turn 11 reverseAt d).2 := by
  rcases d with ⟨i, s⟩
  cases h : reverseAt i <;> fin_cases s <;>
    simp [outerStar, CycleBoundaryOrientation.turn, h]
  all_goals exact hC.cube _

theorem center_step
    (hroot : (rotation.toRotationSystem.phi ^ 5) root = root) (i : Fin 5) :
    rotation.toRotationSystem.phi (center rotation root i) = center rotation root (i + 1) := by
  fin_cases i <;> first | rfl | exact hroot

/-- The periods are consequences of the five neighbouring face lengths.
Only the actual face permutation is used. -/
def NeighborPeriods : Prop := ∀ i : Fin 5,
  (rotation.toRotationSystem.phi ^ (if i = 0 then 6 else 5)) (center rotation root i).symm =
    (center rotation root i).symm

/-- The neighbouring hexagon is selected by the root edge. All remaining
neighbours have length five in the actual rotation system. -/
structure FaceLengths : Prop where
  central : (rotation.toRotationSystem.faceOrbit root).card = 5
  neighbours : ∀ i : Fin 5,
    (rotation.toRotationSystem.faceOrbit (center rotation root i).symm).card =
      if i = 0 then 6 else 5

theorem period_of_face_length (d : G.Dart) {n : ℕ}
    (h : (rotation.toRotationSystem.faceOrbit d).card = n) :
    (rotation.toRotationSystem.phi ^ n) d = d := by
  have he := (phi_isCycleOn_faceOrbit rotation.toRotationSystem d).pow_card_apply
    (rotation.toRotationSystem.mem_faceOrbit_self d)
  simpa only [h] using he

theorem FaceLengths.central_period (h : FaceLengths rotation root) :
    (rotation.toRotationSystem.phi ^ 5) root = root :=
  period_of_face_length rotation root h.central

theorem FaceLengths.neighbour_periods (h : FaceLengths rotation root) :
    NeighborPeriods rotation root :=
  fun i => period_of_face_length rotation _ (h.neighbours i)

theorem outerStar_edge (hC : Cubic3 rotation.toRotationSystem)
    (hroot : (rotation.toRotationSystem.phi ^ 5) root = root)
    (hn : NeighborPeriods rotation root) (i : Fin 11) :
    (outerStar rotation root i 2).symm = outerStar rotation root (i + 1) 1 := by
  have hp (j : Fin 5) (hj : j ≠ 0) :=
    FacialCoronaTraversal.pentagonal_last rotation.toRotationSystem
      (center rotation root) hC (center_step rotation root hroot) j
      (by simpa [NeighborPeriods, hj] using hn j)
  have hh := FacialCoronaTraversal.hexagonal_last rotation.toRotationSystem
      (center rotation root) hC (center_step rotation root hroot) 0
      (by simpa [NeighborPeriods] using hn 0)
  fin_cases i
  all_goals
    first
    | exact (hp 4 (by decide)).symm
    | exact (hp 3 (by decide)).symm
    | exact (hp 2 (by decide)).symm
    | exact (hp 1 (by decide)).symm
    | exact hh.symm
    | rfl

end
end Mettapedia.GraphTheory.FourColor.PentagonalCoronaGeometry
