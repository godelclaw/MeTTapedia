import Mettapedia.GraphTheory.FourColor.MixedDiamondSeparation
import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalFaceSize
import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalTriangleFree

/-!
# Actual mixed diamond from four face lengths

A central pentagon with consecutive neighbours of lengths five, six, five
supplies every retained edge and rotation of the thirteen-vertex core.
The two remaining neighbouring faces are unrestricted. Girth excludes
collisions before any occurrence or exterior colouring is assumed.
-/

namespace Mettapedia.GraphTheory.FourColor.MixedDiamond

open _root_.SimpleGraph SimpleGraphDartRotation PhysicalForkCodeFaces
open PartialCubicDartSeparation PentagonalCoronaGeometry
open GoertzelV24TwoEdgeCutMinimality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance diamondEdgeFintype : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance diamondEdgeDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

variable (rotation : Data G) (root : G.Dart)

/-- The hexagon is at the root, flanked by two pentagons. -/
structure FaceLengths : Prop where
  central : (rotation.toRotationSystem.faceOrbit root).card = 5
  hexagonal : (rotation.toRotationSystem.faceOrbit (center rotation root 0).symm).card = 6
  pentagonal : ∀ i : Fin 5, i = 1 ∨ i = 4 →
    (rotation.toRotationSystem.faceOrbit (center rotation root i).symm).card = 5

def vertex (v : Vertex) : V := tracedVertex rotation root (embed v)
def dart (d : Slot) : G.Dart := diagramDart rotation root (embedSlot d)

variable (hC : Cubic3 rotation.toRotationSystem) (hfaces : FaceLengths rotation root)
include hC hfaces

private theorem outer_edge (i : Fin 11) (hi : i.val ≤ 2 ∨ 7 ≤ i.val) :
    (outerStar rotation root i 2).symm = outerStar rotation root (i + 1) 1 := by
  have hp (j : Fin 5) (hj : j = 1 ∨ j = 4) :=
    FacialCoronaTraversal.pentagonal_last rotation.toRotationSystem
      (center rotation root) hC
      (center_step rotation root (period_of_face_length rotation root hfaces.central)) j
      (period_of_face_length rotation _ (hfaces.pentagonal j hj))
  have hh := FacialCoronaTraversal.hexagonal_last rotation.toRotationSystem
    (center rotation root) hC
    (center_step rotation root (period_of_face_length rotation root hfaces.central)) 0
    (period_of_face_length rotation _ hfaces.hexagonal)
  fin_cases i
  all_goals try norm_num at hi
  all_goals first
    | rfl
    | exact (hp 4 (by decide)).symm
    | exact (hp 1 (by decide)).symm
    | exact hh.symm

private theorem dart_flip (d e : Slot) (he : flip d = some e) :
    (dart rotation root d).symm = dart rotation root e := by
  have hc := center_back_edge rotation root hC
    (period_of_face_length rotation root hfaces.central)
  have h0 := outer_edge rotation root hC hfaces 0 (by decide)
  have h1 := outer_edge rotation root hC hfaces 1 (by decide)
  have h2 := outer_edge rotation root hC hfaces 2 (by decide)
  have h7 := outer_edge rotation root hC hfaces 7 (by decide)
  have h8 := outer_edge rotation root hC hfaces 8 (by decide)
  have h9 := outer_edge rotation root hC hfaces 9 (by decide)
  have h10 := outer_edge rotation root hC hfaces 10 (by decide)
  rcases d with ⟨v, s⟩
  fin_cases v <;> fin_cases s
  · change some ((10, 1) : Slot) = some e at he
    cases Option.some.inj he
    rfl
  · change none = some e at he
    cases he
  · change some ((1, 1) : Slot) = some e at he
    cases Option.some.inj he
    exact h7
  · change none = some e at he
    cases he
  · change some ((0, 2) : Slot) = some e at he
    cases Option.some.inj he
    exact (congrArg SimpleGraph.Dart.symm h7).symm
  · change some ((2, 1) : Slot) = some e at he
    cases Option.some.inj he
    exact h8
  · change some ((9, 1) : Slot) = some e at he
    cases Option.some.inj he
    rfl
  · change some ((1, 2) : Slot) = some e at he
    cases Option.some.inj he
    exact (congrArg SimpleGraph.Dart.symm h8).symm
  · change some ((3, 1) : Slot) = some e at he
    cases Option.some.inj he
    exact h9
  · change none = some e at he
    cases he
  · change some ((2, 2) : Slot) = some e at he
    cases Option.some.inj he
    exact (congrArg SimpleGraph.Dart.symm h9).symm
  · change some ((4, 1) : Slot) = some e at he
    cases Option.some.inj he
    exact h10
  · change none = some e at he
    cases he
  · change some ((3, 2) : Slot) = some e at he
    cases Option.some.inj he
    exact (congrArg SimpleGraph.Dart.symm h10).symm
  · change some ((5, 1) : Slot) = some e at he
    cases Option.some.inj he
    exact h0
  · change some ((8, 1) : Slot) = some e at he
    cases Option.some.inj he
    rfl
  · change some ((4, 2) : Slot) = some e at he
    cases Option.some.inj he
    exact (congrArg SimpleGraph.Dart.symm h0).symm
  · change some ((6, 1) : Slot) = some e at he
    cases Option.some.inj he
    exact h1
  · change none = some e at he
    cases he
  · change some ((5, 2) : Slot) = some e at he
    cases Option.some.inj he
    exact (congrArg SimpleGraph.Dart.symm h1).symm
  · change some ((7, 1) : Slot) = some e at he
    cases Option.some.inj he
    exact h2
  · change some ((12, 1) : Slot) = some e at he
    cases Option.some.inj he
    rfl
  · change some ((6, 2) : Slot) = some e at he
    cases Option.some.inj he
    exact (congrArg SimpleGraph.Dart.symm h2).symm
  · change none = some e at he
    cases he
  · change some ((9, 2) : Slot) = some e at he
    cases Option.some.inj he
    exact hc 0
  · change some ((5, 0) : Slot) = some e at he
    cases Option.some.inj he
    rfl
  · change some ((12, 0) : Slot) = some e at he
    cases Option.some.inj he
    exact (congrArg SimpleGraph.Dart.symm (hc 4)).symm
  · change some ((10, 2) : Slot) = some e at he
    cases Option.some.inj he
    exact hc 1
  · change some ((2, 0) : Slot) = some e at he
    cases Option.some.inj he
    rfl
  · change some ((8, 0) : Slot) = some e at he
    cases Option.some.inj he
    exact (congrArg SimpleGraph.Dart.symm (hc 0)).symm
  · change some ((11, 2) : Slot) = some e at he
    cases Option.some.inj he
    exact hc 2
  · change some ((0, 0) : Slot) = some e at he
    cases Option.some.inj he
    rfl
  · change some ((9, 0) : Slot) = some e at he
    cases Option.some.inj he
    exact (congrArg SimpleGraph.Dart.symm (hc 1)).symm
  · change some ((12, 2) : Slot) = some e at he
    cases Option.some.inj he
    exact hc 3
  · change none = some e at he
    cases he
  · change some ((10, 0) : Slot) = some e at he
    cases Option.some.inj he
    exact (congrArg SimpleGraph.Dart.symm (hc 2)).symm
  · change some ((8, 2) : Slot) = some e at he
    cases Option.some.inj he
    exact hc 4
  · change some ((7, 0) : Slot) = some e at he
    cases Option.some.inj he
    rfl
  · change some ((11, 0) : Slot) = some e at he
    cases Option.some.inj he
    exact (congrArg SimpleGraph.Dart.symm (hc 3)).symm

/-- The interpretation retains the actual source darts and their operations. -/
def realization : Realization diagram G where
  vertex := vertex rotation root
  dart := dart rotation root
  fst d := diagramDart_fst rotation root (embedSlot d)
  slots_injective v := by
    change Function.Injective (fun s => diagramDart rotation root (embed v, s))
    cases h : embed v with
    | inl i => exact outerStar_injective rotation root hC i
    | inr i => exact innerStar_injective rotation root hC i
  slots_surjective v d hd := diagramDart_surjective_at rotation root hC (embed v) d hd
  rotation := rotation.vertexRotation
  rotate_eq d := by
    change diagramDart rotation root (embedSlot (rotate d)) = _
    rw [embed_rotate]
    exact diagramDart_rotation rotation root hC (embedSlot d)
  flip_eq := dart_flip rotation root hC hfaces

/-- All thirteen positions are distinct in an ambient graph with no triangles
or four-cycles, independently of the other neighbouring face lengths. -/
theorem vertex_injective_of_girth
    (ht : Realization.TriangleFree (G := G))
    (hf : Realization.FourCycleFree (G := G)) :
    Function.Injective (vertex rotation root) :=
  vertex_injective (realization rotation root hC hfaces) ht hf

omit hC in
/-- Minimality supplies both required girth restrictions. -/
theorem vertex_injective_of_minimality
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation) :
    Function.Injective (vertex rotation root) := by
  apply vertex_injective_of_girth rotation root
    (cubic3_of rotation.toRotationSystem minimal.spherical.cubic minimal.vertexRotationCyclic) hfaces
  · intro a b c hab hbc hca
    exact GoertzelV24MinimalTriangleFree.no_common_neighbor_of_vertexMinimalTaitCounterexample
      rotation minimal hab c hca.symm hbc
  · exact fun _ _ _ _ =>
      GoertzelV24MinimalFaceSize.no_fourCycle_of_vertexMinimalTaitCounterexample rotation minimal

end
end Mettapedia.GraphTheory.FourColor.MixedDiamond
