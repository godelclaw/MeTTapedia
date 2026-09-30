import Mettapedia.GraphTheory.FourColor.PentagonalDiamondSeparation
import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalFaceSize
import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalTriangleFree

/-!
# Actual face traversal supplies the diamond's twelve distinct vertices

Only the central face and its three consecutive neighbours have specified
lengths. The face equations realize every retained edge and vertex rotation.
Girth at least five then excludes collisions, before any patch isomorphism
or exterior colouring has been assumed.
-/

namespace Mettapedia.GraphTheory.FourColor.PentagonalDiamond

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

/-- Central pentagon and three consecutive pentagonal neighbours. The two
remaining neighbouring faces are unrestricted. -/
structure FaceLengths : Prop where
  central : (rotation.toRotationSystem.faceOrbit root).card = 5
  neighbours : ∀ i : Fin 5, 1 ≤ i.val → i.val ≤ 3 →
    (rotation.toRotationSystem.faceOrbit (center rotation root i).symm).card = 5

def vertex (v : Vertex) : V := tracedVertex rotation root (embed v)
def dart (d : Slot) : G.Dart := diagramDart rotation root (embedSlot d)

variable (hC : Cubic3 rotation.toRotationSystem) (hfaces : FaceLengths rotation root)
include hC hfaces

private theorem outer_edge (i : Fin 11) (hlo : 3 ≤ i.val) (hhi : i.val ≤ 8) :
    (outerStar rotation root i 2).symm = outerStar rotation root (i + 1) 1 := by
  have hp (j : Fin 5) (hl : 1 ≤ j.val) (hh : j.val ≤ 3) :=
    FacialCoronaTraversal.pentagonal_last rotation.toRotationSystem
      (center rotation root) hC
      (center_step rotation root (period_of_face_length rotation root hfaces.central)) j
      (period_of_face_length rotation _ (hfaces.neighbours j hl hh))
  fin_cases i
  all_goals try norm_num at hlo
  all_goals try norm_num at hhi
  all_goals first
    | rfl
    | exact (hp 3 (by decide) (by decide)).symm
    | exact (hp 2 (by decide) (by decide)).symm
    | exact (hp 1 (by decide) (by decide)).symm

private theorem dart_flip (d e : Slot) (he : flip d = some e) :
    (dart rotation root d).symm = dart rotation root e := by
  have hc := center_back_edge rotation root hC
    (period_of_face_length rotation root hfaces.central)
  have h3 := outer_edge rotation root hC hfaces 3 (by decide) (by decide)
  have h4 := outer_edge rotation root hC hfaces 4 (by decide) (by decide)
  have h5 := outer_edge rotation root hC hfaces 5 (by decide) (by decide)
  have h6 := outer_edge rotation root hC hfaces 6 (by decide) (by decide)
  have h7 := outer_edge rotation root hC hfaces 7 (by decide) (by decide)
  have h8 := outer_edge rotation root hC hfaces 8 (by decide) (by decide)
  rcases d with ⟨v, s⟩
  fin_cases v <;> fin_cases s
  · change some ((11, 1) : Slot) = some e at he
    cases Option.some.inj he
    rfl
  · change none = some e at he
    cases he
  · change some ((1, 1) : Slot) = some e at he
    cases Option.some.inj he
    exact h3
  · change none = some e at he
    cases he
  · change some ((0, 2) : Slot) = some e at he
    cases Option.some.inj he
    exact (congrArg SimpleGraph.Dart.symm h3).symm
  · change some ((2, 1) : Slot) = some e at he
    cases Option.some.inj he
    exact h4
  · change some ((10, 1) : Slot) = some e at he
    cases Option.some.inj he
    rfl
  · change some ((1, 2) : Slot) = some e at he
    cases Option.some.inj he
    exact (congrArg SimpleGraph.Dart.symm h4).symm
  · change some ((3, 1) : Slot) = some e at he
    cases Option.some.inj he
    exact h5
  · change none = some e at he
    cases he
  · change some ((2, 2) : Slot) = some e at he
    cases Option.some.inj he
    exact (congrArg SimpleGraph.Dart.symm h5).symm
  · change some ((4, 1) : Slot) = some e at he
    cases Option.some.inj he
    exact h6
  · change some ((9, 1) : Slot) = some e at he
    cases Option.some.inj he
    rfl
  · change some ((3, 2) : Slot) = some e at he
    cases Option.some.inj he
    exact (congrArg SimpleGraph.Dart.symm h6).symm
  · change some ((5, 1) : Slot) = some e at he
    cases Option.some.inj he
    exact h7
  · change none = some e at he
    cases he
  · change some ((4, 2) : Slot) = some e at he
    cases Option.some.inj he
    exact (congrArg SimpleGraph.Dart.symm h7).symm
  · change some ((6, 1) : Slot) = some e at he
    cases Option.some.inj he
    exact h8
  · change some ((8, 1) : Slot) = some e at he
    cases Option.some.inj he
    rfl
  · change some ((5, 2) : Slot) = some e at he
    cases Option.some.inj he
    exact (congrArg SimpleGraph.Dart.symm h8).symm
  · change none = some e at he
    cases he
  · change some ((8, 2) : Slot) = some e at he
    cases Option.some.inj he
    exact hc 0
  · change none = some e at he
    cases he
  · change some ((11, 0) : Slot) = some e at he
    cases Option.some.inj he
    exact (congrArg SimpleGraph.Dart.symm (hc 4)).symm
  · change some ((9, 2) : Slot) = some e at he
    cases Option.some.inj he
    exact hc 1
  · change some ((6, 0) : Slot) = some e at he
    cases Option.some.inj he
    rfl
  · change some ((7, 0) : Slot) = some e at he
    cases Option.some.inj he
    exact (congrArg SimpleGraph.Dart.symm (hc 0)).symm
  · change some ((10, 2) : Slot) = some e at he
    cases Option.some.inj he
    exact hc 2
  · change some ((4, 0) : Slot) = some e at he
    cases Option.some.inj he
    rfl
  · change some ((8, 0) : Slot) = some e at he
    cases Option.some.inj he
    exact (congrArg SimpleGraph.Dart.symm (hc 1)).symm
  · change some ((11, 2) : Slot) = some e at he
    cases Option.some.inj he
    exact hc 3
  · change some ((2, 0) : Slot) = some e at he
    cases Option.some.inj he
    rfl
  · change some ((9, 0) : Slot) = some e at he
    cases Option.some.inj he
    exact (congrArg SimpleGraph.Dart.symm (hc 2)).symm
  · change some ((7, 2) : Slot) = some e at he
    cases Option.some.inj he
    exact hc 4
  · change some ((0, 0) : Slot) = some e at he
    cases Option.some.inj he
    rfl
  · change some ((10, 0) : Slot) = some e at he
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

/-- All twelve positions are distinct in an ambient graph with no triangles
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
end Mettapedia.GraphTheory.FourColor.PentagonalDiamond
