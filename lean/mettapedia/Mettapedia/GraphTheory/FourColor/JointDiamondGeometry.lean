import Mettapedia.GraphTheory.FourColor.JointDiamondSeparation
import Mettapedia.GraphTheory.FourColor.CubicDartStar
import Mettapedia.GraphTheory.FourColor.FacialCoronaTraversal
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceCyclicOrder

/-!
# Actual traversal of the joint diamond

A central hexagon, its hexagonal neighbour across the root edge, and the
pentagons on the two flanks determine the whole partial cubic diagram.
Every dart below is an actual ambient dart. Four face periods prove all
seventeen internal edges. No injectivity or absence of boundary chords is
assumed by the traversal.
-/

namespace Mettapedia.GraphTheory.FourColor.JointDiamond

open _root_.SimpleGraph SimpleGraphDartRotation PhysicalForkCodeFaces
open PartialCubicDartSeparation GoertzelV24OrbitFaceCyclicOrder

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance jointEdgeFintype : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance jointEdgeDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

variable (rotation : Data G) (root : G.Dart)

def center (i : Fin 6) : G.Dart := (rotation.toRotationSystem.phi ^ i.val) root

abbrev incoming (i : Fin 6) : G.Dart :=
  FacialCoronaTraversal.incoming rotation.toRotationSystem (center rotation root) i

abbrev first (i : Fin 6) : G.Dart :=
  FacialCoronaTraversal.first rotation.toRotationSystem (center rotation root) i

structure FaceLengths : Prop where
  central : (rotation.toRotationSystem.faceOrbit root).card = 6
  hexagonal : (rotation.toRotationSystem.faceOrbit root.symm).card = 6
  pentagonal : ∀ i : Fin 6, i = 1 ∨ i = 5 →
    (rotation.toRotationSystem.faceOrbit (center rotation root i).symm).card = 5

def base : Vertex → G.Dart
  | 0 => center rotation root 3
  | 1 => rotation.vertexRotation (rotation.vertexRotation (center rotation root 4))
  | 2 => first rotation root 5
  | 3 => rotation.vertexRotation (rotation.vertexRotation
      (rotation.toRotationSystem.phi (first rotation root 5)))
  | 4 => rotation.vertexRotation (rotation.vertexRotation (center rotation root 5))
  | 5 => rotation.toRotationSystem.phi (first rotation root 1)
  | 6 => rotation.vertexRotation (rotation.vertexRotation (incoming rotation root 2))
  | 7 => rotation.vertexRotation (center rotation root 2)
  | 8 => rotation.toRotationSystem.phi (first rotation root 0)
  | 9 => rotation.vertexRotation (rotation.vertexRotation
      (rotation.toRotationSystem.phi (rotation.toRotationSystem.phi (first rotation root 0))))
  | 10 => rotation.vertexRotation (rotation.vertexRotation (incoming rotation root 1))
  | 11 => rotation.vertexRotation (rotation.vertexRotation (incoming rotation root 0))
  | 12 => rotation.vertexRotation (center rotation root 1)
  | 13 => rotation.vertexRotation (rotation.vertexRotation (center rotation root 0))

def vertex (v : Vertex) : V := (base rotation root v).fst
def dart (d : Slot) : G.Dart := CubicDartStar.star rotation (base rotation root d.1) d.2

variable (hC : Cubic3 rotation.toRotationSystem) (hfaces : FaceLengths rotation root)
include hC hfaces

omit hC hfaces in
private theorem period (d : G.Dart) {n : ℕ}
    (h : (rotation.toRotationSystem.faceOrbit d).card = n) :
    (rotation.toRotationSystem.phi ^ n) d = d := by
  have he := (phi_isCycleOn_faceOrbit rotation.toRotationSystem d).pow_card_apply
    (rotation.toRotationSystem.mem_faceOrbit_self d)
  simpa only [h] using he

omit hC in
private theorem center_step (i : Fin 6) :
    rotation.toRotationSystem.phi (center rotation root i) = center rotation root (i + 1) := by
  have hroot := period rotation root hfaces.central
  fin_cases i <;> first | rfl | exact hroot

omit hfaces in
private theorem back (d : G.Dart) : d.symm =
    rotation.vertexRotation (rotation.vertexRotation (rotation.toRotationSystem.phi d)) :=
  (hC.cube d.symm).symm

private theorem center_back (i : Fin 6) : (center rotation root i).symm =
    rotation.vertexRotation (rotation.vertexRotation (center rotation root (i + 1))) := by
  rw [← center_step rotation root hfaces i]
  exact back rotation hC _

private theorem pentagon_last (i : Fin 6) (hi : i = 1 ∨ i = 5) :
    rotation.toRotationSystem.phi (first rotation root i) =
      (rotation.vertexRotation (rotation.vertexRotation (incoming rotation root (i + 1)))).symm := by
  exact FacialCoronaTraversal.pentagonal_last rotation.toRotationSystem
    (center rotation root) hC (center_step rotation root hfaces) i
    (period rotation _ (hfaces.pentagonal i hi))

private theorem hexagon_last :
    rotation.toRotationSystem.phi (rotation.toRotationSystem.phi (first rotation root 0)) =
      (rotation.vertexRotation (rotation.vertexRotation (incoming rotation root 1))).symm := by
  exact FacialCoronaTraversal.hexagonal_last rotation.toRotationSystem
    (center rotation root) hC (center_step rotation root hfaces) 0
    (period rotation _ hfaces.hexagonal)

private theorem dart_flip (d e : Slot) (he : flip d = some e) :
    (dart rotation root d).symm = dart rotation root e := by
  have hc : ∀ d : G.Dart,
      rotation.vertexRotation (rotation.vertexRotation (rotation.vertexRotation d)) = d := hC.cube
  have hb := back rotation hC
  have hcentral := center_back rotation root hC hfaces
  have hp1 := pentagon_last rotation root hC hfaces 1 (by decide)
  have hp5 := pentagon_last rotation root hC hfaces 5 (by decide)
  have hh := hexagon_last rotation root hC hfaces
  rcases d with ⟨v, s⟩
  fin_cases v <;> fin_cases s
  · change some ((1, 0) : Slot) = some e at he
    cases Option.some.inj he
    simpa only [dart, base, CubicDartStar.star, hc, SimpleGraph.Dart.symm_symm, Fin.reduceAdd, first, incoming,
      FacialCoronaTraversal.first, FacialCoronaTraversal.incoming,
      Data.toRotationSystem_rho, Data.toRotationSystem_alpha, hc, SimpleGraph.Dart.symm_symm] using
      hcentral 3
  · change none = some e at he
    cases he
  · change some ((7, 2) : Slot) = some e at he
    cases Option.some.inj he
    simpa only [dart, base, CubicDartStar.star, hc, SimpleGraph.Dart.symm_symm, Fin.reduceAdd, first, incoming,
      FacialCoronaTraversal.first, FacialCoronaTraversal.incoming,
      Data.toRotationSystem_rho, Data.toRotationSystem_alpha, hc, SimpleGraph.Dart.symm_symm] using
      (congrArg SimpleGraph.Dart.symm (hcentral 2)).symm
  · change some ((0, 0) : Slot) = some e at he
    cases Option.some.inj he
    simpa only [dart, base, CubicDartStar.star, hc, SimpleGraph.Dart.symm_symm, Fin.reduceAdd, first, incoming,
      FacialCoronaTraversal.first, FacialCoronaTraversal.incoming,
      Data.toRotationSystem_rho, Data.toRotationSystem_alpha, hc, SimpleGraph.Dart.symm_symm] using
      (congrArg SimpleGraph.Dart.symm (hcentral 3)).symm
  · change some ((4, 0) : Slot) = some e at he
    cases Option.some.inj he
    simpa only [dart, base, CubicDartStar.star, hc, SimpleGraph.Dart.symm_symm, Fin.reduceAdd, first, incoming,
      FacialCoronaTraversal.first, FacialCoronaTraversal.incoming,
      Data.toRotationSystem_rho, Data.toRotationSystem_alpha, hc, SimpleGraph.Dart.symm_symm] using
      hcentral 4
  · change none = some e at he
    cases he
  · change some ((3, 0) : Slot) = some e at he
    cases Option.some.inj he
    simpa only [dart, base, CubicDartStar.star, hc, SimpleGraph.Dart.symm_symm, Fin.reduceAdd, first, incoming,
      FacialCoronaTraversal.first, FacialCoronaTraversal.incoming,
      Data.toRotationSystem_rho, Data.toRotationSystem_alpha, hc, SimpleGraph.Dart.symm_symm] using
      hb (first rotation root 5)
  · change none = some e at he
    cases he
  · change some ((4, 2) : Slot) = some e at he
    cases Option.some.inj he
    simp only [dart, base, CubicDartStar.star, first,
      FacialCoronaTraversal.incoming, FacialCoronaTraversal.first, SimpleGraph.Dart.symm_symm, first,
      FacialCoronaTraversal.first, FacialCoronaTraversal.incoming,
      Data.toRotationSystem_rho, Data.toRotationSystem_alpha, hc, SimpleGraph.Dart.symm_symm]
  · change some ((2, 0) : Slot) = some e at he
    cases Option.some.inj he
    simpa only [dart, base, CubicDartStar.star, hc, SimpleGraph.Dart.symm_symm, Fin.reduceAdd, first, incoming,
      FacialCoronaTraversal.first, FacialCoronaTraversal.incoming,
      Data.toRotationSystem_rho, Data.toRotationSystem_alpha, hc, SimpleGraph.Dart.symm_symm] using
      (congrArg SimpleGraph.Dart.symm (hb (first rotation root 5))).symm
  · change some ((11, 0) : Slot) = some e at he
    cases Option.some.inj he
    simpa only [dart, base, CubicDartStar.star, hc, SimpleGraph.Dart.symm_symm, Fin.reduceAdd, first, incoming,
      FacialCoronaTraversal.first, FacialCoronaTraversal.incoming,
      Data.toRotationSystem_rho, Data.toRotationSystem_alpha, hc, SimpleGraph.Dart.symm_symm] using
      congrArg SimpleGraph.Dart.symm hp5
  · change none = some e at he
    cases he
  · change some ((1, 1) : Slot) = some e at he
    cases Option.some.inj he
    simpa only [dart, base, CubicDartStar.star, hc, SimpleGraph.Dart.symm_symm, Fin.reduceAdd, first, incoming,
      FacialCoronaTraversal.first, FacialCoronaTraversal.incoming,
      Data.toRotationSystem_rho, Data.toRotationSystem_alpha, hc, SimpleGraph.Dart.symm_symm] using
      (congrArg SimpleGraph.Dart.symm (hcentral 4)).symm
  · change some ((13, 0) : Slot) = some e at he
    cases Option.some.inj he
    simpa only [dart, base, CubicDartStar.star, hc, SimpleGraph.Dart.symm_symm, Fin.reduceAdd, first, incoming,
      FacialCoronaTraversal.first, FacialCoronaTraversal.incoming,
      Data.toRotationSystem_rho, Data.toRotationSystem_alpha, hc, SimpleGraph.Dart.symm_symm] using
      hcentral 5
  · change some ((2, 2) : Slot) = some e at he
    cases Option.some.inj he
    simp only [dart, base, CubicDartStar.star, first,
      FacialCoronaTraversal.incoming, FacialCoronaTraversal.first, first,
      FacialCoronaTraversal.first, FacialCoronaTraversal.incoming,
      Data.toRotationSystem_rho, Data.toRotationSystem_alpha, hc]
  · change some ((6, 0) : Slot) = some e at he
    cases Option.some.inj he
    simpa only [dart, base, CubicDartStar.star, hc, SimpleGraph.Dart.symm_symm, Fin.reduceAdd, first, incoming,
      FacialCoronaTraversal.first, FacialCoronaTraversal.incoming,
      Data.toRotationSystem_rho, Data.toRotationSystem_alpha, hc, SimpleGraph.Dart.symm_symm] using
      congrArg SimpleGraph.Dart.symm hp1
  · change none = some e at he
    cases he
  · change some ((10, 2) : Slot) = some e at he
    cases Option.some.inj he
    simpa only [dart, base, CubicDartStar.star, hc, SimpleGraph.Dart.symm_symm, Fin.reduceAdd, first, incoming,
      FacialCoronaTraversal.first, FacialCoronaTraversal.incoming,
      Data.toRotationSystem_rho, Data.toRotationSystem_alpha, hc, SimpleGraph.Dart.symm_symm] using
      (congrArg SimpleGraph.Dart.symm (hb (first rotation root 1))).symm
  · change some ((5, 0) : Slot) = some e at he
    cases Option.some.inj he
    simpa only [dart, base, CubicDartStar.star, hc, SimpleGraph.Dart.symm_symm, Fin.reduceAdd, first, incoming,
      FacialCoronaTraversal.first, FacialCoronaTraversal.incoming,
      Data.toRotationSystem_rho, Data.toRotationSystem_alpha, hc, SimpleGraph.Dart.symm_symm] using
      (congrArg SimpleGraph.Dart.symm (congrArg SimpleGraph.Dart.symm hp1)).symm
  · change some ((7, 0) : Slot) = some e at he
    cases Option.some.inj he
    simp only [dart, base, CubicDartStar.star, incoming,
      FacialCoronaTraversal.incoming, SimpleGraph.Dart.symm_symm, incoming,
       FacialCoronaTraversal.incoming,
      Data.toRotationSystem_rho, Data.toRotationSystem_alpha, hc, SimpleGraph.Dart.symm_symm]
  · change none = some e at he
    cases he
  · change some ((6, 1) : Slot) = some e at he
    cases Option.some.inj he
    simp only [dart, base, CubicDartStar.star, incoming,
      FacialCoronaTraversal.incoming, incoming,
       FacialCoronaTraversal.incoming,
      Data.toRotationSystem_rho, Data.toRotationSystem_alpha, hc]
  · change some ((12, 2) : Slot) = some e at he
    cases Option.some.inj he
    simpa only [dart, base, CubicDartStar.star, hc, SimpleGraph.Dart.symm_symm, Fin.reduceAdd, first, incoming,
      FacialCoronaTraversal.first, FacialCoronaTraversal.incoming,
      Data.toRotationSystem_rho, Data.toRotationSystem_alpha, hc, SimpleGraph.Dart.symm_symm] using
      (congrArg SimpleGraph.Dart.symm (hcentral 1)).symm
  · change some ((0, 2) : Slot) = some e at he
    cases Option.some.inj he
    simpa only [dart, base, CubicDartStar.star, hc, SimpleGraph.Dart.symm_symm, Fin.reduceAdd, first, incoming,
      FacialCoronaTraversal.first, FacialCoronaTraversal.incoming,
      Data.toRotationSystem_rho, Data.toRotationSystem_alpha, hc, SimpleGraph.Dart.symm_symm] using
      hcentral 2
  · change some ((9, 0) : Slot) = some e at he
    cases Option.some.inj he
    simpa only [dart, base, CubicDartStar.star, hc, SimpleGraph.Dart.symm_symm, Fin.reduceAdd, first, incoming,
      FacialCoronaTraversal.first, FacialCoronaTraversal.incoming,
      Data.toRotationSystem_rho, Data.toRotationSystem_alpha, hc, SimpleGraph.Dart.symm_symm] using
      hb (rotation.toRotationSystem.phi (first rotation root 0))
  · change none = some e at he
    cases he
  · change some ((11, 2) : Slot) = some e at he
    cases Option.some.inj he
    simpa only [dart, base, CubicDartStar.star, hc, SimpleGraph.Dart.symm_symm, Fin.reduceAdd, first, incoming,
      FacialCoronaTraversal.first, FacialCoronaTraversal.incoming,
      Data.toRotationSystem_rho, Data.toRotationSystem_alpha, hc, SimpleGraph.Dart.symm_symm] using
      (congrArg SimpleGraph.Dart.symm (hb (first rotation root 0))).symm
  · change some ((8, 0) : Slot) = some e at he
    cases Option.some.inj he
    simpa only [dart, base, CubicDartStar.star, hc, SimpleGraph.Dart.symm_symm, Fin.reduceAdd, first, incoming,
      FacialCoronaTraversal.first, FacialCoronaTraversal.incoming,
      Data.toRotationSystem_rho, Data.toRotationSystem_alpha, hc, SimpleGraph.Dart.symm_symm] using
      (congrArg SimpleGraph.Dart.symm (hb (rotation.toRotationSystem.phi (first rotation root 0)))).symm
  · change some ((10, 0) : Slot) = some e at he
    cases Option.some.inj he
    simpa only [dart, base, CubicDartStar.star, hc, SimpleGraph.Dart.symm_symm, Fin.reduceAdd, first, incoming,
      FacialCoronaTraversal.first, FacialCoronaTraversal.incoming,
      Data.toRotationSystem_rho, Data.toRotationSystem_alpha, hc, SimpleGraph.Dart.symm_symm] using
      congrArg SimpleGraph.Dart.symm hh
  · change none = some e at he
    cases he
  · change some ((9, 1) : Slot) = some e at he
    cases Option.some.inj he
    simpa only [dart, base, CubicDartStar.star, hc, SimpleGraph.Dart.symm_symm, Fin.reduceAdd, first, incoming,
      FacialCoronaTraversal.first, FacialCoronaTraversal.incoming,
      Data.toRotationSystem_rho, Data.toRotationSystem_alpha, hc, SimpleGraph.Dart.symm_symm] using
      (congrArg SimpleGraph.Dart.symm (congrArg SimpleGraph.Dart.symm hh)).symm
  · change some ((12, 0) : Slot) = some e at he
    cases Option.some.inj he
    simp only [dart, base, CubicDartStar.star, incoming,
      FacialCoronaTraversal.incoming, SimpleGraph.Dart.symm_symm, incoming,
       FacialCoronaTraversal.incoming,
      Data.toRotationSystem_rho, Data.toRotationSystem_alpha, hc, SimpleGraph.Dart.symm_symm]
  · change some ((5, 2) : Slot) = some e at he
    cases Option.some.inj he
    simpa only [dart, base, CubicDartStar.star, hc, SimpleGraph.Dart.symm_symm, Fin.reduceAdd, first, incoming,
      FacialCoronaTraversal.first, FacialCoronaTraversal.incoming,
      Data.toRotationSystem_rho, Data.toRotationSystem_alpha, hc, SimpleGraph.Dart.symm_symm] using
      hb (first rotation root 1)
  · change some ((3, 1) : Slot) = some e at he
    cases Option.some.inj he
    simpa only [dart, base, CubicDartStar.star, hc, SimpleGraph.Dart.symm_symm, Fin.reduceAdd, first, incoming,
      FacialCoronaTraversal.first, FacialCoronaTraversal.incoming,
      Data.toRotationSystem_rho, Data.toRotationSystem_alpha, hc, SimpleGraph.Dart.symm_symm] using
      (congrArg SimpleGraph.Dart.symm (congrArg SimpleGraph.Dart.symm hp5)).symm
  · change some ((13, 2) : Slot) = some e at he
    cases Option.some.inj he
    simp only [dart, base, CubicDartStar.star, incoming,
      FacialCoronaTraversal.incoming, SimpleGraph.Dart.symm_symm, incoming,
       FacialCoronaTraversal.incoming,
      Data.toRotationSystem_rho, Data.toRotationSystem_alpha, hc, SimpleGraph.Dart.symm_symm]
  · change some ((8, 2) : Slot) = some e at he
    cases Option.some.inj he
    simpa only [dart, base, CubicDartStar.star, hc, SimpleGraph.Dart.symm_symm, Fin.reduceAdd, first, incoming,
      FacialCoronaTraversal.first, FacialCoronaTraversal.incoming,
      Data.toRotationSystem_rho, Data.toRotationSystem_alpha, hc, SimpleGraph.Dart.symm_symm] using
      hb (first rotation root 0)
  · change some ((10, 1) : Slot) = some e at he
    cases Option.some.inj he
    simp only [dart, base, CubicDartStar.star, incoming,
      FacialCoronaTraversal.incoming, incoming,
       FacialCoronaTraversal.incoming,
      Data.toRotationSystem_rho, Data.toRotationSystem_alpha, hc]
  · change some ((13, 1) : Slot) = some e at he
    cases Option.some.inj he
    simpa only [dart, base, CubicDartStar.star, hc, SimpleGraph.Dart.symm_symm, Fin.reduceAdd, first, incoming,
      FacialCoronaTraversal.first, FacialCoronaTraversal.incoming,
      Data.toRotationSystem_rho, Data.toRotationSystem_alpha, hc, SimpleGraph.Dart.symm_symm] using
      (congrArg SimpleGraph.Dart.symm (hcentral 0)).symm
  · change some ((7, 1) : Slot) = some e at he
    cases Option.some.inj he
    simpa only [dart, base, CubicDartStar.star, hc, SimpleGraph.Dart.symm_symm, Fin.reduceAdd, first, incoming,
      FacialCoronaTraversal.first, FacialCoronaTraversal.incoming,
      Data.toRotationSystem_rho, Data.toRotationSystem_alpha, hc, SimpleGraph.Dart.symm_symm] using
      hcentral 1
  · change some ((4, 1) : Slot) = some e at he
    cases Option.some.inj he
    simpa only [dart, base, CubicDartStar.star, hc, SimpleGraph.Dart.symm_symm, Fin.reduceAdd, first, incoming,
      FacialCoronaTraversal.first, FacialCoronaTraversal.incoming,
      Data.toRotationSystem_rho, Data.toRotationSystem_alpha, hc, SimpleGraph.Dart.symm_symm] using
      (congrArg SimpleGraph.Dart.symm (hcentral 5)).symm
  · change some ((12, 1) : Slot) = some e at he
    cases Option.some.inj he
    simpa only [dart, base, CubicDartStar.star, hc, SimpleGraph.Dart.symm_symm, Fin.reduceAdd, first, incoming,
      FacialCoronaTraversal.first, FacialCoronaTraversal.incoming,
      Data.toRotationSystem_rho, Data.toRotationSystem_alpha, hc, SimpleGraph.Dart.symm_symm] using
      hcentral 0
  · change some ((11, 1) : Slot) = some e at he
    cases Option.some.inj he
    simp only [dart, base, CubicDartStar.star, incoming,
      FacialCoronaTraversal.incoming, incoming,
       FacialCoronaTraversal.incoming,
      Data.toRotationSystem_rho, Data.toRotationSystem_alpha, hc]

/-- Four actual face periods supply every operation of the partial diagram. -/
def realization : Realization diagram G where
  vertex := vertex rotation root
  dart := dart rotation root
  fst d := CubicDartStar.fst rotation (base rotation root d.1) d.2
  slots_injective v := CubicDartStar.injective rotation hC (base rotation root v)
  slots_surjective v d hd := CubicDartStar.surjective_at rotation hC (base rotation root v) d hd
  rotation := rotation.vertexRotation
  rotate_eq d := CubicDartStar.rotate rotation hC (base rotation root d.1) d.2
  flip_eq := dart_flip rotation root hC hfaces

end
end Mettapedia.GraphTheory.FourColor.JointDiamond
