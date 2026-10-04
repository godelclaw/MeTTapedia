import MettapediaFourColor.StripSixOrderExample
import MettapediaFourColor.DualDegreePattern

/-! # An alternative diamond in the fixed-order obstruction

The facial dual of the forty-one-vertex sphere has seventy-eight vertices.
A bijection of all directed edges verifies reversal and both rotations.
The degree-five centre at vertex twenty-two has three consecutive
degree-five neighbours, yielding the existing diamond exclusion in the
actual dual. This proves neither universal supply nor normal form of the
example beyond the stated hypotheses.
-/

namespace FourColor.StripSixDualExample

open SimpleGraph Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open GoertzelV24TwoEdgeCutMinimality

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

def star : Fin 78 → List (Fin 78) := ![
  [53,5,2],[22,54,52],[48,49,0],[55,7,4],[33,5,3],[4,35,0],[57,8,7],[6,10,3],[12,6,13],[58,11,13],
  [12,31,7],[60,43,9],[14,10,8],[30,8,9],[26,15,12],[14,29,32],[63,20,17],[62,16,44],[65,21,19],
  [18,37,20],[45,16,19],[66,23,18],[69,1,23],[39,21,22],[29,26,37],[29,36,46],[24,14,30],
  [43,28,30],[27,45,37],[24,25,15],[26,13,27],[10,32,33],[31,15,41],[31,34,4],[33,40,35],
  [48,5,34],[25,39,38],[19,24,28],[51,47,36],[52,36,23],[41,42,34],[46,40,32],[40,50,48],
  [44,27,11],[45,43,17],[44,20,28],[47,41,25],[50,46,38],[2,35,42],[2,50,51],[42,47,49],
  [49,38,52],[51,39,1],[56,0,54],[1,71,53],[57,3,56],[77,55,53],[59,6,55],[61,9,59],[76,58,57],
  [62,11,61],[58,73,60],[64,17,60],[65,16,64],[72,63,62],[67,18,63],[70,21,68],[65,72,68],
  [67,74,66],[71,22,70],[66,75,69],[69,77,54],[73,67,64],[61,74,72],[73,75,68],[70,74,76],
  [59,77,75],[71,76,56]]
def triangle : Fin 78 → List (Fin 41) := ![
  [0,1,22],[32,10,0],[22,17,0],[1,2,20],[20,13,1],[1,13,22],[2,3,12],[2,12,20],[23,12,3],[3,4,24],
  [12,16,20],[4,5,24],[23,16,12],[24,23,3],[23,19,16],[16,19,28],[6,7,27],[5,6,27],[7,8,26],
  [7,26,31],[31,27,7],[8,9,26],[9,10,32],[32,26,9],[26,19,11],[28,26,14],[11,19,23],[24,21,11],
  [11,21,31],[19,26,28],[11,23,24],[20,16,15],[15,16,28],[20,15,13],[13,15,25],[25,22,13],
  [14,26,30],[31,26,11],[30,29,14],[32,30,26],[15,18,25],[28,18,15],[25,18,17],[5,21,24],
  [27,21,5],[21,27,31],[14,18,28],[29,18,14],[17,22,25],[0,17,29],[17,18,29],[0,29,30],[0,30,32],
  [40,1,0],[0,10,40],[38,2,1],[40,38,1],[38,3,2],[35,4,3],[38,35,3],[36,5,4],[4,35,36],[36,6,5],
  [33,7,6],[36,33,6],[33,8,7],[37,9,8],[8,33,34],[8,34,37],[39,10,9],[9,37,39],[10,39,40],
  [36,34,33],[36,35,34],[34,35,37],[39,37,35],[35,38,39],[40,39,38]]
def faceIds : Fin 41 → List (Fin 78) := ![
  [0,53,54,1,52,51,49,2],[53,0,5,4,3,55,56],[55,3,7,6,57],[57,6,8,13,9,58,59],[58,9,11,60,61],
  [60,11,43,44,17,62],[62,17,16,63,64],[63,16,20,19,18,65],[65,18,21,66,68,67],
  [66,21,23,22,69,70],[1,54,71,69,22],[26,24,37,28,27,30],[6,7,10,12,8],[4,5,35,34,33],
  [46,47,38,36,25],[33,34,40,41,32,31],[12,10,31,32,15,14],[2,49,50,42,48],[47,46,41,40,42,50],
  [24,26,14,15,29],[3,4,33,31,10,7],[44,43,27,28,45],[0,2,48,35,5],[13,8,12,14,26,30],
  [9,13,30,27,43,11],[34,35,48,42,40],[18,19,37,24,29,25,36,39,23,21],[17,44,45,20,16],
  [46,25,29,15,32,41],[49,51,38,47,50],[51,52,39,36,38],[19,20,45,28,37],[52,1,22,23,39],
  [64,63,65,67,72],[67,68,74,73,72],[59,58,61,73,74,75,76],[61,60,62,64,72,73],[68,66,70,75,74],
  [56,55,57,59,76,77],[70,69,71,77,76,75],[54,53,56,77,71]]

theorem row_nodup : ∀ v, (star v).Nodup := by decide +kernel
theorem row_symm : ∀ u v, v ∈ star u → u ∈ star v := by decide +kernel
theorem row_loopless : ∀ v, v ∉ star v := by decide +kernel

def graph : SimpleGraph (Fin 78) where
  Adj u v := v ∈ star u
  symm := ⟨row_symm⟩
  loopless := ⟨row_loopless⟩
instance : DecidableRel graph.Adj := by unfold graph; infer_instance

def rows : GraphRotationRows.Rows graph := ⟨star,row_nodup,fun _ _ => Iff.rfl⟩
def rotation := rows.rotation (⟨(0,(star 0).head!), by decide +kernel⟩ : graph.Dart)
theorem cyclic : rotation.IsVertexwiseCyclic := rows.cyclic _

def faceId (u v : Fin 41) : Fin 78 :=
  (faceIds u).getD ((StripSixOrderExample.star u).idxOf v) 0
def toPair (u v : Fin 41) : Fin 78 × Fin 78 := (faceId u v, faceId v u)
def fromPair (u v : Fin 78) : Fin 41 × Fin 41 :=
  let i := (star u).idxOf v
  ((triangle u).getD i 0, (triangle u).getD ((i+1)%3) 0)

theorem forward_check : ∀ u, (StripSixOrderExample.star u).all (fun v => decide
    (graph.Adj (toPair u v).1 (toPair u v).2 ∧
      fromPair (toPair u v).1 (toPair u v).2 = (u,v))) = true := by decide +kernel

theorem backward_check : ∀ u, (star u).all (fun v => decide
    (StripSixOrderExample.ambient.Adj (fromPair u v).1 (fromPair u v).2 ∧
      toPair (fromPair u v).1 (fromPair u v).2 = (u,v))) = true := by decide +kernel

theorem forward_valid (d : StripSixOrderExample.ambient.Dart) :
    graph.Adj (toPair d.fst d.snd).1 (toPair d.fst d.snd).2 ∧
      fromPair (toPair d.fst d.snd).1 (toPair d.fst d.snd).2 = d.toProd :=
  of_decide_eq_true (List.all_eq_true.mp (forward_check d.fst) d.snd d.adj)
theorem backward_valid (d : graph.Dart) :
    StripSixOrderExample.ambient.Adj (fromPair d.fst d.snd).1 (fromPair d.fst d.snd).2 ∧
      toPair (fromPair d.fst d.snd).1 (fromPair d.fst d.snd).2 = d.toProd :=
  of_decide_eq_true (List.all_eq_true.mp (backward_check d.fst) d.snd d.adj)

def darts : StripSixOrderExample.ambient.Dart ≃ graph.Dart where
  toFun d := ⟨toPair d.fst d.snd, (forward_valid d).1⟩
  invFun d := ⟨fromPair d.fst d.snd, (backward_valid d).1⟩
  left_inv d := Dart.ext _ _ (forward_valid d).2
  right_inv d := Dart.ext _ _ (backward_valid d).2

theorem flip (d : StripSixOrderExample.ambient.Dart) : darts d.symm = (darts d).symm := by
  apply Dart.ext
  rfl

theorem step_check : ∀ u, (StripSixOrderExample.star u).all (fun v => decide
    (((toPair u v).1, rows.next (toPair u v).1 (toPair u v).2) =
      toPair v (StripSixOrderExample.rows.next v u))) = true := by decide +kernel

/-- Dual vertex rotation is precisely primal face traversal. -/
theorem vertex_step (d : StripSixOrderExample.ambient.Dart) :
    rotation.vertexRotation (darts d) =
      darts (StripSixOrderExample.rotation.toRotationSystem.phi d) := by
  apply Dart.ext
  exact of_decide_eq_true (List.all_eq_true.mp (step_check d.fst) d.snd d.adj)

/-- Dual face traversal is precisely primal vertex rotation. -/
theorem face_step (d : StripSixOrderExample.ambient.Dart) :
    rotation.toRotationSystem.phi (darts d) =
      darts (StripSixOrderExample.rotation.vertexRotation d) := by
  change rotation.vertexRotation (darts d).symm = _
  rw [← flip, vertex_step]
  rfl

theorem planar : (SimpleGraphBridge.rotationHypermap rotation).Planar :=
  DualDegreePattern.planar StripSixOrderExample.rotation rotation darts face_step flip
    StripSixOrderExample.planar

theorem cubic : graph.IsRegularOfDegree 3 := by
  intro v
  have h : graph.degree v =
      @SimpleGraph.degree (Fin 78) graph v (Subtype.fintype _) :=
    congrArg (@SimpleGraph.degree (Fin 78) graph v) (Subsingleton.elim _ _)
  rw [h, rows.degree]
  exact (by decide +kernel : ∀ v : Fin 78, (star v).length = 3) v

theorem dart_count : Nat.card graph.Dart = 234 :=
  (Nat.card_congr darts).symm.trans StripSixOrderExample.dart_count

/-- The degrees belong to the entire ambient graph, in its actual cyclic order. -/
def root : StripSixOrderExample.ambient.Dart := ⟨(22,0), by decide +kernel⟩
theorem central : StripSixOrderExample.ambient.degree root.fst = 5 := by
  rw [StripSixOrderExample.degree_eq]; decide +kernel

theorem neighbour_degrees : ∀ i : Fin 5, 1 ≤ i.val → i.val ≤ 3 →
    StripSixOrderExample.ambient.degree (((StripSixOrderExample.rotation.vertexRotation ^ i.val) root).snd) =
      5 := by
  intro i hlo hhi
  rw [StripSixOrderExample.degree_eq]
  change (StripSixOrderExample.star
    (((StripSixOrderExample.rows.rotation _).vertexRotation ^ i.val) root).snd).length = 5
  rw [(StripSixOrderExample.rows.pow_reading _ i.val root).2]
  exact (by decide +kernel : ∀ i : Fin 5, 1 ≤ i.val → i.val ≤ 3 →
    (StripSixOrderExample.star (((StripSixOrderExample.star root.fst).formPerm ^ i.val) root.snd)).length =
      5) i hlo hhi

theorem face_pattern : PentagonalDiamond.FaceLengths rotation (darts root) :=
  DualDegreePattern.diamond StripSixOrderExample.rotation rotation darts face_step flip StripSixOrderExample.cyclic
    root
    central neighbour_degrees

/-- The fixed-order obstruction cannot be a vertex-minimal Tait
counterexample in its exact dual representation. -/
theorem alternative_excludes_minimal
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation) : False :=
  DualDegreePattern.not_in_minimal StripSixOrderExample.rotation rotation darts face_step flip StripSixOrderExample.cyclic
    root
    central neighbour_degrees minimal

end FourColor.StripSixDualExample
