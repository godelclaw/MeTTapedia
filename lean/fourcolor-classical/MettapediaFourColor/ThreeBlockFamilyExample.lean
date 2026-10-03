import MettapediaFourColor.ThreeBlockFamilyReconstruction

/-! # One actual sphere realizes both newly covered boundary classes

The source disk is capped by a triangulated eleven-gon. The 18-vertex
sphere supplies the complete core reading. Its 11-vertex exterior has two
explicit initial colourings, neither extending while fixed; the shared
three-run repair reconstructs a genuine ambient colouring for each.
-/

namespace FourColor.ThreeBlockDiskBoundary.FamilyExample

open SimpleGraph FiveTriangleCollapseObstruction KempeBoundarySplit

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def star (v : Fin 18) : List (Fin 18) :=
  (![[1,10,17],
     [0,17,15,2,4,10],
     [1,15,3,4],
     [2,15,12,4],
     [1,2,3,12,5,6,10],
     [4,12,13,6],
     [4,5,13,7,8,9,10],
     [6,13,14,8],
     [6,7,14,11,16,9],
     [6,8,16,10],
     [0,1,4,6,9,16,17],
     [8,14,12,15,17,16],
     [3,15,11,14,13,5,4],
     [5,12,14,7,6],
     [7,13,12,11,8],
     [1,17,11,12,3,2],
     [8,11,17,10,9],
     [0,10,16,11,15,1]] : Fin 18 → List (Fin 18)) v

private theorem symmetric : ∀ u v : Fin 18, v ∈ star u → u ∈ star v := by decide +kernel
private theorem loopless : ∀ v : Fin 18, v ∉ star v := by decide +kernel

def graph : SimpleGraph (Fin 18) where
  Adj u v := v ∈ star u
  symm := ⟨symmetric⟩
  loopless := ⟨loopless⟩

instance : DecidableRel graph.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∈ _))

def rows : GraphRotationRows.Rows graph := ⟨star, by decide +kernel, fun _ _ => Iff.rfl⟩
def rotation := rows.rotation (⟨(0,1), by decide +kernel⟩ : graph.Dart)
theorem cyclic : rotation.IsVertexwiseCyclic := rows.cyclic _
theorem triangular : ExceptionalOverlap.Triangular rotation := by
  unfold ExceptionalOverlap.Triangular
  decide +kernel

def hom : upper.graph →g graph where
  toFun := id
  map_rel' := by decide +kernel

theorem core_turn : ∀ i j k, Turn i j k →
    ExceptionalCoreOrientation.Corner rotation (hom i) (hom k) (hom j) := by
  have h : ∀ i j k : Fin 18, Turn i j k →
      graph.Adj (hom i) (hom k) ∧ graph.Adj (hom i) (hom j) ∧
        rows.next (hom i) (hom k) = hom j := by decide +kernel
  intro i j k ht
  obtain ⟨hik, hij, step⟩ := h i j k ht
  exact ⟨hik, hij, Dart.ext _ _ (Prod.ext rfl step)⟩

def reading : Reading rotation := ⟨hom, Function.injective_id, core_turn⟩

theorem connected : graph.Connected := by
  have parents : ∀ v : Fin 18, v ≠ 0 → ∃ w, w.val < v.val ∧ graph.Adj w v := by
    decide +kernel
  have reach : ∀ n (v : Fin 18), v.val = n → graph.Reachable 0 v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv
      by_cases h : v = 0
      · subst v; exact .refl _
      obtain ⟨w, less, edge⟩ := parents v h
      exact (ih w.val (hv ▸ less) w rfl).trans edge.reachable
  apply (connected_iff_exists_forall_reachable (G := graph)).mpr
  exact ⟨0, fun v => reach v.val v rfl⟩

theorem dart_count : Nat.card graph.Dart = 96 := by
  rw [rows.dart_count]
  decide +kernel

theorem planar : (SimpleGraphBridge.rotationHypermap rotation).Planar := by
  apply (GraphTriangulationEuler.planar_iff_balance rotation cyclic connected
    (GraphTriangulationEuler.covered connected) triangular).mpr
  rw [Nat.card_fin, dart_count]

theorem boundary_proper : ∀ (c : Bool) (u v : Fin 11),
    graph.Adj (u.castAdd 7) (v.castAdd 7) →
      ThreeBlockCore.word false true c u ≠ ThreeBlockCore.word false true c v := by
  decide +kernel

def boundaryIndex (v : keep reading) : Fin 11 :=
  ⟨v.val.val, (keep_point reading v.val).mp v.property⟩

def initial (c : Bool) : (graph.induce (keep reading)).Coloring Color :=
  .mk (fun v => ThreeBlockCore.word false true c (boundaryIndex v))
    (fun {u v} h => boundary_proper c (boundaryIndex u) (boundaryIndex v) h)

theorem initial_boundary (c : Bool) (j : Fin 11) :
    initial c (port reading j) = ThreeBlockCore.word false true c j := rfl

theorem initial_cannot_extend (c : Bool) : ¬ ∃ K : graph.Coloring Color,
    ∀ w : keep reading, K w.val = initial c w := by
  rintro ⟨K, fixed⟩
  let k : upper.graph.Coloring Color := .mk (fun v => K v)
    (fun {_ _} edge => K.valid (hom.map_rel edge))
  have boundary (j : Fin 11) : k (j.castAdd 7) = ThreeBlockCore.word false true c j := by
    exact (fixed (port reading j)).trans (initial_boundary c j)
  have bad := (ThreeBlockCore.necessary false true c k boundary).1
  contradiction

theorem reconstructed (c : Bool) :
    ∃ D : (graph.induce (keep reading)).Coloring Color, ∃ K : graph.Coloring Color,
      ∀ w, K w.val = D w :=
  repair_three_run reading triangular cyclic connected planar false true c
    (initial c) (initial_boundary c)

theorem changed_reconstruction (c : Bool) :
    ∃ D : (graph.induce (keep reading)).Coloring Color, ∃ K : graph.Coloring Color,
      (∀ w, K w.val = D w) ∧ ∃ w, D w ≠ initial c w := by
  classical
  obtain ⟨D, K, agrees⟩ := reconstructed c
  refine ⟨D, K, agrees, ?_⟩
  by_contra unchanged
  apply initial_cannot_extend c
  refine ⟨K, fun w => ?_⟩
  rw [agrees]
  by_contra differs
  exact unchanged ⟨w, differs⟩

theorem exterior_vertices : Fintype.card (keep reading) = 11 := by
  have h := deleted_count reading triangular
  rw [Fintype.card_fin] at h
  omega

end FourColor.ThreeBlockDiskBoundary.FamilyExample
