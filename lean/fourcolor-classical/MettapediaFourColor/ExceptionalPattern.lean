import MettapediaFourColor.NearLinearDiamondData
import MettapediaFourColor.LocalCoverageAssembly
import Mettapedia.GraphTheory.FourColor.SimpleGraphRotationSystem

/-!
# The source exceptional pattern as actual graph darts

The flat string encodes `getX` in `src/combine_cartwheel.cpp` at revision
6cb85666ce89cf8bd813132e4c5dd56053e367a5 of near-linear-4ct/computer-checks.
The unmodified function and MIT notice (copyright 2026 Yuta Inoue) are
retained in tools/fourcolor/near-linear. Labels are shifted by one so that
zero denotes the source gap -1. Gaps impose no rotation step.

An occurrence preserves every listed edge, prescribed degree and known
cyclic step. It does not assume injectivity: collision and obstructing-cycle
analysis remain separate. Its darts are actual darts of the ambient graph.
-/

namespace FourColor.ExceptionalPattern

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open LocalCoverageAssembly

set_option maxRecDepth 32768

def source : String := "8 5 5 5 5 7 5 5 7 5 5 8 5 5 8 5 5\n2 3 4 5 6 7 8 9\n1 9 12 13 3\n1 2 13 0 4\n1 3 0 14 5\n1 4 14 15 6\n1 5 15 16 17 0 7\n1 6 0 8\n1 7 0 9\n1 8 0 10 11 12 2\n9 0 11\n9 10 0 12\n2 9 11 0 13\n2 12 0 3\n4 0 15 5\n5 14 0 16 6\n6 15 0 17\n6 16 0\n"

def rows : List (List ℕ) := NearLinearDiamondData.rows source
def prescribed (i : Fin 17) : ℕ := (rows.headD []).getD i.val 0
def row (i : Fin 17) : List ℕ := rows.getD (i.val + 1) []

def graph : SimpleGraph (Fin 17) where
  Adj i j := j.val + 1 ∈ row i
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩

instance : DecidableRel graph.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∈ _))

/-- Only consecutive non-gap entries prescribe an actual rotation step. -/
def Turn (i j k : Fin 17) : Prop :=
  (j.val + 1, k.val + 1) ∈ (row i).zip ((row i).rotate 1)

instance (i j k : Fin 17) : Decidable (Turn i j k) := by unfold Turn; infer_instance

theorem source_valid : rows.length = 18 ∧ (rows.headD []).length = 17 ∧
    ∀ i : Fin 17, (row i).Nodup ∧ ∀ j ∈ row i, j ≤ 17 := by decide +kernel

def neighbor (i : Fin 8) : Fin 17 := ⟨i.val + 1, by omega⟩

theorem central_edge (i : Fin 8) : graph.Adj 0 (neighbor i) := by
  fin_cases i <;> decide +kernel

theorem central_turn (i : Fin 8) : Turn 0 (neighbor i) (neighbor (i + 1)) := by
  fin_cases i <;> decide +kernel

def centralWord (i : Fin 8) : ℕ := prescribed (neighbor i)

/-- Each seven has at least two fives on both sides in the source word. -/
theorem central_word_gap : ∀ i : Fin 8, centralWord i = 7 →
    centralWord (i - 2) = 5 ∧ centralWord (i + 2) = 5 := by decide +kernel

theorem source_routes : ∀ i : Fin 17, i = 0 ∨ graph.Adj 0 i ∨
    ∃ j : Fin 17, graph.Adj 0 j ∧ graph.Adj j i := by decide +kernel

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] (rotation : Data G)

structure Occurrence where
  vertex : Fin 17 → V
  edge : ∀ i j, graph.Adj i j → G.Adj (vertex i) (vertex j)
  degree : ∀ i, G.degree (vertex i) = prescribed i
  turn : ∀ i j k (hij : graph.Adj i j) (hik : graph.Adj i k), Turn i j k →
    rotation.vertexRotation ⟨(vertex i, vertex j), edge i j hij⟩ =
      ⟨(vertex i, vertex k), edge i k hik⟩

namespace Occurrence
variable {rotation} (x : Occurrence rotation)

def dart (i j : Fin 17) (h : graph.Adj i j) : G.Dart :=
  ⟨(x.vertex i, x.vertex j), x.edge i j h⟩

def centralDart (i : Fin 8) : G.Dart := x.dart 0 (neighbor i) (central_edge i)

theorem central_step (i : Fin 8) :
    rotation.vertexRotation (x.centralDart i) = x.centralDart (i + 1) :=
  x.turn 0 (neighbor i) (neighbor (i + 1)) (central_edge i)
    (central_edge (i + 1)) (central_turn i)

theorem central_pow (i : Fin 8) :
    (rotation.vertexRotation ^ i.val) (x.centralDart 0) = x.centralDart i := by
  have step (n : ℕ) (hn : n < 8) :
      (rotation.vertexRotation ^ n) (x.centralDart 0) = x.centralDart ⟨n, hn⟩ := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih (by omega), x.central_step]
      congr 1
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_one]
      omega
  exact step i.val i.isLt

theorem central_previous (i : Fin 8) :
    rotation.vertexRotation.symm (x.centralDart i) = x.centralDart (i - 1) := by
  apply rotation.vertexRotation.injective
  rw [Equiv.apply_symm_apply, x.central_step]
  simp

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Cyclicity and the actual degree give every outgoing dart a position in
the source word. No injectivity of all seventeen vertex labels is assumed. -/
theorem central_covers (cyclic : rotation.IsVertexwiseCyclic)
    (d : G.Dart) (hd : d.fst = x.vertex 0) :
    ∃ i : Fin 8, x.centralDart i = d := by
  classical
  let fiber : Finset G.Dart := Finset.univ.filter fun d => d.fst = x.vertex 0
  have hc : rotation.vertexRotation.IsCycleOn (fiber : Set G.Dart) := by
    simpa [fiber] using cyclic (x.vertex 0)
  have hn : fiber.card = 8 := by
    change ({d : G.Dart | d.fst = x.vertex 0} : Finset G.Dart).card = 8
    rw [G.dart_fst_fiber_card_eq_degree]
    exact (SimpleGraph.degree_instance_independent (x.vertex 0) _ _).symm.trans (x.degree 0)
  obtain ⟨n, hn', he⟩ := hc.exists_pow_eq
    (show x.centralDart 0 ∈ fiber by simp [fiber, centralDart, dart])
    (show d ∈ fiber by simp [fiber, hd])
  rw [hn] at hn'
  exact ⟨⟨n, hn'⟩, (x.central_pow ⟨n, hn'⟩).symm.trans he⟩

/-- Transfer the source word's spacing law to the actual shared dart. -/
theorem seven_previous_two (cyclic : rotation.IsVertexwiseCyclic)
    (d : G.Dart) (hd : d.fst = x.vertex 0) (h7 : G.degree d.snd = 7) :
    G.degree (rotation.vertexRotation.symm (rotation.vertexRotation.symm d)).snd = 5 := by
  obtain ⟨i, rfl⟩ := x.central_covers cyclic d hd
  have hi : centralWord i = 7 := (x.degree (neighbor i)).symm.trans h7
  rw [x.central_previous, x.central_previous]
  change G.degree (x.vertex (neighbor (i - 1 - 1))) = 5
  rw [x.degree]
  simpa [centralWord, sub_sub] using (central_word_gap i hi).1

/-- The source pattern itself supplies the prescribed second degree-eight
centre, with an actual two-edge walk witnessing its distance bound. -/
theorem next_centre : x.vertex 14 ∈ closedBall G (x.vertex 0) 2 ∧
    G.degree (x.vertex 14) = 8 := by
  let p : G.Walk (x.vertex 0) (x.vertex 14) :=
    .cons (x.edge 0 4 (by decide +kernel))
      (.cons (x.edge 4 14 (by decide +kernel)) .nil)
  exact ⟨by simpa [closedBall, p] using p.edist_le, x.degree 14⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Every prescribed source vertex stays within two actual graph steps. -/
theorem vertex_near (i : Fin 17) : x.vertex i ∈ closedBall G (x.vertex 0) 2 := by
  rcases source_routes i with rfl | h | ⟨j, hj, hji⟩
  · exact centre_mem G _ _
  · let p : G.Walk (x.vertex 0) (x.vertex i) := .cons (x.edge 0 i h) .nil
    exact (show G.edist (x.vertex 0) (x.vertex i) ≤ 1 by simpa [p] using p.edist_le).trans
      (by decide)
  · let p : G.Walk (x.vertex 0) (x.vertex i) :=
      .cons (x.edge 0 j hj) (.cons (x.edge j i hji) .nil)
    simpa [closedBall, p] using p.edist_le

end Occurrence
end FourColor.ExceptionalPattern
