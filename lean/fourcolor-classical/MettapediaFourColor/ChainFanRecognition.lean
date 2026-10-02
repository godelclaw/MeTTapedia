import MettapediaFourColor.ActualChainRecognition

/-!
# A consecutive degree word recognizes the chain

Four consecutive neighbours of a degree-six centre, with degrees 5,6,5,5,
determine the retained three-triangle core. The actual minimal-map consumer
constructs its boundary and reconstructs a colouring without an additional
catalogue recognition or colouring hypothesis.
-/

namespace FourColor.ChainFanRecognition

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open ChainCoreReading ExceptionalCoreOrientation ExceptionalOverlap

def position : Fin 5 → ℕ := ![3, 0, 2, 1, 0]
def word : Fin 4 → ℕ := ![5, 6, 5, 5]

theorem positions : ∀ k : Fin 3,
    first k ≠ 1 ∧ second k ≠ 1 ∧ position (first k) = k.val ∧
      position (second k) = k.val + 1 := by decide +kernel

theorem degrees : ∀ i : Fin 5, i ≠ 1 →
    ∃ n : Fin 4, position i = n.val ∧ degree i = word n := by decide +kernel

theorem edges : ∀ i j : Fin 5, core.Adj i j →
    (i = 1 ∧ j ≠ 1) ∨ (j = 1 ∧ i ≠ 1) ∨
    ∃ k : Fin 3, (i = first k ∧ j = second k) ∨
      (j = first k ∧ i = second k) := by decide +kernel

variable {V : Type*} {G : SimpleGraph V} (rotation : Data G)

def walk (d : G.Dart) (n : ℕ) := (rotation.vertexRotation ^ n) d

theorem walk_fst (d : G.Dart) (n : ℕ) : (walk rotation d n).fst = d.fst :=
  FacialStarCompletion.pow_fst rotation d n

theorem walk_next (d : G.Dart) (n : ℕ) :
    rotation.vertexRotation (walk rotation d n) = walk rotation d (n + 1) := by
  simp only [walk, pow_succ', Equiv.Perm.mul_apply]

def vertex (d : G.Dart) (i : Fin 5) : V :=
  if i = 1 then d.fst else (walk rotation d (position i)).snd

theorem vertex_center (d : G.Dart) : vertex rotation d 1 = d.fst := by simp [vertex]

theorem vertex_other (d : G.Dart) (i : Fin 5) (ne : i ≠ 1) :
    vertex rotation d i = (walk rotation d (position i)).snd := by simp [vertex, ne]

theorem vertex_first (d : G.Dart) (k : Fin 3) :
    vertex rotation d (first k) = (walk rotation d k.val).snd := by
  rw [vertex_other rotation d _ (positions k).1, (positions k).2.2.1]

theorem vertex_second (d : G.Dart) (k : Fin 3) :
    vertex rotation d (second k) = (walk rotation d (k.val + 1)).snd := by
  rw [vertex_other rotation d _ (positions k).2.1, (positions k).2.2.2]

theorem center_adj (d : G.Dart) (i : Fin 5) (ne : i ≠ 1) :
    G.Adj (vertex rotation d 1) (vertex rotation d i) := by
  rw [vertex_center, vertex_other rotation d i ne]
  simpa only [walk_fst] using (walk rotation d (position i)).adj

theorem face (d : G.Dart) (k : Fin 3) :
    Corner rotation (vertex rotation d 1) (vertex rotation d (first k))
      (vertex rotation d (second k)) := by
  rw [vertex_center, vertex_first, vertex_second]
  have adj (n : ℕ) : G.Adj d.fst (walk rotation d n).snd := by
    simpa only [walk_fst] using (walk rotation d n).adj
  have eq (n : ℕ) : (⟨(d.fst, (walk rotation d n).snd), adj n⟩ : G.Dart) =
      walk rotation d n := by
    apply SimpleGraph.Dart.ext
    exact Prod.ext (walk_fst rotation d n).symm rfl
  refine ⟨adj _, adj _, ?_⟩
  rw [eq, eq, walk_next]

variable [G.LocallyFinite]

def hom (tri : Triangular rotation) (d : G.Dart) : core →g G where
  toFun := vertex rotation d
  map_rel' := by
    intro i j hij
    rcases edges i j hij with ⟨rfl, hj⟩ | ⟨rfl, hi⟩ | ⟨k, h | h⟩
    · exact center_adj rotation d j hj
    · exact (center_adj rotation d i hi).symm
    · rcases h with ⟨rfl, rfl⟩
      obtain ⟨adj, _, _⟩ := Corner.rotate rotation tri (face rotation d k)
      exact adj
    · rcases h with ⟨rfl, rfl⟩
      obtain ⟨adj, _, _⟩ := Corner.rotate rotation tri (face rotation d k)
      exact adj.symm

/-- No preselected core homomorphism is required: the same rotation walk
constructs all core vertices and the three compatible facial readings. -/
def reading (tri : Triangular rotation) (d : G.Dart)
    (center : G.degree d.fst = 6)
    (neighbors : ∀ n : Fin 4, G.degree (walk rotation d n.val).snd = word n) :
    Reading rotation where
  map := hom rotation tri d
  degree_eq := by
    intro i
    change G.degree (vertex rotation d i) = degree i
    by_cases hi : i = 1
    · subst i
      rw [vertex_center, center]
      rfl
    · obtain ⟨n, hn, hd⟩ := degrees i hi
      rw [vertex_other rotation d i hi, hn, neighbors, hd]
  face := face rotation d

noncomputable section

variable {W : Type*} [Fintype W] [DecidableEq W]
  {H : SimpleGraph W} [DecidableRel H.Adj] (original : Data H)
  (minimal : GoertzelV24TwoEdgeCutMinimality.GraphBackedVertexMinimalTaitCounterexample original)

/-- The consecutive degree word is excluded in an actual minimal map. -/
theorem not_in_minimal
    (d : (MinimalExceptionalEmbedding.graph original minimal).Dart)
    (center : (MinimalExceptionalEmbedding.graph original minimal).degree d.fst = 6)
    (neighbors : ∀ n : Fin 4,
      (MinimalExceptionalEmbedding.graph original minimal).degree
        (walk (MinimalExceptionalEmbedding.rotation original minimal) d n.val).snd = word n) :
    False := by
  classical
  exact ActualChainRecognition.not_in_minimal original minimal
    (reading (G := MinimalExceptionalEmbedding.graph original minimal)
      (MinimalExceptionalEmbedding.rotation original minimal)
      (MinimalExceptionalEmbedding.triangular original minimal) d center neighbors)

end
end FourColor.ChainFanRecognition
