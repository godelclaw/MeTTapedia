import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFaces
import Mettapedia.GraphTheory.FourColor.SimpleGraphRotationSystem

/-!
# The three actual darts at a cubic vertex

A rooted dart and two rotations enumerate its whole vertex fibre. This
supplies local coordinates without assuming that different roots have
different vertices.
-/

namespace Mettapedia.GraphTheory.FourColor.CubicDartStar

open _root_.SimpleGraph SimpleGraphDartRotation PhysicalForkCodeFaces

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance starEdgeFintype : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance starEdgeDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

def star (rotation : Data G) (root : G.Dart) : Fin 3 → G.Dart
  | 0 => root
  | 1 => rotation.vertexRotation root
  | 2 => rotation.vertexRotation (rotation.vertexRotation root)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem fst (rotation : Data G) (root : G.Dart) (s : Fin 3) :
    (star rotation root s).fst = root.fst := by
  fin_cases s <;> simp [star, rotation.vertexRotation_fst]

variable (rotation : Data G) (hC : Cubic3 rotation.toRotationSystem) (root : G.Dart)
include hC

theorem injective : Function.Injective (star rotation root) := by
  have h10 : rotation.vertexRotation root ≠ root := hC.moves _
  have h21 : rotation.vertexRotation (rotation.vertexRotation root) ≠
      rotation.vertexRotation root := hC.moves _
  have h20 : rotation.vertexRotation (rotation.vertexRotation root) ≠ root := by
    intro he
    have hh := congrArg rotation.vertexRotation he
    have hc : ∀ d : G.Dart,
        rotation.vertexRotation (rotation.vertexRotation (rotation.vertexRotation d)) = d := hC.cube
    rw [hc] at hh
    exact h10 hh.symm
  intro a b he
  fin_cases a <;> fin_cases b <;> simp only [star] at he <;>
    first | rfl | exact (h10 he).elim | exact (h10 he.symm).elim |
      exact (h21 he).elim | exact (h21 he.symm).elim |
      exact (h20 he).elim | exact (h20 he.symm).elim

theorem surjective_at (d : G.Dart) (hd : d.fst = root.fst) :
    ∃ s, star rotation root s = d := by
  rcases hC.fiber root d hd with he | he | he
  · exact ⟨0, he.symm⟩
  · exact ⟨1, he.symm⟩
  · exact ⟨2, he.symm⟩

theorem rotate (s : Fin 3) :
    star rotation root (s + 1) = rotation.vertexRotation (star rotation root s) := by
  fin_cases s
  · rfl
  · rfl
  · exact (hC.cube root).symm

end Mettapedia.GraphTheory.FourColor.CubicDartStar
