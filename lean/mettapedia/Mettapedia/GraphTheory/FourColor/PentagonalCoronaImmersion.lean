import Mettapedia.GraphTheory.FourColor.PentagonalCoronaSeparationCheck
import Mettapedia.GraphTheory.FourColor.PentagonalCoronaBoundary

/-!
# Actual facial darts realize the partial corona diagram

The realization uses the original graph darts. Every local slot, rotation
and internal reversal is constructed from cubicity and the six face periods.
No injectivity of the sixteen vertices is assumed. The separation theorem
therefore derives that injectivity in triangle-free target graphs.
-/

namespace Mettapedia.GraphTheory.FourColor.PentagonalCoronaGeometry

open _root_.SimpleGraph SimpleGraphDartRotation PhysicalForkCodeFaces
open PartialCubicDartSeparation

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance coronaImmersionEdgeFintype : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance coronaImmersionEdgeDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

variable (rotation : Data G) (root : G.Dart)

def innerStar (i : Fin 5) : Fin 3 → G.Dart
  | 0 => center rotation root i
  | 1 => rotation.vertexRotation (center rotation root i)
  | 2 => rotation.vertexRotation (rotation.vertexRotation (center rotation root i))

def diagramDart : PentagonalCoronaSeparation.Slot → G.Dart
  | (.inl i, s) => outerStar rotation root i s
  | (.inr i, s) => innerStar rotation root i s

theorem diagramDart_fst (d : PentagonalCoronaSeparation.Slot) :
    (diagramDart rotation root d).fst = tracedVertex rotation root d.1 := by
  rcases d with ⟨v, s⟩
  cases v with
  | inl i => exact outerStar_fst rotation root i s
  | inr i =>
    fin_cases s <;> simp [diagramDart, innerStar, tracedVertex, rotation.vertexRotation_fst]

variable (hC : Cubic3 rotation.toRotationSystem)
include hC

theorem innerStar_injective (i : Fin 5) : Function.Injective (innerStar rotation root i) := by
  have h10 : rotation.vertexRotation (center rotation root i) ≠ center rotation root i := hC.moves _
  have h21 : rotation.vertexRotation (rotation.vertexRotation (center rotation root i)) ≠
      rotation.vertexRotation (center rotation root i) := hC.moves _
  have h20 : rotation.vertexRotation (rotation.vertexRotation (center rotation root i)) ≠
      center rotation root i := by
    intro he
    have hh := congrArg rotation.vertexRotation he
    have hcube : ∀ d : G.Dart,
        rotation.vertexRotation (rotation.vertexRotation (rotation.vertexRotation d)) = d := hC.cube
    rw [hcube] at hh
    exact h10 hh.symm
  intro a b he
  fin_cases a <;> fin_cases b <;> simp only [innerStar] at he <;>
    first | rfl | exact (h10 he).elim | exact (h10 he.symm).elim |
      exact (h21 he).elim | exact (h21 he.symm).elim |
      exact (h20 he).elim | exact (h20 he.symm).elim

theorem diagramDart_surjective_at (v : PentagonalCoronaSeparation.Vertex)
    (d : G.Dart) (hd : d.fst = tracedVertex rotation root v) :
    ∃ s, diagramDart rotation root (v, s) = d := by
  cases v with
  | inl i => exact outerStar_surjective_at rotation root hC i d hd
  | inr i =>
    have hh : rotation.toRotationSystem.vertOf d =
        rotation.toRotationSystem.vertOf (center rotation root i) := hd
    rcases hC.fiber (center rotation root i) d hh with he | he | he
    · exact ⟨0, he.symm⟩
    · exact ⟨1, he.symm⟩
    · exact ⟨2, he.symm⟩

theorem diagramDart_rotation (d : PentagonalCoronaSeparation.Slot) :
    diagramDart rotation root (PentagonalCoronaSeparation.rotate d) =
      rotation.vertexRotation (diagramDart rotation root d) := by
  rcases d with ⟨v, s⟩
  cases v with
  | inl i => exact (outerStar_rotation rotation root hC (i, s)).symm
  | inr i =>
    fin_cases s
    · rfl
    · rfl
    · exact (hC.cube (center rotation root i)).symm

variable (hroot : (rotation.toRotationSystem.phi ^ 5) root = root)
  (hn : NeighborPeriods rotation root)
include hroot hn

omit hn in
theorem center_back_edge (i : Fin 5) :
    (center rotation root i).symm =
      rotation.vertexRotation (rotation.vertexRotation (center rotation root (i + 1))) := by
  have hs := center_step rotation root hroot i
  change rotation.vertexRotation (center rotation root i).symm = center rotation root (i + 1) at hs
  have he := congrArg (fun d : G.Dart => rotation.vertexRotation (rotation.vertexRotation d)) hs
  have hcube : ∀ d : G.Dart,
      rotation.vertexRotation (rotation.vertexRotation (rotation.vertexRotation d)) = d := hC.cube
  rw [hcube] at he
  exact he

theorem diagramDart_flip (d e : PentagonalCoronaSeparation.Slot)
    (he : PentagonalCoronaSeparation.flip d = some e) :
    (diagramDart rotation root d).symm = diagramDart rotation root e := by
  rcases d with ⟨v, s⟩
  cases v with
  | inl i =>
    fin_cases s
    · fin_cases i <;>
        simp only [PentagonalCoronaSeparation.flip, Nat.reduceMod,
          dite_true, Option.some.injEq] at he
      all_goals first | contradiction | subst e; rfl
    · simp only [PentagonalCoronaSeparation.flip, Option.some.injEq] at he
      subst e
      have hh := congrArg SimpleGraph.Dart.symm (outerStar_edge rotation root hC hroot hn (i - 1))
      simpa only [diagramDart, outerStar, sub_add_cancel, SimpleGraph.Dart.symm_symm] using hh.symm
    · simp only [PentagonalCoronaSeparation.flip, Option.some.injEq] at he
      subst e
      exact outerStar_edge rotation root hC hroot hn i
  | inr i =>
    fin_cases s
    · simp only [PentagonalCoronaSeparation.flip, Option.some.injEq] at he
      subst e
      exact center_back_edge rotation root hC hroot i
    · simp only [PentagonalCoronaSeparation.flip, Option.some.injEq] at he
      subst e
      fin_cases i <;> rfl
    · simp only [PentagonalCoronaSeparation.flip, Option.some.injEq] at he
      subst e
      have hh := congrArg SimpleGraph.Dart.symm (center_back_edge rotation root hC hroot (i - 1))
      simpa only [diagramDart, innerStar, sub_add_cancel, SimpleGraph.Dart.symm_symm] using hh.symm

/-- This is an interpretation of actual operations, before any global
vertex injectivity has been established. -/
def coronaRealization : Realization PentagonalCoronaSeparation.diagram G where
  vertex := tracedVertex rotation root
  dart := diagramDart rotation root
  fst := diagramDart_fst rotation root
  slots_injective v := by
    cases v with
    | inl i => exact outerStar_injective rotation root hC i
    | inr i => exact innerStar_injective rotation root hC i
  slots_surjective := diagramDart_surjective_at rotation root hC
  rotation := rotation.vertexRotation
  rotate_eq := diagramDart_rotation rotation root hC
  flip_eq := diagramDart_flip rotation root hC hroot hn

/-- The actual face periods and local cubic laws force sixteen distinct
vertices whenever the source graph is triangle-free. -/
theorem tracedVertex_injective_of_triangleFree
    (ht : Realization.TriangleFree (G := G)) :
    Function.Injective (tracedVertex rotation root) :=
  (coronaRealization rotation root hC hroot hn).vertex_injective ht 6
    PentagonalCoronaSeparation.separates_all

end
end Mettapedia.GraphTheory.FourColor.PentagonalCoronaGeometry
