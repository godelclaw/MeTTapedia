import MettapediaFourColor.FourTriangleCompletion
import MettapediaFourColor.FourTriangleOccurrence
import MettapediaFourColor.FourTriangleRecognition
import MettapediaFourColor.FourTriangleRepairGeometry

/-!
# Four retained faces supply complete reduction occurrences

The common boundary-completion theorem grows all ten ports from the same
six core vertices. Minimality supplies inducedness. A degree-preserving
reflection of the tripod source aligns its positive completion with the
reversed classical presentation, retaining all edges and ordered ports.
Both actual occurrences feed the same strict reconstruction theorem.
-/

namespace FourColor.FourTriangleCompletedOccurrence

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open FourTriangleCompletion ExceptionalCoreOrientation ExceptionalOverlap

set_option maxRecDepth 32768

variable (s : Fin 2)

/-- The fan keeps its labels. The tripod reflects its entire source disk. -/
def relabel : Fin 16 ≃ Fin 16 where
  toFun := ![(fun i => i), ![4, 3, 2, 1, 0, 9, 8, 7, 6, 5, 10, 12, 11, 13, 15, 14]] s
  invFun := ![(fun i => i), ![4, 3, 2, 1, 0, 9, 8, 7, 6, 5, 10, 12, 11, 13, 15, 14]] s
  left_inv := by revert s; decide +kernel
  right_inv := by revert s; decide +kernel

def sourceIso : (FourTriangleCore.input s).graph ≃g (FourTriangleCore.input s).graph where
  toEquiv := relabel s
  map_rel_iff' := by revert s; decide +kernel

/-- Core degrees are preserved by the same relabelling used for edges and turns. -/
theorem core_reading : ∀ v : Fin 16, 10 ≤ v.val → ∃ i : Fin 6,
    relabel s v = i.natAdd 10 ∧
      FourTriangleCore.degree s i = FourTriangleConstruction.degree s v := by
  revert s; decide +kernel

theorem boundary_preserved : ∀ v : Fin 16, v.val < 10 → (relabel s v).val < 10 := by
  revert s; decide +kernel

/-- The entire ordered interface is aligned, not merely its set of vertices. -/
theorem boundary_alignment :
    (FourTriangleConstruction.boundary 0).map (relabel 0) =
      (FourTriangleCore.input 0).boundary.rotate 9 ∧
    (FourTriangleConstruction.boundary 1).map (relabel 1) =
      (FourTriangleCore.input 1).boundary.rotate 1 := by decide +kernel

/-- Every reference core turn becomes a positive completed source turn. -/
theorem source_turn : ∀ d : Fin 70,
    10 ≤ (FourTriangleConstruction.vertex s d).val →
    ∃ (i : Fin 6) (p : Fin (FourTriangleCore.degree s i)),
      relabel s (FourTriangleConstruction.vertex s d) = i.natAdd 10 ∧
      relabel s (FourTriangleConstruction.vertex s
        ((FourTriangleConstruction.table s).map.edge d)) =
        row s i p.val ∧
      relabel s (FourTriangleConstruction.vertex s
        ((FourTriangleConstruction.table s).map.face d)) =
        i.natAdd 10 ∧
      relabel s (FourTriangleConstruction.vertex s ((FourTriangleConstruction.table s).map.edge
        ((FourTriangleConstruction.table s).map.face d))) =
          row s i ((p.val + 1) % FourTriangleCore.degree s i) := by
  revert s; decide +kernel

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] [Finite V]
  {rotation : Data G} (r : FourTriangleCore.Reading s rotation)
  (degrees : ∀ i, G.degree (r.map i) = FourTriangleCore.degree s i)

def sourceHom (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic) :
    (FourTriangleCore.input s).graph →g G :=
  (hom s r degrees tri cyclic).comp (sourceIso s).toHom

theorem sourceHom_apply (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (v : Fin 16) : sourceHom s r degrees tri cyclic v =
      vertex s r degrees tri (relabel s v) := rfl

/-- No full boundary map or injectivity proof is supplied independently of
this same core reading. -/
def occurrence (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (injection : Function.Injective r.map)
    (reflect : ∀ i j, G.Adj (r.map i) (r.map j) → (FourTriangleCore.core s).Adj i j) :
    FourTriangleOccurrence.Occurrence s rotation where
  hom := sourceHom s r degrees tri cyclic
  turn := by
    intro d hd
    obtain ⟨i, p, hi, hp, hj, hq⟩ := source_turn s d hd
    obtain ⟨_, _, h⟩ := full_turn s r degrees tri cyclic i p
    simpa only [FourTriangleOccurrence.dart, sourceHom_apply, hi, hp, hj, hq] using h
  degree_eq := by
    intro v hv
    obtain ⟨i, hi, hd⟩ := core_reading s v hv
    rw [sourceHom_apply, hi, vertex_core, degrees, hd]
  core_injective := by
    intro a ha b hb eq
    obtain ⟨i, hi, _⟩ := core_reading s a ha
    obtain ⟨j, hj, _⟩ := core_reading s b hb
    rw [sourceHom_apply, sourceHom_apply, hi, hj, vertex_core, vertex_core] at eq
    apply (relabel s).injective
    rw [hi, hj, injection eq]
  outside := by
    intro p v hp hv
    obtain ⟨i, hi, _⟩ := core_reading s v hv
    let q : Fin 10 := ⟨(relabel s p).val, boundary_preserved s p hp⟩
    have pe : relabel s p = q.castAdd 6 := by apply Fin.ext; rfl
    rw [sourceHom_apply, sourceHom_apply, hi, pe, vertex_core]
    exact ring_outside_core s r degrees tri cyclic reflect q i

end FourColor.FourTriangleCompletedOccurrence

namespace FourColor.ActualFourTrianglePatch

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open GoertzelV24TwoEdgeCutMinimality
open MinimalExceptionalEmbedding (graph rotation)

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  (original : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample original)
  (s : Fin 2) (r : FourTriangleCore.Reading s (rotation original minimal))
  (degrees : ∀ i, (graph original minimal).degree (r.map i) = FourTriangleCore.degree s i)

/-- The four actual facial triangles and their six degrees construct the
entire occurrence needed by the reduction theorem. -/
def occurrence : FourTriangleOccurrence.Occurrence s (rotation original minimal) := by
  obtain ⟨inj, reflect⟩ := FourTriangleRecognition.embedded original minimal r degrees
  exact FourTriangleCompletedOccurrence.occurrence s r degrees
    (MinimalExceptionalEmbedding.triangular original minimal)
    (MinimalExceptionalEmbedding.cyclic original minimal) inj (fun i j => (reflect i j).mp)

include original minimal s r degrees in
/-- Recognition and strict reconstruction are connected without any
assumed exterior colouring, boundary completion or occurrence. -/
theorem not_in_minimal : False :=
  FourTriangleRepairGeometry.not_in_minimal s original minimal
    (occurrence original minimal s r degrees)

end
end FourColor.ActualFourTrianglePatch
