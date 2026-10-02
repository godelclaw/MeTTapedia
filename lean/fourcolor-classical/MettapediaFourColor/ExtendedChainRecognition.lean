import MettapediaFourColor.ExtendedChainOccurrence

/-! The shared fan completion supplies every observation of the actual
nine-port occurrence. Inducedness excludes capture of a boundary port by
the core, while different exterior ports may still identify. -/

namespace FourColor.ExtendedChainRecognition

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open NearLinearChainData ExceptionalCoreOrientation ExceptionalOverlap
open ExtendedChainCore ExtendedChainCompletion

set_option maxRecDepth 32768

theorem source_degree : ∀ i : Fin 5, degree007 (sourceCore i) = degree i := by decide +kernel

theorem source_turn : ∀ d : Fin 60, 9 ≤ (vertex007 d).val →
    ∃ (i : Fin 5) (p : Fin (degree i)),
      vertex007 d = sourceCore i ∧
      vertex007 (table007.map.edge d) = rename (row i p.val) ∧
      vertex007 (table007.map.face d) = sourceCore i ∧
      vertex007 (table007.map.edge (table007.map.face d)) =
        rename (row i (FanBoundaryScheme.nextPos scheme i p).val) := by decide +kernel

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] [Finite V]
  {rotation : Data G} (r : ExtendedChainCore.Reading rotation)

theorem full_turn (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (i : Fin 5) (p : Fin (degree i)) :
    Corner rotation (vertex r (sourceCore i)) (vertex r (rename (row i p.val)))
      (vertex r (rename (row i (FanBoundaryScheme.nextPos scheme i p).val))) := by
  simpa only [vertex_rename, vertex_core, FanBoundaryScheme.vertex_core, scheme, reading] using
    FanBoundaryScheme.full_turn (reading r) tri cyclic i p

theorem outside (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (reflect : ∀ i j, G.Adj (r.map i) (r.map j) → ThreeTriangleFan.core.Adj i j)
    (p : Fin 9) (i : Fin 5) : vertex r (p.castAdd 5) ≠ r.map i := by
  have h := FanBoundaryScheme.ring_outside_core (reading r) tri cyclic reflect p i
  rw [← vertex_rename, rename_ring] at h
  exact h

/-- The full fourteen-vertex source is reconstructed from the same five
core vertices and their three compatible facial readings. -/
def occurrence (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (reflect : ∀ i j, G.Adj (r.map i) (r.map j) → ThreeTriangleFan.core.Adj i j) :
    ExtendedChainOccurrence.Occurrence rotation where
  hom := hom r tri cyclic
  turn := by
    intro d hd
    obtain ⟨i, p, hi, hp, hj, hq⟩ := source_turn d hd
    obtain ⟨_, _, h⟩ := full_turn r tri cyclic i p
    simpa only [ExtendedChainOccurrence.dart, hom_apply, hi, hp, hj, hq] using h
  degree_eq := by
    intro v hv
    obtain ⟨i, rfl⟩ := (source_core v).mp hv
    change G.degree (vertex r (sourceCore i)) = _
    rw [vertex_core, r.degree_eq]
    exact (source_degree i).symm
  core_injective := by
    intro a ha b hb eq
    obtain ⟨i, rfl⟩ := (source_core a).mp ha
    obtain ⟨j, rfl⟩ := (source_core b).mp hb
    change vertex r (sourceCore i) = vertex r (sourceCore j) at eq
    rw [vertex_core, vertex_core] at eq
    exact congrArg sourceCore (ExtendedChainCore.injective r tri cyclic eq)
  outside := by
    intro p v hp hv
    obtain ⟨i, rfl⟩ := (source_core v).mp hv
    let q : Fin 9 := ⟨p.val, hp⟩
    have pe : p = q.castAdd 5 := by apply Fin.ext; rfl
    change vertex r p ≠ vertex r (sourceCore i)
    rw [pe, vertex_core]
    exact outside r tri cyclic reflect q i

end FourColor.ExtendedChainRecognition
