import MettapediaFourColor.ExtendedChainCore
import MettapediaFourColor.FanBoundaryScheme

/-! The nine-port D0006 completion uses the same owner-and-seam law as
the eight-port D0004 completion. The source relabelling retains all ordered
ports and the common five-vertex core. -/

namespace FourColor.ExtendedChainCompletion

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open NearLinearChainData ExceptionalOverlap

set_option maxRecDepth 32768

def rename : Fin 14 ≃ Fin 14 where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 13, 11, 12, 9, 10]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 12, 13, 10, 11, 9]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def shift : Fin 5 → ℕ := ![2, 1, 1, 1, 1]

def row (i : Fin 5) (n : ℕ) : Fin 14 :=
  rename.symm (((stars0006 (ExtendedChainCore.sourceCore i)).reverse.rotate (shift i)).getD n 0)

def owner : Fin 9 → Fin 5 × ℕ :=
  ![(0, 3), (0, 2), (2, 4), (2, 3), (3, 4), (3, 3), (4, 3), (4, 2), (1, 4)]

def scheme : FanBoundaryScheme.Scheme 9 where
  graph := input0006.graph.comap rename
  degree := ExtendedChainCore.degree
  proper := ExtendedChainCore.proper_degrees
  row := row
  owner := owner
  owner_bounds := by decide +kernel
  core_prefix := by decide +kernel
  ring_cases := by decide +kernel
  edge_reading := by decide +kernel

def sourceIso : scheme.graph ≃g input0006.graph where
  toEquiv := rename
  map_rel_iff' := Iff.rfl

theorem rename_core : ∀ i : Fin 5,
    rename (i.natAdd 9) = ExtendedChainCore.sourceCore i := by decide +kernel

theorem rename_ring : ∀ p : Fin 9, rename (p.castAdd 5) = p.castAdd 5 := by decide +kernel

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {rotation : Data G}
  (r : ExtendedChainCore.Reading rotation)

def reading : FanBoundaryScheme.Reading scheme rotation where
  toReading := r.toReading
  degree_eq := r.degree_eq

def vertex (v : Fin 14) : V := FanBoundaryScheme.vertex (reading r) (rename.symm v)

theorem vertex_core (i : Fin 5) : vertex r (ExtendedChainCore.sourceCore i) = r.map i := by
  unfold vertex
  rw [← rename_core, Equiv.symm_apply_apply, FanBoundaryScheme.vertex_core]
  rfl

theorem vertex_rename (v : Fin 14) :
    vertex r (rename v) = FanBoundaryScheme.vertex (reading r) v := by
  unfold vertex
  rw [Equiv.symm_apply_apply]

theorem vertex_near (v : Fin 14) :
    vertex r v ∈ LocalCoverageAssembly.closedBall G (r.map 1) 2 :=
  FanBoundaryScheme.vertex_near (reading r) (rename.symm v)

variable [Finite V]

/-- The same completion law reconstructs every source edge, including the
new port's edges. No independent boundary witnesses are supplied. -/
def hom (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic) :
    input0006.graph →g G :=
  (FanBoundaryScheme.hom (reading r) tri cyclic).comp sourceIso.symm.toHom

theorem hom_apply (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (v : Fin 14) : hom r tri cyclic v = vertex r v := rfl

end FourColor.ExtendedChainCompletion
