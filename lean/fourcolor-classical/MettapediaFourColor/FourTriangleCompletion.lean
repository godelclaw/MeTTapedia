import MettapediaFourColor.FourTriangleCore
import MettapediaFourColor.FacialBoundaryScheme

/-!
# Joint boundary completion for the fan and tripod

One owner-and-seam construction reads every source vertex from the same six
core vertices and four faces. It preserves complete source stars, degrees
and all edges. Both layouts use the positive published source orientation.
This is distinct from the reversed classical presentation of D0052.
-/

namespace FourColor.FourTriangleCompletion

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open ExceptionalCoreOrientation ExceptionalOverlap

set_option maxRecDepth 32768

variable (s : Fin 2)

def core : FacialBoundaryScheme.Core 6 where
  graph := FourTriangleCore.core s
  star := FourTriangleCore.star s
  positive := fun i => (FourTriangleCore.star_specs s i).1
  adjacent := fun i => (FourTriangleCore.star_specs s i).2.2
  seam := by revert s; decide +kernel

def shift : Fin 2 → Fin 6 → ℕ := ![![2, 2, 1, 2, 1, 1], ![2, 1, 1, 2, 2, 1]]

def row (i : Fin 6) (n : ℕ) : Fin 16 :=
  (((FourTriangleCore.input s).internalStar (i.natAdd 10)).rotate (shift s i)).getD n 0

def owner : Fin 2 → Fin 10 → Fin 6 × ℕ :=
  ![![(4, 3), (5, 3), (3, 3), (3, 4), (1, 3), (1, 4), (0, 2), (0, 3), (2, 5), (4, 2)],
    ![(5, 3), (3, 4), (3, 5), (4, 2), (4, 3), (2, 4), (0, 2), (0, 3), (1, 4), (5, 2)]]

def scheme : FacialBoundaryScheme.Scheme (core s) 10 where
  graph := (FourTriangleCore.input s).graph
  degree := FourTriangleCore.degree s
  proper := fun i => (FourTriangleCore.star_specs s i).2.1
  row := row s
  owner := owner s
  owner_bounds := by revert s; decide +kernel
  core_prefix := by revert s; decide +kernel
  ring_cases := by revert s; decide +kernel
  edge_reading := by revert s; decide +kernel

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {rotation : Data G}
  (r : FourTriangleCore.Reading s rotation)
  (degrees : ∀ i, G.degree (r.map i) = FourTriangleCore.degree s i)
  (tri : Triangular rotation)

def reading : FacialBoundaryScheme.Reading (core s) (scheme s) rotation where
  map := r.map
  turns := FourTriangleCore.turns r tri
  degree_eq := degrees

def vertex (v : Fin 16) : V := FacialBoundaryScheme.vertex (core s) (reading s r degrees tri) v

theorem vertex_core (i : Fin 6) : vertex s r degrees tri (i.natAdd 10) = r.map i :=
  FacialBoundaryScheme.vertex_core (core s) (reading s r degrees tri) i

variable [Finite V] (cyclic : rotation.IsVertexwiseCyclic)

def hom : (FourTriangleCore.input s).graph →g G :=
  FacialBoundaryScheme.hom (core s) (reading s r degrees tri) tri cyclic

theorem hom_apply (v : Fin 16) : hom s r degrees tri cyclic v = vertex s r degrees tri v := rfl

include cyclic

/-- Every full source star, including its previously unknown boundary arc,
is reconstructed in the actual rotation. -/
theorem full_turn (i : Fin 6) (p : Fin (FourTriangleCore.degree s i)) :
    Corner rotation (vertex s r degrees tri (i.natAdd 10))
      (vertex s r degrees tri (row s i p.val))
      (vertex s r degrees tri (row s i ((p.val + 1) % FourTriangleCore.degree s i))) :=
  FacialBoundaryScheme.full_turn (core s) (reading s r degrees tri) tri cyclic i p

/-- The same induced core protects both complete boundaries from core capture. -/
theorem ring_outside_core
    (reflect : ∀ i j, G.Adj (r.map i) (r.map j) → (FourTriangleCore.core s).Adj i j)
    (p : Fin 10) (j : Fin 6) : vertex s r degrees tri (p.castAdd 6) ≠ r.map j :=
  FacialBoundaryScheme.ring_outside_core (core s) (reading s r degrees tri) tri cyclic reflect p j

end FourColor.FourTriangleCompletion
