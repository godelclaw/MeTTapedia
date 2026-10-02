import MettapediaFourColor.ThreeTriangleFan

/-! The D0004 degree profile specializes the common facial-fan geometry.
The shared injectivity and inducedness laws also apply to other completed
boundary profiles. -/

namespace FourColor.ChainCoreReading

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open ExceptionalCoreOrientation ExceptionalOverlap NearLinearChainData

set_option maxRecDepth 32768

abbrev core := ThreeTriangleFan.core
abbrev star := ThreeTriangleFan.star
def spoke (i : Fin 5) (p : Fin (star i).length) := (star i).get p
abbrev first := ThreeTriangleFan.first
abbrev second := ThreeTriangleFan.second

def degree : Fin 5 → ℕ := ![5, 6, 5, 6, 5]

theorem star_specs : ∀ i : Fin 5,
    0 < (star i).length ∧ (star i).length < degree i ∧
      ∀ j, core.Adj i j ↔ ∃ p, spoke i p = j := by decide +kernel

abbrev spoke_injective := ThreeTriangleFan.spoke_injective
abbrev center_adj := ThreeTriangleFan.center_adj
abbrev step_partition := ThreeTriangleFan.step_partition
abbrev star_consecutive_adjacent := ThreeTriangleFan.star_consecutive_adjacent

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- The degree profile is retained alongside the shared facial geometry. -/
structure Reading (rotation : Data G) extends ThreeTriangleFan.Reading rotation where
  degree_eq : ∀ i, G.degree (map i) = degree i

variable {rotation : Data G} (r : Reading rotation)

theorem turns (tri : Triangular rotation) (i : Fin 5) (p q : Fin (star i).length)
    (next : q.val = p.val + 1) :
    Corner rotation (r.map i) (r.map (spoke i p)) (r.map (spoke i q)) :=
  ThreeTriangleFan.turns r.toReading tri i p q next

theorem proper (i : Fin 5) : (star i).length < G.degree (r.map i) := by
  rw [r.degree_eq]
  exact (star_specs i).2.1

variable [Finite V]

theorem neighbors_injective (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (i : Fin 5) : Function.Injective (fun p => r.map (spoke i p)) :=
  ThreeTriangleFan.neighbors_injective r.toReading (proper r) tri cyclic i

theorem injective (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic) :
    Function.Injective r.map :=
  ThreeTriangleFan.injective r.toReading (proper r) tri cyclic

theorem reflects (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (facial : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj c a →
      Corner rotation a b c ∨ Corner rotation a c b)
    (i j : Fin 5) (adj : G.Adj (r.map i) (r.map j)) : core.Adj i j :=
  ThreeTriangleFan.reflects r.toReading (proper r) tri cyclic facial i j adj

end FourColor.ChainCoreReading
