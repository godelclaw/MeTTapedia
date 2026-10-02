import MettapediaFourColor.ChainFanRecognition

/-!
# The second degree profile of the same three-triangle fan

The D0006 core has the same seven edges and facial intervals as D0004.
Only the degree of the second-to-last observed neighbour changes, from
five to six. The shared fan geometry supplies injectivity and inducedness.
Completing the additional boundary port is a separate obligation.
-/

namespace FourColor.ExtendedChainCore

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open ExceptionalCoreOrientation ExceptionalOverlap NearLinearChainData
open ThreeTriangleFan

def sourceCore : Fin 5 → Fin 14 := ![13, 11, 12, 9, 10]
def degree : Fin 5 → ℕ := ![5, 6, 6, 6, 5]
def word : Fin 4 → ℕ := ![5, 6, 6, 5]

theorem source_injective : Function.Injective sourceCore := by decide +kernel

theorem source_edges : ∀ i j : Fin 5,
    input0006.graph.Adj (sourceCore i) (sourceCore j) ↔ core.Adj i j := by
  decide +kernel

theorem source_degrees : ∀ i : Fin 5,
    (stars0006 (sourceCore i)).length = degree i := by decide +kernel

theorem source_core : ∀ v : Fin 14, 9 ≤ v.val ↔ ∃ i, sourceCore i = v := by
  decide +kernel

theorem proper_degrees : ∀ i : Fin 5, (star i).length < degree i := by decide +kernel

theorem degrees : ∀ i : Fin 5, i ≠ 1 →
    ∃ n : Fin 4, ChainFanRecognition.position i = n.val ∧ degree i = word n := by
  decide +kernel

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

structure Reading (rotation : Data G) extends ThreeTriangleFan.Reading rotation where
  degree_eq : ∀ i, G.degree (map i) = degree i

variable {rotation : Data G} (r : Reading rotation)

theorem proper (i : Fin 5) : (star i).length < G.degree (r.map i) := by
  rw [r.degree_eq]
  exact proper_degrees i

/-- All vertices come from the same rotation walk, rather than independent
choices for the three triangles. -/
def of_word (tri : Triangular rotation) (d : G.Dart)
    (center : G.degree d.fst = 6)
    (neighbors : ∀ n : Fin 4,
      G.degree (ChainFanRecognition.walk rotation d n.val).snd = word n) :
    Reading rotation where
  map := ChainFanRecognition.hom rotation tri d
  face := ChainFanRecognition.face rotation d
  degree_eq := by
    intro i
    change G.degree (ChainFanRecognition.vertex rotation d i) = degree i
    by_cases hi : i = 1
    · subst i
      rw [ChainFanRecognition.vertex_center, center]
      rfl
    · obtain ⟨n, hn, hd⟩ := degrees i hi
      rw [ChainFanRecognition.vertex_other rotation d i hi, hn, neighbors, hd]

variable [Finite V]

theorem injective (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic) :
    Function.Injective r.map :=
  ThreeTriangleFan.injective r.toReading (proper r) tri cyclic

theorem reflects (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (facial : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj c a →
      Corner rotation a b c ∨ Corner rotation a c b)
    (i j : Fin 5) (adj : G.Adj (r.map i) (r.map j)) : core.Adj i j :=
  ThreeTriangleFan.reflects r.toReading (proper r) tri cyclic facial i j adj

end FourColor.ExtendedChainCore
