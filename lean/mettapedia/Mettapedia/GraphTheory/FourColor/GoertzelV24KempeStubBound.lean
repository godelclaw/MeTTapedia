import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# A Kempe component carries at most two stubs

In a properly three-edge-coloured cubic graph, a two-coloured subgraph has
degree exactly two at every interior vertex and degree one at a boundary
stub.  Such a component is therefore a path between two stubs, or a cycle
carrying none — so it never holds three.

That is the shape of the statement; the content is a counting fact needing
no colours at all: a connected graph of maximum degree two has at most two
vertices of degree one.  Connectedness supplies `edges ≥ vertices - 1`, the
handshake identity turns the degree bound into `2·edges ≤ 2·vertices - d`,
and the two together force `d ≤ 2`.

The bound is about the *open* structure, where stubs genuinely have degree
one.  Closing the boundary makes every degree two and the components become
cycles, which may pass through arbitrarily many former stub positions.  The
two counts measure different things and neither bounds the other.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24KempeStubBound

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The vertices of degree one: the stubs of the component. -/
def stubs (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter fun v => G.degree v = 1

/-- **At most two stubs.**  A connected graph of maximum degree two has at
most two vertices of degree one. -/
theorem card_stubs_le_two (hconn : G.Connected) (hdeg : ∀ v, G.degree v ≤ 2) :
    (stubs G).card ≤ 2 := by
  classical
  set D := stubs G with hD
  -- the handshake identity
  have hsum : ∑ v, G.degree v = 2 * G.edgeFinset.card :=
    G.sum_degrees_eq_twice_card_edges
  -- degree one on the stubs, at most two elsewhere
  have hsplit : (∑ v, G.degree v) + D.card ≤ 2 * Fintype.card V := by
    have hdecomp : (∑ v ∈ D, G.degree v) + (∑ v ∈ Dᶜ, G.degree v)
        = ∑ v, G.degree v := Finset.sum_add_sum_compl D _
    have hone : ∑ v ∈ D, G.degree v = D.card := by
      rw [Finset.sum_congr rfl (fun v hv => ?_), Finset.sum_const, smul_eq_mul,
        mul_one]
      simp only [hD, stubs, Finset.mem_filter] at hv
      exact hv.2
    have htwo : ∑ v ∈ Dᶜ, G.degree v ≤ 2 * Dᶜ.card := by
      calc ∑ v ∈ Dᶜ, G.degree v ≤ ∑ _v ∈ Dᶜ, 2 :=
            Finset.sum_le_sum fun v _ => hdeg v
        _ = 2 * Dᶜ.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have hcompl : Dᶜ.card = Fintype.card V - D.card := by
      rw [Finset.card_compl]
    have hle : D.card ≤ Fintype.card V := Finset.card_le_univ D
    rw [← hdecomp, hone]
    omega
  -- connectedness supplies enough edges
  have hedge : Fintype.card V ≤ G.edgeFinset.card + 1 := by
    have := hconn.card_vert_le_card_edgeSet_add_one
    simpa [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset,
      Set.toFinset_card] using this
  omega

end GoertzelV24KempeStubBound

end Mettapedia.GraphTheory.FourColor
