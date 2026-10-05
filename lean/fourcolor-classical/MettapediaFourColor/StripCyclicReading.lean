import MettapediaFourColor.CyclicCoreStars
import MettapediaFourColor.TriangleStripAnchors

/-! # Complete cyclic readings of D0099

The turns are decoded from the full pinned source rows. Preserving them
forces complete ambient core stars, even when boundary vertices coincide.
Interior injectivity and boundary separation are separate reconstruction
obligations; neither is assumed by the star theorem.
-/

namespace FourColor.StripCyclicReading

open SimpleGraph TriangleStripAnchors
open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation ExceptionalCoreOrientation

set_option maxRecDepth 10000

def Turn (i j k : Fin 19) : Prop :=
  11 ≤ i.val ∧ (j.val + 1, k.val + 1) ∈
    (input0099.neighbors i).zip ((input0099.neighbors i).rotate 1)

instance (i j k) : Decidable (Turn i j k) := inferInstanceAs (Decidable (_ ∧ _))

theorem core_nonempty : ∀ i : Fin 19, 11 ≤ i.val → ∃ j, input0099.graph.Adj i j := by
  decide +kernel

set_option maxHeartbeats 2000000 in
theorem core_predecessor : ∀ i j : Fin 19, 11 ≤ i.val → input0099.graph.Adj i j →
    ∃ k, input0099.graph.Adj i k ∧ Turn i k j := by decide +kernel

variable {V : Type*} {G : SimpleGraph V}

structure Reading (data : Data G) where
  hom : input0099.graph →g G
  turn : ∀ i j k, Turn i j k → Corner data (hom i) (hom k) (hom j)

theorem Reading.core_stars [Finite V] {data : Data G} (r : Reading data)
    (cyclic : data.IsVertexwiseCyclic) (i : Fin 19) (hi : 11 ≤ i.val)
    (v : V) (edge : G.Adj (r.hom i) v) :
    ∃ j, input0099.graph.Adj i j ∧ r.hom j = v := by
  have predecessor (j) (hj : input0099.graph.Adj i j) :
      ∃ k, input0099.graph.Adj i k ∧ Corner data (r.hom i) (r.hom j) (r.hom k) := by
    obtain ⟨k, hk, turn⟩ := core_predecessor i j hi hj
    exact ⟨k, hk, r.turn i k j turn⟩
  obtain ⟨j, hj, adj⟩ := CyclicCoreStars.covers data cyclic r.hom i
    (core_nonempty i hi) predecessor v edge
  exact ⟨j, adj, hj⟩

end FourColor.StripCyclicReading
