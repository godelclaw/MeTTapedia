import MettapediaFourColor.StripCyclicReading
import MettapediaFourColor.StripSixJointReconstruction

/-! # Joint strip repair from actual cyclic core readings

The complete ambient stars are derived from the cyclic reading. Only core
vertices must be distinct; the boundary can identify vertices while retaining
one compatible exterior colouring. Exterior closure and the initial boundary
class remain explicit, so this is not a coverage theorem.
-/

namespace FourColor.StripCyclicReading

open SimpleGraph TriangleStripAnchors StripResponseSummary KempeBoundarySplit
open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation

theorem Reading.whole_repair {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} {data : Data G}
    (r : Reading data) (cyclic : data.IsVertexwiseCyclic)
    (injective : Set.InjOn r.hom {i : Fin 19 | 11 ≤ i.val})
    (no_capture : ∀ a : Fin 19, ¬11 ≤ a.val →
      r.hom a ∉ r.hom '' {i : Fin 19 | 11 ≤ i.val})
    (e : H ↪g G)
    (outside : ∀ w, e w ∉ r.hom '' {i : Fin 19 | 11 ≤ i.val})
    (covers : ∀ v, v ∉ r.hom '' {i : Fin 19 | 11 ≤ i.val} → ∃ w, e w = v)
    (ports : Fin 11 → W) (boundary : ∀ i, e (ports i) = r.hom (port i))
    (closed : KempeClosed (GraphTrace H (List.ofFn ports)))
    (s : Bool) (C : H.Coloring Color)
    (initial : ∀ i, C (ports i) = StripSixConnection.input s i) :
    Fintype.card W < Fintype.card V ∧
      ∃ D : H.Coloring Color, ∃ K : G.Coloring Color, ∀ w, K (e w) = D w := by
  exact StripSixJointRepair.whole_repair_of_core_injective r.hom injective no_capture
    e outside covers (r.core_stars cyclic) ports boundary closed s C initial

end FourColor.StripCyclicReading
