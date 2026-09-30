import Mettapedia.GraphTheory.FourColor.PentagonalCoronaNoncollision
import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalFaceSize

/-! # Girth hypotheses for partial-diagram recognition

In a cubic cyclically five-edge-connected simple graph, a triangle leaves
only one exterior vertex and a four-cycle leaves at most two. More than six
vertices therefore supplies both short-cycle exclusions used by recognition.
-/

namespace Mettapedia.GraphTheory.FourColor.PartialCubicDartSeparation.Realization

open _root_.SimpleGraph SimpleGraphDartRotation GoertzelV24MinimalFaceSize
open GoertzelV24CubicSmallBoundaryCycle

noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance normalFormEdgeDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

theorem girth_of_cyclicallyFive (rotation : Data G)
    (hcubic : G.IsRegularOfDegree 3) (hcyclic : CyclicallyFiveEdgeConnected G)
    (hsize : 6 < Fintype.card V) : TriangleFree (G := G) ∧ FourCycleFree (G := G) := by
  refine ⟨PentagonalCoronaGeometry.triangleFree_of_cyclicallyFive_of_four_lt_card
    rotation hcubic hcyclic (by omega), ?_⟩
  intro a b c d hab hbc hcd hda hac hbd
  have hcomp := natCard_complement_fourCycle_le_two_of_cyclicallyFive rotation
    (fun v => (degree_instance_independent v _ _).trans (hcubic v))
    hcyclic hab hbc hcd hda hac hbd
  have hcard := fintype_card_eq_four_add_complement_fourCycle
    hab.ne hac hda.symm.ne hbc.ne hbd hcd.ne
  omega

end
end Mettapedia.GraphTheory.FourColor.PartialCubicDartSeparation.Realization
