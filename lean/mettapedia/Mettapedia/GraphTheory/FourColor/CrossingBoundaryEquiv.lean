import Mettapedia.GraphTheory.FourColor.GoertzelV24VertexSidePrimalKempeTrail
import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicSmallBoundaryCycle

/-!
# The exact graph-cut and rotation-boundary correspondence

Both representations retain the same actual dart and the same shore
predicates. This equivalence is shared by six- and seven-port consumers.
-/

namespace Mettapedia.GraphTheory.FourColor.MatchingBoundaryConnectivity

open GoertzelV24CubicSmallBoundaryCycle GoertzelV24RotationCutDartDecomposition

noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The graph-cut dart and rotation-system port retain the same actual dart. -/
def crossingBoundaryEquiv (rotation : SimpleGraphDartRotation.Data G) (keep : V → Prop) :
    CrossingSideDart G keep ≃ BoundaryDart rotation.toRotationSystem keep where
  toFun d := ⟨⟨d.1, d.2.1⟩, d.2.2⟩
  invFun b := ⟨b.1.1, b.1.2, b.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end
end Mettapedia.GraphTheory.FourColor.MatchingBoundaryConnectivity
