import Mettapedia.GraphTheory.FourColor.GoertzelLemma44

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- Minimal residual seed object extracted from the exact v23 Step 2 single-component
purification theorem. -/
structure V23ResidualBoundarySeed {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (a b : Color) (faceBoundary : Finset G.edgeSet) where
  component_purification :
    ∀ K : (C.bicoloredSubgraph a b).ConnectedComponent,
      v23PolarizedFaceGenerator C a b faceBoundary +
          v23PolarizedFaceGenerator (C.swapOnKempeComponent a b K) a b faceBoundary =
        componentBoundarySlice C a b faceBoundary K

/-- Finite initial residual state: the exact componentwise purification data together with the
already-proved recovery of the downstream boundary-only generator. -/
structure V23ResidualBoundaryInitialState {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (a b : Color) (faceBoundary : Finset G.edgeSet) where
  seed : V23ResidualBoundarySeed C a b faceBoundary
  sum_purification_eq_boundaryOnly :
    Finset.sum (boundaryKempeComponents C a b faceBoundary)
      (fun K : (C.bicoloredSubgraph a b).ConnectedComponent =>
        v23PolarizedFaceGenerator C a b faceBoundary +
          (v23PolarizedFaceGenerator (C.swapOnKempeComponent a b K) a b faceBoundary :
            G.edgeSet → Color)) =
      polarizedFaceGenerator C a b faceBoundary

theorem residualBoundarySeed_of_v23_single_component_purification
    {G : SimpleGraph V} (C : G.EdgeColoring Color)
    (a b : Color) (faceBoundary : Finset G.edgeSet) :
    V23ResidualBoundarySeed C a b faceBoundary := by
  exact ⟨fun K => v23_single_component_purification C a b faceBoundary K⟩

theorem residualBoundaryInitialState_of_sum_v23_single_component_purifications_eq_boundaryOnlyGenerator
    {G : SimpleGraph V} (C : G.EdgeColoring Color)
    (a b : Color) (faceBoundary : Finset G.edgeSet) :
    V23ResidualBoundaryInitialState C a b faceBoundary := by
  exact
    ⟨residualBoundarySeed_of_v23_single_component_purification C a b faceBoundary,
      sum_v23_single_component_purifications_eq_boundaryOnlyGenerator C a b faceBoundary⟩

end Mettapedia.GraphTheory.FourColor
