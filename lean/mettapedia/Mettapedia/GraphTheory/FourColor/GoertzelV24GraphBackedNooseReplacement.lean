import Mettapedia.GraphTheory.FourColor.GoertzelV24DualNooseLiteralReplacement
import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalGraphBackedPresentation

/-!
# Graph-backed output of physical noose replacement

The literal equal-state splice and terminating digon normalization return an
endpoint-simple rotation-system counterexample.  This file closes the final
representation boundary of M2: endpoint injectivity constructs the canonical
primal simple graph, transports the rotation data and the complete cap-stable
structural class, and reflects any graph-backed Tait colouring to the literal
rotation system.

The final theorem specializes this generic transport to two nested facial-dual
nooses.  Thus its conclusion is already in the graph-backed normal class used
by the decomposition supplier; no presentation claim remains implicit.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24GraphBackedNooseReplacement

open GoertzelV24DualNooseLiteralReplacement
open GoertzelV24FaceDualConnectedness
open GoertzelV24IteratedDigonNormalization
open GoertzelV24MinimalGraphBackedPresentation
open GoertzelV24RotationSystemPrimalGraphBacking
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation

noncomputable section

universe u

/-- A graph-backed zero-Tait-count member of the complete cap-stable class
with strictly fewer than `bound` vertices. -/
def GraphBackedCounterexampleBelow (bound : Nat) : Prop :=
  ∃ (V' : Type u),
    ∃ (_ : Fintype V') (_ : DecidableEq V'),
    ∃ (G' : SimpleGraph V'),
      ∃ (_ : DecidableRel G'.Adj),
      ∃ graphData : Data G',
        BridgelessSphericalCubicMapData graphData.toRotationSystem ∧
          ¬ RotationSystemTaitColorable graphData.toRotationSystem ∧
          Fintype.card V' < bound

/-- Canonical graph backing preserves every field returned by endpoint-simple
normalization, including zero Count and the strict vertex bound. -/
theorem graphBackedCounterexampleBelow_of_endpointSimpleCounterexampleBelow
    {bound : Nat}
    (counterexample : EndpointSimpleCounterexampleBelow.{u} bound) :
    GraphBackedCounterexampleBelow.{u} bound := by
  classical
  obtain ⟨V', E', iV', dV', iE', dE', RS', hclass, hnot,
      hinjective, hcard⟩ := counterexample
  letI : Fintype V' := iV'
  letI : DecidableEq V' := dV'
  letI : Fintype E' := iE'
  letI : DecidableEq E' := dE'
  let G' : SimpleGraph V' := rotationPrimalGraph RS'
  letI : DecidableRel G'.Adj := Classical.decRel _
  let backing : Data G' := graphData RS' hinjective
  refine ⟨V', inferInstance, inferInstance, G', inferInstance, backing,
    ?_, ?_, hcard⟩
  · exact graphData_bridgelessSphericalCubicMapData
      RS' hinjective hclass
  · intro hgraphColorable
    exact hnot
      (rotationSystemTaitColorable_of_graphData
        RS' hinjective hgraphColorable)

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]

/-- **Graph-backed actual-noose form of M2.**  Two bounded facial-dual
nooses with strictly nested literal shores and equal computed phased states
construct a strictly smaller graph-backed zero-Tait-count map in the full
bridgeless spherical cubic class.  Exact bonds, physical gluing, strict loss,
parallel-seam normalization and canonical graph backing are all constructed
inside the theorem. -/
theorem exists_graphBackedCounterexampleBelow_of_nested_dualNooses
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (w : Nat)
    (oldNoose newNoose : DualNooseSide graphData minimal)
    (hOldLength : oldNoose.walk.length ≤ w)
    (hNewLength : newNoose.walk.length ≤ w)
    (hOldComplementTwo :
      2 ≤ (Finset.univ \ oldNoose.shore).card)
    (hNewComplementTwo :
      2 ≤ (Finset.univ \ newNoose.shore).card)
    (hproper : newNoose.shore ⊂ oldNoose.shore)
    (heq :
      (oldNoose.toConnectedShoreNode w hOldLength hOldComplementTwo).cardPhasedState
          graphData minimal =
        (newNoose.toConnectedShoreNode w hNewLength hNewComplementTwo).cardPhasedState
          graphData minimal) :
    GraphBackedCounterexampleBelow.{u} (Fintype.card V) :=
  graphBackedCounterexampleBelow_of_endpointSimpleCounterexampleBelow
    (exists_endpointSimple_replacement_of_nested_dualNooses
      graphData minimal w oldNoose newNoose
      hOldLength hNewLength hOldComplementTwo hNewComplementTwo hproper heq)

end

end GoertzelV24GraphBackedNooseReplacement

end Mettapedia.GraphTheory.FourColor
