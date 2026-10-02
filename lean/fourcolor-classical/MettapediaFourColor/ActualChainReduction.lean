import MettapediaFourColor.NearLinearChainOccurrence
import MettapediaFourColor.NearLinearChainContract

/-!
# Actual chain reduction from vertex minimality

The retained local occurrence constructs the disk embedding. A singleton
contract colouring is supplied by the smaller-map theorem, and planar
exterior closure supplies the compatible boundary relation. The shared
boundary-subdivision repair then reconstructs the original colouring.
No exterior colouring or closure hypothesis is supplied by the caller.
-/

namespace FourColor.ActualChainReduction

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open GoertzelV24TwoEdgeCutMinimality Hypermap
open NearLinearChainConstruction NearLinearChainOccurrence

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  (original : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample original)

local instance : (MinimalExceptionalEmbedding.graph original minimal).LocallyFinite :=
  fun _ => Fintype.ofFinite _

/-- Actual geometry and minimality supply the initial witness, the exterior
closure, the repaired interior and the complete reconstructed colouring. -/
theorem colorable
    (r : Occurrence (MinimalExceptionalEmbedding.rotation original minimal)) :
    (DualGraphQuery.map (MinimalExceptionalEmbedding.rotation original minimal)).FourColorable := by
  classical
  let h := reading r
  let M := DualGraphQuery.map (MinimalExceptionalEmbedding.rotation original minimal)
  obtain ⟨k, initial⟩ := ActualDualContract.singleton_colorable original minimal
    (embed (cfmap config).map M (cfring config) h NearLinearChainContract.contractDart)
  exact InjectiveEmbeddedRepair.colorable embeddable
    (ActualDualLocalGeometry.planar original minimal) (DualGraphQuery.plain _)
    (DualGraphQuery.cubic _ (MinimalExceptionalEmbedding.triangular original minimal))
    (preembedding r (MinimalExceptionalEmbedding.cyclic original minimal))
    (disk_injective r (MinimalExceptionalEmbedding.cyclic original minimal)
      (MinimalExceptionalEmbedding.triangular original minimal))
    NearLinearChainContract.singleton_reducible initial

theorem not_in_minimal
    (r : Occurrence (MinimalExceptionalEmbedding.rotation original minimal)) : False :=
  ActualDualContract.not_colorable original minimal (colorable original minimal r)

end
end FourColor.ActualChainReduction
