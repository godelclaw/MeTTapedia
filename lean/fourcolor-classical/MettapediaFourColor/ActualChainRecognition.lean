import MettapediaFourColor.ChainCoreOccurrence
import MettapediaFourColor.ActualChainReduction

/-!
# A three-triangle fan supplies an actual chain reduction

Only the five core vertices, their degrees and three facial readings are
supplied. Actual minimality makes every triangle facial, so the common
centre prevents extra core edges. The full interface is then constructed
and consumed by the previously certified reconstruction theorem.
-/

namespace FourColor.ActualChainRecognition

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open GoertzelV24TwoEdgeCutMinimality

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  (original : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample original)

local instance : (MinimalExceptionalEmbedding.graph original minimal).LocallyFinite :=
  fun _ => Fintype.ofFinite _

/-- The core fan constructs a complete occurrence without an assumed
embedding, injectivity, boundary completion or colouring. -/
def occurrence
    (r : ChainCoreReading.Reading (MinimalExceptionalEmbedding.rotation original minimal)) :
    NearLinearChainOccurrence.Occurrence
      (MinimalExceptionalEmbedding.rotation original minimal) := by
  classical
  exact ChainCoreOccurrence.occurrence r
    (MinimalExceptionalEmbedding.triangular original minimal)
    (MinimalExceptionalEmbedding.cyclic original minimal)
    (ChainCoreReading.reflects r (MinimalExceptionalEmbedding.triangular original minimal)
      (MinimalExceptionalEmbedding.cyclic original minimal)
      (fun _ _ _ => MinimalExceptionalEmbedding.triangle_facial original minimal))

theorem not_in_minimal
    (r : ChainCoreReading.Reading (MinimalExceptionalEmbedding.rotation original minimal)) : False :=
  ActualChainReduction.not_in_minimal original minimal (occurrence original minimal r)

end
end FourColor.ActualChainRecognition
