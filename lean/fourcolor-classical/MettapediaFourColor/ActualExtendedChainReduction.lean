import MettapediaFourColor.ExtendedChainRecognition
import MettapediaFourColor.ExtendedChainContract

/-!
# Actual nine-port chain reduction from vertex minimality

The retained local occurrence constructs the disk embedding. A singleton
contract colouring is supplied by the smaller-map theorem, and planar
exterior closure supplies the compatible boundary relation. The existing
configuration-7 repair then reconstructs the original colouring.
No exterior colouring or closure hypothesis is supplied by the caller.
-/

namespace FourColor.ActualExtendedChainReduction

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open GoertzelV24TwoEdgeCutMinimality Hypermap
open ExtendedChainOccurrence

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  (original : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample original)

/-- Actual geometry and minimality supply the initial witness, the exterior
closure, the repaired interior and the complete reconstructed colouring. -/
theorem colorable
    (r : Occurrence (MinimalExceptionalEmbedding.rotation original minimal)) :
    (DualGraphQuery.map (MinimalExceptionalEmbedding.rotation original minimal)).FourColorable := by
  classical
  let h := reading r
  let M := DualGraphQuery.map (MinimalExceptionalEmbedding.rotation original minimal)
  obtain ⟨k, initial⟩ := ActualDualContract.singleton_colorable original minimal
    (embed (cfmap config).map M (cfring config) h ExtendedChainContract.contractDart)
  exact InjectiveEmbeddedRepair.colorable embeddable
    (ActualDualLocalGeometry.planar original minimal) (DualGraphQuery.plain _)
    (DualGraphQuery.cubic _ (MinimalExceptionalEmbedding.triangular original minimal))
    (preembedding r (MinimalExceptionalEmbedding.cyclic original minimal))
    (disk_injective r (MinimalExceptionalEmbedding.cyclic original minimal)
      (MinimalExceptionalEmbedding.triangular original minimal))
    ExtendedChainContract.singleton_reducible initial

/-- Actual minimality supplies facial triangles, and the common fan
geometry constructs the occurrence from its core alone. -/
def occurrence
    (r : ExtendedChainCore.Reading (MinimalExceptionalEmbedding.rotation original minimal)) :
    Occurrence (MinimalExceptionalEmbedding.rotation original minimal) :=
  ExtendedChainRecognition.occurrence r
    (MinimalExceptionalEmbedding.triangular original minimal)
    (MinimalExceptionalEmbedding.cyclic original minimal)
    (ExtendedChainCore.reflects r (MinimalExceptionalEmbedding.triangular original minimal)
      (MinimalExceptionalEmbedding.cyclic original minimal)
      (fun _ _ _ => MinimalExceptionalEmbedding.triangle_facial original minimal))

theorem not_in_minimal
    (r : ExtendedChainCore.Reading
      (MinimalExceptionalEmbedding.rotation original minimal)) : False :=
  ActualDualContract.not_colorable original minimal
    (colorable original minimal (occurrence original minimal r))

/-- The degree word supplies all core and boundary observations. -/
theorem not_degree_word
    (d : (MinimalExceptionalEmbedding.graph original minimal).Dart)
    (center : (MinimalExceptionalEmbedding.graph original minimal).degree d.fst = 6)
    (neighbors : ∀ n : Fin 4,
      (MinimalExceptionalEmbedding.graph original minimal).degree
        (ChainFanRecognition.walk
          (MinimalExceptionalEmbedding.rotation original minimal) d n.val).snd =
          ExtendedChainCore.word n) : False :=
  not_in_minimal original minimal
    (ExtendedChainCore.of_word (G := MinimalExceptionalEmbedding.graph original minimal)
      (MinimalExceptionalEmbedding.triangular original minimal)
      d center neighbors)

end
end FourColor.ActualExtendedChainReduction
