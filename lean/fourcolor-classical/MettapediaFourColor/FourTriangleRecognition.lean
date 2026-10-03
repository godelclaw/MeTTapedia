import MettapediaFourColor.FourTriangleCore
import MettapediaFourColor.MinimalExceptionalEmbedding

/-!
# Actual-map recognition of the fan and tripod cores

Vertex minimality supplies the facial-triangle and cyclic-rotation laws.
The four retained face readings then determine an injective induced core,
for both D0051 and D0052. This does not yet construct either complete
ten-port occurrence or supply its colouring repair.
-/

namespace FourColor.FourTriangleRecognition

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open GoertzelV24TwoEdgeCutMinimality FourTriangleCore
open MinimalExceptionalEmbedding (graph rotation)

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  (original : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample original)

/-- Geometry is supplied by the same actual minimal map. In particular,
injectivity and the absence of extra core edges are conclusions. -/
theorem embedded {s : Fin 2} (r : Reading s (rotation original minimal))
    (degrees : ∀ i, (graph original minimal).degree (r.map i) = degree s i) :
    Function.Injective r.map ∧ ∀ i j,
      (graph original minimal).Adj (r.map i) (r.map j) ↔ (core s).Adj i j :=
  source_profile_embedding r degrees
    (MinimalExceptionalEmbedding.triangular original minimal)
    (MinimalExceptionalEmbedding.cyclic original minimal)
    (fun _ _ _ => MinimalExceptionalEmbedding.triangle_facial original minimal)

end FourColor.FourTriangleRecognition
