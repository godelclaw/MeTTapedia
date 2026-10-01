import Mettapedia.GraphTheory.FourColor.DualTruncateFacePhaseGSLT
import Mettapedia.GraphTheory.FourColor.DualTruncateSpanningFaceExample

/-!
# A nontrivial literal face-phase repair

The theta source retains its three distinct parallel edges. One of its face
polygons has the opposite phase to a fixed source choice. Its actual target
colouring is proper and cross-compatible, but is not that source image.
The general physical normalization repairs it without changing any cross
edge. The fixture is separate from the uniform proof.
-/

namespace Mettapedia.GraphTheory.FourColor.DualTruncateFacePhaseExample

open DualTruncateColoring DualTruncateFacePhaseKempe
open GoertzelV24ThetaPresentationCounterexample

noncomputable section
abbrev source := DualTruncateSpanningFaceExample.source
abbrev witness := DualTruncateSpanningFaceExample.inputSource

def inputCorners : ThetaDart → Color
  | .firstLeft | .firstRight | .secondRight => blue
  | .secondLeft | .thirdLeft | .thirdRight => red

theorem inputCorners_valid : DualTruncateCornerSemantics.Valid source inputCorners := by
  constructor
  · intro d; cases d <;> decide +kernel
  constructor
  · intro d; cases d <;> decide +kernel
  · intro d
    unfold DualTruncateCornerSemantics.Balanced
    cases d <;> decide +kernel

def input := DualTruncateCornerSemantics.colouring source inputCorners inputCorners_valid

def initial : State source witness where
  colouring := input
  tait := DualTruncateCornerSemantics.colouring_tait source inputCorners inputCorners_valid
  compatible := by
    intro d
    change DualTruncateCornerSemantics.cross source inputCorners (source.edgeOf d) = _
    rw [DualTruncateCornerSemantics.cross_edge source inputCorners d (inputCorners_valid.2.2 d)]
    cases d <;> decide +kernel

theorem input_requires_repair : input (.inr ThetaDart.firstLeft) ≠
    DualTruncateColoring.colouring source witness (.inr ThetaDart.firstLeft) := by
  decide +kernel

theorem repair_exact : (normalize source witness initial).colouring =
    DualTruncateColoring.colouring source witness := normalize_exact source witness initial

theorem all_cross_preserved (edge : ThetaEdge) :
    (normalize source witness initial).colouring (.inl edge) = input (.inl edge) :=
  normalize_cross_preserved source witness initial edge

theorem history_length : (DualTruncateFacePhaseGSLT.repair source witness initial).length = 3 := rfl

end
end Mettapedia.GraphTheory.FourColor.DualTruncateFacePhaseExample
