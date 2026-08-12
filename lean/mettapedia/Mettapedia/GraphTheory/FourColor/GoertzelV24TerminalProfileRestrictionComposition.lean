import Mettapedia.GraphTheory.FourColor.GoertzelV24CorridorProfilePortPartition
import Mettapedia.GraphTheory.FourColor.GoertzelV24CorridorProfileRestriction
import Mettapedia.GraphTheory.FourColor.GoertzelV24TerminalProfileRestriction

/-!
# Composing terminal-profile restrictions

A slab boundary may first be partitioned into moving crossings and fixed
terminals and then restricted to one moving boundary block.  This file proves
that forgetting the fixed terminals after those two operations is exactly the
single crossing restriction obtained by composing their index maps.

The result is deliberately one-way.  It never reconstructs terminal data from
the crossing-only profile, and it makes no claim that terminal coordinates of
different slabs agree.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24TerminalProfileRestrictionComposition

open GoertzelV24CorridorProfile
open GoertzelV24CorridorProfilePortPartition
open GoertzelV24CorridorProfileRestriction
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24GraphDerivedTerminalProfile

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Forgetting fixed terminals commutes with selecting a moving crossing
block.  This is the generic square used when a terminal-aware slab relation
is projected to its crossing-only presentation. -/
theorem forgetTerminals_restrictCrossings
    {smallWidth largeWidth terminalCount faceFragmentCount : Nat}
    (profile : CorridorCutProfile largeWidth terminalCount faceFragmentCount)
    (inclusion : Fin smallWidth → Fin largeWidth) :
    forgetTerminals
        (CorridorCutProfile.restrictCrossings profile inclusion) =
      CorridorCutProfile.restrictCrossings (forgetTerminals profile)
        inclusion := by
  unfold forgetTerminals
  unfold CorridorCutProfile.restrictCrossings
  congr 1
  · funext pair first second
    rcases first with first | impossible
    · rcases second with second | impossible
      · rfl
      · exact Fin.elim0 impossible
    · exact Fin.elim0 impossible
  · funext fragment port
    rcases port with crossing | impossible
    · rfl
    · exact Fin.elim0 impossible

/-- Partitioning a crossing list, selecting one moving block, and forgetting
the fixed terminals is the same five-field profile as selecting that block
directly from the original list. -/
theorem forgetTerminals_restrictCrossings_partitionCrossings
    {smallWidth crossingWidth terminalCount totalWidth faceFragmentCount : Nat}
    (profile : CorridorCutProfile totalWidth 0 faceFragmentCount)
    (crossingIndex : Fin crossingWidth → Fin totalWidth)
    (terminalIndex : Fin terminalCount → Fin totalWidth)
    (inclusion : Fin smallWidth → Fin crossingWidth) :
    forgetTerminals
        (CorridorCutProfile.restrictCrossings
          (CorridorCutProfile.partitionCrossings profile crossingIndex
            terminalIndex)
          inclusion) =
      CorridorCutProfile.restrictCrossings profile
        (crossingIndex ∘ inclusion) := by
  unfold forgetTerminals
  unfold CorridorCutProfile.restrictCrossings
  unfold CorridorCutProfile.partitionCrossings
  congr 1
  · funext pair first second
    rcases first with first | impossible
    · rcases second with second | impossible
      · rfl
      · exact Fin.elim0 impossible
    · exact Fin.elim0 impossible
  · funext fragment port
    rcases port with crossing | impossible
    · rfl
    · exact Fin.elim0 impossible

/-- The corresponding raw graph-cut presentations differ only by whether the
fixed terminal family is stored explicitly.  Region edges, moving crossings,
and face fragments are definitionally identical. -/
theorem restrictCrossings_partitionCrossings_eq_withTerminalEdges
    {RS : RotationSystem V E}
    {smallWidth crossingWidth terminalCount totalWidth faceFragmentCount : Nat}
    (data : GraphCorridorCutData RS totalWidth 0 faceFragmentCount)
    (crossingIndex : Fin crossingWidth → Fin totalWidth)
    (terminalIndex : Fin terminalCount → Fin totalWidth)
    (inclusion : Fin smallWidth → Fin crossingWidth) :
    GraphCorridorCutData.restrictCrossings
        (GraphCorridorCutData.partitionCrossings data crossingIndex
          terminalIndex)
        inclusion =
      withTerminalEdges
        (GraphCorridorCutData.restrictCrossings data
          (crossingIndex ∘ inclusion))
        (fun terminal => data.crossingEdge (terminalIndex terminal)) :=
  rfl

end

end GoertzelV24TerminalProfileRestrictionComposition

end Mettapedia.GraphTheory.FourColor
