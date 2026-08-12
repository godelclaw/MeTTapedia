import Mettapedia.GraphTheory.FourColor.GoertzelV24GraphDerivedCorridorOpenProfile

/-!
# Partitioning corridor boundary ports

A geometric boundary may be presented first as one ordered list of crossed
edges and later split into moving crossings and fixed terminal edges.  This
file performs that split without changing the regional graph or its face
fragments.

The construction is only a reindexing operation.  It does not assert that the
two selected blocks cover the original boundary, nor that either block is
injective; concrete geometry supplies those properties when they are needed.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24CorridorProfilePortPartition

open GoertzelV24CorridorProfile
open GoertzelV24GraphDerivedCorridorCutProfile

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Reindex a boundary port by selecting either an ordinary crossing or a
terminal from one common crossing list. -/
def partitionCorridorPort
    {crossingWidth terminalCount totalWidth : Nat}
    (crossingIndex : Fin crossingWidth → Fin totalWidth)
    (terminalIndex : Fin terminalCount → Fin totalWidth) :
    CorridorPort crossingWidth terminalCount → CorridorPort totalWidth 0
  | .inl crossing => .inl (crossingIndex crossing)
  | .inr terminal => .inl (terminalIndex terminal)

@[simp]
theorem partitionCorridorPort_inl
    {crossingWidth terminalCount totalWidth : Nat}
    (crossingIndex : Fin crossingWidth → Fin totalWidth)
    (terminalIndex : Fin terminalCount → Fin totalWidth)
    (crossing : Fin crossingWidth) :
    partitionCorridorPort crossingIndex terminalIndex (.inl crossing) =
      (.inl (crossingIndex crossing) : CorridorPort totalWidth 0) :=
  rfl

@[simp]
theorem partitionCorridorPort_inr
    {crossingWidth terminalCount totalWidth : Nat}
    (crossingIndex : Fin crossingWidth → Fin totalWidth)
    (terminalIndex : Fin terminalCount → Fin totalWidth)
    (terminal : Fin terminalCount) :
    partitionCorridorPort crossingIndex terminalIndex (.inr terminal) =
      (.inl (terminalIndex terminal) : CorridorPort totalWidth 0) :=
  rfl

/-- Reclassify selected entries of one crossing-only profile as crossing and
terminal coordinates, retaining the same face-fragment carrier and all five
profile fields. -/
def CorridorCutProfile.partitionCrossings
    {crossingWidth terminalCount totalWidth faceFragmentCount : Nat}
    (profile : CorridorCutProfile totalWidth 0 faceFragmentCount)
    (crossingIndex : Fin crossingWidth → Fin totalWidth)
    (terminalIndex : Fin terminalCount → Fin totalWidth) :
    CorridorCutProfile crossingWidth terminalCount faceFragmentCount where
  edgeColor crossing := profile.edgeColor (crossingIndex crossing)
  strandConnected pair first second :=
    profile.strandConnected pair
      (partitionCorridorPort crossingIndex terminalIndex first)
      (partitionCorridorPort crossingIndex terminalIndex second)
  faceContinues := profile.faceContinues
  fragmentContainsPort fragment port :=
    profile.fragmentContainsPort fragment
      (partitionCorridorPort crossingIndex terminalIndex port)
  faceLengthCap := profile.faceLengthCap

/-- Reclassify selected entries of one crossing-only graph cut while leaving
its edge region and face-fragment presentation unchanged. -/
def GraphCorridorCutData.partitionCrossings
    {RS : RotationSystem V E}
    {crossingWidth terminalCount totalWidth faceFragmentCount : Nat}
    (data : GraphCorridorCutData RS totalWidth 0 faceFragmentCount)
    (crossingIndex : Fin crossingWidth → Fin totalWidth)
    (terminalIndex : Fin terminalCount → Fin totalWidth) :
    GraphCorridorCutData RS crossingWidth terminalCount faceFragmentCount where
  regionEdges := data.regionEdges
  crossingEdge crossing := data.crossingEdge (crossingIndex crossing)
  terminalEdge terminal := data.crossingEdge (terminalIndex terminal)
  fragmentFace := data.fragmentFace
  fragmentEdges := data.fragmentEdges

@[simp]
theorem GraphCorridorCutData.partitionCrossings_portEdge
    {RS : RotationSystem V E}
    {crossingWidth terminalCount totalWidth faceFragmentCount : Nat}
    (data : GraphCorridorCutData RS totalWidth 0 faceFragmentCount)
    (crossingIndex : Fin crossingWidth → Fin totalWidth)
    (terminalIndex : Fin terminalCount → Fin totalWidth)
    (port : CorridorPort crossingWidth terminalCount) :
    (GraphCorridorCutData.partitionCrossings data crossingIndex terminalIndex
        ).portEdge port =
      data.portEdge
        (partitionCorridorPort crossingIndex terminalIndex port) := by
  cases port <;> rfl

/-- Regional profile construction commutes with splitting one ordered
crossing list into moving crossings and fixed terminals. -/
theorem GraphCorridorCutData.partitionCrossings_regionalProfile
    {RS : RotationSystem V E}
    {crossingWidth terminalCount totalWidth faceFragmentCount : Nat}
    (data : GraphCorridorCutData RS totalWidth 0 faceFragmentCount)
    (crossingIndex : Fin crossingWidth → Fin totalWidth)
    (terminalIndex : Fin terminalCount → Fin totalWidth)
    (color : E → Color)
    (hcrossing : ∀ crossing, color (data.crossingEdge crossing) ≠ 0) :
    CorridorCutProfile.partitionCrossings
        (data.regionalProfile color hcrossing) crossingIndex terminalIndex =
      (GraphCorridorCutData.partitionCrossings data crossingIndex terminalIndex
        ).regionalProfile color
          (fun crossing => hcrossing (crossingIndex crossing)) := by
  unfold CorridorCutProfile.partitionCrossings
  unfold GraphCorridorCutData.regionalProfile
  congr 1
  · exact funext fun pair => funext fun first => funext fun second => by
      cases first <;> cases second <;> rfl
  · exact funext fun fragment => funext fun port => by
      cases port <;> rfl

end

end GoertzelV24CorridorProfilePortPartition

end Mettapedia.GraphTheory.FourColor
