import Mettapedia.GraphTheory.FourColor.GoertzelV24BoundaryProfileFiniteState
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebBoundaryData

/-!
# Terminal-aware graph-derived corridor profiles

The finite corridor-profile carrier is already parametric in a family of
fixed terminal edges.  This module supplies the missing graph-side adapter:
it augments a zero-terminal cut with an explicit terminal family while
retaining the same region, crossing edges, and partial-face fragments.

For Cell 3 the five terminals are the five named inner-boundary edges.  The
resulting carrier is `BoundedCorridorCutProfile 2 5 8`.  This construction
does not assert that a local Cell region contains those five edges.  The
`PortsInRegion` equivalence below keeps the source's genuinely cumulative
region obligation explicit; the later Cell update theorem must discharge it.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24GraphDerivedTerminalProfile

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24CorridorProfile
open GoertzelV24GraphDerivedCorridorCutProfile

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Add an explicitly named family of fixed terminal edges to graph-derived
cut data that previously had no terminals.  All geometric coordinates other
than the terminal family are retained definitionally. -/
def withTerminalEdges
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (cut : GraphCorridorCutData RS crossingEdgeCount 0 faceFragmentCount)
    (terminalEdge : Fin terminalCount -> E) :
    GraphCorridorCutData RS crossingEdgeCount terminalCount
      faceFragmentCount where
  regionEdges := cut.regionEdges
  crossingEdge := cut.crossingEdge
  terminalEdge := terminalEdge
  fragmentFace := cut.fragmentFace
  fragmentEdges := cut.fragmentEdges

@[simp] theorem withTerminalEdges_regionEdges
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (cut : GraphCorridorCutData RS crossingEdgeCount 0 faceFragmentCount)
    (terminalEdge : Fin terminalCount -> E) :
    (withTerminalEdges cut terminalEdge).regionEdges = cut.regionEdges :=
  rfl

@[simp] theorem withTerminalEdges_crossingEdge
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (cut : GraphCorridorCutData RS crossingEdgeCount 0 faceFragmentCount)
    (terminalEdge : Fin terminalCount -> E)
    (crossing : Fin crossingEdgeCount) :
    (withTerminalEdges cut terminalEdge).crossingEdge crossing =
      cut.crossingEdge crossing :=
  rfl

@[simp] theorem withTerminalEdges_terminalEdge
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (cut : GraphCorridorCutData RS crossingEdgeCount 0 faceFragmentCount)
    (terminalEdge : Fin terminalCount -> E)
    (terminal : Fin terminalCount) :
    (withTerminalEdges cut terminalEdge).terminalEdge terminal =
      terminalEdge terminal :=
  rfl

@[simp] theorem withTerminalEdges_fragmentFace
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (cut : GraphCorridorCutData RS crossingEdgeCount 0 faceFragmentCount)
    (terminalEdge : Fin terminalCount -> E)
    (fragment : Fin faceFragmentCount) :
    (withTerminalEdges cut terminalEdge).fragmentFace fragment =
      cut.fragmentFace fragment :=
  rfl

@[simp] theorem withTerminalEdges_fragmentEdges
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (cut : GraphCorridorCutData RS crossingEdgeCount 0 faceFragmentCount)
    (terminalEdge : Fin terminalCount -> E)
    (fragment : Fin faceFragmentCount) :
    (withTerminalEdges cut terminalEdge).fragmentEdges fragment =
      cut.fragmentEdges fragment :=
  rfl

@[simp] theorem withTerminalEdges_portEdge_crossing
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (cut : GraphCorridorCutData RS crossingEdgeCount 0 faceFragmentCount)
    (terminalEdge : Fin terminalCount -> E)
    (crossing : Fin crossingEdgeCount) :
    (withTerminalEdges cut terminalEdge).portEdge
        (Sum.inl crossing : CorridorPort crossingEdgeCount terminalCount) =
      cut.crossingEdge crossing :=
  rfl

@[simp] theorem withTerminalEdges_portEdge_terminal
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (cut : GraphCorridorCutData RS crossingEdgeCount 0 faceFragmentCount)
    (terminalEdge : Fin terminalCount -> E)
    (terminal : Fin terminalCount) :
    (withTerminalEdges cut terminalEdge).portEdge
        (Sum.inr terminal : CorridorPort crossingEdgeCount terminalCount) =
      terminalEdge terminal :=
  rfl

@[simp] theorem withTerminalEdges_regionalFragmentEdges
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (cut : GraphCorridorCutData RS crossingEdgeCount 0 faceFragmentCount)
    (terminalEdge : Fin terminalCount -> E)
    (fragment : Fin faceFragmentCount) :
    (withTerminalEdges cut terminalEdge).regionalFragmentEdges fragment =
      cut.regionalFragmentEdges fragment :=
  rfl

/-- Terminal augmentation is geometrically valid exactly when the original
crossing ports remain in the region and every newly named terminal edge is
also in that same region. -/
theorem withTerminalEdges_portsInRegion_iff
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (cut : GraphCorridorCutData RS crossingEdgeCount 0 faceFragmentCount)
    (terminalEdge : Fin terminalCount -> E) :
    (withTerminalEdges cut terminalEdge).PortsInRegion <->
      cut.PortsInRegion /\
        forall terminal, terminalEdge terminal ∈ cut.regionEdges := by
  constructor
  · intro hports
    constructor
    · intro port
      rcases port with crossing | impossible
      · exact hports (Sum.inl crossing)
      · exact Fin.elim0 impossible
    · intro terminal
      exact hports (Sum.inr terminal)
  · rintro ⟨hcrossing, hterminal⟩ port
    rcases port with crossing | terminal
    · exact hcrossing (Sum.inl crossing)
    · exact hterminal terminal

/-- Terminal augmentation has distinct ports exactly when the crossing list
and terminal list are separately injective and no crossing edge is also a
terminal edge. -/
theorem withTerminalEdges_portsInjective_iff
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (cut : GraphCorridorCutData RS crossingEdgeCount 0 faceFragmentCount)
    (terminalEdge : Fin terminalCount -> E) :
    (withTerminalEdges cut terminalEdge).PortsInjective <->
      Function.Injective cut.crossingEdge /\
        Function.Injective terminalEdge /\
          forall crossing terminal,
            cut.crossingEdge crossing ≠ terminalEdge terminal := by
  constructor
  · intro hinjective
    refine ⟨?_, ?_, ?_⟩
    · intro first second heq
      have hports :
          (Sum.inl first : CorridorPort crossingEdgeCount terminalCount) =
            Sum.inl second := by
        apply hinjective
        simpa using heq
      exact Sum.inl_injective hports
    · intro first second heq
      have hports :
          (Sum.inr first : CorridorPort crossingEdgeCount terminalCount) =
            Sum.inr second := by
        apply hinjective
        simpa using heq
      exact Sum.inr_injective hports
    · intro crossing terminal heq
      have hports :
          (Sum.inl crossing : CorridorPort crossingEdgeCount terminalCount) =
            Sum.inr terminal := by
        apply hinjective
        simpa using heq
      cases hports
  · rintro ⟨hcrossing, hterminal, hdisjoint⟩ first second heq
    rcases first with first | first <;> rcases second with second | second
    · exact congrArg Sum.inl (hcrossing heq)
    · exact (hdisjoint first second heq).elim
    · exact (hdisjoint second first heq.symm).elim
    · exact congrArg Sum.inr (hterminal heq)

/-- Adding terminals does not alter the computed regional face fragments. -/
@[simp] theorem withTerminalEdges_fragmentsOnFaceInRegion_iff
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (cut : GraphCorridorCutData RS crossingEdgeCount 0 faceFragmentCount)
    (terminalEdge : Fin terminalCount -> E) :
    (withTerminalEdges cut terminalEdge).FragmentsOnFaceInRegion <->
      cut.FragmentsOnFaceInRegion := by
  rfl

/-- The terminal-aware finite carrier required when a width-two Cell-3 cut
remembers the five named inner-boundary edges and at most eight partial face
fragments.  Its finiteness, decidable equality, and exact count are inherited
from the existing parametric carrier. -/
abbrev Cell3TerminalAwareProfile :=
  BoundedCorridorCutProfile 2 5 8

/-- Exact size of the existing conservative Boolean carrier at Cell-3
width.  This proves finiteness but also records why later work should isolate
the graph-realizable/reachable subcarrier before extracting a practical
threshold. -/
theorem card_cell3TerminalAwareProfile :
    Fintype.card Cell3TerminalAwareProfile =
      3584770624228412041971806031305297940343236798606615203183066838974303878865092935155712 := by
  rw [card_boundedCorridorCutProfile]
  norm_num [boundedCorridorCutProfileCount, corridorCutProfileCount,
    Fin.sum_univ_succ]

section ClosedWeb

variable {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount crossingEdgeCount faceFragmentCount : Nat}

/-- Use the actual five inner-boundary edges of a closed-web instance as the
fixed terminal family of a graph-derived cut. -/
def withInnerBoundaryTerminals
    {RS : RotationSystem V G.edgeSet}
    (boundary : AnnularBoundaryData G outerCount)
    (cut : GraphCorridorCutData RS crossingEdgeCount 0 faceFragmentCount) :
    GraphCorridorCutData RS crossingEdgeCount 5 faceFragmentCount :=
  withTerminalEdges cut boundary.innerBoundaryEdge

@[simp] theorem withInnerBoundaryTerminals_terminalEdge
    {RS : RotationSystem V G.edgeSet}
    (boundary : AnnularBoundaryData G outerCount)
    (cut : GraphCorridorCutData RS crossingEdgeCount 0 faceFragmentCount)
    (terminal : Fin 5) :
    (withInnerBoundaryTerminals boundary cut).terminalEdge terminal =
      boundary.innerBoundaryEdge terminal :=
  rfl

/-- The precise remaining geometric obligation for a terminal-aware source
cut: the old crossing ports are valid and all five cap-foot edges belong to
the chosen cumulative side of the cut. -/
theorem withInnerBoundaryTerminals_portsInRegion_iff
    {RS : RotationSystem V G.edgeSet}
    (boundary : AnnularBoundaryData G outerCount)
    (cut : GraphCorridorCutData RS crossingEdgeCount 0 faceFragmentCount) :
    (withInnerBoundaryTerminals boundary cut).PortsInRegion <->
      cut.PortsInRegion /\
        forall terminal, boundary.innerBoundaryEdge terminal ∈ cut.regionEdges := by
  exact withTerminalEdges_portsInRegion_iff cut boundary.innerBoundaryEdge

end ClosedWeb

end

end GoertzelV24GraphDerivedTerminalProfile

end Mettapedia.GraphTheory.FourColor
