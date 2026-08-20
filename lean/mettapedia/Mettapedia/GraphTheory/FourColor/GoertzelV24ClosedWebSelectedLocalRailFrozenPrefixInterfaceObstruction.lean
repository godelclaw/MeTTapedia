import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailFrozenPrefixSeparation

/-!
# L1: a frozen selected-rail support cannot include its live interface

The remote-support invariant is intentionally stated for a support wholly
behind the mutable window.  It cannot be placed on an entire assembly which
already ends at the next window's incoming faces: both rails then share their
terminal vertex with the corresponding future support, contradicting full
support disjointness.

The theorems below make that typing error impossible to forget.  A rolling
state must separate the genuinely frozen support from the bounded live suffix
and permit their named splice endpoints; it cannot label the complete
endpoint-carrying assembly as frozen.  This is a kernel-checked refutation of
the tempting whole-assembly prepend API, not a local transition, end-cap
construction, or closure of Fable flag L1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {leftPlacement : SelectedInternalHexRungPlacement corridor rungs leftInterior}
    {rightPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior leftInterior hnext)}
    {leftIncomingBefore leftIncomingAfter :
      {position // position ∈ selectedPlacementSidePositions leftPlacement}}
    {successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement}
    {left : SeparatedSelectedSourceLocalRailPaths leftPlacement
      leftIncomingBefore leftIncomingAfter successor.frame.leftBefore
      successor.frame.leftAfter}

private abbrev SelectedFace :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

private theorem firstIncoming_mem_firstSupport
    (window : CertifiedSelectedLocalRailTerminalWindow successor left) :
    selectedPlacementSideFace leftPlacement leftIncomingBefore ∈
      window.firstSupport := by
  rcases window with ⟨outcome, _⟩
  cases outcome with
  | straight assembly => exact assembly.firstRail.start_mem_support
  | swapped assembly => exact assembly.firstRail.start_mem_support

private theorem secondIncoming_mem_secondSupport
    (window : CertifiedSelectedLocalRailTerminalWindow successor left) :
    selectedPlacementSideFace leftPlacement leftIncomingAfter ∈
      window.secondSupport := by
  rcases window with ⟨outcome, _⟩
  cases outcome with
  | straight assembly => exact assembly.secondRail.start_mem_support
  | swapped assembly => exact assembly.secondRail.start_mem_support

/-- A complete prefix ending at the first incoming face cannot have its whole
first support frozen against that same future window. -/
theorem not_firstSupport_separatedFromFuture_of_attachedTerminalWindow
    {firstStart secondStart : SelectedFace (web := web)}
    {cutoff : Nat}
    (prefixAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart
      (selectedPlacementSideFace leftPlacement leftIncomingBefore)
      (selectedPlacementSideFace leftPlacement leftIncomingAfter))
    (window : CertifiedSelectedLocalRailTerminalWindow successor left)
    (hgap : cutoff + 3 < leftInterior.center.val) :
    ¬ SupportSeparatedFromFutureSelectedWindows (corridor := corridor)
      cutoff prefixAssembly.firstRail.support := by
  intro hfrozen
  have hdisjoint := hfrozen window.firstSupport window.firstSupport_near hgap
  exact (List.disjoint_left.mp hdisjoint
    prefixAssembly.firstRail.end_mem_support)
      (firstIncoming_mem_firstSupport window)

/-- The same endpoint obstruction occurs on the second rail. -/
theorem not_secondSupport_separatedFromFuture_of_attachedTerminalWindow
    {firstStart secondStart : SelectedFace (web := web)}
    {cutoff : Nat}
    (prefixAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart
      (selectedPlacementSideFace leftPlacement leftIncomingBefore)
      (selectedPlacementSideFace leftPlacement leftIncomingAfter))
    (window : CertifiedSelectedLocalRailTerminalWindow successor left)
    (hgap : cutoff + 3 < leftInterior.center.val) :
    ¬ SupportSeparatedFromFutureSelectedWindows (corridor := corridor)
      cutoff prefixAssembly.secondRail.support := by
  intro hfrozen
  have hdisjoint := hfrozen window.secondSupport window.secondSupport_near hgap
  exact (List.disjoint_left.mp hdisjoint
    prefixAssembly.secondRail.end_mem_support)
      (secondIncoming_mem_secondSupport window)

/-- **L1 state-shape refutation.** The future-separation invariant cannot be
stored on the entire endpoint-carrying prefix assembly.  The rolling state
must expose a smaller frozen support and a bounded live suffix separately. -/
theorem not_separatedFromFutureSelectedWindows_of_attachedTerminalWindow
    {firstStart secondStart : SelectedFace (web := web)}
    {cutoff : Nat}
    (prefixAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart
      (selectedPlacementSideFace leftPlacement leftIncomingBefore)
      (selectedPlacementSideFace leftPlacement leftIncomingAfter))
    (window : CertifiedSelectedLocalRailTerminalWindow successor left)
    (hgap : cutoff + 3 < leftInterior.center.val) :
    ¬ prefixAssembly.SeparatedFromFutureSelectedWindows
      (corridor := corridor) cutoff := by
  intro hfrozen
  exact not_firstSupport_separatedFromFuture_of_attachedTerminalWindow
    prefixAssembly window hgap hfrozen.1

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
