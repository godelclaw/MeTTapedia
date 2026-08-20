import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailAssemblyAppend

/-!
# L1: future separation invariant for a frozen selected-rail prefix

The source composes radius-one collar pieces through a bounded mutable window.
Once a selected-rail piece is sufficiently far behind that window, its support
must never be reconsidered by later local repairs.  This file records that
claim as a quantified invariant and proves three facts:

* every certified two-cell terminal window supplies the invariant;
* moving the cutoff to the right preserves it;
* appending two assemblies which carry it preserves it.

Thus the unbounded prefix is handled by induction while only the bounded
neighbouring window remains geometric.  This does not construct that local
transition, attach either end cap, or close Fable flag L1.
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

private abbrev SelectedFace :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

/-- A support frozen at `cutoff` is disjoint from every later certified
two-centre carrier whose first centre is more than three positions to its
right.  The quantified future support is literal facial support, not a finite
profile code. -/
def SupportSeparatedFromFutureSelectedWindows
    (cutoff : Nat) (support : List (SelectedFace (web := web))) : Prop :=
  ∀ {futureInterior : CorridorInterior blockLength}
      {hfutureNext : futureInterior.center.val + 2 < blockLength}
      (futureSupport : List (SelectedFace (web := web))),
    SupportNearSelectedCenterPair (corridor := corridor)
        futureInterior.center
        (nextCorridorInterior futureInterior hfutureNext).center futureSupport →
      cutoff + 3 < futureInterior.center.val →
      support.Disjoint futureSupport

/-- Advancing the frozen cutoff can only weaken its future obligation. -/
theorem SupportSeparatedFromFutureSelectedWindows.mono
    {oldCutoff newCutoff : Nat} {support : List (SelectedFace (web := web))}
    (hfuture : SupportSeparatedFromFutureSelectedWindows
      (corridor := corridor) oldCutoff support)
    (hle : oldCutoff ≤ newCutoff) :
    SupportSeparatedFromFutureSelectedWindows
      (corridor := corridor) newCutoff support := by
  intro futureInterior hfutureNext futureSupport hnear hgap
  apply hfuture futureSupport hnear
  omega

/-- Future separation is closed under concatenating frozen supports. -/
theorem supportSeparatedFromFutureSelectedWindows_append
    {cutoff : Nat} {firstSupport secondSupport : List (SelectedFace (web := web))}
    (hfirst : SupportSeparatedFromFutureSelectedWindows
      (corridor := corridor) cutoff firstSupport)
    (hsecond : SupportSeparatedFromFutureSelectedWindows
      (corridor := corridor) cutoff secondSupport) :
    SupportSeparatedFromFutureSelectedWindows
      (corridor := corridor) cutoff (firstSupport ++ secondSupport) := by
  intro futureInterior hfutureNext futureSupport hnear hgap
  rw [List.disjoint_left]
  intro face hface hfutureFace
  rcases List.mem_append.mp hface with hfirstFace | hsecondFace
  · exact (List.disjoint_left.mp
      (hfirst futureSupport hnear hgap) hfirstFace) hfutureFace
  · exact (List.disjoint_left.mp
      (hsecond futureSupport hnear hgap) hsecondFace) hfutureFace

variable
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

/-- The first support of a canonical terminal window can be frozen at its
left centre: the already-proved remote-window theorem discharges every future
query. -/
theorem CertifiedSelectedLocalRailTerminalWindow.firstSupport_separatedFromFuture
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    (window : CertifiedSelectedLocalRailTerminalWindow successor left) :
    SupportSeparatedFromFutureSelectedWindows (corridor := corridor)
      leftInterior.center.val window.firstSupport := by
  intro futureInterior hfutureNext futureSupport hnear hgap
  exact window.firstSupport_disjoint_of_remote hsource futureSupport hnear hgap

/-- The symmetric seed theorem for the second terminal support. -/
theorem CertifiedSelectedLocalRailTerminalWindow.secondSupport_separatedFromFuture
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    (window : CertifiedSelectedLocalRailTerminalWindow successor left) :
    SupportSeparatedFromFutureSelectedWindows (corridor := corridor)
      leftInterior.center.val window.secondSupport := by
  intro futureInterior hfutureNext futureSupport hnear hgap
  exact window.secondSupport_disjoint_of_remote hsource futureSupport hnear hgap

/-- Both rails of an arbitrary assembly carry the same frozen-prefix
invariant.  This is proof-relevant induction state, not an assumption that the
next local window composes. -/
def SeparatedFromFutureSelectedWindows
    {firstStart secondStart firstFinish secondFinish : SelectedFace (web := web)}
    (assembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart firstFinish secondFinish)
    (cutoff : Nat) : Prop :=
  SupportSeparatedFromFutureSelectedWindows (corridor := corridor) cutoff
      assembly.firstRail.support ∧
    SupportSeparatedFromFutureSelectedWindows (corridor := corridor) cutoff
      assembly.secondRail.support

/-- Ordered assembly append preserves the frozen-prefix invariant.  The four
local noncollision proofs construct the append; no additional global
separation premise is needed. -/
theorem appendAssembly_separatedFromFutureSelectedWindows
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    {cutoff : Nat}
    (prefixAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (suffixAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleFirst middleSecond firstFinish secondFinish)
    (hfirstPath : prefixAssembly.firstRail.support.Disjoint
      suffixAssembly.firstRail.support.tail)
    (hsecondPath : prefixAssembly.secondRail.support.Disjoint
      suffixAssembly.secondRail.support.tail)
    (hfirstSecond : prefixAssembly.firstRail.support.Disjoint
      suffixAssembly.secondRail.support.tail)
    (hsecondFirst : prefixAssembly.secondRail.support.Disjoint
      suffixAssembly.firstRail.support.tail)
    (hprefix : prefixAssembly.SeparatedFromFutureSelectedWindows
      (corridor := corridor) cutoff)
    (hsuffix : suffixAssembly.SeparatedFromFutureSelectedWindows
      (corridor := corridor) cutoff) :
    (appendAssembly prefixAssembly suffixAssembly hfirstPath hsecondPath
      hfirstSecond hsecondFirst).SeparatedFromFutureSelectedWindows
        (corridor := corridor) cutoff := by
  constructor
  · intro futureInterior hfutureNext futureSupport hnear hgap
    have hp := hprefix.1 futureSupport hnear hgap
    have hs := hsuffix.1 futureSupport hnear hgap
    change (prefixAssembly.firstRail.append suffixAssembly.firstRail).support.Disjoint
      futureSupport
    rw [SimpleGraph.Walk.support_append, List.disjoint_left]
    intro face hface hfutureFace
    rcases List.mem_append.mp hface with hprefixFace | hsuffixFace
    · exact (List.disjoint_left.mp hp hprefixFace) hfutureFace
    · exact (List.disjoint_left.mp hs (List.mem_of_mem_tail hsuffixFace)) hfutureFace
  · intro futureInterior hfutureNext futureSupport hnear hgap
    have hp := hprefix.2 futureSupport hnear hgap
    have hs := hsuffix.2 futureSupport hnear hgap
    change (prefixAssembly.secondRail.append suffixAssembly.secondRail).support.Disjoint
      futureSupport
    rw [SimpleGraph.Walk.support_append, List.disjoint_left]
    intro face hface hfutureFace
    rcases List.mem_append.mp hface with hprefixFace | hsuffixFace
    · exact (List.disjoint_left.mp hp hprefixFace) hfutureFace
    · exact (List.disjoint_left.mp hs (List.mem_of_mem_tail hsuffixFace)) hfutureFace

/-- Crossed assembly append preserves the same invariant; endpoint parity is
irrelevant to future support separation. -/
theorem appendAssemblyCrossed_separatedFromFutureSelectedWindows
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    {cutoff : Nat}
    (prefixAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (suffixAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleSecond middleFirst firstFinish secondFinish)
    (hfirstPath : prefixAssembly.firstRail.support.Disjoint
      suffixAssembly.secondRail.support.tail)
    (hsecondPath : prefixAssembly.secondRail.support.Disjoint
      suffixAssembly.firstRail.support.tail)
    (hfirstSecond : prefixAssembly.firstRail.support.Disjoint
      suffixAssembly.firstRail.support.tail)
    (hsecondFirst : prefixAssembly.secondRail.support.Disjoint
      suffixAssembly.secondRail.support.tail)
    (hprefix : prefixAssembly.SeparatedFromFutureSelectedWindows
      (corridor := corridor) cutoff)
    (hsuffix : suffixAssembly.SeparatedFromFutureSelectedWindows
      (corridor := corridor) cutoff) :
    (appendAssemblyCrossed prefixAssembly suffixAssembly hfirstPath hsecondPath
      hfirstSecond hsecondFirst).SeparatedFromFutureSelectedWindows
        (corridor := corridor) cutoff := by
  constructor
  · intro futureInterior hfutureNext futureSupport hnear hgap
    have hp := hprefix.1 futureSupport hnear hgap
    have hs := hsuffix.2 futureSupport hnear hgap
    change (prefixAssembly.firstRail.append suffixAssembly.secondRail).support.Disjoint
      futureSupport
    rw [SimpleGraph.Walk.support_append, List.disjoint_left]
    intro face hface hfutureFace
    rcases List.mem_append.mp hface with hprefixFace | hsuffixFace
    · exact (List.disjoint_left.mp hp hprefixFace) hfutureFace
    · exact (List.disjoint_left.mp hs (List.mem_of_mem_tail hsuffixFace)) hfutureFace
  · intro futureInterior hfutureNext futureSupport hnear hgap
    have hp := hprefix.2 futureSupport hnear hgap
    have hs := hsuffix.1 futureSupport hnear hgap
    change (prefixAssembly.secondRail.append suffixAssembly.firstRail).support.Disjoint
      futureSupport
    rw [SimpleGraph.Walk.support_append, List.disjoint_left]
    intro face hface hfutureFace
    rcases List.mem_append.mp hface with hprefixFace | hsuffixFace
    · exact (List.disjoint_left.mp hp hprefixFace) hfutureFace
    · exact (List.disjoint_left.mp hs (List.mem_of_mem_tail hsuffixFace)) hfutureFace

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
